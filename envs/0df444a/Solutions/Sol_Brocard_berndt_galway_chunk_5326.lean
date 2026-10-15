-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5326
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:29:58.625143+00:00
-- url     : https://prove2.me/submissions/d47ba334-bae7-429a-b97e-33a0b23862bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 957733812 ≤ n < 957913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 957735062 1250 957733812 957733849
    0x902060d06080715141b0a08042301021b040c0309020301150302031903171e0f07031a0102030f0d060503190c0501030c080f041b0b09120a0803160e 65
    0x90200300f140310012144c00c40d003540d0319040b038592403080c102d40390f68402da003511150902a066044080c050a2240040d855444044150784035664140200b8404010300740c0340030314a403150940c138194004500e065003950f149120301e0b40302031410100401003094006104c1096a104c080000580302407244001441213010255034a80c518810546401d455661341088003080264100010ba0008080f951400303040310f141c2c4080d642c008110b44c1000001c50600300300d000b51030034070110a8180c01e2060040c4165503051203c4100303e40c000958a02c01080d01d40141d108000b02c04c0751410441c0178040480e0600c4000c505c0b44c0c0d42d078000034a4400c03c030b500c0c078214150409614042004040025009040c2030805100c00152074501038031844c801403500300c4c10403c840010302002031411201c00c0c601035600200040d03a88071101400b460704078981035400b072984010719070211a070000f03031400c0d21075100c0303c00341c41c5944d50162448602c4000c0301e03120510007441c07801086503480c2d401070281a420507 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 957736312 1250 957735062 957735073
    0x509241309060b270901020d02030a0e06010503120d020c1015060e190e0702010b0a080313140d080a0504050d1515180c090e0405210903030d0902060d0608 68
    0x18144503080703581c501803062140c41100b41050011010368440b00440010025030305051703a50040c4540607210780302c03810741c1070780c40001080140f1019a2244107803130983c0d01100d402d070303894130117240d0740f8231604c0782c00f2110303003c14022151a00c07007540040601020b264240c40e03882c4e0140c5450010f842e08011480c6500c40440c13410702095078402071444505c0021a1004a054041c1c4c01003600d240c50360050000702c0000c6000116203d0003500217007a41900a480b03c0015581ca0f40320513101c2c2c014620700d104440c1c0c0047d002403402040d0f655580d910302c005214441c1c45c0b03060765078491950703c00d405580038844144000142951450442d0030200e002d40300042920103201e520408071140340c540c10801600c0c000d000d11000f010b00020b41840300201c0b4000a94003800384050350700264551080f00010421002c000821a004c03c1c0d02c511074807005082191080c8131040122701c0d02034001c045030184d005000842a580e00c0d40c100007029400544414509148404204d00b42e90f804d0f0800f0b21140e221 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 957737562 1250 957736312 957736331
    0x503010909030e04050925051c030c1b05130605030c06070212060a0f0606021501030201201c0318110415120f0b01060e0d0803040302031b070501030506010905092413 73
    0x42d40c9040c147c03064503862800d8200000609a40d80d40e2408140030f141d000c44660400d4000d250090195402000304bc406c9641a01500f00d11806409200c0c00340a1344000c0754101819070107080305540380180544140600f600500041e6040820140d9200701d8891a000f03400d10140300c040d0141c00e4031710002c2003c81400ca460001e48001390b0000d01191702c00180343d00c0b4031300c1d4a00118150b90382480e20030035030296529040d601220056448210780680d452800c404406000246205c0180e030b102441154241c90f910b1089414069006e0090030b500400c5d88620302d080e502c2856504c000e4241c2000c03030742d200c060b040310b0801035a000f05c2c0d0407080b00c2c8614041c405440e030301900602d402e00d400741001c0705001c04220501010580100a1607001c070200d410075000303105560300003640701d59440114100c0a800b954400300c9215241c00301e07203408082170300c6501c221200401d544000e0005582c0f0303254203140c01002c1c3c2000c6042c140c42001c405201c2c0b556030b140c2c5490001c8498030300010030040768 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 957738812 1250 957737562 957737593
    0x1050915070807030b0a15081914151903030c05150106020a0807113c0607020112090507081608010b0307030813090203040f051009030503010909030e040509 69
    0xd03120040800501103808110300709500550700e50b40700e0024a804544803207014041182200035030400000345001081404001c2c3e070209004d0b10802c0c081642c040301c480c04280790030444180d107219000c13454401c4009184000146484182000c001c4d07c48440ca01f9000e0400f5002203458004a0001d01400d10301000d104040092043c211811440210707554907024002e036699000c6c05c0018a04600420040706100e51a01080240e40d0060141080b0754085801002c800e4640d4490121460721079015841e1903200d5034000501d01400360100b45881d600e9001074460000c502e4404c81a1601c9007414400a00140414002001c0c184002c0c441c0101c2c0c410751180701821600b0848041c0c1c0340080400403a03900103051021250010380c52651002c80300300d56410444035410070501c0e140004140000c0205000802e05014011019101034204542640c819121380d502c0150000c0d5080c001071011180701d50120800c0c2e032003801e2900b8035175501d80125098035412a00e100c413030303040800003021508 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 957740062 1250 957738812 957738823
    0x81f030303021b0c21030705060a06032303030402040905010209150c1504080a03020a0513240f08041518050c0108010e040b01090c03060b0c0c0a050d0506040f1b08010509 75
    0x806100c0684400c0498402040320408545505c1204003800080e0300c51010082c000c89040310307004403c1d81d102e4600411842e014010034031040302c0c848030220219071803041703006c144030143d012000918510784071034003000064010b06000f514155420803045010b65079031400318000f40c07482c2442c0f039114200480118113084801403030221a10700a0100400200541d08070b40b0300000c0740c10b0040c1c0394608950101e5003401420172128122010000100d002010005100d4503c05031034640c1c681c0c001045000c803402811800190041a0340d41d003c640040d502d002d440f641c1d10f15052002911301010248107502d0f42c104070007aa46604401109901942e0042c001400341c62260008500350800342d0703940b000c001c81403151140ba075035151119480d440c8603801500051010840580d1103178880d0441c2621070100d402068414010f42000180b41e04040701400c8000742c000001e01429609c0c2c2c0c44010003112000c404907804951807102d0a0700380903c090001c00340100e040002142d00d42413807070502c2d15 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 957741312 1250 957740062 957740107
    0x30c0309050307031106030a06050d0c0810022d13030f02100f17090a15051008070b0406110304170610091404030c020f04020a0509090a140403081f03030302 69
    0x94206441c140080740b0071442418a16001b41c6a042e034076030f9480301c0d450040c42981c2105a0000c0b481c05540144032483d0403110540e9504001e454a43d0022420b0340c0403840341c2540081c2d1032280402d581510070030003070401c4c1c0000b0141c60091510f0002e040c0000311240030b4004440c8100c40d100d40c8420750800c1c803002032149049042c452000700203034402601e0129042e000b0b41c1501c546800040b01942e043c42450f24180d4811405580e10b81780c1e461803400b4040842e8400c0882009003000a94030300e0008099048035080d040300c500c0c00e0f0a011044a0740010141d140066110420000074111410040307482c04c170414002034155424203030360140d401c4105500101ca5a0700300707601104092a00164035800c1035041c1050441d14090b0b2020074840301420050b194010305c003094070107140d0b030004000c01d4491411500746a0958802202d00110307172202c8004148540307000d0001d40020700406030540c0002c41403c080500e1400c4044070314000b1801d40084000075000305403c451841982803e0780403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 957742562 1250 957741312 957741319
    0x30c330a060f0b0a030609060b03013f05010f0507050306040f240302030d0518130e060c030105010f18060e0109030c0b09040c0c050c15130e1008060f011412030304030c030905 77
    0xa03894641162220300040c020b14090107421208810714901d82d00103001540755030240601e0b000f1003407101c8154201a10386c153707815424200c03049d403d115184220783c4115141c5c0c503041d086440b04c2e01804000c0403400310340314000380c0d5401d4640058001040d2200003d81840300301038564114414141409070b00c1e004201800003d11110000c814074102c9140d180d0000c0d0351000c0c00c15170020841c1c024025041803a0058003c403030500404505131130055040e03400c02c0c0c946d202000c04c9070104468107984142d298948050210040c41811710805400c208040d0503d06111801d4980d110200440d1482c0d101d800240400203134882c20307007000e000f6180c550032070381480c00c440b21494030740548a541110280384120903001180c903905201d0420350300e00318411440481016226107045031215002c0c7c0d02001e011544400001700c08000042c3c481c401c1e072004401140d6070346004040c10582d16007941443c3e100540001c100900403003000518821800303a5603e611640d0b82c6c0c20043d01080c0d81b500220300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 957743812 1250 957742562 957742571
    0x2070f3c0807030324030c0f0602030d05090a051623060706050907090207110f1903030c031704030818070501320c030c330a060f0b0a030609 62
    0x340c85110310603021034015154541c0c4400e285021001000120700c40420304090580050034480d5004506054038840e03040000c0700c645030345011084280c5c078440c41005034010001c2d60150f01c5590040d40d0040c1c1e84400700c0b01c20072811740d502c0d400c007441a07003030460003594036804208080c41e540340364910340d610f641c82c0c40c0b602c1e0760180801c48a201c0c082020700115100d40108074001c90030041ca500515200c001151030700b2241c0341000140c8160f01ca0749100b40001c00c06240140f5050504045881001c0d000b0001c8519556050301c400410300010f409000c580140801401e040201540c4942e10980d03400c1d4252900001e1140c00c1c0d00c0300070044e039040d40404000c2c4503903600719594540d40e0001510130f0034900300410402d820300d40022005d1490800104081e034a9440000c01741034103103094016501d03403800b8401d20503080c1c404200c6480400c40c10f008035604c8012251042038110900c0107000c9413141d110144031192103525403168207440703400200000241e07030610510000e090003040a00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 957745062 1250 957743812 957743903
    0x203070329040218090c0405151212040510050903030f0c151b0c0705210d0e100f021501030b0114040510050616060c08040b060f012102070f 62
    0x1c484041a0701404c9041203114003080c0c801400f04248131074500b0040042c0490301d005251311144e021241c0e1000d0080f5442001003a20800102e00d190b0200070b03914003181018642810400b0310300b07028040c80140442042275043c50b4905000911a03540c20340d028540c1c0e40031300c2c4242441c068040007141c40c2c00300e881d401c2c000151014401140c1c94009e13500303e6074407000ca0380c29035420310000342d000701d038000040b03154007a80e4554200350400344141c520584081c042c10100c140d0744000c0c03160843c0d07405400600d00c05951801750540a4480714144101d94a500c107104115074280f10a13003081c1d83c01d00390b000041141e180c00e11204590081d00b9203061255041507503100c80c00c040c55014542c0f095101040c802e1208603c030b01501e01c401e0b00580f0030b000d0040916400b800000b0240e406442400c41580052180e0400300061803003407030103a40d4084c20190507809005914408410741401540030048200415160071616842c28041c031244d000d41442030800c1c0c111100c504a0014041800c0501038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 957746312 1250 957745062 957745069
    0xb130e161b0827100f0518190e010e090c0405150409060b1f0801090b0316150e01031e0b040f0f0e0f0c0904080304030201271203050c0702040b040902030703290402 72
    0x140b4419003107041c01515038020845c007d40f001e66400825811013440d0f840c026950900e1342e551030440f401d0801641099032100c80c25004603c048800c803030305038082a2100c0c0c02d0304240e40941d520200c9001480401400e0000090a551036107206440c0035894902000c0280341c2201e1508229076030030341c1410306034601c080140102005210f440e03106030350766010b01c0984d24280b0256281e44000c0540080302a111a10341441c40c00d010700d01400620b500c5c02c400000e50117446400c402d08049000070641c0783c08052284040d04e8144501b581281e12038030003410b060780d5070059071140c000c000c070301040790120a0704052501c1040d243c0c1c81200da002c00040b414070b4480b0309406401941003043c0556980e16070030181c1c090244a80a00400502d1081c0031442c0c08240b892208524400c000c900030060450900320140c542c2514519000081000214010301c1d02e50f000b000126409800490080b21580019007422902e510640b0b10352103031109a6125041c11051079001c1228485952541c00d080d00403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 957747562 1250 957746312 957746327
    0x10212010b040f170705030102030906040311070b0711040e01180312060e04031101020c0a0c05100807140901090317090a0f03050a03080403050c01060b130e161b082710 74
    0x103c04e24611003242c0e860b4840720620500000c0c08000d00299600d00b0502c10803565a202110183d0000c1c2d00108256548240450307080c2c03c85100c5009a400e1501070340b42ca8581c031000c40611948a5950040b500c1e51420a01070480c440e0181001c8110144460501074551046281e500800500e42182844034044100c2c00b0703074005403d80341000c0e26210711050180240b280c1210168103100e04d4010b0001c000c1142c000340e0554205903000c00300c4c1c8041400035181d550054a110700442c1c00c0b442d08041003104030000c2c241d82481407500d2050269a80c98402c280c02607410f94101030300001401d1011801c0c03540300328000301400d00401039540c3c85c40d11295103c40002d8801010002c9003004101414031550650790f903503180d8002042a01d80d9940c1807021944410005843c6603960721000070401807001c101403040a440c00c01350403030b0b41120340841d114041d810300074424151354400321021030000300190005003915400701140c5111031040c0d01507100d03d9445244219403c511801916600030306 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 957748812 1250 957747562 957747569
    0x10906330f050f070c0501031d0615030a02041418070815150612011a0a140a090f0605270d1b09090b04020f0d0215070507051002010212010b040f 64
    0x1401480c107585454112924862280e941c0700c0c25030702003a09818070000036054400c444d4241c1b0100584400b446800200b8245002800350a42010380010045805000015034840004050325645112640018120781030700010070300801e00b15040129540d4800e00c2c0f06a506ea8040003001d12030324080000383c1c1ca00b02140c031101440d0801002c9080c5d0b206110f980c03480360300003c000c59140c001e03a640c500c8010f0401d1191812503070030784031580c84a520550840d0941c0c0d0281e07031160400c0c130400d20680300c5a48640003200c01c01c402d0140001c0d407400d2055040e40600360542c0e455546502842c1e039a0001030b184141c02c40c44004940c1c03002c2140d5544110700c10a20b0380100110404e40424600b0000c09200707071301c4a01c0c12410204200704009c40c24060710700c2284200d03403c0703141c076042c07034140001c440907000002d400c60107115803045a404000b020707140745403055003140d0f01c00c1c0c0c4030382c00b081c040c0412031004000f6230340103c1d0303810050f915803d4442c09818803940301802d291402400d010038164512 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 957750062 1250 957748812 957748817
    0x304110f031c0c0f08070303050c0f0d0b030c04060e01030308010602010c08150f100e04050c03130b0903190503091e0714131104080d0336020901090633 67
    0x60314414800d006203d00c00c0b403140c00c10080c038081c020505003103243e5440700a0850000e460440001c0001213020241d403107429011421a0038400407003014802001182e420550501ca46100c1a406980e42e0055801031310300c41c654031206526501c0c0c00750001034107803c00b07802e5904001025070295800305165a00c05910400340301400100310101e015183d00480d02500300b8000324800c07000a8001d80c80e550710340b80035503040000daa100c40c0009201c1c0000d40e081e454503804058103a01240c188007099800880000a80e0710708402d036400d08600302001d8804070302062011040140504090051488404c80c078012001000e80c9558001c3c2c50b1266401070002d240c0312404c030603100d07450302c0a004c141280c0d890010030444041c00824101c90f00306100b0301e60a44144400d0444180c171034060303840d000c01c426010a12a00341011442c0350f4402c0c05d1a81450b140c8160080400f45e61006540b03030082c06003030340015010b82485524500f69103002203c100e220394400c0091000001d8500240d8104000d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 957751312 1250 957750062 957750103
    0x7051f120b0f030d030c02210301140a09090302100c0e032508031803070501090e01120830070311040312051603090503070e010311130f110304110f03 66
    0x40002a03020002d5800707441d091311503107a11814894143c4d01038429018907400715502d804181e5041010407840100e0540a9001840104400d000d920000d407295400201200c50782a03da414030001c45c1c0881e84258010713031080b04191112400344c0b148200a00c408d103480c110300010640420b6a4551a2a03071200c041c078012001c0d49041024072202c0090301841068a980b03580d0303006101e403990740700c0305da09200703004900001821358002c2078001e044841d0780301c00d5211a8a0041140d1000d00c481c20f0a8540c0107003000300c00310400c2d07071480100d040d2030f1644c5084002c1c012020b02004680000304290149485c202d5540055110042034404072603010402d03079002e40e4846000c8490f8000e8030013680320503500d209014105038005583c0300680342e056046030402507644a0300006a0028817002e00b40781c10348030710903207981441c42105a00420015010840da102100300754111031007150a8544008040140000c108011440a00051007116066003610013400029150f880005003040701c13003040e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 957752562 1250 957751312 957751331
    0x60613061d0a0f0c0c0209060109080d120f05010602160b0a050f0913090f051002030c0904020a0e0a141302041d04170f04080d0816120b09040507051f12 67
    0xc54101d039520707410f50002400020302090300039080d803541c040120300c1158003e0005a940d48541070070b00c1211258801050311030b000d000240c4520b0f0204207041000d5440e40c0c9803004035803c82c01458024617990340101001050414144141328940e0868580c0c0081000b4407281c0c168404192800505560400c59842040c0d00020f01e10500d003890b04c0e060107007085007130001d0004a584414045008006913500d113200469402d00328407046510401c01581480070309024201a4003420311540303641003080c4232144d02000601030a0440c2c5c4004500c10150700b610215082840c40e00d140000b042c6030542c00c040c10300c0f048142030298500c913101f40d0b8042c80002014841c00301c0d20280c4503081e4a2074241e60f001c3e106c04c0092194000e000b0b10380c4030311501c00d10400030f80c401c0c40f04910031524906c0d400a0034110042c11109140c140c42000729503910781c5420f041c982d4600070344500840c8035100034141c1901c3c0c40c007407018240c00f0440740c100030048100b001803816044844179101e01c0040c44c0000712a0031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 957753812 1250 957752562 957752581
    0x304060e040e0f06040318240c0501050a0c0e060f090603040c0b0a020303100e0f01063902010e060403030c061116050a20150a050417060613061d 64
    0x21106540304a100302c83c89409a15000700304540114000c1d6500c4c006500158110603580015128030041e1201802070030075100c40d11900310000006500d01412440c900c3c0c1c40301402d4590549003504e59a9940786030f9540640c00460340d0104160540c0c4090170410024900a0240240c40131076000d4000040094200540c9242c030001804010b00450340354a0603840080d9280c0046844c1c1101c0c03018aa00400c0e20803429541c5171107041c11181d1901d403a801d201003201c40010b002000c408488903820340001000d0602000304440700d902215442100702400014502e0381c0c1e4480860040f0002c12080c00860350003504903070341d04c1d006900400e602c80071000036480b511400c90310300300c2e1200182200c002c2080c041500242940529182d8245000740c101510050309a180303003550101506410951200300d01c0701030316140956051507410301e5a01d1040c0345d10203903c181c84010680148080154a00c2c0c4480078218103c4048010401c0c03c2c2003034801c00c1c55a203603401034440c18582800217003c890 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 957755062 1250 957753812 957753821
    0x12091104180b040c0e060a05030307060f0e070e0f0703050702100b0d0b07030212060a15080402030f0a030507051203070903030c0501150807050103050a0b011e050f04030b060102100b030304060e04 86
    0x41d40860307081d0b028a09401c103110601503c0c041c1c514100b6108000c10f42500d42883d120040c2c0c0c10050140d498001d07141c0da4100203017240c50503200c141792070301d44a41d80e21409100c0c0000030030348011503c400d40381200a8859418000309400149032410081c4140950f000803079a4065200d10f100080d110b1001001a4041d4000765000f032000c1040d50405c154980e064002c2c00020881000585442e11400c04010a07526580200140318804c1504e4111b401d10815200d9001400178080e10011281d0446540c10164041400e4012541c00120101044820050314600c0c8910f41d000358103509001342c000701144070741d22028040081d0070b080d03401444001e6101d1040e0354115800040d4040d42c408025854503450304c107480c003103807400b40040c0e60110180512903241d10165240350440302c81d009441415289801070b4001c0290500414080e00e01c08802000514094507102500746461400203260080026441503040d0a16408803c681ca00106032000d442d400e0400542c0b0000906c0400c0040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 957756312 1250 957755062 957755111
    0xe0c03071205160e0a080c010e1201050f09070f0f030210021603060c0f1d212a31380901080304050402031e090d12091104 54
    0x358075000030701c400c0c9011451102a101003a413204400226542e0400c211801140300d00000c1c5c1c1c00190901c1d80541c4140041c40d00d40d0401004020040042c108013401c4400c02c40348050322004c2d00c0240000d0300c10030003246000300000d03d01a520141400c0c002c0d501c2c10060311009003e4080d440c44000464024060091446206050340e86020740c4e0381031000c041c06034800b003900480c0301c0c440a40d50041c420842d00440c2c54034030741400e0300c070210311052100e400e0008285c00103404500740c0d641c1d401075003400721001d41c00c95030303402880203100da9903000e51009121040c40e04c01e00d1400b0940d03894801c1141200c0545083c00301c00d540c000152581000078100c0745054124a040300700130080d27410105505030100300030f0340c1c200504210104050100840c400c2c0614421a03000b80020001490290001c0da40103c0c1c43c08015940d461400c00c0700000c140558000c2c40580041d101e0041241d4803030102c50405e050f91009100009594448035800401c24840500894983c41030003303110000c218602e05 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 957757562 1250 957756312 957756347
    0x501230906121f0c020102131e0b03042a0806240d050f01060b03060a03110d061b0311190804050a020315011703090603010e0a06050a0609050102160e0c0307 69
    0x1c202a041203240c50300b0510308000c03c1403600d001c2104492051081e100541e1210740050400c03400c108103030802002c1185601e106144480002c07440c075072480e014502172803140041020b00580d6109a00b112009000104411441b41d0f508010b140000580c060300140b0b03046402d038608980001e4040d000480c03079601a0890100c040e41010000002200d11004d0303a09002084016114070a85c01180720982c1c500c2e0b800300d026541403010400c01010300794a52030081101cac1912045640700c00a80c0c500c43c4071501c0c20020000103020458050280c9403040e070300a440136241140224130203c410081e03010032410000c000c1c00042c01c00000304458050a82c000b000c403100b0301c080a45645d441882402100224011014035101002000003a100003000041c859170650b82403545402100740024030030300c1301c1c60711410001a00c0c2c4416034001d0240c036a40d078500c0c1c00709090030000b82c6480d09901c542c410241c0c6500c1c2c20460300d106666029003002204034001c0e500c2c0c480d04000c950951078003651440c3d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 957758812 1250 957757562 957757573
    0x4061d3333180f0108070f0912060209010e01020a0b150307050319051903020d140d0908090406060c0830151201020309060a0e1501030f06050123090612 67
    0x540c40500303809480e403941c180c0c0540c0b41d90341c14501401848406010480c1c04034442c000030400e0140240c0c400380c0d81c00000d01e030009481d41d840070300c9150f400750038100359601e581c0061300d070915590140710b500350100280000c1404001940d12141c040000030701281441410742a4980b02d03a4003031007900e0081000500300c480c0c03441e4411042c000c00b40300240803102d6119128241e000c800c07201100e810f01a070180c01501d030810742000103840c4001d554444100c1480100103c410111039885010201c1d8016042c0c1d07600c51b03581d10240022105c0b81e1b084032040c00f004409000c0018000002c035082c1881840e07248240d01c00188100244a42045269640704ea128041044503480603158580d8000704a035841e04055032140618200e22040d04c40424617081070700050341112840c1c000c44210104801154051813801241e090705d19000e070003c44001920154000c280080f034003d15015190702c2110484881e0148202c48000240b80421030003102a080081e240c0d0ba14803107041011000300080c0c90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 957760062 1250 957758812 957758899
    0x41103010e01080d0c1218170d0f0309150b04022a07050909100b01050f0c060108070b0f0403030810030b0405150c0a1d04061d33 57
    0x20301c10009028141151181c1089220040d100300c0d1215110364000d200c0d960109880c907400c881c0310300801c0380818032910321000042e00c08500b15220802d80c0c2c008000c2d100d040104d100044c078020380300c007401040505040d41034001c14810f8100729203000d620303040051980d14550109003c2e0040020503e81d084800502100010301c410006241c3c0f80003c0943d00ca4a4580301040394102c002d8039621a1680903940d03a14910499620000300142c0504119041841414000665511004460426402140040000c01e204200382806007111140c4541003480031200136550b4000d511000c0c0c104040d12001c0750001442104c040061508040065058542401d005075500400b004500c0b0324080300c2c0006002600040035240c202e481640d5031401c07540015402c10f507840071444207030303405603a401000a0551010180d08441043d504803c04c46140989030100000c1805e080c6841203403c00d0068a03091270981c0105500d880202e0b02020501640343c20300d60080d007514000e8440d04202013000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 957761312 1250 957760062 957760079
    0x90902071b060c0311010c12020d0e010507090303090e04051c2601143c03060103061e05010b030115050c07080c270403030b031005070801031a07020601031104110301 73
    0x9450890003074854085c3d8681c41c10800c1d080b110780a401d580019010022800400349a400614040444150210f80421003000950071140103944000100310340e030104204140d0880c000c0b20041040030300006081c0740c19100e0325112206010031401e642c80740517801c280c0300e0180e00d02c03030703505020b5840c45401c40c40e030103c1c800803500003801204440800298030201394684401c0f0034042e07914801061850320b141510070300112104110045070381269035003080450720f003041424000d40c094034003c551984044240000003900c02c1d020360710305040000520110b5000702c2180d0445a03241514002800f0f0030204644500588045211500446100040d05040000c60100f40d0608941d400548021409c00e0100881c8019a0307220780c425000020300400d00070350054101200283c103462403107081005010488204595100214006000500610045542405c2d605054211400e03d5052440004e5581c400511004120048044100081d07455540208540951022420341c481d42c403030458 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 957762562 1250 957761312 957761327
    0x62e0303080a1d0d080712020c070e060d120e01140d05060907030b090a150b0f0705150103020d0209181e1209090c0304060219030c020606030706090902071b06 70
    0x200704950502c29044000055603c500305400310260062034580b41c468030a8480c490000c1001c414040c00da0140780b00940c0e58001008000344c0d40c000f41003154100240c00c5070310781014007100e014514052520001610b8242c81c0e103110341c00d90410032510400b400040360020481084141018004140c1000103c5182c11041c01500100c500112503664648114100c41d010701d222a4403540d4400420803150582d8840e240042d203010a0700300d00b9489105540540d8004021030b411302e10001518424020240010125004402c0920201c1c1d4910b800003201c00c000e0540280c4190344840200301071a290311810459100d945064565401c0300218601081a001c15401c11500500e0194208500000304982c5840c034010940300590b20b9604004a244e00000c0040303420580c01c0080095070b40041c0c1e050641441213540105445101d480300908004c0040c0c135181c000da101181c240491a081010310342904c004900068454102c0d00b02030b11481c00d007903520841e840401c0700129041c1c0d8071009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 957763812 1250 957762562 957762571
    0xb09210c0f030d0203220302040c12051f15030e010606030c171e04050c090a1e0c0f0e0307090e0f120306030a0f0f0606180606080603062e030308 64
    0x5001c44101c014a05054907503500f0b041c0e40c03006030001c00c607418804070020a8a4040c021188404078000c1c0c0780d6001c2400c41d101c509000e004207049280d184010543e90045581c0710001110f01301d540c0141c46242c1a1a11181c05400114a07040c1840396041c1d00c40d52011606244800003480417070743d0b90074054010301407440c207000046c0c2190902c004c440341144185010328180341c800d40d000c458074800d849101c50003034001c8a082c00340850b500c4250799140da03200c3c01421411000140036507104125901d0060311a540340c1c500b400c00c02d440c00b0980e0000104810307001703a810842030f0540035000090418049803c000e01d054036001180701040c00008900b40b100d601c020403034001006100154989000890340300c0e5241d48031704100800240e030484107070f0a00c1e104070003815040f04142d031a201170b60380a4002e08007503240480c107502c0c4040340d405104020701c580d0400d0081c1e03081990110f51980303801030203400190f400c0d601124034680c045500880200b14400002140c549038a0010711540303060702c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 957765062 1250 957763812 957763819
    0x915280320030403031d0304180c03090507030303020d02160c0911071205130b03180706090e06060f070c060507020405060405070c0b070504050301021602040e01020f040b09210c 78
    0x11942240c00040241a1101c110094100341581c1c1d0340d5804501074244221001c15005648a006484c14070402c0070700042e1102854001a2100c80f4100108a55550100354101070070250544003043e001300d04001626018603016031b40d80007548000000c1d01c0707000e404a80c04d040c001c4004080c4070010820030243e4003800018450b01400c800c5040382e0740201b1602900c104240003070801070b24001c40060840d8044402c141c8403180c0e441101c49055001194040f010101c2e00403000e100104c1480500701410a80c2402464941041288108076200400403401018001102e5240452a1055413907881d805190402002e865050060050300a103a0490141e403c00740819001d00c1c260045a100c2c580c260341d0790b540d600c0591136400541c0005040d600034010300f08404a1291401c1c002842410381152044d1072460700361040c40704450300000e003200e0316441172192508039911a41107404507030b004c40c541c80d01c40c000c3c40e0018035020013212000d0104040d5604030301c0e540c00040f0714000c4888045 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 957766312 1250 957765062 957765071
    0x5010e160e0c1c0603200405150103181403040906080d0804020f0a030c14091506031602100609270b060d41010b0609152803 55
    0xc042404406a90240c95088410303038000507000e014082c0603140e4080e10346009031403a4000c15814084600c1500141e405d0311015003908040341e100a40b0382076007a42990700b08401d207400c412102e500065565403904054580111a10002071041d165440c640c00594007000400c0401ca01d40c1d40f64420300c142d940060030101c000640b03100202d061130174080c490f2622000d0356a1503082000a14101c0c850700c1c7e01020030b49010010440752103044d400b030207040040500c07840d2100108003182200510302160713025640041e00241e00c8040a89400035000000d860088984400a0341404403403e44014070900d04078001031403940c103401c05008219040b605e80c1030021000003040b4480c4c2c61680291160110b2808a485e504000c20520303c224010805250211200141d490415402d0710200506801001420030104500c0411903034031107aa4001700452287c1c1e00200d46940240103030148543c810380c1981014411490450b42a90031007030320030f548920f1003803602a0144083c0c1d9480000703480c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 957767562 1250 957766312 957766333
    0x307090e07060809190602030705070507060806181b07050a060509070306061509140402130e07090e01030b010905041103010c031e0204060801090b0a0b070305030601080c0702093105010e 82
    0xc9450414800d170b08141ca80452501c0d100c0402a610242c0b42400f003042c20005500850b406002c020040c1401d995a14407a081c003c0070004800d03510040c0406020940c81030100110b0044840340c00103c0d616080c9880310040d08001381810600103002d04000c0c01c21042100440000c80d0000c160bc0c0301c3e210400c0029180c2c002100b0f443c065280c0e18011440491003407000045800e500d03008400010710151810594500c8640c8001c4954082001c04800c1028000300c16003000644001d000c00014109242d8596250180c8920b4103108c0c405429a541e40450140f0954800c04807001c2c0c4090001c0c445158500001030040001030684504100745010a11081380369008981c02c8503140c0c4d40e0408680d007482582d00091080103044c43d400800d9100001c0d0320920000030f8030485000303448036600c0f4a055070024021510003800c2c011242d200300501401a44e851044c10340007000c03401815031141a2600e01c00c99103507201038504030710302e0801038403007081070541089454865150170703a10b98040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 957768812 1250 957767562 957767581
    0x705040305030a081b07081b01020c1905012901030c02060702340611010f09031707090512010207050c0307081216021c020414041e020307090e070608 66
    0x16a0100400c25002044006a014030400f40b2035044260016000c0e2204200f0512444903844003104883d41a008100c0b09107a811180300e500c001e145041c025840c0c040700c01240c03502d80560815660f40002c0c507103016414018254444007201d8406081100346428140c400880031401140182c000780c10107035100e0b01c031440465114003491150b0010001161041c0c503c4228000307500352841c4000404404800990045070420300521154842c407600c1e07a04010602d083d00c50440312000e42c5410600b4000000f94401f034400d2403404441520807103074641c640100c4510789030354405944070709524400c5248060641c01000c81d1813041c001c4981e41403c203030526885400500c00c00703040d50425007102c50412291070003069641e0b500d1000328200c11450780054801025204060604443d10381381350f01711300b0103126609500454003068103142c0380c15550043c444080e1800c0c0468803816031451402c54900700312040c06048200b800384111000c492031107540380203500c038000001e0803580108000a8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 957770062 1250 957768812 957768817
    0x150a182705090114280f0905100c020a17091305150102010e0d080709090e031e03040b0411030708010516080115050706020f0f1918081b0105091e01080705 68
    0x6000340b51420311070352400c0c0d4620368034204800c1e020310405d0392004100541d0152007101d2025180302000600e4100070b0a081c0c1c80c1404095003429100e240806041480b50000342034a55503601c40d07601c641c01150002c20307842c14000c2264450304201c450003613050b44001e98022902c100da4185e1021084d22030303a0012400c0e50f10210580e1000d13008046081021441105801d52003403003810318407605541c8440c100d044504981c020301ca140c00c0407a2940c407031000315215100015204000170b01b98180b58a0b154161b5074003400080c400d600340c0d12545401d8405101a100510b4940020011464a8210080b0710314550f5132103400100c0000010900c95000d1702c0020204099542d003904244265031805d009501490150030800024410000c840381da0400400b2444070b011910000f03881013100c003818801c40c40e203400c84e21003170310441407000400c00202103012070005001001100441c50058070548120f44003290814982417140e80d414040000c46200d0303003000e1703071945019926014104c43c41e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 957771312 1250 957770062 957770081
    0x5190c08060415081603030305071106060d1e2103020f0d1a2d01020c0d0615030f0804170d0801260d0e040b150a1827050901 55
    0x20011400310710035042542c8107000b10103044808460a03502c41c540c85281a583c52209110b40d4a003401c02c3c402c041e41801580d4205415050050001884a070740a8440000030b241c1d900030303501d90f8451424010a01d28900b491005581c28401340001810310300203070f00250302c400c40f5407103100c010014800d00c40c3c42101c1c5201c02102c0c1090500302c803030302010040c00700d58080c60b102c40030614403944e83d40e5542c102c03082060f00c06c4129508000d400712281444010078101c242c15900059154011512000703100c400f07059010000080f09000c0341250103541e030b800d81010b400001580207900c20002e030704008000383c41150b00b0314048e06201e100074a035181100c9061400044800004002d040c41c0018030b4141e018808540d440030351300c04118603242c0b080407420080041c2404020440c50308040c400c002c0a407206413a18003150f50100d07626846403140c80e00110400201414034060403c60300815000742601c210184ac9820070070307070561046881000c040344210724002c0400d5403800d0504c2000c03103e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 957772562 1250 957771312 957771317
    0x303030605120c0d060b04020a1d04140a1e020f040503072c04021c06051b070206040b0c0f030d050402130207020d1103100905072c0a090317090105190c 67
    0x43c04030000340b01e501c000c83c04084504644440c0c1080d161780d901d00240041c12200e503584100e502201d10f5145004402e055020b016910f012901c042c00010100c60b190700145040011841c1c030720041034607104030401881d089000784041040030586244100500403210200c3c1200c000d42c0e11440c880044202e04048500742120449010348600003c19100d903002e4001000381d660010a5000503001c094008011507204d03a85038204502c284080c00c81e000aa446026064109101540420080d2103180180b45a5101c04202d06100b074030100031400143c0094000e8940301c0c4030f407070180005030100303550803840f03081c11208012559200b44240d412142e0010b20144082d042502c8078820303401050f080e0381d054010035640c04119661030040c00c6d2400d2180d0018468107140c49103180524500d640341c80300350f030b03a10a001203d02d51041081600328500c00c0e03001515402615003a030703102c3e032081c000c081038807607140c1080740003503065003c6845a000320b0513501403441c0a0000c030003112810b0700410701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 957773812 1250 957772562 957772573
    0xc03170307080415090506040c0e011403061f0312050d05070f0c0f11040204120c05011e031a090403050901080702010b13200c1b010201090c050d03020703080a09030303060512 77
    0x814542c20021202204210f0f0014001c5c01c1038841500701031084905548500300c4250800840100340c8200340140480f114840c3c002c004140082c1d00c60b84042c24400800144074140b110129059140070020350b400880b40d005032000302c0b4064a5504100032010702c4500d0100051980b5001c0c0e00006803285107556110600151956800c90342c05845500b5035040e00c04062150080d11a4401400038050038614840000d41c0c40c0b0b4101c240000c2c40e00668100304170759441201068219125420b03445c2c032400d02059680d4000140c01d820015412050341c4024000309100c14980c1000081000050a80ea40d8881341e9841030260f00341ea10140416170000707090440311240814030750042641103010550a0281300d00314018100c0f83d00001c0d040010398009010410741c9101c3d118501d0b0001900780001d2001401300d44410040880f1031144900035017149401d8820948207100c001d001c4c690204003c1c6d103940d600700d0001d225100c640012408246050000310745490720861808104448100604 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 957775062 1250 957773812 957773821
    0xf030210051b0708070305010b04060e0f0403020102070f0605060108060d0b271203010510030b060d0515121e010e0709111201060503190b03211201030c0317030708 72
    0x2501da41c03012054001c0e9203000c00003100035060038044040145211002845401e0942c103103182180c1d0340040d140d10039450f05e0b108000d9211540407803a030040c00e072922501c4903a2141000d0340a846607034002003034900400030610070002d403984524099a001ea91700c980e81c1d41e5020500c02148401c50740940f101968a000440010803458100c0e259646c1846103450441b001e0109880e00c0382410826503070507004001401542010b903030000c4400ea40307290600007100c1000c0850b66602c1040310800c0c1190311a0f00144003011094441b83c0d030800c3c0680045d4605d0700d440300150315818803118040070a07445000280d42034005009582e600205a0003400c2010714080c014001068448071009051206220102410b142d950003203000340718035228241e833460160342c200c01081c020388038510024074154004e04240c90000310200010b03081000c00c005105034085008040c02448004104030740d0b1180080304000c84400f043e01242e105614160642c0c041110007080e90008450400c00034041c00d0024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 957776312 1250 957775062 957775067
    0xb0310030b010909170d0b0901090507030c0216050f06070f0f0203060c2107020723040507030e030d1a030d020a230a0b1b040603020c0d050310030303230f0703060f030210 75
    0x10071b04081d0174500003441c41e070114042100c40409a000010141e43e40b0304002480c0e8040c0140c003568070040c405005001031050303034500c04401074007440340a03444800c0b001c4402c0e01c450048030702c0030390080000b034803001041c0703004141e03c45411004c034002d0140b5000300705242c140d503065840c41056040c8118a0380240285100d1546008103071000b103101d0f0100c0014003904004a00702c0c0180c21100202d410301d110b02c14401036034030141007001094580300d00708007085000f1065400c1d000d01201c0c00b05a80e4542c80d00000203084881081d640f5000e001c140c0c0c61050740000320f0310500781c41140039600302008090b03198400325000c03a00c0741790364028481800000e0f0322002810382c000d4010014200c03001e0004100b0341c007600b103500840042f9900207100c2056060400c010905404c8070325244c3d10714a82401d28445006946c07200a091645a860381e440340601500601003200c44210000d10b03074980a0511406040160b5640d03002c00e2a00c41c01154521131590846d040d42d802401044064120712005c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 957777562 1250 957776312 957776317
    0x105041701020d0e06090616080a1509060801151403060403120f0f09020f0301062301120903091805060117130506090d09210314040b0310030b01090917 67
    0x40c2811554200000164103400d4403c0100c0e40351400020f21042c60b004510520b0a80302809001c5c0150101820701c0403540e0005604e070340100f8001012032005130500f0719942070105900321080d001d00303040002c6071400d015848171041007061000120901d966481c0d00d0400c501d01c0600e83c2c3c05400420008010a0050f05032a0300708544501c0000d600310034003614011102a0071020b1021a194600841940381c0044c0c031110702c203400c034004c201041c54042e8000c41005c19240e500605480e10035030b501282e01441c0010240705405070b05000005189c5030050041115000355100546d000c0300300c0c01040381ca889014818103040c2c48408d5111455010b640c4a554000d004000442c2d00301559400540184003183c01801c40e94010403400c1c886000c060130329075007a00128050b40019402c0c0490900380500401104c3c0c060400310f480e4441002881e0082c811a000b46e01041030010620130ba1003184840b9600701c0c1d0207441380c890a40d803603845a4003a1003001c0006482010100c04032580e100e0090300 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 957778812 1250 957777562 957777599
    0x15010506190203041703041a031501030c0e04090831031e051f0b04150506280203031909031706130905030306040e01090807170f0d02180f010504 64
    0x1100d0809039686500d00c4170882101c0c0760485504041000c000c0207614200c001503040001d504035081d0701c0c0100a00180b0f4a00406607410152281d10020109000d82a01d41e03403480050024401c010560803d103480398000c080303c4450902c00d024040b25140c0c00c1c0c0361000444614000c1900c0ea9245840c0d100c0c0c40d4035000d1b021038010418600d03074400240208110035a05030400a6124007010943c490b1040340d03101e101c114056418503480c04900d00f40441b8007004e64008981e141d458103040c2c0d0312803140700d01e8810100b886001082d20091034503000000f85200e64500e05040c046d461180203103006803144840c000340421040300c6807450030203a090001e5400b01014000c01d148401c43c0303041c041134880787c0c41c040d0b0300c6030400014003040d42080e00609542910b2100207006070704050761040164400c0000107407001c0e400d1031075000485071200c1100c1101840364491902c032040c60140d04025408105803240c1c2c945030102000c0181440c01c000303102c1c1c200586a131414a03141c1070304681c1c050407000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 957780062 1250 957778812 957778817
    0x30d051e1c14040c0611120d111b160b0d0b1f05070b0c0f0a1407201009060f120902090703150e040b0c0903010e1507021501050619 58
    0x2081c44458051085021203907514881280368100b904041140c0b42260f005082040403003031640c03840b0400001c0b28001890120000c40c0c0e11040302101c2e0004141481c02145603510014848000d1118119520f41c10030103c4152140440c00181d080f034040010309c94414052014860345503480303c01d5210f00c511a5000d07240c44c82c42d4401a03c42c90a4403000504540411404a200402d0142600c5000e60101c0b02e40640d910304420149003070010301400e00300d5800c002a048409070842d449034142c0750440e51102c81861403803204558042421021044603015030070464404004a100304001000c940c1c90792181440d9a0081804407500d00c011860344103030380d403240e02c0c03400140c0703503441114410724059500146c408010366080c9030b0b440951313010302c0b403031800c44003400302040d0010030094011034448a016540c11030200441d0241426034481a01d600694000c0e6070702004960580d4410110b0354241d504012010b41c0b101c00e0a4001e025042d00f041c410700c01c11a0040c1030007400001c00441c1e0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 957781312 1250 957780062 957780097
    0x2100f110d020601061101090f0b060a031b091109010e090601140d021b0a17160f0515010602070803040e0408091c050c0a050f0d11120c030d051e 64
    0x5903299840c1051a05854006921040040003003a6020002c50741c00c1c0712280c02800243c0c40c986480030030004c01c100c09000c0c28003043c080f41d031585d2010800c00043d40e111070030071401c1000700e514100c2c6517810f1007410350450401244031400b0070508200c80c0355010517107548410900700c5003405803c00e4020083d0341400340000c24400d0b80d004100151540720a04680541d452400d114441c40b462415203000c4d080d940500284000545d1a400030303c045032541642e070762900003c010a030302e45002c9107805807540740e019060300c00744107000ca40c9403c0942100301e058800e0340d030303a20300300d9417100c0c18418140980c00030300052204490100b0000d420500400009040c144403d0004084c1032a9100d40d0406030402200d039800c204042c012819000c20484d46c00b1a0545490301040b48240c10842071480b82c01d10004080810100c500d0303080300c030380026125404440210040c07070f13607402030381040360300c64414440c440342d00520420444416024003034007130319800810301121a841e0840d100c0b0f500c2e0030400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 957782562 1250 957781312 957781337
    0x1d16050d060e010810020304050316080f0d0911060301080a02040207021f0c050105090105060a05010f0c17120f010305030a0f0c240b0a05060a1206030605040b18030702100f 76
    0x501860002e05030003121080254980040c0030b14280d00b00300d402040c940103004000c0441c41c080141d03004400010043e07032809025140010045c0700350007501c3d0807a80040744400d28040b0941c0480442c0740b0444c0e0f078040090303079034040260703a0009200c0c3c19120ba200b061003100508013600501640743c4042c000703094204010340ea4144a2401c1c400076400129550900424001d007405040c3e0094207408c000c2090381050800308040c1002ca000b02410301c034030082914146441052000039841c2c1058400074480340c40309420ba1194800d84007650810408008200c0088944081c503040740c3d8003078002c4d4038103240e00030140c50001e2804198000d10004035564004600009400b510386101c4000040c0e42001e000c010104a036041c045281c00f610040fa0309002c180c071642c04882070319549040c5100d074035800300031403005420b80740c2006008030306010900c0200082c03171503403c0c0038070040019510160611a20550349018100380690b0100300d0040d202d248501070801404209a00e00e03000050000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 957783812 1250 957782562 957782587
    0x1e1112070e1005030906040b04080c01050906161d04230a0f0f0b09010302010810091a0301140c0d0f020c0f070302010f020f030706020904090c09060f1d1605 69
    0x403034040020a039551140c01603031901030403503494800507080240c254284a8075075656000001c0004100991580115052281031415522500700c040024001ea2801e01030039500c0311020354088079003402103c03a1901c4c644c00717042071602481c2c00300350340d540c500f003030000700009801d2203188900d0240308408280f42c80d040b4500c8180c4030350000c00000c0780b031907480c6000008640310346940f00309161403c0700259060b600e00b141c1c0350440f41c0902c2c1540040c2c903100400f40e0507a070284d128603000c030300d010910201b0b1100d18040ca80c0d81c2400701c000700315122039440341c00100c21017222844d04012003004a41030110f171a900042810001b0796006081110200c0f5052801c2d0314005002c41c2d41c0d019070320400442d82d220003d00c00303a003403034805000401507020003030381d5030300070340c5401040290042080c2600d80c4403948074003926038120710744402e0180c0e25403c1d43c0080860b8081c41e03080100351007000c202004400c0c04182028140d4224544a40d242c0c1940c190341c015226000c81001002c0007003421440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 957785062 1250 957783812 957783847
    0x3040602040506042d0b0306040b040f150e0f060108010315020f030f0609250302030a0b0a06080708250503091e1b040c2708010c0809101e11 62
    0x100040400a0515030743c3c41c0741030201d1403280b003550014030080083c1b040c0280c80d8103172a00000c0684000c510344c000c600006001e003244000451801c1d10740b06001480406021b60a803c4441c05400070b010380e190302c0c3d048081105c007280c031180810040001000041c40d01c0000c8503180c400c03042d0041c00d01e0b0b800d1440e014150b0050710400f40001d92034003409581e18280d41c025402140d4852203041d080b100080281000c00c54035040780500d64003100040c02e28506400018400f00020054000113480b00c0024054584c1130f82d50400040e01c040c00540800800740b01d2071550034110102070219807501c4000c646550000b03111820f180218150b88070407400300c070071504400f80070070058041d2004101904c61848500d9690318420350608a44a1040b600090742c0e6811039420240054094200a00a4a01078159128000039032078008042e154070b910030110750080242da002d640b83c6028505900b4151509101d0b520b55400c010030300e840700d5011603800b492040c00250065030410180721100407100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 957786312 1250 957785062 957785069
    0x605130b031314010510090902060405060f0307090e070c081c0608010b030f07140d02030a050f0309011b1502090102010f06080f070f0b0307030c0c0b070905011103040311060304060204050604 84
    0xc29800300060402c0801c0420480d20f01440c0000c110518000f01070500d0108140f0071903494a030b0351450303c0d055490301f40440d030203003001500032961210314107484c4032203520407a61203001490f12800458002d917020281030080d03501d42d80c2d15105080c16142d4040950043d5070304001d04c0c0e00b446000f001980e03030b8002c40f401441c00301d00010f100304121083c5800e05550f44030b100b60300d4000c0c40090000010070581d03140200000d54089181000c00e101091603d5a14000500f092041c1ca03190510150004000c0849503c00c2c1d807085041c117110304940d06a41a111070081009400d40200100c2003203503400b42030b030b01d90148004504190813400b0001100e40c00e4011400a07000000390444004040181074010f01d0303200c0161181138035211000e1100d000140c412000c242d205c1c0004010540300301415407016810071500321903814540000741c0700c074000f8030800e800b2a4a0703001c005d510b80000f206540490382c10104406d16502d5407010171400368401802114401e45c24400800d041d203400c0080c1024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 957787562 1250 957786312 957786331
    0x20a1118100f060e030303160e0316080706030b0609010e0f0d050a1a0c1e040b04170d180e2d0a0b0402090d0f03030905030f0a03050a0e070605130b03 66
    0x25042c250b44a004000e950048401c0c040c8068038000e0644000003140d9204840e0322135a80e00710308021044603400c2e020641d0315070500ca691a404803d0866801c0e54007150705103411145002d541e85001c3c3e055603a18140944d000b0b4051203840302d1075000707500203045c1c0d00005100b010300d0110030000451440040130700b07499039400b042c600010445503aa0b54030302a6865103410f8868030700b60700d144034180b0034440001200341c03500065501d205801c00680d00030717003418100d03e0f071600c1d1160305400ba91603004e442945c11340701c1d031002915241d000300d6030b135225040e6101c6516903003030805100245103a00030381609110030441c40100d2001c41d080c020000240c905950390022804d000300a8815200141e40c3d0314450b51041007600b01c1561028110540700f50701c42414541c240c8079007016401824000f401034014000000c43c000405800c800901000d5400c0d2010015511400610b030115400341c000f10300c03141c3c003001042c0245c0d800b0350007804110021055000c400c6803a81015121a001907642602 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 957788812 1250 957787562 957787591
    0x30b040f0b090d180305030412051216110411030114030a12032f03071101090219090f05130201113307032d09082706030403020a1118 59
    0x103103500c41a19200d244d0503034408503c1600b5074461031748074419441041a4071448038112804c100c4184240362026140b8001c4070740f18400074543ca00340b1000040225500d1086421505a0b407809108021410000020580c1140e0034118002c07540c1842480b0968988108140c2c4000601d0450513020764000c141d0340850b0400f01250110540444480c1c202880040b070320300c04080d4241c0314141e036441004c134900f210100f0f00300420640140031200010390458160108800652146c0040c00e0446240e200c0401000c0e104611010494401707540062045c048030341e0202c090340c030424104007252400000d0314604481d000346050b0a8407225034910b045001d041c200b08883d0402c45940360301c91035908040c0010780b51855011061090a080c102040c1910310000c0160051684401c0b2610351141c0c001342d031680301c1c84400084a190514921441c09408030340d4410381003400940703024680c9030300184a007046a039112642100850181038028003203d60b2801c0715501c9a41c5030b401400031403102c18 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 957790062 1250 957788812 957788833
    0x41b0f0902040504051b0f090135010603090c12022b0c0b071104050414011416020705100f050f0403030f1206150e0604080d0521040309030b040f0b09 66
    0x1620380041c00c6d4840703a00c002010451500301d0100700c44d1012038803030035680d94180100c010703a50588200101700401020500000141e81b02d02070b805944610081c40b0586a079803641e0403415202143c00080001110040801c080540140001c03e228401403604414403114050394852494064650190500314071101050110a0746140d01600c1500086403505002c0c0d2904240d04655107a541d0082e9659800a802e1181175007555070007211100080c00240700c1c0c0c98603400e0b456000e540542044030382003419504503000180c1482100d0000d4144100422188810780e94042403141d0401404020846070400881c00002040a1440307078480c0c83e03002030f0000008204981442064110600d444814000518440744204010f001890150b00709440e0344013144c50760203076511488642c860400d07090241074018016100d003940101c4640c1217801c3d04110301c09a42419100640452110842400800d4070340700b0096115003d55807158000c240c613560307003000c8101200e20328180e40040780b419 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 957791312 1250 957790062 957790069
    0x32603090d030b0307121115030c070507050604150807110106030305030f1e0a0902030f01020c06160f090506090d0c060810050609030304150c050109030c060e0102030f041b0f09020405 81
    0xf40740d000042d0f00034a0910309203822030b44100c51010016220300c8010503601c0f155511452502c1c29516000021034903410042071501203600803880448a60082d001c0c00f213900c1c108402a142250340d00c0140200d0001d0661043e11000c0000e01161f040000742c1800d07500c100401d00445004500c02c1d0b0f16a990ba1a100180a00074200601114030a00143d0000b0102420301300d000c94104038140f2000800700d0300d6100180c5030100c070110341c2144e5400841c82040007440400c00d2482114000302c1d00c0300075031000c002200c540c3c0c0c0b41c680201c045500d4140a0015080c403c0c060002079502800c0b207011030000361210070010348554003400001d6120001c00c48007000341040319004180076540d444c249990100004c0d141d00850140003500317100880080300035840349400814140c1c01c00000c211480721070900410300b00b21113000703942041c204111698000014821030b445222485811011901c559850031006601800d408a0f22502c003100803403101c69014440000305101c041c0140d0303440c81c140c1031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 957792562 1250 957791312 957791321
    0xa0c080610121a0601021501150f0809030d090804032003010f02040317030c0715140f090a110415080109110609012307080c061f0807032603090d03 65
    0x1c565041d40d40c00b800340c00581c562499820000b092400481e059840d00b0040b441c10285003005002404207600004902010480610309201c460396408103d8451000c15681d0711810389480f45c950b0301c00c005100da6400198044e07184c3c45d1145004500d030507520f4035451400300c1c0020100303483c01100300c00c00041d40303000d20881c1210004407070b00394240340c0f079900da082c55a0301c1d0800c811303c046000000100e047da00f8004803444150302450801d900c2c2a030203400b20083c58070303540c1c03002c0d20301a41e40800d171204020001540301350101001007400211316036402ca40917114510700e6802644030a01804108164964100502441e07400012a05014140801050510782d01540148410028620240d92000f00407000050f1500c40e0007600280080b4542184514a800703090031702e0101c1c018400e40d8010071000d000341d903400100c0c0030640da440d840c44407160891023503841c144d100300000c00c00211440b00b502590701500000c11712291007008042142e43c400c440d1081e4070f03001a100440d406415104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 957793812 1250 957792562 957792569
    0x201090909110a080c0307091a150c010606210b01170a0c0e060a08010b0309070302040603240e1b0316030f051e2e0c050d060e1b0304050a0c080610 65
    0x1041031740c0d0081702094607651180541d01c400d0b074654600e40007600980f09400d200a002034104011031a51806a03089a004a00300e10714650811900049540c030400148246a0a0820b0683c0c0003400d100d58200400000428038180980c00d040c1505120400b50b40741e100c0c0c54003160206a824500000900e4030109c00f27012403180c0e03414029a00441c0c3d2124485040d6240082d6040c0d40351115007400c1d2070b00e015944001e500a00b03008011040000318842c0301c244a5466620102c4080488009001d035180b94049000d03650050695030744c1c5850404041512810107025580004003807059103090980c650010b895008441c80c3d03640400c034040110702107298000001011065402040f5500c68036103001100d10b070b20391a4408580c0c084446000a0b00350500c9008001d084030916020309141c00c010704503100341d442c0510000c0d1800303001140600c521407607621044035000101d50190075400c050300c02d070f400303201e14506c180002e50020940005030020000400703561801030440807a03040e0980 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 957795062 1250 957793812 957793829
    0x1c290a06050f030f0402031c0203340b060a030501020c03090f030304060f080709080118060c020c060d05130209040818040902032a1507061107020604120201090909110a 74
    0xc81400d960608050f0b030340108801d0300854143d181c6000091411010011501c000c00c80c071800d04140540010080482d03200c0000c0d650040350300d9208041d0001e0a4072038121031404c01404100002c0c82c540740c0150301c03600c0200541030a07030f02e1f07880301ea0032a0090020865280c0c00007861781d00a141980030300400c102c08800841c6440d060480081031207a0f2180514140200b89000c00c20b010f008803505009081024000c00c0342205202c40d070184100f005009a8100f89040d084504141c400f1541c103050b98405440030b40341924000895004180c010403554205e40090702000040c1d68510309130303000300d0047e0b29107615427501042c070355942c0024071041e5200701d00e0701d12010016180443d500c696110710134441860720047d820460404101040d2243d40004407410450850054001511180e8010071040015415150702180188660354000c0d602c10001e0004000790480640030068991042c58914851035a078100f2005841c5410411100c0003405240b2410300d06040450000801c500c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 957796312 1250 957795062 957795067
    0x3050109050f0c0f1c090302210c150411030a0302060a050f15040b041410030b0907060e061608040e01081603080f0c1213031b06051c290a0605 63
    0x1c54a0f030f045210760b004560452401107070340304481c140c40c0d03c108061450000c0610210486150094a03a660f015281c070500825542d846039014600c004e6414200c107401c002c100c180c4060003809065200200119480c0700008481c1100c1d0720280020380340d251003a0010b02c0c0c40d060400002043c0c6600510094218a44100b0030900041e0a10080c00e0440159000660703030314110045006401b050704004148030f5154113214a85c6509601c1e10202d03030196281c080240c5031a01d0842d100d205610508000464079184004107190550040c002035100038220f003404c98042c1c0da1040c558000c9d5000070b81e02c680345c4004010240080c02000101047c01c4140184c007800c503a0340310558050004014a6044045860f0140c03d40c200406101c1c910503080503900c0707011403c1150750031100343c001190780c245030441001881612503449001d5401035180c050505144420603601780c0c07010b06100840948500501c0201c10080c2e601d200c80c2250044580041c0e1206814041c400348944c1c402c1c030400804 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 957797562 1250 957796312 957796321
    0x60106081302010941040c05070f0212150a060f060f0f05090d051b04060e090c13140403120506030d0e150c061f060c02030a1203110a03050109050f 65
    0x2080d049005d0b1441031441464034510702210000f41c01e50002c598110100000c0c2c1700c40300d080304d054640103900d0111010711040c0100482210117000d000d2004096410419008005142905104001d01c54032412185a4030355030601c0482c590056801144403907440c1000e005043d4005480c9000c0c2880b81024001e0451070440100b4440b600400c000420201040d0b4601695444c1c2c04180c40780d070050119025081e40005d5043c440d142c888000c2d20940c5000310014074282c9140070f640c405c0c10444007030151050410144010705107500c1c9480d005907615080390b2201c022510005016500070307590390000380e1050a181e003c444014001c64880d500c403650540c80c0035441000b4003810394059a0b0345005c4007071140c032140703070b030141d02c08031801d038020f070001c020004c0c0c00c2c0040036240300280f01640075916912002620044412103020b505900b004d040280403c8461040c018120802d00d000140c1081007a0100102e4100031138400010340c4074001042850994003500790000008039458160303040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 957798812 1250 957797562 957797567
    0x708040c12210e100203130807051e010201091211060c250c030204111806090105030a20030c070c05090c070318050a0905070f02010b0a0501140702030f06010608130201 74
    0x14814110001050410882c1c2d034a10300c01e59034014525405007500e1410480907002079102d80014110060710103a80e0320005000ba00007450303004644018001a02c40c01e0545410001d01c000c0e100c98506640d2154040c1c40042e04403541d03000c04d0111942c89003040755503073b01c019040c11005059028940703418000b5056000039407401c401c0300c020540040a54180c18589110400000c1d88003a41c001c0c50b115030382c81d650381040700a0403074182845c00b00178017104d0002003000502400e1401c07030029400b880020b1080c142c603400044660300b01017010802002c3e1000c100d545a004456140210001103960f13001c03c5000001d00024140c211800302c039030f02d4481c03118043c5d40542030000c0c0412000b1010010f07041094940407020b04800b400c00c00b44141c494000101800090352f410000920340400d1188080c8107100b92805904001d0544100d40e1900004480c44500444002220b0008000300f100685c0c0800903600041000400361005d5031500d240038080020040000f0540d20320b00f031040c0e0040c2c6c0e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 957800062 1250 957798812 957798833
    0xd090e060d0326060a0e160311090d051c1707080705040e0403230a0e150d0f0b0a1d07050d0f090b15300f03030708040c12 54
    0x1105807a4818044200c0c01c044801c1d50410072403403245035212030320251103041e0560240c481c3c4001c1c1c1c0c4001c882d5640d5010402e0030102201c0b4280c6000c012401c02c0d500c2c610a1300030708807108812080c141001c2c2c40400040c0400c034020400c60300b60348009044480d80107480f103440d1000d5000e04040c00303608086442075210301801001310007004a06000100d482d8090004d40d8040c0402e03641545041c40e10345000b5101c095460300030080901090b00302e03800741c0254400c58907056850354400c84034161a000344000c80c280c03441030b586242e40030f101075030b00185107100d50041040110b80209190f9040d209000481c101c0317400501d400d00e06032039500016007001480c02e8025240345406a540c0c0c130590b0050000b80000200014030906005149040c404846100340c001c1c040b1103415550309030544100540810115100c40700f0aa1489038400c000400c410040c1e051600e060948105003241c0b07100768110341c0100d0307284020440040502082c40700000c0000301070400707032507000f40304213568070ba06030742c00d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 957801312 1250 957800062 957800071
    0x501050d0e07081203011a03010602030d0e010e03130f120503030f0604140c0706050901061a0705010b0a17010f020f032202040f020903061b160602040e04060e0d090e 73
    0x481d200e00d110100e2074400c001c450000c0c2180019600643ca1005800c04240e10a206481d01903030400300c0d401a20402d04101c070704803002a0007c43c6044074141500d005490380c4002c209580d50780f084140c41d9882c0a0000b4461090b442c00070b500014100a03105c1c90541c015000009141c814079106000198000112900019000217800680e680c0b80005800b4042c00c605500710310030041c0520006400e545d001e0300e2454855075050000b60342e0440c065007200c0c813501c54802c1603020100325290450380304000b801424080c20000c9843c208c1c0c107010480340c0c079580e84811000c2c21215001e0b81229070a22032080000c41a60095141045842059540340005410401c1d14a0810080c2031241243d0740c038036030351590161040c0844890000c03644025040318020602038010301001a00c00002c0d807440203409140a1100c90030030070001151052201080341c110740d445d82c20880400c0340d03031500b00120f01c40c9125440201d070f00100e6151003030034007030b00d10141018032020500078880d142c030141030b290b8003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 957802562 1250 957801312 957801337
    0xf0c0a0f0f030f261903050403020d1409030106061107080601120809010e120c03010c0503090604240e03250209010504020c01112a030a05030a09030e041b0e0604050105 74
    0x40703c440c20068003000c02e11500e10300001500c1510120413004001400d043c546070301c50b402d041c40140105405a400c01c480c001c1c0141c1110802d48074683c01651300c1c60240c13000c003104504110710400442d0850300a9080000480c4c001c0c5159201c1e440104004000303804000080c02507949015000d9451590080008080040c0425042c010380d10640201c0e019000060a408400402003622a02c90310000c20050281d4200110740303071000c0c01a01180d005600e41c1c8000e049503507594968601c0984840700b0040030b1800d061000801e5107940c0902d180c2c030000400039603a5880e0000034422042d58181e0382110410003070760300c00050381d1895000d504685e016500544e0b41d4a280310b5075401044800342001604501082c011124201000502e01450a8800b20400c10004440940c0d5a009540c00c60000400800000720061100c1d00845440c40c824200043c403000e8500000b02500c0501103111851104200c5007004607601040e82e10480400781d515a1406080c81c000a145100f10a1141d40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 957803812 1250 957802562 957802583
    0x9140114090303070c03060c2a0201020f03040b03070e09040210140405041503020301060905090601380306040b0105160206070f0b01030b010312090609031e050f0c0a0f0f03 76
    0x30021403000855001500080c1507940c3d80303030f0038501041610900e000541d10189040071700c0180501035621f034485a00c0c0f03044202d600b20301d03410310301c0c03081c3c003081c4000c0341180103200c07800e49985020001303030004e0041c400180b0788910f80340c030000308555002d51980e40320f0110001400050b89994811309010b000b185401c1c0303e0416400c000d44020700c515031169800902d003240c0201130004140105059034800c8000b84415541d4802c0d82d01629030070348254070f05401400040041c1c0000012001b0442c01540c000030b0450000c203400c852810122b020045100340000400126162a1051180c40482420002c2c00c03c034800814803800c1c844844024002d841c00107525041c012404803611100754845410402c560710f038038040068003c04c0c4805c0324034450300b4030300201840c02004424144d51203503507041d90f05032850b1101e100854100c48040c0300c49161407500c0d40860424009a0000d101d010010403d0480700400c2c40901c0ca85503000104d21030104001703104070360b0062080e600300e0390007410009 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 957805062 1250 957803812 957803837
    0xc0109050609060d1e062904120302242203021c09031704050307060815010804031e111e031605071203081b0a1e0509030a0c090c091401 60
    0x10800810b00440700b02824990b4814020f0640100080d98034076a1f030315500107003403540c140d03c00d44040ca50f540c2d1040c0c144400c0c441d01c03d0030340c28000b905000e0b10448050380119464414015a400d45281003403000d201040180707030810a0300c490b03045074101d0004180455440003902c9044e540c0b140d040d400d2000075030000e158802e50a50b00595040704640004030549204010350f07611a02c203007800f9000d00800080d5050152684a05c90303d440c001000d204a0660011502034000820071000d029803003140c01d00044448904d45010a01c44d00c0300100400e5400c0b4080c030700803070441030030070b940c2d4454611450780201006031400c0c0042d86d544810710075254035000b0305050103034010450480a4130016414190b20050860140c3e6403554440c112040c0b200300c00841c1c2c80b404141c00082400c84514100c0002203a900074034541051824604107000000068200703240c03c002030b81c8a013010202400740610611404e030780b4664038102108640e2804140d60100c0c4921002c243c1800305062110 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 957806312 1250 957805062 957805087
    0xa1701240e18090102070302070f14040b040609020c0c040f15030b10030b0a0203010603060605091c02151602030c0402120f070507140f010605032103040606030812090c010905060906 80
    0x14410b010580091118514121201e14002d4010b41403d0300144a280c4000a103642c80c0c0f01c1790001d0b5881e541c001407103100d5543c01d000180914498440e086503555400084420151018210b9105c1d0310015200256044041105842403401410b0801c2e00d40640d91035003c0d640140b04080300d0b800003044078036650711024070601e91602d46c4083c28060f826810048a104c5650055040e0740094500b00134845d1104e10442d110b018a8a00d9504460200300c0f4000c18040c0e4003030182443c0c402040c004244614440103a62600000112500011580018011441c05000420b0282d9081c0c1342142094450071240d404600c0c007500713040717403440c0c520003064a2a1242080314140398020480340805030321035445642e1508460b407403c045503c0c141d0045513502e0003196041605802c1a11500b0320111b103814000c141e40007401c200c50141c3c0d00c000000c006010036004e0b0442d140301c019034440c47c1c80c0111160f424030a2040b0b4980c100301d840c42d420b010300c1d036907074094400c2154140c0c1c0c4140c0f24100f1801c1e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 957807562 1250 957806312 957806329
    0x3060a03150605150d05010f0b0d1505130b010e0f0306010e0403110d081f0608070e04020c12030103020a080706050d05090a0212030301060f08060904170f0a1701240e 73
    0x109030410344aa4513500c1880b880c400030110040b8580041150303a0307840140502c010050301450001400800014400780780c5500501031000e44115480071590742c440004101c07602588405450903281c4000c840705603080302101010103802d4580c0f1007802d40b100b0010f0345660b0305004a2030300d061041c0201e0f003854892420114005e20301012104070800e9040c0140c00000112550041080d8400301d070b00c813043c3c00c20041802c41d0f2007070700c881c04180c540301d1003541c0120465125641160342881803c2c040881048800b200c54004c60710039940c0e50542c010310018821680043c040c0382e100c1d080400c50507600008460030708140d11030024403a1200d540745400e014901d00082d42c04075101409150810001c801181240c1164039900020980010b0554403a00122515075000b50034000144c007080c6400e400c0f81030b20300c5410409180c9120180d01c00c609030404618440054454849504915a8094228003400242c8408000040780c5004a032000200c1079003041001026120011302e521100d05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 957808812 1250 957807562 957807569
    0x100c0c08040305030315060c151506030a06090c05041a0a140a020d0809070e06090702070b0a080115110a0f020307050607111305010f150e09090c01030e0303060a031506 74
    0x149039030741d541d070381c18042d0b42c03900140c50201d0005142c000d00032507440c006040361f00316080e000149c50484050b454403800d000700241101c1040303203407608044030781d40d56400a61080000000c0016001e081804500072510900400400e0200805c070a00804c180345603001104102000550390395218124100d490070803003407070f090070107001003512200d0303030740100d151708099446560341141d994645044641d6211548605008100354502240007070400727006441d4050110b00460381da0a50b603440d0306c0c842e54007448190b0300049540006200b69511514404099411413402c80c0540d284e8018050b19012421401020480650404d100b151001d00c1148000e107401440350361541c2450424141004030883e01e5817040750814102818640e0034030910b4180c504001030805e1131410510042800388400e50110309102500682c2001581d980d41080c1c400c034031110281c00310100390000502501d0751001080440e03002030040020070703141c0420a00840b0742082444510840d044082001000030341c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 957810062 1250 957808812 957808823
    0x1e03041d07091823040b0604021303030302091c12020d0f0503010b0a030b0603090a06200319020d3e03070c030306030206070305190309020d0f140a0c14010e03100c0c 73
    0x103001c00c441d130211055071041e402440301401a81e6a0780822080f449801146807404824103018004288603070302030700040101400400850301d8134607410070103805d282c0c401c9501d04500e000d400002c3c0d40c1404141a00720481c00d143c0350103482080050054081405100040c900201380c1489a52003034209900c647e00281599907203081188001d902d03149908400e030b0b822401d02c41061052648903a07428801000282082e06580711107000070007c044001410944540074003a0f007884000a126080000800003444401107417040001011b09104041082180842140d18803461002c98110f941c0410a403420020024032850250010501a000690854004685102050341100042c50302c650f24080e4902d00c500b0110048007075584410000750802d00405a0a0009159889015506128003041d0f1194000301c0f07642441c1c070607241415551b1001d00341d01013100b9203412408880c681d000786008806101d008000ca41e07030303440e1640203c004581d28502c0a1200d131285207400d07940c50b0f101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 957811312 1250 957810062 957810101
    0xf021507030c020f03120622020a1707030b03070b0319061203030615021b040b0d0302160914060607081c0c08072f1e03041d070918 58
    0x9540c000d0080c040ea480319070140c840c1e01105480ca440000680700240840e01000c005642d6520900c420005000806042c00059505503042821107001130205600d156894500740040181c501c0c0f0180005040380f400e240c0b80140400e0b50751404038410043c1c0307071070b001111f50781d07103400700725051542070100050384040c5032020210b1607000080f40600854000d507003d20009488d0305014041e03c00441c00b020140e0710140c0017240d40c20054440c50000d42000b800005c1c24415400824061444420308900603080904400d00600b0700090300006404030b00700821410040e03004200e9001006010144140c4020902e80100981c410480c1c201110a12071038040b89041d25005003c0c0c1a017011000100304500000781c00d142c887c108441c10301d40140c3c4180e80c01d840784000b09007010b910b403200030400d02440f05512071070700c0b03458034030307600c0002040c0115a91840d0000644004c0d45907503031f6000004143e800c3c071840a40c000304c0c00b000d0318280e12920310118030b0102d10300001d220a150700110f0440b02d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 957812562 1250 957811312 957811321
    0x606051c0b0721091104020301080601150203121e0a0b0607112404030311060f010303050a0e03121314010509010f03090209180c03060103120e01030209090109060f0e0903030103030f0215 82
    0x1500401300341031103041142c602003554410081640002d014042103684100300402c003803400c6003c05120b011a03170055a20b00308400028520302c3c00221100281102e02543c01c150007001400341c030340d001d032900c507080000710410000a052072003502070281a0100b03030f070158501d5580c4c0d00c42402242d030003118424500030855903a0102c0d500301d84000d0380424208640300000120110700d0030310945035500e107512543e0039645c4c20303940c0e03400040c1e80c0c03400c0150340800d581d2161400c00c960810f45410070702c4103440c4c04c001819400c0c407a03001d401000c408410016514a541d03044003c2d904030202c242015903d10201c60011001441c5004000c0e62110941d001c1c0a190341410143c02400030106055170314800700c0e9002d0540e01d101c2803100615140305020a41d50240c822010503114410500d03025150a10200c0050390031402030b009210b10341d44c0d500c800c10640b424011820028180520300046a203805114076440740014840a03050048039206201c6503442840303100f88900038110401c1041c1407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 957813812 1250 957812562 957812627
    0xf030601091e06050a0b0d020d0509160906031101080910060e0402090f0412110118080408060708010b030606030c040e04060f051807170a02030d0c0606051c0b07 71
    0x40100c4280c24203866503a1106070b15a41e000703080036600042e0401581e24900300003c21217600800241c3c0941ea424000c10044070014001c10380661128001404008407219032907400702c41c00d9001d4200c5a103006000c0001480c803624407207000a007400e10b072440340d40c0d199085051000e10f00d000c008680c0342410200e44e008400907001d003d0b0f4000d807404003081c0c0d02c2c030b542c51041e41e400355005000c0d100d0f05513101c051300d44240e080500340c00c541e40010940b2054500b6030494903010032003c1f00c44400c00b04061003046010455580e010f601441c1104055240241d00c41e081e02c03018005a0094500200145c5402801d1040303c0082902d0701c1508a5880e00382402001404840c004d01c240c14101800320b0301c4407010444048036084240007908805141600790000c2a2004003a403119004254214015a505110505d22411107445060407100c051030400b01b10750303032900141d00c20b80221009c800c1ca49201613009804a60050150a05844440007903442e05825075500d4010180120282c030b0070003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 957815062 1250 957813812 957813821
    0x423120c071e061d13050402030f07031104141902070602090604180c03060501021f0e031902010c0206040f0605150603010902090f1f140c0313140d1502090f03060109 73
    0xd02daa6694082c6038401c1107014180d10240221950000c0b864018501c05850365220a407c41d1009013101c91021034181d0003418805158001d85801078a907110312454103103801034801c41548c050600f43c052901e807400b04448403001d050328968581c0401d41104000480c0d0407144000d00c000e065070344555a4902850680f42880c660001040c188181980e03128080d020368015690141c02a00d4088501c801d103095418803a03516136546519200040f001580c11300040441401c6281c55112404038000068256890a49800219400b00040201140d411155000390a503c00030101d5562182112800c0e0201888681030f4000000000020f40003110b80c021300604c54180c45098210040d48200f00d1603800c851001c01d1f140d15511a40710b1407500c0785030300c1078000b00014461401c2505010782d151541e00440410200240110401d008107010a015601e85a104a40c1e01180840c0c0b691441100900344000b0840300d070300495040740703a540d0b1151482c44000c0103002c8a1040da9175001910190 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 957816312 1250 957815062 957815069
    0x25271d071416060b33040b18120616050f0d06080c03191a070c0b15040b030313031e050319030b0108160c1103010f050423120c071e 58
    0x43d440c0400d06000d030b081118070581072088440c403d08180c0010303005903e01402c01900300d40d0f00d0320308001c0859580c0c2403201603c07961800c1e40803034030400c85c20014132000742d03607481600085901c20070400c00c443c0900c1d00c0807110070186180050711035851401c201824003402000c0c8540d81e0a1000c0890904800150122010421000c07a05580301030800d180b02e40c407032501e0140014580c010084182c441c80102d083c0c20041c186040c0c80e52020648841c11404402d459490100403a00004401403500b8020800c003000d0442c0511314251214041c0b20301414a403000510002030700040001100154041c000340b2900324080d80c0d52544d01404020001000c1048000464940721510350294410000d8610500c0511607070182503510580a42d58400030f441d08550014071090700d15056102802052090b03081180082038a0a2030300e40112070500d00d150365a6807000714448404032000000c0c40d2004d071f010300710046070b0f03503a40d58041c1c606000c20380d00446001d2071a2014803040142421100c0101c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 957817562 1250 957816312 957816323
    0x40c0302210402011215140a0312120506040605061605071d04140111040b1c06030503071101020d0507030c0f0b01030803100b1306050325271d071416 66
    0x1c9180d01200314045554001040d224001c4440090009100e1f244100031105002803002d0409030340c0303540744540c0d0254030000c2030003d800240c4100312000f203401529000340e402c503400c0c4112810000440c02500420000d070302c81d0351040300484148041800580f018094107481490505840d0f0710800480c1000e6078100c40b0428004103191000c6418030a6a141441001405181c54a88880000c00c0e0b004101e800154200303a4000342411007151140f1401544214040c2d030304c81202e41081ca034408a05401175055410000b00000c2260b4041c0840e80c1d100e600d0b0400c0f4404681c1d07800e041442d4040b5050062001d10103500100500c00c409019500c1440e0410034841011784034942030149009050186d1402c1200c1e99007400720a000c3d5015640c0010354032849000300130040c0c441c05007000b0011556011407002c0d6420300d84450540c55058844d680c6c001c881c5030075403904280480a2070040c5c072010300035000d030b40402c00030392082c01100310140014060540384c2c3d40c00311051958403514a82240c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 957818812 1250 957817562 957817577
    0x30903071202030717010f1e050f01050a121a040b010510320c0d091a0c12071506030501060e060306072c060c0102030117070f05040c030221040201 65
    0x201d150503140c11140d0160b025000d44030043c60308121504c03040d40c1040c0c20302c85549a5051340c210180d50702c121515202d00d981d80d030415018514803042203d1014100d001d070885000d0051109459001021013103d07054510310a041b0010b0420002c58290781e00c5004232000039030244000e01c07000000a5040e59011204000c10281d82001902c48218544082400d10303c80e6290142c4000744040c0010700c5071600308500d140c40010f0b840320b17090030100b81c2024040b0702616020700c40500050301c18038034150002045860701d017151080a68907013050010694101001902c1d1041029050300c85080041481061110544030703e000707800381c100b5020340707039041e003103200010000d141c0040c42c1d5001d408551a207294021401c541c10840401000002d448070b200b00c055400f840d15000001c00d2128002e000040e100d50600000710800480000e40e100d45500199041c00042540343c10142101c00485000650340c1d10900242e0103805096103a209081d14210a0a6030a60b00f225480c46103100b41e0301c001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 957820062 1250 957818812 957818819
    0x7021b0d20150412080d06080604050a060c020304060e100513090603050d08040210032a051201080a1a040c0f0803190203040f030f062019080c03070804020a08010e03090307 76
    0x200e50285100d26094000424441320124225000500324000f070760101060082d101e08007149420010b0310b04031003c0c0d000855a009010807031080b24481b00052016510706803525500904a45e40e8001c11403060088030102a640740c000c43c00c854854203032000c51070185a07286020030060003248401d407007602412a82d00c070014400c6222604c255401002c1c21161942c04104400811489403012040c1c40551b062034030303040d445140f03d1710404840d034401ea0b5484149541801060301a44102c4039640b0446581c4000348420080d0300d03c240c803881154282e50703101c3c00c0100c0b03941802d1340450090301d078510020524180100041c040f41c20000c00c503054420003060200e9803842240300781152180b05880c14000101d4006041030214010305000c1140e8074544d054106071040f900d10401c3c1d1800000703404c2105901c2c520075456016880c1406d45840c50881200707816488010580786c104414040010119640ca42185000c3d0100c00002c103c48283c180c0da59a41cbc0e4803070b00a50744244110f04000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 957821312 1250 957820062 957820099
    0x1b0a060e011116061119090b12011a0412080405040b150a143106093c03060203190e030f0a0c1406060901090507021b0d20 54
    0x840e1030280300100928045207030f54200074000d4246012641e50362100040b81e00004501c025100d0362001000112000c0c1241c3d90241041c10180c1c06902c8080f0240b1a81c0d61800b0304404a80c11a030807502840006000134070986c90511a41c1c2024600e045086030030024041e00c04060001d0320381c20745040220004540410805c0308a00c6034030004201e040000008483c400c2e514810381540071101e6506004001c001100c0e2200b10750b000008400b071031500c9159240301d0b00d009000402442c280080e5440c00c000240a0400801070f00050703403003c01080107030710709140a51100b0a1000c1c010605840e0700e074605032000e03500985a800f81140190385141013008588a100d0440090b00d000b140b509040b5907582c2c61070340041c1801414070007001e03450408124141c40c048542c0841a000e042c00b4a010700401c81441c4040c1c00c4424081d1810080007400c03500020002811100002d40318240403070400080c0707410400321402040c1c20700820400035200b0004244040103a800c45d40a40c04009a0041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 957822562 1250 957821312 957821321
    0x6151e15160c0b130605031302040e2a091b0304030807050705030a0e03060a0b03030d09020a0e0a060305061302010c020d1b0612180201091406040905010e06011808070b0d021b0a060e01 81
    0x40d105608a80310009004ac035040d440b05000700d10001c256620200440350000046210b030302e48a29000f444c0c808402e641c40c044001c145e004000f0001403003940042500070300035000040009040c441c0e43e00106500601460607254210341c0402200d42c0c07182e843c000140f0300007601a03454041e21131030001c00c2000da034074018245a50030103801127050880c1d0030014005440e0483c4140e811040e0504081007014600c0c6003207114161401022440c1031462802c85c4c60050000d042243e84502141c4c0040140e174030810b41e00846d038045800b08480c00f002e06207010a810f04000794024464660780004203160041c5241c0202c041280c0f040240a9600c4100e00d80800e0384c0200038000b549512081c070030341c00e00c56040141d191026142c941481e0702c50405404440c420b8201040e201d6100e4100095583e0000c5200030080078081403410040c640b91940b50380d0301083c002c051034a20042500000480035505803210192203031001300c596080d1b08001910f0b1200c40744d0a903000ca0070401d42036040c900c14001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 957823812 1250 957822562 957822571
    0x1014070f050f0c03130810020702060a0f020c0406080a03024303050106060c150e1c020a17120c0c030306010c02060c06151e15160c0b13060503 63
    0x1119000341555030812901580944050030520b2028003031501295000c00150035402c1da82c42c8a0044141031810580c070701030a110ba81d0001c00e0041002400503101e00782540d0504003d03040ca0100a14086003c0e07041070383d460802c503007040c540840080c50034400070b00c0000d9a4029020b0302c5403001c83c1c0324085144040c2e40340903426142085002011b880050010101c44009840f000c517180b5100e0703450f5401c1d9090fa602c120300207840c4c6200c01007031003c08074101c034102c0341500c01045000114081d0603210450940c05011402030407204411190003849954440c0d0341c44203201c0e148440c615105211504458202840010400c0001e07005012400848445e55401c4000f10300303540d5160011261070040c00d80c1260440d4052050705080e0000704405400740046540f40203164080d0818000716103454118180d01581a06440b0200e03141c140072001030f40d440f000165503451040403500c29030407030311710020b1002c011070710001003803601000903214000c1a085550316865a41c101100c041c0020748 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 957825062 1250 957823812 957823817
    0xb0f09040b01060c021302040b0a110a022209080706020d0b0d0506060d0c230f03190f0204060e2806061205071b0303060e07030522150905101407 64
    0x7006021490050503144c141d648020840c000814840500d82c003a60080d03440541940c030301081c009180d54021201c1c40c1050001c000030010101b840d0005800310050380d032060034000040740c10680c083d03443d0708a13172665900b086406940d0385981c80d1034030080d80010741c800d400e24582456260f1034582007915000181d0850020119a107a00d010030500640010080360102c0c0c0c00400081c4100e62441c003007400c9680e0700381407040c1c07540b05000e2181c60040058003510036040604078110f120390054600d2a9582c10440c4885181c00c04d2001c6030080c8401c0d040b0780100550001000340340d02c0201c00605552184c0321001c2c80740040054090181c81c0c007800350305d011034000310b0344201c10354003680010344c0841341e40b030100c0707181d000f51602c41c1e481c20b1061001d0b030010f40c6902c4180300010580000a800000034034041046107021441030141d03000c0d6459000401007042049010301080003000e2003440600941041203a100707280c0a41d9540712040c01e0310307030241020302409a42e00b045600074812415034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 957826312 1250 957825062 957825083
    0x501050a1406090405070c1103032506060902070f0c1a03010e040606051908011d06040834050613051c0306030b01090903090f050607030f030209040f0b0f0904 70
    0x140084070011a4401e68001c042840200d00c6659203000d00c9004a4a646410103e440941049158030500e00e210342d001303605c10090050b144540c40403007401c178100d0104800c000308441c0b61503805440b2a43c01a20090b001144020900c2021902845050310804210841ca541c0d8600c8010040c42c5655030034000c0e600740010016400a0702140d03611602c50440050602d803194001010041840440c0700c1c108081c0300c0900c590b910901c100380d01000410341035844450010300b11a560f910051000f4130440340410215200c0c200b148a012000ca125081c2000341002007101860a81804005681501c9003002040240b04044144c40c5003580242c042c08400746201c1801078011004658081015601c4000001040c512103031140a8520070101041c07a407528100280303600342580090032a2400d12408120642c1c07140200c810841d81420010303880c0d00094003d90003030040f41c0360560058140819510303046200da0014212120490304050228100b81c284400d04070202c40060030f90202 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 957827562 1250 957826312 957826319
    0x80d0902120a0803150910060507080c01020d020a090902210907030b13030810060e04110f03090a030f0512010504050c041a0a0f0c02180702030d0207110906040501050a 74
    0x554018524960000d00041d040c905846401c5140c01e000840546079100040b041c0320000c0c01c9000002a01242220580c541c0c2c10240003000c1c1c0019544548028040c00080c8141040035585c1aa2146034285000b10f4590900c00f1528010358002280c95001850220700403810071400d00c241c805160804070721601ca0721518800600800c0003401c41045840b0f1008000000f42d40c099941c1d04c03840e0180e442c0a1209254076020b030540c54007500c0710540c44101030b4184001640f084154107118022500400e01400c1c212804407140700d880300b0803054410000c00c11151180014404241c035200f903450308150113031070130221080d00ad054103403584e903031300c0701c0c010001442c058000e20307042460046d036076141c48c0d540c0041702034544100c1d0b4103000d055400f05400b1001d5801004d801c1405400e81070106220055500140d12565001c02c030210344400c03c008640841e1081040c0c0724070503d8024115035555041c2003410054030140308092240c0740300e03000030711903092078000d0034100e4501034134001d0220704 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 957828812 1250 957827562 957827587
    0x50f0d05030d061e03030537050d06050307060206040b0c070b040807051005060a170102210a0b0409030f05160c060c060509010e0c060d15090902040b03010b0109210c0f05010f0c08 79
    0x44000d8489040c0110b481030b9001d0580c1c001124011540c480683d00d204101903001903c0303133070340264803035000700104001568020079040e07030207a400300d051900303592601e180b4011401000c0c4050311500c1c00d20304100c10402041c6c020004039000b003040301e42c0020901852001d481c0d04446075600100710b545e0030030400c00e64100c01040007224200150070b0000d405000080030103400c00409144031078000340580100d441c8501c0c107517410300f03803000e10100e00291005040407907003140313113010000002100382108600360840c02e10309500c0004800e0a1b07955900c0100866500c1c44c00741e61252910010801031030051003409244e020701009403182801c17460800609800c007400e840181030300e52040e940041c802e8100c00002e424010070001d2041014010311080341c410340d0000703010b60b00d801d5a00d80300760317046200b1404a5100b6185001c1854181c103a800080b000502c004000c8420004003240c1c641074810a031095072001c0c1d0390000b592004400465100020782400380c03000760100620f034019035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 957830062 1250 957828812 957828847
    0x1718031009021e0301110c1c020a11220c03050709091814030f0c01090b0105010c020f0618030f01020901141905090d02061809061504050f0d05030d061e030305 70
    0x700004c000007250400c1d0140c6010030b50004844000c1d5800001e52410710701e2840c5500e0b00003011902c010000c00440c0e55803001501c1d01c00d0300c0c41c4d101d4948100381c088502c85102c01842e10a8a6000c04d0102d1074000700050050f10b0141c0b01c1c0c10202c3c1c0f4503200458080340601c681002c81e0001485503800200d50380312135019100c502c0c00340f109030008100318000d000403880240000105040001000320007401c050711440c1060704450b04000f81035051030050383e51980e02c0c0c10303c0203046a2150ba1030101000104000d070a02104c0d0760075001d98141815051019400340280420a8075468504144000070155a11030400d0b9400c42141c50303040c0045062190003d4203020501818095800b0030540003e040c41c0c2010102403075500801a03556924108035080030b403ca40305030f070380306140c405003040c0085074080d5014040c0503c02d42c50340841d141d0f5549100d000141c0c0c21006895540c0c540c0040307000545802c1c0030702d03180300030844440c101d0b91280c2e10080044a40568540f41044584c0c0c004c0060300307 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 957831312 1250 957830062 957830119
    0x3010911130e01050a06090b0d1e0f0207060b01030b0306040f020114220b0301050117060f040e160501020c0927010c050903010e28171803100902 64
    0x109014607058140880303000780282c010015815150b40c5082e0410100b00b62941140c020080072240810040340b1242c19240401003401020642889170000c107502e1800040c18004020b081180d0000d0202442c3d0061041030301400042c004504070304010b400740d444a540f00d58040c2d00074030000340403030904032407044141c1c81494040c840e140c0c02d20b4003412a4010038040504104028101e0002800d00303140000108040900281150324000c0043c0c40b0051000c6982584024180015400d54031000c03c041c0c0c0400051041166410003034400b65200d01030420701d081440c1569001c6078560002910402c2180b00400c0c3c4030240d910401e54200d10074240b100c1f20000c040020101200c49801c2c098401204903990300c10303841e00220780405003541c1015800d440f6642100c000a5024624170031001700c140025440e10340400b13603901d44200c13a040d00c010003034031081000c2560080241580171200365013070100c00b11075040003421070b03000c01c0740c0e007001009510880c14050500c1c1c00262110400b800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 957832562 1250 957831312 957831341
    0x91116050c0306041a07080405100e1e030405010f0801050d0206070f06050a2007330204060203090f091303030b01021009060506010810030b0a0510050607120305010812030109 77
    0x20510000d0102c0e2034020251401c48829900c030500d1404404030700c0219500560524004403241070623242c46817522081c0d04036051282d201d1054080707145003004403889000c3c2220a2245150301c45404907229080340c003d1500040310713107140003415482100340c0e50690300010710080b150700c1664200320080e403040d00201c40324ad215a1a14010640d140f00c1d031441580c10140124a04640c030514990300304010540d40d8004a00f0f02159000c5940ca80301000c41c01003482c0c5602e003030090803062600c0b03c810800403c8030a4000200850742e298040040c198a030320940390034005d5003174a030402a520740708586035036140603814503500201b031098112142da9041801500c95403a1102401c1054403030000c4107507142512042400340c3d550b8008180c07030748070302d1400f5000100c40c115941c200031070802400c810030781900ea40110740f403144c02c0d068a5000b82402403049580f60151304d480c05440c02c0c43d5000e200403c1c5000300014a40c2804524030a01d1030202c181503103541c2c02e09418500178800001c0c0f1008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 957833812 1250 957832562 957832573
    0xa110f0f070c091406090901060303140a02070b04090f050601110c040903260906150d0605100e09060f1506090d0807060507110c060430051603060609111605 69
    0xc5850244c810004640c0c81c03511040018504501441294900500b9100042c1e2400000300b0100b0b5100c64120070041c42020820350f5110b001d94220325160054006294038000043c00055208483d0310924010ba01c040b02484183c1c0d69600660fa5900500c02914158008030003d0050340303410350018001521078206410030600325241e10310351060584611031000407a9081c0100041c2c2080101d034442d02d5601000700030a611004500441c4072844018100350312800820108032400781c1420183c0707110009134042d482c00848103590391304c0907107035110310b520a080410f00d098100d855401c4c030440060a850301d040c2c855800d2040207242c03a042a03c1e00d640074448213000581c1d50040324041c2041d03941c0d0240e4296004240d60400403664001445070700108010060500c00c0510000d02e868200b002140580e5080035038103241c260350304010010f0040f10b21041c411280700351031034240c1b03000b80003c2141e1625081203400315242c03815850011034061200540d144600025486218407a409459 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 957835062 1250 957833812 957833819
    0x6132616060c170c010f1113032306040b01060f020607050301180f090b091209180604020c0604120f050c030f0306012a06050a150504020a05041d0a110f0f070c 70
    0xc0540c10013000c06440d80d440d41141d001e0b9030b07100e01440b840c00c0000c0480500d080d900000d07a0b20030101500c0001d00d4030184105140c0f621040c1d610705e24011000d8070076213010303103001d14000100313000c00d0060b035010405444a60031030758400141c441c45401d581d141d407465642025400a80e02902c4201c6e0003a140e20364400f42054541802241c0c405441001550450f040582c001e07414107598419460700224280711072081c0b42c0c0c80d500c1e1180104c2010203c2d0fa215100e4a0205019200e024220b070068441d070030601c420066055462540c1210310760392005004130300075049542d44180c0f004808940c1c020b201c0988501c600c1c0f002140c11001c141082c00c000d4204240e10507081448140c00c10070000c00b03141e000140440c1d4050142e0149990004100000c2d601142c0d500202041c002c80f4091540843e0311a803550203041290041c1911041c03400c515451041c800c00314903021038024008504040c812420000510301360b070b4141000f2900382c2d040c0500350701642c649070000307842558580c40315174002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 957836312 1250 957835062 957835103
    0x90a14070302032701050907170309010503130602070f020a050d08040e060a080d110d0e031b06091306050f0604030b0708040804030c170f030a090504050606132616060c 74
    0x707070216078584d00106651030002c42c650700340301d01c0780e010400e45041818203c01502c00802107800c50482400c045459448026914400c0460f030788000300014800035140041c00850400d15030380a02c21510440501c0c6c40e1000c2c0180701c800044000c0c0f40cc01c0500c0284807900100500c143d1281000d0004a40700c0c0c2c1e41e6507500c1c40d20600c02c0e00760b030110701c0b84048541e81c91814484100300b503480341004e00341e4500c103902107503a95103600c1600c08083d0a0301b41d1110701c0d42d10f00c0200c84c1c0540c00188a1a001c05d903065110700100440d109035441b07071400120340100d0341001c0301034804582e00306054804659440c00d094601180041c82190812010800400080c0340e44000c800985140c40c81200309110821141d89809840d4807116080d500920044400c1c551000c100010384000b507501103581d468a0010590038095014803803000c41d88003001140b141c2e01d12034604d0300604c45803200088140024511a2201301c190a800904003070500140300746030107414012000f81c411485204001c6651583d07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 957837562 1250 957836312 957836371
    0x1060b16021c02180702010c020d0503071d041a09130f1214040f0608071103030109090510020f0a081b07020409050f01050709050a091505010c080415050702090a1407030203 76
    0x110f0b40c540908001744004681d0900c141821b94203140002e080303150403004040c1103400010248000c1115011a00c0d44001d01240d40c00d011000c05041417040c1540c10403090303250506100180e000340000000030f040d002040c1c00800f840380d04000071041c215041c0e20341c018030418502b5001c060000d0381d00c1c0c481110425000900003412a03280034100241040740040c018100a000031007080032450940c85480d00100880317044034a1424001041d8071030b85401400c040d02c451700c10204900c081075840041c3c030488000c041c5455565100c4009a54000c0184201c40f41c81d0603070f445009c1c00b4413075900142480e0384902d2001d40100121581c8030144901c030381c2998030071180f081c002010300350304124500b00010480c2c05000704090600c05030045d00c14a100c4c0b500c0c04e201d901d041040005103201803001c2d0354129005800742007a00040c1e03111102015156a0007a9803c0b80a4a503c80004418102030f2089007403240c2000141c0c0b03000c1d2140d000441c00f0b5080a02901060301c0064007200d00040407661 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 957838812 1250 957837562 957837589
    0x11115040b0402040b01050703080f060307030f1112030c1507120507090510030c1403060d1a04020312030f0406240e1603050405150a1104030807020301060b16021c02 73
    0x801c0030149480e10502c0107035418928224140903081c0107120000c1e41007a029648107808060311042c560302e02c00020314201080d40068042d056951407081444404850020040340641d136a03000c0c46020a0000d03900d214070f4a1188140d000140300702810021500e000c4c3c3c0003481468202c91110395140e000080b2131003030f903040d00407491641d010001030400c103100100d50340d1641810020684a55009405c0e502d40e440c00507070ba100004000340c21a5103000400c040c5682003030054110754a503086800030488152410380c03080c41141160312941c502c900440f407280790141c040c941c640e1119910300703014000e06149625000c070b00d40341100e021481500540000c20079010290a182031140484820071003940040041608203410070000c02c3e00001c1c4001d0501003040350440c84c1c0d80300b0a800c0700500421680ca58151000600081440413207005410200c1c000c6008001c0303960303036521700452403080703008190b28010b4103a0840058500544120307024950880c2c1c200001e50329600144a00c41c0303140 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 957840062 1250 957838812 957838823
    0xc080414040609050c0a050906220e16120c02070b2109010209030706050705010f14010306150e070e0402090904081e041a0a1b1202120f0901111504 65
    0x880d099840d25025841c000d1030246000c000604068407002c00b5482412661014844e0000c0c0c05d42c0207803101e00841d04c00b83c0500d03c200c2c5000e4105040d10b06003c036944240041c0d801801c1c003240070389240c1c110600c450740541d03c1349102c403034602c09611b0103050040100c07002d50240071400110280c0340c0000309103194220b040e4101c02c1c40303007064604200e18082c1c940710f11603106109500e071584000554400b0346805003417050302c81c0c4803441d04174051b12a081d0040354036420001c40e040f82a880380d9416050301c1c4034580c144228170b03001401c0d00182041d031040085160190000c14500c5005150f41380c2e00c4800a040541307040b000c0e00c04501c40750001d5404032800c0100040d24840c1042d00ca0386045000f54600020b480d04c0e00c2d00a209464005410402c2d40c080f40010310b001c5028000d0030b03200301d01c0015441e0002500302d1800c12007420300f0000c20300c8016005800819001d0603a440c00c40e08c100348898900b50806103080700443c0d002c803c09100c11420720900903104982010380e02d00901c51032080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 957841312 1250 957840062 957840089
    0x609091605093312210325200d020c2418040b09070c1502120916270207062403050c0d0f0212011d07050315090a120c0804 54
    0xc140304c2a528000d0500c89281c100341448010322101102c00c40d503800341c010000342c907510381c04640d0240074001000d44043c0351014142c541c61301d4100c84041c010008105c148031141107181d6107184c07903d601e14152070040e0001c0c0c0c0106803d00e0814600a030b181c150803680e5000040b070081030003003507100055800b5840d0b4007540401c503e18003400380c500b951800ba0381540550409020103803004d89c0cc90701c024401c00c2e052008840c0346045038103460b55006070980d501441c0c2003039105192102102d800c142c0c04046901400300f500a100b00c403080d804898011000c25a503055040d0b04001d4010b9002101c295480d40c0c0c0d6450f02d040d02240c040302d407030300003d800b5940c0b40c510300e0050301d0b00101500346800340c5042003000010950309013a5484094050328144030442e03404a0315401804010305103d001440010070700d910840000360312054440c154100c56a203070003030103103a5000a04071141845070b4882040e0380001031035501422404500390400440510640e5a0040c1680207600300380000e10f280f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 957842562 1250 957841312 957841411
    0x6092806030614011517060f040912120e100e0304090c09060210060501050906130e180c0f0303030c16021c050d090302060417070504090803060909160509 68
    0x11408007900502d14080c5100062030300245c0541078040034100c24949041000000c1d189480300e0450040803500104100302e0901d00d4a40220742c0c010544c0948005046d4102c1d04110341309500c6041c20302091003000740313000e240c108102e5014100c0801d072000385000600001418180704d004012001c00251240110300e42400d10080ca060444544900c01078104181080b080c0d80040449a84080c01d480880d9248986030320124040c030b0550145640020720030401030a070140c40076501000c07c00c0402d40d00c8160001c1c0403c41410f005000345c59041c0c1040000c21041444a00100440781200c41100c0100b00c4640008103460412040e40d40704401b07002d0a6805c00c1020300c5610500e00050078401102030868010910900450203416640e041101c3c0d04252010200700c0c0d240100802071041c0700031901342c684483c0503002662203a00450900011070703400803000c80d041840d1555070800081c614503001c1000812031010740010b014503030600141e81c0c500090300c1221825030505203466040e403d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 957843812 1250 957842562 957842591
    0x7060e010203010503121e0c0a1b060e060301050306071b0f0506102310121109031c0c330605010801060513090518070303020d030b0405060928060306 66
    0x84074104120703440d8200a010b081c0100d5076814085c7c6040b14107001e8503820351b1b00c0e84500c1d012410780b02404c801c008070103101c800583d09800a080e40c0c1956036001850341c3d14414048940000e000c0d40d580740e0401000102801d108007a01030300550052205a0b80315110b40358000305003064036054410350040003c00c0701c01716504e03016a00a00e0b00102003028141c0c052811101e850740d6800f030030b105000f10703801d102999204140209216261000410498400f2000002c040e03000c0c045042c028010810142030100001c2c2c10010030040301e4942c8c0100322711039903070780c080b491050b131007401581000d1021007040500e1340494080c095142c00d00090644c200000504103000507400038040100401078a601c48056094403000c484011030089482d80b43e80841a040500314040c0c03103200d11403a1400000e041d400038401c28000321a031010840682c05c0c206220980d0001c603981034105c40c0d050003140301e4070103180240c0f40320b41d20100e08140119058038180180c0d61250b01c00d80d412501d44540d15036501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 957845062 1250 957843812 957843823
    0x20d0b010306021218030714070f08030c3901030f020f031b0910110a0203030f04030b01080a110d06091707140607020a03180b030127060609050d02040207060e010203010503 76
    0x244005c1c013030440380c9902c4080c19541d11400000810b2004402c503a01c01c518001c02800010341502c40c20790361035070f484088040d079071381217100500780314400c10716240c0305207402d0640b14000d041c10003000c030441451762242034010709103c0074a504050380d544d80031800054900c080c281c10f07000600c1003030b070700d0408614035041d1841c02c001c0c0c407410900030049451244d807448070302260070640e030400c0e56580c120101001c1c01e199000b60003075007600000598071102c11281e00104251380c030079000307400541d8840c20155510000c0010090003c01120059842440c1002032160b00078881d8402141c01d04a40d510020402451852440c3d250004100072040040e1f0341c149480841c407400051015140c45000207603250000744024040c40020381002c803008403a0904d91018001c800c111980da075035614071040040c88001d41c1207540559070b1a603d1240318240c02298115100c650340ea180150a000c108040c10001c07042c128ac0c001c1d402c100d8180020041c0c0103110f10800302400068980d85420141410b04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 957846312 1250 957845062 957845071
    0x2307120e010315061218080c0c1c0314071e03021c081b030613020703120c110703060b040603060f0b03190b01231e03070b04061209020d0b0103060212 66
    0x10703111843c0510a10741e0055191040e80c400b508041100b000003840c460700c80c61002000341c01103c0009402d5202c41000500302c500c0c2c0340a48064440600d100c03114000682c100800500080b55000401c1e403041402e805048000e0013805448007100300e20b6a01076940c003a082046000da00500080015051000d180310408001800d0082035071802d0303103a208107042e0f1900c9000340c800780440801c8081c6c9032030300c0241090036040c5c030844da00c841030700703016050fa01001c1082d41c03003504065885070500e10803507881700d101301000001c24070b10382113694070406000c900309000c1c2c01a6940340b0000104465019200c901020f030b00002500070141c03428981421181004428102c907a11008400220302c0d1440a04692940100310f030005058103640c900300c1950280c81d540891110074403043e40d05461000c08814504500f01e94056580e00617840c041e002e9842100b0205144462129401025401001d0818402860030148d031226546502c0d60580c280c00649400d940400c0441030042c0c1d41d40c856400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 957847562 1250 957846312 957846341
    0x90d080703021204020d03020a1203050a0b0f03060609070e0d060f0b03010605010f050a0e13230603100e03070602032707180f15150206100302012307120e0103 70
    0x40c40d121507600d0f0404070000c3c20082c05112400980300c18144280100009554442280d462041e03107070a0080182000350b800c004d92038038110441003180b4044240400740359000e8003070030040d40d50f1000c001c20020001c1c5070700103200b82102005a1076642c0c1000e506850710484000a1843c1401c094800300c6024030011030082e0302d049400d0000307a03080100440c2c0610140f52450b99105410b908035803201c02045000d030030000750880d07060007004541220841012a00d4013601c90134501d001038220081c2a500103070981c20080858103044000d4014400c413030844411a80351081d95507541c400c03a4000c80c2d01440b0101c1c4440d40846000203000c035040b50060220080030220309242000507000700828505240035075a603110105a606600a0029003d080010a0800d955002410500c01005010380010701502000500e0002d202802c10142c2e501a5540009600302d000010340c0c1c014a0000b003001e0341c006116107400604d400116086849503995900d00c401002070014081d03a4011150042 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 957848812 1250 957847562 957847567
    0xa26070504180f2a0e0906010501200a080d02030f010b0301050916111b03010b0a030503030a111201120c0b071106090d08032707030c0504020a090509090d08070302 72
    0x31150312400505407a040002c0f07010840c3c103450040a1120f0b040c203250802c030586400082c0e1960002244c03021940030800070700143d0b4a012890b40c0303400c801d00909003c180381000350020b9482142000b50741c894a90f0403520b01d583e164561110641001075400500f540000400c003015141d00c60043c0103060228520f411941880001054128000c164218000d007034000c40141602c1b84150704010f40001c0140d03800c2c2ea14002c1003100c08003000107624069130802a81d0107503800e100e1610f4003126089405507095454084410700604005104152041d200703001d0601c1001c010301c1d42c00c1c02850380f1080b442a000c080e00e05802004402c3e400b001c1408000d110a001140031010488a0400200c8220341e64110380310006010f048411800340c1100740200810401e0f41c000140984000e00700c6402a075280415090039503225401c1c040142340c801d2041c1c00300060705042c2c01500e070300c4440b42013203e00c0c6926400840c40d80e00045130030ba5640c0d80002c0d0003284190b00320903c0d580021345490191b2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 957850062 1250 957848812 957848831
    0x30909010e04141f0906110703030903080114010e0d2d0b0f0c16052a030c0307060f08060f10080a38040f06060507050d090617060a26070504 62
    0x208882804c0503204841070304d5021a1342000096030001e51008043d002680c4c1340d9010f420020000e103a5481c0c2140411689000400c40003094050800d11a2050f5140c099841841c42480f0000c1c403103480c05c507a89240100c01c01003000c44000e940c11402030340d080010410405041007003403040042c100104501000c410720500241c080119151152a006843c201d1145480d00300e180803020724500c81024070550406a5080300c2101852884030708a0881e180e01d030301c6004040d00c0f180d80f1f2140e2004590004005e4071110b0044d9041035102c240100321f0524041100d0200707690508101d000c00c005031180c01003040f01c01c500c0c400d000d007a2440190514843c1908080c811101520100e903c0100345003000c2c80d40c40707503955001800701080300142841000e54500c0054078581000380222020300413810210780c4c0f50300c260000001c5800300c1d500c0c001045400208514440750291103540c0140b030030500802e03142044010012504e45108514400c030006d01501c60030400c054000d6032003036060141d081c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 957851312 1250 957850062 957850093
    0x311040302010c0813051002072d031b05041109010206100317090d0c0f0512010c120905013803061306050c040e01030803010306060b0a09140102030909010e0414 71
    0x640059071102000e99540444178802d1a0302196500c059848155071102801403a80454000c0481d400e8404055101c0d011a24003030b1120140f001d91a082c0702c8410040010980c10107034402c1c80100314010600e51903d45010030241c40300c000784074815103070000e8801e0442d41d0401406600c403c6802e861140385040d542d500d22408140744c2e42c3d01d8501d101003420078544d43c4404450501541c0b00754868280766844564200310401482503501c01d0520407500700401030180204212880180c1d03070710a401128180700030042141c07107029501c56603550040c103001940700d0a44500010140c500c040d61010400000c0110005208103d010750001024000c0441c82108107600040e400382004c9282e584135540303000207029a5001401c102c0d4014000818440b00800941c16240920014032883c2c1e101c40301440244546103c3e100004e806000412504e9986c036050042008144107903450040224009540d014003070f00f082c2007203003856092008001c19680c2d1f0071800d443e280d01401c00e086444596 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 957852562 1250 957851312 957851327
    0x40311010e120d060f0306050f01060c120318050d02011418031626091822030306080f01020d0e01090804090e0c0402070b04020f090105280806090d031104030201 71
    0x100b03461480100d888451080c06821441c01341101c0114608500c0da0f908202024050a031441c1c001c1c00b04c100004074803a07100304108004213401c400400d40c201e002c401c040740148002c0204680c5003052920386400aa014001031261542d1603001041c10004ca80040c400110301416010180800c0194500d60b12000f02c00d540304416528441c91b91004141801d2868500e8001580070070f8202002603a50040703203030041e01ca507807810382e10b92001031340880c0d503150b543d03a0640e41048001c041500040c078400f1201c0c41729020310711a25000c00da00e81d41d40b10740752070b2840404d001410369402241e418030341c1c29a489890803148900c80284240800c42e05ca40308944504d014021900382c032681c0ca11b620602c00c00100740289005041103503918030600307005040f14819a01284126403000340d2444c5481d08400300c078181d85c001805805452401088001c900148003a0080482c500312400101030b8000d10001c2d10a012040280108600c0000003c007190030b90998401d400405000920150741e0001c1c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 957853812 1250 957852562 957852583
    0x90908132108180406030506010f0b03060a091a041802030c03240a0b15030711010c0e040903090302030106120302150f1302061911010b0303190f0c08030f040311010e 73
    0x910b54401c0443c15402e2203210303451500e90060b0900744000204540026024122908402c201c0012170f00c0740ca0f905018442610761076400100a90144081d0784254803e028400c4d001418030003802141021400345c4580145074190125080c03012000d6040911540041e018118042d10402282406140300d01e02621607440344a4a03040c001424036850fa805501555001808035151015503159401542d00864220303000582c2d41240703650040c5c0502643c0d05501040c2c030740312078070701802c0280001403007400340540030449070f15000005a2801e20400000d86100c0031240017900a904001e80341080038502040b040458000300140d04040700c1e58140c02800c5074441004840d410f00004a40740250418010f00d440c20764480140300c0d800006c0016040b1401000f4000c0b004500f08140d200c1c025060b024814950781d59660100a1196416580c80b2003d41401c0001400c1515051001c0d042180c426101c100d002c0d06000915070481c950100b0071540100a110810340260026182c48a221 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 957855062 1250 957853812 957853823
    0xf080c0f0f100c0c0629060703020a0303021606050c0307080c2b09050114070e06090a0504020318030703030b0109050405070f031508030d06170303070503041403040909081321 77
    0x12400d005684103040369001130390000401d00c202800200002c94039107103c1050309a000c3e55041b50307001801d228041c4c40006425401402d20380c0c1300d40e2820b60182d0b010b20310b40411100f8800b01900001d54a22400f4052801200e6040c0c9038034011801401424015100ca80115401c2c4104035124070b42080c80e000001140103c005e418103200158000b030f01345400014071f694205100c40d45056100801e1612441080c0c2d11f580c1d010b84580c042c0134091040040e15500110015010b2000c0e003080d030000c5420050225442e0840c440d40f4000a04507005001d0450000b0385902d006030f00c2d0b60384944ae02002e00411a01001203084c42003001d4603501810444009041e00c071404e220425240054000003480e40c070003a243c0da5800c4a1410008080c540160180503400d541483d40d05480003040d01e110b4401ca48a043c0b070740c0c0f0b580c0c5401c4c901c01450041d1251070300c0108030100da40c2c145406182e0800d441500c04a484040c858070300240b940e0181c02c003a094800503240d41101460400750742d481c0d1078228 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 957856312 1250 957855062 957855071
    0x120203100e01110a08040308010e010b0906070503040504060810061508040f0c0302040606020708120405060703110c03030703110f010519090f0c0803130803180402030a02070f080c0f0f10 82
    0x841c50140036000c1c10070388071a43c1c580421200400794000c0380c0e580c8214401e075110190340e03882d9140c8400d04502801902c1c2040020b000c2454282449401000b90b54041c004584c10156a07000080580e80c6580103607110703401c0b001100e10299054000e450180420141007101c62511407001094060001d0001d0540c00c082141c180a00011145002c0a140c000c0c01c00d210301a100c81010396600540e00c1480034070311580043c640b01e200c000c4192815a08002e1180f0301d0f06415850032030742e0315040c091000d07180c00b07024544d542654003003004041d501d10030b032200c0b5844c02b841d007040f034100a0308103c020f4103641001c08000d60b480700b50301d00c0c400e2000404400200c0003168100302a00c1d10f000c1d1401410440c801c080421206400800303011040c10600410030b0b019103421810f5202c0c094040e40d800340d8403e400ba210614680b6030059584803070907480042c1060181d0b2558030408040d4a0180c400030301c00107140d0120003050080340b0003003490800030000d0344004140346542e4006940c0c00ca0715a981da = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 957857562 1250 957856312 957856331
    0xc29070f0f050319060e220210080414100f0b030a1101140d06030f140d0807030f0f021903111204020907050913020414010f050703030509010b060403050606030712020310 75
    0x220680c0350400e13400240820040f44c4500c01607500032004c3d07a50484a014119084040d080f914840440c0268007408000303505101c020f00760351000010703008031007212541040240d00b01e0108803281290104c0380d0085070b420810f20340c480031900e1060241e03009401645004001c518101070340c0f01c2e450030a00c2c0c901d01c602d540008207141400354801c10038020b41800400400d010750504001c20150090302d0118549105c140117564500d41e0642c400040365070040090724407402030344141c4034090407403c00b0807516020b8081104036806170b91000b00b4038540303105940c0c00366490322950031001c00c410000d03490116040c1300900c0802009000902c81c00403030303001440a074031520580d1280301001e01000140c0803010080006074004d0f0213a60512006062070146540c410b29151403041c1c1e56440e82440d004164604034041d003401401440b6030342d00c8041100c0380e919540001c00013140103901400b614100303c010903047c40711540c03121881c00312840e0b0110150383c0216500c10b1a03841008001442540d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 957858812 1250 957857562 957857581
    0x90c010f02030412200a0302130b0d02041b09080615040b030102041a070b06030c060706090c0503060a3806071518030e090c190c29070f0f0503 63
    0x2141c021141310300e25110507004100c1d9011012000c901403407045c0e064442d8a00c28017940900340d100c0a9445218080b625000804030391001e500c4141c09050100f0034a042d03004141640c6130304548803c0540d1010040382c40301d070320444c50405010000c002e01345506205846450f0751140c0308440d0f02c21a5218202c03442503409504480c010b0450070f2408804240e0f036180d0103195007180c102980c05c000f4080001e02039150100c1c08205c2c051000703101c40d08104050721084010840c0800454a40c44020408281a075040200522071000028086131a07c0302c00759a401d0709042c0e511070301e82c44d0040d0b60070a0702d2424100602448003010f9410315261507040c100390484555140000446a20b449180c400d100303d18418440030078040c2e00d408034420202c03030500c0350042c021070300e9a51a1006010300f0307214543c5a20b4088281d8103d1400f80a0086c09450320243c1040445141140c1c0d10024020030f52032608112a0b58400a2070401b000803003914840940603044408000040010000c000f840070b08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 957860062 1250 957858812 957858817
    0x804030e012114011a070803042d3203090103020307051b0109062912010618020d0c170408130801140702300304031e0903030f0503090c010f0203 64
    0x7188010500c201070f20b03482c2d4038000e08403e01444641d00180d0348070005015900d012103492039444004189113170b859840c7d4054480c04809841955a1025212040300c0400300200074824001c200d200d076100381d04200c21182d1801e514030610802e81c0055a56a00300000c4180c5580000030b0901695982d02d0075801c413800c0c803903003080c4070326038940b030030f11120562056019880740c610036481005909210b903c03801149001040d9811000c402c80c02c00d00940c10712003001c4100c020780c203002080e001c2c1c9070200d91101840c0c0101582c0b80c2940480d40c81221b900d60b005010710914141440005112000e00307040b0640c3d0014006409040005940701203503a0030004100100190002044250200322040b0703200c0005413a818014401c0c41e209529902d03513014283c1440305c50020118251442003c0d1680581008005030144509004191070180300802848079280582e982d0b442c00c5c6042d464042d0981008003c0744080020a000700321004200054520003040242010340c0e1450a4010072403451 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 957861312 1250 957860062 957860117
    0x516090e0706140a0e030703030c0317060d14010b1c1e080a03020315090103030c05060906160e04020d09050618010507050d150302030f1006080109170f070204060611010506010804030e01 82
    0x5205000e0002300349903224030b42d0850140300e030b6030310b200d404501d075034800b400041514526400300690740000d0000f0700200300002401121000032451502e03140010740180140d031940c0040800800101c0c04000d0b81c40f0103640b00d52070751004071084264984545045005800e1024207050780000800c0b810110064103030400040180701591a60712403070300422030001c02d40e00b244c81c0d1042c240410b80102c0c0c0032582520440c080c0c0d43d001100c50b0a0031084680311258601c0c113801c207500300324881800000c0d0142c00401c90080e0b00404039810045a403003074804813004001c080f64905014010360719408401c03910342d1045120b000c10b00c040684010201603001f54402545817017010380c464000040031a406400401c0030204006160359000e5a07030980e406203000070180c4402000b401e0303850152034003074194181105086030900742e482e400326048075100d4121401181414201000c0e50342c1c24001d0540c001001e00c4c000314107043c0740d40c0141070542e00020050600c01450084801080c2c80045900d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 957862562 1250 957861312 957861319
    0x606030415091119060f120e0a0f1a0f040f0203101407030608160312110d03060f06210c0309060906090c0806010803030c160516090e0706140a0e 64
    0x1400e40038540b150038460888003050044410b180d980c5902005156200f0441702e8589800611340c0d410078040340c108985e5490101020382e01c4881c0c044010040001175a000d10444024202480720304000241d1a2a03401080b0500076480401400c02c480011030b03074200b0303800340183c2540d40c601e10020f4203101c00f542c248007441e440d054030300040405040c0750303e000b50030545080206a40340d075030440d1100d46144800d070085581040801c00141130801c000f002d00c80d1440c12400d007080c8004503d0800e2034806000d00003a8459070140310004021951340014072881c01e0003500c0c0320303041460b04080380c0d02c207000305006580d5000303586403036020f0340044405070362006042050018501d004002070950110945640c2c4a070b8101003041040040c0d00e505030f54000300150304560b0340520005079540b00020710401c2d0700c0703030009580000c0d40401007460b01200c2c0b11910710046040550700ca0885900c11810041540b01c1e540401c0066041540390900d81c4441e0640c6640707081d802400d070341c1c82820550aa81 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 957863812 1250 957862562 957862571
    0x70b0a0501031b1d13020603090601030501151d100909050102040807080c031b0109030f05210a0c061505120f16050a050111010f0c0f020709140606030415 68
    0x88819a00660607240b09181e480f4040551844104036020280104107025820b00b034425a04100d080440d0780c040c03200701d801c00d54100c00e82d011842c1908240d030306410b150700150061007007020a001c2c034803040408100d0821818a031041d400c8028080c10120705003100c129020444400d44110210040c0c00c0004050200308040c0c0b9000703000354403a00c82c48070f080c01980804160303900081442d01c1403c1000703004050740c10320180031140c110034000180303042c00a00580000041c1c49044c80042c0140100c014240c0002c0c010801001d4815044540c01000340420590040c01c1d0054a004059070b006500040d4440c000c1038940510b002075000700e03600c046031141d80b5001100c0054120180c501800544403d00135042546041c8440b03401030a03400b5071580b805004d10351080700611f0700c04a0b80c60001c1512a091480c1d28101c0d03141000c03000002d40d900c20711404460701004008010b21102800300700301501e07982d50f20000e540190040c1e1042c14008046014011454074400b203111a000e001c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 957865062 1250 957863812 957863821
    0x1e0105060405130204051b191806081b070b070c0b0601082802070206040b09130e0d03050c120f011a0c1005041a090307110409030e040b240702031c050406050906070b 73
    0x4100340725920f42340d00040601325414031009584c08410300702c400c50b403681355903a2150704000c03e04500c01400310341e2441d02400340c0070104050310b00302800746804e40c0380c0c1c5a84801a0814404070f15009001c141813003807590034480c01e50003d40312001c40340084060610840d04140d010406840340f0240030f50b22140106005c40e854510f00001d0088803030403180d402815411a500c207041d41c6080e20400a10f070401080c01e907400780650411a40030a00c4a011450f0850660341412007040648003090302141c1007005210300c15a42101041b00c100400d2070740e040082c045549aa42c41003030000800c01078890300400e080000c49185c005610f040001c0540c5c10385000300380d107684e907040303040140d9030400c07010282c3c9082e08007881134014403500342d0754190510a94005000c05440d404c65010f4010261452100c8c50020310074507101ca025a5651483c5d440c039040c01054601400868050440f0112003440e5908a8022003100d00701d4a103801c0c001d03240c4056900250281c081c040018000a000324200f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 957866312 1250 957865062 957865087
    0xa0506040605270a08130308130306110c03030604240b030a0b010309030206070c020613030506161107060c15020f0c070609050a0608090a02031e0105060405130204051b 74
    0x591103065a030b540e9020352800780c3d03e1140c040491034040b61040d0480502c000100d0400d80090a85021306080c020700682c0c2da50f540c24071a80000c503070360107101d1a040b0900c10802107014450355014070402c1c080c10704c007409070001e85070b1101030300a502c40d90f540c11510f8018000c0d130604545041000b40c0f41d02403907a0360f00104030a54411079000c62000e203404504900e41d802481100342030364240e03000380b040b582c030302e103059540701c681e85020b82e40a4810f0080c425400032800c0040b0180d071244001c0c050604000240650000203441854148803240c029014640000181e01003140d5481c07418202080c428140141c100060054514259000040c0042c030714512900800d6510203d804075403949a0b1004100e4000c0124010140d00c6106500d0402840d446032070001e80017502601681e1503000300d940068988205d82031400c61214025900100c03080085c843e46038040415a81407001c1c2c5002450304548282c8220024840c0c2d9603240401c6220b5186040e141084c003494004980e1090440c481 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 957867562 1250 957866312 957866321
    0x90212060a0e03030412050a18060203070501051806040828090510090b0414010909090c0518010509070f0201020d0c18060302040b0706110f070b0a180203060601050c0a05060406 78
    0x1c4062807030425260740703541c0000104481c40350f07800c121303038808403190803004444550010071002e08101c007600c50141100712a0b01100020304007034005541d944168908a070030340b500100000000c0010303104601c845c401c086141ca81c000d500c0b450140e41d031800340c018081c1064898206045078508030720b5082029401161900c1a600e00f00c40c0054010540f500403071b00c001a0b80140c003441d10007840100040c502c215040003116405041030300f603039501c41006104881403000142e0304040c010608003d9428034800111003ca600b40032690250706141c082105403401600260130400e0256160140520030f5040e1420740c20640c0c03040c41a82c8031600f000740184804402d039030310245c1014001401034043d2007198100e50301082c6460030010355484050060820501e848242c480400030b0b6612075442000030000240300c0c03a040c001c0340c00c180310380740110791544401815502e0b4601000300541c0d00041c88583c17003c82480d10665426480c810142071800d5041d00a10700c0c0314900c180002c100e03c6800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 957868812 1250 957867562 957867571
    0x12020420072405130b060f03010905010c0f02030f030115140307020f0c0105091806010c0c090903030c08010815041e0302010207050607181a0f0a02030903070b040b0d0e0109021206 79
    0x1032006450800b0b9120504a4400f620190035100c2014809000a080326041c82c0e401040104108408450300d40403030300795400141c044441c0d95490f1050308009070400200101035045100440c1015510440c2c1043c034030041c041c0499520340c1f0b410680300548986918000380200201c620b403282880c000c0a9038400040c0d0105181d40114008860310303503c40e07415160f543e0002003066118035100074146000c5000900602d041152200c0c6400c0490080c11103400101014800081c251080d400d00800f100c007049801c5081005032401000b807827400083c031202c50f03050000c11504548451070604040b8201c0c1c641a080801d0b054080360074941c06501818195005105507034031075556400031141d080d0702c065000c4220441e00024000881c5031801616076100e011110380c509035a03029001d0b51500f0264105006030700002d90fa441030705041c400b140c020841200c40604140c24154202480d019865010060795a17981c0303609010042500860040d94018085d406042c0103909400e449040489 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 957870062 1250 957868812 957868853
    0x50921010c03050c090307032306011d0915010e071710050114030103030827070e1f05130b0102030418021905031504020a033309061202042007 63
    0x10001481c1c1c800c080d04544421174000c003e895800e0460341e902c84500800c50070540c42c840c0880c0c00a648400420003180a000014418000f0901500036800001c10090076401950008000200c0e40c0d414a00000d0550781e50a120301038560320000e0172211010312500355a034403203c03071003800740e94940e03d1180000d40c0d10030381c1c0e1001442010060010300784002e100050000340c0380c0d1b00150520700115030071031003004104103c200140d401d92082d40b0b4102650030200300201d01e20288048590310a00c80c60034121100322402e1802d06d000c001500c0001d0207460130310020344079500726003c0e80c03003401114042d0080d6940002002c0300742c2c00034002508a1240303480001001c42018080078041c10590788140807442e420302d159044070f018032002e5005048602d09068a41c0200540460f08281c543d1181d0242d4203211810300c2d0f001c185402e4858030764840c9840703515184040c011030750f035003450304422501a9030100d80e4241010016149041085091080030800b0602004202c0f03549080e01740c51041c070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 957871312 1250 957870062 957870071
    0x501050c0d060b120402040203220305031602011a010503101a0406020c1203181c03021507030b0619200c0f041e0f110703050405031507050a050921010c03 68
    0x4100f11078152040110034402e040b03000001800501d0310341c000b107a01008100d580d00a440b1100824120500e20150840110304040b0400001c542465180101510a13100070711104581002400c03140010000c290304026000000585007818084e4820082111120801c03254004502505158000d40900350040c061440a0300f9a8900b00b1a655450808007016514051440380504841e10704101c90b1500a020049990401c0d203d5082c0900400d0290b00a46100042290300f4a10303540020310300c0301814500042814540c07900c100b0f41c1c00d1003a01000000250910f000c06948000301c00c01c40d800030310061160860356080119510808030001d4070703c51105444001000280d601c0c0810f0100c0101c08000410089000c0b50040441815058000149029080d8581000341d010400a50210f44001030420aa09040201c4030b80d48044013501d42d07070703801c02c0e01006000b4460324105d076040013408a032001c0d460f1b8641072101d043c115000340c1002c0c00460032606501a2071070140390701c08203282 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 957872562 1250 957871312 957871319
    0x6021b0109150e061305120720092206061a04060801080c1c0606030206030a1d030a0e060c0715082403030d0c020312040c03140d0e0108040f0501050c0d06 68
    0x640140c03100d50500740c0191011707540b02d10a0f29401c0f04603890075180c610030f039000d0041c0104900c6c002c1c441030380a52141c00c00001510503040310080c20000040c02140c004080100d410034104840406034403082c1c04007001c00359070512038040c00d02600300c991070f000300915005902c1c1c44180203100310f075544e480300302c020383c0d03142c0c24075031503101c1d5016407900688403048100c0d00740700f4040000c0c0d8080c402c00c0c0020700c03240c4070380106019420413a003044032203031b03109440d107039494084040380100c1c4014001140b03029499000105100200405140106004241d940c5028010711241c4050040344800c40215109084010201c07001500c0c40410450903050b0341303045081158040101d02400740003140b0300642c60516000a040401c02c52003180000d0081c0031025807480780e96401140a4003100b2052815404d00641d09500601002c44a901510b6003803070440d04050300c6000040b00342045885552181800f0503001e21001c0010019464a810895205403100181201c0401c180c001c0180585 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 957873812 1250 957872562 957872603
    0x203210906041502071b0609080712020d1a130209060301150e0a061809020406120c05090705090303130303020610180b0616050309010e0105071101030906021b0109 72
    0x10345641003240c110300d0010b4003080040034801c0311102454801440c0078066203c410341c12401c0030101283d04500c180401016611035540700161100c20b004e0101103140c01840c0404245111009000306002c806d281e0034007402a40e001d200084081d541e02451600003030f4611183c9104104921030703120b42d004240380d03003814440c0200c1c0b0401300600e80390343c508101c0c8078403c51500500103c0c0e81e546504020600030505001d540700300381c03a007801040307100e003603c104410345031150480304c3d00010902482020504101201c0100c0e07030251401800d940300c1c50350840316032145c260050707010700c00081c0e4204900c509901260441c0c2c040e03801c1d01c81c16195150010000880d030b1080c80c21301c00c01e84080c1c44020380c0b10f030302c1aa60380324010201413500200c0728903000c0b00004500207507000c0d0000b0903507400658104c04c408440354402d103002894a891136036140c803054948140c071b41c1096038035a095010080150f04817545804580400046003520340c103224040c2480710000c40300300c078404006240740c10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 957875062 1250 957873812 957873877
    0x70f0314010501020615120d020a020a15080a0902010311040b12091b0603090f1212130c03081602041802150703080711070306050f010608130302120a0513060203 71
    0x1a4168040c01c6603031120586c401d0325903c0030002c1940030201103110820f24004200d060000b0301c1c0c5801410709090f0360b00400007610134541c4101c2007485042c62404040b58170050780c9620562220f0001012800e5000480003091000f00090003c007000a001c20080351080c098260030b44461403401084e56005401900c82c800300c2560400c507400000c10603c1403900d0000741d0b600c284a0400c4a241007580d0519502d802007084110914403400606800444070f080c03002503001d40c40e40d1f002c0b2800200d0365620a0300714401c0c440038103604004a0741d10b003812071030344080803555001003050000101e031010764100321240145c103d00ca044108419181c00400ca0203031041d145e01611200c580d5036408200340c0d4920f1451584d542240116000400003131914407940c1d003d800429001030266050086c051300315400600f0506812402d0038200d40025800583d0780c032021007204855888112030641640c50b8010140c4020b64850410008141c107031f03000000d007844609a00c4641c42410000301c0180c2c0c1a0f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 957876312 1250 957875062 957875069
    0x1050906211506040b180c07020402070602040e07020d020111070f1509050c040b031501170a1205090a0b2703070503151509130605150402030403090609050a08210f03070f031401 78
    0x80b15802c6c0002c60251200c0c014001082c0081c101516017000c07565131000b00d9200f034001729184011101400f400c141c1c100000200342c03410340020024602d10406400d054096600d00801d594a032140c020200a8124480c00b40303840c15038418000804586401d0361100249044540240e1600c41400640c1c60001007101c003008081c1e00d82c80b1103909041c4030801c090050001c1002d5445201c440d10009442d40380c440138600d1280d43c0b0703203440d0b030395110411605030103560244448420512100e0318208410801c044c44000041070715034900504408207007030071700c0e59000c250b05000e180c0004148003c0d1040e194403c2d1708000c40d60201d40418001c00040303201c00d68904080c2880a076800b000503440354030550704822904e80540d070683d003180020703003680e00c00ca0307045000591601c400c00446030000110300152000321145284541400500b0f03540c2d011792800e0703507003030a01c0100760490111307080111080302d100849002ea8914042c4009403014641da540080001d20b0f00148002c22081c5582c2c3d035059 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 957877562 1250 957876312 957876349
    0xd050403020a200d0f0503040803030a050103060c0504050913020a181d010221040c05060414210a020d080705010c1d010e090601030f111602090603030301050906211506040b 76
    0x80f000c01e80314a05205441e117801c984510080002288100013040514812210600007042c5503042d0324010040d04c209441c071105014003403005110359034440c5035032540700107058107000f0001d0b03446c00003c00040807640f10221a0302c4204c04080401050303000307884003040301044441a00180795030b0030300305e22441c501c00c81d090700c0d04424107119900003508643c04c08c0c0103018987d0150740f076000246280e8400d501c032001c0c1540c82c118050300343c1084000044e00c0e411420f0441c1c240004101d082d526801c080100034410f01c1c2290741c40d000c100c0c2080a40b03010075040ba0080000000d20807000c2d1440c1c281c01d03801c10061043e144040000e41c4034107640b0881050252103c2c000303489a0340154043c1c0801a031003802140c95800c0b100200030900c000d0034000e00e2681c0b0143c3d802c001c41c01807080303002c40a00024003070382040006021540780d8000c0107420060a0310268104224510021044190040c1086050041491165000c42c0140c04503000310400c03503040120705074501c00c1000d480d0700140d61012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 957878812 1250 957877562 957877579
    0x61b010b10140c0f0102031303110718020702060712080708130c0e07031e050a14012103050c0a0308180a050601090f0204090609050411100206010b0f0d050403020a20 73
    0x148010140054086031241030f040301c8550031650051800d80e0001c1381c10399511140d0001f5542030680c0035440b5100d035a00c5101429116003000d42d035150b03010154a100c0c2106400040090864642104070380310543c12003444120840a03d034001d009030000d5411400080002011660050104840400d184d0f48202c0c0822034034540201103001c1c0a000703180d04241595441580a001c40c404055285007980010001c0d29182501c840003c43d000d840050014852110050220741591503000d002c2d0b05248c0302a00d5241e00713034a400c440c0ca204180f244400750181d00703840010541c01c5a03503140a0083c00c00350f60801c903a40c0229a994510710607003d06651301913001000702c03107079035480354000e000e007140d002d031900e501c0d1210842942d240d41d000c0b801180d51407041000740424107009001c024400c450f04040039030041d00003075440406005200081c000040d07030040788029601242c940460703440c0e0070300940c605820043e48644515a080c0c1c0e203129081001d041a45040d24071104c1c20800601684 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 957880062 1250 957878812 957878837
    0x114070c15061d04060501080a030203160f0c120521090f03030919090e030c0d0518220b0105160b2d090c030d1b11061b010b10 56
    0x2034404000c41c00c501009981c0e400c000c60030b6071122082c60032202860540c004542800c0c50910100e0340c0590005032180c0080846900003a80881210101040c20f40211400e000c5414450120500d100c0c006244803154040042c03908500b18002d141240140300780d60b0320502000064800d0001c10400c903280d1081006484c000d86011a081e180311040581101d04006142d008180c0321246020000d0488038900d0041002683c68000d03c3c0460b12013401960400b405100225519110410700405021021909010703602c0c0b844030560381d540c0010000641c20a844e0940712401103030908100c5028200050f02c1d100e94010422214a00010301d00d044944502e07448a1350036140241c003c682c03950030386001900382d044036491042c0c1c200300c401e10308145042000b00280341c0450501454003d0b007000030b4044409400131140a02c1c00c04450300403841009a18000d1008055a1506540301c0c07808251442c00d0240c8000003038802014400800440c0c1000080008000d1640e40c1d58000409580c03414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 957881312 1250 957880062 957880073
    0x30e030a1104020a120e0a0b0603073611070b06010e0907051e042403050408091e040905010507092102041128031d0d03020a2c030114070c 61
    0x80c141070001d881c200c4107580c1e01c0306044064414006e030301131007036014900700c0701800200550030390004400c5008283c1d0324980310740d2084a521404a003800c641e07c5008000c00303c02081c4a00b201030740c02c040100243c1e101c401412103e5000003609a0b0540600d00c0004e101d54010301164068044c01080c0b142ca9560300b5104442c5035110b441c000f403d035100140941004011300d0040c05c0604000304034210102c0d485544180056440c2d6110420582001d013448040b44540b03089808001050381ca0507081c80301642c00c541c0d5002114540f0f90403e02d880400d00510406502050049109580d14080180e40e4810100712501c0c1c406180000c82a58444200529055100d8010500705000320781c20191501502a900e44508010301400f501c12502e290078164540700d6549000c1e600310303d209030b0027040125a5504c10303c0710440c03003e1590005103040940e0207100701c009065005428070070304001c0d0089401b9291038100da0107002c0d600300150801c1d4241041d80c0d081c41680c007035131101c894100c40d4491 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 957882562 1250 957881312 957881317
    0x6180f100501181e030f080408010c05070c05150c060a05060307080a151a030715030b100e010e1f05040503100c14030c12090d0809010b0f010810090207050703030e030a110402 77
    0x458802c00e854040000000d0300c4a039030711806d038000c40809440c3c5240825071400c0d1000040310034108013080000c02c0001340d8440300e007000d940056460303d000c10000030142c00c0c0d52041001d1000b20317204100800890040e01c2e084a131069070190103079844e40b551100019a03442d40031400810000082100180b0610964444240b19010501d50601048110007107401e012141c0c00c50b203100400442c500f8801d0342c250050500c40c9070191100c03003000c0d503400c80c0144000780142150b03040180d0050140c2195568003941c600d01e02e1058814201007210a1010340a41d0003482041e0003402000e019014544151207142c15000d056121019800440c403903602c0c050340b004050890210040c4008003d090200c0d020520580700107004042e40c0f80c81050141c90490300820340c142c40d0707041a62005158030340b02d405808280d82030030301d802d003a10b0701c01d00c0700820740640e0422015a0300c0400c40030103000000034460f0403030b40030b92030300c0940c81c4000b028191030310000300b409412601902a24251030500d50b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 957883812 1250 957882562 957882599
    0x1021308160b03090715050705280605180102190e090c0912030403120306060e0907021b0a0e07081b1305130b090403210b150306180f10050118 63
    0x303440400d0b80700c0e41c506c00e02076069203051000074004901c48013040b90402011030040c3d06044003250b240217580e480038541e03117a000300401d500d0b120400700d036008002c07100195180007640e0003551208051004461040e11211001d000148921050704540c20034028643c010161443d49078500709818090094190740e074240c05c18548004c000c00000300c0c83c04068a0701c01d42c03c682d0003250083c03508000520000c15000c241e032055103600240403006400140e801a507041050032040000700000010300c0c502516442340d10300b030320f40710100a501d40e80002580e116540c4002c100c00704009616010141c1d01441403d00070342c0001d004280214600683c0000706e1340641030300440d0000d0020089503090406413001c5010458400055650711100b00c8400e807c1c1d40b407010208540d05007a4000303100000100c041d0740f106400040840d91580ba20102c00141c90b4102541400c94140f0100741c0101e2902150440d05c4590311103804030790356200b00c40300090280d5040414290368207110120f0030022001c0d5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 957885062 1250 957883812 957883831
    0x40902090a0e10020351061b010c0f020f0a0b1306290d05420a201209100f09060606090302090a090f06020c01021308160b03 55
    0x202d20000300805130000b1803240c850501b00c031030f00740b405400002442c100e0714115400b05040d440100c800d070b4400d0041d03034202c4000049001040c2e4102010600c00c0c402c545900c030f4150948070b9154074404054220b4042951541d4810482641485080b03856800c1e801900303030241c0100c0080004a80302110081c0c10250160f5110b060b1402e80d13580c10111000100f14640882e00d091030701c66850910007540148a205441130101e8003059036602d526410700c0d04c1c60f8078100447d0076010182c4000d1a01c0403142c1c0e031110381d00e40f500c1d810f0b10f030741e81c00356410072200380c0002402c040c8a91011652141c48100e5100104c90850401007100c1c5926040700f0020401c420901c1102e04485203c0d5060007a130304118041580020407043c0d0381802004e0b250075401020502080400c10401a00e0313540c40a03601c00c00080300080c000000313250000340e0a0710010054903841c000b084400301a60194010107214403400c1c01c405d100c640c0d6042070b41d100d140014941000c03400c41c0c501007000425103401154445200b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 957886312 1250 957885062 957885073
    0x1c1a0f0d0b0603150708040201020c15040e0405070812040e0903070f06020a020f0d09090623060f0d0f060503151510180801093014120a020a0e040902090a0e 69
    0x134000080c40d4100b2904040082c107500c05110541d6018881c103440c141e03003950318079440b01450b20650710394841c80c466820080300800024003804030901802000c0c240000949001c181b2441c1c5002a540040c01010001170745800071400c0c00000008035810103510108404800c4500e0711420029045490086e007035000708400074081600c14451039410703100315240c0341d000906200850040311416040550109107025080341c800152166195078200c0440da441d5460112600b14562402480c3d0704610b074a0410540410b160555041901a51820780440700c035400e4600320710703002750801d840e1810b010b052082c0e0081e03d03003001040c0e09120f0300681402c4803040740d99001201c000c000daa0140c4416590b0f036036204d08105440303c28000740c0300300c114032004248140e0b58015060340448030b40000e01410340c1c2214140a5484143c64900751016840d4a9500c0d04241510207503001000c0c090004007144042d40c03803032500e44198800190040d100d03c100355200700b0208001d00a64004a0051154 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 957887562 1250 957886312 957886333
    0x6030c05040f230115112508011401060e03030a0f14040b070501021308120a0c170309010912030603080405040b0411070309150e06120601051c1a0f0d0b0603 69
    0x50484481c02d542c603151486007580741801c0310700c61790b141d00800030400c6400b08030702c1100d040002d03910440f08400031111403060740d00554110000e489503c282d015500700205601a80300032030355241200c9041d01e4040180b100070b4101a1a07200f0780e20380030082800802c2ca20304480c4103018820a00c98980c220b1480c190b12502c2e41c144c2604034a2080b10340782c1d000145c10100595a0311580c0003040c01400a140912401c2c0f4071072410301824100b0820040c2000d60b00e001c1c4002c880c4d003518114050b00c8510344d2401d16158940c060070345004180c40e584403440051540302c0c840d118401c116900609410b04181c10b000400014062800e019640a1b4652101c081030040390401010440d229495056280349045100c2c484000200404003d0104c0d044801082c3d44074030049884a01441101801c580d5840005860741e000f1858a44804c0441d10315140c400702c82d941c45a900050705035100080c0076145410884020340002c00070341c00113540303c6400d00041010702847c0e0046d41c0101520b20720401d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 957888812 1250 957887562 957887591
    0x70e030f16170a0302060f0405161410050a0504090e01090b07050403120309080a0c05070f0801020d0510030f0f110409080a1e020d0c0213050a050f010906030c05040f 73
    0xa4060034a20321211075001000210225001c81100440707150180c079000e0340d140c4000e5280c92008204440400c0110000f60810005100c417251048102c401c0602554488640081900b0541c0c000c40c0192510800609102e028034161080804c00380c0e100f83c41d0500304000c00024001000146210f90b40f21205800042c00151825110320343c5a0b40307042d266440c50500c041d400b803804411905040c601602503010820281c21a4150455810140061143c0345807641c90300d61143e0100d001e003d004000803503003d01c19002130000b01580c80c01841180c89040010a1181b6a448000c0c03c11801444030000038180e0400d02800d28043c01c0703000c0300c222540020038151041e028040f100c00d40d000400c1c41c011508145025851002e800e42c1d22072445500c03201039a50342003d1080424040c410300e042045642c0d0709880207480300508028001800c01800c074101070041038444c5030300c0010010010542d5212445844100c90700025210076040c07a0106000040c0300c400d8608410170303104d0500000f14072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 957890062 1250 957888812 957888823
    0x323030c070b090310060e040f390815060d0312090606050108010b130314031c020703020606060c06070807050d0c02060919020607020f12100c090609030803070e030f 73
    0x10102e0902d69503940300e4003090300f481381000d003c00302e20b49040c505002008404c150a540b0070751080002101a40504150960120380300e0802d45c3c6e105101800c00100e01440e104a40c00c000700041e4100b0f4030340baa805142c84800280403050b800c07810783c00040c102c2c03600c0340e043c045c50390103800e00d80e50a2080500b000c00340d0722101010782d001038032402c1c02c2105503402442d0500500d1030038a581d0034840c2225207002855050b200140440c180d01c265103e407800203104480828800202181c0c000700501d1350a0b020f50495801034025002c0c680004140f41400c80807152811100b0002e000c1c2540c901300103840b8840050038550802c6024060b803028100300e407003081074424040c5c008280501e810705c00e070303450012686140d00c0d00141c111807040050300c80d90241c07540d5030703812180c60f441003a0500c0840c2d683e520402040d603092182407488030082c0070a03804078000d0b1071a035a075481200d0300c07114281c440c480c0a2000600c0100200000341403184134000050401d54002c045d100c00c0c4103819404c900d0311 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 957891312 1250 957890062 957890069
    0xa020a021c090e0c070b1008030d111306090510090803030a0c02010912180f05030c0108130c031a010806150f03070504020c1e0a0506010e0a09050109030c0311070323030c07 76
    0x24200252203020f00c000c3d4080c06e42c2c0701c00c185156615103410130b801503449001e02c04900c41c4041d1101e48030484c2d0005003040d103800c1c405003190740c0d1380703560f55030b10042c1402c61a100340d500404d4102102c040140c4200041cac0c0696031100700540c03443e00d909000c007000700328242002007155a14030b0220006103030740c510324081c2c248541e81c80010641813035034054030320915402001060850707001041581c078040b616070b038014800d08020205507034440c1803c0d1010b0034020003c001092110001c030410800d820604110003c692180038680e88407074002d55161003d5500c1344d00f00d1181111600345252078100705501c240040e0540c0c00003569240401c06076004400039894a4000c0301d1003046607114680351616807015500100f042c2d00d42c0d0344446846502c1802448074090681d00003800c030040c03540003015110b901000030000a881070800514801c1446012030001d490a24801011a40040d280c030a894014494915000d421140b002c00e5503044114a00180010301c8032100e020300a000b0030000707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 957892562 1250 957891312 957891331
    0x90c04090b0610020106061e0e27150904020603131b090c02070e150a031202011b0315150e0303030a150501050f1c0b12070e0a020a021c090e 62
    0xa41054020000200c643e0500c0c84116890808100030341c9a000817404800103251510406607010702000b154a40e0000910381d400c40d01d0704d0007a484604042901e034203a10a00000030301c040d1070354040032507019a050702283c3c0c40014031001c01c025180c140015038000504500600380101c3c15607030110503102d140b1540d000480f00e9501000001418000c040074006580f0140902c1810800c15030800f03d0003a02e82a80202e450011006c4c03a19040ca444014640140900c0c201e0303020008001d010741180c88000d100e180d60b080804210600a0056410f19001422140201c0303040c0b6008214481310350b000c0e20200450280c088405440900c01180200109140445c51401c070308525803a00341240c0c007044c1006800c00045102c42c80d8402a55113206501156282001440014001912080f00c025900040c0c804041041000c001107a5084400703042d2104110740e240c00208007203000f825083c0000d80c10075885503011445024403a102c91107103040814905448180c00303800c0328000c9909040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 957893812 1250 957892562 957892583
    0x70923100815060c1b0411030c040801060b031303030c141201140f09071103070606090b03211804180c1d0103120503090111340309030b090c0409 64
    0x842602c0081d07032002152040d140d00c1d140076081840c69940d141003041c0400b1801c0b5060201074981c1e959005030045c5408080c90946074109480108217a511a1242184643c607029001440121b07120a0b40d20451545503400e84900340c50300d05a000d005101385c1c40041004580d03003c41c4055001c0e0207030450f401034091a01175981441c242d005040c0303130740118034030582d00e40c02008019940e200049922031001d00d00382c0e40c04034088001615602940704000c100c0390030064040351079100c0d42d110a8003440d04030300b100c070100300410f08024071801c444540c00c2c0d0345000300700360380e01750000321664290243c0c046d00c00a1400c0400c580140035103407111007100e030550162420040126921140040424200301800041d4550340c0c0b0002c000e400b0a05003414402c0110005e451002c0a61003080740480c11400e05a541c00362413031904484800c40003000c0c00541c50000b40e8441e10f03920202041295054841c1b034041c9096848035180510010480140e03071244016034240d0342c840307008145816108000703680 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 957895062 1250 957893812 957893821
    0x120307020c0a0e010b030402131103040602090103180825140307020114030f010909030c122303150111030c160302011e0906050f04170f060f0709231008 67
    0x500300d22030f4005080201c4160061000704034810859822a0f8111407a86254000b5410f05015004e035511030386810030048200406d014441c2c00a020f580800d0ba4100500b00c3e050740446200e940c400d01c09000340070140300701c51000390013001c2034031a00c80846418043c1b0742680d640100140b5056910b030392540000c07e9010031541c000b203a4203140c2c0c4210381d04500318030300031021800c080c10511850b10040d41b070b403214105050040044080080c2c0094000c024022486405003401204400085003a5034404180d140c402c2810196406a0b8103240034514034000396004603a00e00d555070854281380070400010b04107040070400700741541d25a03036000000034030f140000750001501148058140c1b00102000700b8141e40407550501f03441180c10300517240e0040200388801405183c1007a905503e6050314440e015500107203012400c03100ea8110740c0b05694045418131060320030780d0078801050404005004821030a001d040702001c030011142e0343c1c22580c20000d400c9501a03510071012030420340502 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 957896312 1250 957895062 957895069
    0x1203040906050d080f0706020702061b070603140604051e07030e0606060a39030306030b07112e020a0c050d030c0c1b03020303072114040e09120307020c 67
    0x402030404446401e8020f009490f200520f22624040d208a00030000303002e000c00400341d0681e0700c2c654010b014a5210303a10a030388600c0168008196020303506c00c000c4000340b010311a0140e8104c090034000c0101064503800284030141c0340181c54500c80d03203421a42803c0d02900d04410710b12808031a60702103868180404400e007410300c0038114074040e00081180303c0c2a83d4019140b010500c440420310600c0f1424038002c0d00b02524031619101c0c005040d4100e20b02816415081401542d005500100b115100c590059031030440c885242007441d0070a01d01030f1100d458641c1c1e49140303000020212011071801801000c02c991103496000003054030996040300b031040400c080c0c40c400c41c0700d003002c1160302000100a0400c03078415038000c1107004901c903000740d0000c2c00d1072442c000715030140c00c80e0b4840001349007002d0392075108080c500f0703c1ca4402c071100302e1240c810380110a1924044010030310301410024513102c58000148030b15101d114000480c5285080b000046102c0c6903c0e501501c080c41524080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 957897562 1250 957896312 957896321
    0x7020609100f091a12060a0315060302041107021f0e0405041a0a15090905120c06040317040804030f0204090f2405061f12050411040e0f0a02120a0212030409 69
    0x6022400760042d04400f401030003c2114041002c3c1d610100046d9036100010706c101d1402c0d00001c000c4c440011414454204a400010940788215020b00010405a1601c41a40100740c2c000e940142c0e94241c036126014000780d45000800e02d07207001000c40e40940003080a507070702540c084030384248064241a290000b411a2030300151600320900c104005484005200c4440c1c1c001c1f955400d039a40c400c942001410009604901540d032401c64440700d103080500d0b1607450880e02a070215600094074005001d940007100d1103554070505407400c050854541c21220305103a14101e800542c0c0f5050b0760003090070401d05a008904c0b4003050480c0d0a40585180030140302071014070b0b0341700d0400c024400e0765542c42e0f02c0c555421a1121103400090103940d000c0b0703045603407400781450240c58070b801d12043c00031080e4500400c41c02039a052048074010000c0030703580c500c894048030781c40d04401d0715100141380180c0c2143d02031039608100c400305201500001d586130310070000001203600c00201080510464051b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 957898812 1250 957897562 957897569
    0x902210c0a061803020907050c010e0610060507080708070c081b03010e070302030a0b070311030f060a0605070b070809030c0f0303041109160f17010909030e03031e07020609100f09 79
    0x40c01c0e0141d03d50100c2200b45180d0030701000f44150030483c00901240c0c0300c1d205844110040100038003002400d500b8180e20340f03105890fa001d040950403008249107014404851069520603021031500100740c85090300c60b0000c250440b032030a84500005050b0004001030100d51402c2100c0c840b44c1040c04003050b085840784203460129400208042016039004600510303015000f44424a603540c59400440c001c20403080000320002012041c00682005609443c0c41034030107845941c03142d520781c1c00648060080050042910f0020000174030200e210359006600590b001c02200d0401086507502030400704048021100c0c2c0d40003108005c20f10800002c400001300081c5c8a014031400d00d00c226402000303034400004144410070184511052089201000d0b1403188500b82c4401d5840d00f226101510024100b40c0006003c0f0038241545d00c0d0100c102d503802000292410f02040009000c0d20064003d0706080c0c1e84400d09011002c100c1d1110401174076011344035034442c0c7c0d10144040c00948480e07490f41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 957900062 1250 957898812 957898817
    0x51306020d0e1f1b0206040602061f0b180316080c040f02040b091507050a0309062316060f06060324030201050703030209031e030c15130201030902210c0a06 69
    0x54400c4074034942c2c0102680400a01c0d04459544c0f4040264502c0403c480e0002d4100f60700050000f40640c5c003017482405811303a040740c100c1e5141c10441c16420300286004040f107002c4208203480700ca0404840c40180110040c0a40d0020155840001818086580030303114a401c04c11084600386480e104e800c0c541c01e036124045042a003400130a240c3c50040002d141c0c05030807a8289025071280200c00d6610f20f81e480360480741c08503c9031800a000da0041d20038000461010703400c10b803064000108850ba00c0d08021704260410081800c65505d40150341c0054501903995400485c40d80114000d0744007410705174602040118031551b03241941d1016101903940c12110007002e01c0142c0e444030440b1030450705441c0160f11007481d080004e00300324403e000c520103e0300d0001e8001c8403107004400760000110000c2501c0071540c10503000c006115045078864500b09006a0890041d0b020381d02514070b007800586034010030010200d0018040d0100c1803d0310301c0e5400007100c4035072403400f14100b5000e440c091 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 957901312 1250 957900062 957900079
    0x1204111f180f12030c0b1e070305071d1203180f030a05060f0a0e06090109061b1704050f0d020703020a06031107060906021e0309010e07180b01051306020d0e 69
    0x81c80082200d42d64010100b0712141541c0c3d40b814144589200d42c1019040011030000d400c202d060f03c0810f52505110300488010080018003486c068401c0d24440e120b503480300c14040305480c0514100e10100050180d00c50380389081b0a4a0b4182003014101402070501c100489440c0f640030400041100404c0501c258070403194440081e40c086006504640869403024203519482c0004003c0c00a944101019124035010004441d5054008048890040800300a0202c11314052094061031421640200d0084d4241242c0380c0c00c2d031200309521502803010f403070742c007030110ba030281c00c2c0b880703100e000801130380228424000d528128148400810807418100507445d400402c07600d032402210000381010307598041c0d180034031a85404036030b0502e002130720090014034100036000c550340040d590410300c0d62070082130b102d04500010b03500080c0e0b0720a405060080b40c161b14400003500f040d00c819410000141b000140d40f00107410310002408164001d00600341102000030080403041d00c4039440303070088 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 957902562 1250 957901312 957901319
    0x270507050a1a0a0203041517060405090a1103010603170a02101503031107080d1d0a1a07171204110f0a0b1e040b090108010803030c1204111f18 63
    0x95040b4034100460b40d500b02529503030300c0d180984c254000c0d5400210021500c100444000f6072110005080c055440000f14440d200d4105100840303030111000b80007a40300e0b0700c2d808003048000445071a0701100400102e4100c0d00c90741d41800307140d0305155101b401800400c8a03200c0540601000c030a03050b07620009c11051500500384605c4208510001e0188484414146201d003400e2141c0f02c09003510004458400e03640d070718010040c0003500c11102005465801e40c8069181c0340c007403407080310750b081c00a652500103c69078040c55801084100c1d01e628000204641d0000f2078070151210071a0441880c155280c20b0402d0030310b03030b000010418810000342100102d96910b6003011000d40d240d4a07130300381d1101a048019000c41c50000185941e0450110340005d0030007c1c0002002201400c1c1d8030301c1c07041e90b030311408580d0b20f000a40300760203003103c24030603003040540d0702c8646c0742c2c000d0180d06021f851071400d0f000b1410705162481006418800d0402d14030229801c01d40c0300700040e400303064080c9540d24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 957903812 1250 957902562 957902579
    0x607120f0f050c1b0415080f0c06031b0f0c07090504060506100c12030609090501020c010b150909062b11031218030c180702010c0905030d1101270507050a 68
    0x30080444000450584c082c10494480360301040f174004940341c00200d407903203c038841035903044620741c51500c1d4410800e00d0038035418820f0540c3c0c01400300920341d11060360405000745998010348106020f424090110030010303041000b04600800c050140014a4202810281c0544000a1045008a241d1081540c466510a041c03549050b002171b212010500d0018045000e002203600c41c5010a0500b202c103400d0200c198000c00d88244e0380310081042d1200e802c2030108035807075600070034071b80c182c01c1c4011203403418108211503000313070300801400310f001c0d10341c030300007418107041c44400b000c0306a0002c0301342040b0100e00648030707210b4202d00606151144128601c128130408048040403000f041d01038245403410440d00500340b40003040b42c0090002140301400100741100c48000640c2401d20440500303008103500f42c02c4e11030240c050200308440300410b564252030542c40001f15035072402400b901d2015100321032888c1180003220b140c092800d092042c90842503400803807264210302410410a507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 957905062 1250 957903812 957903823
    0x2030c030609070905151c060e01060c0c030606170105010819151b080f0601050405150a020c12030408060a02190c03090803030f09010c2307020607120f0f050c 70
    0x80116a5034503950781c1c1583c1280c640d4a075074421a040010301c44140c4d0300303482400140c428a1034690703400d1440000608100180c40444c400c2c0743c20380590000521501d4440c846070681c0c0e0f4010703950880526a2035480808031015544111142441c220b000c4000c00001e01403940103000103001019001140184c5005440380000000c081041c503403a559450f12603900036031480d8072003410960f5003809112010380011342c01c0703c003183c80700d800c82d00258182d8040c2096409546020b84113107410454040d8810040d8040031070b0400358483c0c11060600c558403514100d0380f0840c1d4902039501c0d103242201c95458030001130400390081c9c1c01030250701501b481f0864405551501c51034000c00704809801c05449035140c5030002040c42c000002040910503218810078000c2c1201c0307000304100300c070b20b903012610f10381c80703c22014a89401400000c0c0502c4910090304080380010000381c60850300f507a4945000110641501c04601c2d21404941400e4024074801004491410041d01c1e140e42990300d140c440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 957906312 1250 957905062 957905071
    0xb270f01050d06091103090709050408030f0c0903100f0b06041212120c09060f0516380601031103010b0304020907050702030a05060105030d05070c12030c020315060103060902030c03 80
    0x100410001803289064008500400e1104c0e41000030110a0032040c01a0f8070448aa511030703c100640001c0c054080d105245c4503030342001c101c60841e00c9000c50f060620401411010480e48140024600c5503820300070300b00c540c0364a810010b50794035210310202c1035903100c21a15105510501c010000e130104500040603082e8003041d001c2103900120802c0d14210ba20302994280d151900310300c04811030b00028448155125503c440c0d48039070105c013040b141f0b0f20400000640942c0b0714108030340040d2404007444000d00801400702034502c1914042e0300000c000014809012808400f806000e58151266110440700444c0c154a950306180c800e890610000d0310090062269000255019100e0401da82000381d0040980d922030450b420b19590b508028060307240300e80902c20391243c44901800c111421980d012054052891401e00c61035400d6042c14015001d2140c20000140180c0e424010313921001c4400c402e442c4503040c4403000404540445c0c018141c644c1c41002800000307804201682d500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 957907562 1250 957906312 957906317
    0x1f0806040e011a120f07060309050c09040f0605040302120a260103030207121a040506241309020a080a030206100518010e10080f030a0e030118021311040b270f01 71
    0x28048244e81c3e1514164005003d00e03402e0017202808260658581c002c01e80180c040d0084403284550942000100d5800761801451100718981d01c80004900b60015544980680165050310080e6034000c440d0364403907503042c000a000e0240204204d0080f22045980b6992140703034400560451350045c7d9a02c40901920a45a860000440401c10007006103000449011000c0c02a814a858020790700c1c1410b6500f490441d0844a809921341488034a01d00c9800004040c5071810300580781030401080801c2040c1d0308147d03141c07070104070301000300040300d0414400c1d4018006440d0840148075800d105402140c0b00d00d84446030201050f10748607840781175a0b041c264204403500d40120204250f0441d601c440e1a40c061420b002e402c030140400941a25001c5455440c1d043c095079081500300c0d03000210341030800da290b02081000d0b04110710900c0c0c52034205403001540341c90082008000d500036500c503180c041d8001440d60700c0010ba464407120041c031705d170551b003c11107508070001e6044050180720504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 957908812 1250 957907562 957907579
    0x1801060806090a0f020f04060e010c410c01080108030702090c0c1e031306030204050604090c020f011a010923011416060b01091505181f0806040e011a 66
    0x9210466489a9108010404d08640da09401c15050303103540c12512541c404113007040301444c19940120020110150700c1a0086074054040715031034603030003002d813481000030001701840b01a000c413030782c5011400071001d00030a10301e06138030001421030605030001034154100380325a500607152002c071243c0054030040700c182c680c900c01141502d41300c410311000c40341d903900c040300c0c901c0c4017808802010401d02d1031071022080d6446180a805030700c2544540c3d0f42124040100704010f0482e42c3c0031036810700180c81603503016031200581c6429944000c0341c000c1c0110040440c402c10713680140c41c110003031003100340c0313a103480e00c40c000080d0069104060060506c4860396030540b00d040c1000444180d0050401e01d290350540c1401c0003002007001141803400f1496403000414446104c010a2078420004e655a51800001c29122051640301400003071b00024900b004921000b80d425140c90000040c0c1d41e010307503d01c0d00350100320641d00324482d1952982d00d00a0782c14809075030260240c801400a440303641 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 957910062 1250 957908812 957908821
    0x3080a0b28081006061e051204060b09010e04030c030305070519020705190f0308072906150a0212210c190305070c150b06030106030902180106080609 66
    0x4040942100d618060201c50001481400d003044101c0301c02d46401c0c00440300704050444202c0c088481e140078044c080749203002c0b24003500107041c00b00174101009251590410b600c60340720300d8411005480884145841c4d40c005078003030030086022070042030759150100040c103141c1c074080c10382e80d00404003500b0036480ba00000d4010303004004440740003900380407400c64114545030094644400b400769600c034010090180b0b403803140d050742c0d040c20740d8100900d01d039a0500d0350703503012042d038000c101c102c40500c00b000350b0062906c107005550303108a001480092084c50154200710340901c10441f0280e0b101000d00581d556594001050030010001036511036580382c0d40c2d5030740327840540c060100000d8018a103041088800034000689003801c001300418400784ca00c00303c00c1e81550002c0700c122002956120384d00d404280c0c82011084600c080723160020320603600e40e002c2000307544240c002c2c00119448014400c1141008100d5105112080301219510750618100405030074002d003106100c1c052210206 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 957911312 1250 957910062 957910069
    0x40326040f03320d110d02120307090807030c060f031a01050c0c100c05061806061309062c0303010f030f0507120b01090c020303100504021c11031f0303080a0b 70
    0x2845100040d16812442900001d82958980032000304c8000a03482d941c10801c44480001d400f000d0054503006014124800c10140708180c0000b003d04041041e408030015040c401072020001560160600c98050303420404060500103203084c10400f054a411103041084400c8582e0383d04000e0246403569075041c406921500d070078101414950700020049000031000d4001106000407480381041d60390b07660301d90801401c0d6104a04d0709190300c0c1c04c20700000d0058905000407081c0e054403c1030000310f6048544591003150306900355202010811189030180009203a01e441c2a04d02c03e0005500c1c56041190f080c44d400650b100c010310041001c031040341000303c14440080501561021001c80c40c882d8240301034090028413440c0d40b410715110090744c5007403012013264400ca101d40c0b01030800f146050300703200095100c0e020100f182c40c0c250405164081103401000340002c002e181698990914580b159941444d0100300f0f400c200d0100020000030741c000741c0942e808400c1d07040c00101d101c07152000c13 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 957912562 1250 957911312 957911363
    0x60b01050d020d02031b0c151b0307020705010207140319080403140d031a090414011b1101180b071d04020f030f060f060409110f040326040f03 63
    0x1281a00342c00843d440071040c80d6940614820024060a020120f21702001c0d40198400d01036090310542002144002c400321007203d15070085a03000c992500c40042801c2c2203079a4206840d4040140c0141d8010011903a0401c9003002810007003125030201c45508000981d64000059150003040d04204680b00b8043c40100703607001903801c09070000100a40ba000b03036480701c5240000c800402c0c170b070500f01700c034210949803010700064025041b0030a0340c4840e1a4603401c0c40140021800c1ca641351900c00340030b0641c43c0800003c603416921500b64442100c1a00b50035541020000740141d06074544043c0411800c0c00442e0304050a800c00144041503581142c848480307081d0600e4009000040c0c05071101a482e004501c618003a07940c040c5152100001c0011040248030a01c0e4000d4041c00705110861403940312510b100005541035190a4000c062140590007a40c8180d03000e000902032490f0410f103540150740110581001130f4502818003143c04409a01400058410381c080001c034000e030780d4131140 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 957913669 1107 957912562 957912577
    0x70b031e0f0a0207151a0909031810032912071503150e04050a0b0106050901050d020d0b09010e06030d030b0312090d08030130020d060b0105 62
    0x400704000e908551026603c1d40d801c072181c4807021a451155000c3d01034148142d001b403034175143c1007040c180c80007446414079401c20481c15a010404c0b078400f44440104a61800540e11003100840c0103000b01c9000140c0308401001c03034041744914104d140d4075071302e007240d22507002c071541c01a25840740d18511494814441000c2103a6004c2d01070b0304803125400f41d50030744118484e640c0c0c0b40862044c0094800780c0d148d0300700c00070010038401c0085145d8050046420a1440c03d641c100008009110b003011156005501150b0661034910f5500900311000c1c00401040d5556150744060050034401d840b40f5101f0302c42d0700a001d2075907009018a0620020050181c140c1c07810800306a00c460b88020003296120202040d00b07800191007001860103010002c42a600420b42d01c241a621481c2044401d90b8180302da00d0b050700140c0d900c002c802450740e8441004103007070300e01c180142d641c0d014404 = true := by decide +kernel

theorem cover : BRFrame.Cov 957733812 957913669 := by
  have h0 := BRFrame.cov_init 957733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 957733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 957733812 ≤ n) (h2 : n < 957913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
