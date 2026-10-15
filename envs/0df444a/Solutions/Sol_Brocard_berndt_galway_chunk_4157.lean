-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4157
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:44:25.767896+00:00
-- url     : https://prove2.me/submissions/614a25fb-a7ae-41d3-83bd-d2fd35231df9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 747482014 ≤ n < 747661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 747483264 1250 747482014 747482017
    0x150302211203010815010e07020c12010605030f0f010b060304170a0e040e010506092a0d09080c240103152d09050c03010e102703020d090f120201120f060803 69
    0xf4802c17103000c0c01c100d80c1c1f20b044001c0d074110f00321090b00051b0f000382411826800c20140c0c80c841b480404002103640ca4482011a26000440c0441071455114844a046000c3e0038820000c81d400d007140c10504d5824642c64103144a1400e020401008000203050450380340030b5070340d45252042c00b8100348000c00e0849111402000c003107801c00c0c011504800002c0080d1201401303180f44400591407182110032000c01c168086c0c10801c0205030042c0d486094001043d440800780540c07601040081a249064a00c98803525100003000506229404014000100c0c1008000848200482e00040d1030b040b1401e103a0305002001c0c5051a82c0e41c00d44400b41480c8015009520064050b40440741c2a241da45e041c54200d070803090001005403c1084041001d01558004003101c04180000342c07400124660240c0000750124011400759010074071071030b070071600450010f0040155003000925945090050f9450340d0140030024100440c0218030328400440741d2140009403503074102084a1501d07030020a0f900e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 747484514 1250 747483264 747483283
    0x160201090f0311070609120305031b0708130b0703171e090d03230615090a0f09050a0606090501030c0c0b040c0509090303040c050f0301020d0e030406031503022112030108 75
    0x8038000c43c40c4c04a105406130a50390201d80f40240070260b000d5107900c003120107400c080c28071942000c0700403003004191a00c0028040d0b1a004105660f610410000038107200300065008205104042c86400003198115522140801b0700941c010966a111202498540312500c4103030000c036100414000d84590004807410ba01115807030800224151000e2034644c8440800f80d0041158500c001400d141440e030302c0300f40c030302075550445801c2c0448040081c0d0203118981181030083e00200b000c11100720a0702600e6000048488100030007420700c0030043c000020b5002d01383c18542c03551849a00c2e9441402d00c44141034210400380c80d24105450724185410091180500c600091404200c000b80080201c9014a500204040390300b86030006011500003044680355042d5824440d403000001d50740503007a032156020002d03550307407410140302400703c6a5200351004220f000140900040c0c560208820408000800c0c3c401c0100700c00000914001140e01c1070001d0b688044000682d4260003d0700094 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 747485764 1250 747484514 747484547
    0x30a0e0f0106060504051302070f02062d09280311030309060d020301060e090c09040923060106080717010b0d020c070303020102040509010905510a060e09160201090f03 74
    0xa0b60303e0b040c1c01c203c059002e00040501344ac0c001c12030f604c2c014a003100042c002c407030074000780282007480d10440e07021403441482c1c1810345010000d0311f10b4030341c42e00305000210702100001d5070040200d10a800c0044400c42d01000b080001c1855409220399070030001d64038071900c000e00c903a40c2d40c40e070120841c020b90000c1c450702d00424100000030000380703041407005114000180d010703030510600034104006007000c90011b5a103414000c50260342c0b244041d25142c025401132006021030351505c64010081c00c00203140c0020445a00900c10707052000b00700d024111110285601d48620126140100034840c07446000582d20400000104058064000c3c0007190000c45d04180181c0e0b880c85100c06482e03045030300304996005100c030314090345a0000481d06903006a81034038034104513201c5e203076101d00302c0c0890341607440b6800410b62607914110420802070025071401441e070340d9002001c151306000181040307c0c3d500c0d0302014481102d2003544940e014640018403ca032060440c00e01034080d108440c01941c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 747487014 1250 747485764 747485779
    0x110705030408060703021c021303140c010f03110405090c0f0705060a060f0b0a0305190c020304170c030c0621070309020102011808030c1606020705030a0f09050303030a0e0f010606050405 82
    0x84c1c4060103842a02c2c58521508880200c084a1424590095108548401d004810041d021001c24a10803a0501c10700d4648018100c00603c0f01c000b401c0c0c5010030600d01c041506214075640b60b03000d50401d0301c080316420f85502072a502c84e400d2800080c042c00441240c0b1040c0410700303800340813000558901807042e2090800c00c2c15159000f5014003074450040400c41c0c501040820202d030b10030740c081a4084c14034201c50850b40489080f400990701103851810042c4e00214081c440120090601060861808002c2450b01081c0021030b032100300e120307400383c80f4081c003082d2500052000c480c1d0440441d03d0f1420a0268542400e02500a043c0810164019880c100010158505101c01c00200540000c403403411981c0c0e0701b8028825900030f044d1105045040349648001507101c0c00944840c1c4e2180700035588032460720200170450702e03003a45d0031070400c80b0030101044617072408070071a50404400c401c04140f084a0904441c54180e1040e205d04d655071800c40005074030303a880b40142041d500100c0700e54 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 747488264 1250 747487014 747487021
    0xc031b01110c2407020a061e0c12081f0f0e0603210a0302071a010501230d2a0c03020706030c0503150102160e0103060c0306061b020411070503040806 66
    0x390354402e42180542c00807074144410140d0700110321081c0700d040c480300c95180f1340740c2a54040b461590082e032150b800f080520000400702400a14559400415413401600029407a19580c5200840d04814418050380f040841c0c81d04200342503501e8181d20320b001081415070f8408482c500c2e6402d9201e2102c01c91186404a1524980810201c80c10441c01c80ca1400c3c00701440c02002d02030388210094020b150b420404600000d21507140a541d03000c42400d41800c0c2d62400c0d00140c1405804c951040200b003011125802d24001c0205071204111802000103000c0d01d654021030203000c2c950040211410015141d4070a20f0340118041d0300d052090742038500c02c580ea08415016101c40b82d9001002c02c40500008143c0003030801c40e41407083c0d0501c1280c0c2c80c0c1d05a0703c4420140c00b03e58001000320021500180709000081c0500c40e00c00c00c140c502041100d00c2d1440080131042408030112103c41c0302203244080d0358641d0001840f0341c1300401070301ea44034464030b001640d940c0640300b40e44240c01400000f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 747489514 1250 747488264 747488297
    0x207060302090310110409150905090102040b0a0e042307030e010203310b010b0304060c18030b040606170c0405010f0305120a03021c0b03010f060f170c031b01 70
    0x2610504200500180b00e0314403030703c4d00e03040508903040c026550700c0070a1000048804880c00f81c0031404010f4200501e40300d0401d0005016180c0040c46942581c3c0108001c000002a200858142050918104084001e240300050280040c0151040c140c2e030040c080c0203000201c41d00e0325004070070644007044100780141410f42030340001c0b50b800ca0350046504191070f5546581d074003030061855000c12140c40500390f0351081c21a12080e0480c2030700040105c10482081003d2041100310030b142d043c070000054940d418484582c03442d003c01880e000e04040401e04100181d00300390f018100d402201c0030350784600c0c0383e03441e0b0740d440c0d00c6c3c01303144254180b034000141c0c40403561a8030266600200608000904e020080c881940320b1400c4908042d03007005011240401c009440313a01e14140348002c0f80036081c0404060075668211440c031800d6141000800000f607040c003215046941c14000701c113030300440e03141c018200009902000c0e01341c0140040030010840e03840c4004c00d03144098907661408810070340c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 747490764 1250 747489514 747489517
    0x60903042d230103090b011202040b06031e010f180c02010f0903030213140303040303050a02100509033703241d0f01121b080307120809011a040903090e01030c060207060302 76
    0x38060451000c11b80107002400c0c80c03208040b80c0b503001401c04070b13042140c0740100da400c1e0300c2150182000c810364071450010b0680d00001d1030042c00031501d491265424800c600b0071005124115245150765060741131304440c000e40245195070401141040030030103904015001e540842c0c10604c9030000b80c24041442d40c00c5001c0d241c42900c2c064004d500309070540e54182d4813940705120640542c1f00361880d01c50030342c1050280b540714000080180d80c1f101d098440c1c010414181c4c2e2841d0000c4c20004040c407150303500b0005080c40c248014600400c4d10041505c10300c084203010701c89511180c0703816201095401c078030003100507d11886480d94206980d40410549544001c1c041e1001412000b04402e001c0f646020317420341503580e48041e4a501a0381c0f465964550751086d14100c0e0302d034180c0d003110290103030484649a0b212840100070b0280707036001ca0001996800c14003500e03215603a01c1e0000414903100b4180d2402070010045000801e58480c10720f100d41c0031300c900c2014014131403428089800d5202e0300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 747492014 1250 747490764 747490781
    0x415060f12060c0e030609070303030f1a091f0905040218060d0809030106151d0307060f030f140c040e010b120c0a121104030c08060903042d230103 65
    0x7244540211090342c2c80201500a0031085410006424250540e96034140005402210184020462940b41d440c0140c1550400a501d600312031402e0603402e09514800c0d42c2026004084404507001d648042070f400c2c544240340700711060025601400300350004250300c8039005034003c0b03e40000141c1d0040f401c0032000c5048076000e400c0256881c5541c006903161000d031003104801400030410030b4903003103100c00c3c81204009a90000d900d06181801d4480901c01ca620400c0040d0042e0480504240001d84242d070203000350003c05684500d03c141c100303065480300441c4080d4518180329400e01094202440d0054080c03400700316031140000070b0014414044030594612003c5099041c1c0d01e8150500b655041241c90b136092044204503548404000d100315040b8005080c203e81c0c80d5421070908804c1940d464221050550040007400b4140b0000401da0b0704407030190501c06401d0f4004014000015440d0000d4440745480c01c6010540c5810030140100030010120080c122114050045040d5081e00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 747493264 1250 747492014 747492029
    0x2031c0c110411040b130506070807060e0c090606071506060801030b090105150f0415090f0e010b030c0d0507030b09150f070f182102010206090f0303151302030415060f 74
    0x301300c1008044e040304080d00c03c4060043ca01240780384d5039030105866900c1040202d0311310740d00041040801c1124412046540740c0607000300820310101010544c03501c4044c0c0317182d20420000c2030135010000318440000e100d4032041001c1c4800c6603114009421040300303000c00c1344c00407626000225501c2c030520507948160380b104030034400d20500c44140191540b40008a98100762180503080105000c80b84100041c00741c0d1b0030000c0c000300700321314140894040d0044020140d040c428039001c01da50003d1a0f103181482105c1551009655181503403030200c01e80d100034523102240c070410006ca00d0109143c11019089004070105a603145010060201c04175150f0740411030505454900c244100303200600c842c100c5109000158480c1e540c210b150620408804440c502c404120707045503414009180c10400e5880140040c41c1c820740c0803a100c5c0401030403000100c80040d803100880ea00c030741103440100d562500440d5241001e04015405400828080b0142420301c400050940251402401291400c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 747494514 1250 747493264 747493267
    0x81506010c11010c02460e0103060506030114090105250507060f0f091415040c030605060f0628091503020309012d0f140106080402031c0c110411 64
    0x1031401504c4507107840a069030400050184424104404075144a8000501c41c0700d0184411416507074403498040039044050440050f41040f02207840c42d05036041d80c0e48410082000e82e50341d00802d004004001704803504141c1c103014050307201e0041d4012800b0301207011074840200c00302000170603082001c10348500001d84c10843e810115090364400c464845c0741610100f0344034111507110050b10000882500d60361010041601c402604005440c44818482c4041d800c40c602921041d141c0c20261001410458480380007580c0d036034039850182584000280a161280c0095980c60001c000313449901c480000c10a001d041070500441c2603400721943d10410074012900341d0400c50103500080c043c15050340d00d680b4000e110941d401404481c40510850015001d2007080080301951002408204035600d003400c0e40d21640341a000580c1901d216023040d0740325444520209242a8030400710007a601549000600c00c0e6034444640e500d01401441c4034005950060104002c0342c22420503910868070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 747495764 1250 747494514 747494543
    0x7110d0f12021608160f0b0a0f02070b04090e010b010305160309060908070b040b01060906020c0906030c0901181d0703060b010c051b04050a090c090f09050304081506010c 75
    0xc00c400040c524500610584030781000c0e80003401103480f41a089200035811030380032150301c0f10400c040000100741541e450314101d40b07040c1c0b11182c240b0500ca001410007222410400303201e0b0003000603e000b041021b070a180d882d83c2d505444001015901d1180656500f414503403100c6604c01e0003482d0003000406503c0c105609080c40540050082080071521640c4600d40080400d0501e8080c0000c00d005071980710b41c03440c007841d10b0038200005802c000184000080306001181e030000f00214600c80030744829000383c42d0a400a450101084a40b40e409060400007081c2504a412281514a0184024800c00303420000e13803100074017080d40709005644106000c002045007500301c0944003406042580040d00141c546a00f4168404007980c005000c9415040c0076040c1840f420342d200f0414281040b03107801d01d50310f4403c0a0840e120351400c2540f0b074540c8001200e126800052072035800350407a544c0795035a0f40070300c1d2078151508224010304000000200c1a50041c1668050f050f07201071005958032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 747497014 1250 747495764 747495773
    0x50f030907050a080114150a0e091524061e0313050715141305120d14070f12020c0315010510080903030c2206020a0c0b0c070909080706020f07110d0f 66
    0x55080c242c2c503038030010503100050000740200459000b00315050203040bd6040c2507514866585014160b070226411501001c00182c0400b091074042090460b00c4594a0021110b54003414a040416007050300d03002060000f071055074010f0b010390703521a80c1034400b0346075076803a984014002c00074420045a02020100150714404000340070414500810402c516200c03400700c0c00322002082c001d1601e6206075480b05505400c0782c143c55007081c0122a42d440c0c20f1155030340401c5120202001042c05c0301491a41642d00d000b4400000700d04405421207050301224280440c101400380f140502650700815184610361203801e019204480380780c010b40c41d50302e420006051990020360141d105808543c1c914102014481d2894020030480e4010000f0740c1c081d007400042d02815500120401104000c054507901700402c41c80103d0300f00e40d00025415019041c2042d10f4410864014003244c4000780c1c200c06841200040e040141c050008401466071034000e00918150042001d005e8071140f482400c00175 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 747498264 1250 747497014 747497041
    0xf0f09090c080a0812060a060516021809072103050403080309120403060b01030b030c0a260304030b0f070309050a06050c130f0503010f0209100f050f030907050a080114 74
    0x58410031030300907110b555030b01d00e508011819804888002002440f0504070007106603413900010102d032100c86c1a0700d0200090024850360001410326456200800107541d50b00388040c1c0c0f4000e46d150006200e2802d009807545400c400d0060b0301403400d001e800c9a081200500355081055490340312145050300355103414503503400c0103100045600c610481d66246a501102400c0250b20405020496442103400541528070b0a00700341d0182e40000700c1c00e04945d54170701071002150550714090805400508260141c184100301615051000080000401141c0d031242c078031502e80c0001845060300d032460100c042d01c011070030161155000c144403c0c0803515507400243c014401014051a00203101c20764055144a9404070681c0c1612403001c1020f82001c0c001c07118051211181180340c80f0801d400106c02c0f0038111ba04d0410002250f02e507142c0303140900212064680001061516481d080303034099620440740c060980100c044c80d81c001085101401003d88103820380764898401c0d9034609203a1180c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 747499514 1250 747498264 747498281
    0x13060c02090a200c1c031a0906030316050f01141308180d1a150d060b030c03060f191109040e030904020c0303010f140120150f100f0f09 60
    0x11600012650701107181c00e0005042013074419018081c05100080304400c000050001481850b05019440354500005145160540800c0700d0213041d5840768008207141d40241c800d5805441e0050f03000c0c006002c0c0014040b0302e017070741c6034000b4000e80c406020790080c400c2090b281410b90f4801056004d0000702010090309220903000143d5440c03c03900320005040050b04d078010780d0b42100341c41c80100311110106403240e1041c010340f58030441da10310340082003071406600c4000c4c2100e41c0d00e105107080e40c0e42c180450100c00800504940003400c180c810041c1c0d1450a1b90000140089148811180d9010b8011850f1440c04031241380d041c0500902404080c203445c0c40703c08034600040103c4180e954952000e0701c0f0700c03a4480025030f2a5030418040c1c41c0d000b00a038010640041c1c03800c0d081d101aa0307101a514040342010080002695480d81038117240111801021160b5581c28081001c5440d1b102c40340c62080d04030100450340d0a64418100d030580445020304500c010351100c00f030100000d540c000b240c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 747500764 1250 747499514 747499541
    0x140106090614092719020f0a0e0f04050414060106080402010806220c18050a030519080405040603080901030f2c0a0611130806010b07021e03060c13060c02090a 70
    0x2900c040c00107400b0030401c0c81c0c0408541070380c894010b106950503808401c00e44922005c404516244031026581998003070300810780100002030721205000e45a00c0c4030b0100380c44011b041400282030a18100043c1059411201901e20401c4000180d00303215002d40c9000e6a0103864140403900c541c01400a00c100c0d10700e0412403072402c9410b407940d021061040c1c00c0c49461a0f560a0030380000c00703900403010682c503401603104420b4001c0901c08180b012030217500c80e807214140d022030f80c0c03203e280c802414012039028940c01841c28000000b4415104001d1a1015090783d041108800052046080301c1d81140b9100600807040143d0030401350030f000100e80b4400820884646090503622241600c403401c4108203e64804038005a410656264400107400c0c0407018040c1c030340c1800c2c801c0005000e0803001900c01c007010303d02d0b1140741035201e18071030b400c542c0902603411501e4105400c854944c4143e800310700c40d40c40b5640004d0070034460544c545040d50b004040555070340303820700c01c1009065641007034031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 747502014 1250 747500764 747500779
    0xf030d0b1e0906090429070908071a031f08030d11120103060506031015060e06040303080c0304020d0609230f031b010e0a1217090a1203060801090614010609061409 72
    0x346c0f18180f0180101c0d4400315050020782e0381c5040312000300400358075442400c1391fa209283c28062954496440a201d03500c0400780c0d42c8030b580c2c044001801c090380d10154003510f40030342404984400c01000620841d400441d091240c1550074180300d419115480812600380710100c018000910581c00c026003004000382200c072030010140d0b080e002c8613130141c0c511008954035281000301541042e4003202201003211903500301b03442d6131406003c2540091015010035800000034085541d04503020b41a1a005002006548100e1612002d94110400720f00714000410403c3c03500d034880010456030501d09580918140315102c0e83c0c404060034140c803946041d548541585d07501040420030f40003142e0240a07aa0161901e4881c050300f0340e0140224400a0075024042120280300020105045940180c040303e5840007683e00718000e00c0c498010034025400d10314214148905504800c01c1c0348001c40d40d59031144d99a48050324812064401c1c3e0012841c8141030451514090707010b800380702d20140410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 747503264 1250 747502014 747502043
    0xe04050c01122003041104092a1a031b0c0c090c0c1f05100f0b1308030c0f0c060a080c1e04030807050c0103061a0c0f030d0b1e09060904 60
    0x3c040c010b05001d8030307510301c0c40080200000d110904544200c4400e0941302000440c1c02d40e104c0006165801000c0807541d001c04412010701d440c042c0c0048001c1030207190310b1054080790145403680d540b0949180c158403100032000e031000d9172003000326024082c400000b82003180b0b50318188240110020081c030704d003200c1808101fa2052080c400c000e01c0c002056a4003030340141c01c06940c42142c2e4058041c0c12080036110042c8850341e0901440c80c15a940e8065843c2c440130703d40c41c1a00a502c0c150060a03481c0004a106421120005010384072040b90307105036428612260140041400b481481100250b000c130045075041c041d1b6402403052a42241c503483d1005e0803c40e21264a9100b5401101d00120005962080c407400b4440d80340310003000d01e410300000c0c0ca440c000c1c071f00c0d426004600c54403038440000c513020100320030841016564a4241501d8481c01245078071001810506e02407070040700701d600e18034020300f2000700d000f40ca1100103140d100c090f00c41c01e050100d4131070000d00c1200c000070244142c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 747504514 1250 747503264 747503291
    0xd0921050a1809060e04120507081803010905010912090806240d06110a120504020112050c130e01090c09150c0305070203060f06040b030102090d0204181514010e04050c0112 76
    0x40c0d4001e48440800821030b030806d03140101a02102e04401000c0090610168000030b082a00700c401d649104c0340c02c0901d0921b0100000d005003e1403000400f03961912103004100041d0b841c82407021071070303511744940ca141d23105881520342c481202d00d56881100341a5110907a481809014101c0c1000f40400b05030708a136644d40e50447e40b80c01450214580d0216403854220307805500130090050a4070184030501b099030004e04031010390b61079040d40d903448400140700d01b031303007034080e1204002e001c0700108015a8600c0b114030020f1007030041c20906420080505445800780128404030341d0405048803070081517100440344080703d502d00b01c1c1000002c00c00c5d400583da04110407401611280c0d94003840b400d102042008481c0c4080844e8066401444000c02d140ea50003461440e0030307010789004c14424490071100900014240d4000c2c6540c0044442c00b2080d1216446030b00000e550703140c80e02050740c80d86203440003148111002011980030070509101c075403240344d000b400350324100004580e410140c1403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 747505764 1250 747504514 747504521
    0xd020427030801080c0f0d0b060103110406170606070b0708040c03060608061008070f0303050f09101d010206060d0201180b0301060c0501061a1b030409020d0921050a1809 75
    0x1007a800110844014400960b0030301c07480f02601d10031198400d1030f0302d8a04c045a62880c0625016150604c080b00280c0e0340e0f4003c0e000401071242e1b600049558540340c1001070400c0e001d090314285105280d100103011428944100c1700030942241543c3c1c80740c2d550080c00ca80b20040248101da03811428600000018541d004500c0508115000f030201894208101c0b50f0308100e50340032107000d9000c0902001001d29004c4942c0c25281c1603d821a5900070a282d0110144164240c0d5500700c051070f401542003591142c01580c42e194031646c01402e58044400485e41c4410589629500c9008129000010360103000b40036000c0e841c0080c2c4503c01c40d0381d1031240d01d0980090f07200b080030070100c0da803a10403c0401e01c9424003400504910201001850b891945035005122103000c034800034040900c101d29041042c0c43c0100564142236548014842d400405025801801c8614505660004504024003400c25000343c04994072241040d1185030102c035031159a071080d002640081030003281c1c8208500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 747507014 1250 747505764 747505841
    0x105090103382e0f06030b06090603070306030b0c04050604090c020f010905100c140f0a1205040606090f0507020a031b02090a200a020a0f021314060f06090d0204 71
    0x22252078400030b07003004003035415903016090b02c66040542000e0000e04045140c102c00e485d041e25001a2581911021401610070044155400040441000000c0794140c00517001c0e64031942004900e612082501e880794060340c024554013020900c41030001d0302503981301a9030105144104d800d150b148081c020b08543d904042520310360049020300741441c10078000c98038660410303c3c0c00807030480b485280c509035000d5594141036208001510340031491003025403805100b458078042041d4142440c040700100403c0c07040c59a101d06200c100e6402e419940700c5c2070300c110f0040d000341100890300d9408545100090801600c05d214001034000561035455165210300c98400c400100011038000c0c40781e50004448400c040c03d003041010100e9680e001c51001c411550000440c1c02005440c07001500c0e0044544a00c4809032030801c1101d25052040314941c098002503c0c0e400c0070f00100d00c24480c0c24840c110b031560b00000851942001414140d110070200240341c640d8080c0340e40011005c084202400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 747508264 1250 747507014 747507031
    0x51e03040609020f0d1a0405010912180506040e04020904050f0a06051f08072c0403021c2c060712080717060112020d0609110c0105010509010338 64
    0x42002c48114188031200d9500e111013120002e09641090341c4403115203048101c0000302a00000c041800c20070250403818643c0e91107034410311301d01c0281d20300401c042901c00082e5210303400c130400050607040c1081110300f502e10710614801181d85035001d001d8406406002220940f194081000c4454400c0c0302c1c0000341403181901181500341079291280b8440303440c1044800649030031007000aa440021540300325003100e040c110310031045010b041c0c004400307402000b0f8804c0060f4104420581d0218808040c404111569031805140190480c2e20020b4410503104200121812502440008591102c1820001c1540d03213040c907580d0b01c500d10008030b02080030106000205000f04981c011441482804a01c08a58500c0c0b0700340000034884500750442d2032101e6800214001c40140b9a001100a024841c03814008009030310b0446000750302004003200e0310b51070000045014640f50f05e04034102c82e000702d0740c00c0720401d0310f581c203800303110000f551034000143d141c00b9404104001c4150a100c2c0104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 747509514 1250 747508264 747508271
    0x603070503061006170702190c0e270c091506130905090f01020a0e04020d09050a21030204080a0303050603100920041e05131709030111120601051e030406 68
    0x10000b02418204691714503003201d4510104106c412940050800c10f040403042d03030321451000e142019004024039070850744a07100000e0400081b0400342c0c07a50045008842c5028101007404a509a00c401c44c502c41550320440301030108940c48854141c1c101d003081d00a21081c580f070014900004e0400146d032100416a88070340c2088000117081c031110b010750542070020740c540081e624008000180b000022842380740d01103035689840d10554003e007545903001044420502c02414002c004000c45540c1003c041c443e00c003051000e500c01d0007541e0884151100518558106075000c3e405008000c6c0104d8251046200c003560840f6180140300e580c6000b0804010111040591200001c0e0f400440d240228104000800703c0380011644c8035420189807000611a02d5610f0345070414100c98001408101c41e400303a019800079010024012820214001c125180318003654007114051814006101d104240024185500850081000034000a0241d61b4903020041007004d940080e58290740c802d98 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 747510764 1250 747509514 747509519
    0x2a1c050f18010f05030405060f0c040503060f040c050a0302030703060e011410090c030b1c02120a08090301050708060a03030e040207060606110c01111f15151e0806010806030705030610 81
    0x810211410b1440000c3c44e2a520b103181c19100e0f82d50361640a8203c0d503444000c003000616002d07001c030507100079050040507a9a03900700f03000c5c141120324040c0c400780d5910f840c5c0c110008107031400110060441e40d004d0701a088043c6951102e0b00185001001c002995484a942c494070303003481140d10f84900307004103c0e00c540ca07052140b40742c1203d50380e10b089024140343c010080d180d541c1d41c4802007c210550b1113034007110000c5d440480c0b0381c5072109980202610070748a800c0208590309003e800e0b4040150002c003c0783da03a1004c111100a002d90b8066081801c0b504248007182c40b1b1160454980c60140c0050314108542d5a0b6108440340f540c1b2980006502e2001003032185428840c1c000844000d19083c0340c40c800d14000c00e0f450b49186a0050500c1200104000c6281d0940d080110100070305002000da050b50f070008a05403c2d103140710303276000038201414002020840c800c07412001000341d407101d005548020047d07807803810160280e580340c841c5040c005000c1d581006010300c20942070004004c52407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 747512014 1250 747510764 747510767
    0x303120c1905130302040b01020109200f030a0305091e0315010806070305151210020417070617220b010305160603020c0307080322082a1c050f1801 65
    0x2250280c90808002c010826140c1d55007070f0030580d2060780e0b011a030018000e14101c1c0140e0050603100001001c450108510b8458440300c00c0d8607020001c0103558400e400ca20340000c06803100d4501e2002004194284100070b21400c080c412624080b14010f6004241d40d202800030b03243c8154880c1382031aa0340480300521050f4070038808141c120351b06080511541c100000c40f41100c2c82d19540c410300400c1081d8601403c44c10070030002d100808490411584c564680c5051100040741203015619031090a0002407403a2044800d206d481c1e00114518240b51240c08101000121200d501c0490407810180003001c200e820241c64001e500c203a0082c0f40c4502e0284002111612036071050741418410310040b0f0341408080201c07040c803580720300307140d03076a079140b91000121040300342d544ea07100f0340390168070800c0000c0d11004194000440140c0f40030301250720000351180c000410041c1c3c158000c258607030b1181824001c07d141092550070058200754418041290580001d9207812141b03458a10821155 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 747513264 1250 747512014 747512047
    0x1f0222090b040b030c0d03140904060909020307051009140f0907080103120e0a03080a0203070c03080403030e1f140c10090b0606030123010516051b0301051b090303120c 74
    0xf44055026002034010303100080c14120401c1c03005010700c881c82d403c0b03042e50207080086640c4040014400c00c1002d444000e010024020110124001d00c50041c0c0850903103042c040d0300300382030b2281d607a585100d410710300d04400141004012580160408a080fa8140d4a006a603486050140c1d501c0015600d50b040900c1e402007c001d81400388000703100c0d6030b01c19440d51600001913940040803690307174a10b1b08004030303d14407906e203003d0b082006241010040254040007001103a0080d03a84040184106003000b4000c040314070715103410102c0c803000e56034040c090308040d401d0855015019042013403480c4980e050010950880d885540e494600d4020030003480c2029400071416504181158104000d5044108032460400340000d9281c144040d9603210304122407440165026001096041d0300c5d065584581c41e03012a091601804001d034403d080512400d40302d030504080001c03110244041025640d0b008030405901030000308010010b502682e1007070f900510304850f002e03648440d400e41e0304001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 747514514 1250 747513264 747513281
    0xa0506090a02090103091524060f051803060c040314030f09040911060309012310050d05070308040e070329041116030221031509070519110c01021f0222090b04 70
    0x503030348c003403c240066a404800035211f0201400d00c0d44d6200451100c9411051030035400f50351511880042181c41c0703456a026104403485400310013541e56101a0190301c90083c0140d184003141c090044a80d10301c0d00707400404140c0d0191008117843c00a0b1004030349a0390085403401038a079102c00300c1520114400c10810115460b01d051190305007040344442d9125040751181031721600c0c02100c0902401014440701d4000c680c401c002c40e980b03540d01d5503038507041079003100c140740868980789011031540300b50340a850203000c3c1c0982c00303081e2500040c1008010000141842a82801801045074000e1003904075a181c9006e40c0080940e252041d5819200014070b180644c00c00105000b40129407081d03410300e000000c1e003110042d03c560344016040b140d034040e698040400600d0440400390143d0810070740d9020350402800d5074502c00c0c1c0d482c016a5501451211105200c507130fa0540d4849442a50240036000c013240218280010b400d400000c10010a4002000c0166a288005914580340c4544000e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 747515764 1250 747514514 747514571
    0x1306020c1c020f190b03070201060e090a0b070320270d0503070303020703050d0f15060f02150414060408040504060e070f120b03070303170a0506090a020901030915 72
    0x1001c0c080d5404550340740c50700101240548481c180c0c1d0625541440010390240119402c100d45a1130595002800b0345841d108551044031850081502c41101007145a1859007041985281d526001c408a00400040700c040402114500362002408015001441c809180b014010342e000c3c000f407202d50762010b000002a110306042520003000820100540350300c141c15090060b224040d60406850f03900c43c89842145107442e1900d599100025940100d4207020444215000310341c0b18081645c4108810100e01d004d40c2c03007504a1481000200d802582c0140319105e051301d8200c240c40210301d0004207540c100d560b180040340510507401e26101d410f0091518185052103800d20f00e0024008080002c01c41003001205294000302107802d411a6100400280c01c9412050b902c0c1401402c41101c3c00704009405120004164000480e0060340d0090b07900a0800c2155115a10810000d5000c00140c3c1c0c18140c4641d42c0401141c00e101e00c0d18054184c03d040461803400c2c0203040d030700d00a0720011148 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 747517014 1250 747515764 747515809
    0x1b011b1a07051c0b0105131e060302130e10030b160e0d080910180602030a080606040f05010503040303150f1701050c04050f040902040207060b090f09060f0c1306020c 73
    0x200304510103040c4040c003010140740040d510f000c40c00100c495108165030103c0e0708142c81d40008841d001e071030044648c4c0441e03c400340c0d00d003900c03020104c00341c1c41000045160a5a4001c00340070b140111002030703800c00040c040003000d46070341c2d646211892404484003040075201214038048550003010204031200308454091100b459991450b22501851a0b868025000a094a03003c83d00446494421001c42000c98142d05d5035200001e5491744400303403810001d881c5401140d60303801d1840c207903070135900d000d20311403401c60428004481c15000100190700b0140c80b056540300c04400c5118030009441c0c010810145c00d414109406100140c0710104840340c0c0c50481000440e410070f40949003070361001c603141400300745d0a50008019100c8120080c0d40302d80300040d81020445282d20202680c0300c2560004000d5680c1d10304400c002c60200e8100b1520b0300100300140415410b80b0069a101c0c43c42c0c1000b82c100305e800b50b0601040c0489403c2480580d01801c80100c042c9010561101c00e640c066040c03e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 747518264 1250 747517014 747517027
    0x31e0318060c23120307020c0103150905340915080a0b0a031b09051003030e10050415110631032a020a0506030402031b011b1a0705 58
    0x40180921401c00f5091080301d205041c611181841c003101001254811542026919444010103500c00d0310b4420152040030849009035000c0d01904902e41e0900c40c0d2081014030303044441c00540402440307180d2413254007002c60501904a0700440d03507041c800d52002540050f1040150040c07581d908040c04c5014101128913a090303100145991150000303001107140301500001c01c005020a4100410b01c1d80c158501e1410036084591000865440d0715091000b1303215140a202101c18074000a00050100d078071903403490a041400d48803022043c64194034150b038030505040f00c50400c0c80c800001640114070047d50b5027007009202d410401c1036108841801c48041e6044105503800e0f01e80d004040c80c22981002d25015802d41d041d200d002d0f020280702c0d58070400480d0f000e8a12000101e11801c140b010205441c01c11405483c415503000d00240b003424070356840c11642680100c20b150400c403010075002a0170600e801c0100300342e849108009110b1540300c8100324200c0c002800b04040010502c600c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 747519514 1250 747518264 747518267
    0xa09090809040e1006060203030a0c090302010c0f1a0a09150615121d030309070e06010e2404140f04050c04031b1a040608070e011e09031e031806 64
    0x8880707000384202c800103964110400303024106035825514494441c80c003200040c456030040029032040700090010001e25035580d030252180c865034000640018402410000080c900f04400c0107054003846484010750b900c01d10140e6005411610f070800f0b5502c4001060401c00204c40704005105107400921070142880d0326601610300b4048400204807c0801c14421440e0a1307111401e101d15240945000421130704080b940e0303900580b00903145110b102d40000d41c55040c0860785000c4e08050707466000c000100b108100400d0407500344151000c441408031241000200010b00c014844941c442a240c41c9000c1048850204901041d010394100740c100184040720904860036640c0c009844050690807525031001c1d2144c03034000c004040410034022803000304540250044a001d0b5485107016940d001c422a4510404c1c0001404240405020f40d86008400c1c940205400b0f1807401c0101280c0d2a1283e54030144400380300d4560740748401e0850185580308014051046900750403030300d403a03e030900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 747520764 1250 747519514 747519517
    0xe1b03030a030c1110061514030c030603031903050a14040b040204090f0b25020d0e0f03010b0d06020d0c0507050a0b0a1b090f0909080d0507021603050c0a090908 71
    0x169000c2690b9000e2150072580141880c501c02c10715642210240f5180c200b0f2207001b0403807401448503030070305407111200180c0b00703a048a50f1011f04980d007a0840c0c4079102c7d4642280c05c0641090b40c940802d104003035644510001038500c521140e540032850b414034581e0001194079450445854920103010040840c3e44641d0440d00b2507816036002904c8040350522814884280c41d0041088001001340441c20b03041c8100098150780b41040705109030701805050ba5100074a450100120304440c25031803091810300100030220a0280021480300c44400c0012440c8070010b000310307601d81c0d02090010181086129a4400d00c0560500c50b20782140354035a240d4810700b81070010844600340b40020000100d58104c0f0b20a107510306c40704001c0314075168010f040e045050040b03460400f06054000b42580342401401803050300010081c0c50300b543e10b50164041c2c44000d100c1010b41c481c01c5c480e1100020b00201e202d00440c05800a81844040e03a42044800003850b40300d00d040d0b500300300c9400701240c080b40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 747522014 1250 747520764 747520777
    0x3142a0105070b100f06021b0d0201020a0b0406060f080105190605090c1309060b03090c0f0d1b1a0d0e060106090504021812070f1205060f07050c100e1b0303 69
    0x80b0320359680f400901c8400110a4001103d4905c111900140d4590000360145810308918000340700f05907103200b0b1050885105001900680c004096076010421900daa150000d02903907021038480d0b2a000c03004a80d1290b5885035855030341d40d9040020240b02031104409044806000388440c071300c0e250009841c08000f07130182c901480c0001d5142032502203103003010001e05a0f03460510446944131800091504115882c0c1c0150060348500c80c0746242040101900310001820000c407022a031701e03500d40110304003040b01c1507075410460100c0c68080c0d60184103001d00940100640d24021000310381c00f80c840404050846611400041c0007854200d4141c03429220b06a03030068441c03080000441205c2c140390400c03500202c450050004d0840081074040c20b44d40440d1a500e03440d0b0350b1b000c401c500041c0b2410050590340045000c1040914005409038000520746081418100d084110300c0c00c0091510300800d081d50340740c15000c440203003403050525414203030380d02450049008004c87c0d180d01c5010b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 747523264 1250 747522014 747522023
    0x51311041a01082d19090506070e0a0302151b030c07030201030b030c04090c1707240c050d090e15010e04230901020721050d09020a03142a010507 64
    0x4400588904203000c8807808a000c00c91002090448154441d0b441d50b0064407010421981d0b810100f040c10951b01660300f0156112000306207d030360308007044920594440e01141c0c0103a8140c80000035035907100c140c00110345a8801250344205c4800541002c1ca41848140110703001440407031040e4001089075400c890702030134041801303001100000d0500003506078240d4070514288459041c03000c03101540040c0c900c6003440110800620f61215501c030035a11030344441d40c4030001226403c6e13210540200300f2080ba81400c54080a503559080e0420070805c880e403000814003c401c02c81d040d0300f140c0c940c3c0c00050420595100c04010f0780020142074042c60a10f008070744800001e00702400310100324512441c0c545602c8418180718416902035805403006582001034014610b01c480d61720841800201c66503150710b03190400907001400035058107002680c3c813140398400000421150801044090300e084090030f49103440700600009065001c1c02c46103051075080d03800141e030340c101302101d00e1103820 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 747524514 1250 747523264 747523277
    0xa050711070612060e190f02160f0204021b0d020705041b08180a060603020312120a09050102160f06050f0606071403090a0e09062a1c051311041a01 65
    0x1020b00c2d40094031051748449854031500e800c2201c1c0e0741c2c524580d11086041c00310140a90000d00001505900400092808100b03001072440000b40c080d91052803030500c003500240c00c002c8854505036510b103a80e41035240c00d8000a044c000da5a5040c0300140160504681c01c002c0e407440305d03070084401d17458041440140030010000c9010440e446000d0a0100740f80001c4858040c140e20341080508110702c4102e000c0e01c1b50311030320010f0a00c00c00640d003110302880c0043c40365a9460005030044c1c44290f02c01c1e62036541c00c104c0309440080480b4007180e580c0c0a03000f9011408940d00d41303a0102d420081c016a903018552081c0002c035a65041185c0605800807030003240f4400a0540724194810050300503441006140c1c0041c000c00c00030f250611502c0e03180c00342c5545540c0c011050307584c8200125005200743c91a500f0327082d07030320891018208440c2c64021180003181c4c01b0340300300221030b01a202004001c0740400180c00300005100062044642924184094040200c1100000d001d1a0700507050011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 747525764 1250 747524514 747524537
    0x50a150506160210021f0606081303030b03030307033c021b1608070b040305070b0a030b04060806090d02010e03090120061608090a02090103060c0306030b0a02030a0507110706 77
    0x342c15a05400d8000380009180800d110010b55143c0d40000b0304c016501c4140403a9030000d03401e00c51481100e1303c6440c1e09905079107240d40000e55080d094011820726a4450003e001e980707040014502c2500c607501c00045403e40001d500d510460986046a40300748444180480704001321001a4601812400540c0fa02041903070300840c00003c0c948a5030600c40c4075034500070700c40c441d101e001c216034080041e250b0f0103454001c0040075116600002e0008d9110300380421400b84404000c0104200340c2c900014001c03845000070341540c21941c011034050f0300400900c400c103441031002c6005c40259000030010340341140d40050700c2c0d0048078100c905003e50602020340401c0d62144a40840030644262030842ca0064500e554107001840f1101c00030b14158000b0b0f2100200081c134100c2c0e03a800600f03500e800d82c607594407c00641002c01220003015115880000000c02500300e0318040d014446002d80c80f442e02494802c11070310000c2410041190801122041c00d00c082002800c0d00d6452078049041d15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 747527014 1250 747525764 747525787
    0xe09130b0603030f0d091b06050a0f1b060c030c02010c1202030411030f030d0507050307051b120c1b060f0304110d14010b0307060807050405090603070e04030c06050a150506 76
    0x1401200400c9408000780c1110440c10784d81c04105224032544602201f0300291300d4465108605000b81b50124004011a000c80f6000c2c1c5e940011100302c1d842d040e01c2c00a6410403c00200046640c104c80443d01d42d0f4894011680600405000398130300d01c0200025401440d008143c450b0445402c1c00c0f0f50f41c0080031400707012540d171020b04d201d80054203c42c015a000010665241d102002c4800103500d042c007c1012948550704a03405010641d9076a421300d455007401d000c3e0400000c40032031440c461803507070400440400b4041c000c840744c90f4003d000c90207048210a000c064207850828420300040000440744150b070b4040e00e0b002504000e030312000104000100d42d0081c182c200182858040014030811400305403c9007440303c10550955440c1d960710001a40d8000003a6407200201c0d0007400140114148010390544c81207004044510840c3d03a080701d00b1240e881520140d0004040405543c20301c4894001c50f0b4110456110030001541c041440c40c001c11440e010380da114480000e02801e014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 747528264 1250 747527014 747527017
    0x50720030607050415020601181d0f0a06050a0e0d110316150e0d080a0905070512070501080106020a0f020409260307021515061c1b0e09130b060303 65
    0x220009011260350b802c0544016006030014401c040081e45840f218144003440490031604880901d1000ca03800030448d41c040000c0e08d5481501c1d4040408105041c9400310700b04072480702a417210000e090405200d0900c4803e845004145008607810300f400692580000a50007051106030f107030898400241c800c2150941c0320b2440301515146840b0820002e00801e040e0b074102245609a040181264250103113846074030142003000816980400100d07140d40982222585500c201c0c01e440c2043d40b40c0001850304820611002c41275400300c03074140540d5070003071003550140140d4001024585084d640c5c61544020001d0024021070b210382c2d041082009510700721400b84c5903513600901443d0b0480f16455541c000306ea000e0010700c180c0d5410091000c02e090085e01079040592100c90f800744500a01c00164030008413250081c0354094092a01c82e824801c981c1e241428208a6000c008002c10087c2500c42c1115490301c2222141c080c0418881583d04d107001441c0d01040c00301d03840d9110740c0000d045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 747529514 1250 747528264 747528323
    0x1b0109020310050709090c03021306031503081e0705250b03010b0a20010903121e050718140a090c02250f0e010f170d030504020303071a1e070507 64
    0x1110f01f004560b115184e01900a40600e900648200780015556a400ca00740c642c00d110300200141c4ca50801e1011801c1030004045c41c2d400f001400c92505022000001140e00040c4180c880da0048168501900386070b00e803482000320340c640a40c1c41d050505034a050a44410300c00c00c4103241c00001d000705007500540c142c03000c1c3c08a8802030a407071144090600d003c1c18400a007103000850001c8001000e01c0305c0c3c4209014042605e103506440e12282140c0d6004080291401040c0801003031040b40910b2034004003405068140c07044a6454081c105000c04c5041640101828504128400d613109038009004c0c0341d29081d2607a500301087c1765071490303c425145600031034280041a00041008030310016880d049a1710b014401071026030702e1031305254004c14100d025001d40c1028401c2c800c034512a0f00326079000340c0001d06580c5030100c00d565052104245c12142c4031603841c0b25007008440d0000800c4840840c551014103055803400c03440c01000d0744a0b01200501b1061101c0b002c6040c2c2aa42c800d0b5540f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 747530764 1250 747529514 747529529
    0x203180a05091602010b4002160309080c06180d02150414060f040e041a040303050601020d0c0201081305071e03050d09060801030b19111b0109020310050709 69
    0x2402d00340010b041d140030711a00b034444055030030001c400e034003414081c0c00c80320300a1203e1a09040d181004108420104110b005241d40c500c0465031f400d0411907078401054285070144074909a1780c014503000d45442e10f16400216550031091015815850b10401c44043c0802c100e5010f40908114000804050403140e02071f4100031526003850381221703100300410036520002500048001c64104003c00ba02c60000e85010460041c00104a0900c82800854101e40726041003005904118400014480100c82c02d0b40040d031150180300455806200a8030941e0861030140b08002168001070314902004e000e1a0492440c1e0b800401403202c140140000783c44140c4c80c00c0304c030044003000e800f000403550009484500440b44000761060140c031240044414989407440160f20f581c46981e1a000c0040c4042e9402d1085088610748050b54442c0c2410394480c030920940750002d04252100041d000c0d00c0c0b0700c0050707151a0103000541d0700000d102c500c04c040d501001c10555500c0c80101c0707040c1041d500004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 747532014 1250 747530764 747530779
    0xf06160804060306240e01120f02120105040207020328150e060106050c06070f09030203030a2712080a05210723271005040f06020a030203180a05 64
    0x810450490024001c40d41c1543c0d00340502c03902c1e01d4020407142d442d104245400d8801c011155029030107070100301c940d1041410560000700c6240310920603150714500d07a420b03060b40024003113481000d013400103026110079502141003030710303070740c08a070b030310031440000a55000040d814841c0d03076500c4800c0b08880300d60151440011403600246480904403200841751070b03000f0301c4008201188502c0079907032030b8102c1c031004104c80d48802d03105450031b5045007000d40400c550542c0100242c4c070200700400404e1b549980d144214880c0f8001c6840c3c01002d0502c07010030b4107d101003040352038403c441c1c40c0c2420360030400c500c1d40c40c8070000c1c0503545071083c4000030401c0350f4032261046030001e0741e0b842144109026100d8942d80c0810340b90710641d58000b240400800c7c0010b00c02d05d00d50b0400101081082036414000d15428002c510003d0342c41d22200c1120000680c00040600144506409501c010304041c0022300c100f2509903000794580c0551250040307400c004040314065076840e0041c4800038103000e000103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 747533264 1250 747532014 747532057
    0x170405100e03071205033a0903051306050d0b12030405010e0f03010e03030910050402010804030c0f15151401080f1003061d2505150405280b040506090f06 68
    0x10303100e800070903201801c03c0e408581e80391f1019030b484410311002c203c109400d030900c44900e030300001056000e8094080000070300c80040540c600b00c80d4103000e412582c032860b8071010f40c401c0b00010740e1100c00141d401a2020184100d0210b0004240d8007520000d00342540007611420119a0300d500396085c142d810742c02c0007c000822100800194003c00c140c0059410440b030648040c01030710b0301650004c3c0040c2030342001401282c03181c680918030601c1071031030b4000d50728240c81f24004280b8010300b2442490780c50303100310303d0008030b075100c0001414040c8259641030840d000207004440020500350207003c50740c0006545005840f2841c003e582e002d201004241042c1d411714000c198010b600c2030b00d038881c0790300c0311005240034100d460419540d0103038a2080341c208814400e036520801d40d10144c5600502020503e9600d40b1022812586903081205000e082864000740c4801e242e8024890781004102c140940c1d25940101c4000b040190740441c07000031098081000c81c071816120b0560880703c2d0024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 747534514 1250 747533264 747533273
    0x30b150304050d08011d0403020c09040b070906080910020702010c0807081e090901060e04291503010807120f02030a0b1b0c060a0f110301030b04170405100e030712 72
    0x40c50080d801079040711451401d140054410007000c0c0110003114000021a82503032854804241e4031500c43e1050345c051005590201f8000c5600355400c0b01c0000701d520800036000d03030100c001070044c100c52a010400c0d05003401a01d031620f91580520100300e400150f02c00544e400380c08803a1449038010043d070780e201c409040c0f44105411082281341d100d41e048045408040a203c192112107c00425a03100c2c0c1c0d05c0c000d8295007581014010603005500c0d089060000034030505500002b651420780d01c03804041c40f00c1040040c00944c01403805991042c801488074070000607555044d41c0080c240002d0502407402d000381e211200707040080d498861444a641040858205180258083d001e40b00c1d0140e00d240182c2918055001400201c1d0b00490004140388610780004500041d40400020030100d180003031203650b4402d800075104084500140001c09c544a002c01c0c40a4403150541c60405080c440024102c201c03065800040141c030440c00d00441d501802000000c28480201d0f052031303400d6103030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 747535764 1250 747534514 747534517
    0x50904080f19030506060715050a06080f2425090f08010c0f0e13180b0405160807240e1011060a020307140a051204150534030b15 57
    0x8142d0000b0b030909010544904012064400b4603500ca0211000512180c600ca0000e1100030303c400e0840d42c440000040410082c800e15000074082e1001e0201402c8484c2044800140740c003070351b00e42409030700810003058080018a40a91130f00d07460040c0c00c0100c100200c0385401280c0144050035441e400001e05401d055002c501400ca0b5030300c41e10001d001c0300c1001d030395080d03d0021481d0004449032100105498036031008020041300d0700d504d5602031442d00c80c102d0104c3e003160115078076800f400c05980304c10603002d5101c006002050040034094104001d030415074040000d840309040340c11002003191400b480c8080d8074154060902d041c0500040750080035035000e00400304160166102003400380c00d07180201c030710402c180e455410181c5003c610028040e40420854400c01c1000e00850b49040d03400001c45000f02e00441c803000f100424840c24804451024041407800c69070401004280d40e180c40c1d003c100546180004601d49405a10a40241040b90a180d41c001450b6810b980000c90140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 747537014 1250 747535764 747535807
    0x14010b10030c20070902160c03060207140109020105160809152a0601140a030510050f01060804020d030f0e06070506041406092e02031911070c050904080f 68
    0x1660451043e04440f02082c01c00204040d950f01c5801a02050102e043c070b40e0000c1600d5140da4081840034001034032038403440113980d00100c1e141500000c80c482400120b22004400e2150a40208117840c001d40c00604140f10b1442c1c4001c007181100d101d10280016001030b5050084082c0c4480c00d400c0005403943d94650040c01c848182c901844410201c0090440004074040701d20f100030b0020b80d08051031920949650381c0a95440203039404080300058040c031910711085050744010516092403004151040ac4c1600319000b000a02d8080001698070460307003840c0c460709801c0203615200d90040403241840c109006540228002034030740100000040e4484c0b00d50b0050342e2202030801c1311101c59032208425500c0c03100a901152501c005000e846105c06602c4000000300c5014800200303200060742c00c00c454003002c010011107095406280b9015110084402600391031420b461035845905091050203124013078400940041c0030024008225214008141c2d407154503013600020070742403040c400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 747538264 1250 747537014 747537017
    0x60a0c031109011d0a150305370e10020a0210051602101a0d1101020f0313090905012003010f080d2705120304080606060c0a14010b10030c 61
    0x400c50703104640c1d024050303596024050b561941c1c44041c0e901c5920308080c0300e0707200070380c45101d116000983c0140c20f20070301015900c07071f1404901d916141841068480c1c940700c81d5035610f80320ba40400e1031002d00113038400c1421000d060018410445030000741c80c00d500c120304a002980300203020b0340007540024003c040c0c05144003040c4140da6a9040c078001d1068099201d0000d030344812089503100c8441d411128031500d408402e240c0650390b510000344403407082d4000b598848205030310703510b480d64140890100d002e01900103614003d0041541c50804a5601c11840c01c0c40d0388180100c108007083d04444854400e48108052540c410071601107154420f00c03072880814560789000031407480229801c11409415140e80405012080e0407250340455412080810301643c10b010885944001c001060100d0000c000e40e01d60741410715891601c40c025100c10b00c0b0700030a00480d0f80e0203d000a44511003940045441c0a06d8030f00c2450601402850b414644e01c10101600511560383c154803501c5100040d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 747539514 1250 747538264 747538271
    0x90a0b040f0207050705060d0902180118110a0e010e040f0510062c0d020901170708070308071412030406051b03040506041b0b0409060824070309060e060a0c03 70
    0x3600324404a100c0d00030002c0c0260085c10080140e45820070185c00440069003010803400d50b00c0c1d0018807020f0403000d8810305610071700c0040c000ca521040d440b0b68520901c0004008000a0a0705000c0e68041e403103595007048a00c040715032060b4400c0501030400c0c8030103001482a80391a444443c043c010444801130004003490001440f20f10070080d8034464441651801f40e9807690700c080007491850040c280b81c010481c24000d20043e220b583e1210700900000120043c251314222446e808c003030251340503126903401042c060000c212048102c0300b807036601441134003c5515410905040890110782c04501000c007000300414010705130000c071300c10066005640c001481c01140134a66010945003d000c651051340003d0000b000501880c90800d01a210070506a13035917103204100340c1c099013062000c161580020803002c02c0800000c841c0c0c000c102140c0007144901f074600880d540005249404142e210001700e0188020359018884210414040c1c508501e0008100009410168240c1c40001d00c4d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 747540764 1250 747539514 747539531
    0x3072601052e05030406090b090c010e030a0203030f0307020f0d02010207110a03230f0d05070c0506090d03030b04091205130b0306030c0111010f0c02160603020f041e05090a0b04 78
    0x103284442c000b1001c0c52600e6800c240b00940120b806420090045803442d40d146403a0b0085110741d02924852245a0020a2003891480004180740c140050050003a800403165400503903020064a21104203003100686a80c0c0305032040b0b1130017220711a80005402203030001070031254113400402940f03000d9012144401c1400c014401d0031113003888042c0044080d680300c003000007107a8881c0c00004401c1011a0350124903a046181016040e00c1c201c8041000010400100104150b03060010314003103441904012140b40030840714a080035004040503580d00d4002120741d0345502140440e60400003041e0b1000c4940707006419540700807180c3c00c00403403101000550624600449100c1c000180c058411010440015901042c04c54102c240554954034003000d10700e41c3e4828506030680303d82c001c042c41e03035000c100582080400c2d00002c0406004000401020030780320b080b50102c503074444001410680e03080c2c2d00d80101010390003140d03010803a102400403044564111200c9502d08540800c502403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 747542014 1250 747540764 747540799
    0x9130c0207030b0c09011b0c0e0726060f10020f0d09060809010c020705010f0224061c03021c0e0a03030305060f03011802010c080d02042303011505060307260105 71
    0x5603103091070000301c495001c40c100901c40b01d00d644030107100301818821661030384480061a0811501040001da00c608042f0b8010310021000140400a402c03460240c1031010109082c00c4500214034041c3d8803000c84032038094400c00002c0c16200c080e009030386001704200c1005050303100324031500001951880104000c68810312607156088910303002015514078140c01920454806070309a8254050396884205044d156007100ca0b110610b4810394140d881c0041c2003080d0a55201800d10340c5140810142000035000250b10140c0d03110840604a45000c0b0001220121100c1c10a2a048100c01400000b0190182c001c240280c00c2100d8102d18500700c0024542210801c640030640c4407100f440c110003550180d04d4450030a4001c200c11740c0703400284103008099a102d87d00001006660440c0f025000600010258020304110000c0c407410400c1038096050280a01a480c400c11000011a180c1d9018810340095424003000254200f210740d044030504140900c80e20340039100511043d0100c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 747543264 1250 747542014 747542017
    0x9010c031406031507030b0901080a14030315150c0a050f06090f100b0a051c02090f0105030607030b130f1d03040f1401020c04180212030301080c010509130c0207030b0c 74
    0x30980500104201242c21132106040c00010784001c0c2450ba9400640321a03445568040c0d0181070018001e10000c103242c503003d80003c1070001940415001070040c0032000078582400b2442c1030007180c01c4440e0f1280320035031f000284170b050700c3d05025200394051001040008540e00710b6201140c1c0c142c9503d561684240b90700d43c0603103013140301250400941144800c0c110790212040380d80c0640200e9240380c945000c00d42c2c0c0030703511011480c0d140c8074254280461a1a4903040c2e484032502000c1e20240d4034100120b0390b5200044c01d2401411344900500780303c3d8446101751840300b01815018451000120a50001004070460000d88000c0e0b46141001c1c030a00042114101c41c4405150b0301014030301886180004203840da0241140141f0b802c0b4007031566180200d5114411581101e20f40380001d10410400c0d91140d404920150000e100402c00501d000c0340028030300000b800c3c0781d0390b9080707114009104240c2000401d4035807031901c1900004168001640001d4034030440480b00b1701d803036521010885 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 747544514 1250 747543264 747543271
    0x30f02100f0f0503090c030a1505090102040f1202040f0f1a063c0415020616090909020d0b0703090215040503070302060a1806031b031a01080907090509010c0314 71
    0x10481c4540382c4440c81d4841e4008552003448402036580c00c00084000a0400c2a1340304c1c10360b5041c000119800380650544a003981102c00345000714541403030300c445140328038920b114035502603c82c0078240c415500d4540140d2440300074150100860f24101e44000c005200d00d400781c1c0c02d07042005032008068148442180d035030f83d41ca0001100d0a22042c0052071003007200005016654042c4c028810749400792102400242501c00b18040d40b203020800003c0c030303008004090400c80111a01413201c0345070083c0740301050b901d101401003921109400455004400408000d09401c0540b00704035845a150303119500c12842190ba42042c00b062082d60303c114000c5000c1c41d07a040c0c01c0140100014070700403004240104003400c101e4120440382c0c0c0c0707003c15860181e000c0b101103910b6400084c201e48011000c00b0300c940c0181810030a10481e86011041074400c0c041c040e051040c0c003808120100b00400c5288000c10b0011014401d070b1900e000d0940c0a010030151b042c01083c2409502010ec00d84011a03911 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 747545764 1250 747544514 747544517
    0x60503030306060414030a0f03030c08090d080403050a020a0503070c05090f22111c05070801021c0b030f030a090626130201112508190314090604030f02100f 69
    0x6041c200000410b0420025076006c1e81403190451480021f40039501e01000705000791400075400c4051000a0001c4000414030101604100c070b00c2000d403904101556003190301440c2103900c4a1101e00c050703140c1150040081e10601c000f260420030008030703c44a03c282c4800f9100c00c0061385400712903030020301c01680c1441a15400c964140b07100c0098056641110b40240c00160200719084003103140d99052103040106001000041014864100a6a001000583c00862610344408614591a070852003030f04c2c2000c2e15a059001c079a07a0411000741c48400b410203070b990707414a80700e0250070490781d84203030804154040c090800a00705c10300d600f0402503440840e0807d0351386413080006040c0d28034000f00c0c1805002c010b1150300101c104494002c00d00400308003e00342c008c1070040c20003c2c046900070303810380c0e00004030a98462414101d219150780d150404101081803404204401e01801826507001840424004144280703110135056075402521003403103c20700c1c07400c00c403003440080070b8900 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 747547014 1250 747545764 747545767
    0x1f06090f0c1704060f05150a0b0307020309190801060e090d0504030c05092505040608060a060f050a0306031e02040b040c08011206110a020a12030e060105210f07080106050303030606 80
    0x100c07509002e201d0350b80b140c45644001005120307092030004a403403d030703051245014130141140da0703414004031071009401d403608070606620780502c00a40da0f104925a8a000d03060310582e1052206041001c28081c000000003030000b251500840c0c1450f00c022140d014071441460390045019004400300c80a40b60030408035007299003444240a00b03542d01a01c10b500180741c201c40326100d450071200911341c00c000c3c2d0303454507a5070b0316000c4020300d82d10380a400c50b07120b01c64806c1d0400040707030000c00e0a18404018240140c0310ba025010560082007240c2c0003031f00c01c1107501c19880c00d030788100c1c0ca4075243c94801c40303007042820312420030300c400c807042d04041c0404903010b6001070200e10607504522070050300c51400858640240003010040b9081030b012007000d6031091070345502300102d020b00d445c1303240c8807071030200011a04c00d00f02c0ea59400062044602451849000c7c424071484421408610f903003150403146151064641207030344c1c042a21813503d483d481c06102084601c0c012040301d018950060200b03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 747548264 1250 747547014 747547037
    0x10914010c0809030313080c030705090906040212030715060e071701091a06040f0603110c03040504020f04080a050607110111030408090d02030d080f0109060e1501021f06090f0c 78
    0x39035180c0d0083c810103525200500c28a1280510410b03900054140c0c50040c1c00e10030000401d042ca03105540d080305206049080800c00c2120340001c07600d0344141c0465002240341620740c0303580d0a510030b092000c1d0184840c0c003080d40f060703000d94001d1000c69028400107090303556145400c0740e0034a44c0031001c8030061480030042200040741d400000000700307885000d25443c0c442400261240e442607001c011541c844100c1082030079014429400c001540c840010b03e024001080039031284100c0c099135102d1039001c40d2000d01e00d003e92003940c0151505c5002c4407881d80396810425507496089074034030b00294111115450074801800707000301c0b04840b46038843c21921aa07032404c0c210340100407c103802c440011185005a9020400d0f008641c03129103685503c2d0034840d800320b011140582140b610a401c1c09001c00481c0d0405020f540d02c10040102d080c03080c2d1191707004034180001188402c0409501c138501d8035282c4125423080c3d00f103072080315003000502108043c100507951005050408161492000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 747549514 1250 747548264 747548273
    0x902040e011d04110112020a08180c06030103170d09030e03010e0106061d1807080403120908070305030a09080414090f0618070210020d02090405070c0b1602190302060402010914010c 80
    0x81c051135050501c2a090026042218120303004960700500048613042400200007401e46400c3d25142c1d20409020360540080225000e8401880010800032004041b003034122160070a41d008441c180a040c081c150075400c1c010f04104480c25110700c02d521300340d000d0301002d20503c500400c80c0c1c1c080c0c0b5428039035a181c20345100d4080044074115004070581e841c0201c10000002183d2140b0426120341c0300900300b0307080050181c00b9a40d10318444501c1e008003a00460308880541d800980d144c50919560354505100a004c3c111984000f0a90580070402140019190300c443d00444029a29100d00c1d50380d519400d10b8203001904d801d40c0083c00c1c405403070790000c4040002644000940112440f66111031005401c0f0703404072802404071940070641c200e252816001d0181c1011312441c1070001035003191104114544040c00a40c0744100d03140e08105450b00a00c4500000b100001ca4000c440100341000707500d030344049404a00107074100b4000f0500071949645020400d0040c2e40c1d940f00c0e11200d549 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 747550764 1250 747549514 747549533
    0x40515090c13020904141e0403050417010e010f022d04120206120702060a0c031b050c010b0d08090a0f0b0d0507200d0e0607080d090314040902040e011d04 68
    0x440031455004c010083c0a80c8540c018590881c042080e80c20751481c080c0190720300a940e0245400841030301c2018080425403290030f6406032085802e60b495800320309800f0600510050b00d14035205d5007400501d0300101503a50142c040ca41403809074040030f07000800d2911328504c0d040d14507006040c0c10f0006200c410710001e44c814200d440641aa450039404903500c10310210f0442d000e40050388000304100301188580615203c110b000e007400c0c0300f0700c1460001030144011310844041000310104007031070743c0b410940100800b010040e204086100160824802d5030b4044402d10303015180161000540d1000304030500e048400b500001070600030070559010180601034001c2c001c10100e1400b44140304040d10702c0d0300e64401c01c0c0004047e03080a101c4090040c08004995505c07540080c8826400304e80180b00b190b0700484854400034154000b40350558a034210f4212000e0100310100c3d010031034041d80c0c1d0051040d40c9200c0c1c03070540c2513030342d441400e1404c0e403102010030085040c0c01c1c0842c00040c0142d4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 747552014 1250 747550764 747550789
    0xa090909020d3318030c0204230a060e0115030203090a02100815040501050a0315020d02160308090703020d06051315271a0907030c06030203040515090c 67
    0x42000c01258050f8950810040d20180704100508802c080150010400f407003294221000c1d400c1804402520000725000215009014052201c0d6000620031552254407540304058041228800d0240056014820780c0c0101c441101c100c0c40e00401003180388031400359a0480b40301042c0000a034100703542c124080d41014003810410700c14101c00000590311040070309010109541c0d02c2c0a2464864031480c41e0507525480340e07004a113010014811603d4445594050301e410511032201e10707810804500003886030415108a16102140740b43c0020390360758001441ca4000d940780d02182e1184500c00c0e484079010310000f940400301e143c00768000b03032040e00069401400c050f20101e20a4240d210940701c080e81001e002d40080d035548105040c010220300140d00701b900800d06107400802907035030b07c68050900c4001140403041c500042d50456042220002031503001112003c1595105000340103900280c80441d03050140941c808540d00200e04124401c22b44140209401c00441080c4104005400d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 747553264 1250 747552014 747552019
    0x2703070503041a1e03040b06090f13080d05070903030206070810051e0405070908010e1903050306030a140607110f0c15070b010b0a030507020604080d0b061623030a09090902 76
    0xa101ca105448000380054139407104102c030f900d507070380707845d19028807009001018907215000303182c00d00800d1108814016400004404901000003650420040340d010340f581100100e41002c04210070b0b0b0368064124811640700341c00700c40307841d101d620341501d0020b4101c81c01c000c010642c0b07108200ca440c145602280650040040c030044c4000403000c40c3c01d4a504a031040041108040f007040760500c240b04905404090340c003e46107000804030b0084c0c5070000c4031000b404000010001c41c0305a90203210180150303602407aa8006200c02d441502d85502c001c848000209031541080c410f00342020442c40d51011822000d031809100701c50820503842202c2c101013801e0901400030400103030b040400070307010b40115000a601c42c02d401d1402001d803080200300c00115001b0302c0c240800111303610706564044900c40e101040041010780131600b14000d08581f04e14800d0310401640c18031481044800d0a080d1082d01218000c4104192607540c0c07203490040000108140d004100d018015408124000d200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 747554514 1250 747553264 747553267
    0xa080c1908012901050906040909060e030315030106090e03073309060c030b090a020f0f1209010c231b0a03050a03060501090e0a0e12032703070503041a 67
    0x3507003421400c42e120382d4010030310304281003200c44480e91011080d1a02034801d29200b03140a95030000304559002e144074000201c3d4940000c8801c00405402900001e0084001c481c0c80e8a0304082540007194050825070095190400100c1c4003442c9001d144840f403510001145031040720760310a500505a01b0f11401030000c00d10026142c18180030700343c1e000101c05d80c0c1c00300c1d40098606001d8125110128180c040c146410100c16046c0c40341e40c00c01d07901c240b1941c801230311f414046040d036181d441002d00e00607518000041019101c0b4106802700d0213600303214000c200d112120082030f030340709901c0c1102c1c503d0030442400c14040844e650b0020034150380c5100419051003c010750461908440b00b030b00f00c001c03a501003078190f0a1031703051291400812091905440082ca0800010b52108003d40080200754840d02803402c07849003041215441030002240c07039034030b1415800b0041c00520341242141c1118444084000c0d00c01e0000c10360300d000303800c407010314a002d24044a4031140d9035403084c90a4072010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 747555764 1250 747554514 747554519
    0x20a0311041b0e041d0601120303020c12070501050604050103110d06152601060b0a030b010c210201140903162a09050a020c15070302120915060a080c19 67
    0x180195030b00310112803602ca02c3c504121400c204410b40320040e0416007944181d030310318181e400c000034895044032404844015440d0103810704802030b1141c03022101840c8207080340c03102c0c0c0925000081281c0f90291008003c2e54480108100c03d44000784400303000840d41b0300e00800c6d03d1901d00c0b03006200074440c10b000508651103180843c09241c00d5803080c4201400410301c3c14010f0b4018030428401d0ba228002000443c1c103001c8040614003890441c10700301603542c5400c00e5582d00441d00074030025007115043d44015440a036401818207943c84403070065081c8070b441000c0f5489200c1141c080c900c40c50242d41012919510401e044103160b20549540c8070342c16640c0070300c424010710030041440d602603071a006030034510f40300180c0300042c1c65126401e1041151001c4200080b40c402c0313154008020b1000551211141100030780580700300d4200010491050048115001408080880c3c00c2c00e04901c071541c800c1c3c20803035104450300c5414015001444140b00314540b0800b00040040440701704492941c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 747557014 1250 747555764 747555791
    0x40212010b220b0102060903041811310b160201021f050a0c05040312030b0301060f2301050f1c0213090c090504021c0203180a0f170304020a031104 65
    0x1070b941c0b04001d119414402000444540d0007150306103d000c0c0001d01c050300701984941d6880c0f00ba03100d14040e1950540e850801d2000c03540200181240800701e007512078605290041850075110a48042d0010680e0170b882028924405001151600c101c1c2034105025082c0398058854454401c81c118041c546000ca0703c14802410300c0010040c0c0200003c01d483c01c1d0074120100c0c0c1e200300c001030600c441400200b00203594500355a04041c4d19140102d069645040031901600003600310054a114403c0b011607e10403180b10412441a00c42038a054840c81a00540b90f41c841c1d440040c80d40e85080054001c0410014400c1c01c844080b90001850b0229006003001055215006a0012525074102c0070500d070703103c0f0840c0080e0008440441c50f05000d2180340d1900e480140c00d00d135410b90040006801e40c00c1c8001a504044040d009841d2068098900100c22086440c022241e8009020070a502024990280d92140303a019002030813007411a100c3c0b00c980e804130011079920980740c248040c0c40b072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 747558264 1250 747557014 747557029
    0x20d0c03140c011104080c0102150c13030510020c070b0a1e0212040b0306210c12070f14090c04030c1202040905010f0204140108040506220506091b030606010206040212010b 76
    0x22035130000d40e00c0d110741c20300420740d0400c60001c182c141150300001c0f84194100f40341848681040c03c504a140e50b503200840030030360305a241c1e81301601310700848445180e200740b5a0000e04c440044001a00e0002e0b8690b042c415079802051080f0f80054035040b03407000c1100082040d00c2c0101003d0040311640e022340342e03c4e0f540725807094000d03c00000011090000c1400d0040707a0401c2c501c140c00d583e60707000400c1d00c913055549004080b10f80c46124011200c04500760284000c1000d07007500c80d050240d04d61260342181000c01c0e00c0c03000c00d0240c4041c200240c81a0540010b49050b01c1e40900141c00451410b00d40c0041810000404c3c1ea220b65030314102c0700010002d10801c0c82000b1000005600c462a10440303440054040d903101e4140720a2000700000203001250480e80302021388100145d500c000048000d5210712001c00500724480d8000b40041306000098080c440b5011020101c400100b80c010706171034090642c0c6007405a401400468010716000c0e16034101082039130000909580c44c000084c079031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 747559514 1250 747558264 747558281
    0x1404020108071e0e0928110c1603120206190b1314060f1509100203090a06020124240e040606081e131403090d03081006020d0c03140c01 60
    0xc00c04c0c1001c1000c04e81410002c00b80d00801254540000e40004e01e0615082e10044a40700000703643c3c0d260145422030010282e54403420028200c502103510101c1c0d100c040c02981c04280c80c862072444d04401407520005155120329104400911704e010742a04e8400545a074041140d80310300c0e06200721103c040e261203101620b418031840d00032142882c90a10861840f0303500281d0103079101c4505021190320390000c03102e9900c0705a030180310300310904030103d0542c000c0703812580c1c0c4105018400649a903054000703014440c00f4a02c2440c818103001c0d080c44e8080c80c02d00c25001113003464068109405a811401084d4408500703200c03485d40c00440000d400c40d049508500d012500d04000c1c81210521420700108610b114a8100302c82c0c1801030394180350207290b0100400d0490316078141400d4200610507691f002c00054000d00e0000d80c00e00d00640801c004483c0c03041c80c01d2480c140094204d200003030303495900c00d40d5100da0b079007032070142c4080326001c1451840b1150400704010207104440700b445003a12 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 747560764 1250 747559514 747559517
    0xa081b030f070807030605060702220e03040609050409210207030b090d0e040b09010e0c0d0c0302180102010b21160f080f01020903071202180a0f060602011404020108071e 75
    0x4140361442d8050040b440182200b002c00d0703e4807005000c0b42c0c80724070864801c00d8044841c1401c412240b008440040c0034403651405039820040c4449000c407000001e07009850311503e8021a02d03840360709100844100040c046c08054400d010070032084007128000303e4004d500d10680725a80d4807500c1da5804501d003524101d01d60b6210300404402950700c5240a07032000c0c030803141845004500c400180990006005002d501200e80380442c034000b800d00d00701e82603134004003424852400c00300d5010b4002d401c46860714940f404803c1d0b80320020341c410b104222001500604c0071107000e008640c50845d00b0000000000c0350b125115410840c015500c500030b00801c1c169542c0c0820600b0881c0081c203000c14507002a80070f0303006110382c00440d41d011a4800036100317414241070040f611800041c07128500c900214070002100400e02481e40f100790042007080e52000d1b0180f0485607141400c900300c403100180d4890b01420680407500546c881c10081d0740203031a902d071850803c1503014010110f4121001c2100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 747562014 1250 747560764 747560791
    0xb0405070f0f1a0901020a0501090c0302090121080c01020c070e220b160e06071208150105031501020f3004050306040f030306080703111804080a081b03 67
    0x4903071040e09601d1809468040c956400552411642c00c080b000c003072442080d000d40c080358030401a40f08001041c269034000e00280184031040c00c0900c603105007400b0a03401005030381d0003c0342c01401e160720308040b40900301e0b1280a040c095196000345400c4070201c0c8410755020400d5008402042100c98040c2456101707c003543c1c05c1c06241e80e0050185035100400d141001d0284102089841206a43c40408440c85003c200c004140443c0e4a07a404101c890f032200d0046198818018034459240d0104000d403107251a81d00c4030080c0c145411601c881050000798100000794007140c514005009420301030044446602034907240a00304074804000c800d8813001c1d100b080d5161080303043e08180416100070300e140b5244c203000200b5228000144060a40880380c28407208041c8a070703000c0c0f130080c50640d045e50b03038844e103e2410054508403144880d105801030621282203000f01d0800a0003154013140c0c01c0e02e85640c9590503900d05a0080a07500c02151003148030b014204e903000154402c800c01000c0c034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 747563264 1250 747562014 747562019
    0x1020912100c080f0403140405040507050c010b0a080a20040c0c050c100e0f0315010f0503011406090628030305030a05180c0415050409030c1205120112020d0b040507 73
    0x800c00c0b1840342625204004804042c82910034003500f076180c10507003614000100052900d5000a548915031190b500186084100728949504c00084c14600e580b98009102c110325110801ca9588254069444540c10a902000000e19030031a118030300d50110503000300001d00000003504454444100501242080300c1d110200002801102030104c011600c18058002400c1c005140d0310040f60b0060080d03050484103180c0d40d07400c12401100503440c01c0280481d686031048420791f403040d440303180e0096003480c100804070410604070521580c0c0160091003213170f40381c0c3c0410840c61300c2e000ca08441010103074080442e01380c6988824000d18025210682c3d241449103004048420051104407982c1000c1c4981684d0300d800b04200300000021140030900e2026500c01c2062808254402a4000c0c0343c4000e0500b01900030071807908007402803503854952a4581e000350fa00c0e2144201540d00d0540c0c0e00b0041c0190105510411078060014042c00319603a8990b4076004a0034044e07805442561215008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 747564514 1250 747563264 747563293
    0x2011e0908100c180e0a09050a050d020c0f060708090d0309030807060203071205070c14010605041503051c0c02220213031704031718030610150809030a1101020912 72
    0x610710007845a1254161072498107228481030400a407960400d151076521f00414050304001c00f104194000040e034407000da140401070b60f40d030951112a03028058591404100b0b190090603034983d03030340001c10b061400d00070304100850100ca800c02142800f000c2c0300c01201260b0680041c101492050000590724105075a01829030b100b007004e0100d0f074609100c104684107500c401c2d00030080350303c0852216100c81c0c0e80c0781e041c0034000fa03420030350708640741c25411b4102c106ea000c3d602040303a000724241c50065002c00c154400ea11000004040402c015407010801424444a02d08628104001045644980202d40026a804904003a52040c03003014180f040c40001c054648002c00400d06103403034a85560380e0458058114115410002c602084420030030483c00c035250a202c6009043c1d801d5031416100c0080303d1001402058000d80d1003501408046000c0c07010349009040507002941031a04000084034020180203411950b035400f03000c15103160b110b14600394112030148010340410740d00c41c02c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 747565764 1250 747564514 747564527
    0xe01171b010534030806100203040503210f0315010e1903081e0c060f0a060b0301121106030108070518070509100c171b0a02011e0908100c 61
    0x9002a15101a94140c005a030480b044820908440e6500780b00c1a03103038041c02d50324503151645020800c1031009444109a40840344611680003100c2007040e60500d01e5080366030f07004e039003d80742e00f55000e0602109187c0c41e04280c030000b500003461803850702019200b01500c0d90400d8034200e00c1c85058111a186942e04050460100b1209030340a49042002458629852000f84006090440000388407030502c810051028402140c1850407907035400d52a02c0c081d541c2d24100c804050028400c00416041c075118014003044a155130040c604603401d10506103c4440c1d4444211000308165003040034035150034020b14020008203024105661610701484a01884d0107134503030040d04c41100b0003000a400c401a500b0742d8005880c1d04101e40055001a118070078103041c080c00700381c014081d841c04c0080d404001c003d20b034010b480ca5100b80b032000c203d440d03455078420002400708100403904003900d02a40215480300e0f1542c82c00069250703031851f2003418003c40000241c65103480d040fa15452940009 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 747567014 1250 747565764 747565783
    0x6050306090d0807050903030712020606090f190509010207020306070e010212040503030d0914060406090c06050a0e060307140c0a030207051903030f030b19030203240609040305040e0117 82
    0x10054804611a401e00403e00000101040c041c84000300ba203040c10384003082a51446603000228040d07010f00000b001e56941d000301e038090b20031041200042c0300700d80a00155805000d0840b1310044a040066141000e0600203104803000c0d942407083c040940c1d4100503160192840d61681030358010034030002410801d540d0095030ba03a02c4200410401c0e81c400008030743d045000801c0c000344008042c60209800c01294200b82454441c080902040c01450380c00070b0990f0b44100c1e40c8104d0140d0324101990f00b8010710407001f002c500032400418040c10040000c55010406141510b0038000c40705901e04940c20480701c1c031a00e54010141c40d41010303010403e02e00a09011244040c00d66a0b07800c20a541d042c0300c0c04003d04201e00f50b6002000341d8060741028000510080814906810002c2c101c1c0e18451248000c0e446403244000400380b041203040d0044e103c00c00d400c40c4805070340d1941d0500c0301074040600210308004040000089d00a46010700758003920701007501603060100542400d28008000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 747568264 1250 747567014 747567031
    0xc020c01020309011d04091709032e05090106050a080a06140103050d2118020108150112020c0a170c0c091e060a05030d0905010201050f01150c06020702060d06050306 73
    0x1040b83c0e4446a0700000004180000c1e40d0320104580d41c03110201d0040c2090000c0200942e102e424000004030042c130107018160f909404960000842c5034003c61850442490805848581c031112803d924040c0c00031039100e807c050000c5103a581d1a40030500701e5805500910f00d030b0f00075041420401a4901074a5a00318507414203106650440c0c450350340354551511800280400d8404000d07107a021080c1303121003600c51007000c101c00da00310302400110700c8040000728009425980014995101c2e01c40d10f000070341060351040340c80031707141c603011000307600c00708400803944101c514610008502c00b090304002c0e80b0006016484500000e16545809440d440031485034201d8020410310113803c19045034000d42210b0f041312a51284004141c414150f5089680c25000b10000c01c501c158001b1070120480b1020780c001c0103540d90b000d402c86040d11b020301950f502c68503252481c141483c49845503c403941c2c0070b60401890501140d0000c1c500360300c40c3c10202d48007612030504100c185028492194400c551 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 747569514 1250 747568264 747568267
    0x408031c0204060e010810090903120509060f0a15050a0b2d0712110d03050910090213200412021f0206010618050306010f050901080304211509060c020c010203 70
    0x40440c058500132007840030313504010070480010b8035900c0d000001c00080041c00010461000c0500380109401c030080f43e21002d00f800c03c0081400c0102c0041c1491003404c8018210b0803d8aa15800b580507001140d8018002103241d4404101c83c0d03143d01c1ca9600500c68120050b5480f0702c0180a080080034641010080c000c0010400b40d881401404454417160700c14a02d1004d0480c0243c10340c0c2c04281c2046100307152107422884038a50b901a80072a0158550004455032103203003142001c1690035581d0029044409a04041c201c10b016401007080d580000c2144d10610481400705403460b00694040c012000100c03441000350705000303c5801481068120507603d1091540c0d000e9524001031264034200240051406855100c9201c5203015010041c142c404559507651002200000303802110321074118070000040e801400011181111107442602881000710f0b036201d01c8642824505460710140c9060a034841007082c80303003040d500d2082c10005294082260020314266400e40c001b07055520 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 747570764 1250 747569514 747569519
    0x6031b0f030605060a030803040f140d0203040e090721120e06093c3c0a050d050109060b061602040518010501061724240408031c0204 59
    0x6595410a6a400210108064444c0008500d83c29019030002d80408004024003041041c406120425980203803103c18011548400c07c64807050b9950804015038400c1004200c104035140c01ea40d4482040c4003502d001e2075440e80e41c0f03103804206a203054207502c06000350b1001c100000050080d041020710303060710491400d10108509111388013620344292000012001400301c0c81140c04149400540700d00a408003000c085000c10314a00e203c0da1094541c00c0703590a07401e02c14a200003045160030901c0114a2800441d1310644264140842e0401d105c403901260f40d44540400c204038a100d140002101c0710141421011100c0e05a0070034442d03c401c00c83c985c2c2c0c41d0703640300c80a0029601101d0000d0152522040d038140075070020007045040d42000c0c00000c50580220700507455401d0340e10880c105569000f440503803c09406040e51540454600801b11814101d0012411150a400544028012100f4001c15802c075a201c1c40070707a400040c2c4601c1a2440140d46a072504010006600b89030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 747572014 1250 747570764 747570779
    0x130906050a050f040f180c080a033504030815032b090f0e06010207140303030f090a0b0a0b10020f1b060d06090f0e0f280b090106031b 59
    0x58400c2501c103803001983e0185a9071690f2000d6540c504000c1d08000243d001d440504241c0240d11041d0340005522400242d8100c01091000d2035641c103684659101a40e1198010f5044090780366044020003592404501031840130400d0281e4003a440b520228035001010100307120b40c44000901036040001030035204032021040e06240c071b041139a61b01410711200402c03251075640350300403200c0d08001c150005021000c120707443d019490a0f03080d58407860719000c1014007990012107072034060740108001081211f11048194001d8050303816500085030030f4558150440c803c2d9800700030701c0c1e5070700b458908514003090f00c02c0407510f00d40003414520160101050301d51061040f4403490714190001c000440d030f0740b00c040300d805d803960b05c204100140e10354280340300800e080850701c3d8a1514051500c00501400a8031440041080b4000c100d80b100e000001c038610106070f12601c14510040b2801d60004d8192203005100d030380107400015070f5526500307080b480d000700c8041c03201c1032400b031010078800c09 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 747573264 1250 747572014 747572029
    0x427061a040902131d07090222060504090218040e010e010b18013302030403060c09260f0714091303020601060e0112380a0501120207020a030813090605 67
    0xc1d58040c1340014410b110042c0030503040a030185410050181d4000480c0344881580503248561100c044003112100d03440b415603504c015400348a0114000b80b004210303010603a0010946506800444454800d0348800703e0250f4100c003c6a91341a51149500070101c10700744330b031160700b51048035001c040c1d0035110380f00019110180141c18079038941020341280150090202105044100100c5c0700d1700c0c0f0310b07001c002c0d00c80d081030004907500d0741003036a10310045100340c078214241c0310111340c804007800c018400300e400382c8441c240c0c1e000c85004000303c40610313104c14402c9200170b2024000a00705184d0f55010442800703001000079108600c0c40640402081c0c0c00100e0b030741520780c2c500b44a86800084001a00c100d2507814403400c1c002d04100d0001e00e40c5254520120666542c41c4003010070318403000801c2c0b07400c0101c509442c1c002040c60401c01c1692304c581000d00c0e1880300d4900c01480c05da40e5030081096103509400c29a01070100043c054100c0b5210b0303811400a1440d658100315407810b200c00140391 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 747574514 1250 747573264 747573289
    0x51023040b0d181a1005030304031703040606050915011e0f1d060714100e030a0f0512161205040201140a02030d06090614010810050427061a040902 65
    0xe1603074844403c1c8040c0070007080a03801607004001510036290703018130450203400c1140d02c01074071800d030b5400080300d0a00005440940341c1c0000505c0c081c0e42c402d0751360390107600000c10554101d5164100000d168071a524201c0c0240101e83d070404210300404005007984010820090482100a88484481d41d1100e810b07400508585424403d202c0031801d80032001c940302c0720140c1d000f8800600c0c40c3c1008071580c044001c0c000040c1c00d5806528180d81c010b0201c1d0194117149925030030411000700010300c9490528184100360400d10708210800a105404003c2118180492039004401d180300c0c03900291501e02c0503160003018481c03850113a00081040319503074003498481d040400c101c200d840c0248107840e40740c00c1040b801c10025503901c889030302900107481603c000c0ca10548030780b0002e5106504035842401d028414540c4280b0340348c00d0200038145041564601c110164561280c034500141001203603010342c101081c882e4913400440d506002e00081248180d250960384030041e122400b00903217 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 747575764 1250 747574514 747574537
    0x30e03070e060a2c070816020307120f020a1a04020a050a080a020f0105070203030a0804020f01030c0e121e06061503070f0f050d06081e03040605070813051023040b 72
    0xa0003400d80942206040900113064081c035050410030221550042020b0302c2038982e00f00200001d02d0710f81c41030341c50703205081000d0005503414980b1140d56001c0c120310030b500d07919441290080320342600c9402020005e80702d91000144608140700c154070307000480c2006000c080f54400422490042410f80ea1139000d80e000b405850a014003100701d03170080080d1a03c00360040e087d0fa40d6002c016100034841501186e080380324070f000d511130301841c1d4428401e000c0740c1030716500d0340c5001c00300c10003c100780c030440c09101e940d03944030b000c20120f5001203070405440c002003130310300400040c28008200b080ca89089030507420000410b20801618030780c000044c0c141241103003444d01008400002c00c454034480d860908041908000c070006000c617000943d9034046048680701003805581501485c0c4910807442000002042446580b000c501d10700004e0070000e030710000c4c50186076074401c007003202c4070225500d110210760001a0010480b5030301c0070390302441d80301240f050301c2c0500304000c121036030046084161 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 747577014 1250 747575764 747575789
    0x51203102c0c0901030f05060a03110d08070c06030c0c03050304030e211005090d080c0f120a2a082205072403090203120d0b090103030e03070e060a 65
    0x1c032a11000504900300112a01d484411860402404442d5a10030079103a40040e01d009815507041099200d098010070380140300204142c55500d03000b00007c0844441c560006103c240391000600c10001030414500c00e44500c8915031419901504846201200e1b400348104400d6490010f9801b804681d413056060800e004c1004601000c50f8000036150001c00b4074440ac00e502c00c509200001d00004044802c90086c0050354130030760340507100c0c0d944c070b403d00000c21048000700750b5142009000d06004010011018100040700d01c0500880b1030a50b0281c03400c694030303c00c0c01d1514501685010f43c0f41d00e04160180e4a0f2050203004210650007801090150300c20356045c10340880380c6400a40b06900607085401254499046109550b14203000001c0000d0000c00020030b207020340035050019400401a041007016072502c051190701c41c4400205072641c880b003130380c103503610148040e001e18080da94040c00c0b4400e0109240c68010250040400d0703800b00b03010440160343d0800d4040c1510540401403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 747578264 1250 747577014 747577049
    0x8060303030126011401080132060334051807030c020a050609100b3c0d0320031e091909090203100b031c020c0d0f05120310 55
    0x11588100c03101c4103c00154280300c800c000740c04405c14541d05a0b40b0000c02005850205001300c3c1009500320048882611100031031030b1084888091558028170107015521061110f040f10084d10b00b0700f400b14a1080119007002e804900d040d644e50014000c01d4a0142800e030420f00c003501c00b030a00030070040404d0346400d0402d07000c9200340030954034164058102e0300b540c2408001c00703484810403002110310500c1c1181d400c5052030080310b034903820f804144c3c400f8500c00c441d440e00a5804050081c800402c20001500340081d228a00c90981c0103000e607480803050b003506001c0301d00c5c5923171040c008406a07209004403c1000d000f050034400c401078104416039264003603000305010707008007c0079218034080070500041400c0c45401003041640b0803816180a4200c0c001c2000494400c40d106d00d4041c4d000d1211030b5444100d03607543c1c80c60348881d4011112100591400102c80038400c580c1118411300d2200f03801d041160070807402d2001000706507031a09600e054400e00450100320701c111980c0354004000c1c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 747579514 1250 747578264 747578309
    0x801060f08040204091b0305150604063c090203180616110109060617010e061b091f0c060e01050618071403160f09061b0303060e0a05070807080603030301 68
    0x81d2a180252049060119a1f603040c000e0b180e02d45a640c404140075404000346092800740b08040582d90700b1a05011814004055610454442010365201074003d040c800c945543c1d50242d100288089a8090303903078904010707166840c0d0003003140d0007180d604c0031083c09070317401d00110781e80c0b80d8449628202042c1e82064005901604144002802481c83c0420224407515140500c600d84402c1034003e12805105100d000e40d1440210356414000300c402480220611414004291038280100f12001a0002002d058600540780c9070103c041003080c00c041003004200d018068604881400030001e600d454400b086010808100c0c0d9170b00d0314401d000003040309008012070345072680320000042e142d2510000114101d000c04402c43d002c2482009800c1c2c0c2d407823040c1c4a85d0161804c680e10016400c14100d03ca030041032443d50100c0c2419100c0d540822185e6a50420902c1000c5000d40440c50782000d0320302034a4420040d00460410508070304200d41920f00004482c1107862080e400039551440303088 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 747580764 1250 747579514 747579533
    0xc080a0e01140a03200c0c010309020103021e031506120c07050f070b130b03101e0305012c060408030f04110907200304050a141c050a030801060f0804020409 69
    0x100650040400b080d0046000d5059010000400e0a00345600700101400c5d0100454082c03184010f401d90300c5000c6528240d4401d400c000c0c9543c0c4181805401c0c03030b02000c41c06074001c500c00040c2110b05004810081c58001c02a8041179014040c1c80c02444c004031011103503a101c0005040702805000050360100b0072208100c1c000d00c400c45141a11b200a440c0c0030710b5102c52340300000000b041030900304081240646902141c2c01507003000c4000030198038004414090342e02083c0c0c40484402c3c880c20000c045442805000d82c1080081302203102815840703d0446020713280d40d603001243e03104600308030004007400102d03504070740300da00034011991b217914004104114080c042c5070882c0d800c40130701c15030b0764000904a50b1340c0034503521300e10b4941d007141134203580313024074410340303503c1001d0b071408005801c142c40614076001c0002d00704164060340f40da48a00110036404003100d103035120b40f6400b000d05512080250142c062880e0400b09840c900d00b00500524000c0c202a00c01ca589040310020000c2180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 747582014 1250 747580764 747580787
    0xa14090c071e0c151704020d02060f0f070c171b040603120f2a2405010303050403060b010806060316021f060302010212070c03080a03060902040308190c080a0e01 71
    0x1060068800c10b03490500d641e00f0381803184c020105820350010030740d40e0095020310161001c21402003c1540c0b541c00300b042d06140c208080e038011104009800e59010048010b00340c0c010219039081d5108083d01c0c00348a10300c0d8581c0044409000f01900004002d8003083c00c262060001301080c10710a23200000800500842c0e02c0289424a4018090301c0c8c203400040c50000007040e501d480b0700d038002200101c00080d4076014050007040c0782d01c0c0580b0000760a01182d02107084d051a00109040d6407031616022940700303070800d4011070000311f410000c0042a0043c80b05c3c1940038a444841c40c207003a0013151480c0005400010503100c4442020007281c0300b003103d003040c2c8071071301ca84008012174080c10400802d5140403d034014005c00c01c038030781280741401c1101c0e03a80d9404152065424919200d0007140d4000038511410141c65240008001c0018000ba0014600910303030542c1d11600c4410400b51989484480014052080b01e000049032400082c0c4a0484d03083c10090840c002c1c4100480708100c942 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 747583264 1250 747582014 747582053
    0x5270a02190e1825050906040e0d0c051501030c050a1502031b1507080a1a1503090a0b010806071106060307090506040216050a030318081603050d0504110a14090c07 72
    0x713045241d841c00e56001c0c0142181c1e400e032824085601d9000034481904c50500300844564084481c2002c40ca2203004107a420300c4c0a9001c2e03c03074444601e07410480b04407081e84203803007032a01d17054140301503d0100503410081042005000b02070005e4000a9204d01824148503c507202a2500c0e2051304001c2c0a904018601c10ba64000e0501d801c54000d030071840d00395070700c5800d9441c0801c0d01108c0c0300c011091001500300100740034203034006102003203201d40c0014080e24150107880d0880001443c20021603010386825409050f142c40c20580040c01d000d0075000310901d40d8444011b010b1641c601241c021706407481c480001c01e00e544e81e03c0c007180280c81003455003183d01446200c1d600174050007091301c0c2d5285200395400e2001c45050845280c000800d141c0280040c07104000d440b0214010102d42c110840c402c4c1070140c01c100c0b10031044030444200300e4042d6900d103a01e04540001d03161130125074010381741000c2e5607000f0140e00c401054031190001c201030310043e00013a080052040c0072201040e1107007030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 747584514 1250 747583264 747583303
    0x303160f0903240b0301060b04051e03060108010504030318110907020316050313050a0605030c1606091202060903030106092d0f0e0c031905270a02190e18 68
    0x6510301c031440c4403003024102c842940390021001841c5811b0281c8421282e14003c09400d090814040101c0c0b01c0c400506280c0d912f0280d0000130b41c0391414043e650080c048440005502d180504025040e507001c000c0e02c104146488099034000380b00c83c03040d40410348050310380205907031320b561051b03155216801c813596088119906407810060000001c2a58115203102600031a0740d1710f00b07024008000c0e008407004a4414000190f10025080203006103100c2407813003034080007451f00e42c107045071005101502c200e0749401d402004250100115034200040d00005d500d903602d04000101080c9980c052030290040311050700d007810051740603090070005c00036020100190b5400f004400b44000344156400751000000040c43c1d0300b50701e070960703205031445044035000103490b800000046c003000f00342c0181c00c901b440428803000542c02144400c640410000d115007445401000303400403040b00e131851205800d0906000b82d41c440918a600036a4100a042e00b0320001801c16080c04107188140620030803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 747585764 1250 747584514 747584543
    0x10e01060b1e040806180a020406090506040c0903030206071b12080910051e190f0b01030605040b0d060e151014030f07031101030e1b040e0303160f0903 67
    0x60400081c03442c21049a41c0a011904181d960a4a0f000e148a480c507290044c0c0d002603e0b00b40141c201019102c00389060341d1000102c0e078001002c5440305d0b0001c41d03d40350b50300d0400840341014422400150124100400f62038038541d8000d5545000812480420200d120342e49015a8030078040741d0b0b560344c0311801c0011149001c00050018208031480151881003044240600f61075108890181c106207412803015006403249035400ca00107481720400c000c403601d400d15005024800c01c4565940301d480030855001d0b1800041c00c0d1615904090b100303900e040410b07039040d51000c03690200554000800700b55a82501469400c1070880b030708400c815548603007044890200003049c6800c0d1103020741e07401946948401450b030b17122240507001f140c0350712946092001c00d504803042c4640810500d80482c2451071080070780c0c1000521040d07821000c0041070b281403075103410302070301200709001070082d8158034010040c14030f0201040c410700706202c0e00d00c4c039034115188030b0b070315100103190010a4804480c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 747587014 1250 747585764 747585779
    0xb03030f0f0901031b0801030b10080303040606150219170903030706061d09030304030305100f0305010f06060804050a11040902060a0c050705010221090a0302100801061d1c05010e0106 81
    0xd0200c0b96050001e80b41004089000515100d80100480c113542ca404079682540c0d2000c200300e00150800c4000b68080768000341004c000c100440c45940305130004100745181080c444210b8809800840954000d07903481d0060352804c201c52162141c001000018036a035111203804a4442c00d03000340d406000001d0184144001c40e0050740803990400c905140b400d604482400d25008140c0300d210103504100081f0f004284241c00036500304180188040b04150707140000400600d6030390003158280d445030420b480800f500d1046800400181c2420b04491800380e03181030300c848041000906d03a428404400d1000d48855015121050f800f400303071a80c60720143c1c009400c04100d440704490b640b003040c1e804143c0e5440880d8441e4071408955100f80032100d01000b014075034212440d62900280440c00010260381e40251404814030251030b10184c1d5410640d00a0010001090311920020f81109400c099111164402c0b601c251641c01001d0590300f42c80d240b8003401154068541079801d20701d0200710700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 747588264 1250 747587014 747587017
    0x21903111324020309010c02130e0303010f0f0b0703140304110607080c011a10030c0e060d0203100f0302010e13020c1f0c020a050703030c0312050f01171b040b03030f0f 74
    0x1148406440d4000e0b0340189007240c4d60302c2004203050028130015502801418003003d600420f0301200b8012800000036004a032841e003003640088903022041d0400c1141003001c00c0c0c0200034020b00c1c041240b0b496910b450160aa208510141407200c05c00400603082c45501984070081c00341c0246410703583c004c9030410205c1038101c3d2101216079480c1056210348800103010020045001810000c4581c20316201900104000d624000c28050403c844400965845005203101c41c104030380161281008803040c120540d458108200581907a281880983c0c1c0181101040200464442424650300044c0501078040c0c03011540302c902c0307030360354040c80c0d490000d00144064048401c101301c04141d400080b80d94100c211005031880d04203800c1400440d106007a0301d1000d0b8005d04200b240500740743d1482c401c640d0208ea410701c0b1003034181e0042c0440e00d9030702c0c0014058407480000306607200032413070000b140f007034590302d8244902d54400074682e417510103200f40c0c0c40140112220301d03180c3c148407150441ea03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 747589514 1250 747588264 747588299
    0xa18150905041e05090c03060f01030b060a0815061309050a0b060d170c030f0c011406101209110402070606030204060909211206030516090219031113 66
    0x450100c00340880c0c503081038810703400c071202c0c04640a03040400030034402e002400090300c2c0d1500ca000300d080d0300c80952400c01496006190765091250b081d803440c00c111200d010040c206501c1a020594200f080c2d0f50300098031010102c03043c14460140c1c0b5290006020102c41150340c01c205403c1200007010320802140c65603c480c0958141d85003944e4040c108141e0120120008180141440d4002c04141d20000581030b94000301c000c07a86011140c110480203a001007010b100b941c2c2d1610030791501003070013000c9250801026200d8000b920f00d021806882c51b0b07140ca840d00380c211f503641074800501c140ca08114100741ca000d00300f103580302002c2c10104060980d6000590046082410000748401d4a21071075005c5a0401d0000c10100000100503014000c2c00320844204158841250580d480c14440c49000394428001007144481d0504001210009680714910551060120131030a0385c8000b190f5064841030710303002070036180203403400c0402d001d000038540c81d10009042c0410750164070000c4403103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 747590764 1250 747589514 747589517
    0xa051206090c090112110a120f030f02031602090907090509012406050f030408040e24010e030c0112240f0b0405150c2109040e060f0c0a1815 62
    0x78071490420320855032428445e51142e42d200100c4500414190309421100e28801007030001042d6849540d0805911010300c161148200e582d0000d04058024140b08150b03440d82c0081c5052204030303c442d09a601883d28042c0c000c1c0211400510403010034000c54000e0320511104100e54100000740c2c0c1d0082c03200300c0480c0410040d0404980c880341d1070b9101a01100e0040c0c1c1c03800d181480c111666081c13074202902c215500075052102080308000150b803284a40b0300e140004801c09000c031458103c80780c0d080310b06030501224042c6501c490f10080b0b52840e6000c002e09080300f5054100b81a503004008038102d00d041e0300c030050f01c4a010b040095040108440c0d807644100700050b15240000c04c01d2003240b007403c1d480031041c52074204240c190400380100841d014180c030f00c400140d01609419808160204104030300001c1e5541d060300c0c10f88501c00d502d6405000803e500c1ca80702d003842010710750182542c1c030f01d00780100c1c046a2862190318880a1a4404442c00d8410f0365219031101c6091403804d001b20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 747592014 1250 747590764 747590773
    0x13020a0f051317030c0a0f06051f05010e0d0501090605070f02120901030507031b030902210601031e1410050a050c0904091104020a0804060609051b090a05120609 71
    0x48114461416205016424900380c030b00d051a107241d0000742d0740500d035645850701040c010384e4000e80d400c1c05243c0041d03005418000c15183c2c0ea02c1e00d84102c031001450700d8a64544420240404481124503801b900d00a007000c203000b0702c100b400120f40d582c0d107100080c269070900b81c03080d0400019400103401802c2e43d07284e8400741c00195a06981780c1e0b42c0380722100c0148800344500001da6109804c0301d501300c05141400500701d06111490350036040d0140014000c0380d01d0703900c00c2d4114107100c8480908550301c81d040c00c0304840c80c80201511618184030261038022090009034480100000000341e95a007c003c2c80000c040b201e1001d070b11504544e0440c07044603d0034000819030581405014402d9201e103601514007028401080006c2904803000d594030104040b5240380790305c0e6440100500c580d551500d40341071901d454181d00ba10180d030804682c160030f01c001e100030850860405041c80001404090300c840c000400300b00c00da0815030016611000d0300d50041081000810340a001d420003500740c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 747593264 1250 747592014 747592037
    0x10f240503240408040308030406020a09081b040906020903060106020601080d05030402090403050307031d07090f02040503030307050d0e060c030411010903020901090e010e121306020a0804090b0d0213020a 90
    0x58440581490080c80b01824070030045420802c86440c40d8804d00c103600c41410251207481c2d83c138403a00116011600e0380da00181c4c0c0700c005600400035900a008010080900c003002c0c10108000c200f1700f800090040d9110b00204040100d140c041c0c03801000c2c00f078111341480d070399200029503c0320300703124190240c0108444142510b11036030441303203c0d0b0b030094181c41c00ca480380d580488141e0f00c0100428105a660080c5c041565428201101000d07a09002402c240d1300f001c401e1402c4a0450304c495116a00c100004c205070303100442501c0c0c0c003030300904025403151080741548010b0154600003070224015041045030f00f51100b00518081c50080c0c412840c12030740800195031414103800080d41c2310f100e0f94010005e00750140c009234079072444640082014400610b015140c145000442c5003424004101e010403005210400402041c46100500000d00d65813a000e00d640b2941c082e0403035490b110320844040c0d440c1d44c032074603043d15400360000d000c6412a40700d120003501324100a10000707070440c1c0c80 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 747594514 1250 747593264 747593269
    0x30b07080405070b0702030a020a030c060f05070c06180e0108032a1c0207030f0c1d25030e0607080f0601050705060f1815072d0e03010f2405 62
    0x2120300c01e9030b20000500180341400720410250300849812603140c4150040c000040e103540711f03072200440c4038a2050002d0703410031101804810704e02e07800741c04000c000d00810300070078500720f00d035412102d050500c800c00e4400b04444000c40001608a54504090100006000304001005040145001101180040070040d02000c50500d4600c45140d039800009295002c032000702040e056611980110317141103582c0d40d03804005030000501a80c0b20f10324150200000d1501c0003a07590881c0d071040030140546041ca000f450003c242c00d6864082142051842d28441d00030b511110340c10b481201124424500700c80c1c01441010116250503d000700315010481d10350059007030340c04a60740200900b8503551281c1c450f4510540080c070441e684a1001c3c54040c04c030406003c941d00041c1600b20240c0c4334600084040d1040c9107200d00388144040c0d4512004400032141084d410151041c03070945083c0040b03000007400b5000301824039100703d00c0d005031050f041000d443d1001e12800c00032401c8903055506c804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 747595764 1250 747594514 747594527
    0x1804051005300106080a0b06030102040602060c07030203120a0b1806030d050c07030c1d010e061005030405011b03061a2515092009070f031107080a09030b07 69
    0x38642d0480d242429031203003804200407041c08442c2640107010100074140095095039031a81c400400c80e04280b0a90052202c0101c00743d500081c254001d5240901d022030003543c401e030003000a5019603010a4000c10140309000f200c01c102c004111410240c100100e40000502c0c04c00000d91040c002e0412035683d1600da105220320650300107000e464020061001a202035100d0418082107005000e004070024581e00103075009001081c109081c503040c0d90481c0542d094060f00605021300c800401c01006135a0050504511803c0f40303407807910b945446c5026800740410128540007070300a0840640b00d190300d540444211440800010400c00140c1340100c01d46c4074149040301c00070403404410441c0d1628503510042144168803004500301651328031011a210035000321848a044012680c442c244c964055100610442e5440000d081c00280074040b03603d800210001c0c0754960020003014103821064035086600803043c940c0d035003040384000780104664001141c1004ac134034040741030584100c6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 747597014 1250 747595764 747595769
    0x1120c0503060d05070b07050a0314030c09130b0d110a140f040c180f0302040e010212150103060302030a05100e0d09140a090f200c06040b1003020618040510 69
    0x80395103185482d800c00b03005201e040c40c0000e803040d10491100145005003007008041c0a40a0301c0035011343d6010745402031561000301c1c00d6000c40201482400303407000c0c0c9202200c0400c0022603440e401154420400c50103420800d0006038055131040c1c030b103402d0001d6990801c0c107440040390740c10009a281c40351800c2440c0101c43c020303005103034540b081146051039401881c1c2d00102d414000880407001c003e4004448054002140480c80e0020030000c608141c040e043c1070340d0b8804001c1d410f0a01042c5100040352000b820701071a924440d00b03005050340654400c1c8055038026003a141d08000381d05284e80c1d903005241100e520303140f40811140c0307500c0001c41c0d0712060903403e135607030107041d490054603035410001d072500c0544c425540301000644100038450b036a685001541d0105900c09a000d8441450300304204040d4480c2c000c0000e030000d5107010608691043d80544503544548035007425038204c1d0030707542009402c110000350442c0b403020fa10f400c0c0808001c1c100d40503c0660f60385118180255100e2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 747598264 1250 747597014 747597017
    0x7030b0c16110103022512080702030306042a0c020f040c05030f04080421050d030c050708030c040b0c1612021005030a091b08011d0307032006041101120c 68
    0x121801000204001d00800b03010760305250143c1041d011140c4c0d404014071030400d095060034070f03091003030401001c40d054112500e01402e2041141c500051301a440744401851244660f61700c1d071040a80c242094000404000c082051200e10600d0340b102900300914000103074800c6034980d41000321813030035010300c10170310407a50389050458480350100455810040c0040320030b20414032002c142e0340403103400c00d05402003046802e00150f02c10300344503081a002c201030780d04150602244542058003c41242c80b265480100d0036030302d03038902e1006075030303400f031600308600089000802c400a220b000544c8142c00c5a030710428013100e9541c4030380001c007405452000350007507200140c1100050141c805168040e0000001103151817403903492a6504010020f00581c40503004014000003000b4811401c01c0c03881c1c0361503458880c024284040c0c1d00c3c050710342e00a00704105403200c1010b400902e0403502c1000e031700408a0385036050602e018070082c3c1c071030414a170000ba940c0003115803003102802030000441e1203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 747599514 1250 747598264 747598297
    0x801140c070309030b091c0e01170f0106051c0609020403020307060201140703240303020106080c0102060c1e04090204030f0b0903031e100f0e0a0b1e010e0f030a0507030b0c 76
    0x5580e031701003084000810000690040046881c82c02400790640404441c1e02d1340c0300c071007c611180c005070246141d4848a503040f03c1c100c1c100b2a80e22452544241510081e041c0a5141c13210f034018801d00044202002d601070381442c44c0060002a560060402e0740d100310f00f0340e40c9403900d4200482c00c032041c2d41c10300b45a0950550100b845180280d00c000c401c4004025181c2c00319041200c0c1080d1b1440b070350b00c101d00603959444100007104090101e032402c06800d00c040c0015003031000d4808103034002c802c010784040311080034246198442c4c0045500909250030203540300e5540e828906079004c2c11800c1a03c0c40c140000000341d0000c0d022045078420707506680e1307040303041d248100c40490403000140746030703c45500e0b01008580c3d96000070080c3d00034108070300c12040074076202020300180c480d800c0d1814010308440d0300055002120740082e40c2404c0007841c2250850b4035a200003001345421419203074041c000c1180c180280040400c4903c1a80c5c040c40840b25162600e600300700312032041d00000c1507a1240c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 747600764 1250 747599514 747599519
    0x10b12030909130515060a090e060115020708100b090a0204051e011b050a061a130509031b0a1a010506070204020904110c1506010302040605030a091401060801140c070309 75
    0xc040b65140e81040c2203d8400c0c40a41c090307914146845070384070840d060007041d0710400c00c151030205810009010b1000701880349200010019a88000601500c071191056079200d407410707442000035200800f0000112a000340c06000c4420040004007042400740d08880d002400c0c1d4081e5000700c43c11540040c1c00c0030544400840c1a0780c0d4409040411030422140f038907601203030300f1080b1031545941e020302c000d02090440e42c50710100702da03100705c4985200b10040040c1c4005503540c0201d08580808a00301040f5030303840d50040e604500c01c10030615005a40c200b4400040b0074001841d40b10a449180c2d40c401c204440180d444250b6424810260b02030b104000720380050401e40c000d40310940d405000450601c002c0c801088203038110b01d0021100d82d02c14103006101107441c0d40507580000342820b08507e85410130303030010300520000380244c900d561141c90040030001d8581914605820102c0204083c54039102503034041c02000032a1460035590502140c0c807501200c0444100b15030603164034000d90b1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 747602014 1250 747600764 747600769
    0x15060d06020a1101020a110106140607020d0507030503070b011805010b090f010c0f11100305070219021f12150e0f0606130605270d2a0e09010b120309 66
    0x502c100403100800180c0500c4101d14002400901080c26054850a80341066554110b08541c040da008185c1e542d01a42250b00b1a01c3d140300300d451494060303405000414481c14902d01c2c0800c180d1006200f0301c000502c20061015041c0101c0c141c5503511400000380c5407244010090303403003c0c041d2810f40307241085280c00700d28090940242c4507006051980c0c09054075102c85000c03104a0300306584201031944002864900b4084151582580703040c10081800c01c120f00030760711500e00210002110170f0850390350942d91810440505108514145030b100c0700c26420040c0044010300a20701c00e42c0c14401b00b03044101c00da48200041da03075074074010101590ba80d60440d60707650000d041d9079004501008400c0394a03015072400e0000d070400381c0f9025622118449580030b0401d41c03038115800c5100540040450313541c1d0114040500ea008440c036581c10403003101407214100703102c542691920720414002441c20344098250310550112000308041d41c3c4902c241f15030003100d0074040d0380d60b80041050318081d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 747603264 1250 747602014 747602017
    0xb07050a0e12010219091413181a0112240612060b3d020c0307030f110102060708070305040c120305030f150307030b090c0306130515060d0602 63
    0x40181c941036100510a5020941075611888032280594001881d20b500300707043e0700f058110130401d141c041c2d403092409100c0700000545050382c0e48100c1c0c68000001500100ba00032024900c0d6544042c02944114074158649402e5480365960061240000090781603203d455000003075080405085030682d20130304001c2d0748540c0001807881e9556207802090025034903240780116489200b000a202ca41001044081c40c8100405c20240e1035107814010b1480001e068241040001041000e000090400690600a28401c0c0c1c07a01807003080b60000910142c8000003074000d0280b00c510704000c006c540126110041103407124080703881c00c03010a083d5481f07a400645e10500881c0c105241c5900d44c042c0701000f40308260264005880401032080500000c1c4180350002c255800c1c2c907102d41c803668042a03c0c0c078068070001d082e030306440700040c0c00c5107024002400e42d450001d040d90110b2405e2410801a184071030003c0e2491300c1119030209101c59640302003800390b00c0050504088017215039412019 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 747604514 1250 747603264 747603277
    0x16061109030f120a030914070b28210b120309041a18250e0102190312091406010801020721081915080601060315050d03200a2301090b0705 61
    0x60494103c100700301c6080c223200440c0a04112410542e0701c001c003602c0307811015020b51407541c00390004038800f010107400c640e400600c41c0d040b203000c03000304040700340301401410300400a980248010700c01203106000800100007019044804011840ea44203c410780440f00406203a008440350000b24038000469060540c405164043c48020095402600500110640a810104440003c140c281d1b40c0c05200310300d074030340709250503040201e8161801041c04407540a4003141a9807240504144803164040380682c100c04002c0760300780d50303440e6510341c000d6220500c240c0b48504030b203020105449815815154070711899568500a8440300316800c82c1e10400a42000400c2e500d100030306641c0c0195071090002c0104078041d0003a07601d81603001d0281c1c0c01281e61010000fa450505011f29500c4400703002c0c03035642525112156648080007100b2014082107500c0c3c00b40305905044040200400b6204611690603074801900c0213018070003402d03030724403510080c040101c0c80c0c002072070b0b2803195000e401d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 747605764 1250 747604514 747604523
    0x2030720100519231b0d02030901300f020702030312011a13091a0301140108070603060b1e0408062d060108060f06041208070606080d080103030516061109030f120a0309 74
    0x28000c17140030f13162424080c1801c1ca0302503000419010b14542c0c006000b541c00c0301d10580980ca0200603410043c54550201c902c04103200e41c1d4042d000001c07030045d0f0595000c01c0c4d001e01100e13039504662004602424003489003905010400e81020628003214055810b51a58110300d08007150501c00c810029200380458051480c90440703030a030f0282d9003400f8140800b92001d103001c4265041828450a081464012100b410300308441081a180d10504031141504003003180c00035008460004c001c1403049600c01e500c680700e40c0c0c05104100006042142a030724001e01100440742490840f5507201d00112103080c0071500ea000020700d103041c40e40010880c4500200400d00e015240e102d03800c446030502d00181d48940c3c010070203200f081a03d04c5171a014146590040207001a0544018018801400004c080280109810250311b05801200640c554400e1080c4004020014828000c1d0414510310344244170307078a880311040703a0100f9400d4210440f040c4d110f02e0f001c203c2d102900034241b85601140c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 747607014 1250 747605764 747605797
    0x30203180607021f4a0907090905160c020f0103060302060c0a0318050307030201050a0c120f03140115050c0a050f16090b010203072010051923 63
    0x103005035134000d006064050032108926610400500040042e1140ea00107880c0e003034044040360180380320320400041c04000d4080041d01c10b00c0e255503030000303400c42401150420240028040d426402c15000e90544800100821075955000300119007205088980170104002800c018050f051000c0c0c01d0314a46410706021070a25525030100e1001c0d03010085030103143e0030880c83c86081550050781140020100c80d0100c107038a0901c80003c4e2100010300c402814032900140448031140607a01d01c401d0070360400192916803a80318005009500e0356021800001e241201e00c80042540c90861416510441004101c2c03240b00301d81950036a001c440036542c140f0038202d868000940820a000d6151060800340c04500c0c1d08003501002c075036039030b004640460701b440c100f0b520690f800016114416000340407088111607240d5410000d44406070b415402c0f0900c0a0b10282190300b060060460038001c2d800903100400c008000c585888400200c16288a8420350404c138900000b0f014201900400302e554 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 747608264 1250 747607014 747607027
    0xd17070302250b06011b0206121807061d010c35130f0f0605181201140403080703060807091d0703150c0c08030604051008030c06100906030302031806 66
    0xb0450756881e000444000650804004203075a00030030309080e00c40c032600508401400d950000e5040d000300c404001080100000142d40c5000300100144800380b01400d84900986920006084081884038a80004144045801e0552080440d502e0082c0c00941c0c54001ca18020500c040c21410107280d440d00a80065800c0f1420201d00e0040c200d513180c101014110398034000c4200030007055031b400300700c00350711448040058035081802c0310000b40040c200e140000c45080c000510300c001c26120b0104079842c1005e04070100403c041c140f80903038000e445022899550300303021000d451250180f4115604002c3c020005851075401240c640d001d0f4240d01060301c8200f401842c50200d203640140c450f0440c042140d0070510003842014002e603224901840b0320002da480c0cbc401d20340300151649000d00e5482c40024440c04041105101800004068030b940d02c4007110320954690b416500000d83d81400040058016070500c1124100d940c5500a14240920000c0380318609848041030368000200304100d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 747609514 1250 747608264 747608317
    0x60307020604141c030212010f060f03090323071b050d0b0414011503060b0a0b160203010b10030902030601120507030803190f0c110120090a050409050a0201020d17070302 75
    0xc01a01ea04917030307005880380c5844085204d61141a40251822284000c051140662000c210b43c040c040030304002c10915210b1070112180e00003c0000c1e40840c202029022160003420300a00005000d411406000f040302441040c80e4403291003419409000c00f0104c100003000055007613031050041c640f076045082594038a80c01e680716640c07000d0010200b04428000c12005102d415940e000503151000054100403098140d44114607440e1501300c0b61001010031550250402051a10050300404441c217040c0d0002e070181440c5481240300340562000460704a50601c101d940a0b500100104521803440c1c580c4a00ca034400b030b1260040380d0b031251038100842c0e92805090000c0010714000140d0f0744600e280184100b52030104002243d040480c08040c100c2071110f520200480114103d41c1c0e00203d42c0000c03101c01c004e50040340c02c1400c100b4800280440420f1118a0038002e0702504c00f00c9403901c404907480c09140e602c581140d44043c02240429202c0c0e80a040401c5684941081c4130801880 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 747610764 1250 747609514 747609553
    0x50a0807050606100c0314030c090a0e0a0e06041127070f090806150f0f04051008070617130317090f01060506090a0902031e010e07080606030702060414 67
    0x2000e59080c2d012809208050500c01e81d5a201c2c0780c40b5142a41109465540081541030390401003443c424010020607100b80d03200048501c0280c00604040c41140c1d00e11590f0500203080b241e500b48a46000c11480d102c410100e101d07486150b1000c00b1700d05206000007045942d40a2050340c44505001c1112401c50040401d5005e0003801c481d203901000390f0f6605802800d1182c642c1024055810010070302013005140440300f4000c01c07040300d0902c448400400410b01034454540440d510604007018440b03500c40104605064613404c07070580b080c4030303204c0809590301610b00c40500c01154a400004aa107402100c00b21180c038401c0c0740001c00ba00d400e44988046002c1541e604500c0d82000702502d80c480024400c2d0002428162101c0341031252074800030304100003d119112440da00007001440426140e120f040050044908110303540d43c6480c0000002c0d44200c41d2036000c504154080780c0c4a203000002e480c45180d41d03070b0040c00c250343ca554404074032108140c001c185a2040c0c0609081680d001403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 747612014 1250 747610764 747610777
    0x3702030c090a0617070507031d060f040611070509040b011a070602120609060a0b0a0507230f0114060d12090503100b0306060a06050f13030c380a0c050a08 68
    0xe07524500d00c880844c03540f040b0140585041c013440402c100301000660000e03001440079036600c030b83c108030034000381c0480d00611444c265000c1c400307000203000c200c00e504050034100c81150202241c001326101e00070b00402d0341d0150b40142100604500411001ea0103c402d4098260b8510006081c020b0035a540010ba0700080f04094965000e14100245420072807101c5501050440348000f1851a062060085201e03101038201000000907000003482842c0d2316009040d02d400000800208081c0300643c1c98641e030700c04c03a880075400e2903001c800c086042c800c1a0f006a00003840310202c1f0100d80d03a0401c4044400d0010828025240300000300e0b55401c1c41380513041d80c4850001b00711031250000301401c03d03000a000500ca6401034401f40101070740081981c0703107108004ea48541d103101102582021042c0c642c80140746550712500402e007403515001841c0c0104012024160b03052064040009121407405890a208000d010300c0c01842c0c800c030758015509001d501030740c12003185910385041a07480103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 747613264 1250 747612014 747612017
    0x3010c2c030327031f0b0a1208120903030c0d020903010e01050103030e0a0e1918080c0d12091101030c18080a17071509150c083702030c090a06 63
    0x100c0400e11440c9843d400070303030641d104901602800c034a0000040030028261200054143d44100f42449504c0364242000580002c035070364940c117640d51810303110303036409580004047d0410303c0c0442c107018800002d8034080d581c2c111001c0c6c2410005041d4500a400051080d68590b481e16003180d207070781007071051a000c3c42c000c2e51900c459a8402c000e00c2840d10300ea0380164a12a4004100222a2070380201d400303014102c81e401040c041101d54415882c0f00c51800003520100001512011250000070b520050b2485501c07120145050001c0e00740440740e844201400c4141075240842c1103620a0307000f4416030f07083d400e01d04c15502007039000503103403034007500569080c2d40a45d2082d07061040c01e905c03555551a103003801c14070f440180d603918400c2d140c815142801094940c44a80104039050707844405540d0400010030410140340401005400c050f111031040f400d4140914a2186100c0526001501c45020740b1201c001108a007400950000380740ba0044501407100003415940c85050340010900c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 747614514 1250 747613264 747613297
    0x2040306020a030902041808030c07060b0604061205010e09190302160b090411031014130f0c140f180d170706050705070c03020d02010e04020a1d03010c2c0303 70
    0x1352060000b11010031820000da10000d00b600c500207404103003140d520000b0b41e40b20079180c0307403e4500380c0060b14907034400d0381c0d104001040204040b0b80c02076010302d0000c686002409580d0343ca03140ea290b182020b4803039142981013110400602d1501c60007103000740780301e0320440300c1e50905040700902e01140c60300456100880042c0084070b503e080e0040c844c42a03044084117155003041074591081055600c0f51008800600b40d035003100e80c1e2400c89032405400c60840c28840c004a100e40203009007204d24400c00032840d000508404101c8060a90b040d0341001e40065103003898585148461140c1540c0155000d0102405072001880c4000c2d908428280402d40645401e00382c40d0200c2603c100516520401c10113000c1140400c0b02a030408088980640e1696031400441c0012200790300500f5246801900024100d846140d101c81c0403c0d4881890b6142c40d00b072040c103400c241c01d8512801d244c40010344201030700c050307440ca85200002c1c45880c039421540e21600070800301703007140c10000511401142 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 747615764 1250 747614514 747614531
    0x2d01030e0c01050319140a0f0513030203090427080c15040807020105030403020129030123060919050108070504061e0312171812131802040306020a03 66
    0x2014040d40c500303081968040c140c0c5401901c00207085000040185222141c0c502441c1640c1c503080d0700c105003000307000c040c803001c03841e120b1818400340c0400d00161461034506000580d01d010a80c05611085074154080c526110391402004060003c03903800d1070450b00c0d40010f601d00c200291050035041441600101e07240c1105c11502c6003440c401d01c40011039400380308100400202002c0848000e140e09003031494490b11542030803070040200349040308003c00100c000071a0583c1928408040c4030040700288041418000030891104519000c3c05c03000c0d6454010440a280610304d8a41c480e4440c1340d802d44804441d6001005d8480a0f401681c054003c0181808541803600505000d46904044286803111b00f08005507107010b40d00c80585034403110200b24483e94450141c40756800d4179261540c001303003001114030080c010002c15080c440c1c485c40d80720302074400545064803d050f2a0a444048103440c00c207076540c0c950303101c030700840803141c6c200404070000d1300324809008542d003680e034002031203a07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 747617014 1250 747615764 747615767
    0x9060f070f03081006050a0c060e0609010b0307060c0305030c0304060b030303070309051e0a150605031605040b0d0c060f0203160f3c051c05030f010b040b03010302040207022d01 78
    0x1c000c0d1a00f01280313000c40c001d0103c15040800c0f80c1d40c0c0c000501c1c060070003480710b0524500400c20405004240e000388003d000030103505400041c01d80e4021410b407094180c0d9048159500e0f48910401004a10144006071303002c114600034562180c0114004244d45824600080c1141d000b1160400401e0740d40c50742c142804005c1190142072001c009400341c401c1c8225442c15a9070390040340c014108150700c00301c201d0741d000c1500f10100401c0050100c4001c030030044000030412100780642c50117945000960760b041e1900c5800795407559002100488100d0074444229007445440442d0400e61101300030950240c070b00d070380800e010b280c0101120700381c0414915100400340c80d070401c2000002c05850203200c4c4200d401c071080014204204c7d80e8448510b0901c0c010382065680141d224881800719000301e200c80d040300040d44a0801344c2d40c00f0701a42e032900c182c8200c0d8082c902414001e07280500045c001402c06074010f100a500040512515240e032000c60310030015052403001c800030398850b03030500302e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 747618264 1250 747617014 747617027
    0x3040605060906130506040e030406090602010e121204030201270201260a0b21160602151302040f0615110309091611030f0703090506091509060f070f03 67
    0x10403034440c04a0300300b00000a0000311641c03240604070361794002189041d5925400030095404504c01e594580b9070300e00c1c001c1c048001602ca07842c0503500300f6510744c0440f6008582d28000c915000c0300a41041007100802c200014020000c5041d0365036403980b45c02d4000781c50110f03201849a80c041c203400c6403961000408000300c1c14100c003243d2015244400c4070028003001c05501c2001600c2c0058260a07c900160900c01340e0004600b1141e4000404401c06a01240405441c0495414130300e001d41d403030204070383e1000318642e0300b03201e511014049a000c0c65080303041030996000070804170302040144401c0080f02c1a55010184401040001d0000710707800114001c08105420055400e0010b1180815800744000700380d00c01c00d0001d0740d000cac2074160007440341e0754101240104407911a000300c2500780899000110a502103103448600090a140c00012a07074826000b40617445428142e842247c40c03078224400d603581c04442400050811a8074001070311a50303010752814160320042d400d015225 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 747619514 1250 747618264 747618271
    0x703061a030d08160507140601050f0307080706050d0f140105010315080c1c0f030c0201120c0f0c0201021e0105010302040b0a05030d050a030f050127050105011b0c08070b03040605 79
    0x2600940318030803506412000c0302d40d1080c1c030414900132000011408680c0c03803145a0008000b00e2000040da881c100000070224180c0c0c0081d20400140c0b0701c20400c0580d41c031000d2007845100d621002c42404007501c00d5001d45003550f0900c10104610300303507008010641e04d1820740c480c806144003004000c4d41d1b906020703501c050030048ad494900c0c24100700c0381644481c0188581c50154020400000315102000c0e8040d080c280c010f850100c10201a14000b03202e8056014242c0c0001c58901403c0791100f03103841200d24600c02d03a1145070400d00c010b00c0c151100580d00605034198080c0704501002c041d0a1401c00c80500345030700000400e0741c114810002104d120100b464041c02052500380099100002d1000003080b00c1d040840e165814548100c000d072a44045541000c2e09203000010269502c05040308070404014004681c64091601c0000301d80b424815a800100701102c560100490728440c03c120724042c0000d5411152290a007502e0401240d0100d182a40d0000400051203440c0c40746680 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 747620764 1250 747619514 747619519
    0x90d030b030703020906060f0c030c0706020c0a090e1501090b15070b061c200907020a1e0611030c0a090e0105010c0b190c030e0c0d02300703061a 64
    0x21100c0e50380d010968800090000a0203001000045076180d40c0e1802900c9500c1c01d12950184d840076610f810b0341c1c03243c000d000780c5090391190b800c2c0410124008034149001000141000007801d28250018000d0030041c19460361b180180c0009010301d02e9402d6106000c0e1121050224114000340180800343c90015032415250300c09024880007c0e8000311020707003010044501ca01d03c141c2401d441081050064001462a14404100802c588040d4030f0095950002c03141c8110341d954a1034140d807a003c0643c4010010340440d680b0701018a0b0030b61241c0c06e071900031040010b5075840c01c0900d0115034000c2d26914068200440c0c000b40203640403900001805961405070320342d524141c00607001c4004500010440c4501000083e501003130285412411401d00720103020b49501890060000c2501d20340010490281c1842a081400c0c84200802290b80c00ba141e560401c402d44603442905d510107850048206009007107500c612410003401010f1805940005810101081e6034040e00c50710700e11960 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 747622014 1250 747620764 747620771
    0xa080303010e1f120605070323040b070309050a140706181211040218130c0804060c2601050916050a140f0a09030c09050c1c060b0a08090d03 62
    0x411034070241081900a001c1c845042641c0300030b26a00f44030061140c200c3e031824822000b006041c800c0542105000d10200e40b01000141d1551007d034980c5419800100040024070021900003280684402d41c006503d28000503500c86a5440301e003003550041c000d54255140f450104200c1905002c4100201501d04081105582c84100060b4401c55849115501d00e85a406e04050007071808000000d240004c0c000c43d078401c54400c0c40781c24045140115801945040c015241c5140d00d449030540c414507544801c10140d68030394a41c4081d084450010040228a00e80d207901d0f80b16441030408454195440d070030142d0704000a000702400020103544642020351090a5000c0d003000407200c1180c01e91038180c000c7e01d245240700107203105601040d425107000040300124a5400070701c8a0569100f0020844919540c130301c0380041d01c005071503140c080b41c401c104810034210300182050b43d04416084c04203c582d0b6440d007170240c03600002c4021f40800c1c2200c0c1000000b00007440b4400d16072515003001c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 747623264 1250 747622014 747622019
    0x2a031b150e0a0b040f03020705040e0d0801211e0c080615091e040204150609080f01020a140309070803030114090612060106030c03020f0304260301030f020f04180c050a08030301 78
    0x91143c1d41c00f80000d01041c03c0c1c1380701d14084c944207028200180c075026000b4000007004d000d07000d48d550300640c5d40b08000303941000042441d9494a0b0318449020740c0b40e0a10903070803291744038010070f03c480e059401c14810a07090040300060703109030410001c050103406031005103418545046528900c1c00c0c10f44c0700f0b0f2511701c01c00000100e40784410310310308024652480259518400b14008100c24110b9941003401020005500c0d907202130346200352a0f41800790381012040008241c00d0340604001e001c0410500c00300c4000311401c8201940c1e101400000b140c01c03955540310050704590080c1c01c895203004850a002d01142044400c0c03036081141610012458058100d180d901c40f00c0601500c803c250302d8841000255101c1c0d0161050b2191b0342515640e6810985040c600741145803803e6854401990b02c1031100c0c10402007070780c0c12603130011032050800d4201d90030040b40283c080a05a81702c2d072740d05607846035035540d600310240300c5124445480000f420700c41086203664955010740c1c21a401003005 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 747624514 1250 747623264 747623273
    0x5060705040e1308070506090106080c0a03050d050f04180902091e0c030604020c0f070501021c02060a110c03030a060305070510053009030310062a031b150e0a 70
    0x1040c3c3c03103581c2426418450380e02e480c042100340b06071341c070140c018410602884010041907000e0022a84200c007150740c8804420203110300203505100150042d0891040c409505008100801c9508203003118586001d8842181d00901c40b05070092540042d035444c880811401d04070038181d0020b41c0c0801d120105603108046a001034401810903c0c2030001002060007501c0b80d4040e41c4489070220107a403460400c0c10b03c515a206020310902d4014440d5503480ca0510380344506441880b2031aa01a040303d070b58100c00c40d0060101c1d44880811540b0420104e01c400c0300503c095401124180d5001c5400740c9981066071070818281c1020348030380904969005455001000c03030303440c00c2c4c9402440751502c136108561030b021055482e1100d854010030082240c9140080011445070948210a00d1141d40740c8404a8401810910703507011100703980b0344e401c0040c1010065585607031080c074004808014408500f00600c0703501c8030482f917407541d007041e55a5044142c040c40d40300071050002001808000d440d0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 747625764 1250 747624514 747624539
    0x50919020d060915092d0b0408030402011e0e0406050324061302220f050603181216030905030c0616030203090306160806030c03070b18031204030506070504 69
    0x7401410036941d00b100030704002624541c4500592040ca04000f03039405400c008480400c10280104948525104203050340414240044590b0f0800d807001c0384c0d540d0703554507444103a101a0040c0d0610560140904900c1400c05002e0b8540e441a070359045c0117507801d01030209441554111a1183c0c0000c4541c1d070240f0000e1a004003004e88086201e22642c132440c0101d2608032002c0300e508899030000034000b42c0707a40140380e2503061a4488100d100c0070365031b818000d4240081c0b07001b0658040c1c0d08001088908500c000314407200d52025080d0b4014014190250040394400c00f085807032012144410303c141600151030100811064000d00100c401020015070203114501506100c001480407203420b0500c00c005840924030042c0403143c1600b490312440b00c003605220100f60016440740005103281c2004100400c82c100080c008282c100e003000442d10258010b100e030012000021080081d055034100485003894001c605610740e039504604000382001c10041c12001805030030001007056803900704 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 747627014 1250 747625764 747625789
    0x605180108100c03020702100818011b0f110109050c030d140d021318060e06100e06090312030f0907151205060402281e091707050d050105091902 64
    0x400046565030300c0e0060703001b40a9280040c1d0410080c114910f222034019000e240030317500c0c0c0c0d180c1c01c08205410340c45500362034890388001451900a03000c0055070b80591540d10341e285585c140345140c44000a41c050840790940700960b10780d402401d002c400c0c2e04041c000c2e0018414189000c6503048016001540540f040000c880411540040c42000c210b840140303890190002c100a992014183c1c0f44071405040e040c0200500c840c0d1a0b030200e82c180c40d00007005000056251149071400b000c08040010a8000c030280030780600480101e8044030b001600154400c540803800035000c0d0a14079140d501e00a81504808510103c0000014499800600b486400042c204001c105a9220401705019004520805514806841100c11658882c101100d940303401036603040201d0034990b903420550440d5400c41030105003007080601202454040e0100011580022034603915038030404501b654048860998180c1d54884c00e002c6044030a105900188500303a0f510208070004e60006482e500240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 747628264 1250 747627014 747627043
    0x60920010f02281202010507030b01030603020f010e0a08031b06010e130f17030a0c110102030c07060b15031014030c1302180a0f0e01090e0703020d17030a0605180108 73
    0x40024100164121000c0943c4607401150140810301c1250007034041c160075a1020b003c01d007042d0078880c155109100703000c1140e4000b40901c02520041e001541c242010800e480e820600c00e41c00030403407940c1000100524040e0210314120b2285040d400c5041a4060b00f2984d00c584101e401d0051070745c031380302115910540140c00d0a0b910b003040d1a005440ea1542c00501e00080400b104002d80040c203540044940c91f010346800440000d03680c070071402c0344030855240b01d0b503046c03d0000d500030504684c0541200780014041c8074450741001108002074004899071030138048a0101800388546594460280e15000e40003400180c48980c005500810003140c80c0000580c04188003001540c01d51140c0300418006e0314941c1800d44071850038640b104103005180143c22124000561000e103440f6440103580d0300400b528040703041d80c1c2044483c0302400130588200f800d02f1504900c099910b002035004a81c90500080c0311482e1100348000f03034000701054481c811820004003d44400440e51400b91241c5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 747629514 1250 747628264 747628303
    0x60203030c03071101150504230106030e030708040306020c070603180b04030c0b01030602030a060b030105060702060901050d1a041d100510090519051003200d060920010f02 76
    0x450b20100c44405452284913420b6082c6071444240501140c0040b042e11003d44040c0702c48548000a80c42c185900f0000306403205410f40104011440380e80114140c8246074181c80c540f017000d0f1500190bd4109420681782c0c42c0d400229915201000c00c0002c0040246040a000103186000071f004500c0ea4500c0c054162404d50b8006810036100d482c1c01020301e6440f151605155840e0b08101009400c02c480c05030110340703444804510000180180d81c1245c038000d02d400d1911000d0307030030302c102508441c2c45141070010070720044002e0195800380c2c0d0b042400d540c850105051501e0204410784210210a4a1110800c0c5240105240100d00811400180c8034003151340d88136090110301c3d88580d075105007404c42c44c002c2030144000d0300c0d91a8810a042c0000140116116601140d01540c084c0c40014684010740c620050061a041000c1c05007c1d0000c100700341e8203401d9100e800a44094040c2121640c0030b02c190031550b94185041d80c41c100b0741c00e00e003044040e00710000295881aa5466400c201001c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 747630764 1250 747629514 747629521
    0x206070c1502041d040c05010e0a03290a0f0510030312050c1e0c0705060406050706050603100608060601031a130e190311190809040c09090608030406110106060203030c03 75
    0x42d0301200c0080c1100c05888680da03001e0424880c040105032030440d042d0b000d01200140d01c3d03100b000384c4082880e00804840d049455079442209000000d00384440b0271040ba050b601b82c9020340094140300b10b0240d040811004070700c5101504558000b0020010300a12507400d001181c1e100c000c500f13100c6050007001800e034a442075840c0c0300703000d13040600440c9801505e00c070401e024041c010f006407203c030070308407007819880340100000350103140905d8000540500c0840c0204034070b034110300d40001e0090f00303603241045200c01e00c0f01580c0c41c1d500a040306501c001c0501c0001e50b490701c6114a2410303d014040c04110103200041e454201a405802005440313140c40a051013092103240ccc1102e20014184a40000c14600a03028210070340358000c6a026191410314042061402c2550256000c0b26062603c0c003403004010080829440c01403c110b00650003143d0050300744100d8001d048050025503c85190080003029040140c0450550743d050480400006800000b62900302c0306017070502d9202c1e81e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 747632014 1250 747630764 747630803
    0x819031407050706060f0b040317030103030c0807060902100903140a0c090b18090601030c080c0306012328090e0303010e1b0a031a0906010c0206161a0a0c0206070c 72
    0x107450340003141b54a1040c540003a039140490010b204036442800d121089908146518440b0b0100344405004201090b083c1c000003880380c4000d090751403082000080510154021400381c10603c41c0000201d0707001b100c203100307020484858081d403c0707078000144100d0031b0554460700086542d2150152258445d800c4401d1a69604012040071080b0401940300d0314041160540e03a0700b0a100590ba80c00304a0004107403018081000301491002800070300780399107004020790345864079483d01e000e0380000710078198a588d0380c100d4481105c000035109070400801d6254040a244466011300e01c1c0d9803a01c1c0800c00f10030303c00300075a41111070300888041d090b0b44032840c03204034840c24003000b6041440041c0d042d44a94260348a0003502102526807130003440120f00f40f0198a0b01036070701d140800d4404040700014600b48006010300e1401c484450042a00e640c0c580107106542c2c4005135218841c0c0e0200b0404500700e100b6080c3c80300f618801000b09090920002d040303201e5107032000d04484407000c002c05826 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 747633264 1250 747632014 747632021
    0x315070210090614131e080f120a050c0702211e010509060a1a0907030b0a06030905120f12060d0f06050604060506040f050405090a0f0819031407050706 67
    0x6030050703031080c000c0703900503c3c09900a0040c4c1050800054401c0b01284034104071100c15010194804041a020300404031610660503005100322a0307410308000c09030190840c0d8000d0030361f030000c110540c4c0960406c6544d02042d500d008040280e0003009211290150381d482031040b10050380140c9a40c500051840700c5418282c816039541848007140b5000300f41c04405520a51041d1445001d845203500c6d07005014040e6400b00070091070700395050010800ba441c1030342c8040d07004182400d0005082c1920400305081d5072196005201195032103841c00c081c0030341408a88844010f1411a038034144041102000318050381000300d980c61110300004d4203548402c1002d00c00d160304000240038502c6285010000ba10045070103e001c4d41c200000014070342803240917641a01c1f5820201d500080c1050140402400d009180d1545845071300c4140003c01c1c401880d00e0811402801282e030b5803940308000513981c140640b042e10401d85001c0040103000c2c0344503e45134101e81d032131800d10b03980d484504009015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 747634514 1250 747633264 747633283
    0x1c05030a090f0f050c0d0210080910050907080105013311060f0901200a0507021c052104030c0e060102101406011404030f0803061507121d03150702 65
    0x7410b0300079022051062402d8012189485042140c5190300070000b0301040108101e0b0013500507601d00041c0c9200741c092151f4682c4118150202d58101d82c441007d5001e1380c2c0151200d040076001a44103014000080c000e15016003070a02c0c5c1c01c0c0f0790005203802024500100a0350804401b9220003a604051007180165981002802210f6041c10714518014240d001507421498a61901d1885006021400b0b10100c500748581412820080da608055540364041e510890744000b0705124482c0c404440031000c54464000e0004014424403515410000288042c20030014002444100001642c50041500b0395450412540d480c0d12240011307480c01c0c00080316000001d05040141c0a06015035404034800d10342660788445104200c5c0ea111602d10450102600050020030305002140e104001182c1005029101d6400000300c0203d1072042d400184d070031144903000000d4072080750350000b10249500ba1066184001e802c2880009540301302d608003c0c50b41450310340000b40128020310102c1d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 747635764 1250 747634514 747634523
    0x507030b040c050a0e041a0a1104150e091302061b100c090b040e0a0506030c06030903090103200304170409060f0e070f020a0f0203010603240e1c05030a09 68
    0x50601e0302c0c0050066649000c0e6502030400010006400014071114500441d080040b44000c200b004100000400d0011700d80c6000d140c445400d01c80d07544800c001030004008400c1d081020701e20f03e00005042240032140701c0d2080c00d03840184204000d420207003850503a03040f19101d0341c91401540d0407600da0040702a040440c050014900c0240c0401d07085444408075541c0c500d01c030325896188030303002801540290201d8038000f00008691811660195407c404014122002a01c10100048a0f40d004a031843c88581000c25107414950b018050394908500003100c55600e552940420751140c04010006008400003440800a84610300100c8018091341c0c0014042151120000d00d08040d0901c10050704064610001c0d4800380b04c1d9050f81056446070740581529191500c40e40b8042d000b0100c03da904d5540c45500100052200b0000040d400c402c1040c454103c550101e81e40032a2084110b085441d04564280320303c424015226050440103410300c80e890b604c424181c040140101c250050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 747637014 1250 747635764 747635783
    0x412020a050915010905120a061d01020a090e0601170403030c090306020c030c16080c2103040f050310090503160c05030f010209131103012c0403030b1302180d050703 73
    0x30762441d6a104010800c80a81741c40c0c2003540e4038070a116001d0180f1003010b2064000c404900c000405941102d80311403103e404191303540000001032422a8800c0081f0320104003d0603003008903150300c24246521100074205400c68051342001314a99940c0103100078205aa00c0c0d290f10605401f8181c038002454004401715118000c42c180140c0d20340c00314040e00160711400c0c2c582040c15808814100540d04014040c0c007001c60b0107400d07c60b43c004003400300c4006a0607024142e0007004200007400041040c84400055589050141802c003c40d0345240344110b0306024000c00482e01c000122668140c482205c001e506244e0704140c441e040300c6421682c4e041c021100c01101894054020744001c032411142207080c0c07150381c001036080341c8113f080c3d501c0b00481440104241c069050072811200c081d1a80d40c501d8400081411104c180125012400f19640310b58901603820000a43c0906240f4100e0444c5032270150148004a420703060043c5106020301d03c48981000400d0006000460b408078122 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 747638264 1250 747637014 747637021
    0x3060528050714091c031103072004020a14130909080a0813050a0f06180f0c080c06030105040b0d050d0e030c0d120e031c030905011a060412020a0509 66
    0x20809400140c42c4000094600311204402e10307190400c072030345070740300070702010310140c408890200040280c4815000d1140e01d140510310008180018628640314125000d000c402c3d1441590241c94020140c5014910510450b12202e030002c84450550b984400c81300c0e2207035006d5003803020020980d0082c40c2c0e018103201001c000c011043c0c025000314201a1620180f0303541e030068403005c04048a4000e0615401421144013140d41928404030080c00740c000801c020421260f86611540a28004c60340104440541024007654401c10b801402010010305800a00701c00081c0381e900060060603c01c541e81d00002c1440d40e180405001c160f6480000e95600005604020b01940707007041138940240500e0b80c5410741c078500b65124400056000074235408940080c0b50403941c0a0440001a4151044c02200400007150756030b000c0d0040580c0d600030401820350300c0c2c00ca0950710020711041e4210701c040841d21a40d40d694043d5400c3ea86a44120b0400b04044c0c0000340b4105402c1c0d0049400c0b24409050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 747639514 1250 747638264 747638341
    0x1203040905060a0602160b0304170c0d0e060405210304080f030a0f08040b0a0b180c0d151521110408010b0108010f09020c03120a091703010f030605 65
    0xa00d11900b81142c110311103903a50401683c171803a684100074990381c5c03504020300200b64540091a0058041c0c21038035824001c0030004412580300d000c5c91411540208142080e8550083c14441068070540c0d0480c189480c11000c40ca189501da9850070030041c0c00c2104c034031040c108009880c01000e1a80480d401c2e40550010107440750700c0000d01d400010040d8021401c0140a028100d018540c014141500380d40d441d040d080007040e00c03034a00c5610618a101e803603400ca20200c1c0440c003e554a00f980c030390f12215203424100303c0e003141c1000c1201000c1e980d42084075600e071003604421030b02d9504004101d2084000841074400d880183c0f441442d140948140e0f04001c0c90001d4415500f402000300405941c020041d113600f9024441c15682c1d170b44803602400440c0e015005800c081c2d41a0080307070304003200660340e02d16404080b01d0700c2c080c40b41d0382c484070418800500b10b2821700d480c072000340f1440e550626845150310307a05400080c01c0c464880d0041030702c0760340c4107580c0e154290410030921000008040c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 747640764 1250 747639514 747639521
    0xa0917180307060804030809030c0304090902061c0605040e1b060f040314070e01061707180e0109050f28050615070309180209280308070f03200303040b0612030409 72
    0x17010303800121141d00040d9402d4000046a4850032948003c3d82002e203848518800751250680c00c0741c102c8004d10940404511071380343c240e030138416010086003590604c4c061004403070038000e0a01070380d030244010102c0b0b1401c15440c804112025038030a50354140019105029100315440200b000d0810100e6840c0c00c800414200207030340c20f4140000c9281d0b6100c400302c0f0044200d44c1544010800600496416400b07611000101004d822501151681c1c1d0300c04100419003d034402c0007000e80714010849821040505980c2c80500184410f900c01103480940c0c140c0c1d52911664000d03160b03280081000c030760b1035029520802c407000401c0d0740e6595007443c00900c02e800d85c0c0302e03903045580c09641b02c00fa5001c00c2d0080c4d80d903843c03014100050b010400b85107502268251400d1240c010781d06000840416000e00c01050b09074066220341441861900d4014940d00400c002c0c91800302d44041c086400f0480481241d03045500b01c0c05c480e02c95210400019a400388210740310500d0700c070000e40000c03071011940 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 747642014 1250 747640764 747640771
    0x103080415030501230a1d01030606090c270e0103080702100f0e04110405030f210909060f030c0301150302040b0d0308011a0415050c060a09171803070608 68
    0x1821011480a80c1c0016030a0316000e020f80f0031705007005800784014110740301240307410900052942000f269206011109402040c02c1808204090303001402401818000e507001050b030701130100001800954028180310020b0950705549010810b4826520b248041ca1805080b10756011b060170350f5280b07855003941d40000c800324000d0400441c5424030340e000f400c241d000e1210316159071543d0710002c41080020110160004c41c0c4640900000c031b4180c50401c95081c1ca01d00744e40081032041202491003034400c21001e42c8010b005010010468192104400b1603003014003500c8908081d188100002e0900702c00f1a9401c0d0990310700401e8040c03010060902000b240c0c02070f035080150b6000358050100312480c2a00280101d88200e0040140c0b112201c215580205d400d031000707003880c0d191810f070145404d20403080c0c00020008240d07540d948006124094002600ba032003080070710300c16683e1040309161960184025500801d1030460901d003880c003441232400c02420340300156103448001d04002d8064 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 747643264 1250 747642014 747642029
    0xa0f02011b0c1a150d0318060801030c0f05030d050703050d11041d1312021216060c02010b0f04021806120a140708040f030c141e070b0304020907030608030301030804 73
    0x1c5562010802c603855800d40100134071207000803c800c032442404030708000c410085080084030300000465000319401a00900260360301c03803449516500f00030500703d4480e0040401c004083c5810040395900188110b648807007820101e03228603150406582e6409a03c8103884a18100201e42111503801c034000c105851441034040c14815100041303007042d2500300c0b2028800020b251080c004074a00f9030380038008450620483e40e030360040210400841d00116940100d10b46083c543c0d40400c0802c3c020b070948008288020031449245a00040c1e8840f1100d00c5240610740c0010720040140e0b01d0800c0d0358500802401042d503a03140c550102c580300004480030300355285404848400c0c0c00c01145a60701944955450115549407500d0f05001c01032030170021014854191180f01c0001e032441441c000f14a031080240007010f80307090b000100070890800701d00c86034108d50000d20084400c103082d69086501640c1d05d09555030344c8041a001000d02d41c10005a40c0700220001082000c4507004105a0b00d05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 747644514 1250 747643264 747643283
    0xc1a0601030c03020406140714100e1e032b061202031c0c06020313060515030c0a060c030e0a05060f130506040b030f0916061709030703050a0f02011b0c 67
    0x6600b81102213009601a89000450b070f25032041c4d82d801c00301c0c041c120b606e01031400305401c0801c0084c0e0301d1400c00004540280140c544010784201c3c0800d001080807005658100c400c50203e500180b6101d106030009001e55584003030400550089181217803900003440d02c01003010940b2402c3c1000e0511040504912074443c00003400c0c4140d40500e100c035019500d41d01c81c2d03031010240340d68a40c003a410040600b2000590b181c068004101203004030340c0a028a405c0f000950103198041c141007010402c1500c1c09520800b90822809911000f800b03085501031409900a1783d11030002103001c801075001c0e961003003003c03035056002c0070305000404800508424001407142d5510500c800d0307009501c180140b039441480022540349074619541d51056005007591101c100300c034102d1210ba19035400c50b40002e800440109442d400050f041c58000c0c0c2c00c04001c40c00c20403507540042c4144591840103042000c03504000220034000d405c0b110700c80e0f0f10744401c0000c0c0e2010000080c55400384035005e5070019003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 747645764 1250 747644514 747644531
    0x12092313020906091003020f28020106050603150109050d0b0708010e040507050103050408070f060b0a081c11070806090606010905060a0905220207050f0c1c11010c1a060103 76
    0x103961084440008002c2c1207181070054a41c2040407120003400c010051603020000e00b44c208015000900c0802c06401c011100140d502c010150287c238000d14107429a8940b07207051000c0d0303403800b00340d81d4030124200d46882c0b255425001240e007000150720694110350040181c104004000e004d0034442d2025580e000c2e00360703a030fa1000031800c4100f42c0d005030460308a500300707000951003501b240d64080d009055203850500c082e03450460342c0807020700564070315a83d0b0030780f82810302d49580d0400083c640c000c0240f040ca440c054000a00300140005c3d401801000c2025404507481880b04100810300d10301594514504441032503202da10885d406400174180b01c501164034500081911106009581e6004003079003841c1c1405040248510348480220b642d40f891015121103000512007280f04601134041c203018402490b01c0c041c0140346883c46682c280c50208001c0800d0039072901560341089400ca9080603a00c0140ca45c1100c001c000343c4507070f0031419840700c0c2c658413919041c0105406c0e60200034501 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 747647014 1250 747645764 747645799
    0x3090301050f0c0a051e16050d05070305190e03122203031e05090409110f041e02180402030a050f09070b04090911060c2401050607120923 61
    0x801c494a000f80601401860212807007003010b07180c0f80b0704084648101002130010111142c0006005089041d503c0ea0a40c04000080c091428a2419070600398108006c82d03034050320034000c6c800c1081b0301d1140403001c840740070300c1200d9140308050068151000c03110b0610716422160b004800559600c3d10106500c611701d10350801c40303c00c5035059035030b0300d0340b85c0510540c80c0c58074500d1520040403c41e0901100405035510300c46c0504051144d00c000140d0042203042c840f0144c0b1050996204500e0301401103000d00c0b9030035074600601044200165035041e0013901c1078401e070300c41d0600e6400905c0882000118890391748140d014081d11220a00c040c0e523001c501c0307655950103005d403081d0b80c0c006101c10807440c00d4075000040003920404011000300120000300d207082d009810070420650081040080580c3c10745030790003280018000e0740400350b04010102d441d6100c1d07240003d108900d40800000c0982c40b80c0342d001d024001515003100f00004a110b804403c28403130030402d01c00c0204a09442180c0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 747648264 1250 747647014 747647041
    0x30e131806050c0909070309060e1c0206010b0708120910090c2904050d08091003140a11030105130207050d260f271203100b0738090309030105 63
    0x14030014141049640c2d008400c47c09004800c204607001d9807507401e8128148070601030444600c02d0800d581c10080400300c0d00134500041a031222102150800900c804202d8100443e00041e44003108401c0c00c2e11100b4001c0e1601150030190300c101481d0404200401c01300709110740884a107040554502201c560390050341084070750019a419004020400160400d12040744609010301200c0f810f103181040400e852a5081c103a0000090b80d840230008015010801150004403c500410642da2003a101189920040c010f051050080d002145460030490301182c0d0840c3d070102c00d803090a43c8001001c0d05407100d58001c805102c030f5500c3c002429082842034a03110b201d8000704000107488035174020070000c011120300388131440096046415840c0811030001c2c8151080c60709652840c242c0b6072a043d000d40d80d001034000c030508000010100301c414441800251900401c91041400c039018650041130301c54408581c031111908001881c08084050f000e145010fa000707004c030360380e400c0214914 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 747649514 1250 747648264 747648277
    0xa09060905010825020f0f0708011112240d03110111130b0f07021801030203120a0e040b0102070923010503120d2f0304030f020613030e131806050c 65
    0x549460504c1c14040c2e1004a1501140c0100e03030056940c1c80c3d41074460241800780c0c00b803480d102e0354400b074010000c2d01d8091190b0029840300410003820408d410403400b40300038001c0d00e812862001036041c45000c4401d25510160b0b90801020301790964403a1038050142c01d0501c0c0c004e0020b500e0910200454403101080b10b26400c0500c05041c10300d41403034500156078104209100e0903039820f01c400001a00d806100004c0c0600e1203000a48540c9548101840c1805803003803030451201c240040121b150304018515a04041180d001c1a41c0f00d540004034904034040d80407201c03460428a400c0184101c180e8081030840407a94049050380c1c80c0c07002d041e544d0102074070f500d0034070f007041222040e80060350b130242c031081c2c01024607980b00d540c0c81d01203221180d05030341049030400400002c0c0410183c0041100b610660b05002504451400e42e8500030f508504480203001e00c218813034000d900e40e54005002c48140700c11001001144242c00250a1610508404841743c41ca41008500c045200d40b040c0c807407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 747650764 1250 747649514 747649531
    0x5060c030c16050a02060304301d19270b0303030c03040305040302060316031824060905010602060709060306050915030f0a05010f0c1803170f0a090609050108 70
    0x50001d030b00b4200b100341400144251002d00502d000500140c0c0e4a400540c000c3d40290104140201e0129a20aa42c5a90344041c0900f017900010b044e14580c0024510402a0700580301c1348074600b101010a01541c00e01c40521500c41422001203164a103403402d401c05182075606188000f0480310425003101c280c0003040d603040d402480003800d4001d9030f00045074420b200c1d19105080c83d42e41e40c003064143d041696800a0148060181600d44e07070b15100c3e098080c1c1d400e0141c080c0c29078040e12400c0615000a06500d41903000358002c00e41201c0030b400410041200d00740030029907070358000007500c0d000c09803160400114130b5500080c61602c02c1c0118015a0f5000b0715241803034403950300e60005414150704154050143c0c40001403d48030a024920714140a64000b28440411a90a40458207000b4501d800c3c401e008441340d100901424006045e6940401c3c195941c01d0000f40b45080d50181e00e8513004840400240c81900640c070133400b80842d40c581e2a050082c0351902c0055500e49000c44030042d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 747652014 1250 747650764 747650767
    0xc020a0f0605272a09040b131b0303020601060930150b0f03150c0c0715090303030501060306121104110f03061009030302101505090901050405060c030c 67
    0x14040394041d0301032034000d1489600c1c202d002502ea4040003e243c00940100302c0398005200c0c4204100c042d0a0034a40e00030720b120420101c40b2850001248120050b00103441501e071100051003489a501c010030f10031340c1003000c01c4411510400c90340711407551800200d0060040764000600a40030b00c801505803140512090f50208074851007800b04d40c1d880c200b800e805103006144c140451898032801c03044407122100810031000c1745081c000005040c03ca11402036000040d840a20f001041c8008d41200d00d42d0741c415511212150300501c0d04486400c0541c01c10309201c001d080003500007907207801b00c0f8801d8900340300300d03aa41c00080d81201c0092080005890484441d80c5c00190000d41c0c100c3e074007000800c00a203034010185001c10b40d07044001100e502d160b000040c00301511b0031403903910002c40e81e8a0149800c0d400e5a070000d4071138540d41a03082e412601d17500350018000200d5286000f40401400b03440349442e201000c4da02a050070f035401c1c1c405002b01c1020a602c01801800c43e880f503d00b041c5ea15 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 747653264 1250 747652014 747652043
    0xc210a08070e01020a0c0e100503160303031d03131d060a05060903010f1802030f030a050717070b0a0c031a0a060c0c08032208030406120218150c010c020a 68
    0x1502d4040d00380c9026811070082682420014501404075030217030050300d10884942c50502d26481300000c0076007015100790b00a00e4816460741c01020040283e03503040c0307404281c8005050003007400c48a81e4101c0c00480c0000b1a0533440c10f90891049011507480d80c2c019003401c3d11920b403140d030318403003990941d40081018005210030b0411034018142680e0142c0006041048003a01400701da403180b0203031028080000200701035140802c1407084c0c8000c1e101c0614a01000d56070040d20600c02c41100400941c02034a0b6040040e07150001d40b0300d0300c0e401c0340e40002549850b4250030000c1c0100204000030918210220b0300500d00544003040340325018111410150804900b039804800c0a0000c41e84c1214490011403020000c0c0041c0c003014400d01400388810b0782040306540c8055040d008900c00380e106100401c5000d0780840407c204242074000140e0300e00c01d980344403000d4010035441c0c42d0001c9412034182c2115602070700404e4020f02c684001c01c07139117800500498440c0300d106c0018010031321030a6071 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 747654514 1250 747653264 747653267
    0xf02330a060b090108090a1a1914010626040501061706040c030b15120307020a1d010b1309052404060501050306040c030917190305090a0b0703110c210a0807 69
    0x3608186c2802c121404400b0b5961001d4050300400003501001900708140a0800d2181a07400c6103179049030000d01002030442c9043c41d9501e0f0510840d81000401203907a02d480c0008010350039100d5001507410705510341070914501034205442a600540ca0710380c00c0e00586c100c041400c6024079440351400310300901d1a00c864607141b1026000c241c903840e1b2084028240d50380c2c4408a0801545540075507100d0b00e4a004104146049a00844c01d4402440c000e0603400f0b50203c01d1415540f009007455101c40312440005101101d42e0400c1482c18074100030700900b00e00c2810100c0021107003000e09455094410b00b40400d8036010320030180031481c2400440d6141c900786e003004e45981c0c40b500d40014012505c2e00c90640081c0440340c90b000c0391000080c02c0f40c3e018008401c01a40d01e480342014002810f0a01c40386503503800c1104044c103d06028400301c0c0f00701d48a50080c5980c0e4000c0c800e16511041038003141a1548059401c21000f80201c104201c103400c000c5054030031000bd90b8031078610940e40c0640 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 747655764 1250 747654514 747654527
    0x19140f04242f010606030f051608180a0c0602011d0102090109050607050307020612040506010e16080709050306070e030c0a14060d060b0d02030a0b0d050601060f02330a060b0901 78
    0x40d040c480c0d03403182050340010b100134030a01340101681d44e40841c059041401140c101c440141a400391241c05045507507160b40c205c8407081c0c01001549450b04c11200459a09041c480e82d0b42004040492404c40000d903580e0542000b40c05540101111b0360b840c0104195a0803442640d06281c0403170220302c010419440c6c0310002d003440304d0180d82541e141420990000d540c0d5441642056965681c40c0280400e00504124440c09459090780c0020700b420700344588880742c44458040c43c01c1043c04400203991b03610a50020006200190881c0c3e0a401c020202070031105005660340e000b8803c080c2c2403000c0e0319150520380101c404400c49001132207600d000388819070b40411034090310031b5111680000d080d40f00e500280881c4040680044c1c0b40d013001c1054005070703040000b031940b00d090400c000e2008602d010607824112621405c0c8090701805580050f030410070807412010f03400b9003491940c14030358554025054046c82103a100300590340d540c0702210031a0346500807020489800c2c840d1107201d500849 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 747657014 1250 747655764 747655817
    0x6020d05090f03070e0106080c0403080904020c0f070b1e03060d020f0a2d082a0d02030304080a050d092405070f150f1119140f0424 58
    0x10008802202e5a00201e440c008066000c040184283e40041048586c00703801544c0201c1074002c1d0914240c5191940a454058082c05038402d990000d1000b008a60420040303141c100c0e000c1c00d441c9256501c12a059254014400500041c103000524100542403602180d00c602030007084030020844540900103424986100550001462800460610440700424049031103000e01946a14074884000c1c00034926030344118415804508580c1060b44d00042c103e0942c4003100700c25820031140f900088081d425018041c3d054040000c0c0031440c680086040030095001e04101c501d02c86114404a03806c0074a0700c80c40443c07002194a030305035040288810b2080c2056860401e061110985614141c10440c050407a24010840420240140e00c2c0c040c1000c21180303008100f1804600414004040c80f810145280030f488041c501c0040a0251805000c51100c455645464502d000707071104041d40b103400750411003c3c0d5803141403540f8003665058400c40003169115020350381440200c030021003c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 747658264 1250 747657014 747657019
    0x1140a1812051c0623090a050405010204050d0803060f0109120305030a0b100f0f260603070e040807051546020a0e04020309060609041104060e0402011806020d0509 72
    0x1c0000609040315441a03900710400c10400080c0d0074640072969003017096a10b02c03032802005000054031950382d402c2c1d4180d070140907410041082e41d00e51034114024800d0341c00c030300e5011440d41e06082c10f004100001c0d51107034000796085099094000015a2021018031030300b140e0a01582c411000070741300700099038110f40400dc001c145100326030009503400c0124000e200005d0f0840d1600b503501c69000050503135514190416003c030030310481c43c60900d0007007450070903980c3c0046008244151002c0003010010480540310403000d0905240c4a40c0340c1d44905800d89441c030841d4401d88a0b09241607500c0d001d010040800c8116098107082c6400505100300c105c06045100320b40c03411040b04049401030101c44403840180d44800c0d00001400c0b41c02c09071b0069018506c1442040034601c0c00284242d0485001c80d03039204550758518002801682c1c503900b1380d07000740c10540000f403201c50540ca00c3e4007440c800d888140940c1040d010543d24501b0f203218200c01680941d8888028070f001c1d00082030f0710f4102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 747659514 1250 747658264 747658267
    0x2011209020a030807060507080603070504020a1713050d05030915090c09010b031008060112240603060902010318050c010806061605100506030a0302070b1c050901140a181205 77
    0x6800142c12000240d2058410641c00182c007003c0000703501c200780d80400c00b414224103905202012aa40300c200e80940c030301039903001502d04e05d4a40105c13102c14842c0e0305846040c04074600078070301e2500741e40d41e18002c070350b0340c45003030301d6241c80b24043d50a403480b400601d0014019030038036507144c0300b2281002d170410344103014103a07441c00c2ca40c90f1010158046c0c89516072540d41c81c248582e185030071401c641c0c0200243e070000c0d40180b040d40b42c10dc0c055a4004d4028860380149500b01007981c401d100701e082c980b480e240c07806d9000410080550010755426000741c0301007003840107950000ea4a00380060000b0880d821888151200d0341c010380c0159000b61000d000e003410810803501880c0c0c1c0003010401620a9401420900448032041c02641c1d885501039000c2e04d9424400d5402958070501c1d400342607982500440d602080350101c140f11a4400c5107030400340101c2c10016141c6008148444070120034040e0307c0c000546104c41c5004500440c420103804820340c040507220079151b10f41d0605240c040200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 747660764 1250 747659514 747659531
    0xa060f12062d05030a0302030f0d060803032a09090402040e0102040b122406040608073011090609090a0b040222080d05041e0b0406020a02040f090807020112 69
    0x128036002c2910401d003004442541810804805210346503c400d20135482040600000783d800f00a0718071040481210949070f003481c2d5100781c00381c43c00d81c011983c0f07171101104104004070740c5900c114a42e01203145a210213150181016614840c41d0000c5421200ea00040380050506601800c1c024200c00001400c040d121900621503920174180c4681c0c1110f08800d11440d07903402c094200d4408c5d0010807081c004500e0101089040c007641c0314220903c4103400020314024041c8900c18032000c41030f0078503540103200302102040039a200310b0025200e0322b08200314a850044108850401c42d00a00060400e81d28030b04001c141c5400408407501707141c80d001004450380316400900300d4138080503807080c00c034003400003844c10f03400c01540024125445020401c40c060b401501322019180c2c0010100c0c0c5501708100a0a00110707154400c0940050010b0005a02680450012117aa20841e41801006848260030080c0d0f0740d20348000d031485104012000041d8003800e482502c111074040e02069852 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 747661870 1106 747660764 747660779
    0x405010804080310030b04061e0908180310050103140d0c03091703070f03030c020d050910082d060906010309030903110a0f0b0d06050a060f1206 64
    0x1640003001c9000c9620f2480c4d60006507410025545281c100b614040004200c9103e400700c4400142030500c1e01c0c108203003e550051604030f4142d608240700d111039403005c24981c03071846515229044002c0a5a203003030207041d0007180100c070b0180102c200c50340860708280206558a00300665041c54500280d004500b460540b131195142008402c0c1420b4218514407404a01034003144646140705c0070980d041d04441084445035007038689400740c00da42641c69000c0c084c1e14550000551025140703951080301c05560061150f8609915100c5100227145820703804100800041d0481d803c20406081c10040c03a60024400c0c40d0400c00100e8030b440080c4003210900008200e60f40380d1500b0b445a42c0c40c403003548003900365040c0d41d941480d61442001c500c3c0e44409030200090f03051184c0002c1d203160100138a82107607041c1d03e80c643c80440c502c9007181d020318041c04803c9003580d215000304464 = true := by decide +kernel

theorem cover : BRFrame.Cov 747482014 747661870 := by
  have h0 := BRFrame.cov_init 747482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 747482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 747482014 ≤ n) (h2 : n < 747661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
