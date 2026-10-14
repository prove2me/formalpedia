-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0010
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:20:44.001864+00:00
-- url     : https://prove2.me/submissions/6fba74c5-1604-4844-be91-1343013a0092

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 1618712 ≤ n < 1798569 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 1619962 1250 1618712 1618739
    0x100f0b030607020d08060a0302060d020a031409070303030e0705010503010308070f020310020301090c111b0111010e06010501080c030c0403020609010e04060311030d08010810150305030703030b09130209010303050f040e01 97
    0x300d0001170010010030b04031300c6c180005808036a0000c0c0307001d0800540c2c4d07541070300a40c407061509080c90785e1162524000340c440c0720b22602c030302c01d01d0010300075080c65800c010301920f9440d819031090f50001c1c076051050ba030b080400d0700d06507500410b116440318564541800c4080c01c00c0c10207941032050984e1080400550b8006605039030600405001c42e418504090322012040d00d0201c500d90441a0070303c1d56034500e481140f40c02c0704140360000c0702c983d400024508440385004151055003084005020658001c2c500513040250780c9c061601e10329090b8001401c50169000c000d00c58200007880c4485a80700355501c00e10b4442c020b10030080c1760780c1e900d40201c40300300e540c081a0082c05070442414440d400b50640c0c0e4103e4501d640036081c050032b44240c0100406c0d0844402c6c0c00e10802c41e201201042040010b000d04920903200090401021003c0205038640100050fa10045140c201d0b0016102e0080203811a649820030b1a151181c1098196645c007030358102c00003010741e040000544507448a01c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 1621212 1250 1619962 1619983
    0x203061507050604030f02070f030501060f0602061003030c030314090604110d02031b010512010602010b090109020408030a0e010306050409050606040c050301051807030204030804180e060702100f0b03060702 91
    0x51410305542240350100540c060040d0142458204070005000709000d051035042c084054410759007142e4850a03907469551481c0c0040c0c445a40d100814882046074015444c085c0c091400103040301d2404035400c1440c88813a000007020411600050b4007090302036002a41c004034641c0070315029140512880c1d81c0c5450813201995803c140540650060801204041035030740c0140180070f01c4ac0400e40c90854a07081001018104002004000070740786021054a010b814154008640d668030f0b8010000c041c070042e0030075901540704110070403104030000203c0f030f2203000d1400c000302940c11210041c2d0003441d04d0b9000603086400d0440a60401001280300351003420211400c020b24500c64004890300e0109001d60f580180e011032a2842c1c141c20401c08540c08070013860098600340d225601c140071a00070b0f6102200034800c82c0226850f03d03101d03004030034a10204e000105000e1a160200a6507035000b001c200c1d948a540e0310f0280f0001905030040800c000014085569504001100030b40c2c4003a48076 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 1622462 1250 1621212 1621219
    0x70804210203010b060306060f090d0b070507050f0c01091403011e0207020306010f080717010b10030506030c0d0b01090b01020102090a060507020108010b070c0902090f040501060908010c03050603030301140d0c09020306 96
    0x110411005c0c9044800e807801000003070700c007500341103072400031800301e92005003602d9001070a00c80100003d501c9a110512603059907503000e0302c4069a14210345080071000c0540c040d50009014290340d07903800703d040d100710303a0300e440d02a80221054010900400c9488200d0001200301c034401180a0020b4008085036442582121402ea83c3da0300c41c001e100c007442c003500407240c0019404000301c0c001201c01c1c0f0004400c61000007500d2404000003150030081001c06000301c0d4032002001458981844a020750f142d06a84a03030700250140c0d1410541e0105000340b0203015a20022151264803d6042e25120540905205403454440ca0040c0264001c1c03842280051141000424041c00340303010b46521950003041c3c000e059042200007406034010b140c41176000001c00300303c01c0d419a42c0c0e0003400e0082c615a118840c4503411b0160060a46804400900a0600f800140b00b12900c0c004203ca04650646044442c3c20122030001210f20050f041c0c09010040c0080001c100c0f11181c3d8029130050800300d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 1623712 1250 1622462 1622471
    0x30607020f0d030b060a08101707031707030206070305091203150a05010207030f020d030c020301020a0f08070306030309031203020c030f13060306050303070b06030c03070902070605010509010b0406030207080421020301 96
    0x942c00303c05071000d0712101c5030000014004000c43e580130b045015080300072210a204190349442841301c502d0000d2a050340a81d20002040050050b9071940d04800d451480e58603107041403a071406581c840020b04540105692480014404001807040c03103440c0005042e0241d480c1843c4021017641d0101040703040c0320701454000083c0d55800050040202c0e903102c1d00d0711302c6140f129020085d40100740394056081c031030101c41c203800503a0284001c01c1040550348548115802e40300000344480c00080c00b440905241810910209400440f01411298442072500c0f82048a201c00c8001e406080d2094210f88404141058a41c1c0584080d02204500f4401c1000701c583c1c8540032400c1d5409442500c1e0142c004000460104181a2410f54090405400c995100f907079400882e180100c550301a2000c0c40e8045500344c200306290203420300511f07046881041a5051644400c5a813140c0d03c141420715600040000c1044151010ba4000b00100c044a0704a01890000d81c156524840400c902c25482e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 1624962 1250 1623712 1623733
    0x3020c010b01020a050a200a080102190e06090402030901110a02060108160308030708090c03030f07060501090203060f011209050601030b010504050f0f06060a09050a06110601060503090a02060702010e030607020f 93
    0x34070301401174200d401880340360050345030807149201d01d1120803400c03204c1310a42012901c4001c1c601b03004081541c00144e942c00154510060655404c00306401c2007411102c541041e5105003d488481c94101c0d0b0045e0740b034403a03000e0540100141034080c070082ca0007140b0400071640210701d45048400345400e03a000000c07004c074031072800d414070300000340504030a0011421075807050255590252031034044419a00c0e4080000e483c680002d01c00811754400080d0704000c101c0980a454018440726030f0035030031401d00a0004204220116842e0f04029070b68103600c1c50034842d0703007081d51125085815601c507546c4a0601c10041e51090040c54083d0741424081604048440380d1b0600c00c8120402040d220f4485008211003580004076900401140d620302084580ea118088002040181c60704414400341c4c3c0d003103906040c4160b100c5070501505104018070710394081428400745504540340ea503103816920050743d1070101459881d82600c9088200302d0050303000541701c83c0403100441294a12a01d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 1626212 1250 1624962 1624967
    0xa0608070206040f0302030909010305010c0f020a02060409090309030c0603050402010305060102061005010e0105040b0f091503040b04020d0602070605041101110c06040504050403050c030f0901030b01030207030c201003020c010b01 101
    0x800ea40306001a840304001601040d190b01c2c2c5008128440d02c1980e1600e1499400a040c00f0020380060701c05035905d24086042940048414000096078005014220180c1d00010380601981c80780041c51525098083d040510803992000035652002e8000040d54a0310001401040121012404a4940400f184d81c640c000039400748603500c6103040000d202c0c106001121448403100391641402010311020400030301c200050044216110102070b1101810400c000c0e95559103c8103c035042c004005000100707640d4204c3e07680c45501a42d600a45c04424a0100c1c0280700e0440d01034451803030841440104100405a001045000d030f075000d1509030b164600b591a0b40805859030f034444800c020030400c0b8180f03074000c2984603000c1d080c582c0c20060b40d004d07094195405000103a040c07400005800c6025a0184030344a1f90300310070320b0b0841c18180c09950180124207501c2c800340c1f8800c200702584184001e901025501340f1000340c1002502d40c850000903020390414540b1103a15402d06622504a52 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 1627462 1250 1626212 1626227
    0x60601030b09060d15020a020c15070305120408040b0703020303060a0503010203090a030c0204060302030a0b0403031a060706090203070510030e0c060901020c2b030503010603050702011a010311040504050901020403020a06 97
    0x800c000c041c4400e50b21003004200c00700ca842141116000c5c80c15545204002440c4050280e407100e68000e014070340040c200f0000062086040c020b0f101005002d030304042607104068403125000218865041c1e1540d00304a00c481c0255884440c102600261242c00c060307000c405180141030584803416402d458804050070f07404211150081036100300e24440100e8400c044140441d40040d2001803105d840380c020900341145810709840354602031080c0800c0540c1481411075101004400b603a2403010400081d4003840307485805011b070358880c80e411003590341c00d008800013014000c10380c0c92007500c1341c18081c000e4900c0080c662590b0080c038001c1101c50800900301c4001810503400740c204a0a140b0803c86500c001051700404801c2111503458801000ca8020038410301a4036156201e62504c0001020750304001d250745c04590501003820501c0e0700c103404107010701600f400d0200e540c21404031000140e000325030010341d1190802091003003500f010340c0100300742c0e030081e245a2501602c0384001e86616 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 1628712 1250 1627462 1627481
    0x30d090e061c060905010204060816080106050d140702010605030c03030405030709110c03030403020105040209070c0b040201032301120c120305030103020603060607050105040c0501020f0c09010308090102010902030a08070506060103 102
    0x1550001e0000d10301140c0002c910041111848103014440d100d150403104100800c442076035001078144500f9410108840d400002c2c1d01c4801c07509641c0060003003e60a040c440c0b01c081c80004514003070f440fa140e8209042202c840001c0c540c071483c0c00040240030b0b0030b00307105040c000d029a114602107410048112030680314041d000740701051a02d000c0400400c4a0b41030403070104010700c80c011514400340010f50050b4040e90003c80d00f81064010401403c00207000300c0c0c24445402d40884c0010040c3c03115a41c0300342c09080014050003c5600c64103515264070445030310b011130400100300c154002003c4501e1500030101d41c410780b41c4400c070244035500c0c0030034040c0101380180010401480c11300001c550003c0c2c0508690304104540c1d4590f405c0d24400e035070465091513030004c02e014550341000310862051401c0000c111404200c004242c0040040c000a80007100c00118602a0790007504580e01140e0b014007154000507450078102c070603810003801202c0034021400404d14962203405030100c3d1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 1629962 1250 1628712 1628729
    0xe010b071707020a030c08011515120510080a03020a0b010602010b0105031f05060301090209100503010b09010c060b030a0b0103030e03070609050103050403031409010209010212070804060804030509130b030d09 92
    0x1244408486a07525040141c040b40e01c1502a60088006040c2d0722181004100140000c6480380b1803c20120602441da0400c501050074030f400221056804503a0310b04440c10380c100040c1940318600c1e0a401c00c4080d820000d070512920946c001003650016140c1c00c2c2a00684c500070190f41c07030340e10803801d8440301511640051001d1020429240102d4020807450600142c034401c1c13240d480020440d280c00980c0700c031840c0d59006c112501e840c01d00e402c0c081d100507820319200346558106080000d050089400e481e040001c84407101080207500d900c00418044010200d8680340b002e894030409103402400110f000848a03280c1101605000030010b003900c006455101c1801d0070f0500440080c00008d00681c1052b441d6001d4a06e444005004140100c0e01000090790780c3e2013000000e0b16042c0543e5403140954010844140441c500313205880030341d510b5140040003503c5900701294240544000c02d41d20442c84440764039030f050160301401746441d0a03000e0346c040761725a000589074459a44100c008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 1631212 1250 1629962 1629983
    0x207110907030603050d08150102010b010212160503040308031008010608060a020304151a030f06010b18010215090604020103050601020604020306010603021b0f0604030216030c0509040201050c0114010e010b07 92
    0x115454500082503018840c2e25002400c242d5036214070b45850180c0d4409008500e020060200701007400c8044e102d405020300091224566120000b55aa4240d883c240c624681c08500c1c0c030420001800c00c513511a80180031240c8480d100c1c04d065969920681e180411000b030080e00090481040c0582011542e840e4041c00d19a07488a6030500a58030082c0100c44c0d038030707a00e5140c5c0401a098480c0400007030f240c0c968180c445583d0070074503141914159003142e0552106004000b040020800c882d10325100e5105040aa105280182d24000030740d44c5031002250024100540ca141c001030003407050707000740d80600c01c9850b403100580e1038090603500a50550080c100501266000b0f40040088a442541d2048180c201c0d5500500300b280b198420b00d10380c6c004d0810b10007415410400c3c0a80021081c01079004185141e6980107504a13900c0707000d0003260146d0001d01968001c3c026140304c900c111009005880784107200c05100b86090040310814544000003140030107408081d101450f5100d180c000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 1632462 1250 1631212 1631243
    0x1030201050a0302160c090c02010218100905030703030c02030606040b10030506030c0a0603060905060109050d03080c0706050a0504140c01050403020910030807030801080601090c141303060510050111010207 91
    0x1106a48401810b4043c540c0800034915442c148920010149000d544001606814045c94070f06581217080000116801445032069074000c035107200a12150850b03402085038098001502c514406901039070749401222400024583c20840e65181c0c2c0e442101600c070940c0d2040c0030007007210f00300b14030075400100d10010316a4240c025403100f40c00410060031940c90540840010718915080d0300700c0800241c0f00d80d030800c01218103009007030b000403007400c003509040c2c10800130034a00ca4000d2302c00381c03c2005050104503048840030883d040070b40c00c450140103070702d030032a0400080c00054a007158030400c8103810219031200400d640c40e94000595030285403070702e95002c004008901400c004080100c410b000000100c0035801450118401d8031050402d42c5095407050030170005174841c07c0c03d2030800f540540c030070760b1082d5040789103000d18005a845003410102e503604030410b41c0000f02010726002c10301481d0400ca10824045860036030702c2004c07017185410007600741d00900c14001c204038845016107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 1633712 1250 1632462 1632467
    0x50a05030609040501061703090307080601030209240613031103010b010801150509030303040605070801060c02010203070b07050702030d05090f040b03070303030509100204060801050108011706060f0105070204060e010611070b0301030201 104
    0x203e8200d80a40d00116009480340c0f082800a103540d24540c0240d4000035108203241000d12a080c010720703845c000b400c115850341d000714044000051a2465440400d1030f00d440d4010202c00c0c3e121820300c0a0045522046000580510310140340420350300d504c5200301c0b0500d40d00e4140500b81c90020103940b0040ca69203400f160444a44030a180d440078081c0a210703c50b941c2e18200065441280522004149810130709800340c03140c20180c01c0102040554038840d000760343c00108a0b00c80503400340d02000e1903580d94404031007a0082010003540760281d800c61b840890750100140407000d008841501d88045a20208022200e01590f06a0150003c10040011900952000d83d00c00c0c0c00c03a06032013040d8444007016041f6403180d00590085860000103124035640716a019000d000d0107028900001604160b142d83d42c50f001b00000e104041405090b04141d114400b42c6202c1517000e04140000ca442e80c14a1804904c01d0080000003406030040e07405e405400104901243c640107030ba50700c0c59003583c004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 1634962 1250 1633712 1633729
    0xa0203090d0e030102040503060f01050a0602070803030c0304110d0302010c180303020705060d11040905040302010c05070b0f04080408010606050903010e0109030507060c05040509010801020a080901020a09050d050f0d02030703030b01050a050306 107
    0x41d83c103550038080010b1a072401d000030303403007003c1d400d039401941d60401d82000000f1200790461011036000140900c0320701d90000440e50050100a4000e49940d118a440040040580d5450b50041480b80501c010140c0540045034208103c1c0c84807441301c0b02d8059440c8007003035141b0005d00141d2065800304540c0c20000c000b01080c4002c840041280c00280c40c1c594248c0c0c0c040d5000488841d60307071042105040d428812030450840910f002d81c40c1c2111501d039101100006011040c54404090104c0c0820000604860040070303040000d028841d07544c1c202410301e422114000e070181d400c0c206030300c4080406129440c1803c0d1b0603200c41e03007084c0781504c440009000110302c5905002e01004007050642d62600458004d0840c50009039483c0d0403005c0040900801421400e660313801030292000c00360300030341c00106449044e9400300414045007451484c1010041c081d0a5500130b64079014040c070f0740400180b2046000351000e000c01000780004417110300c161141040000c03014000b04000345080e030380 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 1636212 1250 1634962 1634987
    0xe06070e0603090c040c0909050a0605010903020f01030905010c02030c07050d120503130611030405150606030604020c0a020402031003020109270c020109060606020304061706060906030402030a05070e06090a0203090d 95
    0x111140042d0080100d01110030b070a400b81b010410041c8208a0001c482c010290b106078042c1082c0400c924100018049071110b01002344076050341d0303085e0f10040e4425400075040d642c028000744040005080c020307440760302c03181096840c0c0c0900e48010469040881528101e203a004c05104130160446400300c6507074101904070b84840320325170701040c04144a80540404400140c0e40300e0f6a0b0b00b01803521919000e00105c40302c000304030081c1000019640c0c50180c030ba010f50192009640c40408070b041c181420140c15009503c02d01c0403092003000341103000c10f001520300c03e0300c810b14141c0d01c0300f100520600902e030308029003141c44588403492140d01e40240388550301c18000440c00c00300c0c607640c041c1901c0c03540d003195005070310104003000607692107503011347c140000d012b041c109420250081203052081d206800c2c0038506c008003180454604004801e40c2c01e0300f0900b6514055110421080c40b40f80680d4803c0c4948000c501040c11540203200712401170742c91000800440550100c240e0b00000d6024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 1637462 1250 1636212 1636231
    0xa02090a0b040b0d05071d130902090c070308071b031d100e0405070302040509040602090d0210030b01030506040506010e0108070504150305040203010608061003031110060303020a0203010e06070e0603 88
    0x3800001e1207441c00000d0406000034001540c0c0f554001d0715044121000209142e08122030714280e0001507060380314000c2450720079501ca824007510703040000c02603c4003290086d0441b901204200c20201401d02030300455120740d031407807285c1d01c80010403118040100028103602940158203c00a03010b10740459850350403182d501078800285001402c1610f4140420001c507842040800c41841e00c1c1c45800e03400000d506007181003078280408034800400c0100010105079000401201c0342c1e98007426400210360007010311452400740e1000601404004004601107030a240105645e40f40a010315072150606079140c0c10040d849200440301f0600c00361007401444020400412004501044d00e03503030701c0c11924080f407107040c01e00c145070844156500824080d080030f01404002070503941200c04981d011f2404000e014002c1c1340b880e081a4140c81202002c81c9044400402c05401080c2c4840c50b42c0200d000f082542010158113440e00c1c0111046000545640014892032402c0400b864000c1d04a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 1638712 1250 1637462 1637479
    0x180605011b0507090903020a02041508070306021e070510270201080a15091401090c090506030705040b0301030b0402040e0a12140c06131202070b070204020703020312010308030612060105090a0209 86
    0xc03880b04c0100e801e0100180c00607000718a035101542406d002c0c0010100c408403116003050b00c0d00724060f071100b845000003132010b80c000491503403824000d02042c0307205c409800c640399030f200b1030320b03045a5600c80550b40956583c200060850760b10340c640700c010725009605614101e60070303d550045681d90780c014844c9080c1641d030180500c12000c011100307409000c4c802000640050402008840700405a01041d040e07030419040902980d4090403810031200191a0701c0e450b91120a000d0340c05016640001000150201c000001d2000c0345007558011350081d10104a080620844640c4800c04444094010f07000c02c0d02c00200d0a1190300d07204046000d6000443c1400c4290010b9410705034280c2d2003100300143c2d22143c800380007071a4000c21801b003a5000800505d890003038407080c01d010340c480280c80342e030b0301055550230b250092040720f0000350b032030040018030340c3c40c0e103414582600183c440d9805600e076060f0741c842580c3c00140c00703810785100030b10421540da00c0d1b0101002a6009950090304403110 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 1639962 1250 1638712 1638719
    0x90402130b04060306050904020a03030309020d0609050303061219020105090120010906050610090b0307050415120e0106030308010311030102190302030703150e04030f02070803040f180605011b0507 87
    0x2600d150002415101503020307a214030b030002c000c0c142c0c4c00700d40140c2e01c80c4404105100060740c2d0a031009044943c141408202e00e0241d0000075486240b204000d450b1909258a031030030088040300031442000308490703581d07002c2080a40c0c150b54105442c01e11918440204800e4055030062000c3c01d140308051412081d48000382251650001001201e002142c3d100c50b003200c00c00c00b071402403581c024016a01c010046514003801070034034132203106031100c642c1c1c0000481c0503a0320860445000d440e01c110000e00c0da5440c00c82c0100244905150207402520b818050f1342005d4044c0511310840f81c1540e81c058050f425901c0300c8080201940700c00f2340c150340c208600001c3d922480d8000e596200151001602d038030784020040c00340c844500b10101da64940d001c05002070085184c1441d001a050301d410782c0790652802c0305034034000903500401c0480c0700100340003d0104100c2e240c1c1d015155946000194980b0742250302d8252451400390502050b000601085030183c401840c1c00400e0060301151a078641c0c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 1641212 1250 1639962 1639987
    0x10f030b0a0e0c061c0c030e0601060c051212090601050114040509090705030f060406060e06060703080405010605150405040608030f03070c0c031e05060609040302100c030603080a081803030601020a0602090402 92
    0x3101100d241711440804981d41118214856a05000721908043c000c20843d082d03111780300d600c1400b44105200b8617007000405c0c00001c01055000e18840d0305466503400c01e84820710300460b000c50310b51a80f841010008119544900c283c50407043e000c84146081600b050104402d81030700030440007440c0b041d004001000ea808103d031f5400002c886010300018245410700e10705650198010b5010b10043e0f000344141070f00e90a08540c0201d41524003031002d5115450300601410180e40540c0d405420035003021441090040100200c03502101c00700300c0550740b80e088a441e4081e208500790807420034400070780440c1c000c40b0161009413250441360005030b100e645004180c0c03080303900191441e04040d102400c0010070001d20380c1101c0f00706c41040080c0340c60390300250b55461000400702d450380c48140e04071003e8081d03041403001e55440034825031030700c440c40001071502c2c208541500002d6000038064802c0c0d40c010045a000b044107134080c0003007408075152007020350300407030361690440c2e0300700a505070300d40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 1642462 1250 1641212 1641217
    0x1020f0109060203090d0c050c06070206070203070602060a0c11060c0c070b030108010519090b0106050904090b0406020306011707080402190902030403020a0201020c0a0f120819020705010206010f030b0a0e0c06 92
    0xc2c03040c0070068481c01c0c101038842c030b405000304940040c480780c0700300390000c1080081c3c082c128040464405503103840c00e101140840c0030300c540c029014482c2d1480402c55540100b00740e442a076000104005150050380100c46240c0740045140c0e2580100c0c0c04545004d8a010040001c66600030440e84e681303070340d00352089256009038041d2509940d203c00340402050920844a00c20b20085414400300119440d410845001840394074107202c8001481451510313943c01115886800001c200d0301d5107403609000c0b02940c422101d00d800103500c01341c00c1d1400c1010501e07103401099942e8840c400356070395a091000c80c0130200301c0801584892a000200d20500b4001144601d00c00c1c0e02030700c4034408910001e45000c40080d0124468407460405000d408800f20403002280c500725070801c4403010505003a5618440c01400c000e50031607042100071000c3d00000c2c91f90485d01c0a81c00c6480980e41e03858503083e90300090000a022400100c0440d012032880d401480600e900c850644d45090801c00006900d036 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 1643712 1250 1642462 1642481
    0x6030f07060804030207050901080309010305150d0602030f0f04120c03030212090a0209090105010b09040f0204030c0b040f060309031704020a05031603030206090102030705040e090304050a09020408010f0b0604050f01020f01 98
    0x140b200040004041d07052103284014102921880b02c0b55041045080e2640220440981096034420000d444480d841601e01d0701c405014004100b0490300e82440000307948112901c005034030069011906074018501c1e124407580c1c0104c2211542e00025030100c0e282840990300780e00b055000d02c002072008101401c510f010300f480c5001040080400d1052144a810080440d890350349400010410031136010100e802405085600060382c00040100c00001e0040360070191002d040340e01c021403924580002002502ea050f403294a40036034550046080c2c400c0400010000345d020340003484409460410240c0085c0300130529040140c80300082890a0b50103886150905600c090400c01d142c1c05000d000e0b085229040250303d10300d0300d0000505948203511aa105088094000a0007682d050050710090180245800841a5030700824400ba40103030180c0180c951030110101080b01880c40307402c000e89405482c2904091800080101c5008180405815401011643d8280010a10610400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 1644962 1250 1643712 1643717
    0x220503030301140102060f0103050618030d050c03100806010803070602070602070b0c19020114060108041401020307030f060602190204020901020a050a140c0303030f0f060109030221010506010507020603010504020306030f0706 99
    0x28143c11000900e4000060030300980c280c4042c0060002c02c40c003051050340403141403104440300d140414040d14520900301c6500a091a050902c00e0381d00341f550066000d04050307010800101d446041003501c0d0202031254005542c01000b5000004603650042e004003406008010f0401c4160340b206486060304584c1007003c55070004804a400800030310b01c0e0000ba00c00c0c4001c00c10910208051019650042c1849040c0400d103400101000039100703030810014007000c0255203030305105401070050416106c59070100d6080c51030201d1464800101080c0d0032484200d4518031224503000e020083d804078503043c3c118090a00c01e00c02240042101c01c180920960403111501001a039190030210580f041ca03110381c2041052164481c10752146640100d8810000d41264980c00016282c1c0350b44d9600007500520b07040d00004820078184201c002c2c0c0c10000c8000d0040f9a200350044840e480f0b4100c00070351152003400103020310300381540034552010f0040c0442d01085500343c06c0740e180400790b0340a80300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 1646212 1250 1644962 1644989
    0xd0c0801050a080109020102100203220503090a06030b0102030901030b03030903070e0f0106050702011205060103090f03020114010803040f060507020a03020402041502070605121302130c020706030b030c0303220503030301 97
    0x2071030a20b5140d410040441000030400b60409600007504c907003016140d122225004008a6402e82c3c8028100c61144480300091540550318034196884e0f03000b040d202c034811050b04070300203183c5000b4000d00e0b40f4804140d01541c40c18032180c0040d4000c001ca0111079070548818060800c050702d0411500014042640c0441e44916182c3c0d01c01035006016080003040040920620340180d0b00100c00310420150701101154a99901c8012002040d551001401004002d2129014144c041d84003c02c0a04104011281d50b038903608400e903284114440d44089040c00031080110512800240158038401030489041c280c7e2500010140d81080c0c000c0c00560202180004000b03404001100c010304050900e00e080400303003150b81c9910b031001481c0d90740c01c0c0886401041150341d01c04205c030039a9100401040780598140c4e0095540c0009c0c0102e1011a20740f159011032403800080031880d10130001c000710302d400b0814501081c2850b0000c0308610b6001e188501080301d42e003e0ac0070f0741c0a0030400541d608d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 1647462 1250 1646212 1646219
    0x10e0d0c020f100903020108040f060204170105071107090c050409020708040608090606090604020705010902031006050a0b0712030209011202040b0304020a0e090a080906090306090a050d02030307050d05040204020d0c0801 97
    0x181d05201420b0144190618100c500d949500403280f90b040380e0302401c0a0007560303280d0804004510004c0002012035200140c041040485104400b2441108400802c03e65a62200031707101101511440880d03a441071108100600240c1c1104c0d072052002d2400905140d6100c074a04141d800001049510000c0814140400342e8003203d180d034000e618000a003202e007407160205180500c0a00428051500007403080c040c4202504030140c02580502180c4008004c0c01640005241c1c901420303218500130300000481a50301010360301615044489541e6032080c600d0140c0096004040031414800c0e0a80c00a041038903520281004010340350750380d1382d03a10b05441001110a400c0e000328092030411030a0003070340400020215142540030100640d204420320009400b40600c0d020260700d0b1142004004100b4404505c106409100b01d003221065959040709a80340d0004480c0c40000860602154103410001e070090380d0000d0020b40b00501e40481802c602080d00d0500c0320702d50101d07480b0300040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 1648712 1250 1647462 1647469
    0x4050907080d2a0606030206070b0103050708010e0606060d060f1d01060801030807030f03320601020309090a0c09030204020307030c0806010203190806041104060906020c1008011205010e0d0c02 85
    0xb0a0030b645003a1203038607040041107800794112031610356000304100030700c000c214155124a01031074004100c65116006890100d580c580240400c032500d0060180001c1c05070014010301615a042070080d06550351007000f40301c2203401c401031600e100360b201d660002d03d40340c81420707450180c0b80200406283d180f041100100346441a4040810410500700400100741d002080c0c40f00d480d1f0519040c52103841c8444100c02421001d20b0311131182004c9440d1038041c6110035401e1884054400f030a083d0740d5150001a40c4a003e41100745070028000000164024031075401580c414145013058100c1e83e890b0b40114040340c008880f41c40120f0303603a514400c01150012a21940424244011842e2034125821501d048515581030f005100030100420210342d5075802210403107103e040147c6c4c64594a5500400b8800c26200f4140540100444120039040c64540a600c40005854200841c0d20b041d01c03596040e007078043c040e5070655a8030307a07090481d10f044c441b440307a02e1030b25951501c2c04442401007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 1649962 1250 1648712 1648723
    0xb0403030b10050f0c010f06060201020705010608030f070206030703020409050703020a0e030607091403070504090602040302090708010302060a0804030c14010506010909050114120a080c06040c050f150a0309020405090708 97
    0xe944101e89210307500c1d402c664032200b100d12151002c10040c1e00d84012041c1d050141440a011a8169041c0040410305650550203040d410703020f00020b1084584c0c4485050b200d10540b024103500840411030707a809070821100550704002030349401880c1c00da0b1480710004031070301600c248000139000100c4640d41d40e4400e0744c012901008501415071b0b428040005070070080648543c01d251205580900303100c0e070f400e0164400400000d0300a000440c0b00d460050300951090108a11890580c008150780e98424003405042c4e0360b000d8805803a0010100065901c1c480060085082290840d02c600c0001c1608044e0011030b080000041214204100003604011040c1c020b094600c3c60800100000da441080c094031060081c0c4030011542003400c50340c1d08003291100041c1c452400041c020800b42c00c0007451903c41c0e07008815800a050f11201040300740110b0b404256032096105550f0840d5004140050840c11440d0400040c440200d0b40442d05488044594603103c2d0801c42c01000814002d120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 1651212 1250 1649962 1649981
    0x40f0503010203090604061d0a14070608040c0506030406020904021b0f0c030307140f0304060504060201050606040303020c040f020c0d0507060b04090209070804030309150b040606050a020c0103020304020a0905040b040303 97
    0xd43c1107142c4907030a0342d600e0800070700161616440e410080c01851840b0840c0001d140050142c3c2c0b01c10794103042502d41d54a481508581a03c00c10a00041c1948907481130350040d81d0280008110074604410401d42c0d80010b04180c60260f42045480415a6144014003038880c0161120504450840211741000c003848550300081c2c104001e201400d40c0c0c04011281100d900407900c4003503103d8030703109501d06074285002c440030380320014003c12543d801502502c2215410360081c00142d03039030014464640194440200540d002e00380ba100545015040b4094480d1004001030a00041c0241503142800c95644100402c8000440b0320501c4203e02403c04450381c00d403014451000e0380e0b40490825903004144004124500c000301d0308162290300592a540d4026154030840389190800c44014005218810b101c0e0f4036024000070040e0103041618440099600030701140e030084c000640c06581f000f030040382c0c0b000040c2c1000c02c4c0080a0700c1510301850188500e000549003c0c5400303021240c8984 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 1652462 1250 1651212 1651219
    0x601050a14060f0403020301020f0d0606020a03210f020414040f0204030b0f0a090b0f07080702070e07030c050c0f0105071706060301090903030e010908030717010b040504090f08030408040f05 84
    0x1003482075191042000c502114241e0b81140d03680c01450454205010744e81000350700d5400003e000016030800030242c9101c005025080000e166a030300181e076600134585000740031904c0644800802220000a40c0c210b0154070804610b11624031100b2003260301c590400207070160f41c40b4517501181414411011072201c5140218070741401c682311411103243c01007590a4030180030000400d581d04541066828035403002e0b07100c0c028144080c480040a1007129240c00041c0c1c41400241a1480041d41408468107800c8000f83c076200c000046020b010034071120300c207002c020007a8004004041181c40c01202c1c44500006003820080001400c181d1100c0a0990f1310710b00405100b010f94443c0100ca044070002a00000d5088691030140e0141981c0710300400355500e404042000e1000300d0004511503121135466550b812412304038412039920038007908032220f1040c04140003d0400340d0240d078411380110b03080783c031452459071820265802240d084a0007600841e0030000b81035038140350350150000b103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 1653712 1250 1652462 1652479
    0x70504050c0405040e0a0606080d080a02030402010c0209060303090a03120201050106020a030e040c110105070914010201090b010e040602071707020301060501030203010302030a020103050a0608010c0302030609070816050307030b0d0f0203060105 107
    0x1c5404000c0c09140902c501ca1a0360f084200100036081020b2460709510150501016030303185581500c451140c070403e00420203000000d4401d40c403e100301e9124070f90585541d01c0500b41038092009800c4001c0c862609807004002450782ca5984034001303801144151500008054100b00003820359006034404c07001d550105501d940020b4002046001d0500107030b500007481c05906c2c1c0300311454450076104c804035503c2c03e020b106240c0d41c4040c826042d5107042d0080090703000d0180c0121700b242c4c5660000740140070301e00c006000c82401d9032481c0350014040d00015041c00380316110205402d1001003c070b9603903c000a0782c0c104600b000e0003020010603090904600755031454002c00c0e22031040040003810950b07608001504011743d5800070740a004200003c1001d159142c5000e002544150781551040d9500c4000518151043c04400c1c0314149190524652002ca60020380306508003a012000b45615100c82401740c2e1143c00200d041c0d0303400381c2c0c0350b42c0e142e200360b0041c1801d014041c3c04c25802400ba0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 1654962 1250 1653712 1653721
    0x11030108100509030405040603060c090501180303030207050a0506012303030307080627070c030e040203040309030b0a020d0504030801030b07020d02061b0702030102030103080408070f03020108181f0c0207050405 93
    0x4190a264071500c030002061503501c01d0380791030651213030b40c00080d4460f1401d2804414000142e201d4507002c1d00c1c07900c0d2801082d45400c01900c00703000020841d084440200b40500020b880ae4024061441c03041040300e1880303480d660f485040c200c0c00d07000841c01281c42d6508000c3c191840300420034001050700554a5410101070003404440001c0202c0e00404411040800085610518144030404424441002d0401072401400f050b24041f054000400e9107010ba6450b180501c202c1c1d0050354503444841c5001d00e550740301c15400b040140100030169083c8030f00c0c255518a8050103208510075074621101d58110f1900e11100e95003c0e02c0001154021010008441d4000602c981c01100401a10302220311f401041400742c8503e220007034065001000020810400c64054015035400074203031403145846038070400d070042e46440042d00082030007010646501c42c00c644030203107241d42001e907040c510324101d030800e10303015032202100602c2d83c8521250010b40c1c11711034540a480100c405000c1800d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 1656212 1250 1654962 1654979
    0x20901020703020f010210050106030b030c01020c030304090902060409060602010917030601320c03030402030d020d0203070206030a0b06070506060f0d020619020102040e0108030406030b01030204050105070605040c05060d06050301110301 104
    0xc0c1c0d400000d000e495143c3d070f001c40c0c1c1d07030003000651840030407079409010968540c4070050182c03584482041c000d10a150107061190300201d405036140c1c501800450606182c85184409405030300d07010f1b60440010400440d68643c58003580c0050b15507500040703120012072401650121807c001b81d00212402e000b801626a4080060107180711414442c440000621440380300a03c0060a126030a05c0c00068255403d04040050340c440c60084003038410061521900b1381e03c5000320302a250043c1c0080043d5801443c248000d560002d480500000e811080703a800b0032400d0741705642c1600d00350311842c20800e4601c0d01b054880703140742c0b0503100e24000c010310380d010a415019101c1403503030031201c01d0040703007409100f581654010010490b601e90755503541e0200c19182e82c0b041c06000f0000c1d003001082071903540203008840c1201c030103030740311864600a902c680e001030101520445140148200020389552940c010384101c04404600203107052401c8200350071102c1107028811401e0050004020f01074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 1657462 1250 1656212 1656223
    0xa050105151c02040506040b1e120a030f08090309040606020c040b03030a09050108040602090d03050307030501060203040b0301050111010906150f05030705010807050703020a02090406020d20160816050105090d0302090102 97
    0x198140d44c00700306500c40030001006403140c0a5240d80141254400c04090580c2410220039008140da100488950190f5000c0d164242541c002e000320b10002480c00d0f4042c8208a00d9600c541c82100762402e01e03186100150a5800c4c0da401301005900241c880812450144123100e42d07500304a004514044c8241c5001d40b40b0041841b0300c506006942c800102800700c0b5030103d0b21801001040d0b601000e21914010704240c00681e14800040c2c0f0340302c00801c805d8000002c41d002e5807010302d07800e0704680c606401100c003e6005a6490041c0d520782041100140c200e0190500400300b03000c1d4040002d00b418001d11034400a0751089200354070078030040002d660000211604501680361080e0f5401190a083e4946400058000d401112030000c010030b0042690207801c00c4d000700034081c001d142d18544030351b000b52120f4060741240c00040103101c40c201031003030030040c0040c0725954050800b204440d49c9030020000b13000a0320565110004c200c10001c007400040d58980075410218103001e2000d000039330317a9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 1658712 1250 1657462 1657519
    0x3150302131515020303190e0a02060702040e01060602010b01020c03150109090f050a050114070e09061201060503070b0c070501050f040902031905040515060f010c060506040209030a05010515 84
    0x541d0b00d554101c0404100050203001c0c000c0c0350181200088100030080d035a5208a07940718034850b003001c81e4a42060580034010200d401600148404100c903000c01540794030079103080340e02586d100151025448203020307090050486400000700030074441d0000e8209a403540c206071103074000100074041080341c03407409412350311316400001301e080552401d00381c241c0640b440604541b150794442d408203c0c05410170403420002000c0600c003910b50220030f407801100341c3d428a0340640b8036400590b007402d100a0b100c8004110f8000422015920b4000c41e00b0b007001500030309100e85000402d884640300421480380100340c2881c14900e00b18507580d0300c028a0185008810466400002260394442400c09801030b28048040410544c00d01c6c2c501036664047da030840c4460307512402e0004481c0c1c580303680091810101a10340b1040c0404543e200c00043c803006107240d61003a800d2007074000300e4804001c1c0444007445030000185038104040300c9075085074906540d6104014554940b01040c000b40e1b21100c81 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 1659962 1250 1658712 1658749
    0x30c010f050d1a030a0501020d11030106051903061205030304020307080d08010902070312110304060c030e0c010c0c0b04030c0305060c0306130b01020109080d06090605060304030807110a02060406050a03150302 92
    0x100ca601480f2210100e0040b220f943d152040541003002d011040d4024484100d02500400c09000c19034451040d5010902c2010085141409000c10329000d040840181080c140b5000a99030346940401c140180d907a1426141c5902c007004100c210b040802c81800039015410051101050800c401810702e030050199440003034001c1240c2040601071082c0001c2c0c41c000d40010b00100f00300780254556600101e80545440d41408045114a4000d1181200701038000b40034007501c4000c031005486081308080220b0302076100c060300080140c110409480a10310860441008614504140349072000103409601d15031010420711007143d03143c1403d0280b00da4441404501c0c002c409005038010440300c0c42c00b520030030300041d111315400c0203940000705030f0303136180b10410029843e04140700b000d000460340200420300801c04500c03c02c1c0144818080c1e45940800c484280390140d000c204070b40c010341e1048000c100c000c140d00030b9441c2c01d8000c1c0c440b0107003413060184401d031441e00090540c60318441026030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 1661212 1250 1659962 1659971
    0x40b01030320060109020703031503020f04091403070b1008010e031605100501060201060501030c02011a040e070312050403020901060c0506010b0a051e04030b010608010b04050616060504030c02030c010f050d 91
    0x4410a070308024441980001c0b05851444d03075904680e40107541702d40c1c0100c000070f00c5e1a4040c06185007002d203004c00d032a0080c10340002d04048509000080178011015556000d98403544032508004000601600e8410700d00d0744004e040c0514403200241c2c603600035010503410075101d81c41d295000070580385c00900311aa0715a01d510181003442c10005041e0138428124100400464510b8054000904858003a0f80401014642d4002282250400004022a00d514100502c8035240640191300e90702d4055040d500240c1c3c0d640e403400368141c48402c0030400300d10040307410425841c006402c907005200701c0c00c0c01c16060b0082e0b0380c2c0949501c014001da800100011500046691182042d101d803c4440441c840b502d00001d1040e0845070054441140c07410602e03800882c6040c410480380d4101e132100061300342424105420880f8940085d01c00c1c2c00b00358403110700440401c0d454010107000d1806610ba00e4856000d0380149420501c03101d01413414003406011032643c466110045400c2401880400a07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 1662462 1250 1661212 1661237
    0x3030a050706020a050405120703030807030b0607060c0e0303030a0e01060e01080a150608030c030408070b0903030d020306030102070c180509120403020906030c060a05040f0807051003020327030703080906040b010303 95
    0x451902a131f030441500018210324000030504006035220580e0b0003621001007694580000303c0035503918503200d0b03801c007005014003400034100c0c0e040f8801e080d0b403e080699044050902280c61608201d410401c01515651142480f00c0c017882040042d0190140f584035540c14800d1450303445205044c01050500c100344071203661aa25481a0064034401d02669a05d08800c50507641c0d0f03810038040c900442c051180d002a0301c2d83c044003161001c09000d0095410840041102002034000800c900e8165408004040020b100511007070080c0c0962080c00340821000c4002004441d8010648809036005c10003243c6811089400d0f030702140d81c1103e400900d0f0341e415000c81e080c52883c41d0380f55040b00011400d030010f0f94000e4098800d0300c00c814500102d043c1c1d60140c0e507540d500607200352600310b0081c0750890360262094008590110540c510203170144403c401c09121720b001156101402d410129a02d400c06a01c041000d400c99841300081066083c50380392610b8500061000030280b00c0e07d0512031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 1663712 1250 1662462 1662467
    0x80d06030503031f050a050f0105070302100207031e030501030b010b0903010608031602011107060507080904091502090f0108010305070e04050a060501030f0b0109020307020d03020f07050102030109090204050603030a050706020a 100
    0x8095540101601e803641801d142c800d2003510100301d0000303180001c04c0040340c2d60074981d203020b0031294014203419104024200559042d4051070003502180540081011a00192700050901a1107640d4130108080d10700e003020125101c04484108050034480100081500761980606580c00c88105990741e200b0200024010031030341e4800c1120b80008140b10380954013104202c0c1c40c05000380ca400c01183c560020b016110002c601512002c070341e0a00c80d94022071510806061a000301410000d9012442c1c7c842102c03032035400402c104c446400086030409814880c06c180843e180a09000348954119034419407207580d280108070001c0b11410014050120400c89800c100350400800c21039541c584c00c4c0a074114005c903800b920402c00d44c40c00028522041d10803a4480c40180d8041c010180c8bc503075046000e94030400003c1d018120030b118450100f5020320045000700100718000400e042d00c0d105110550750010200d5101e5001030020100c6070390000c04403900b00303511103401661041c0c2c14609 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 1664962 1250 1663712 1663721
    0x90703080a0e091003050c0102030408060703020d1d01050a0e0109031d030102040315140106050307050a111f020409050c340b09060405100204060c030810030b07020303180a02060304080d 82
    0x2d078411414000c4c044a8134502c0d1907241502d0249066600a180e40c4006a83d40d00c203a2103400c0060b40082c0001d08440e200340d001d01415205040085426880f2104203c10044075000d000d01c1d41e50b4500622403481c1c12446030342101410700b4001d002c012442e4030050070032508440034250048a8480f0070382d180c0d070f0a40c11203002d541d112904030341c001800360400000b445100c204203610300c06113001280c8917000c1c0003075070712030399155072603621b01800d443c002c440007050a40003412030300c03c203201039040c4801d10740784813a440d0f0f6640d00140c60b0b61030300c411001a100c1c058079a0104890410203005d0484500307143e02074400700b0101d1610f0103070780c0b208018016604150702420403005001400f07499900443c070300e40100d009004070f8a03581e014901e95412480f683c4920004905012111800a0b008000142d4000400c040050b41c60350350303884148880200b1245600141c000008010700181c0c506400008803040d40300a01c0055001d41c0400d9891101410103005001c2c00320300700754403141e141c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 1666212 1250 1664962 1664987
    0x904050c0c01050c0d0606080f0a0902010908030c030c0105010506040506040e07021c0302180406050a05010c02040e01020301030f0201020f070608070503270d0311030408070605070c060603030806010809010203090703080a 97
    0x200100e2804411310720b120b811440119210320b060810000b4424419621103024104c490b6a02c865622440805070003003a1a4408030305208020b9000142c021051014020004038000515921030480308144e0843d001608054441c1c0004d010900c12519007000f40c07025201155407145440d1500e0174142d240200b407400c440300c0304142000c8004490f0381a005403080800702c0c80201d03242c004480030041a1543c6000320340d013140f103084040215611031300d01c0e500b1160014000103003541030b900c006ca00f0380c0c1c000d800507150715010f01c503041c0465a040010035207802007000504281340c2422401404c11402500c15010404040045490400d1210410f0b08605210180c04923841c2c0b81416180c482506c0c03000140424034100045040441e07160480e4840d540c07006000d45046010394683c0300800c0003030141c20403c00d07a000c0c5840060a103110341360203035000391182c04003850036400051003140c0c0207050034880e034014000c1c801b0082002031024180c17680110b03040c0d1170306401c14088031140040035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 1667462 1250 1666212 1666237
    0x90806070201090308060d0201020c04050a02040e0103050307020a051002061b0c0102071104180203070302060d09050a06020702030105070c0201081b0f040605040f0905040206040603020f09040204030302030d050609060102030904050c 102
    0x1018800c2454055114209452103501c030220203a69982c2007080c940b00c040707c0a8003681024180e21103e241950181d544052403200044c02c00d902c0f00e1020403c0c4001360000c4407030b40c1c40050000d0561500101c1d80e0000d11040758600742d034021805009450300340c00f80071400c1c00710f00c0024154140b800c200a448440c0340010013192521840d0405921099607405850301403850302c101e0040080900040c0c60800d60068005c0c14102c4c61035080c00310551081300401042e69941c2400340c0010802d0104960f414041c110150311010640105421190040e1940c41440300306180d03100141d0700500041e9100d80e22030740c10f10450011404403855442000d140c015040340000300400d035150000c0103441540c5103182e40c14160f07511340580104680003613a01030345c081070601040044a2090f001006102c0000c0901030030051030002280680c0c03c150821400740c3c2011400103964443d030320595078090301c1200c0e41c04007800c003800041e40701c0c401c0d455418044e50300c43c000960701c2c2070101c2c11981c90b071018a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 1668712 1250 1667462 1667473
    0x702060313020f010905010c03110106090204030b0103030906051809070c020303030117060609071e020106030c030b040b06040510050103020708090904030206040302060f010501020c0103090609020d060203010503070501090e04030e010908 104
    0x25000001d584904030101d11500c0c0e080805802c079446a48584240c2e81e060b15800d49117500744e24281d40a84001004000c10341d294200464044960300203040118800c4050380007075415440e0103040540c0303603004501045814000e0760764081302c1c04181001240e055402640a860341c500486038260f80610283d0540320001c00052100d41703400200c2481c100d04425604140c45000400c4020302042c0e0310403000802c1041040005486505006d4910000303000028040743e80741c4d55000c1c8604c0b29442139410f03001c0c1d14104010300c43e11601c10307039101c03100300d03020012454a0003100341591842d004841c1010341c00301c1c0803400c12001000700e500c4c008000b40104075134640340c42c00079030300d0500b100e04600600581020075400c0e00110b2140e07060760b0701600501003d42000004400800700701405581d16911001c0c0040946c803407840408c401c0303014030f00150303803527060009040c0b0308105944014100500c0700d10410051016421283d0455450b181c071440c10a00000100c4919549070814000e60040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 1669962 1250 1668712 1668721
    0x7020a0806070201110702030616020703050109060203070f05120106050f0405040e01020c0c090103050604030e040f02030a09020406050a030203030304020904080708030703090201030f060b16060e0708010b03070b070f06090807020603 102
    0x141d0a00c26001e6034024080d46240d100c5410490040d188001d4065100c60040351003641c03074001c00c884050340b6104803000e5036a25258542503607184c1500f555040c0d03000090040f03d0303070b10004907030701540103050062920b6521170038207111110520602c802c108010400e8210b2902d12030441c1e00401e0000c1040c82100e1403004494000d40c032400503103000c2c0c80380c03000c082d40508121114034100c0350480050b04045c0c1d0781d51019200440c0303914440354001e42d2200c6620740c07107143d8400346000e113181c20b80000e00030015106010446000d41c200c00d200b00321003502080142d42c000b04030780d40180c1c10380b041800c5484a01d411a4140210f40340181802c501208001000b94182d00441049000b660188070104001032124111022400365801409080018414a074600c0103207001140c8100350014035000c2d0000030303c4c24084290401400d0365120b00c101c004a1900304000e102078201d02d5030f000e25221841d40c1c0d43e5000200c0d2003006211503190010882441b0804065a03003060b005420541e803840c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 1671212 1250 1669962 1669979
    0xd0b061902060105040f0b03060a020a020a061d0606030f0c04020c030c010204030f0b0a09030f0e0102070302030d09050102010509010204080601060f0e03010204140306070c0803061c0f06051012020f011407020a 92
    0x3003400b684d80190702c5d210404100700100d00400c0c0c100b0b080500900b038151100c15256003e07601c000c14200135442810504070001d0510310031a01c0e07d5294041950040c40f0708618181400d0000d0240e0b807007035200c9080c000355124046402e26001c98111001030b5a4000c01e082c0760301310700541107003042030351000c60004180035000c1003c5002030311035100032442e6a10380150400321750428601500040c1c210008210042c0a820b5802c0c54007014012120100c0d80e0341d00180c074045111031031100003410341c18100700390350302400703402e07040a41e01000354142418003418a41d1254140b01e030303204000f088001d80355101c0c0610912480e001001d0000c1d55111b80320030111142c1c5401c2200b26009209400000d03046034882e0040515843c0e000340020701d90b403110000c100302402101c081c0c81182c00c607508000005408a0b890205ea02d105640101341880e100000303040ea540941d00160318151010500c8006036255880c0b10004035090a2180e01102992540c0c0b03024026004002d4000e502840301094445 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 1672462 1250 1671212 1671223
    0x80106020609010e06011401030f0f0e0c0a23060d0203010806070e03030703080703113f0c09040207030905040e0106050a09021c020307020f0604030305150a050102030d0b061902 78
    0x4660340c007100c09a44a008800b400c94014610002031307a040180148080b00042c4040001e10b01d05140110704c5072004034101e011154048024501581d0301e110300c03c41000e09000030007590100301d4a00110500d4803841c00d00010509084034800c0c1c009561034a0540d81d003906540a1076078804c021505da40c1c40e4248079688081c141d0b5020041501c0043c82c50607494000103d60f030302903060b5102d1010780c888003c15009019000401801080c0c244041450a001d2410340111240c40c1003c1c40c040021410320310011140407100381401001032000c005151109004a695140303040d100140d0307440c00303030608a845500300d812450b802401d00121900c132003015089801559400c9400946296488089000302c0c840e10250304c0302000c103c0000740030b499159001d10750100b51801035071407041c0700e60013260034410200c2d01100401c4d5a0700511a03100401012140f003c06e0a5410103005d60030000040e54a000d0810300d40111619038072200f485031035000030703202c0a100100c1d420b8005001004040d403210b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 1673712 1250 1672462 1672469
    0x3050402031006031101120b030a080403020a0e0403050f0304020402130b0a08010f060e010c0204020f030c04090501080d050306100201060506030a02040806061906080901022a060601030b010219020a0302060301060801 95
    0x1d1080000c40402c0300520300c20101100d60201000710034040e40801560301411802081142560313070202211161018820b09030607a01c1045141e0b03440f4110b01c10080345081c0ca40107850811002c00c00c103c00a5040400c441c444403100c00b01549075030303403031000030003074460701500d2685000d02d81c80005002008002511403200c0c075442c0c80d84030f681c0702c003901c6c9401c0c4518401d10300014540b1403070410300d500034050040414000780c000b5160203040e81001181c0d50081e1120107403075000003002c2002040901c11070b0302500443d005845003003a414002441408003030141031042c0c9990020840560007544400001c1c14003510b1107840389016204400290800c0c410350380a0701941000071081c0c5402e881c4200c0e140181050154030b58100503040b100f44000402d510044d40d802c00400000800788030307080d0111a561a690310348421800a030508000010b042241418142043d07001c1e241c1e00403580c1001c001c1401c011902108480c000505901c0365684080d4000d180040081030341c0e9849102d180c1039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 1674962 1250 1673712 1673719
    0x3020301090b010305060102060601140d020a050901020d020f0a080903030705060103030302090109080a0f06020a02150a090c05090609010519030b09010203090d11030703120905010e01050403020d14040504020702010513030303050402 102
    0x100301a42d00150141e480c1280c0c0140140c0041001980f03a602403a00e0605078061000b019050071102d4003960304a9200e400300c080455070101d0b960f42039607410011075030790352064405001911040c040c0142e448100303001c010400000840d50381d206031403c0040e0350b0303c2608042200c4095a480c2005402980030000711800100300c403001203500d48000641c0e000c0c2c640e015402074200d0b9225180e02000750052000350085000e2202e0310700d000c14007402d81e036001e110402d8002071030452900d0100041581503028030701a411040400001e684d90550700e9045440030b4489d0440c600d00035044070700c4aa2160801068441c2003401c0c0203200e14158040c61140011000b26162000c1c40304080e142d000020208540c1a40200000e40001c0d105841c0b107100407041e40b03004602c61045590701400e540d200c00c5131890f00da55075400c0105240d8104161045403040341026684694a11034080d013510032802120b0040760002802411640b0803812070700500d07504503104038201d80328a0024041c1000740c030260b22 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 1676212 1250 1674962 1674971
    0x120706090b0703090b18031c0e0601080606010210050702060403031d030406080f0105010801030206070602070309150302070309050105031b160206030f0907050405060603070804020307150207080115030803010b070804050d030302030109 103
    0xb03e035604810406c4500030620020b50800015186070441422010040c1f00080e40f22461440f0101c420003c0b680a40480b00280105107030001c0024a0600312280b80100380e420441404100d0340c0209200e600150507190120301c0c82e40078000c1414154803042048142c1c4400103001800c5540300d8040c41c01211030b20307040e546a0340e0b00c800450300c4060a02010754040302c01c000a00c000f4010313500401840b441b904040784856a034140d02d0603404d207402c4002001c20780004850040650003161940500401d003845411410000c4986001c0700c00f055040c01e2541c400180d0443c001c601540300c82c01c4a0b0700424035aa60300c1c00c241d5680e0710705016614040c2d240b164082c08900d80c9020302a0a1049101030712080c115a10010304079118000030304240c0c0c060044040c0400c0054500004e90741d007201c00d070000c1801501c2c20031900c1c04c5800c2c46201c2d00c100c003941e0400780005004102120f045400c1000259100c1c8181d0400d150507200300d9214540c0008440f0180d01090f030160041e50480700206c80802 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 1677462 1250 1676212 1676221
    0x2010b12010203042a0302030304031202010e0111040501030c020f06040c03120503060904060504080c060901020405100203070f06020912010c0c06050601030506030c04050910020c01090b07020a05120706090b0703090b 95
    0x2400e034002910300a00464651402c15681758100c81032001002e1500848a0965034940100381107510580080d140300340c000300c08000058090140075205080c4100030083c4201c04101003a080c0503d01a650405481c0ca1011400601c20440311030340200d82416661941414501901350108610041f50703803054950a07200400c2c00382e01541c1c03080002814011171956903599400045c500208111441e19003400110681c4a00f004503a20030344203074000581d00d40c1820100640c80f40314074515011940100a000c000a180404600010b45e101c0d03400f50f00e0310075040004468800d00140c0b500558604504042000d80c0244030b124510b000b1380b02000f650300e40c0310044094a10848000b80c041d40010b0310400c0909042d03008640c000090703419682181c2e4004144406c0e0f0344500b4002107180c2d110f1002d0000d000c0d419100729040046030005084111080d6541512002040070b0f1000c041e04c0410f070802845119080700050f40ea002c0103940584c80c09010180081846100544604100c1740025 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 1678712 1250 1677462 1677499
    0x1060b0307020304030809060705010c030905060c16020f03010605090702010606030501090c05090906010504090e0109020909010902010f03050402060d050a1506050a05120a0204030f05030307020f0312130203070f0602010b 97
    0x9074012440c0781d02840c50305043d925000d0301a440490103030b411500801c00000481d80c288a800d070042e1866501290102c840e083c4685495005810b0a44d028420400031012887c0ca58801031016070650307181807005c80704800640100a154400340c0c0100c91a03040010fa1981980400d00b550115101001240d0301e9a06920860300102080780220b0020800c8039850b10381b0000942c1e1000e01403511502d81070715260b40354240c1d10070981d461201ea449124680440c6444413019a100689000800150030945c0000380583c1c0c9190380e5005055844010500307544500b030445e21140360001081c849401c060710040001e241407184024550404071010031414070030800c8841692080c0c3e0b9550502c1c1e01038492208140002c1c09001201c0e6081000100262407590111401d500480240d034580c0307412480a0304040c0b09103039000c00f40d0801c2200380c0004827401e0300c1c0c0c0d800c035041c40c0018101160390f1012a1505d100c54001d0703915075414000004181b503054002005042d02511800410090b01d21807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 1679962 1250 1678712 1678717
    0x18051009020a0b0714030408010c030b03190b040302010605030604030903021e03060a0b030106080d11060a0902030d0302030403030e0a05070f0806040506010b09010c0804080709050f0f0103020103050702031e030105010201060b 99
    0x7075025001d81020454812520302802c2d40c0e0340205c000b54008006051000d1950740254050f207042d94641a110110540511504010f032106401411840501c214420302c03500c29400d00030201c024940c04070341858401d50003103004c1c10000c0c04561941c101810007400d4030b01c45110892046126140b49569009641c500390103002c0080d00801c215121072559801401246180360b801d5076a801002134541000c105d814103404030341d01d410b00610503000d452401d002d0010080c1202c40d04040ca6200140c6000078190703a016114030700183ca03170300d641c5403c801400b542ca61243c1c007840b5415821090142c0460020308603032190b0400002c40d41d452484984810007240d02070030580110b401000b24400040081c40102014905911190741d1581c42c010950415044944140e0240b642480080050f2180076040000d000415145241c940604080c80c0c5050100030304064440300420352a5001308107a030301400c6e100c109015041d00315032600229030024400d060040d0f00b042000902003854004 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 1681212 1250 1679962 1679981
    0x106030b0904030f030b0d0609060e030a020a02060310050603040605060a0801090503040909110303040f06020d0c02030d030b0109090f0209040507030c0206011202010212030108031c0501060909050901060504180510 94
    0x85005a0300c585041c4c822104034200502070545441c0948180d9030b0b801c4032204803d11130380001454411505041d401c942c2c441e07903030300c150f540b081008030304d000e80001e003070000f01741d04440303581d0340c0c0e514081c15880902c07041d03000c1e61704070102200380820007403030b034106500c516016960049030b1941d50031202d080e51000c080250007070f0000c01c030030f102408183e00181c5850740105480c40401d000480860300c0d6034403d9002c0f807603d4050391400d11001d9818040340100c4a1140b9080504400700d4000a03154400040140c0a2550b10b0780b13a06902d9014030382c4000181448a020894905001c8014000c0d500c00d440851140c1c3c5000300264103280a803140002d440c0044d8000c0191346c3c01c1450410104c11410350680c1544121100d03901d66104050003903001c1d000c00c9002d9a00c8510310580055009007802d100e0115070b05040051100b943c0c0312800c40101d400088000c1030302d440702541a4014005500019080707410300c885161138140c0308000c41505072042003142c401c2d0b610201040d0417652181c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 1682462 1250 1681212 1681219
    0x10305060a05010e0d05030405030a0f0b0903030c0301060f0e0a080a0204050a060b0f0d09080d0c02060601020109080a050a20010203040c0905010509010b030603010f0c0206101706040311070e07090504050106030b 93
    0x4c103400b1490625070801c0341024814801c4074a4151500c0000c1d180c00507901d802c613101c3d00c0c442144420094a03056594110140744000e41c19030038030907280c00e500d0205000703050800510000340301d0150320441406250103c003070302040321281c441d4030207602c807001100184e008038100f501142e554280ba100310301c22200341c03954440c100400c0d42c04590700b40d8400c00f0a901c800343c4813544600400c140344010209583e00c00d400141d101a100008ae007807070f0004044a040da4034180b032a8010070581c008841d030194052901c140d495a40d040b080d200c10040454076002003500400f9403c1d241c6055000707602690140880d002200e45da002d01405464007405a990001005001040b0541c1c00c60044e60b0030003001400030424050062625007101c160245440040c7e0090080c00010f505980e884170140c505030fa401180c03088a0a15180d40d8840504005c08001d0841e81070500213070103004000c041c000d00303181a0351504012000070206c1ea62401418030403843c0100014006000e84111902d000c0d010303 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 1683712 1250 1682462 1682477
    0x60908070e0603030f030f06040e0f0a03030b01110f030c07150207030b06040603051b1c05070b0702030102040803040612060e090d0c050102090418120206040b01031217040303020702010305060a0501 87
    0x408071031a403039809009640c05210500c8081110440702001d94030640807007050f079903580b9218040105403840c041e1040d2140e0001030f000e001c3d00764017048003409030b42c142c02d0204400c0c02c0360b00102d444070106000d00603039028203180341c00c2d28580403006140213003007402190006900c94451032461000b020301d0b0005a07128150400010364020b4641d6440800200700090302680ca407115030428005a4a81980d056001105412850040b90340e251100b80f000078600c00000640d260340d507560b988e0040c0c0c0c00d0148041004803c6507002d404846c0604a150156620f0310359410002d0090419005214242c0341089004511481402d051510605000000302040c4401340c8007501c1210032003000303440b80e540800c007072120380e02c8a0003042210751810168210a03003141c105064200402400081150028401d06c004500800c3c61079055075044482e00c0030103440c0c250305540140c03c207141c120351520600300708820305402d503002d130035480d00070380303084c8841c3e580d020070804030003550b001d01800701c0c20f171 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 1684962 1250 1683712 1683719
    0x307030b0709120302030309070e060604030b040f050106061d010807080606030a0b040219090506040312050a02010204030c0605030103120801150e01030608100615030b1f17010b1306090807 83
    0x20000c10607001045400c001288680b1441c031903000030a00407064015900010510131200d900708100402000c3d01d1b180da4100c3c3c1008400203284d03100360310018000c90021808581800700301c10840c3d040c00d5000000300801d90392207102502030444517420304898000194580c3d8254010b01d00e49100c1c1e1799955982600d079407501d0802c00203410203081d40400f0b80d500e1500f0f441d50744440c0f00600140344114600c0c107020740c103024004e200b2002038001c13500406003480b04000181c5044695400701105040c56500c960119004900a01a940c030282400800c0c0c02c000030896000350086050340d01655401003041c80080301540c50071003e1007001c981000303003804e52005510880f140785000405243c00b00e20a032b0340364803207841c0069004510003280d075560701c00c002048072007859040c0000141030a02c804402c400000301c4185100045102c298410004002c1e261f1140c0d56400c2c21400e0011285c0c2956190ba0909480b41c00ca0740f0070810442d040304010403401e02564885044031103284c01003a04504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 1686212 1250 1684962 1684973
    0x60109050d030c020a03030207051302090a060e0607050109080307080603010c020601050f010203040e090102030a1b05090405040c030803090a02010207050102010603020604091d030a0c0201120506010e040911030102070305030a060e06030703 105
    0x601c284254104600001c015005a481c1740488000f18001d41c001c0426500f01002c01c80001c1c507008006090a20402c1a40140d849221120301110803904048007001c1c0800046101c0b82720b200802841c0b5442c0c442d05804210440c000385000d0355541d52a1052503448405050803910519610340c0942d00c2200104014071f030004800d1050081071054908195580c2242c0d544034106076203019280c3d40100400514108503c14040c0700c0008428600028207130b600701401ea1b10595424500603034507400090309200724491580000c65000d0383c000c3e50f0340303807941c4a5921388400380c030101e006008080300050a90302c140550004e503500100f034a0310301460501c13220001c1c100c440321403100f4201c100f00111118810f0024041180701c0d03031035a0310401150f10006141c0c0c01801c4c0103140c22441c0c2010b00c14241d038448221904a003054400090341922414000b80c0081c0c44e6494542c076600020300d1008250340513001c0c3d03000ba4000d00c130130b0004030340328000617101240c00c0f03825580551140d2010008544c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 1687462 1250 1686212 1686229
    0x605090c0912010f0e0604110402040b04151b030203030703060506030c0d0209030c0d05030c0609031207030c02160f0314010207030203030705031305070306020a080a06030c050f03070b0705010605100806010905 92
    0x2c4000b00000b907408450710f804800e80b0010b149101940c3c1100c002c000910050b9180c501060b18111411803405050103001c1e211405503001d8070801840580000c00700d68050740794044200303501065450049040c0c5030003035890b80212490380000e810004000b501d801c0401c141c901a8040c030208a00705181024a6802500414403d40c1d142c400d0882d040003035101c0740c000500700e42c0a00095662820004180380c544540070341142e84541c070402110381840c0070015213541040eaa0304d004951049078000c12441c2c0058001c0f0b8a1172074001e00c000051118050034180104c81c070801c09030b0109080100c00070b080307005a00005c0c0250b002000001c03003081c40358009550060840744082140d9000f91a01460116182c10445003507500040c1c02c1e41c0c0315044805039030320400060041c4000c0381555100d16a5075541e20900340150600030140449582c28460f00c0054900844840d85035103490402502800442c4a04c078003400910022005d464031503050b441c81041b041e1500c0356900d150105220014 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 1688712 1250 1687462 1687489
    0xe03070807091e020406030b0316030f11060d0e0f010c0801030b06010503060a08010903030906060503060403020a0b0a02040b0315040b0307060e190302030303040b0108010b0109051e01030207050307050604060605090c09 96
    0x2182100801c0e03c03d2462032024101030700076503078000341411002c0141850729100102c0d15158982103001000000e10350310b40c1c00346081d1710100002140070307000b000c18924082c25001e2111b16041a12030355115100042c035119107540c17280284000c21a480065403200c90a00000d481c207401a00010071039401000115044000900001c0c2d00350369600d0b81a0841d4920942140020340340d800301e2007402681c0c00b46001912084000c1e0010f8245554065550001d40c24028900c106150008442d12059810364005020780b80303000ea60703898007101d81c8001e1100112070b14400ca142810030751990400043c44015150a44c0700e000c4401800800c1100b81807407030794070b0300c1c520001c104c020005840601c0558000c070304c100c107801099410b044905081d03889c1200214104100b5400c00c210b03a0756015181c411406101103a81118a40040101d0280c03144817006852803000042d4075003005000102039208501a0004024040e29a000c00c510940160b4085e01c1804052018031a41d107088601c100c0c0702d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 1689962 1250 1688712 1688741
    0x70c05151201030501020706060b091804030203090a0303021501090c05031801090609031707031109010507050c10050705120306010f1b02130207020916050301150203040305030d020a0e0307080709 86
    0x502000000e804504507003604100c1e0f6917500454070b1307003c000141c0140009005481e5042e070030924030101048000d0f01048962031729640501c04101494028401c46161030f20103481020015240d04029540364811092503124000301d200006030798071548142d0010144507030300c1626544032b4410101010036200c100c400c29550301c0b40c1ca070001030300c00d1140e01c40f018802d40324260010f5a40c2da50884241000302440281420841840b0040400c242256400d42c403d007886134448000f400c08034170f403130f003644016608110150a06040d403a0000080d1419a100c1c10441e2581e10350b070070840c807080c00709880d6903000c9013105c0880c900d030714061a5003032808184503004000c281c03c1500020920121120741307a83d00b940c0010700f1000d5060400046500003044100c0302141140140c00901c28403051061040324201e200070034007510b100340100d40c0295004000c0b00e440e801c0a000c050000d501c020850f101080c00c0705e0380c2142c0f6040104030f46040750209005002030a01d000440300c0688100c1d01100d2a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 1691212 1250 1689962 1689967
    0x30302040f0e0a0b0306010303090909050a050d1110090f0201080a0e010c0906110102030402090f0603030c010c05040512150403030e030f040f0302030d05070b01050103090201111009020108010605070c0515 90
    0x1c0c40440c5000440040001d024482043e0800e2079215084400d000040c0d80250014401880801e80040c07403d001c076564102e001400070300e9410054204800c00070014030500641100e910415808050b1103071209011069403103512519802c00d023201c0007a600242024440384591001d58010740c4007691013818007001181000715101c01c10700715a09108410b0110341c800038140802640100b25016075840c44000318914107040d00061080d03d0000d00d06020358462100180031070b18240700350b810f0402024005e00c013900c87c1038030140113600507001d1280154070801c0191050a0001040b11001032034840c00482a2a203840841c094982c4551004861004110200d036400c003210041c402001d1940c24071540505500c1014140000c4a0501c0200141440102c0221311800300c0030341110024200000c84221600c0141c940c1100c541701029140505840712000300c8458001c2e80d18203100b680c070302c0100d80e2508029115405030a002801c400c61003001031200b42001c03114041011804203c250 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 1692462 1250 1691212 1691219
    0xf060a03060e0604030f1416050f0303010306020702040507030605010f080a0605030a03020f160303050a0e010201060302060309100606051602040b06070605090d030e010204060e090a060302030105070905130903020a02060703030204 101
    0x2511030810038041a90301c500c3c1000240740d441315611901450340c0c40d20544100407148050b03058081c04100030140e0340b00441c3c0104000b010001c01442203001020f680c0c8030340e92030600701c009400c0401c0607402030b402c00c0006800e0621070711902e410707154143c40d440c1040d410742c4001c030b94038a0000e204680d03071941d5000201710341d9030410601d152284030354000c000c500070343c003115810210384000f80030703d550503510300b80300084d04134050368841d4259240030040464100c1c0100c2c091b182692001e07401800002c00d1002044d0041424a82041024414852035655002c200c815110704001350301d40c0c0d04140b900100500d010f800101e1030303082c0148610704080d0152545003c803801980c240c1c289502c802c001a9100d43c05000d02040b00707038150021403c00d803510502415009000b0101803049034408000740c2c80300071030f034040d41c06190040c008001920302400301030448030281c0510307841759400e03540c030002d01201401500c3c50664168041d0419a2041d4284081600211800c900781034082c040032 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 1693712 1250 1692462 1692473
    0x30c090c050f07050c090a0c0201060503010504030c02010c0602040905041a06010819020705010209030d0201020918070801140d05010903080a0f0603080405010f050c060403090501120e0706050306060702060d020414030a0b0f060a03 101
    0x11806001f25040015941d01c140001a0854125070f00071400b0764140000c0001198100c0010141b054080c200503140081e9031510a0007885140c001c04506071501c8184010300484403420340003d9041e054003021629030000555043e00200c480400ca03d40142c82148449130036000b0f02400d5202d0000036040429450001c2c2c10701c843c0650080050303501007030062103860b000004600c00184d690b410405402c0c004402003503a80140a1481d061006001400003500c40c494200b41040c1c00c4802001480050300d0000e08141d02925001407403428000003040c50103161007410204c07584a00f00c549440d00d00401514005091042002409000c3c0844c00c00c129050018511030781c4255112461141840005041c81d62107891b1243d240d860b0444600e40d101000901d9015283e950802907101e640c0c0300300298040c0314510700250400e03000305903411100c1c0250050400c0c5d4075104410307546030102c00d0600d0340e1121020006400d00500c6004900820003003010303650449005412408540c0d100e8441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 1694962 1250 1693712 1693729
    0x60a1a061206040606090e070305060f0603100303080604110d09020d0b0906040302120901020a0f08040503010c08010905090c03030304030503070302040906031103010f0b0102120f070b0f01030c090c050f07050c 92
    0x1d450000e460602005400d1800c2d20400010340300c1802c2a2000d40e0812000c044c00c480c0040040040c03550304c4002c102aa039a8044002480200030500c641e80d150050f00c1000d410304500c011408138001c14049980d070f1515000700b0203002884c8200b2810501d8030074858000e016032550990b04510441c0080c030204114150152042130120300521883c1094134000b03207044108d100b5060121000e0201275800d030b3740400c0c406a026000b00f68000340f81458140308004c0d100300c1d48016850340c41d0a410424075600304c331130301e41200c100f131600308415030342c00041d15101c041a0310225450b820070400600028003900165802195a150043c1400d0b00c0390310507030441d011500242c520448d90b20a8a14030b1909000d00e01503aa40900d09000f10790680c00080c0d0b40c0c00301c0c82003281704440003060200d206013106083d980100e03001421101a4180066001266407085c0010740344450000c0700407510a550b4050b82d400211555035480c035042110b80e480380349401c042c400320303440e003d070440002c07113030755060301 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 1696212 1250 1694962 1694977
    0x203090304030c06020d090509061203030a060e1008070608090304080304060801080105070e06030a090501090609060b030d0801080607050901020a05011a010306050d02030c0d0c090e030702040c0809060a1a06 91
    0x356500c03400c50411a0500481d07900c01d03021540401d95a10324154030824510032220251a541030f1070b222000002c05507a44000d000b07441c0c0c4004420002070343d86d42d4001074101d402140c07504841d51140e000d903411805d2580100540b952201a0400c030040c812241d4543c0708500c1c40c00d8900701622502418110781c00356000000241e0b0410040c05044005e200791030b08018241484440311700048041041400010a5038120726955411002441000c0d0050000303582d020300100695441890240d004003025800c440c082c0c411450b420096501802d40503060340c841000801c1503a882020460b490740c4209000d504500400f4180c1c400070714240100941c81d200e404891941c1c00d80d200005080310010380c03000c0d1107410000074110158401207243c0658500030b482501000700d0606050781145099489001a1458914080014031001c80a030155510865090280b12100b0800300c404803010741e99410150000d01c08604030820a50010030019079940d10112102e20200008900740c01014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 1697462 1250 1696212 1696231
    0x703050103110301020306030d03020d02040504020d0207061103090705150c030304030206010618030209041e0209011805240907020111041404060501030c020a030305040f0204060801020d0b030f03070b040c05040203 94
    0x2401441000155048449090419802182545446400079039580c020001020505138000b540b500e0400242c0c0494000c1c08002d881950765800400d0100001d40c4441d0043e6041450294840d524001c407030101c1c0e00070201c8500405a45044c001042107401c4d02c02010b0402c00c90030056400750701300500c05035203c0d0740240c02608040d8544130000d82500d28008000c1e0300c100300440c0610069464210190b002030f0400351b0211421281c003401c40501c104010702942c0408607000010341e404071148210000f222001091202e030b112669030962550a5544059141e035140e80c03050351364101a2540755024560340700216180000711185941c9500ca90003030720309251084481ca1450034603003e4080107040a2031308009814050078000d451341070106000b0205a1140041814040c841200d071100c1b54000700200b000d1580d9540c032038000e500100c043c5000c41d00306207485d140c501c0d012441d505000c6450016626240403603031950100540284101e41c540c0b1000c00211b85529140b024600c5a907424 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 1698712 1250 1697462 1697471
    0xb0c0702040605100210021308070e01060e04060b07020f010e12010b0906030303040305190e0301020301090606030509070305030306010e010219080304020111030c030d02070501020702090c0d0c020111030f090708060703 96
    0x340103020540b20319030411401420b01485001d5120f0380001c036142541002480140c491451703940040d10000c2c0399010038044c1c07281500c0800c84408000e4094105c0300c07075440e01c42c26183c004040c8001c1c1c0e0414400d140311103c06211040c0941000c4080b07407562981498810280c10000b00002d482c501a00c0441c035203a0b569104000c900c0c10140c1c00b2642040c0c04070019070462804d0b0b58001c0c510312402c0100a0003054805088950714010f4619a8160720010000e6489603103d0078510700418852040800007401c000c003056082c0c41c003160200c292074110018510f9540c07924015a0340c41050a51141103225495050f0b03000358015200401c128412010242e40341024000106402c5449003008101e0700100416801420000300b10b0314101c4000e00d002da02d030340f0b141c2032042c028040c0620203500000d0751410043d00c00d0b40c41008003d04240300c0c00811504100e0b480403401c943d4108541d0380c140c0010800b04880541c030250403944810307080c085650040d26403010318100481030700c0f0a00825100d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 1699962 1250 1698712 1698727
    0x30d0e0c0f0102060c0901030908040e010303020114010605070b0106080606040b0d0c020d08010e01060f030e01050a0608010606030204050f060702030a080a020c090109090201020a0210030f020703020f0f0102030105010c060b010c0b0c 102
    0x300c01c82440300d01c092000300b0030b50400303c0c01000241b0601c9607160505d5528010f131000c000040d01a14002c1ca60392014041d1582d49060190180c1550707a541e4200348802d034008940d40d0300a4041d2000290001740c08151a030078008140c07000900582807030b43c08a000d02c80000c81814080c0100070310304007500301183c0c90303090032406440d189018404a040c0801d620040c0716400815849904507002e5203444003001c89014401d40040402500f4110341d54281010400036580c90f400c01002c1702c0c3c45030002c001150366004118124025801001c4d0320824034502c49420307142c6000906801350004041c1c410001003a81c81c54056070000c03481402580001c10000882c1c5095490103005200d00c2c0014400392603a0b0340001e440b1050058000d00c1140c544200142c19446641300304000441c0900440d6110600d04000c0d6480c42c50710340200a603c5809150000300c44107000b6070341200d43c1a19522000ca411f5a00c000141ca010b80446041010340002c0d0004074514500140c0103100c0000030b5079071000c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 1701212 1250 1699962 1699969
    0x304050604030c031109010e07080a0b09010602010902010f02011e0221010f0303030f020301050a030210020705040c05040305010e07080a12030f020304140606030601060f05090111070b0408060901060b0406050903030d0e0c 97
    0x40205201b4419800b490040101c0551442400d41c4194245082503903541d807070044000070310103046442d4210000000101700f154055000e040c1e0780d0b00036241d81d00c60440b82c620807400c0e5400c4c00009506080c203446400806403564000c0c05a52249441c1c502c40c00003400c0e5400c1139850264059022500101420018103400d4456050014244001545135604000208603d00c13142d1100a015200f008140c00c40d091007844504042d203402001408421520000145960024082907649500e040d555580c05000007640900711000c410180520301000d0321624000340c20074804505050b2202c01c40c1c00d17005214401184603a100b0102c1c190b0a000b40c141040ca04440246510300030b038001070047c8000e0f900034010000003801440c001d9900c000e460010bc51250901480030842d00c1002c0000c40d100d6039070740180088d40c1d009000c0302d2040c0c0d00e0341314260a0710300e00d2191031055401040140310662080c1c00400203070304081c08980c54030380701c13036a0f40045489901508000e900001c10180b200d29 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 1702462 1250 1701212 1701233
    0x10519020a02030a06022703030412020f0901030b150303090f060310030606080304091802090604021b010501090203060103050601090312030207060204051c0302010606020309060313030201060305030d060501021203010b03180304050604030c03 106
    0x504229147c103941c0300382c81c04241e40340302e240180350749001c000e1701500855541c120414a01680649640803951796454884400b030401e480a5002d0600315843e0710150800100741c84510034024401e0a04030240c0082c00f103036502c06083c0c00b0005040703417404404240c00b0301400d001030004000540d1b0307403880c19400400302c034200c0c1c505809502039807500c0c80150f520032018030b4018000300d8005944041c20460313082c2d403202d165010411035007801c0000850103841e03400f8602c60a0300f070324240810740d02d4000450307500c103890000802103485080881c4c2642d202c2ea0107403850b01c0c0b06007001440d141d120380016402800c08250040048201d5040f00201039081c01414000c101c540001c0d07081c9008400054158003000b0320384e40c02200c405107504203040c03003500b062008580000036280e503004200f440c03802400031809000d002d4411a00c0300301c030142c4210200ca040700c40c0b565905085484100789482e841e180901800094841070102040c2c981d5000d0040c80114419001096003e01d5880c4c80d05050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 1703712 1250 1702462 1702507
    0xd0515060105070302100c0e030a05031c0b06030403050c07091d0d030209010f03020c0a0c12050c09040b18010b03070801020c01050606090d0201050309010f020301090203010611010902010519020a02030a0602 91
    0x2c01d010180000340c00181404044602010100d29200481d2041b1041140c8440031541845802016018404c0c088024034880c0c440c1007074000801102d403461025160009041c5030081c20801c0094046442a070141140125030410b540d00c19a6a08a0105139540104102d0880550340258940d00008220303d500c032a1003428250f042005500019211054010040c02490740008503549805024040f05881540c0681000c0c3d115484804070701d030546e00c001d0226658819040c0e10f1545180600d0800d2144c0c0c0d00100c03001e40c581d2441070041e01148000c3d01c03452190349503c507803106ca17070342030200d58013800b195000140c892020200031070039a0005481d16000d408200201c031030035140c0c1c00403840706070707028201203549840d10b1641074010701035002100d094a20101c00828a4030140c1c00031030480d42a0742d10b800120146040c1c079400c031803402c00d009004c00d2007081440418500300c0c205c141030503407074010744181e0a51500031030f041440c07041c01183c0c0310343c4c0050107103081500e810001424 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 1704962 1250 1703712 1703717
    0x40506040504050601050d03050f03100302030f03030c070f0203011d010506010e040b060306060c07090507050a030c021605090a0b0603040803060406060801080d050d090f050a03081302150304050c0d05150601 91
    0x110b0406855241c0c865006000c4e8034052841903e9080030705005400301c4288528070b15500385d41e4500300080040900c2503006c100c0c82805142c0c00101c2816002040e21b0081c801107814515000d816903803219850b0400000320b070503541340c424021640304140c48440b002e20100001054602c0c1a0f400100b082d8404014140b04500e0220225515142e0200760703030f404801543c12179940e1150081071858000168001c1c004542000304100586a10001404010300b55490911100603400e000780e80f01c03e40161140d140300c0762050b00b04243e242c0a01c459402136003104001032040042d0000c1115940121030544003000300009110785407c00f842034000400c21443c042e020395050283c1e5907200d0f5a130b00c581004104000c60f0b600c1c034020803a4009001c45030300110140052045182c102d85801d01860150701044006001805078101444038000150740200254022000700710769807110340014109454501c16605a0f9405403030300c0055418690252005080e8041d1418418807000030007000d02d0704 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 1706212 1250 1704962 1704971
    0xf010803070b0606070606080d05070318060c0f060e030403060501050307050102030415050d15060f120203060f1c060908070c05010203090f040b030f01020a030f0605040c0206010501080403170f0604050604 90
    0x42101d440c041c540081c3e0890320307a59210303124202100030380010f800039405400303401a0749561b030b0740240042058602c25140c503144038014254078451002c8501c036440104114101002c0082e9141c030003030f60854814480042e0700080e419105180d600706d0b40045804664a1005000d54a003c2007000000d190034401076190500708190408280e241e04204018044046410f01d4295030316003140d8024407504051000d01591100001c00e5243c1c080c9002c80420098001c0650100c580d0089074490700024003c05e5000481f002031114144254003020303541c82101440300b0005089000d59280b80c0d00030a0116212440e905140c08105129400b00341550b1040041e640c40307494041d030300f00a0071700444001800c0d00e844400319050068051103a146c0e5480061609642505076010303200540b1400b4042004070784070f0f028041182d070031013030717000c05079210703400400003503102c2c540142d8018440d180151030b02032076034103560301c040d41034800c040d100410720704003c2141810300c94103a001008035810b01 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 1707462 1250 1706212 1706227
    0x30106051005070308040507050402070303050f16021c0908010c050403031101022704020d0c0f0e01020304030b0a02030711011406010e01030504020d060b010e03030d050103050705060a090603091403030901050f010803 95
    0x280309120f600350080a0080040000d000d01505020304c0004003000740042d55684094500203000740021540c5546032071900010903a002d02c844890000d4840c1a0010314488521601e440400010b0090030400c20090f023030b001c18842c10030300a0700a181c0b86601d840b6100d50941c6405010340d04180c4511226a1041c00001141852030740000f840d03a0070040780350341c140c81500124001c1e22621140710f80b000d04000d4440a481d0b48a07246140104060342d80c880c000c0b0440c401240c0340e2180d1b12000d01411942004036209c450554001c40d0000340c00c0c10140040b03070703003800c4040c255452100249810f18540c401c20000b543c1007101a00c030510246410085032500303031300090886240100241c00705660344107000d55a401a12009100c95006046944802d00d90140d1400b40009020840d9113015031000080c01c0e0401c80e0945954208507150f00c1c000c4c03410300404900410720000142c07006e115401020076041d005000441c0140b43d51030000c01c407072130001d008240442c0182d10800d0283e01c00c1100d80d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 1708712 1250 1707462 1707467
    0x1060e0c071106040509070e03010e0106030503071202070e010603020705060609070c120905060d0603021c080406080601020c0d030f0201050603030405010903060915020406050a020c011d010807030f020d0603020301060510 97
    0x1c40c60554041c203460001840308002c80c042d4040c9422058010800c40144003c40350448481c4044080444c003e0111074419202d403826200305200c0100254018800710000800310a501d2804912610450311255552522907100c61400ea1000000c41e0340011080140902801195030141090b600b942540c1801c610041070300c068000c000d05440590f00040380d4091250504000600c00203000b19224103450910300001c01e030901c0100d2207590805018800c0d00c17801c0d111164810b4000205c242020f2804905460300d403000ac1c41a41140542d841e180708907aa640061030100d8026039401c080c2144101d000707401c40b4400341c0407c4c4203500502040129a90002095007665800100811500140e14240c803080b00a16610020340780085800701d01f1542c001d004e4000044183d003214070035001000103484901034068140c2541400d03040c9642d40d54002c1081310b80048980c64006035560101d90b20b502281c12915450303035619290b203020000c9d45024020308002c0c14045440d120200e0800d00c02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 1709962 1250 1708712 1708717
    0x9010302040504050717010c18030809120106030209040f0b06032109010302040302030a051c05090306010603020f0903010504050c03070e0903031303050f0708040603050108010504020f1306030c0b040801060e0c 92
    0x1e1040b600c541c001803c0107000d001c0c6000422190b0342c45903040b011085514003070280d0b5008400042c4030440600099203910040704110f941251190385004841d00c1840b002d9040c900e50980319640f1a500040141c48403804184039a000d0580b00e04500010316042e5003c48001d054a486644044030320545a29a08804c1d402079840510290b5603c07029801640a40100d9001a6041c050108000140040400c1c0a80403800004030540ca6000f0b580c070a0356039003e00011580c06a002c080144202402580103107801c5000c024014203180f0450006400c3d168116800c641541202d44080035178101045502c000c3e0500369041203a92900c0500255a400010b00020b5084182c0c080d450506010700304480740e00140250076541c410542c181080c00341e02620410300000d25140c00080c81e99018440c05000d203600914022541a800c07003040000042c801441440583d43c0c800000007900382000740c4000c0207540001601c880c5006c2980d42160204d0780040c03442d6845000f040342195000d400c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 1711212 1250 1709962 1709969
    0xc1201050123090409050f030703020105060901030c0b130308071505010602010911040507051c020301060807090501020303041b05060c1b0406030201020703120201020d0204060c050c040b01020706030b04110304030816030603020901 101
    0x11180e0f112001680020060110100701034898011100da41450a0022005000075802a002404a41c5440c002e001000348240b2024000e004006401e00181d40000b000302980d181078010001010b49a840780080fa07440030504641c0c01d1703130b081038000310b20b090350040c82c0c0108001d000030026086035484400c1c1c0071040200d62441660b0f01d0780060820b90081094907038810125501b50b1000701c10103c154000c0d0b00a0081d440442e1058001502e5184120255826a0810703400b031401c585480d0f5440841d88010a90400d40d01182072001c80c0640f6940007800088044000a000091218820700c096420380c10340240500d050a03424000350340c000802c1e0080320781c0a0f591214817207009400b00c7c02401624000c03000c00c0e0002400042d43c1c0d9015518103000c074081c00c00c3d075102174450410801120215600980940c001910400502e8007e40c4070805c00c0f01e0250000c80d4104400b800450b080d801210204c0200f20481d091040744150340b40e89034800d4200e41420071580b4119000280c41840511 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 1712462 1250 1711212 1711277
    0x605060f0f0d020307020601080705090c0a0f03060305030a0201090204061a0a050f0c0601030303060608060405010f1401020106030f052107020904020904140604030e01030c030506060a0e01090e0c12010501 90
    0x518004245601d4102c81800d9450402151a03042a0000070345940003841070a0281c0310752074001c140e6180c10014140103182140780b1500e070001080054810142200400f4141540e42c20b00001069040c001490450302984c000103100f100c03441080101c070855005000c81d04001000c0320300700d504003000c60f40c0f801c40e142013250710340c81c1d45120252284289142c9110f14001d5800000400d9056000300003940c200d62034840702552005c044c00110b980034070031607500b2180d00c1e1042140c02c00100281403078100601c00880c00c1a281d440308010b800e6680b01c2140c1591010202d62648405060303003045044408084501c1c0021940000752050405400a4465034061001c5010486c0340302e114614001c0d85029540d25140031700700034144070724440696002c41e052203840d03c0614402c3c07240318898103009100500f0300741c0c2d100044491110300300074141030224126002c0b64100c0003507407007846220309040482d50350000165603021218182c3c060b505100300036409110510b5000b0704c2503007030041c08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 1713712 1250 1712462 1712467
    0x306050307060c020a03060f0212011401080a0507020c06041707080a050705010e040f0c02011407110613060e120a030609090201050904050a0b0d03080a05010602122205040218010801090605060f 85
    0xc0c0000f4245c05040e0344000c005901d050104a031615254020300210b84000441c500c0607aa24403d100c1c50841042c01d103400250300c2400200820103a074459134102c2c003588122440c6c5021000803c07600d174099007040c0440b04940101c82c052040410640d006803c522029080d40100d41e40d40c15907038011401541c1c10b100d01500110030340e0f1a1640411650080d409046c8070125071400c1c064020403010f5680303d0040d5000c400203000b60b00031109084c3c203208070401800103a8483e100703074044000c001c404031031890b110560300039402010058180c00ca900084000e5882c0e020302c101404a5925030701ca44403290401a0303050242c1c1c0c000c0c054840c6081d0548011a003a915807240788001e240f01c150312540201c051030050700781903124810074803a207e5480c0800060340c0b980421b981e1a040800c101e2145d079400c11849002050701641440601c4848035407254481e120740c00182640c01440a103016a038158040300761541c1c0c0100344900504061034100606820900401c1072842044007040c0200d200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 1714962 1250 1713712 1713737
    0x3230309040609050a050105060306030a02010509040209031c0206060301050f070f0905060408030a0801080102030103080915130e04060f0b010203030601030207080d0c05041703040501120506030f0a05030c0706030605030706 98
    0x5204a500e1044000c2080080d40c0e101c00d40003004041c2980c02000d5103241000129041c20240c0803030f4000c050040083c0181e08507640112034550203001580c0d0881e4007403007500c0c1c450724104110142c0400318040400c8080344140024603002000300800c0c8281c2c100400d100314070f4424280c040d0884001e140040b0320451030701041d9080c4460707910254126000240c00110030f20040041c2c40c42c403141ea606d50203c6e07640c8800c290300f40e00080c000070b08401c3c0200180000c6103400300d0040c440302c05101405003000411250400150641e6000f0b000c8502c21804020070444e05224003085511007800400c040f03064100005e5503800010807090506500084260901401500761818090048810300c90381c1d071000702c001c0090300f061185071800310483c061100c00d01000b0041c1c0301512410ba4812a902e90143c0d4000c014100141581e80c16001d415080581c0480611240210902501c02035076105041c0008038500035003948840201803900034184042ea5020030940101e80951130940c000948 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 1716212 1250 1714962 1715033
    0xc0503040b0c070b0907050f010207050a050103021b0616080606070308010e070504030602030a0204030302010e1c030207020f040c020a030905030106050a0902070309080610080c0d030c12050c0a03050414060403 92
    0xf41031009018848010304021080b0000103880b816204191000c03072500c460f8400580e510b14090240d41c2d4807010140d424001540300303034080e040c00b10001d201c10030b10344410900c40742000015208110806241d41c040c1e00b9154000c00710940103d401c3d51a1403412100d520000c1c05040117010382c0c1c1e14010440041460144a141524081c613040f1400f1943c0741480c80e400c5c002503005201c00c0307002d5400c0120126078118040740c480043e0042d42025203540c010390008500071346c0071500490340a00c0c42e03102124142c036144a901f0480e0305d150010310a4202d24107014112a0342340c1c0c01039200b80c0c1843c009205036280c080404044801c0c08201503203906480c6007c1e2800c50381601701c030480f88511410840382d8424800c6c5107044a00e642c1c150b80c40c0403400c04c10300c00032031084200540400c40103080c2c070002a0007180000d03102c01151404604180100d40210b08000891a05400040002c14184009208100c01d82010b020440741d9500c0e05186079612a01000d1400c009000b00094003d001150007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 1717462 1250 1716212 1716217
    0x7120806060d02041403070801060303080c07150204061206090605060909090a12080a0e0102030708040212071503020d05090f0604080304030c0203070b0a030b040605010e0607080403060203010b0301080d02010c0503040b0c 97
    0x61050b0401d40d02c40c0d407540039a400a9401e405c110b8401d00c5001e8001030400340621813082a0317078060307950000513a1000035034069580080e10850f010482e07848002a060303061b10280c4044e02040c2d4500300c4922813220310713030241c0d4115002024107a00d4a402001199100c2c801c482001d2020340d00c030603040d41c50340780090600075a080c0c0900000c40750201d40d540940d11200c071034480d80c01d4540801c550f41400000c1400c0340421120000804c0c40c59000c60003500c4c120444c91007040307030001101d00c919210740d902054800c0c11421540840c1c2c0204144074040c00340e00031560302050740c2e0010a05107050181180c0d50380c401a0001e09140c00000100301070510905c00c49103081c0d0090203c806071695484801c400303034000301c501e2001a107000f02110140ca02801000d040340c5d4140e44444c100c414180c20441194490102201c040c01c041100000044180c00a14001c000301c0d02c00c01d44940c94800d11038107146125440e00116450a4941100f0b0707070300802500d8000c0c1c2c221042c00d00550300d81e15101c0251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 1718712 1250 1717462 1717477
    0x301020301030c03051b030a03050318070602010204050103060b030402030601060c1401020307081008060709030602030c0c070807030201080906040803131a040c060f14041a0702100302030603060c0712080606 91
    0x5500000010042c020485100c100300ea11850480f01900c03510040501100b01524100340d054000c0c00814005c01d00c14405140c02c40568555010f0070140350450034a841c03625805080507035008241004250b82611617540101f1441c44d10a2440c5000ea0000781c89160501809050004005454081c02540803034040741c004100700855036803d04203009810150300300c80385081c41038100000301c2c844101190313040c02012162200284c0b6401c41e83c0d1400a0b410081c103414268000f4400841c080380104490401454004003801c0c810b411800010310a0400800880c1580e00003070074400090f11100459030301803042000c2942c0320f4814909503035015140034030384007507420003010301090100c501c0620044882d00e4464401c3c0060080003540e0b0202c1488060103500302c02d11040010344c0744900303038009100380794602c645000b09690015103040440c030076440000c0e6020040200e0750904203d82a0403160405140b402c0803125a284500240742e83d40c03c0c402c01c200341d4085844c80e1030702800d95100303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 1719962 1250 1718712 1718719
    0x40e0703080a02060402090c040302010206060f1207030b010911040602070306020c1002030c0c010b09090a021908030a0801030b0f01030804030305162a05180f0c070203100501050102011b0801090b010c02 89
    0x844500b40d000035600d2000b07440c184e219600e03000201724000900c0048030b0840c2c0e41038028155581e105c208215044010750305107a080000c810010070546c2d010f2102c0005540700f40040109541010204801c442c03440f404070600807000c010901c022500013950001f203070360003030b8056901e035000315080d0305102000c0b041c4481c4038008803e200305080341c0c10141c03d900d5054002000b603500301d0000c00041003020740d10b800803904844281070143c107140500c8000f0b0740001441d4685a55030300011407555001c00e00c01381c00541d100c00144200b01400107216041010400362a44a505584640074148601d2100500f403020010300710592807109100c1d4201d107904400282820300010104000a038828000307060001c040703000c08071342490044d2204800517650702602c055580ca42c2c100c19071070000505120203108040c00b40c50010b9400300114030700d400301010042907e51524001a00f95135484200a0710781c0c1d409801c0c508069071002da42030442d286a040410f1480d954001a1110103142c44041d40 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 1721212 1250 1719962 1719967
    0x6020c0d060207080d02071101020a151d06010306090b010602010b060f0a0216060302041d01030c050d0203070305030315100215070e01030b0a08010b09070503010815040201030b0301020304030309050717030405040e070308 97
    0xc200b980369014008050095908c0d58503d40417100481e195201d48400130442c0c444140b0200340000c143d4400002c80c248584044032300c80103003408a18108c2c00740d0003112125140d80301001004514820310b0700624150009001ca080c3e09000210300d40034140b00050310400c00300e002401036208001d043e400309003a808001c62940c884070004c001e903001c0e004451b80041c1b10348444600404102070b4a04898008640c481c441e03081104002c503040c1c00e14001c0c0d81c14403407a0008000720300e00340f00450007040080c654007802c010360700a00070101154010b0705c0564100780e652290038000e2002030340d4804401d1401d02c400c03180301c20041e0010304040b200e403500300d0030a1002040304001503002258440040b00e4100060b0b5402c42d00702c500f480b00340a8a03a00303810400302c0350004895040c91760307003240c41418013081c0140c0c02e5010908a0b04211400c0d07000a071555202024800180514030107821650340d83c8901c50040e41c101b6640348264400d0034000e90745c0b5941d180e07403004203107d010042c5512014070350303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 1722462 1250 1721212 1721227
    0xc03030b1809070306061502071202060c10050f010504020304050d03090c080307080301080f1c030504020301020f0d0209010e0303090a05010c02030c0406031407050105070b04020103020a0c02040c050c060c0406020c0d06020708 99
    0x140c1d2440d06000c121445817605102107840404a07034460387d4030089134001d10182e4104001d0811002510703000726081b4800b4400705402070410700002034460404000054140703452215807441c2201a4005809144100f0030f020101b100421000e0391a8620705000c01c0083c918a0240309004590380324204138080440d6100400010748001c50403a510f00d4100c43c003891241000702d03140c1e03902e11400003a00380300881c059401e0b03000f6001140d019000400050405000c0045521545d1040211540380e540c000748009842da0480c07103c01e204501540158280560f0310081511711006018041c1440400e4810000b19a401c102c101ca6a500c042c20078464a5682e01e49801d040d9465142c460039406000008101548a501507418403504140c42001a84441e00150025800448850708010300d07088030401585880c040c00e110303017a15907601ca56a01072007203801c2c1040809454042c60241c10401007181950015584500d0041216460500801b41c503104009118140b0000c0c0068804100e96 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 1723712 1250 1722462 1722481
    0x9020a02011a090601050301050d030210091101030e011118040b03030c06070f0804020d080f13170d03020c06010317070f0507060905040e150601030603170702010e060301060c03030b18 81
    0x88020550810024410b0546208104403204100c03000c0d40085d00c00d000411442c81e1640050f58080d000e401034541c01840f12021100341c2c1c444a2060b50f400402d24101071482d64144212201081c4c0310b00200000c2110142041d03151154540c0c4801401d000031100c2c0031340c0d489500c0351030201d00007070840b1b54440460300019102c90040b2001d201250040b22680c021500800009204a40c01440026181211342d40c0408c16004902010f000303403800d0001da1040000c01c85110080c000201e0000b180740d100d52042e80c0352000541810081500500258000c1c031030002d540c80c1900d901c01c0c0000030101400c4080c00b21405039000281074450002d042000303002c000f06030001955500da0741c200c2a03903103039402d1009440c4030312400106503212109401525031100211038001d401450041000341d6a6110f00d06500c0201351401c1c10030360000303050b004560b040220414051000d591050441d1300d4102c001d00106803015000c0d051644884c140390469852501c2854210103001d4140d0fa9400c100219 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 1724962 1250 1723712 1723721
    0x60905011401020f030d02070c030b040b09010e070503030403060507050f03010b03070e010c050a0201030903020304050d03030204050406050d0512030604090f0308090f0c0d0201120906021b150408070602031009020a0201 96
    0x10503125458480303880340d442d40f022030000c00c4c91184000452a2a4440000c0c500035403103c0401d65509410000c04800100418190350255004040b450420b00b08401c00c03e084038040000b48070b1542c82049c08100b544c802200703403800c40c0d81115000819988414007a07841d0300c00c3c0c483d07100d054100000045420407200c1c01a500620240c1c0d268504060303048015180f1280983d009411580440ca1700030040d0310036084030407a14440c1c0b05903070625540d50b02260607c1301440084001c00d401180c1806181468400c0300d00505044a0000704845541c450a4440000b03400d240a030280000c009541034407070703030071905003542d10542201031503015050080801000b40c6d84403441e8090040c0042c000e140000e00c080080740018041c0441c20940e90064030101c1e243d0805d98401c1d91202c8541d008944e00c0e20282407144680550818105920b689079800c00810000e000c550000010a00c800b28038014181da101690103000182d0fa42c0b1040049500d000700c991080302030b140001507801c40e05506400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 1726212 1250 1724962 1724969
    0x3080a03050105090606041206061502010b03060c030403050301030813050d06050f070c120507060f0c0c050d080106090501080603160f050a081203070e060705010c09030b0903030f01030201031d0106090501 90
    0xc081000d070341c80e0340030011034820950340b29502c62000e20051114000a008038118240306640009941c0d95032084442d00c9042c030300c3c0c00320250355500c00032503090801b4420141d002813210740f00340c0b5600d8aa940505603010600015240d844c0109086001e282c0d11000c070780c06088010120012030f42c0304e2510750003800301100d00342452000c3c81d0220b00b41c41e0144081014055000000d801d4440504004035115003015405a81304c6032501550090341c2294410b0f961419840d030394290307a2100c00d0502c14030744503902d00864100030707a000c01041700c9980702c10f241c01034031400d103401b0784291a01d00c00030b40f40402d1010302407440b1104623400912280c05c8040e43c0d0813205c06403600001d0036903403040710742c1b100914015414442ea0030000944824495600300c08107800042030207080c0400b6450f00b0b42106c6140c0290300115034444000c0c0203100a1021040d8082d602200071491440d05901010780004184402418140c9560b0303910210241d03500400c0b00d048a040c02002415910385410780644402e10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 1727462 1250 1726212 1726217
    0x30405060415020a0c0602130504020c0102070501140f0105090c0408060f0106030b03010c020c0603040201030204030503070c090f0c0e010e12010c0305041103010203070503180c040203090303040209010f080703020607050708030403080a 103
    0x380460795140e1a00940c3d01041240d1222540004503880d140083e60141c044488515502300b00031909540318400740030080c0b01100016213800051a2060840b0480c0f2109401c1d041107800304084101d4156215066030000c2c1d910f0005512042024500341c043c54105501d54001c020811200440b007a00041c1242c0d00c1c3d80e4140003520b0510241400c030f4138500c1000700147c00c4010128030b10706107400296041072061400600d000d5881c1c83d240d007140c021100407281c1c1450540100082d0806010b03049180344444070404c48140f2240c000350004284c0d00b411818800c0e54145a00c9980d10f006040c0e9214a03440d00034041285032a500600800040714100d0707031000c44651685041c00d051003960321814071600e40c0da141d43c0390007031203402300c502c2c1d000d4440311841355035007602c4292110b0010303501441001c0029626400d04d441000600701050304944001c007480c89040081c42c40c001962012660141c84042c0d50340203070b050860419440703401104c20341c40001400410040148000c0010102c030b03a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 1728712 1250 1727462 1727483
    0x3030b01021203010f21050111030106080f0c03060f03150a060302011806020309120708070e010e0a05090c010e01090905010806040b0f0606040308090102010b030d030509070807080d050702030f030304050604 91
    0x100e040345a400b00b8000c0021881c808841804a2002c3e101480491b1480d143d0140381ea070841c0d6143c41c2940c0307008000300382101c07010004021300b0780c0040895800441c20760300c1403854544030611400ca4000148914481c00d1259010307669a141032088034021a00e0328049425071501c119400c0140200d132000700c3c00107100c1d00d0308149890000c00c0f400d0070b0755119400313181380c401c4a508200815041c1d00300240b09001d0322400058440c0208007044c014281c020450b41d55624118100f51004030007088410503a0500040000d0b40401064040364940f01742002c062410406004031809641c1707401108101e440e08001065a41002494a03c503501c25446012680d55078000b441c140700c030a40d000c9030441420b101c14000195204060241010180300005145d072406000901d04100d030580714012a50b14001d0048904003801908050708000b0300034200d00d490b04811a580d1484551064100310004c40c2560455a0030700c0480e402041c21401c980d01d80c1050300381252900000d841c11103800c1100d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 1729962 1250 1728712 1728733
    0x3090b28020708030604050711010603050705090601050a02060106050318060f180a03090303050a050715060302030f0309010c0209040206040b07030f0206060109031a04030210020703030204030213020909160201061203030b0102 99
    0x310700890380141c0e48030003820b065442d4401408040c04c00601040b081c801c43c8050704882d0402489110001d50043c0004c124051801050021400307024007150304021003000020755054000540c0340c110703006403910703e80e20b41c0d880c0100d4012901180da00e469038082c480500403400f0343c01c000980aa09611400c911405106035540e03a540c40842008011600030f050400c042401031002d0710400c615030610300c0c41d03c020f80c1cbe0b559007241c0c0c0c2c240c0c0380c803440369031280144250706007003000200c0c0e0710000c0c0056107004500750010748000c8120b203000340b05840301c1000404540762282500d0003010f26040c00c03a03e400c2c40f803038050024402d00b26003c0051264500040c03c540c03180030700f0780c03c9039044000102c03611005180d039000303004000d00c1642948078600c0548401d4469200070070070742e80030780d030010b80f5241544100320720303110074000c0c00341d0881c01400a01419030350303c0a400d810000c1c80d04004c00601000500781e01426096100320620403100c44c144051680640056109580c02d9080d20b019034031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 1731212 1250 1729962 1730041
    0xc0306050901061b0b04050a140304080c090604020904020703020601090b06030105130903020a050607111005010608161101050a0203011d0702120702120d0c030f03020702010e09060103090b 83
    0x18621425600051580c01004090700448a12862858034110040800e940340c4507005280b100780d81c1140c003640b0001000041c01407221782e0b050141d010f107002d9450b262400c1121aa60007400003164400c010500100305142e650b07504551700458068019134441c60b0300e08010703407200c109214284059042c503003030841e5850010304a0381a038000904003020710003031190b65401803019420450951081403c0e0001007401088485c0c403821007a500d0b0080645044212405c0800144882804c103003030200512805410001c0740e580101c110110301003001c04d0790380445016810b284501025403a00051140200c0107400650581d04150b032a200c0c0e030308174002c0f112080441110180c0050300320300b50201c0031854081c0203b5895000900064051480c018850704204020342c0b12804103064a02d0f030410550403512000b11560241011410300003203400103024180d03d00d40061280c01c0410001c0d680e07078003c0c0e110400d0140c1029040070b9503d05820041c001c40f000402c60001d90720414440081e018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 1732462 1250 1731212 1731221
    0x105090108070303050d0b0105090409050102030106030c02010203040b060d1b0b041a03040201170604090204020301080a030807020f1c110105090115080d0c02090604060e070201060f060807050703080612010c11010c03 95
    0xb58940d5400e8a040000c3c4031a1b801402000c540a04000c1c04001803882565280901c1d0903160060000503070b03075490844040d08403085060130300b065900510401010400d00c05c025580008180c900310114042440c007010010000320b55202030080c65900403802d80040c2c0090f0041e01e140b00708004401d0004071646010740400c56000b400164280342e8800d1b52108901c515400c0000a00003107108101c0c0d500003400c1e60000d800c202115030042c4442818186e1104881c2d412203842d001811180f10301c64806611800c842c0c0040b4100703581c421800489038031802070a8003409480c8001c001504100d20b803030307003e02210420044e0523602003002180840010806184070306031500c1d200d500400a81c01c0c003100d80c000500d0070b644156032380b9000400c1d8090b02c2c40c041c49448998000940242840c000301111409500903004104d190410000d0b0381d9004000c8503009509404c005410740e81d02c42c0024001d6004038092015942096071440c5001d400003904000320002100034002000001022000c58 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 1733712 1250 1732462 1732469
    0x50712060305061302030102040815060a050604231903050a050d030501060903031202070807030908010608060705070308040609080406031406030105040203030406080703060b0712020d08060a090b060918010509010807 95
    0x60b04030102183c8443d000742c0b03201340d44900c0900050704040d40c4180740781c1003d42e940e10130420700344100d00304039052524200c80070190104071000d500389400c10740c00c000042082c0d080c9005502c4040f11005090741c4a0b65104c080c031402c0703408000c08684916183c1d80320004003034101d903184960011984202d009001c3c0d9416101c0b03680d2290011442c50710f00321000500c0010400c00280d00300b2038580440c0c0442c0052550f039000b9162550320900d031039541402c5070b51680c4821080e800100a01c0700e22a070040c12a9800c94240c42d0048043d11142000401004424001001d00e0000100000c14642580194412034281c15210300c6981d00d84041c1400e945040342e0081d4940c00070002444403c3c0107000c2c42d50414698030700020340da07844880c00303d203a41c803012007516444800040008200d80c108401c4074220740c5da02d40a901800c1c880c010481689090245418040c0c071a840386a4a0b01c40301c1c1038078003541c00140b21080f9003011040c03282005000b030003864000d01c204400402c5650740066501c084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 1734962 1250 1733712 1733723
    0x903050c040608120a050408070e070f02030901020c0105030402120d030f0605030c06070b04031110020d0e01020702130f020f1603020706080405060a020d020903010207060605041a06030103020d020d080d0507120603 94
    0x2d90011050b01320325070f110100d20701c10301c4020b010100c1c41c10010004a0f01400d8006680012410300690140010031080d08000443d80200403038192a680840d41218104080c00c0c4a9181d03101e0f880082e88400d04044a83e900f40710744880000460746c150440c0c0f89000e4059000c00ca16a103407818951211b0040c0d460540100c81000300c2c400045c501c03406245d00034020710b468082404052800d5040840e4031100900803038000c25008001407082c4200c080700d0244400846c038042c0f540d030100d0001e50904e500c80781d0700b0307a4900d150101002c0700d804480441c001410803907600d001103001c0350b0b114020548160010b101e003100c0403400600030100180203135003110040590355141050140690701400c215000c0c0c903020320418069071404d0001e4606c0511602d408607400c0e08117010f2004960040c40849000d519075141012a500d82400716410760750142c890a8420410f0700204c2d01c088510b45006001c0c81c07000401c010401e990f980082d0140485a80d0322104843d11000a82030b45c1050002601 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 1736212 1250 1734962 1734973
    0x6010308030601020a02090f010e0a0b100f030e0106030c03060b01020601030503120907030f08030406050c180d0204060506040b040314010b010e040b030a06050703061806080c13020403120903050c040608 89
    0xc15010009154002d00c1481115408900c56000c00d0100c3c0d0300343c8400424a00e024018040740818000d1075502a101c2801003046c3c26103240052030041e00004c5800900418010b5404043d20035080015240c00c18402840025600d2625908ad14928030041c0d0b511403600500034031545c0b01203007075412a038008008504210f01d03010680010a0b020305209003e2080b884000b001402403008250880c0c050705020780c6a1600382003010030f440b0001d29110302c11400b0082c1140030082442400046a000e9441704140d80c11807000c100200082d402040d445100894005200e9410707000500517079208003020100604040300840c01d0f04c80c07194103140411007200c030441150500e6400300c00c0c042c5004085444110449d02c465003203550654400e0000ba84440060080000f4100c040d0082c418080303081180a14100226850712030160003648940003a00d100c200300d0070b940d0180d4000d50341001d5a0827607440c2040f00540041c0709880120741e140a9181034061a160a00c600c4045982d104013800c1d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 1737462 1250 1736212 1736219
    0x301020a09170102070501050a1407031506120b131d0106050a03020405070507020405040606060314010e010902030c040b040f09050601030203090709020912030d061d01030809010c0201090b160b06060a020601 91
    0x1100084290b0200b03102d50b44c24442074020550034000c40e4040c5200c3c180000e0b0a6106a0005107420f00040043d4145820305c03480140742c51010710800700301c840303a1510100c208403103003104c8c1c060700d104a0100d500c90341c0705280340401420380c0c0c003d04008103101145050b800309543d800c1d00741c491500c20355038462a03c91041015040c682c0000d0341c0416203251592030b140d5103a0010b1b0850b5030075242a5600d40d174507002030004503014400e081c1041e0310700505d81c419602d40344641c000c0c80014007694541a030040081055500e694090711b01821a4481441e03c1d5a00c458070a520600b03a441039003510360424010a41030b5010303208a9020b040d501001d2320240b41803100e150081c1d03005520868010b200d140c0c284909003014000b40c410008400004607030320707140c051001c42101c0096042010340e9560401000068290003c880d144102820003c00314110380c0010303070703480c89076034001c2a00302c100240c9c07203040c03180440d07505100b40c3c40713444442469102e40c4c046c0006805221305100142e400380c001031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 1738712 1250 1737462 1737479
    0x7081603030c02040b0402030f04020306010902090319030e0d03020102030a05010b070807030c051f020c06010602060601051909030209010806060a1e0608041506080a060b03150601050304030c0501061202040b0301020a09 96
    0x40d90702c2c6001600c041013401042c4042001c9a208540882d0503400ea0003e020840c502889010300400d6810015424401312030300103130308e84800101d84201465094000030415000c0c0e11303080c0815070700078041c0f000c00c40e6031300b00607021f503100b11682c84000e4541000031501c3c0081c00b050340c001c15080351105062520a907025078004c0400942921113104154080100701242480e0391924084005d0240c1c940e030100d04d030103181c2401030b00035500395040342d41000320710b9034007405031641500c20b50018072691102c154240d40c035104030342000c0d4004502c03200100382403000180e5503000f0b40e0180c03500224259038120038055000d814500d0b610b03640e07200700d04122062107940d0031a001400340c1c2940e00c04208101c1d030711003202d081d44d006000303a410082490003845003510900c4140503003980940f0b01c40082c60001801c00000030846410f00002001060a0611a00d20401115800402002015203420f0ba800f1a20b2039240c040340b00340d0401c0d4030354100b41018000c0d254981c3d05a140d60a01c281013640a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 1739962 1250 1738712 1738727
    0x31e020a030f0507030605010e03030307080c0a0309020d03050406020610030206030109020903190501050403020d03050108030901030216061406030c0103020408030a2a0308010906080102070201080406050603010e0f030306030708160303 103
    0x1a03020142c40e800070a0241055200301402145a6180014034628000014000b080140c001c24400d410510810413116081f81400d40d102d41c2d50003506a98041003c0154001c0c070068101941294131070192001b0140c0000017001501d180b83c00700c030301c240e4540700350345400c1040f0302009400910901c010400000103801810bd00b100c003e081c0d40c00b07081c0c1c28150441c510318104003070754660344903010f2009040d01480384444400041c50180a1981407824099507841402c00c0d82c1d040650000714143d80c03051220501c0c0615900c00410300840c5100d041c105030210050360114070a020300000142958004c0c030803079044600b1b4602031820301b01d6480e0309580c0760382076942d85241a94440b0750700d80000321110440f50103030f101e038490500ca9410b0030f16400407100d15400141445e84100000001b603a00500761591150b80300b04081069030ba0800440d003d0904c807143d204144c820308039404041c00020000d18410304050701207a0015039100c0c1001d036070700190141210211100001440424440d00341e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 1741212 1250 1739962 1739977
    0xe090c040509150405010c08060a0807060c03120e0607030f020a020c040509030408100509010501140904060b041b02010902090a050601081503030403080a080402030c01030509070501050304020d0b0103081801031e02 94
    0x64039003100d0300001d01c01243c44200c4003250640d541381d00000b0041e400c403402580048003500c455100906094100341c0d80e040e240a00028001110402c10415108a02c400a250b0345001e00788180e4502280460740e800080d10070754046410324105100c403055520036916213907541d90040c101040d010007403000030300d000f400c50184c901080001098104c820418a0200ea81300c0000082924003c091242190410b1300800c10820300000d10120750f98404510b190002e4200c2000154007005100140041042c1c1002c2a5040d5074100303640c0d50150107610030340e2014029a104000c581d6181c6a040807510201d4000f0f020481c001d021801c050a000c80409402101034216031409480340c0319004a50489030264002038108800c102c00c605041c00010100c00081c00c09200a0511441c00c030340303403403032401441e04010380800000c0665a900402c07141c4690401d0314920305586a05152032198088020f28404808072080218154400d1255035a10501e031640c00301440745205e0050080c1d0710469 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 1742462 1250 1741212 1741231
    0x20c0307050a050604030207050a0f030312061a090301051e0c070609060213051c0503030601120f0207060c08090c0102030f031302030f0d0306060311040504020a090b0301030b0609010e090c0405 85
    0x10400007900c100506000c640c01480280020300e0186002843c100c000d400ca180140e070b404204200762481c29078098144c943c542001d0b29150340c8000e50310b00518207944140c4004100d8404121001d003284002c0036406400e8000340b00c195a82c85000341c10340e602c82649200f0114407000150841d000501510b0071031b104010109046030182c40d00010398203c031503810100e804000040280d8600081c0401c80c1c043c000b203107090b107404507481c0c0f41c0c0c4a010041099051000e00365100007040341980c01185411041e0380110b442d68040c0c104100148110b00203c40402c5030200450062080050450b90b4002d0590040d443c00200e00189000c2d500b015181040d034584003546800141d9041c0300204046071010010901898200300040603281a544400e00340751070942460501040b84c0b0448043c2c072026680581e90321468042154010825800000e8504020001204105201496500401084030000f80300c1e40c031101003c403448000d80b810030740c0b9403000381130007072a08150f0001988107000c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 1743712 1250 1742462 1742467
    0x5100b010507060f0501090501080604020a060e0102030d02070501020a02070b1303060c11060f040204150f03080717040608040302070509010b03130203100911090901090b040602030a020405060f0c0106080c01050706020c03 97
    0x1c0d81d0f01c0c410b0741c2d401c3c8040b012450303c807001401030308903d204450050140c1c1e4001d003040d041c5a000301d071180445004601c01c21610445145459008008540500365035010443d40c1c0c46041c20402e000b03400c040301e088014012400c001803900c0704941512840000503a08002d120306e035903034020080284034022030a0246a52000d2000e53307007071084d01d1051a00c0951401c0c2450644100720485801f604d8408802124440030f002059610b21000181ea03070007510580c4d116003c0c101001101c1148495010681001038007042d0207030300c100190b00561180d000c66030b250703881d0010052202400d0192080500b0284001100c0c0300d10342103c030503124000380c1501e110103031102000c3d05503464020152586815880b50325031038284400040d0748551600000c001c050126a0f6006c4401c2d4007500c003500e155008008142c0003031081e81101c0080000400d0155103240300b5004002640000860340a039500c3c00070006681d0001007210228410305a4034170749410301315981d40c00203400078894442e551005 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 1744962 1250 1743712 1743727
    0xc050a090e0901201207030614010804080c0a050706090803070b060607020a0503060705070c0e0402030d0f0201020d090309050306070206090d12060e0403050c070b0901120f0902130501090b0102060405100b0105 92
    0x130f80b000e550f940700d481001d035070314030604a000c43c408029144100f01450058100109002210300102c1c004007440c0c04403c0e40c507a405c10003070a0181c25a0703184e49010b0050700000304100001e801003240c106448485040390754007200ba4403802022009010a0f0003440010260f02e40003000b07050103032000340381e115403e49070004249030100032034120000ca01300003400d90510241461120040c131300e56030040320f10315040e0b012035201d4208004103c203003d20b18400700300050003901900c4d00e18114170030802000806040c014a04e0385140300b058081e01401e030102c0c103810b00c0880c016118890200c01841d0340410355000311001c070090070a45502c956108404994010300c0c070803e9028900958900380c640041300c0c541030520b8002c0e0700410801d4010480c2c80c105982248200c04a0340d07031014000382441a0b030700d04001a10000b0f600a510000b210303242003812509034010750584d00f0702d5a0800ca8038600078016030713139048180c4000d000c0342d2100443d505000c003250032100c0680300c1072420b1800c2055 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 1746212 1250 1744962 1744991
    0x603090218010305060105010e0609240403081201060f02010507090e06040905070806040204060605040303090b09040b03060a0c0909060506030103080315090901090b07080c090409080c0a030201020c010c050a090e0901 95
    0x10280c000304c4290300250010040307580c0c801a03084607004110344003860011200300282440d01e540050440724401c0100c51f06000c880f81054600031600480500c3d5101842c3e1408003040200740203030004186614007820b04c1074814803a40740b15460303546034030303001c141007421400b01c00074000c0c120f0340e010707403580c001000041050240b40d004044040c0140300030306041c8100800c0d07a155400030003c00c5800e0000300046580100c5c0c0c0c10031286801e20350b0750782c1c2c282c50303020034050050358000e0b54040c41030398140850343c0d2182c1d10040d0706500355a41c8100c03080c0c40b000c1510564074035200b01c0d98400300510040c404030340484015034000811004000c084d458080c081031b01d101d005c07a5800c0c600e07591106800d0a0180f00050907500450354540004103203041100c0c11010300507006e070030703000b1a03136414040f0070080c800e801c5800c100b03a8042100c00d0b95000d450024080c0d40020b1103500c0c25400c20075400049400741003912444141610b500c500b20b800c080c0c080e0b0b0030280045c80070300150340f1540304110320034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 1747462 1250 1746212 1746259
    0x3100506030c03150402150a0210020703020106090c050307080a050108100209060408010905030703020105090309010903060207050c060d1508010504030c03050703020c06040b030106030c080103080a110703020901090204031403030705030106030902 108
    0x815070224100c0e0300d02130042009420060b101c0051f0138204104c002541c0c1c0d4041583c40c10300025030380040e1105944d060032030042500360041e196552510041d05186a0000003070361050070700d582d500d0820750342c100d901c41c05e0f04c000384140c40e803a500442401e007411505030040c226811000d0946800c003581d0700656400d5900e810780a50b01c03900300182074020b040e07080c01920380c0000380c2c2c0c000f1843c040103040000e006942034800944119404282c00d003c00c10103109441d503601000303000c192146d07001c0e081c4034010b0013003800000941000f0100003400520602400e4815034064a4881c0182c000b6281650320390301c062030440c2140280f050410080e0b881c20050030140201800c110340b650304001001c0c0441d00d02010000038425000010030000c2c81c900100d411001a602c1e0851503420000141440c4c40d0841d0002540300c90304800115164034164007074404c0328041c07002015520009061141c40f440103a503e0701c0010000c00050103424080d4107e060703928400b501030b404001d0000c10583c0c241 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 1748712 1250 1747462 1747483
    0xe030307060204170304080606060c160806010501020106090b06030c090a03150b01030b01180501050c03040503030c0f0105010501090308040509061206070f18080a110102010b1309050706080603100506030c03 91
    0x107503408101404180880d104550301903000308011868141010001c9070703a000c00410507849900c0000f0390310001102404021446030075403480302c00c0c41c0d03121301450781c80b06800d0140c80c2c0158a84000060050002d0048905160001d40010700d540c65401c5100c3c103640c0140c90107508064100c0c00000000c0824201ca0b02c0300d0800640051621700344400181036406124019040283c219014042d952806210301c0c100d81090800654400301c02030034a0460007258030082d031500000c100348640302c50100b181c100c5424508001c0190740c2e220001910520040c0c040908141c40a200c18042401e1501a20342c000300c0040911a45d803c5500c0f0785864550112803c40025030101400076200d0b4000e1540020440204498540e2605241c0c0080c0d07640c61000740074000c1c8080140000c0164000c0d40040f17078940b0040c09a05291200382c40c500701500a2403401c540b1031181c40800604203200d121801c2c0903610041c086c101c11041d45004402414014221551500030114100700036501008002d484c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 1749962 1250 1748712 1748723
    0x40c0c02090c030105040f0606050904091b0f090e01020c0d030c030f0612020a050102010b0105070204090c0305070b04080d03020301030201050403020402030a060b0301080706080108010209010801030b040f020405040b060405090703051207030e030307 109
    0x40c2c4d030500e010711050300c43c0c00800c1c001031414001c007445044e400c00284e46001d40f095034000740c021b035241007807580d440d103500e89108400402040401c00704c4410805501342d5081c1602440f001c0e0303146270080d08078410a4040b403080d82110444c4084c2c68469002050070004903c8c01180040740407038034908890782c42d40300d03218490105000104500300301d41000001d00d4240001c116001441001038000d1045000080c0b0035a521484074081048040c5000084c0d0f8204080390044d648a410342000c0c0d50103405014400e11030191705010b0311b80b00740220f074182c96040e5503590801d49107900b404040e40001d4109121603444000100c4c0c50301040002e18000e01284004141c030901d4550090729100060300310005c4ca13401000704128990300800094112030780320780141040ea8544c2844040b01c0d2048000950040c1000281300074050801c1525000c1d07001141d040005440e81700c038a59441800c0e00c8000c01e0740d00030540705040c1c0150140600103440c043c0c100103002c90010b01c00207081d0f034400c0b941102c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 1751212 1250 1749962 1749967
    0x3080901091509030f0e0306070c050a050303010305060609011505040302040e011e02130902071106030402060d0507050304020f090402030601031103030c070905010905100b04030602071e0501060503060601020a0b06040c0c02090c 100
    0xd043e406030005c0d90204040c2019220000110f02280e140c800040640052220481d03000c020840100010080c0c2904202526103c1d6100c0c50320741e44404042d40c0c0c01d40305114800000c01c13905080b40d050300961002c1d45584e45800e15590a2001800e0a00c017501084c2d5664200c040c1000c1c0410318070340b03058082c40401039954500b030000698110258200004951040c0001c600141c600503031215010000c0325010780300c0e9210310000701588981e004c007406031810141806981a08100a0740c0940d100b1624602645000028040c524000725400b940c10703445a4010004184801480c14000a024003980d00c0c1c070007001c085a00d484480d40c4104450b0750340d0350040103019114440c940c2c002d402c05e800c00d00e40758030f0000f080005010310702000d0511030340000c040d0104419807000702140308449400b0f29404110b42080e80c002d18281c81054028014000011169880824003040d4103501803034542c0c668544030240070092003c01030040501c01101e09605c00350752000070705481661101c5107036a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 1752462 1250 1751212 1751231
    0x5040c08070906090602030d0906090206120103050705010305070203031603060b0a170108010203041703060310060e07080a05090307060b06040302030609030406020c0604030201050316140c03090301110c0a030809010915 96
    0x1002c01d6040e40c041002c0060100302400340b540e001c401c0380e0940c1e2049201040911050400714010688404001c0d401580052507070205a0f0084144c0d040300d01a2090b1038840707644030019420f64608884900040c0c1040002466045440c10400307640781c1c0a24002a216858103654000c503401041b6200101d40340d41c2804580400007608140502000da00940c11800c1c180d42e01c00c05203100d0703050040b0406010001644948007002401d0340c10001c507000b441130710796400d800ca8802e0420385800300051304d075100050709661940a0745019554900045141c8030058a44070000d140700021181c0c405010000040940e408000860003a8255400303195514a00032020349080f901444482c040e4500340300410240c1c6c3c2050a90b0ba202d02d4102c81c00d168801401070444aa28940d144600050030100c0e165200c103000101801c400801903008002c0c10044c0c50780401a0701807583e40f00c0c0c13541d000259150010348034060070350300041600001300f039800c1d06540e8000350f1008652f2074000c40340c0d9500880b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 1753712 1250 1752462 1752467
    0x5060408030715090b01060c03020309090103030509010210050609010b070c030f11090114030718020d060f080c0901050d030c02010c0501020703020604020907030507020606090c040e01080105060a08060108030301120c05040c0807 100
    0xa0f54145140e0381e0400a81c242a40c5105000c0c03014455913041c03083e01c038035407000c0c5402407044841d00c23080103004142960312490080d1058220200319030043c85400c092502e80c02c028400c0300c1c0100002810700c061070f860204102c0301c03035201c00400ca8104038011070000000360f0503d84d05032581c4c0f04090030104444001c0500089141c160b2110b54009010fa040014584000ca2907209403855079a091100c43e10451b0f500010b8442c011180c50400e240c42c10009035241c08603004415034290b02c1c2540c161b4681d1a0070800384140030300503141e0002c07903254040c000900603201c2584042c4103052690031014991142d80c22600041c0003070b070140e0444000c020440c58170400306640206a406e0070041c90400c2c0400030340e9a0401460540100b00748000310755007010300307410b17140144140c140c06042c1d0740e1079961b501d0282c036040d10461301609881d03030046111140400c2d9070341620b1300304e03000f541107070310742154802c4520501406645070180c184000c01d5685a07402101402c0701ca9440380120381c01c04e032600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 1754962 1250 1753712 1753733
    0x71a0702070e06040c03060314011a03070807090b030705060409050106030609020f030f0403050904020a03020912070305030712030b0a08010903020f190f15050106020604060e01020403030507020910050604080307 93
    0x8402190803505091101240d00b40a0a0700710724156000240100c08100075402400e4a07080604506d07103c6140c4100c49205420140c007000001d9040c558103010f040c145551500301c3d00074482c00c2d410950013400410321952140908038001030440705d4041d602c3e00410843d0307000707802c04000e19451300b0051002079014020780000f400c0c00c220861a00358429000004c0c0e000190204441152001c003090074188170f4401d503081d4804c0100b0840d80c03081c41140246c020342c030880c1c0543c0901e15129190100b0500801c5544c1140d4210001c0c503d800856640e509403503010001d10310905546094800c41e80c0c40710281a4060708c03203040005844051030030060314040240e18034081e50f5024161255a001c0d400c0a90301ca656880085003118402624000c2e40c04041005034900c02c03031411000042c1030b50b0000b903150040d070141e481000f1407091000704038240c4c41a4017025010402c10400200107050110b0040d6110070034000f11064140c507080094459841644a40042e500204900d014130218085 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 1756212 1250 1754962 1754971
    0x10803040605030f0709080f15061903080d0905030d06050102010b0d0206040506070303021605070f0602060103050d05030405010212040b0a0f06080606100c050610060801090e0a0615080102071a 85
    0x1142000d01d0500028031600c0000c02810f450104a03022450450013403550720068000c0c0426241c410140701c0d4104d944250001c5015080000b59010640909050390b0b04100303a11508040e034035481c02e544912a0316840b010010f540160b03180c2c141008030f5001e001500e0000320000021501da45807030002801c0d1442d021310103100741c4c07884200d940180d80300c00407103048680c140d44035526900c07203080640081c0240b420110506103200095030400c140400c070002620402418400c860791211800c981e42d0209010046c2a030340b00304400c0e019140580090f582c02072041002501e000e000c403e002104000c10340303045400c10440e0060120001060060352001c00300240d0411406240000c8c0d140c2d00c40010305214000c03d42c04051480c0b180c0b1030400001d005400000b12a043d0510b485c03100117411091240100041110001062081c4507005189620403c4801010040165144c160040020700310515200845d00000601d01c9828000390260354024051a0030021000e100e540300c0c00c50007030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 1757462 1250 1756212 1756229
    0x2030f060609010f0305070c06020408060115050a02060a0513051b010206070c11040b06070206030103050a03140702010c020114130603020c0c030a08030c0904090204060806041b06020c04020c0106051203040e01 92
    0x444110b60741d200d20070540c1d14002e4900070900341c0318a04150780c51580c061010706030300c0c000540419003400024441d0304071901c1402c418844411503c0490f03449c02030072103000058214001090a0700c0e8a43c0049400c07054851912503040c50303655400b0f28000803140d0381d414624101c581d8107036070b60701448500d07400301e1242000c0d02140420303654071800da0ba0800f620782c0304665950904950380c58040079582065409002165296140d080c402c2e600d40c002841103000403403a000619101c20910b0944034150350603100c01e01c01c3c0c1200c1c1e0055481084440c04481d0481050000480d0740c040c0000882c01482035480059032908450700050402c128404294000d5020110b80c800040c907440449900240900d00c65855040711030015000d0b01c2c152a01a50060506101240b401c80c045602401a4030801c209000325500c0c20345031264070440d00c140c002603040842d100901e8200b58006181c4400c100c0d00001c4d156403202d000902020001c00c04640c3c603407020070203000d2840c0c04c1d0341a601401c0b420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 1758712 1250 1757462 1757467
    0x10504050a180603230601060c1e0201020f01020301090606090902030702070605070606080304090605040f0e1b060403020306040c0602060705030603070b0702040b040f1506050705120a180902030f0606 88
    0x403021a11810300d5110b00808002021400c1412400540c07155001d10b51042c141c00b4144880742c03490b5030b5400b5036010a411400340000001e1a41d00544941c103c0c0d40c0d2050741c500482c82e00701002c8052426610b01a1b055020324840000349000070b00c0194082d1290800c00103005062040051010180303401c01d0b00158410001d020215800080c4d020032200c8510f0500d60300c050900d070000141041d64040f507490701c8040b40204422481e50400303002d89406030750422596000c410b441043e1501c0a03c1002c560b0010031940c102d80914690310480b00302c001e0283c81c40c0c15960341c00b00346030600480741507442c00c403141c90501c491380c2d0500409400101d9460b0480c01e604040001980341e210074464000c1c3c005e4001509011501e80703421901010500030402c000d03d4100520351005003140c0c20021002d0495040c3c0803540901500a80b00d410ba0490014400000314211a07809503200542c2c1a050040820715000194007800e807810140074031010158480c00c155542041e0800098401803003080c06 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 1759962 1250 1758712 1758719
    0xf02090d020906150a1e0c110603130203060103080a0e03060405120702040603050d0e010908010606021504060b0904051005060d020d0318170304030c0609030c0308070303061502060a0b010504 84
    0x10103114060360394044500e006992100b00008064102d40f070b100e80b401c8200030510f0f0407441c1e040000403641c0c28030640d024105141c512411110300c602c800c0024800c1c3c80c031403000030003418000d000c0c50340b00d41c910700207003111100b9400080c175010003688125010701002540629059101e00c05000c1c09206400400d80d0b4185540c41980340d50341540101540040416400d055668a8015000460300300c01914108100d9440042100100d008014042801c0c0d000000d01c1a1051040104680181d405802c0b54840c0c2c10729a11042c0c40030b00160340c5991542000000c0d6500c00d40307102d016a00c610000d01e10700003222008816900e00600451144504036128400360302c4c2c0e0802d42c482580c0c1482c1c105401401842c0d1080700b2a0b59410032000070503a15081417021400000030404e1b03030702500494100c0c030f9548001300d558881c2c030b0000a100010110381000055800009001c509100c0d08000c12042d0320707600c50540b40d800c03211030940182d21000a00c12260498460301d102d0501c2860603e140604 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 1761212 1250 1759962 1759969
    0xe04020f0f030105330702040b060a02010c09050a180b03030c01020a08040c1208070201050703020a0b010f0501081005030c01050c031207050909060f090610090b030106030e06090f070e07021005010b0d0f0209 91
    0x4045c51000340301d14000514608640c5c1e96030000c880007031700903e007a031039800c1100d00034004e00524800c900031920f90700000ca2107107005000701d01210910071f1442c0d4403801250300c4a02a149240006805100030300c0101c00f0728000b070001c1e014454003556103145e103191504188125403440e61010018525070b41002e004039505030300b00c881c41d58080c24440c3d0b03114190702d81240341c0641ca03000500750300d030018004200400c446900c101214005d07603440b003a81e25071300c4401d504103600d44100c41d45a408040b2180d904e502403800791488018180999091441e6048070344151601211180c0000c0e10004000c000341c9080c0c03031043c0e00b14005651500f420005180803030554903014201a11034122905840c3e0120b10034280341c07001e013055140507034a0b07582d10800036001d44200882c002450041d2000101810f03400075441c90000040801050b889150200c0c0c0d294084000e07010000f14002c00780d01400c42c140da030040500034042074a140e0b9403001030340e60303282c100c03883d00c00882c9030340b4010000319040d0356 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 1762462 1250 1761212 1761289
    0x3060b0307030b010e040f0e0c06090901060f02030f0a080615070c050415080708010b0405090d0203070303020a050c0303090f06010603150905090f0d0507050d09060c030e04020f0f030105 82
    0x1c4500340014200190001038031404080301c40580d0250800310342800d0459544c00840e2003d0441044405010010041281170f005460101d80c00030340c00d500401c20350f4403030585040b9507103c90066074a0005820000c403029402000038101140300c900900084e82043c0b804001c940c603031100c00c1800c002060303650648281d594031882e44126210303001801003082c900c02c204001c284080031982c0700f5030b80d108100d010f4458103102522551404002481070440880c0c3c2d84034070100c2c0e9000d9490440702d0384d010780c001d41050382414208281405011900a4100001e60103144004020425006910300092401805030001c10400d41003003803109401030000751540c240c8268280208090340c58402140c0303081c2070800d03408480d20600819880e083c1d04040101400c9015405484d80754030f8401090320720307070340074859100060b8485900030046440368610b400e03c098020000751810850480078401500404e0119050f80b030000010001c07460640f0701491109c000390340c94250504000c10000821 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 1763712 1250 1762462 1762471
    0x16060e01080c0d06060206040c0e0103020d0b0709030b0103030203030a1d0a030c02030a060c080907050105031302040c1709030c0f0105010501020316051908030a0f0509060a0c0504050301060306050f0703060b03 92
    0x104041c0401d001e109890b05903400035200e03840c10404e2a41e24207009644040c1650705880420034810089032101004501d28180d80d0094020381c0c1403030311a5280c50010360014185410021020380110006280202460081d0f0180d40150384905007a900a02124203140c0c1b41880e13000240548010344c000400c1f1080c0b0640c16042080c14810784d07002180c10a451b07848000c00e0b01d403400c401404074a070000d80b51401948010b084480445d00c0d04e00544180c0300550340c40c0c5210070601041001480c10f0342140b01c18071040d2a03c4803442c1780400d200341c11110b0680e1448060340010500ba100e85104000160b28048c0020090009524040020b52079218203c890740170650034114450078803400f0016100f03d84206000c40610002e42c1c180400345170400d980b0400d0031820a001b082c802591806460302840071500a80041e495040c3c01c0703070061146891a00521106010000b815a0280b140350300035401030301c001c241860080341004600324001c0c4184107044c90008107103e2070003c2c20503250720 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 1764962 1250 1763712 1763717
    0x3011104080105090a11010e18010603020310080303010f0b07050102120406020315040b060901081b040801020406030c08070e0f03070302040905010b0102010b0303070b0c0d0204090207030908060a02040302030c0405070507080301030b040516060e01 108
    0x25108e040082400c01c0d107192020401504501c0000030740c183e25500451140801d100349001d600d448105164691000380700f83d8002003e01c5109104a202420082400c14171945c00149060045006040d182d8411034042e0340c003513400b1040083c151404c6030301c20a181e4040f82c00f00011403d43c4005421170066002c030710f041100c0100000c1c070580003403400d0400c4079980c1c54440c0c0c55641d81d200450207940175000b03074000a4108400700070080c1c0074100e0700d40602d0042d260310210204810510a0aa00354010190702d44504000000540c4442c81403c054130700a000100d000302070f0400281c02d5501a02085002c1d6004202c0c01000c518101c1d16076400401d108031090f56510a10720b000040d0003180c200c103188510001d0f1a104140c0c02541d544221040801070751000e95903008604100c0c0110300c0083e40542003006a0035840c40d06a02ca0307170f0703c00e15500703215040c003d05440301c00c034a40090b001200d25950309000c0c00240301c82045a50045100c0000303084e10107040210003810320000d800050305 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 1766212 1250 1764962 1764977
    0x60e04060209040b0306010308070309060f080a0902010504050604120605070206090604030e01090509130309090209060405060903030403060e031314060711030703150606230a0c08040503011104080105090a1101 92
    0xc9a9483d03400034545a0401003c8401c3e550312030070100043d81c0809021030104800b80f030300250b41402081e0303000d0140b9503a20b40107820746c0d515020b1406000c0824040741081010000480c070350350382801400c00f4019420104085d041c071440c11208a6034041c1450040d58008410007068a0000480d80d50280d0b1601d080c2d805100581d00503900c2c083c1da0342040b44e02c80c451408100310307000110b00c24030340715019654203107100d43d95007048000c034030038080e501c2c1d048201040b0600c0a42441c5000700542503018084130710b41070b60783e19503404480804010841c141c00c0052241d211100211820000d0310311038842002d40c00017900000d2130ba1107031600041a01c2214903400c0d50381d07981401072030011078014444030100c02c0d120358002c009264602035000490080c0070342e10113002c00ca421501201e00e00d10070491610041d10001d50300c0d408058000c1740c03146030400c80403036262000c2c0140c2c4040c1c03800001064485041046103801e4440c01043c2d804160b01c44025400070519200300e032880e80b402804d0070403 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 1767462 1250 1766212 1766227
    0x3040302060d060b0301060302070515010602030d1505090408130603050f010504090501020706050f100e0402090126010e0606010905010503060d11010507080301031101020c0117010603151203020a030909060e040602 94
    0x4014040c0f81d884600c510102100000300755425400a1001611035400c1d170300141c203040800d8108103401c2c003400b0016441481108080c044030360240580b500040c0e241c1c010b2270343d0351001030b00d050b004a0f812900703100701141c5c1e00c8c003000310000c011026002e2401c090049241802e0f20b02c1d40018140701d001c1c410754441640d60140f250a5040b10748041d0080e00034052450320b1421008600320a0740c0003441e019403075900240d06080b00c40058062580140742ca4890b034030304000003e4029052403013446500c0b03001094903d061091003810f060001c400041d101c1450070343c0001d00050601c0d030205040c41420803c1202c1030752640c01d080095a48084007800010303000f001215039000d51500107064010010011080c448400a080134003042642140c0302c440c547c100441d002620004644140308001d001403020502941048001616890180c80e065075203401140410400c02c0050380503030050b042c014185503000170020041c15800c101404a24030f08442e10341440c50082c4050706240d804078080 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 1768712 1250 1767462 1767487
    0x80601050a030612030305060a05010504030f06020703090b030f010305010506090103030c020904051905010501030c090c08071d060a11010b030706020307020103020906070f0c0e07020606010f05030402130c03090c050307080304030206 102
    0x1e001810b44801c0c0d0803482501c42c5005070003410251a00c270320960040744005072540c0b03d1804c80703040e01d52180e04840c00030301b250390303201c083e420420044050210480f404510304c2061301c095482040c4000c5035160703d524508100d42107400141100380100e800350010302c04030350018509007501d58144d4940850350381e5401e08038104603c40180162041801914000b03001054000d07034161b900490b41c500c115569401c00e10b003240d05100441c03002c910b003a1f0000d10b804c0c3c02942011070941160a016055400e0140051b4455000d0903202c00811090b120487c8074100034400d0a190f00d10580c018101c2ea428000c01940d00c0c09000402410950005210440e513198013040d075841c3c41e407000d9407580c4500b0710310302075070708400e140503980e410070142c0e0004151314030005d502c80c054101a100c5c003100e420740c0030080390389900c001c20a0b6000010704070386085040c011301c5103044540d0581e400044003449403a010fa142c000d1a402640700791703c000400c0c407901c500030040344c0840fa4116802640e424106014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 1769962 1250 1768712 1768721
    0xc0e0703110a0504060201050906060d0b07030b0402120718030302100e0a02040c030e1005040b010e070c02030d02010515060f04090203040c08010501030c0e09030c0a030807050c0f0a02090f07080601050a03 90
    0x10784000d40d50114029160036041405441903503100e4009009039651825110ba461104032951540f040190a0041c0421900700c04250010824617003c200600f15801241c16603100c0c04015007600c90395802c01c0242ca9014811a4102c50131003400d0a07100c0c91502c00130b684119100146102969400c200d4030000c404101d501205a8003400501220000300400b500a00c0325a4031544940110608003924414520403a80718590010a4800307503400e0812510f24110020004018014a1843c2e000903070340410050b50b4945450703002107513038946480b100080205050206004400502621290840110549040d1191910300680360f5441d07040107040d007900d5521800040d441e00c800031062000c4001e41d9800e403201107403244429120401e45a580c3d10440c4002069030b005100c40d034001a110301b80803138000450b894001d05043c044003e903400d1846100003038603c0e900c142003803421420820101a4003034030030116904d16103814030014140420080800341040300018a602445000f50710 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 1771212 1250 1769962 1769981
    0x5160605130b04050304060306120302030f030604020f03040506060f040903020606040506060906070503090a060c021f0e030d03020409050702010509070605092403091203060a0306020906090303030408070c060305040c0e0703 98
    0x154082d00f420542040c0c1d8403a8024024000020309051001c22000500221140b1041c0d15600440c90400d4282140d04160000743c204ca0b84150208514108000d00102031406640150f0181c00c0038140b070700070811075490a06526024904004022001c0b98010520552041c000e49004c103496440800280441c4900803007a60301c00c8011401c40280f01c000030151940050984940c448540c45410079600c280300c1c12002580904180040c5030601c4003040010b8030410fa90074290b22011680740080c2c1402e00c114510400203601040401022865015060700008180001c01c1981090b100040d01c44416000f0350317050000016617481240c0b02c00603040110b08202000207070900c44400b450740b030b03a4401d90300f242c42c40c4207014603800e0300c00b201400c42c0c4c003c0c0401080010454619540c5034065001555046d81c0100140b00b201000d071024002907100c0c0e4410000c032a41e84095250086803090141c01c04000c062a01080100141c1c4040d044801d072441c4c00041c66003680c5248084004d03248442 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 1772462 1250 1771212 1771223
    0x7050303130b01060e090403050a0201090c06050702041118060307050f070b04020306090d1d010e1903031202030c0f07080c0a031808060c070204090201020f0105070507060c0516060513 81
    0x1c10800c9140c41c0d41201d002442035245402c181d0341c030f00003141d0028801d10140d81c050941004a1700103070040006114003615400007090400a98607048510b18007a44a54003183c2c000408c082185003070300c81c0900740ca43d0040d045040101605a018190034001d0702180a42000404245c2e058010000c2d1800c07132aa071015155284a9407504103014001990224041c0c800c14010414004010943c000280000c0d62000781d2801118424555030158013682e50500070500c1c000405600c40200c2820122841e04a91076038510314a0000c001144460003900114418002c0c0700c265404141166405036044810b2078460046041c0310002e40b1480c03041402c03511419070320304200358024001800f41c0d03421a041d2030740c05030344440c15615440121804a0001000c03c50340300140f030f2617400326a0103070040c4120340e50a100d05010b9403c441c4140c8121010030000b00c0e030602040b107280540c0e502d030045494103d08061256003241012010181c0c0200025114000079034652051100060820f4200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 1773712 1250 1772462 1772467
    0x507090e01030507030201030b0301020c060601030518060c090f0a0303050a0305060609060c0105060906010c0b01030807061e0204090606050702010806120f0a03081005040908040605070501110f090307060201050105060d0f02070503 101
    0x80c50b10f1642c44c0382c0c500c0200d01190409510031440d00d01071094805025203440540455580c91004400819008000d06500005900c810684620800041c1c0c424908042c2480c0e6400c4014200304a90014014003845107095007001d100107a4007030b081d1a03030034500c2d0802051701e8032064000b942a00035002a01d4200a0204d00c0981d11901504001d0042400780d0f0000c42e1900e1f410011140c9840c1b14002904159071040100000b0790f1350b03001000340d1401180f0014505010300d101c00c12542c1c040456070410703070f000f02d01404104d40790301c2408000c00303040c1072440c6400c0560340040d018800040c801841007084180200c07220b40f0070300c1610048000310050b21241036007440d011700506000e60300d4101600c859000811039040920400141c660030039030707083c103043c5440ba00b140c03c0d5201c8041216155251040010052642d4016145041800c0c0c01181c41da251034040c540350400d194800030443e0304004c01000917442e6031040f20440c4074440b40100300000c4506d500e402a20602d50003d1545c40700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 1774962 1250 1773712 1773719
    0x40909080306010806040b0a12020312040608090c01030c090501080604090c060306030309050d0503070f0f0203070605030405010f06060f050c0304050a090219030908030601050901030b0d0303020a020106080303090a02040507090e01 101
    0x6801140316000c00d803a99130198449505010440b1620310340981c00c036140755001c1c0103982c00006250342c080d200904440704008400b075800c0300c5410651003600172543c1102407205041090003864405803082c80e003003100f5805004000e200e24041d1094a0501036001c02056882d01d4603001080b00e580c100a02d2140e060396080000c00902d00e41c0700c180c0c00140c03402004140d80c5089002d6600e0326070020700039401c010a58035080d14152045000f20384ca0b13078914400000585080c80703980000d00c0c0b40d856030340d16441d250400301d007501d032030156105240d85041000d000d00c54025007660000f401914002d9280d15500e1356481c41c40c441e98001c60341c40740000d4800100544590014501e5114400015858101300030f400c3d4240d4010f214020b0500005000156181d40b294028100c0c00c2c1051502280c1410068081914080d81035401d0307000903000114410025024040c1c40700500d04c0303c000310710394038019070b02c40e8943c800710100a1040e5101c0d0301280314603100b2401d60003d000e00707440f0314080c0d596 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 1776212 1250 1774962 1774973
    0x106020706020c0a08070308030c070b0405010f0e0a030903080306010c060612030f02030301060e01080408090907030905060106020f060103060f0b0a060e030c06040e040204090606080109050133030b0c040909 91
    0x10a489200010f2040d1074030503589040078541141210209002008218215a100e0341960001407801400000510201c000f01c3c038082e56840c081e80c06030000040c1c000c4411148829200c81405005031984140010400284c1c0402d4120840742c0114840ea103a0b00c5110048034403031071010000c2c02140c10003101280307500b15591a034445510a486203982140d50000998403400244035803004100c0810f00c11000354010075666034403e1141160f107141090400000da05400c0c241c50040000ea40c1d03500c144100141000309a000d8281070000b4810f644000724038a5445c0014000204915210601c0d0700101f401500000031881c0c008080034601526004020045925408068402d215840801e0796605190301154142c0c0d80c480c050710740320b982d150248009481c00340800c5813241d07504c80000070798140130b1044805461043c1e00125801010380601592100003210042038107150040c0d542d4171503903000811080f030b54001001101c03555688000500d0f8021588800034650800054008000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 1777462 1250 1776212 1776223
    0xd02010b0306070206040c0e060d0c0b0a0e031612060603050601060507060c05040b030406090510110403060e01020406050306130905070b07030f031514030c04020c0601080721020103050606070605010602 89
    0x680407540583c1d281c81c4203e03528841664040e20601c0c0d8505c044c85014550161294044000340c2030310300700b6529549843d0b01e20b80307981c8003803042140840c0326069107034000c2d071110071044201d000380036110600b010700d04403006074443c803192100c1c145e0841c020040d550f04030b48011134200c41074072042d603942d0740701500316842903101f1204030381b41100308180360307006506071025100c203580a6400c655031036a079100201640032040d6240d01c03406410020766412405441102400c8089058842d0302d507192103000d8074100340c030382c0e0b03002c0e4014041808411f62110a407a403240084039081030000d01ca1900030010b000d502d074003070068000d0f0140410009003400c0140b00c094401d81d64486160ba250108800329820000c160050089a01040015120428403c1482c2c5c400505036070800c01600002400ca03484411010416040b0340f0040181000074422880100041c01440390549068061080080c40070380c0024140b69070b90300810340300e07100d030030030f542d00355901c40317010009940c48040295540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 1778712 1250 1777462 1777481
    0x20601051203070c030b070210050106031b0201050103050a030309170309010207020a0801090209010302060a030609020d060e01050904030801030b0408090301020a08060405011208040905090109080706020d1a1c0302010e0d0201 99
    0x6541000c20341c44550000401c4481c3c458201802407941410f41da00d0700c1250a0242c424021032088601d0381c50500914424103008010688000846101459480b440c4a44001c040000d5901d0100100081800030468100a0340d2500d80014102042e00d840b6041c3d1055001000c3d482c1808400c000c00d001d8158000d006240c000c03583e600c00140e80b10402c0d4240c4c0c9000d84001e4201180c40010801414008054080b07000c41381008100280c440785004101e80104009400b1241c03245010040d80c004001c245001d000c041d9100501c0f4035054a0180003120b06100042401b4090700000e010f01441c5029504040d40c0140259921207555000400301201032b50340794407941c9864000220480c820360441102030348862410b0400c0d2a09240d4001402d0041040c81e443d500d40032800300207402100107020321442070701c00584410300302d01004100e440c0c400c60707100a04925902c400c3c10796900303401c2243d081d8400d401301142140c00e2030124003400d41556000e0756441030720240d001182d019003064008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 1779962 1250 1778712 1778719
    0x30201090b0a05090a020405070509030115091a03060103030e010c0206030f0f060907120203041103150703060905010501090b030702100e01060602010b061612020307050303041101030b0a05060313030315030302060105 95
    0x89440b820801012a601912125429032081e09400c0041c00e180e0003150303110003581041810541140003007400c1d41d408640721141d400c8841c0c81482001c5091152460f004881510202d4540d00080402d80c0c8007010700014007489016407400d0450f0f0302c40c4c41040d00f1143d01601e1140c03241003100d0858401a0196030b40c03503a5130f011800142a41c10304040d51f5200e0256569064800003000200d103000f5400940140d409800c280d40807a000d48040003114038040a10803202e60324036080b10024100c3e0120340005031601e0a1500411160381d205141206071500b0382005556610345807403c2e40b030580b010080d0710015050524501401c1f1040d400041141c1e204d800070b00400310800200003543c07143e0a28502622442c18504001c901d40c0070b442d04013814940100c1c0d14203041500c800c3c5c55608101da0844600e000504004455640341c01401e10f80e490a403080080e10341814005162404010030542008000c10700c40c00a05120390080e14400c41d12030b40390395081d522810025104c290034013402d0b01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 1781212 1250 1779962 1779983
    0x4080318030f0f1b0307050d0302030901091401050702130b03120406090605031b0304140a0503040303030b01020c0d030e01020106030206040e0609010608010806060103090303090b0f070801090207030e0906010311030403020109 99
    0x40803030045012090240c50202400c41c0050144130310b40342200240c6030b150140300342c2c1d001154a031a00c028085007140030703030021500c0d44010000103050300915005010400140101c1d4403041c0d8212050b680038070f50495914203891a442d0085000f0088050b58551621071008426150f2a6100040c400d50701c0550b18071b542c59448001c1958030384410346d104c1920b040300c020311144400c01d1401031038101c1c6c800d0750040e00b4000e00401c100d142a4900400b034801d030300002000c008146d05803048400d80a800c0c000383c05003042c3c0c0300020700303455895400a41400102d100d8103106a00c00c0d40004040e65005226a49590700c910302074034480404c07100540200311000000c1000f50042c0d4005040751403ca0092a09a0b1904011405060700310000c50034592125014000104840000381c8950b0101442140c6494070b01070003030514506074000c030040d900c104002c0d0040382d404054001c1011056a449141e9224140120001c14202d030024035907000200900c003c055042d00030082d96030040d501130703c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 1782462 1250 1781212 1781233
    0x30801030201020f0118110102160e060405010e010e0402010c02010e0d050a0605091f15090905060405060703020c0a0201030e120403080408060a060e060103050403030605031207021504030c030201080a020408031803 94
    0xd0894500400400c41540200d07010f0f00000c60011f003407100d0040610607581c0801880c0c030031a211100d15006048180c5111b81000414105403003110b005100040480d5810f5140c80780a040000000d08043c1c10080c0b0389a64605590044500c944e40c108041c080c88401c5a031420314584410640300e01b152001e04047c0031a50880d000601e8a5001c0e00140b007036044107000308842c0004210110152250302000840010112030500c2445000b9000b6000342070103180034604942400300013001c80c001d0520505c42d5981c0084005504541c00390f081c00e0010b600b40b000304416203880e02d4609400d82450300050084104050301026104480007003040790b01d41d071036079074081e001d4841601904541d40c1c1110006034003984a070b001203400501a0a00207002d68a40d4003280c18039025008482d0f90050010701d610850614440c106d140000c3d00529a050905540d0f407120600018840071f810030030424089082c0728100e5044078000c0400b982142c1d50780540300da50584401c08281d480e8480d004154924 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 1783712 1250 1782462 1782493
    0x10f0b030606030c010c0c090c03090506060108010308040b09010207090207060e071502060a02090409020d0c050f0607020904030e060d0501060801060807020a0c05060307030b0d110a05060a090504020906070203010903080103020102 101
    0x340502c50080c06050b90803651300c01155044102e10f401d03101032a5500000074400003521030824548015a004260804641001403801401800050400045c0c3c401000421650002c0c0e80c143c5903140943d0703540b03c0c0c100c40102d01d008003c0c0c1012010510004501080117000e5101c840b5051900003a030721000e640c0e410345031098540000301000368206400040f16102c09500400e411200280001489900c540204850815608040700e0031201104180700034580002409030701e100c201c0e43c1700d25000180d40440c0b40c40d01c0c06000141440140011904a0342e100700c00d80b54001c2a0740000c1029680d00c00000b85101000c0c8104000f01d01042c002c5980d4a00c045110005c09800201070242d0925041c1132109a900062007801096038410180c2d0140c3e86401c240c40031180210514003407103e41e0020006117031034961007248502010040b5003201f07500251910b007110070440e401616018040081031030f521443c1c200a5241d4030f060b01c14400c143d0071180e183e0699000380d0895441e01005000e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 1784962 1250 1783712 1783723
    0x60703080609040609140d09080307050307020607050c0603040803040209010603020309032209060e06120a030f0302030408070204020705060901112a0f01141602060705040302060c010608060108010f0b03 89
    0x680058901000203160303080140d2041d4115104030800192280d250f1284404c00d0b08544102441e500300038003c0c03002d81d611031f01c110090108140603501c0d1054590720540c1c0d81c890301c44024007405011441740c1c1400028421080d80c00c1d4080d01d501e13620705e03051400200f00c1d0b0003168203c1c40b80c6a0390300041810342c031034420b82e0300c03800003d001035181000301416140b074007035603d145086a0b2301030840802c1003015802140000d240009800c0e10506155040003100b112545a0034001c0d8089200d0340007107035110b003a403c01c03c2c3c9507060050381c3e901c881c1043c40c40c500c240e05000e50014000203400c402c01000149144c0b180b054034000300155442034004840c40d03c104e080d540c514078818040991030180070750800591450030011103440c180070360000b03170942d4821a1211441000801000b09600e80b50542410040d40b41c8003a00c42c034038098002800500403030201900900d00865542100f8201750321030405081d000c01217a61641e9a400d00e94041c000a0903002c4019081004046403814001031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 1786212 1250 1784962 1784977
    0x5100302010804110f04020a020304140916080711160602010f0504050705041107020405010312020f0703030f08130605040809040609110a050306030a12020607091d01031103010209040f060302090606 87
    0x140d0b01e1140d100ca8903880c8407041c00f2030845600010703c0b8581c810694443c0300405000f2001d40265443d10318044040860100c2c10b45900e010b00306a00400c2000c181042803c150b14a40782007000c0aa200c02c0000c40b554a07030060303600c84a118612059520441e4810390104903070040e802407002440c2c6403190310a44000f03690060040c0d200207410b00c050318190b00b01100d00301c3c90841c000d05240c41500040c00f501c4003a0702c1551501e5000c10040c2005034107226481e00075400c00d008051703681c99954001d01441d42c20001d10708011104003c01c03442e5880300321404103140c20139001c1c0101e04103400c20100560000002610451030b04100240c011404d01441c80041c00d0049102d0514002c404160b4060380000c09680e414010724510400080c7e103000381c00c0581190f41d0040c000c6203080b1401070030716a0560801e140405068003108482841c4040080c1900d0388811a01801c800741c038082070181c040d03861960713401800e20340f80307900da0502c99002d40704807030007210f203c0383e251500390074055144641e52 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 1787462 1250 1786212 1786217
    0x1050f0a0303050a0507080409020301030507080607080106180503030309070e0601170103020405070903050703030c0215030906160306080d0305060406060e0108040803040f060f05060307050103050118050903090301021603030510030201 103
    0x80c81000480d0250f000f80600d090301d41000b61801c9030755916444260701503004006426400700050050100030085140600a0a00205850700340f108014102400520078542000000c017034081c820f40201200030002c05001d021a902ea04000e071445440d4070f124010b228050314808001a40d540c881e000340400c043c4000c690229690031902030001805008042500b8032140150000c005002003082034000d5000359100c26040005104010205102c03000c245140b1006005001400e0800f01d943c0340c029580c4412120540d0062906501030000c580c400d140c240941802c520510b609030b0450751280f4802c0b0350405c07810340c82d0300d4142c0f00d0607494520640040c60103000540029003581c000c0d60814094882c4681c004001e542c1c1900361443c0c0204191859201c0003070180300e0404008210152400742018001d641c1003000c020400c25020490000e2640c40d80081002098240f040301c0f00d21801400030b6555042001750010000b6820808400003454040000d01d0041c080f400c0c181900e605a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 1788712 1250 1787462 1787479
    0xa1d01020c061b0304030206040305060f0a02040509010605070f02031c02060a05091504030207050402030a02120612030f0d020705011d0f0606030c040c030216150b01050301080a0204090f080706021201050f 90
    0x502101643d02120303030303e000d540700800c00400035130382e050b010700011031040d80144030525000038100d00342503028001c03810050040c00706100e5540c50f01d104e00e040d151903190164a84016003000400100e404030040e4241c0200701d191a0b1010b8841c8064101d55600d07004c41d400e54a80161480844808a03061400e40e001141125210010b00e03001c190010300030300c1100c0200b515080003c00301d80c02910b900c200143d00042501c10359040341510380c0d1285003203805c00e0980342d4090aa45e100d00c0740030140c0180e4000040c600b0316030340b056810350301c444d50008000c0104491540e841c82000c0c1001c5020720040c89403071034507a0304040015006100d00300c040c01070300d80c40504100b440003a00c084001401816000e0041304d113103103d940d02e0013080d030340202d25412400d403032202a44103c038a03200c1d040c1d04000d010401407001a1002480700d402e603030f040d100001e040c00340d400e01c3c851041000070000d00c80c100004000e82840380c150058210309402c0e400303010030350740c0c1d031307000c200e1005448021540c003e00d11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 1789962 1250 1788712 1788727
    0x603010b0f030304030b0c040b030c090a150207090f0e0303100e0903070c1401090305010c0309030e04090309031118070c0201080a060302031e011b02030c0105090c06030a050a09080a1d01020c06 85
    0x20817190b01c7d0003180c1c0040440c281a02e4101c46545a0411229130b04150710104880543d41f40502d0710704001c0410322540f20b040030111500a45030501e81c02809500c03a21509501e1440030241d100042008080c030176a61a403d2001c54120380f6105440307140c0c2040d5400001ca9000c01001c42110146130b80001009516403a203000e440c56405213081c1181803014541c000008130348203010b880f00c000c8143e500064040300928015040c1d04000301c52a01481c5070031284c00c0026000160760068940080c0e0743c030014504000041c3d81d00400022011b1642d100d40c091250864102500e04442c3e07200f600e82e04182e03520b01c817214045406910010f5803603400340c040041411240c8041e080c41404000001c41da09002a01b1800161842030080006910024040000403030a105a9810002c3c083c040e001d06200040011240c1c00050070320301c0e40b69038034004580000707020351000e0400c6d58015074450312404040005028000c0d00c040500c2c241420002c840072a40c4040760b070624601d002000c0908200b603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 1791212 1250 1789962 1789973
    0x6040b0d09050109020414040b01060f020309010e0a09060b0a090503031305090406060302030f030c060109020309060402060d0209040507030902120c0108130201020708060103050106080f01050402031b060d0f02030603010b0f03030403 102
    0x10010700b5a036556807111240096107036401056400e03805070031700c07607030a04192400700d40e0010144d100c0410060982e1040808560102c1202c40c2c0e41824a40700000d42901300c0011000c0d05241e000c1e1190510b860000070f194080c0ca006071182101544401000c142c0d600281600c0b4400d4408c0010321841d04c280600c02c031f20342000b0b43c68000c0c0c050140010390603241c4c3d0209140c82c4c01840ea200e00c540c000b1425240c0305604100d4280504102c030000e60440c10b080910a60300d100207400288180008035014603044075a50654004400003030040c4018207007244007800038402c1e8102039008801d0321004651100000900e1244c269040e1740341c4005a541c20800d9000a0f8190b00403411170181c03e500061158003046114061401400001182c0d80762606161a100d40d40e100306a85904143c00c00c40565408200c00d004100c00043c42a011008500083d00a10503888030f24200c500d02a0003481d8180c05901451050501307400800c0118030f01010003650703038894500c040d031542c4200010300c0000c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 1792462 1250 1791212 1791221
    0x6020a08030402061605070b03011401030603020f01050901050f030c07020a05040207050a0b06030102070b0108030309011401080a03051b010207110102010b04020403021507030912050105090d05070503030a050702100e0703020f06040b0d 103
    0x14200c40174100301041d0741d61058144003240d4012410004040010f01188140300502e02e0040d4003401d003000054659404610742040107803400741401400b0503030003041d902907800c031091056821a455900e00d0300300b075104116040460241e00400701558003080c941090320031a04840e8024005010b050741c1640c03240c2c103180c8028100d68265409100d802c0001ea1005c065601a00d01d0b00046c603120724000418508440040c100c8003290a0400010005400e0203e11003404c1350b01841c0c1a551030650400900380c6513004803121030a50b10003c1c000701130000e11540d400012001740e00a0144480745820001030f0700070341c0000f960000c080107040007444100001850040c2c800c0c00c0001c0000d96600c0c0d194160421540140ca859445000300315400d0814001400d00c48500d042003410030b10540c440f203030b60740001002d09007842e03035400204d007405000f044080301c1e00750340c03010600c103028030101c03110f484601c03511040380100c0380824555894036003802600d05544035100380a04000c40c440d495409403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 1793712 1250 1792462 1792477
    0x5071703030f0601090f030804030b060406051f0203090a14010906020705010e04091406070504080c03010504030507020105030a0b060c030d05010b0c03070b151c020108060102150109090515090105060a06020a0803040206 96
    0x175044100140c0341070f01030701081c01113000395441d5496a2840c1080d0351820401401c4500c100e28000040c0700503a20803c0e10b1012502e4011b5051824000301d000f60b2552041815041d4021070310040011800c0f54040c4007291800f00b0781e5000d0f081c0b5230703411007a60748a004e8054507001c43c03001201c03480e050801b680b00e141090702412040d680c1e510000c0c440b6003041e10544130200040e0000070107102452040014032060350003075001b003010780707003648004005000e10f407002410001c0000c0890b001e8001d5402181c40b00701c0003000d066584001c54003c554039845801408039440c00d103000002c1d110614401d0b120303041c0c4401c01070352801c01ca6982c1e9043d50030000742140004000040c0c4201c99440d8500c0c807180e8403e010004d00040081c90001500c02c10006041d141158480394403215000000320072181161128070000c200240d175450902d0500030440d43c0d81c1c1d10b070000c440c10000b440005400142c0103800c10f8450201e05d5840d0b00c0100c0c1c880724040c41c00f9080c803a04101007001410080c0040810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 1794962 1250 1793712 1793717
    0x30c010c05030d06080a1a060303030c07020301020c010608030901030605010c020a05010f05040801022704021c0506030a0506040803010609050303070b011505160f0204060605090306040803060103110c0a05071703030f0601 97
    0x80c078583e00c0300c07a4100c0d01c1c2034121105e076074010905a0204040c0e10a44a03c10513010151401e0f0b15100c80002d0ba2444010001220808007240e0b40f011520300b5010395005110101c0280881900d5006030b5549801c000b1520b400a811310030700084079402290600e1000b60040c0c00d2072202400c1c000151a181c1c0c03942c1c0301c90704014081100007034840c804e01c040d045002d60f0300d2600c4141441c00d101c0314007001381904014851841040240c0115100c49002c0a51106508012070543d4407040040c3c00c080414801a2042c050361080200b04181c480085050f0b8000b502d509804503201c40a00daa2802804002400715075000c00500520400580c030900c2203e0741d00c0c00615105108a194034a006007000403110100504284402c529190082c000640203038030301507041103102d10019a507004058009401d0410010114001340d01c20742004000c00728102c07040703944643c1101115a201480c6100380c030280502800400c448150a603010105132140c401141580c8030b8000e80b40410340094070181c10f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 1796212 1250 1794962 1794967
    0x60e0615040e010303050a0206010902040e061306090204060302030f0f0106050703050c01090804030f1101050903070506030901090605010803030106030c02160e15030d0201020a0e03010c09030b0a0e0105040c05040c03060302030c010c0503 104
    0x104280100b905502031886981c0e0241c5400205001034070303040041e000503a12038014403050000c1c01c0c0e4003403031540c0024202c5c2c90920001c81d5148140091015420104805000040200d0f000380c2540056020310042c102d60440b941c0c2c0c2180b0740c1d600c850280600c42c00914200950804644034501521201c03005100000311344409135252101540507a0045a0b009820303180c0609011010310040c07a0b810f0282016460042d603000042d031505064002c0d00d1042d04007001050060034250b000c0302d081d41c2d00c03600411a55840301a00e075036a410034807845000a0419a07441d411600c0443c01580c080c2c030b40d121740b01046040062442c20702400510114010640804048803960304100c0031a031005160001a61807905000003010003034200400c5003e40c1c18840c031a814264040a10011030343c0090074880c1c191a641d84c148080c11642d440401d0560a0105204c1448002d2503c40f04441089a0422264201a800741d050f600d1910000c1d506810205401610b5401020001c014a108106603071 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 1797462 1250 1796212 1796219
    0x11211030d0c030e010201110306060706021201060903050607031a060f090907030c020c0303030f07110a050708010b0108011e03080307140d050403140408070501140c1906050a060e061504 82
    0x70300d04412000c0c0340c0005921041c502041c50f400079400c0212038000e2000340148920307201c541c41c0500c405420300b0702440c0c0014101083c001c841d810384246194003055011556541c0300000c0078032519010640c0c05005910100c4c681034002d00c29122141ca60300500100c02e4001c03001c024042d0845500008a40c030100009005a9100042c0e58070451094400240c003141d0080002e01e00071700103c015019a10401c02d01c2030340041010341a078005440d14160308002c4912032800c1c20025a41b00c018824801d02201140c0c800f0107410009100500703a0307401100e0ba0762590170074030b8090000c090020045075107000f030005c20200e03002035600030040d081c4800d44124110b1807240550100000c140c1050b510020b000400d80d010340703401d00042402c0035540c00e050412074025203035080c921603141804030010f995294051260280c803610501407081d00c0c0407035150f081009400d0840e40c0b0445807146060000344a2500034403615040c0c50580a284000741e441c031083c0418800c86100e0345e003205506000c0003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 1798569 1107 1797462 1797469
    0x201060305060a0e0703021009060305060103060b0a080903090a080109060f02030601020303070309020102070e0c030702060603011107031209080a050403030201140103020927030d020a0e041103011211 88
    0x41e01d14204d0714142d1134404560320094024054200c070100382500466400120b684035103003800340c1d030350380c8e001181211034900a040009105100c1425494460f19055520100f000c08503864050700d40d001507103180c4c0b540d201c6c2045a4495805504100c2240210040b1300d040b51010340c00c40c20002d00103500c07030100a10840400d82e0f2103100703209583c401c024200040c2920150b090301401d040124000350f520803901d49000d03110301d4022512500b014444c8403111054401301c24101300040c0e07011508074082114480d1171588509001c0045810600100a001490f4607100c1d5184d14500c0c0207400c0d50000032080001c2d07800c81004001588940c6080d5912a02031041c0e14070b42c000300000591411900e41429032035100c040703035201c02055170364001c003095445512070800800880b400c02091347d180414201c038001c8180010020508042010001d49121701d0781000c2c1d43c100341010 = true := by decide +kernel

theorem cover : BRFrame.Cov 1618712 1798569 := by
  have h0 := BRFrame.cov_init 1618712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 1618712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 1618712 ≤ n) (h2 : n < 1798569) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
