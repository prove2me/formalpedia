-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0960
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:30:42.123635+00:00
-- url     : https://prove2.me/submissions/83e36599-792d-45e8-8b96-1d3895f41efe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 172482014 ≤ n < 172661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 172483264 1250 172482014 172482029
    0x10905160801060e2412130b13060902120c03150f040305090d120e1017041e020a1203170907090906020f030a06050109050321070204022110 62
    0x600c240511154030204550441d0315610304992140c6048001402014050010000c900c0208280d15042c5203003c018003500c1e1030508036101d40350380c0c3c00c10052441c80b2014004100c4103d5000243e104030407030a60b202c1c170351f000f0000040d60503041e9010408503020000506e146900501c507501c0c81c2d1904110060145076101c0c1000740c1030424070603122840c1000703800107040c0304e808210392032240c4a50b03004d0348c00b080d002000c0c0422414a45009042c081c4800c010318010400318180400d0755000705000000004044003014451369540c480035201d141c6c00101305080b40c0d50300074810150341c0e80c070b0705107010b0038148242d4100d1160398500078140381c0da2104a03400c801d00e81020000035581c00300340f42c0301b11007903201c000c03800300c1c1c0a00c2c103c0024400c031490002c000380003109201d44030070300794032080c19607500382c9808c1820383e1100b0402d543ca480710441d0fa03d6040542d0007400902d05c416010340549840680b0142c20309802882c2c014064124070511600845608104400044241500c0005015a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 172484514 1250 172483264 172483291
    0x1109060d0b03010605040e10050402061c06210308270708031c060605041e030c0e0406140c040b0c0312040807110607020603041e020312130509010f0510030f020d0203010905 76
    0x1240040c0d1203232011219183d80716070303d20001d419911a64101c42c4070a2507260311100941840d64042d00806060184440d60102d4080d600d003103046200020b030095030540c56082c0e036652a05d0f1207840304a400f82c518a14058492040c0b01d00074810013807403025204400c090745e200c070501d040b4101800005440781c2409406c080c0301b00721241d00401140d00f6540c21000d140a140c0004070b40c10000c0d12250b00051411545100c006501c03000c0044a9001d03e1050034180800b06004041004100054890710200e2008100412040300a5401130030a511924103072410704888000002d5200d8040f80c041c1c0c0c450000044200070081c80441a558a9000701e5001d4140b51003500402d08038000240000c0c260544400e284400b5140c0d80741c0b000420b81d0080444240c110940220540c1d0703089122000c0481520b2807000c11145800d00032141071b01e02c9020700d41c0381c8a18200402c005004000142d50915548800040d005003c6000401c1e002c690785d940581d90354500641c80081342c10003041007054800 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 172485764 1250 172484514 172484531
    0x80f100e15070804080c070e04060b0904020901171c08061c150b03030d1e15120323040609050f040209010c0615080a23060f01091109060d0b0301060504 67
    0x1140c0d842650410b000c0d01e0308030400d0b6200e103060440c91050b00181c410512810340d000a4400070740c20007a115910841c4144280c01100080c0041c00c40305a400079807140c07c450060104100c08500c0c020031020510455841c3c40c4151002103c0d8016204a0400a4911000c012a600784144000c0c8070190001300ca40c100a07564540c091200415421003c1c0c2e65116070780d0448541c0e082080d03030b8203881070711420003c145415018000e076885861200071001c0c100450803081341260640c00084a841d45100c03051800f15503400c0310031260046400c80c0900d8250580d4503c0b481040251020b001c4980301d40020300c3c2440c0c01c2080103242034018901c00c43c010048000c499900c407200c828000e5000c40046480d0701000d5510a255541e038001c0c00440c89001c54100034409030541c0740180c030312041003010001d860320107090744175001118070602d580f005d0f070010845101c441c1c0c04081410701c0b0044581c01c0105000c000b07141507005403205003016417500540d40d8607160070300c40c41c8020901103804000250 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 172487014 1250 172485764 172485793
    0x6010c050705060f0f210901090308010302040e071a0703080f09030d0c050c030d060f05040507021c1b03030504140d0e090406330e240a080f100e 64
    0x755103000301800707490007150701003000100c07a0035160710030074038038071140c49581da00301c2c02c085c19506030031a00307103a2119004261444018810704844680550720262a607086400f1301014201c00f40e540c2d8128800d00170009292000d403010100046113040e1016a6603400d801c0c001d1882c3c2c405003502d010022950103114400d800002203410f4151100c2e0702156005c050030082e42c0174040c441301c1a509001c0004d50b030840341019030080081c1e4a021140a03a02603c440500c01110411145a809640032440c0c805050081c0301e90588003c946217031403000c0907083d038070010080c80d0719503080700030a4580007800100144401030080488050004010340e5803159001424400e0002c050b5004944003000305040c402d00d03030003819150140c0b00080407841003803490351003502d500b5040c40070102c0740140d022820038808a007050082081c0105803c00c412064203a2050420000c2000c0e4070424400b00003e00c20800d0000d4891810a03001500d0b86210440040050310b40000006000c0d412000c401c15410 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 172488264 1250 172487014 172487023
    0xf1801051e1003080d020903010f02090f060c010e010c21090c050127080a0b0c0301050901030210030f1e0b030319110f011401090b1c1203020f0c0d0806010c05 70
    0x907041050010070644441c18a202c2c180701c41d0300003034400d010010b4041c8003000181c00600102c02c05070003c000c3c8140c1c982580c2c040380600b99045502c419040c0110103285484005803402070016800001d14900d09240325003140c004580c0040030034000e41d102e02003000200d1071000b4010008005202100c0c2c0e640e520400301c1894041c00d811320600004030020300c0c100c400090303a617410612021000640b00d00d50141e64445040d0122201840000007400f0a42c003281500d0403907001a00c0d0302c80d80e9003036900b04607801036545001410103603265030600101c0000c0c064110034101c0103400342070100300000c010055a101c442075a0080d88100403e410104c04134000007039104141c508809943c82d82c594080c24540c4400c240384080d0b081c240107054002081a9060488044190400c9001411f401b406400d0307588200c07095003075030281054004981007201c10705070701d081d41c5001890540344080c6140250808021480207030301262080003019001414140c03c00002d007441e400b444800c2c0d5456542c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 172489514 1250 172488264 172488301
    0x70905180d121d0a110a061b020f06070209040f0606050a030f020d030c08040810060909030e040911120304030b06060309030a030b031c02030306040b010e0f060f0d050f180105 77
    0x40a83e07604040c0901c4040440503010a550401624400390103410300c041c00602c0310300078520540d41d24200040c21805510410940440b41c400181004d00e5130f02041007450382054080d070488000c2102c180140d890388501482980300307810241e2803038200d0400741c0880e0081d402c114051010250180046003407054400c1c0a0f640c1122080180c402a00d802c13603000200345c800134094180490042030048010440038500b0454090800c511070342c5503107920941c1d44045020f0302048030750300710102c1414140c2103081d40500401d28050403070703150800f241401400d144540c5140d04041018410002d41c41c2d08980c008a04507442829410000240c50302c0344903c1c0341000605982c1d044440c0180c5061080e40328151000c4401c0145101040010b502c0382d100b00c0c2c05521507843c00030902001c0d8082da070b50320407a220190550007086000303c10701038103500c0300c0a0706120780800d010380c40544d0850b0080e81d01c0740c47e80c3c03c5100e24a0a1082c2c0c18084d502c01c00c0750000050b41044100000908942640da04 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 172490764 1250 172489514 172489547
    0x201180b061309080307030c030606080c1e0406020d020c030303150d0c05040203070f020c09040c0b0901140408010603021e0303180103020c0f0115050103090506010902030402030f070905180d 84
    0x20240c41e034000081000c00101801050541080c03040002d02c803c003006103116032910b84091281c885208022402c5070518020140840c003900e0120729540c003124003821440107010342c40d2492688814400103103400652101e001a400b04006802c415410310600010300c80640003141503051005026460420420b03d00b80135602402405051100c00000d01c401403002410842d5641810382009012200415040c005032241d6410070300380e410204800c510964020100510740342c1403003035960351a80300881c69810400c140d1404034400a001c00144014244540006402461441441210418500481c200607800350900d41a0b403008011a0003100b03414208811038103030500160001e014011103030005103c0e000c501c4184510540c040d0503560102d040d40c43e1401c0d91440118140c1c1d4503100002e00541114004200c0b10840e600075607041440181910450140c030b114452a048a6500c41ea0409440320180b110030400388100326105441e8901800c0309080d440b41c00791504e94450314400c3c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 172492014 1250 172490764 172490783
    0xd2a03020c160f03140a02010206070e03120f030906010b0a09090504061416020f0c0127080604050309040b1806190906060908010f150e040302010906060b03070e01020118 75
    0x2440c46014041071040005400500000c1e64a41c12501040b41450100300c90605c80e11120521031040010804c0305581d05070b000744501e507113a22084510030300312125103130144180740d05204244140030103040e030450018032264a03031078041c1c0d440e444d209041e07001451580007000604007a0703034002d068030b060390804100441d440e250740c900b0200601c58242d401880a40f284288200540c10814260704550301e175080310340140321400310a44407840c0c56119400f00f100c54044880356100c1409051020400d5070200700d042c0c1e0350345c0d03070b4606240c2c046a080700c0c545c05c005110b01e494034280c8a0401140401d407461503020440840d01c10b1182005850103100d94045010f403000c9000000c0b030b400207020020400d0041650b60407024020070b946020b10f180650a200c007281041e00c0c203100d0000c10300007103240640706900d03019411020400190041d0115501e50800e4000300f0b186014a00c01400580300540c0d50f8a442c081c000d1090f114403c00340c0c116414a8079075040c0d0b0303043c0e003140307a2200d4104110700e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 172493264 1250 172492014 172492027
    0x5060a0527100b0301120c090204050d1103030910181d01030b09160b07020108010902180607050a0602040e0105090603010507050d02090303070b010303030c080a020c0307110d06050103080d2a0302 86
    0x4020100342944500c80f940400000454052000c1082042d124846d000c0c0002103622000003805a0045001351508100c030a800c000101d070921021034501c1c40040c3c00d0340d144c6544c030f402098615500380034110104104180001c015a0741c1c0da4910001e00034004000ca180d060400b01c1500d4000620010b015403603c0c40100d12040c0d41400000c102c01414452041c80d40c0c0e0380d0451030510f4014182c2a408101c404000080d42c0303076180200e0303038406026902038185102e404200042500800b0b0103403000d2240441c40c2c40040c420384010800f5051554914050b90700d05803c00c2181c9000426460007a418002445007003a0010280c41c0140030224000d41c8031402200881d1660060020207401c0d81c400c0b800000c1410303055840142d03081000e40e1001c001e503840d00541000d912420b246d214840d03000f000608042102d4103207028528000512441801401d80c031420140e802c2078001380c0d4500340001e042e4405a1141c41407200a20487e4107240c030f44004003411901000c18030b900d04040c5600080c84 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 172494514 1250 172493264 172493281
    0x13050403110a12020106081f020a02030d090b0109050a140103060c170a0606090f060f030504030905030f011e14010b090103060314030711042c031603020105060a0527 73
    0x80340d07100034101c0c11540c0c1c508550501980071016200e10700055440d000006c107000d000400c65030001e44003940740d4600300c0306054101c0300a52010b054801140018403404003180741c0c134011003450601804401c002541480d0325071048440251004200c58508020412000205042141101d8011400089402506005880705104041140c1c0e424003c4010804040040e61184040d65001d9940c00d880c10348079403104510113564041d907400b06882c9a502140184079401a84d4080e00c00e00c2c124590fa07903203001003841c000c804503030040703e651a000c0070b030418000c8a0000c950580c040303d0a206505180c043c10106200c10b02950265035000203074039895034041e0308400000c41d0700110302101c12601c01001030720ba400400c2d00300c602406110b4030401c545000c0c0030303202c400c007006500a481e401440180658400d40d000186050f40424802170040c400c016040d075015601980011a462424404101d0011407e0304420f00c100c6804800e0348000160384054811201088071002da1526010003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 172495764 1250 172494514 172494527
    0xc0601060c212705040c0c17090105041e0306020705240c09010518061303050c0a0311040509010914030405040e0118081606060b0c0d0206071b020f0a09051b030613050403 75
    0x4c031303420504241d003011205600c40c03010402c00d4080c001440c6071030300446101407203205a0220900240040c0001e01c8030810403042e5100c3c0740030004e03008e100507642c1c0d074036203080c0d81003036030300341c980b904020250280c2c9802190780c49242c4151000b1001c90740340c4018190528043c0030315440c10003030041200400c070084201a26403102d00104455250007000c0e841d01c01540c864001220640101200c1c02e0302c0b4107105100b20240c9511141c0d00f0701021403402440014000100040020741d210200c1c0400f0503a48250350700c0031281c03100515500c3d400d10052100b941e105c2c044801c1a81c0c9030032000b10007518840320a402455101881d19601d0903040d6810844204990014002901c1c3c0400082c03070102d05030080c84084000030950f1030340d9180141c243e03251101101c032200400c541eaa040c000c241076001c01c90180f54402005007201008400101341c01403141e41107802070a50710b03c144103810b5050803140d40707804900448185035260400c040303040403480d41480411142c88c0d40108003018040e18 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 172497014 1250 172495764 172495769
    0x15110a02120d12050402030d080c09090408040f051507060902180a02030a27020111120d05090708030301030309030b0406020903150609090f030403020909030c0601060c2127 76
    0x20301407075403811100c1034191214032403103064012410221180d054034025006280c42550018094903a004400e842520030410003410325007a8030b020040c2d14419541c1c1b07040c0c18019030090000903161800c001c1407403460401908454440e408a005100145d0341c4d02d07080b144480d41c040700c007080701c4465101103500c504103002c0100d800103d001c1002600781140d03000c0c5201e41d420311000e0042002c800c51800c94040929102d410784050302e00400b015500514012a040d40208100e0740803904a4045101e240c107c0f0920702c401c6500c0d0400d00c0900d080800500c0058402800507614551440d64041c1a01d1010302c4001d0207540314030700040078450f20740e042d42c00052002d0300369032009203002c2c0c4000c1e02c00c3c004c0314107500c6400700070301003440613400213000700401544030010361809007190208007061200800c0845284410801c41d02d0758001440858002c03d1503480d141704051301443e00e000110150354000c0d14041341e17000c040d01c100e5070007411111004010034884110a0000c143d0203200507280c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 172498264 1250 172497014 172497019
    0x70320010e0a06020f0d0c21052203020a0602060c120402030709091b09020f09060702030a12050316080609070e040902030610030c090b090601050c07150f120615110a02 74
    0x381000400c1034001c208005022100d201ba558104040d542c02d81d03005440140103040e16411320040c2d102180140c038202c4c00c01a050400d42d0500c00410f81d601c000c040d8400c4850821501c0e00030400c01c50a02d00d81d2400904800d00141200d8685014100f90078010104024000c0c03a091000c81c0039920140032680160445450600c4209600c0c144803039444001400c0d0000702e5015000010490024070036100200c00c2546440c0c50300200d5410000b99800000c41a07034103005414003080002c001e191542444103c9450351030f103030705d0180e15104001c12400103000c14400380304200611a42c40c600540c0d07000a40342004100b41003034201017002071840b610003d41511444042c092551a060314880c2100c0c4140143d000380c035114407503041070342d1010350700c2e507041051480445d103a58020702c00b408000442504480009654008c110242c2c0c8a5401500214001c0841082d8103640100303e40ca68410075034090221503d0001801c0c042c0c0c07446403c050802c80d82c5695058000c2084c4050003c841c0c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 172499514 1250 172498264 172498279
    0x417070c0905190605100c15020307020c01021c0206011a0c0106080f071e05060318030d0f060e09060606031008010204090c03050f0106050301030b040f050607020a03030e070320010e 80
    0x2203456810042806507102c0480c2422070b0529503040303401c4d000301c0003510300180c940052a00003c4081d11142c4080104844295071a104548079455500c081c41c86034007a039006110305114000007a05003e820b64081300200740c0131340c0c040f05032a00000c1550446030112244041d9074000a68031100f4003c000c480ca155500f00200010781003800200303040031000c12010b4801040d5912511300d80d4404500ca8409003940194081145240c0350007e1a407049610317800e922000103110ba15802e40c0d00548807011480d41c1d40350014420260b0348a0b4401802c2a40d901154504004803041d40e40c4d1001012544625070000c0010000c05500030ba0310010b0000000031f5403075603240c600c0c18028001c2034084c0c0c000030f482c000000d810000100c030014100c40759502c80031701e564290340341e0381da181c100107205480c01d60300509000000362081290502c1036409038041c0c44440210b250041c1915584464507000d80d010100a1012a4000303a001c1d103440c40314100c1e683c48031444401600c18144460780641d00049 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 172500764 1250 172499514 172499519
    0x6060a0c050a0606060206090115090507050417010f1802010210150f031a0a050112080a23030a0c0e030c01050903010e070e1503070303170703060b1c0e060405060417070c 75
    0x3e600400242c0381543c00340c0d40c140d51261407681c225503034480120b403500300000003000701002650110b074110b80e4034a002442c068540f00c188150504520b101d100c5d582d950900702c0c1400c9942c1c0b00f5030001032003c40c51201035031030b0b0740c000130741da0200c406c1c0700010031395200741c440310072988042004010103017481c6500059640703017000c428140417109440f805200b084005407141c0c2140c800c0c43c0c180c40d40f800840300200c010f625104400d8001c09084003e00c0801c0081d4030320704460302c2c4840403040c110140c55540349820619841922002c00d01902805011120a80d03030f03a4020504c042c02010a10300162508a00f20000303000d4614454a00403602910101290140c034000d40706101d002003450401900a58205050b561905440301400281212801185481c61104056004130440c41c0c04201c058071561a14031580c40241c03440d00c41c05241d003080075140460700030500712010a01c0034002500d480c0d12036a0b00c9020040004104401084120346075048910030740b0300e001c1e000a440312aaa4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 172502014 1250 172500764 172500773
    0x20609010327022b080a110709061707050102060a151502030909010e0402090402010f0302092d090f130807050f0307031e2c0607050304030c1a0306060a0c050a 70
    0x506118103a002d8040510b14201061940c1984002a45140200c40184403591641c80e03586c0c204c0001c440030001c15200d01200280f08000b258050003800b40e000072414a0301948154241c0c142030001c1c215040350707404001b56030300843d40d564414004900490044040d10380d01e05408860b40010804111300d94205c0940d43e17001020304a031400654048545980f2206404c00f00d0604440003948081814001401540b0906502d034406407075040143c184000f000c00100b44610a107000310304440c00910403e1015102c417200c4440d800d0581d428074450600e0401300c0d05901c1d008200d00325982d4085800002c020182c01220324003a0442c0503605c40840901142e5200d9009480560020b01140f50703c0060000603010b070002c4189940350344086801c1101c5001004140901541c0601f031f0011419800d03482d007800a00100c0d20400145070b4603400d51400340d82028068001ca00041c1c0450040e840c41208541101d8000a00300e901548840301003000b103910b0892020000e040d03000d8040d5820401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 172503264 1250 172502014 172502081
    0x504090f0308010f0803070201180909120f0e062203080d051b0405092703040f0f060c050307030c150906091106090f0f120f06010e010b12040206090103 67
    0xd600ca6030302c2c01416680c070f079241071640807070f03014800030764204010000043d0300030704000840c024141c0c60045a2507035030748820105c6000c485d003615992504012410659440400d440e001506400e1804540e81d45134003080d124056a0014007215200c600c2e00d40c2407a0706090a00011540400c3c1e09580301007000e00403018040070b0340c80f08902c50107002c0c40080c030f8059006440c01e41d200940440d150b50340d403171484c1146075101d100b54103206080c8601c2c40100d2a041c80148003600d034030032881030000e21f840114841d40550b50700450400001c1c4000c0d800096001c07040303030203141c1c00d40b030306000c07050450506030001c00300d03020605103e0346411158000c103e00d0b50080040540a0241c0c01c0d0400b10b86401d01805d84500d102321541715983d80312031001803030880c1402141c0e15016142d0f1702504905c0450a2419010b00107032003040c0d004c1c00042003255071518400303000d40524107085041c0318611941110346140608003c0c4a4400810042041d03446588150404210002c14500100302085e000548 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 172504514 1250 172503264 172503293
    0xc04080c030715050904110309030901091d0106080705090a1409090c0a091e140103120903210e0d060203090c06090319020d0b07030614100e120106050409 68
    0x49010300442402149004074681040320400014040441c120721422180c82e4040341d4501d07800740e03840d040c80251816620195100310040b000850751602c1220000d4180d000700d5018414014a40c2e5a010380c60643e4040c460441d8501c1c20b00c0c041c00e0310356107800d480078020042d650f500500d040e14000f03100710f0201d08440c6031010030740303810700f20b901e4441d211526030905403422074020018440402c403204155121041c204035404508200c00d26800c4d400b001d40711001c16031140542590018002c1c4036014010001801c2c140c11b00020203851030f910540c03a1103a0846070740925100311030025070b440c021105d5540d121001044021810024500103000f50010340d082201c0344a8080720203040c0c1805412500b4100000b0000c4c401c0484150011a0304021220100e0b00907840303101c2c0b50001401c02d01c90600400c80fa0302c012810a0170651412810010701c51140d01c01e0a0140d036103c1125003000c02180086010340380c006104160340009409000e440d40310302d070000d00e00420750040c40170f40c0510b00035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 172505764 1250 172504514 172504529
    0x18030b150109060e031c020703020a0b09040605010503011a07030905101d0312120a0204050a0b0a02061b12070513090209040606030b061c150b0a030c05040f14030a0b0c04 75
    0x2040d2101c508130f88206411800580561110070358504051440828a070f000d41c00c0d10450f1845503c070341c081703010070314a513128a82c50100410b0040d410700d01401140040c00c42844c000d4115850001303102500d1000341076600c080000003031020245449054094050030014111311085060554028103501082501110b49003680114240c42d2402141010304e03064800320440c14101815110030718104054500e21103240d00308000030310790301c92070000002000405016911035078441e00c041d040c4503000342058401c48002e0741514402043c0002d80d00991a0040c0305d150a0741c41440a9840380303c1c418401d07040750702d648000a050450703500101610741050310140001135507400240d054503050b00c5105d502101c1800f10b04010040300c181c400550240c02c0010034a46207910048121030f03540c0d00450004100000c00007682a094003440050500900d0820310b0308d403414202d841d9403542805030784040368540681c20507035a01003044007111074010455a54a061103a10301a4540c031500c01c509 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 172507014 1250 172505764 172505777
    0x305030a110615041d0703050d020111070b010b07030908011d0c0909120f04090c0f030b0f10120e01050906060109060c050d05070f0f0308011e12020118030b1501 71
    0x74040804603a4501031080b18401c1c50342c5605450802c0b0180c01c6211110902d10440074082d00b40c0702040005500550040000c0c0551010640c0000d0a50f8094150300d9a680c604000120000e0404110503044035058280036882e00564a41103c602d045580160410b42c02c1105000e0050740303800600c1540b0440310112752132404030740c051010b500b0b400c49001c0c5003508030083c0d0a1070280d241d80146160a181c0c003465241c81d0b01c0d034030800101c4008000300710000341419900000d6582501c90b9103a0820116400b0308103031090400510f4090a001d041010003e0b080048c01d9154003c0d040182c15000e803000030311141c58900c0d12a81d41d40c00440d80b5600007000c1400004580307009882c903859064010300500b101c21500c107802d0b0b0f02948038050481c1d0308011030390160007040581704a0843d0341e00c2542e420384154504a0715580d0310454043c2003013008006a410008002181040d1049542c2801c00742004c81c0724060340404041180c1c0085c01c070030224400c12418049940704078031070b00003d0b03e805 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 172508264 1250 172507014 172507037
    0x40c02010f052805010308030402091b16060b0402090d02040f023705031e040f0503030a0606021c02030412021f051909060f0e03011d060a0612050604110411040305030a 74
    0x30240d4000381b0018000d450100046005400d10200030380e402a10010405e0100710a0202148254058100d44103058000d000d14010040300e80205221400308071400d604048074500010300380d0120150003071049603617a06101c506071198040c0c900f00c40c28400c480405c1342040406280401301c4090302d1600d41d003035641c40c8207010302070801d4a01400c203c0040d2460181410140d5804078000b900c19070390094000d0b0598009001080203604c5400c210350701282461030444064644490544080c4030050810901054192300106031000c0b106c0080c8802800b64040c00450404003c2454001c1c4c01005014007001e0650040010719a01c0109001c0e0000040c0300c0320115004151402044006010050404050f030702c501c038059041303040123000180340d41800d842c51902e41c202c01d00f00a25034102d07a0070048400c0607845100018028100841c40c00c0295942c0c1c16264000100002c000700461042605103440710707030000901c0c00740e0840f4a595181c030317420040d503260008100c043c00150007080c00e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 172509514 1250 172508264 172508341
    0x6090f0912050313080703090504020c030901021c05220b0403120f08010b09041d0106060f0e04060305030f0304050a0803100905090114071d1c0c080c010e040c02010f05 74
    0x3c4078802d000e8520269035030040742d074030501320782e02a40c03082c0c0400410301d0020038182c5d00c0c0e200030710542150000869990030078600190a01c1088a84140640c1410001008842e00305040700c90400304009002617a01d0b140c4014025141590046464000045400f02c100100b505807284032104540f1410a2524400c03012a400c1009000b103610021080c0301040d8182030903080003108a03003841030b111840307100400440c2140c0c400e520034000205880540c0c0f01d842d402450488180e09e00f0741d4148485429a1502035503481040302c20078100c04c1c0000000c05000c010f00890340940d5001141e2583d90030b12008014a1400c0c0340104002d1a10b8100401c906900520034902c07002002494011075540380e0b442601e924018046070b28891102a01840e956902e10702c00d0b9844400184441c0900e1025042071800c0c82d2981d04850011341c080281500d1913a0041048a24a6001c4401186a091560040f801b5000c420447e00d0b03001c1c04e0000340031000715100301011034640030700c0c160500c00c00136215 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 172510764 1250 172509514 172509517
    0xa050103150c271a1c0b0f041401051c0c061b080d02092b0602091909050a0c050a08040206030c0706020c0d02011506171b030405060708130201120e0106090f091205 72
    0xc80c0c0e141700c20b4505403405209420080c00610010aa18050b420006c08074007900c0e0022001c05000c0c15880040c405403810707d2101c8074a0f04c11010320030604410359034005410703000740524001e01912507800003c4004403116162419442072101e0345810a0f88440d2000e900a000a40c0c030801a000d00740100205000b25030300351542c8598202e03807800c0c0359100e01e4000c0d4045101e8940240c000c85050708a007004102840c020041510002850b103480f40c111000c458002c2000c00800c801005400c8145901c0401f56401540460303415940361503501586d01d20b84540c0300002d00c03040c00402c07102000c2d040460129030030301041d0000e10481c20080c0801031406407078003400300441c1c0150030200810b003020094592100c0d075000101c6445d95121a00981d64000b158201c40039031112042101c0e141d80a4001c60f000b01c450b8050b4600d03800c1c00c4d80007900f145070241444250702d5481c158040101c0d425004640285440202080001203c44c0590082d01a03404141c45500084450301541407140d0b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 172512014 1250 172510764 172510777
    0xd05150f04200301020f0417010b0a0510030f0b040f150803040f060302070c0305060108100b030d090905272a010c080717040b03040203060a050103150c271a 69
    0x10900b0b00101c1c401049500c001c0005000340e030550b50a2203c1b018100e40c8000800140030703c646801481103040084d24203460304010243c1c0251200301c0108055103d00c88200c04000940c20f012400440500c0307644001d040314001964400d0502007100392502e00c0340d1152020440042e11030f0350490303c90b070300c841d581d218512a0b06030107200c4d044100f10b218030039400361080070711400c210100103030340b5110646005401c1c3c00581c00c5400c04c0d500b0000b4080b0922401112075001e8020b0200308462308005444181c842c45181d203030356120000106103106120f0981205016030070380411642c81061599a9034032500031500344600c1c1240b40d4640f0b40c0d500b003130082ea8020140e54154551001c0d98446210350000201262400b00b0400100e030000880030190020301151482162280b60038010540ba00340c0c003810101605103440010700120f101807d4507070b9172001050b0301240801d0340c210225150401c000c0599820341102c0c506c50b01003002e140c1d42104844040c0201e4203012060144007400348940c5 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 172513264 1250 172512014 172512023
    0x24170a08090409050c04020a02250303080403080a0b03071512330305030c0c0f0405060a21080301080105060307050901080c0d0303180f03030c020106060806060c010207020d05150f04 80
    0x1d210700c42480ca0250094261544148250b584012101300450b0071790700407085a10140c1c11041c0300a03074520421681a001c030a48408544078503203036071405465100080e20207000c0241d000c00084c02103c035500302c250b09500c09000c0300c02051303440002829042d2a1035140c00041d89602881e50003182d24020a0000c812020365070003642074048002d1b0fa951038200d490b041c680040703079002010503018400707001ca074401d580107021452181380401c20a1018003200303905c910320304004c1c04015243c041804080e03804040100c030111078039161150007040c1600c001000c09400100110f4480d0040d00054041e6606400301c505654440c401c1100e880024050626a030b071000e801e6084900d0007240c5072040314000c0c280041c400c0b91011340100607525079003055482c414481c01407420513070f05220b40f0036404203a100030418141040c400500c1890013030071407407003840b021a035140c01000079070403a000c1d10760041450050081c50700e071954890742d100584850740b581120000c4d0002f59203044852169521 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 172514514 1250 172513264 172513267
    0xf020a0605070c0b0307110303040c45110a0302130806040807030e060d060b0901020f0105010602070b1b07180c020304030b060603090115120b09010908090603070324170a08 76
    0x2c1000d4400d0b9031708000c04240401c08103000c1100c0c413510900085000324001c0da0b113030780c000d03040215800e0b0005241100b0300c00085c00303220701d6289400e05481f0051030110703811000b901880000005020740a18901e050b140c8100290610038650140c0c02409042183c078188144180c0d113070451511040c0c111409040700c01300b000000000380c45401400c0505600401031802d0010802c3d40c00c04542180d08030807440900040c17041541d603010001c0501d4041003500034045d542c18400f0080d03c40340140b103180300314040814041509050589100d01411009040f2007501703030350b85121a2046011300e0001821072404005000a0b0310100032103040d03030340200751201c140c0c036100306014003603000620040300c95680340d842c0d102891280060344000e0543c0041c542168043d4201a50303e603d015020203803982c540080390700007811303500507a43c00c81c208030340c0180c84c1e507100d440690150030541c1c005c10000410480c00d240c2518040d13014000ea038550740105600c0203506001c50340e2000f580c0f0010303080c042d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 172515764 1250 172514514 172514519
    0x50306060a051c02030403032406110f0303090d120203010e0103031209051c03060e06030a02040e100c02030418021e03131406181501030b060604080a0f020a0605070c 73
    0x108a001400408250301e091458203481400d03004400003d04045290342d43c0000c00d01051607403600580b1034204a907a02c1101c0c0c8801c01135010200e804034480c0d9400e016a9800034004264280542d1550700b1040040c0d0740d80e80740c0a1500e5413100b82070941640420035541c44e03601c103100c3c80d00c2561b06a43c1c807411b02c4000c43c2d0035038405440e07683e00d0300d0007010440c5c0c03642c3d0440001142485502161041c00703581d15191608030350090142d8500b608196003085040080020a540008148211036015a00000c040001841d070f00e05043380341030340518460602d440c0316209940000204120341c41000c01d24905882c4000c28030a03442010300080c0d682002600c11854a40004021900021a035480710400c050a40c3d0320200f100000160304081c2c0c005004229009040c000e40f044c4020b20a800b0b0079134900c1c4103021460b07030841804054501d869200000301143c440004036409030002400722b80d28900703d4503118203640f0f983c0c0022406400726070380018401740580d043d12000d55010038031070307201c0c0e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 172517014 1250 172515764 172515769
    0xf12181404090f0c050f100228050a0c05030d030b0d14010e01060b090406080f0a0b06030c06030103050a0c080607020c0f130501080709060e0c0d1503050f0f01110a050306 75
    0x80ea0814050751003a9545940000109403401960314184500d80c0a074402d890803042014055190814501682c0d204a428007003030b6021400310800344003035a00c810101c403680c01031450031502440050480c80741e0b402035001d0001c40d0885004803001102281c00c0000010012825911480c6215070000c0c6069510310004070044102d083d020028000091500304804000e0309503030326075008207080500051031a40a041c180202c5e80600401c4000b059172038030445450b50348100c2460050400c11025000c074045540030b101115011030000e061035160b58503418440d0700d44005001c111043d02c40da0000090014000c2550f03441a0000c3d009046951000004d200880c1c80c645402e590003102007800e582c41c410b02d40304280c083c0610720000d005076070a00341c214040300c0a0b41c03c100c80f840c210008001c58200d4410443e00020154400401c81e1030700c4950320744140000d83c10090490045543d030025004001804038402082c0c10003e20810310224045100d40c0300e00076a04000650400000b507090 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 172518264 1250 172517014 172517039
    0x80118020d080c1002031f050d020303120a0b100305060907080402090c072402071707170f0910050a020c061603030c02071205010506090f0f010603110706090f1218 72
    0x3c004000c4e0b40d24000740f08844000caa104075120007100d9940526544e01c54000342d501e401070001134031506440007840d00002c1d80c074000c0304d01000c2625150300c005090340304c9640250351542c03000b60107004042403802000e00500f03001c403880fa005d1080c5000180f5406c2c86240214001c980140503841143c9881c101024264801c030803c0d2030342442480341e41c1e40e0514451071045c100401e10350058880440703280012000358044440702d403001062290300040303440000030914585654080c1503807205030320780c1d60446026070b04140350701000c6503586e1075456030003100425440c0784c0d035400c0d14200b451040400015004543c0c40c181c140582552080000e40680e11a004202c90350049420582e503a5803030481018110504403810794446040c400581014504c0c1c07a0007100030f01d0360508501d05202c0008080605110b050101529030040c0c403070342800c3c0e00890311001d401c40000d001d408610704041020b103850201c12542e600c0c00b809000c403400d225442c0411440300c0e0044441c3c005d40360000c0f1500c030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 172519514 1250 172518264 172518277
    0xd08010515040e090606240306100c05060a060f050402040605030a0209010306030b1008010507210b150f04050307120506010614120711120408032502030a030801080118020d08 77
    0x2551400c11020600000f0091000e1050050100622035890040305110141044107070420400d02c039204210720850320141643ea009200b540c122940d80d02d15441242d80082240014009004103808d20101074450303080707001512640605011050b64410a0004074829032003188002801440440e2203003203a0f40041145481c14900802d4064807a212460f100c2d0f001c0d0ba07010b2010088080030029200f00b07008031648050a801d07c2440900c10303031101c241c03e010124800c1641951402c0e89134043c1c2c4ca100b039000006103581c07103964030b070400c0032a48ca103168440c1c001c580c401c4c0300d00341000801c03810108a8203505030b408000b41943c0d9191020a1304e81143c44c4440322407059090002812495032000c0c1603104035402e0b07650900c643c1000030380904002040010002c6082c041100b40240c1c8400812600486515850f007081061400e1101404072400c4c44000e500d8020700c0490401e142e400001203050340c0700740001700700c5110450203811245114850003074002c500707907201201142042000e41003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 172520764 1250 172519514 172519549
    0x109090504063804060321030e01020d1d060c1207050904050c031f0605190207050303071a0106090f0303110c03010501080105090f0303042a08010204260d080105 71
    0x4812a10f502030304203e07240c000710041d00c1e070559004505070492009501501d0b500030ba404010680c10340e01e03602d50034a0800802100810041e505000c92032180d8041131100072520021074036076810303c074008050182614109012a50759091182003c0c020904502444103800c207180b402c0358040600015410080c840c0c03061007014002200c1a03102c601510380320391058003100381c0d20f02d0000c10140e0aa440312482101c806840303841880070a401200700c5403d00070f00395200000ac015981c04070b2070400c040c0c000c1900743c000800e02c1d60412508801000702c500b2028003140c00740c1e0700e881d000c8170751022906c940e00f0f081b082d803071040011a004a1608541d0313400401a03070700c48081000400d080d120284d028540d282c1d5214104108180148660105446940003079407443c00d080d1039100c0540c901000340c000c4500d4500034040c0c1e118403111620b0080244500940d102caa0300c43c222080d0880705003041c04035041035035134042c08940103c0d00a4585143e500c4102e066400e20702400803203032100a0740d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 172522014 1250 172520764 172520771
    0x17010620030301030f02090c03070f110c190311060c0c1017130309120b06040e0307050a03080108070b070b19110d020c16120b0718060507060b0105030105010909050406 74
    0x1100c020600007140603501400e60024504081d105118215900038000005035030f046c130502c07003029400600c50b12402400d241c0034000c205c110100340e003002c62140d609640400c8800307175003054074030580c0c011003207d00600d06000024007000130304c0450700c6030000c06c281680000c01500782d585040300098007610068500710b50490104200c9a2070f05005072042c42504d4071100c0080c0c1003560048a5001804680070640540b82c480d59440480700005051f0602c0b40da1100500d078400d00c8100150780e40316030400225020101d140c06e0103040c00c0400e015a51041c09001d04c0030560350b507036501312200c0590080c100c4007507944058008041010b400c1d11001800e07141c0859000c1490840013400202004000050b41e034044020124984422044000a032030001c8604000c4543d041c201010b295800110451249e50348070800c4070361304207010380600b040c2002440400c003181c1c40005418010b124110400c01030520100554090101b40f04150001709407000500805079142c010300e03001481080e011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 172523264 1250 172522014 172522067
    0x5011b03120c0309021f12050a0f090b09010b030d080a0506210706080f01080d1b0203060106090602150108190c15020105060901090e06040201030b1c150c170106 71
    0x6080d1404030b0701c0103000a0325014078500358a094692801d6102400c04008948003c5050190120080002c89110303d0707030700d00000c4c403680090f4010702100d910410003003080e90400d140c8090110005d03a541410b5628002440000f03040014a10343c49031442e480b100340c0f584c3e5008900000d400010840703608012004040d41101104188000903203040c10040c0c030390a0304014005140a80003411240d691816400410400f04086540f1154030071074a4421124a54681c01d000c141100d00c000a4040c8108800016001d9011300c0c45420395806609070b0707420244564a4802044082c0107044494005840d0494607050005000c0b410034800c3c000011500e584036080d11140c0481108080942d44075010880c007407401c41081400b40400400401c4071310420b40303055507110700c02800203042c16511940144103035201d14010421050b1048034080c0c00365985020002e00d80040c0c440203141d405d1038040a4054003607c0340d00c002a01a040c0e05c41640c0c60000100d42c04007011200011010034400d54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 172524514 1250 172523264 172523297
    0xb09060304111008070e0d15090203070b0c0d030507030207030f0e0d0c0e1006020708072709050c040b0406210807050607030509190201050703110c040c080405010c02060105011b03 79
    0x7141c3c00020707076120040207180021010705a0194241428030604403001e441c0001441310342c20300224449442c0004200000741f000c246404c3c0725402c4540c0720a00440e60140b44000002e00003912203060ba414032081d25130300401d60507401190b9000f0042904411502550303032113081c035008020001403c1d42c460700c01948402c0b01c1050701b9080915400140c1c810001c4210f820a540001005948000e00b080d91801c4a0180c03920341038010561006c6500740c60385100c01e55005003045c3d40300300b480c080144440394640326603113041000c00e00340500d0420784031503d141f40500c104002c403030000d4070780d0314813451b0a203d038244042004401c03500d400c030902200c40400c2040140310f00c618425200000c250a00144540c40c01500c500f5000f80c112400f540080140d074404241c6210700c2d4142000001590f50341c01850826444142a54000c1d2803d0001d240d1241e100040500580c02030b0020008000107050880e1902d50900502e4042002c0640708445805000c031380051481c000c1c80c00d0000c0d022445035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 172525764 1250 172524514 172524529
    0xd0509071703040314030406120f02071a15091302010804080c030a0c050f0d051c06090c030b0a080303011d0406020c06010b0703030e07050907050c0307020a0902040f0605040b0906030411 82
    0x1110607142e031000c50148200100402c41c102070b51481c2c4001d41c10a403810300001c0008150041440d0f115407500d55400c41e14840d90140ea0040d0f0307001c400c0300c242020b0310000300c1c108a0200c0d0285070502240750107103014180f06101d00d00829194030640c0400c090341e001500c0c0003c000d0000c5649480420440701c0c0d03c80300380044c104a40180d645d428080c0d0707a07401e201d840c084a8005100160300441201e180071034020b01110701600034041810035003200e20920780014807042e4418810141080c1072210020390660024500e00021554504010740702d00200c3e50780c1c00240903100c0e03044d5484601c2030a4103800b444840d4014442e150141c40c180010003034505040d02070744500341845002c20460101600340c040c49994140c83d030003c02841d4034040011343c40300c0024005c1f800340580041e101c1c0c0400418000c6400b1a6005800550050340d80c0c034103d00294428400d20017180312041002c2a00c600c1241220201c070110305025081070003e50801003154409082120014620600c48141741c46005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 172527014 1250 172525764 172525799
    0x8030a2a1407080609071a1b07050a0602010207020906061303050703080a110307030206070f05210105040b030a030e01050d06240305060d0c031b050d060b15030105060d050907 77
    0x66511500164039141c080c601011a0000400d0303402036001c11101c184001840b0313049903100c6003044e035809190101f1681a01c250f030150081c4180c0f26100251070540003910b401110b03030654040804a60380c54080b8200d014100009501412000c0429038604d4020040e10b00001c0c4240c6424910740d8079680c59150510b00c0e4000c4a10344004240c4618031504031981c8a0002c1c824409103150600c240c0e4001e4640000a101c881400361620900d841c25101d24141d60044420894400007210790000079041c001013403140a00c07444c1054118000f03410301188000b030040c0c3c545c46000c08017403200c00660707854000107600301069507100000146820515410080e0301c802c41c09102c8a1000b0ba0001002c0d42d0000302101e0050880ca00c0071800240380ea0440c0040784d400941114036604031306011881041e913584119031103050741040310148541c980c401d00400360b0032240403600144001039180e55010034403545a000d2020720065100803040d40045a0011421098405040d00c40c284515541c0811 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 172528264 1250 172527014 172527023
    0x6030304150906030b1807080421020a1112120f09090a050601031104050a030b0c0d05090312010f060e01030207020d02090106051c020309060420060712020d030608030a2a 75
    0x46070204010f0703070184030b8000243c409540410004038442201910408041c04400402224000240602241d031010f0600ca200c821040c5200a422540c000c1d42c0d42c810302e8050b25024802c0d100ca108c9440e0801880c2014224030001d45440c620801005580740c10003200403907a02001c00988480303541c8c1d006d20f40c0c801c0310341700c00004050074090700045c101c13108920b80e0321000200b004141308503036950b1504070880e50320a02c50b0100d542c0b0580702001a0040d0490044101d042000b842001c44000c0081e111900300c24001010980e0303100488010b210182c85240702003003d08110550551094005051850000d001e4051082c45640498002c0c2004d03408440003410211381c010b0b101130340146c900703550b0031504070640c107605224100644494014200900341d107120720054085003405440c0d022004801041e0301d89038101030510020004024450f08018040c60b104028200d001e4801d46064809010088d400c08000103019a019460001081e0700b0044c551645202c2c140324a440c0c0141a03c05c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 172529514 1250 172528264 172528277
    0x605070806030a2001090909060603053706090b010906050f04050f010603091e150f0504170a020c060408010c020c01300b180601091a030f0603030415 66
    0x60000c0506101501e810b12940288244602041d00f41e080d00490300c0e01d07440404920300207100141c410982603404400aa8140310b4003c040c00f07030641c0200210b038012016102d0140c414140007010703900c207900e400d5050b4800c01212140754102e0420211280c0315101c0043c001e4042d03125103441e140e09900a90000b6100c1e0b006026034203001074500c60601c4140d43c1403005080103460b1070410031050080710304040d41c1f65a40024001419400301480d091407a07166402441420412040ea111b107042c0403145082103250b621303214191051501c600c2d00003140b1400040000244041d070b40c080e0f0910381c02c44c81030000e010f24554071400244010010200005400d0b0002c00020b42003030441d8005506000c4040750045c41c0710424080701c88040004817444e5026400f001c4508014022102c0c02074000201c20b400b030078080b0302500001e000b50b000b44c0b140f0700c0490351034a00c102d00703e01d4482c1d00c11200400b030000c10901032103220f5007a0460802400e5a082079180c01c0101043c090030920a0006440b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 172530764 1250 172529514 172529521
    0xb120f010b0312180d020f060a080604110705100504110414010302030111030106050f0f121503280f0f0f0b040c060c0807030c150f020c0601080c0102070e0411030105040605 76
    0x5041000030004000b460460381410100e244a075884c919883c4100d001e0001c5148043c2190354004821a02c030030700030150740e200ca020040c000c03c21041100ca1360702951400c6020001144080c040d64130241d80013005004a64603000d009024003800b03403044401c000a80e04036207c903070302d030f00500c407411001ca840182e035985540109402c0d03c809074198562188100018440b2a50090490700984240085c0c540d4521102005400d14410060084004140c441c28441810030000854600d207404504483d01c1e000b00c002c405190584521011004809044601c00081c0f401e08074010b403c1d000b929410955241d503100c1a40041c5002c00803101202007070100401c20003480480009030030030f4a4400c4100140b9507176a0010312510344042c080c045203403419402c10148040b9035004682c030000a01c41d0b503600410290107508221008210390080d2400851304c0e440026018540100590080c07a407240b070301c16001032015019005944c918030780c40c00b0921a403400d0003100e00551050a00040310300c2c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 172532014 1250 172530764 172530769
    0x309140102090411030105180c04082a01090605030106030b030a0501140405060f0606040902071b06050d060501051c0b01111b0901120f0b060604030c0e010302040b0a0b04090b120f010b 81
    0x504c00d000204400b0741c10310050040e0303262030301950191000f01401a21a4565540702c1c10140a10b034025442481650072500c80d44541c0c222052170040001405000c900c15100103503101451350155400061042c80100036085c400d0304192402c00c4050306484100e0000c0e210142500c01500101444100001c280010000c007048803d0703002c0c02c00102200e00c0c1c203004001407803d128911481014a03000b06100d01406046140050340060040515029595401d80603190390080b03200c04150074a0a0030001c0c480d4010011202000402d480e40d440c07100d1409401d01c018540855110b0401800900103010018100300402a12114240850a40181c2c0b0308200d203001058200300c1211a00c9081d09002414210008110941c00701c40b8030010380da020003182050245900103402c1d450190300000f403851039994001d040e41d0007944c06010240b8010305100d1501054400d000c1115070030001006204101c6d032081c0d8080e8001000d45144010b00e0052503c1e107125035071544e04503503485090070400d2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 172533264 1250 172532014 172532021
    0x14040b0108030708070b0a0b0405101503020405060405120f0307061401271a03151b0319021804061e0501020c0609012a05100606091a070303091401020904 68
    0x10601007006628280c007a03500e01940740a001e000620340300d9080082030b0910351903006844990f1000c7c108010500c0e004886050401c0c141c07260750f80c00f8100c1d103016843e05200b8021a002d0360340251540d46010b103001c0c14400010380b24080042e02e030280c1d0664400c00320091009000b000d001d00008592003003c2c40c440100940180c1c09100200b801000b512848003030a0301a40740005601701c0000c0c444800c1415102007140c0714141c0b5894000d06000300c0c0000301c4100c0880c06284c0303540d402820207030350110305040c91205807109109000940e840c201d5001190b002403226203144080810100c010102040517124250080d80b03400e00ca1480c1010350807054120740d80104000d00c002c2116500c030b030f80400d0340703841505440340c100b01c6070240d40b00d1003080720082886201540781840e22030000c581819600c40110b56011100103007403840c001005445107401406403110080403148408240428003030a61140705c007101823507241c452480100e80c1d00304107a80c180000f10300240c2c0c3c030240d80081204a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 172534514 1250 172533264 172533269
    0x80a050715050f011403100203010b0c071202060f0a030f050703020d0b031f0f0e0a030e0102070e01081e0a0f080310050402040308090603060303070f06091202010504120f09050414040b01 82
    0x3074501d403208001a244282c48014111049900960380840000000c00d00300080c005580c0300490000000084c8000c0c500010090b80e060341041e10074032512001c5001440820041c041e5000c1d009108213414221b03000700808034440503041c0003481c0904588004103952080350000f0210382d004c0341d45076060f00140030300c40c00d00c4000c030040c01402140400700e000290a0b0900003100654800000030340b096030307030b04c1000b000010303104490300c4000b54507000700030842c8090030600501400c14005854240424000d041e9001c01001d40105010000c605903203e0454071403025502c50f08000801180e444c2c94601070240c016000182d4038549070311541b1400800d5400140a588108000c102040d45801611540c00048543c40d542e500c5402c006031660055901c09031100309040d0000b000c02c412030348042e01c042e20410a1540000c180d410a030300b00c3e281101c2c05000b0b000244140c0d46018468084500001790500744980a6511a4082022244a82c1166014a072003400b40000d100551401600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 172535764 1250 172534514 172534553
    0x90507170c1c020c1501120c150f0513032103110f041205071d1b1c0b03030f070812100303170c0f0703080f070305150904060207080a0507 61
    0x9001c2c00e402200080440d4110311400c2c2c654081002c86401c0c2040c0510030300780c0c12018641d521944c40d44641610314240c1e601c126602414181c00003800741651100b4040c41e1040d031241c0300c4103a0b8161080e0780c42d900001c0b140c00d4054216001000040d040240104007603c8200001d07074100c5810009000c0f03400300c5100b0107880009100300c41d840310410044800352002c4503414244401645456860b107840d50f0052150600c0c4040c030040822404031003248a015602c070340e0301c840b0f80c0c412101241441810702308584a9000c4009800b10841a000035820481c0902280c0c50244100014181500080e10860341d0550004018601e003085003641500000c07140d1048500a28558026040301c48541e441e105c100f00c0c0f480054202564901078809211040b0404c0d9514000d519000309020800c0fa0701d465682100c40124034170a10a11940d0f2144034076014030020f9108440c01c0102d41d03a00200102c0300c8070f40070007240c400500c0120207001041c64684442e0b40b501c583d4a050312191800030600380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 172537014 1250 172535764 172535767
    0x302060c0c0f0a080706030e031219060902030402010504030f0c0803030907080c030606180907091b030c14030714160321050f06060c03070609081b010902030307080310090507170c 79
    0x242280100742c84080b00c00e40d01340043c041c0032024000d4210f0040352504ac0b45a11a01e08000540d1800c03000440c1d0065182402c0040d40c3e00c9260b100c04a020681c0c0103400a4410700c410f000040c04410850f10580c0100044079040355544181d170300e140c0c8111004603040c1c01103007042011b01e1041201400185007203025144c00e02c5c0102c0421040b941843d0b00024003415100800c4680d01e00b80b0240015000240c0f05200f210030038400105d0100401484500180c540104440418800c100c1c407400041c2501e82d551440e2140d2000701c1d034000c420315031038001d00010040724003224004020011503a00c00d8550b200a00c03000b40ea003020304002d980e0f00c0c400070f50408041000d80d18020038015803024084550640b56801c0204803841d60085540062a003850499040b05000707052001c1e00380703802c1d10042d510510819840c00340c2680d00503203000350190302c1406083d000803256006168859050112007990640d1200802d080d05c03000e030382140c0800c41c03060304501c0c0ca07018001e200c4d5101c4403450055 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 172538264 1250 172537014 172537019
    0x60e120a0b060d03110f0a0b070c0309060302031005061b0114040f0f1103031c0c09030201051206061606020703030f0902011b050f0111090307050406080d14040302060c0c0f0a 77
    0x1c180c0103030300802d803512921107480301c0c10802d03000c1d0b0309030a60340402c10115003145206480050350b40440303007000d0b955001110005a41d091060840c09002941641d4600d141454080290041c1d0806060034840301c0ca4184046096103c40000d032582c5000303e030b042e5180d6220704003110b084440c861001900306140000b0800456051010081a40c3d440049002c03440128180311443c3d90304180a030f98180000980c0200064154220103c0544204002c10068110903001d40d680103171480000e000c030f40d0a0018190107904141c9180d84440060040c0c3c1c60400112072751025490466803c03a03200398086411024141d05200c0c0b00301c40e0304420001c00c491403643d0000ba003060881c00400d012214942a44001c2040074081d148000c0d010100171302170007510044c0d03104650080070310786011744248040041ea900d4035014441c201c4204401610000c0341d02d0004035803501c0c0c2e1038413a809883d0708110000040c0c60b070000400c03250303d501c070242c08121205400c0008402980a0152151140e070805 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 172539514 1250 172538264 172538273
    0x30e0310090c150917010f0513050d020609100b030c061303030201050f040804050d03110714010e06031b160c0b1b2802030114070c0b0106020d021b010216060e120a 72
    0x146005d903110681039900c4c0940054810b8058480325824076241405d040c2800440c0c880314902c000900e2264080c3c030702e41c0d42c9140c002c0340d0f04c200886030703d8008d0384041c001d05544d0255501145203c0700290980340c48404038004503805a10030f04481c80c00307070b408440400905a0a01c60650003641005000f61036003042d03150300120380a2030007a280300d01c1c92441300c0410503024044a4160140036819280c1146e660a4250001c00b13581a0320340c0403404000a0032900d10780041103920420503401c001036030340281c80c008c108035001001002034960001c1c8118001c0740b04c1c00b426000401c0301140b80744c0d843c103140c80707421443c1404020000300d80c1c2c040b400b41d0981e40c02c1c00c10b1003400841c6503290307500350340c041c0d00009015140d410360960498500c1e8051204070b43c0d115000d003154601605692845907070391602241d4032800e11026400603007084244050038001035200c0c19800d4814412100650000610031502241c0350380600042580100040c045c0e040c4202400d40e518001c5000c0d00042040340c45 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 172540764 1250 172539514 172539527
    0x302031210030206070b133305091902060409060e10080c180601050d110a0806030604260f0c011a01020102040501020703060216080301060e010201180201120504030e0310090c15 78
    0x4010106d42ca0000b80030030507010300d001b40d181e0452900c2c0f4056070b009004158001448010000300018100b03281309124150182a0007803c00c00028180c035144001d102e65040b40781c100491307002c1c104010005a1501e603016603000382915801c00e20706400c1c2820b451070300c2c55959201d90701e1900911002c1003d5580c027208284007080c034541d46000f039035a81004072407511601d001400110301d00201c0420700391048025000d00846901d540000e80c0340c10041580c0d130841254014202c0c0007012180e2961004100852075000074270700c04e1070400c1c104c46040800c5800800100080ea03649414820640750405246403960ba820300003146001e04100c0000d442d80500c4c040034206680000d13174401021812904861000c9e0001c00031501c039610360b50018406030403108514015070800301601c012902007542c01135007607416100ca00c000780081c40c03820050640141f0540520a0321910f2030000e0f2400d010b00d81c1c0c03240000e10300107801682032403c2012a00300750801c0302c1c86d0034007005040d9041d030402c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 172542014 1250 172540764 172540777
    0x806010c0b0a150b0a03050405060a0b06030a0b01030f0509160603020406020c01030513020306010605121501090512100c050903100605090c070809030304061d040504081b010902030601030302031210030206 90
    0x400110395084816042d0490b401550300a190013100014404201369040c0d0000d80150b1080082d00c0c125100d0a5150342071350403031040da40e4840c6007040407401d640385035400030780000018103000c100155850018000c070741c0c040740d500c0e160386c10035441401c0b0500082c3c8004044e1086007001c40c10035080001c001c1d42d5222842000b814581e94901040e41000c4550354201d150394010b048401d150307107940c0300400c5900443c0d84406c1c075085c03070701c04500b195050149151406c10181d4440d0b07102460501080191030510758040154060380315203401804403800713000e0301c444280d00d0341660b9507004410f05261000140b0103801651034450140f0555a6280045030000803854229480d101c040c100b0440c1886402c020580c944000a00010002d422205004243d845241d00c074001384900c4040c041603420071a0001d00c3c2c49c10410985250072245117080813500c0d119800040c5060350341d80800d203000d0382a00f003540545d10119156a841d0039151a1550180012202842c05480d640c00b0525501440 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 172543264 1250 172542014 172542031
    0x100302030c030d090504091a04060b03061003080f091c2603010e040206030402060c0d0e0114160b1008030d050a0516080106051c050a06030201080c040b070f17030a02030105010806010c0b 82
    0x41f039190742440341c1003030f48010851250403c41d0048c14039107402070051100c12405402400b540c40054035105110031140c08882d00090300f94035041604c02c01b41c0d0941e21810f4020350004a06d83c682c41030480c82120602118400c407814400a08215010a0b41001d0443c500800d030000b08014048500c19840103038201e6030582c1c00d00c0c1c40c1d032100e01c0020094055484c60702100e1080303401075046603502020303100c008082a00e604d64500f51110406505200750019100c4400c0e00c20200d80001c1c0c0c07103030642944402080c1369a6021a03c0c0c04a8034190751140490a04680e1283c00780034544015100d8250084100c2050701c04071024400301400030b9905200321000d0280100b0382150750821a002b102007070314844000c2020b8513100010500400d000d000585c00903004d80c000460f02745111040b02d090b603145180550601081d0354803883c001c2c0d090781048420594208258900310309100142d401000390100242e100e6040c4000108480c0c800ac0c8054100a80c000c0c004000c00c824030700d1250081c0c01c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 172544514 1250 172543264 172543271
    0x150e03071a0d0c0c302a0302010b0604090501090b060403030f0c020607021203120702030c1e010603080a1e02010506060906030601031b0306030614013b100302030c030d090504 77
    0x41890030f50b020082014045c0509001c901096001c071004d544105403e03030740e44030030004038000c403000322158410601186a00300103030425400e206c00c84066840400d01c6840045110300c801e00c08500b464010340d010007811030303c400060010803118010b9a01c5441d0030b6802c01e041614640b4000c02c8004101e20303030b10a100340c490303e01042d500c401c4102c0d03081c150060900e50906081d0300200740c0c0d035408500400310101000011500141c8003108603011201c0110090a51041804032020a6001030580300300c1c540da0f030749002000500c2c04024007103861030b0361191080c40c0300f082a448401203c40d0740c4c0b10216450070301001007a40c3c0b0386040e038005d40420784800352a81d884000607001000c0701450302c0300705038807050711008076a450303000310055922800d814000d2000e80413442140c10307020700610318a1900c409101202d44d2120480302003071151030403602a9180744403030f0410f40400036681c03500c0c0200115414815800e04010140e49581c0680c0103107200000518000c08184c0c107801040c0c0f00f1a203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 172545764 1250 172544514 172544531
    0x1061d0a110f0304080f041d0a0b01021c02010204030512091008060913081303080c10050603030d091a0403030605010801080604030c0b130b0c070c06090e01150504150e03071a0d 78
    0x1103500c01c0c0c40c10030324078400c62987d8585805000c8446a5542111403612034003400041002c1c42c1e602030f812000f881a0001e01d1107962020804024802e600c2e0b4030390842d0350a01c000401b20ba410030180e020581800d10840c2d9444400003401400580c2c440c20600b44501c200a1144e280c4034400300a501180040084580c0c0e60f00d450420154880c403441c80000301ca0001c0c0204c02c1c0182e82000b401100711020071601044003084000d02a92400c4a09560542007030206c42c0b42c48050350801aa07492107030302a00d500001c40c141e01d000c140b1059034254006503594605121550300040c4181c0540900001003149103810741c1d0080414290b490700920515a220204da142d01c442d08255200d075900c80e0007842d051030086a0340d0403607000b03113906481c1e05c04000e100082e0a405842e248081d07d103515819500340c0c0c204019081c208400b05d580408000e020800014460280d039019500c1e2001e69640b1001b06101904142c42c0c050a90032085c0c00e400740841c0c080da00a894011101d5103144640c0c0451541c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 172547014 1250 172545764 172545773
    0x14040603050714130905130201090512010e070315050106080115030b060910050d050c071703070212030a0f0f0b130b03010b0a080a060f05040b151201061d0a110f0304 73
    0x8450303c0c0c045007030030021860040351920110000c00f9030303e50003810085076441900c035003922201804040d0100d001c802080c00503040501061000040d030000204294006690071494030013107038002c2d10301940c1050710000d96807423806402d0043c5a50302c0d0406035941840066040241c40c05c042c40281030b5070fa0040395180c1c9600060f5800d17018000c21118450710080744c0546240e100c0b4071540c490307501d807000186010001d0000e503014542c125046002e01d076424100025642d0000d00b84d003065100b0400450b16001c0b11000451060500f0360011518505c00c0b440c01d4181d40005240d40c030114101800a00c0644824050707801554140d200881d03c0341e00440400e0050001c203c3d62904010507d0300842c1d00c210008038000003038803e0800b08801c11100d0320800844d4030a035801013140c80c00c000458120782d9071600e55920010010b0980401c0040d000d942421030f070303207648030940c01b45a41840c0307220300c40b000e4031490340320760152000c5c0b00d00c02c4c4140002e020b074842c03d100c00241050100c0030a0502c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 172548264 1250 172547014 172547027
    0x1b13060f09060303030f02040303021906090605010b090f0109031101050d06050406240201050105010e0f0121231905090a060f02040f1d040b220c080607140406030507 73
    0x105444034880300019159100030002d4070b954003060b00828107241002c0450078551080340e04685c1c00d5401b034501d1000203081503821520040e401e88003183c0320300c40079021a03854070601c5c0c001d015400f10f040d80c0719100c405000520181640b210b050005000d41000401d600154414004609181295440c0e4030341c2481c500034159504401c0d0003c2c5002c10105101030f00c0d410545090118003080f031509107001804900380c800900a0600183c990301040c200340c00e20700c1070319144446c1418400a400c000804040d50303600051a2203428a440d00b00b10341e800a090040d40340c030841d4032020600c8030320304440e0080306078070400c061100d005e940340006031907184240048170352a60301000138841204120101e0300a034116001c2c801170008415000101624081d03030004640d0f441600050642e074841d2940544560020304010401d60868425810046d8403080310395543d1191200310744503418800d0b00e62802c500180b6020600001640d0850707628641c0041d80e0031200380d894045559590000c1c221840e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 172549514 1250 172548264 172548269
    0x6050423070c0c0b091525080403120c020901050301020405150d06030b0c04061704020d0f0501021e0315040507021020040303030b1302190c020a0510020a141b1306 72
    0x1d004903200216004c48501e0061104000c101c400d404044040720a11a491203120b608909140800503240c40803412108502070742400f404046050994944a1040d0143c410650030001000415008218a004c41d401350145c001034000318109424200030402451078003a100c07445410114104440c24955003040000d076601064150080c1404a41415650080c0c0120400f007036000a6000d40c403421285414423580d00180400c007030034099220b0040d02c0c0c2183c8002d60b419502081101c01d01e42d80c80d040b56450460200d10315a5034600304011180c4513a13001c070348512540c03c11080c00381e0a540010303c40d8841759564000640508100c240718000202d00022040156010400001340b6401d60311191201405690807030303401e01c40c2c00302036040b4030543c09040c00d0312469040c42420340b0b11805030b40400380d1000d082030000544540000303c0303985034240045c0040c1e100120900410052128100b40d21003400c0003040c1c40c51500100004140e01c003003100f809a003040320401c4152407940c202800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 172550764 1250 172549514 172549523
    0x180813150f0905090f0a022215020c03010203040807140c0312030f1303050f0a0302040812030912130b0a050d05090705030708031201050d050a06110d06050423070c 72
    0x15054036040090058503081c141e400108400c6440040c241c180f0000c0a0703c00c111303a045ca403410b5515144c44070025044581d075400b01c00b500340c101020b01903a020808010f0804a6407810060f401008000c0c40c081c0c4007072500e4080d90040c018000003800c0001aa928a40d1100c80174900140c0000d400d071420b403520400c181d16128a08801d109e0400c2c42000754010302c1d52255665203992540c80104a9281c0c1c0d00000340050000c101981c18010181c000c2c0075107255034078000d031400342d84940d030602e8410806600c00c201030300002489034040c1d003049201c0c02040b1840e07013039040c406c1a0000107c65290703031241c4601c50800084640c80144103104581c0c500c0d000b00d1041000d81005c0e94403950716520380c01503600902c510900440c0380e0f40000141c613900c241e044603a280682c00d01c0305005002548400847c0e0b1031103035180701c8000815a01820b00316140c6003005039280c1c0401c10014040e00d195074440f90196107009903200203980301e41c0020030060380700f410504841d1100d0304201d440044481c009003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 172552014 1250 172550764 172550789
    0x5010c170f0d05150f0405070c0503030103050607180315050a180b10210f0305040b0c0d0e01090b160c08010e0102030f0c2106042a0f0201180813 64
    0xc00000a001400e20710051403010480750740c501e080365490030700040c4c2d12a0b02065110a40c1d4541c82c0c650001a8020706616120300c0350789665807003529541003038204440341c0e0030100401650301c2d408140a40d06180c0c00b4090900d95140d42c54004250311078113a00444a5141c1c400950744118a8001402c140a483c42c41d0f01c1c000801c3c1804803500c68281c4e106101ca2884800008000b18861200d40300d40c540200701c04120b0b80d59540d031281e0200001c004400307000c1e0600001884a030040090110366003400e0141080e0710400200425180003118054140004c0e060140000000c07501900d40c3c0a55400110102060a04246a07000c24603400b11559600303201c0903400345401900a18020030350700140e5402901ea40d64030f44451300840100d02c3c500381c949420041d204441d80c0308030b50086e070b002c0c10016200c50300604400e80301c9505544502d240d080198000035841d403000740d4070800c016600c001c1000007618010500111148403028242e01c40128015103508401c80c1c11070010000d401118 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 172553264 1250 172552014 172552027
    0x9120102070b06060301060504050904150e030706051e0103110d12020c01030f0905030913020c0a0606031e0507170124180507050307141e0405030d031505010c17 71
    0x14003079800300384115542011400840c042d401c000c01940d060703841e2605c504d801c181c1420b091085049004000392200d102c0f410b01c1c0030204181e442192030404102e4041c5544842c00c1c107000c0260764005c2e1000ea056000e819151210224202c0c10314192507000000701416610035000841841564074050144840002c2900c6502e03000143c0c00ca2841082c0c17001c1c08000402c816000c1101c0754000003a20307540013009805984d141142d520407800100c81c6c001400d100959a541c5d01c1c280c4075034422181c45030f4a01d014400c0c040015040e240c00608081c82810140c0c441c4e503035545413021482001141108110001c81300348003034100201101b00078401502e01240d1906188481c00ba92080d040c00404940000364603681902407a0b100381180d0319110b1540d11003040c100d5038409580f6500e00360403003c0c00100780d41021951303040100910b0480c5291074030700305010507042000c22500e43c01454a084280b0490306020745c010000c076003003403c100030746001381d0601800314414409500410100000c94 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 172554514 1250 172553264 172553299
    0xb090f010603060b03040c0e040510050a0c0909051003060e0f0615040c020a050705090402010504080d080a050c160b18070e0103050c1e15190e1206010e040303090809 73
    0x250481d0940d6070180502995682d844400b44000d881c0075006040626003403140e10107a05546403c1803103202214a20181001d8110490b881518540030032a111800a00394070780c440300300400b40c1140403040100b41040002e580c050724452000401d441c0d12449181d0000000f88416619021040c094895074545280c1a40922141103c540e100d5498030520341940d030b20018042c0c4078603500a00806009007880f00300088034400074001c0b03040110400c408a6414400d001401c606102510707400c8050400075008c3d030039654018003403000380400388060b4080f4000761580b40c40c2c0c1074000100c3c0c1c0a0b6190308001c0000403040d00015a074600c50f16030006410761102081504aa00a80984520881c101c00304101404191280442c8a1040c40c4040091508200100d0049081005145055100d070005501c3c103486070280d40101d00391034915139860030030350762801c1030746030001c0a4005581404a084d80289000c0c00c00303003c041e40c41840c9010801ca07034048629034480100705540e0780d14403401 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 172555764 1250 172554514 172554541
    0xf0c171902070905100b03040305160210080405070b030c0904050a020904020a090f0b0f0f0c0a0b0705040608100303050a110a06090f0201030e070e0a0209030c04020406110d080114010806040b09 85
    0x5400c803030f0f03882c103000142e034070001030201c000340c0312010340152540d226034034110396542042c20710110900b9018084070050b591019142140551521112010f203041d04150342444040d0384502d6005000f0400c001070b0944030b04c02c64072078038000ca50009071901c070059590001e0041c155456002032001500d45002c1d1b800c8a4880c080340c00d08003810100d1510b030100300106012356003100d006d4110921099a106400307002400c400090101143c1044001e6211402c3c802816070b0550040307500060b080c4585540b10301191fa02001003a403580c0030b545142c0e0300074214420003004e8410045000207601c0492800e1080c0c20035103410081c20f008041309428a22150f60b541d0408038080307464201d555088040c0810224101c03049003000740303026602c5990300c10103980303e00c407010b5260140414041440d640e520191000e4440d61741c030010f000c1c5901196600e0715000303140c100188008480100100600301d48100248030f400c1c03901c03070a10b0300c0380400b050207400f0b140b0140354084103001c10413120025201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 172557014 1250 172555764 172555769
    0x905150c0702031015060309030e18060415030c05100519021e010b090408090a0f0e010501020705031b1c0803070206040b1608010e04050705030d020703050705010f0c17190207 77
    0x28207135022401c0300200d0381d0072590400c0179650840c0080301c00b04461030281d8050440d1f503000e4141040d5040c2024006444214401d14094500050009210b4641000c2c8214420500103242000324107086440340319840b80148500b0b4480c01038241428080341c415025139165004401e0759810303500e10740742c001c0c2d100c0d01c16002000b044a101c60300c501501405001d46442c0400c081d1000309a0340362500c80749460391040303500c2070b00280ca4000c0001c8103c0301c64202c81c0285000d8050307852650500000900380b0031160700681c07090380f0800c2c400304101b42411048016980c1124011001064546601c00c1c145084602429584021082000581e008a1114891881014403441e1541c4030a84810040d02c0d00d0300450002d801e0b83c006000308000000b445401c28040c00c01c4a4005541c1c2001a00d0200b0b0650703d100145c01c01c0030100108030782044030001030700c0d090905581120700b00d00c000b08032000c0030401400e1141c1c02d138891100800d04804440305200b00700c512203800074450f18040d54403072051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 172558264 1250 172557014 172557019
    0xa2703030311030f040f05030f2107170c030403090308161b0f17160f0306052a0703030b030607030207050708010b061c0b0d20010e0a05040905150c0702 67
    0x2100100b40c0c204041c12a4450301c2c4c5180c801c5a252215128480712040350b1404666600c0100000071070301040c00d02800300e0310b65004901507058101001c0c08007008024107244148000d0100d0f038008601049140355014030001059034503542d0b00c2c1030454501600c2e50019090080002c0d91045261011a09031000e6011b00b4082c81e6440780200c4d458810101d52249100542605a0034401600b0b0100c1d4003140300c60003000c0b1610302c1c4802c04c8501a1158139403054141520102c010010000130340a001e50028400c0c000f00c140160040e98104c0b41c1581081c095484d0200003141c50030903000e5448040120700240464009240100b03015000b5800040280c42510034108001294041400b6602001201502c29418501030440c805e00c00c103013429184c4d0f01d80d521402e842c07a568031070341ca200722094000d4040b48001000071004025180022420034108210084081d1150725400f00744021a031040c1c40004200625042060809150341211041c001074401400320001b6124007500c2454002c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 172559514 1250 172558264 172558271
    0x2030c04091a010e04020a09030501020c031b03090d020609030a05060f1909050c04020708070f0f060635010e030403200a031109100506121005010e030a06020a27030303 74
    0x5200048804050140c0c402d40002d1862032060880e040c640c0103090f41c14031605022840d16129a02da60985e0082d0300d59214690010074100b915005d4064205428903204014515040e55907001c180428070040c00680a40c000003040c0d8440c1d2000c0103404002034010013560402d04203401c90040c0781d14259002c0e01e14150160550350b85942d40d10900000d150310a008094800d500b80038003020b50003190080d9070303049050242c0000f0071542131940e4811807007500343c035a104445140000454003980c01050920b1a140020806000043c0b240d0307414240214807115800c07005810700b40500890040010640000714000007040441e040c240017103205c08024034602d4040304103200195a00344030290080070640c032241000c0c00c01d000500e40282111000100d041c0d10344e0003081040c0e119200c81c10150780d460003008000c40307000800c1000381400b480d20b450281c84040c0080da541149180c0585116400111074050500a007a44044120303240e0300141e51303041095a1100582d601d10058020030704 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 172560764 1250 172559514 172559531
    0x30a0e0a06052104050c0904060906050a0b0d03030905030c15092404060b0109320616021c02100909051f090509070e0a2a1b0305070602030c0409 64
    0x41d000707681c540342c5603c501100d0108038068072428010054400e4466004031140540103031200c0103040d2080d4002d540100e5540404c1c6410f5040794030051010b581c582ca0302c85619035556402003144990364051038003050640c204e007021421032040c0341c0248034910411740d0b80f036291030224080b140b00f039007858152000481440080716581c80703140300465001c100e9034001030000f403007607106065107001031400d0004241c07540089120f00210300100203c10350400080242d115280350280e41c0c40c83c0a590305400c080300304421104103200c40170020721821480c030501d070303501c4d0b800d40b0600d040c26002032440f20003a40300b0300060545070890042352445401e045c0016034080710188021301104080000c65102854004420001d003405842e041c0c43d805042c1002803000b91400d103c03030181401000000380c18a240709015412102c000070204441100c103480ca070700300d4115403060021080443c04408080d42450708403020710406a0003000644007000f0722010ba1040405407081d04c00b1041d08000880 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 172562014 1250 172560764 172560767
    0x13082a030f1f09060c031d010c05090409151103040b090703260c1c0201061e030602070305040e09010b011103030f0c0c0a0530030c09010c14030a0e0a06 67
    0x11007079003051045600100b010000b030141d5260741190b4103400700d40040d0b0301080795900416101000d0019001903220080343c89252401c80250307406c560814000c0121681c680720140550041d50b1900388195a90503816042c0030310712000700c4201018020801140a503800d0994ad2504117036810b4a1080b4500d0000d19030000c00182c00b025650402c0318201362440403061000b410410010000301c1ea03800703000000c1d030090108440c540315552038a1079480a022080b00070300f1615150300440d103041101c6401c0406404a880c48010b60350810310140c2c0c0c400c881d0030700fa962881564000804044001c0c200601800e065201d0003185000341d13110b00b4100d901302212541d9000c1520604003c00400c00403400001c120300080c80e40322046001c4e2040c074102c6840300c50412800f00e071035285c3c0080100404c6d080a0f41c4844140038468480201c5007581440000328506005d0488114144a49201204280004908030004617010340045955510407107200902404000c0301c6240141560503020683d00d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 172563264 1250 172562014 172562023
    0xd050112330207020d0203010e0606270a090302120a080105090703050106080f06010e1210050601020a03171003020a030809120c102708071a041401030213082a03 71
    0x145124482401d8004451001400951109600301d90052a00b0691001a1030038001c001e108495803010f00410b162440078051b1490710b5074075031910702c9009504d82c0303c0d84002c0ba00064000c01d908100050000d0f1a14041c0e140c500400c06032451b0b10350100301c3c80181079020314018140ca0040c2e1744002203490351582a020340b4028000e0b80003143d210750001e0180c0140700e4645500102c1450072500c6000c43e4030100d2403200400708800e019410034400c61408415500580d034001c130b406e200420100800e514010050300c440b00d4082c541907403007008160140d403180f4070a005540c00030041c2c500e055803454000d0255100e40f846d03502a00d0740e0131002070507040c00305000e50000070182c2455a90324041c0c204840fa02d00955030723190440b2201a20300c032040d110103910030180000d500203060160420f102000203c2d42100d03c81c0b18039004200902101022070344410b00c1c0ea0f000e003001750b25040c4c1d118140740e00309600c0c0c0042030140b0980d00c101410041d0100c40c039940c0203d115103600e00049540605899 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 172564514 1250 172563264 172563323
    0x70b131401092f10030e0f0c0904020123040f0303020c0a0308030105150705010207030206091204120803060f19060e0901080303040b220b010e010503030c1c03020d050112 75
    0x5001403a142c41c10180c3c409040080001c04010004901040e60008002940c1d000030b40000076a035651200c1d03c1d07503081000c62850304e0358100034045800380d040004c0d01000010402410449018180e84002810707845203029103808000e0030351201c0c0c480c039803841103038814401a00148214600c1380400c2c00c088000806a81d0025601c92460303003040103010b000c24910318139102c040c1c020814900410300078405400c440780300b68090400c81c241900b2441c40c4c4112050700f89580c890030482044050300300444040384075400b009081d10fa81c0c0b64800665500900364a040c0c2001000c1c442c40802500c0100c04002d440550300c0e10040360141c1c2040c02105032090080d0f2400794010808140415038540c04203a01002a0800f0782e1440c0c0241411058418000d008440300c4990400503c03480001d0108503025150660085081051009000c1c3e82d50780030000c410382204800350307166041803103601218400e4144080610035075943c0c04801c808611031321030a96541450000000d035900d00721504004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 172565764 1250 172564514 172564523
    0x120507030e210409090807141506010c0309080f060910110403260f03070f031404030305060a0b0a090e0604020405010f03110702090108010c1d030d14070b13140109 72
    0x200301c1207a510b0000c0241c20000d0030403044000e0000080c90719250140c0c103540d522030502e241d110f82ea01c4c81c04450038081003d1030842c3e5000380d0003c03000c0306104154664016024605030380300d103c441c1029154601c550300001c1c480d010700c148070440c10b440001e403d800340301c1e64000c030351142a200c0440307401c82d40503640d013510004080008101044e010321008241c50360b071400c107121030000c5901c0c81030a5400b00214006000c00401004445030b0410f500c1c2042c103005040500c20103504210040001c0c0c0c0042000342815a20700205465031503110402c00036019800c0c42547d9003100d40005060070380c4c1d134802e400c10340901400054290405000791802c032107068580200400d0035a0050b0041c0c1074101c3d2103010302109006110141e6038290703a403402401c0c4000006030310501690003d01504c4e5110305401c1c42d100110194000c1c1e06e0005030994014001c0c603200600f6090401000d00920840501800d840881400c1c0400751003d14a4192500e00c10600c1c4000c050200260300d00f690000356000c1e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 172567014 1250 172565764 172565773
    0x705010f050a11031201030c030b07030504024006140a08060403050d021e0a080708010807150c050139140d0209030a050705040e0604050c010513030c06120507030e 72
    0x5034050f004060100501100380283d0f03080c003840404441c402a0241e00550303010301c0000040040c020441c0096800418526051200d468160041682121584c1201002d00801010000402d01075a00200f49104095408071101860141c201c042c00130340c000d480c06605100f031800441d140492030203041b200c0010150030b690359140c40a60303898104010101300c00d90200070700030045142d49005124014030003001c03a1925420f0307100410102000b40f006c400c2c082c404005202103840007582008a9415806c02046c1c00c0d54000c01301c1b040c120a44004010750300341254000380790049500a4039040345500c078600d2401e030180c2070340808a07d030700c156001f14007084c02c1d024002c4c1040d0002c0051408149025107402c031a02c010074980380c030702002075801e038000000501c1507240a000c0c208600f28010002c000c6405d094817082e0b12003525128542c1841400039144ca02e202c81c00204034021900b101b841410366555400c013400d5422000304200030689840c0005824a0003449009003000d0b00390001c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 172568264 1250 172567014 172567027
    0x7050603150127050307080f250f061d010804113106050907020a0f0209150d060e01050c1c0513050a0b07080c12040f030207090c1116081002130e0901020a020705010f05 74
    0x103022503a1272212100c0501015600030515100104808001b440c00355607a0350201c03400203928404146124206040002100910000c54400c1c0c0d140c01017007908841e60100d0b0b10b16400d820020002c400e000009180441011040d8040307664400b50807a9400d0301c0c07441c050359030b500d0b081b62100c00c00711004010090351040c00001d0304005002941c400c0003120380305003000107500000c2206640303200840c1c0311a100d6050381c030804405c0c0656500140d01c0309100e403c1042c2d0350f80d2040c001c4440f421190220381e407100000c040d041c4a00d01c101f40140c0003001d94620000500300780a2600c811074500e0b000c6074162000c80d41d6030005204689008500311800b07842030700c42d541c500d01240940c9600f80c0861081410100707440940c2d100300da002c2d04954840c84001d036041900f56050028030b50000c50183c009480c01c10403000301007030300713003800c07070301c0c140c0140e40707103e41316064203519419000102145804002c0100040d01503004204003100380d000c07151400d640d88d004680075419188d1820009505002070b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 172569514 1250 172568264 172568293
    0x10f0b010915032703090f050d030305100b0c0601030c120215091207090903120203070813030507050a0807060b150415020f0a050304061107050603150127050307080f 73
    0x20b108280e180780c80c01040d0540014100449035500c0e0805203030040d01000814100754100001d5070050002c1e0000340c0c1c0c05860a400981c1c0e20030200c00240901d1385402c00601c28141842ea03840c05007141096490b100c016180103c0e42d28002400304440c8820380100114100049800c114101940244280e10300e42180041055503081440742c540c01800140c0e01c0a40918184400d41c0a810000400924a1020b060041207103004400c42d1032668410024004000d5006000d650300642088507000040400d14007100c42c0c5c03142020140290194140d00420080c1c1c81008240117070199000307211101144c070410102540b80c08a0314024081000b0401c01c0b600c01801c0c0000c002d01c2c0d40152449000e64404043c105110b01e40121034030b41001605100c042c9d004807801d65007040c1c040080201a00b0200454441d2001610400310382000e941c0d2411260b208030f100c814250108403070381e2100f0600d01842e140b41c0034940241c41c401d0040c61030125410100080d003c024800c000010083c00651514 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 172570764 1250 172569514 172569539
    0x20f0309030304170327131407031d0d0503103309030b01030c0806160f050921011d010c05041e0506040e07030f090203101a03070f030203010f0b0109 66
    0x100400c1070b010074412503030014401d000021b0015001c0103c0c168203511003040044400e010071038403c009141001c42050440e903010165805820303424005002c10342d81d400e00d100c07808000111021741c418828400c20703090b8007201450082e48210300091140d91100f0b03d05034030703044165050403095800403440c020800d950343c1001c2c0c40480760a01392600c079100d8944140d0114240c009645040c0b150b4030130400e0590800c8555489204010b5030503140f101802c00520400c90350b4146800c0050114244c155a030358016132050510ba094008070076071a8140b2110701803e2034103482065030a14030345000c2ca220b418000d44d01d0300c001075074403a4603190a20071142500f003461800314200007840440031440d03848140060010f40000c0c041700300d9514015400030300b40ca90380c4040010b81801c0100c1a070041c1c03400075110070031a00c0304c0300100745011a21100e56034040c451800a9062081590000300d0070900d902030420f49000758020720800302c2e589101c20030364071081600d07400224002e6007004003070302d0086c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 172572014 1250 172570764 172570799
    0x10f060507170f0a0801080c062106060f18030d0908030a110102090303040b12100f150c170702040f0605010c120306050607031d012a0c030b0106050703020f0309030304 74
    0xc9500308141e540706400d141c4c00455002c13010030b40100043c0803800080168040e440c034215021842c208503e0601489500c1c1c480e5040b00c02000d02c004505956034502c1510a803103001400541c59001e04240c01942e54001284140039000340741300003030940d1164002c10152400740004602c5c005603540c0849818290201981082d5030920020348160317420310060000f8280b410360b06844552042c1c601c40d044c0000340c030341c050410f990302082040310702c0d014480007120f00704002e01c6400341b800350007920b20314031500000f8400d0021800d4103045204401c06800b18600070340b801c00800c03e054071094211000c81c041c0c2404180c0344036000000940c0c0310060440e002c050314022400c5561200031030040d0f040160100d02042d40f48400d2002c0c0c3d00304080c8000018024640b10980b041c1c0003120700410384c0401e142000e0707460448100410b200701102018011540108801541d695801e4018402e4000c10411070060180b41c204e44d480780b00003c282c40881c54000c0c080c6203043d01e05111301506e0706818 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 172573264 1250 172572014 172572053
    0x20105031b070b0a05060a0909020a05041d010903120c030b03060f2706060f01020a02150c0c031c180b0406083102010807031406040f0b0d05010c08010f060507 70
    0x10845000003c074040c250900891107481c0124590a000080090407682504170b00e20480c0b4001c8404096956411904c085035400d82c0c0009800c0000400454140f0903103000014660901a0340000c142e8400c8803540280d071441400c011460031054118280c030398810026606030f12500101d100760840016054009104800801000c9403c07200400c40340c0e140501c0071030340d400c460104001428110030f211032481092010303007202c1604e580041d005108103a680c2901c494089000340b41100e08100d22038051000902700c0380d005400d80a041d401c10101e8080c0000140088062000e050b581c14070001620b40114040d030400303081200440c1d011000034480c000c44400c01c6807840250b05212900c0b00300d05012540c0110981c00e500000d440d4440141000c1e0416182c500c11020b84c1e401d4608194004800700c50105100308528488409000d4401d10b5551081c54120824108101540440d0800c08652142c40a40e07aaa100329829922117201c0c60002c00d0302004040001001d010b02400c40100300d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 172574514 1250 172573264 172573267
    0xf11010509180f0703020403031d0307050a0915050303040e01031403120106020a050615031207020604090606050d0f0501060c02010e04090c0902040603050a0e03040b1c090605060f0409020105031b 86
    0x910002140042c140e038164110162441c184051000c8090070a984075105003019490b1601d0b40d5002824110404e1040c1074a0a5502c5c5e80da140d580e0a100f140000c1c82c00074210000c45031107250740300c0240000b0038a003400c1030841d1400291800d000c01590100c4451944090142c1e2841d25800b03140619400302005070f0000f0000ea985071502e5040301400b810084c0d00420948505d850064a41200a02504042046842c20525130b540000d6141703a0b200c110781079591100c0c52440458994012038000580050803c000442c0329507220006c2c3c41525107004042c004844456150002c80d81d0070b0203140e0005215100c9880554022880e40e241c03100003a100003032201607921503000742d50300c1d030300051901a00050104207071941401a280c110781c2451081103c1c100080700c01d5034038440c0c0d115086d42004003141102807070440d40c4001e1200302c1008010304c1146160300c0c0400040a08a82036442074031a01384a8401d81403a00c00e003420b035a07044c4c40d49461501d84210802c0d540c4415a00300480c1c400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 172575764 1250 172574514 172574527
    0x1e0c0d021c0203100e010506040e1e0111031f0605071101081e0103120908060903040302010c0c09150e0c090a0902160611030103020a12080f1c0e070f120f110105 71
    0x400f0404c0704103142898a0000d02c01908407515400e44801030a081c0c8128180480d41c4540c42000c101d071540801141c40c0d40c044072540e14140c0d030242c40304a81c4040410000310801840d0040480c41441c1d4003d03164010300b050b41c6880e804e072054095680e028004402c540444421075004550294100308003040c4030400c0102c803000740d041082d00340c00460303803032101250900001d5004560540900940b41c09070078985022055141d0740c0c016440042c1c100810243c0042c01d01810800d1140540040e090038092643d2140040c1d1000d07415200351440809003c002800d921100b205a810703c40c40281041c0344507140c1942440a50400c02200c130451211040c1080041e02c940710302040d040e60305841d15140c1d0300d18010440c00f82d84c00e03405801c54086101e80321000981d9a0129500c8a1035580c4403522004040c40c2810030080d002105250146003001c01c1c1680c00000a118003142d48403011050b9036511015202d02070442c5102c01003161480302c20304800640d00211a800d02d00c0c062500754107140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 172577014 1250 172575764 172575769
    0x13060306180605010506180f040902030a0b04120f05271c050c010302040e07351005040c0f05070203030706050c0304050c0907090608060a03020405091e0c0d021c02 72
    0x100314034200001c082044940004100850040c68014282180c54600b408045038008a840600300303420380c0320790b070700503031501041e56143d00801415402608075804c0c200e4514000d40410020789043e5012184c9103405100244240d0042455486e07aa0b01c903414a003400c1d0400412008009a00003038100070402020b185d244c0000840d040101e462a48000782e003030307007015410310b010321170020704150040109004444210a820b900000203141c02000d1f1310000c1c40c00035843c10711081c1e80c50a0528800c000b940000150303040c40c00340c103120707500302c40d00c99440c000c02c021113884a200001207243d002e100041d0500540141c8440d03400502641d1074490030759260821500d085030481c80b81c040100510060200c01c2114060200e03080e2003013142424980d801501c0c40c00c0702d10414042000b107500141554540510035001180c0c098401c0c403060800c000740300d4650074000000074170340304080040303241701c44000344503060341d8000750486803031a0a68090002d41030b262402c900058a50492010068 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 172578264 1250 172577014 172577021
    0x90c06050901091a04060e040c0801060c080c010f140603010c0e2403012403110d0c2705100207050a06081807030b10121a06030c060c010b01080705040303080613060306 74
    0x3550184c0e00c42d548034144200507014400300300d00035005928080c201904203811180f00c0f0706503820341c10002c103c1809494616024403c4442141142d403c0001c600c800300103e800103681c01c0e480012002440c1d035020145400c940c2150810800690b041500d0437003410321056549050300c0903e0010003090300c01c3e80d003203200d42c403e0380020030420840306084105911010040d840440030b00d002e000c029000701102000e8000c00c10b0ba40d914964400400c0c003211b0080300004140403030f0318070040c686203404071007100700c241d0392003000e00540072409880d480d14408140030090b0750000700382c0c00c000c90414908480c800001230800004c0500080380d202c0004041164400451140444803000d01d03114940b244410710561089001e40c0000c07034410009100d07074282c82d0603d08841d241b19005d0351742d40006441d02c014000195000030780010302100c546019007091103c00800e0b00c8440d030507103030a1401c03540742c82180300c040d000803030b10342c0402c80340d1400c42c0c2e41003d41041882d020400d1620380c4c480604a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 172579514 1250 172578264 172578299
    0x151f0306170f0d0504080d0e060c0604141c0c0807050114090a11060f1801180e0a11130306110d020d050a05180705040506060f070f050c0301090c0605090109 69
    0x3154000c02c200403071002d0030880a8400d40d51868000e04091400c02e6041e51340c2c129403001024403080c00b000c40c800391078500680d080380f4103000c2260110b050a051100a03010401da0300140f41c00b4189009041c228220400c0c0e614000544c2d5940c0c0c180a540c4801e90700790811a0201ca4554071103031030203414400c0c6c0c0c400602800c4424054805402a40f8000307140c0e05071003038968040c140502c581902c07202104156015a040d21611030594000200126441c108400c244011840850340101e4031482e802d10382c501c2419960402c01c13410714584030007052806031800e5840807401185003880050000d40041c2c2595202040490401040e4140c04050b030b005a0700500c0f5880d9101d0810901c0701090107015081131350403082d0000d110202600b2600c420a50003218003640c1c40f0310100d51a0349401d0200d80001b0602d601903034540300203241500d4200800142076a00d4492500c540c4018075062040d0380040b9800958103200520f000c1b41692140c029410740c9041c0312003030310001031026601518601c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 172580764 1250 172579514 172579559
    0x106080703050907030b131109090c0a05090f011e05130c0e010c0203030a210905150a0e0a0b09030702040608011509050405210705010f050f151f0306 66
    0x121403421590040031610000d01150301640003400400204401010301601f0080001440c10700c3c200a00301006035000e0710000c1030708010424100002c0c2070010641d000346400c2103030400801541c0e44208640000160b841020913015400108446100018201084040004400b09607940c2d040003a1600d000702d61680d0003162a00d800303400303007984000d0020078201d003424241c0070046183c002c640d0300c0c000c042100d82408054482101504065000500014242d035003d0001035090700c2c081c0c0e200d100c105605290b03051031a0109061341c0d0075020324080580c0000c0200380248850f12180c01c1c00c1005800855203000400400b00540c440303029880140010f00004262900464642d81800315a903006040b06803a2505100010f0004114800d03940c2401c812201c1c1820441c0001c0d40a104070b0034010701662170038401c5003808003181c028034418400421405030343e036100c141100c4100140000780c0c7e070100700e01c68805480b14a007071100000c0069441d0003c1e016468020b42c03120034410120006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 172582014 1250 172580764 172580777
    0x1150510031d12041a070b04080d06080304080706140a0c121709060f060f0913050c0a0e0601091d0610110102070b04020310090309171f0e1005090c0120060106 70
    0x1008a8a0002820051710004481450300f001c50700c0d40f509580014000400d8000300081801507504150400e00c0a003035840182c0b550340c1d40ea003040c540c0e0b0305090710075240030914203503030004d5040d00700c400d032005c3d48416222503e100d4a01d1741d40d011202e154903100803c1c0080300c10b03251801d2a0790030201d0301c141420300042c045800c2c0280340100421000300308500c16480e44a0b90601519202d007101d0b0071151024041c411002185040c1e030030010b2003071400d900002c001100107200c0070b500d0310490041d9000c4c1c1300c0c0c00d1302c5603c1e03601400024a03102060901c19005c200803036503900704840458021041032801880f20703c00302c0b812a003a03038040070f0709450141100040c003042d803030140b14801140c00c103540f040101003841d590140c0758828510806080300d1107092810300d0840148921502c1910f20803042d0800708204002100502640d0350b21f001501c99030300000c0c04000705e440703014020503094000b0502c02040d00300441d002c0402601003d4044580070040421520400242d4083c00050b02c0e0074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 172583264 1250 172582014 172582019
    0x80c071a0a0306051507060f0e0109080307030606050304081c090519020a0504050615071110030e0606090f0c0a02010e03030403050703120506010c0605071107060801060201150510031d1204 83
    0x70300b5910150131013446800441002c0180e2003c0c2000c8a0480d648442d02060150403020041d0042103442c0d04280c080d42084444800c02c214400254416a103a80701003040d26100c1c8022241070008450007055000100210744110000c602c1c0c1c5040ea4402d0400801d1044950391928200a694018141003503d00ca0f1040118507040b0305400281c06c1c260341c10001d615000e400510f606100f5240d0a501600c002500c2c03060010050340b5010f03615001d41603228184103008018010310529030380072050b014101c045119864820040790090307074400b498410680b00c480f5400b00642c0481d14181c290765840b8002a03040d1000d00103540b007a80a038440948516144c100500003880c521029890300345401d00300640c0f0303a0032200150406412040004066641c000c05540385915801da4801c244503031070001078100e60150006040e14600c0d4024401008410f22021a20701c2e18000c4662005001c6034000c0c4251003540a10b009540c801c2e07120385400c02c0d10158608003441914802e48041002509 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 172584514 1250 172583264 172583267
    0xf0c0e1305060a18120201020c0d05090a0e0702030d051e07020d020d11150c0a091e030803130b0406091205040609170102190c0302190210080603010b04061e050f030703080c071a0a 79
    0x4002d9060141d06041d33207081454000142c15005501440c6c00229542001c00c0d40d581c03081003a41d001c40d07002c080402c03081c2484508004880812264000c111185000041d4060710109035a0b400023100c2e00202600200303c001640d1820401c1c18112542c417032803208840f00600c2024540c051001c80301c0059555860820080040740340744c100148440c000f0000c1140300c000c800100007140d82002845480c1e440e05000c1c070541e100c030350002a00c09080181888103002c601d50004551510408410321030b0070b400501a900f60013144540c0000c5070f402041085031105010881240030712000006251540994541d214103803000540c10029641d0910b8404040c1c0401c0404401c0070528021501604542d00040f107541c4000e0702d134000c2006039008604241c9094015410020004109201e49500d0341441d000c1050070410101580041110000f8281460307a60280d000b00043c001d00031380b9046072610b00c2c0d15440303031030fa006492103604000240d20070707800046161010300b01105c80d560b41e0143d00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 172585764 1250 172584514 172584523
    0xe0906130c090806090604020132040e0709050a15030506030307060903021608030708030a0209030c040509010b01080f130209250906020d0215010612090f0c0e1305060a18120201020c 80
    0x3c2d4407203a004c08184070142c1e0f02b055903a208201384441011340520110350f0700720b01d01543d102c401101580420041003411034002000d120307065640c0c401c141c0940d550104007400070340d07110b1000e10020361203504000703078402d0f0012030f8446800b8080300d142161655030f1078110340065005400503046540d1641e50317508102800c4004003000700085062141548400d4801d210203001c0813981035000500b09059241840190100d0000070800c00c030340e00e411481c4d01c0c007034500e045840d4000343c54100000d0031404804445d80c080c0044403800c0c17400030003e50a0155090340900001c000300110510901d4010302c55000044500a81da100001c0038640b10000c2c3c81c0508400307403802503400c686800000300d956101160304484251402a074000d0031140c0001c003d000680001c0c055000c3d0207001010701c100141c0000440b9004101030380039944090b072200c400c3e6003540d8020102d40118010520042d055003040c075007101c41d40c0d20100c040b070f110794501da08100410b07203c2c000b5075000f05101500c01c1c2c0a00 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 172587014 1250 172585764 172585771
    0x20d12150b0c3316020f01060b03070f1403060d020109080307031d030118020f0409050102031617090604171603030e01051501050d021b07060509030705100e0906130c090806 76
    0x541d000680c2c03483c0004022074040003450001c441100305614095244204448100b04005c0402000526243e10218215900c100c07100d4001c202c4566103408903e10035146c0700c10802058100c1c90854803840c0800150894042007a03042009040010450314010f00c0100703400340c881d4403401602c0c05450550b01c021010f500c19244664940740d00060440204000e0310080c1340c0c104e91845085e01180f00240082c882c0c0b1034090031541c070110400c0711220000808240c0640c071078503401002409a003000d0041c1d5000c94070341c82d4542103400403400244481050340301220b10a82d40c2400d211000c0b60040801144040035000a5155041765540310401e12880350485501007050a4156400d40064000e10a003040c285145900058a03001c1180b1400c184141c00c408005071078081e940ca080c01003c6800c04d10506202e800f880720b0001c1c4e20300e043c3c0000702011286458102ca964080d02c01c11040750700080a2079040080104121070750a00c1e84a8000181c2035500c9078030549041002c003600e17100005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 172588264 1250 172587014 172587073
    0x10c09090509030307030b012a0b0c0301081203071202070809090c040b040e090705030d080712050f0105060d0902030313080f0d0e131104030c03050c01020d12150b0c 73
    0x1010b0040540010048941c031a00da4240440d07130340740400040729081e04001382d01e46444c1c10140c8042c003400514241a000601411104110703496101490205100a1180c0d80c0b180e480807140e40ac41c0e60020001c1c651000c01c50504031815000b1049041c280da02c4000100c900040010b0301009c60b1510210f443c0c1c0101d444802c260915003001d6065986115074002d80c982c510141d03000030018032081003603201900002d4107440c400c0075500f0020300b000034250b0700c1d40040b410480c54825007001074424103204002d0446603c0d0180d203050140185603210029858001d40c50b070341103002507202000100010000403540701ca280f498200c0369420042c1ca494064441c1e0003800d0300d00b01d915404800300d90060001c648021640d40141c005030b008000401910b642c40c140030400005216840f039110301103a0085041d140c0601103c001286c6a02450b01e5020200e08000c0c00e410201060344d01c20300c442818003441c0800f007034540c8207148050f00300b0f4982c2881a80b054150b90f400441211116101a201 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 172589514 1250 172588264 172588271
    0x915030203120d0b0d050a120c02010c03050304020423060a0b040506030c1605010908070204050601020a030f0f050c06040606050118060801031502040b0307020a12050403080d200c010c0909 83
    0x85500181e19405040b100000c41c2070042196039040b2290f51020340e15000081c00042d4031401403805e02d80f11000c401040c0c503043e001c1c201132032510b8081d24910007840d41c141e5402c0c101d04001d070390a5500350806001030342c00c10b40d5a090f403420541850421100c849449403c80a0780ca46181045000409a00554401202808100015202d04041d290004e1800b01601e4858902d980805000d445422000e03000c0d40c00d1110f040140700d4514000e2042c180282ea00348120b98400006a03614032a840c0002c0006140c4480184240d115401c4c40960205070304c0e002d460100f44c0d08485107010800d9600b03a07482981d65000700701c150781183d0803101181c081000b640c4401e29213000504031050510014259184640c0c0c107450f000310550494000e4005500742c140c9074140820001c1d91000c8112040b0f5201d444449174140c5140250241d404595210014925180c030340e2001201800f080b11814081003650000300034540f4030740c4064400550b240700002900a82c04400404e107045a0344081c2c1414503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 172590764 1250 172589514 172589519
    0x160c05030a03080a0903020307050a0602090112020a120b01050d110d060603060b04060c030507020d08070c0905090c120f0a0302030c0c19060810030206032a0a020a0f0c0e0406060915 80
    0x1000300041364440c041d190300180c07002940c10240d085105a40c00100a80694110304c2c1c10001c1a0b8013034a8030f01020b0ba40c00510205100c5100c04920501d003a603800324441907001101c006080e00314110035031040c9441030504885041207000c1d9001019813000d0014041003502c50115a445018018039452905110003464030350ba8032030364032980c02038004110072140040c00381340c020400c0b503929640c050114031002d07156041415103a04000340460317004004500000f2000880d0051a009070303044406031a40da6515030801c103c80c444c000b4844242c0c0502000401e2202040c000790003800c2c000d4000d580d131031a54040060a040c0c40412442c8146401000c6c9031030031460f1800001034420f241000d40b11512010002e0399003880592000798001c10010402401602080c2c101070003070b41d1182031817114404802059844d0141c194410b0041c0d00a1000c030000c01c940c450504006030080030465081c03a100d400c0709408101c06ca030181e42c071688030f107020020303003000744100410550f0f0710404240450 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 172592014 1250 172590764 172590767
    0x130b0a060e040534050f0a0c0515040203100b0a030b01030b06091303051204060f090302010606020106080a02180711010c030902010f020f06010e280b0a0506030f0a02030a0e0102160c05030a03 84
    0x44800500d80b08000142001301e0814040c8003120030310114440001d40b2050b00e000000c1441e0241c0310101c65501a41700194604000044214010381e801005005c42442501c101001403c00382d480c40d5200e4545070000021645a070038031406107008211207102850b0000038001c2c00d40c0040c110036402412641c0d13400100b6401800c0d54480700900c05880425111401c1c66070140c0140c0c0d09a1014501d441102c004054056000104071403403a0000c0c0300307244c3e8501c000d039103a0000e0300f000b0f900089030080c00306010550b4100715601403000d041a00c5000007500b10ba03400c5031004100d44000c00da407291801d095680044680c208082c4604c004c0101601d14a5459101d25042c86498802a224000701d003840000068035503041400c0001511454010610840544451141d190080c189440c01183c142040c2044034815201c3e19960322264880403a100029030004007802c80503555526411102c0c00c003030006203010f10364002c2034902c040e0b05041c401f14040d0294090b43c403036482000c100c80082d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 172593264 1250 172592014 172592071
    0x209090a0f11160b0601030603211215092a0c0b010b0c0a020103200c150109180b070309020a0b1305030609070303080c0903120a080a09030509130b0a060e0405 70
    0x61343c402d400c1c0c46a42c59407030042e005442d0310f0704001c0000950800c4038452a1101080d241c0034000c1e55141d001c001e01d803030b0680049400c0310710701c15845041d48a0038030801c030f1390350401016800e080d500e40074140e00d01540034002e0250441e5010000d50060141018001200d0025003d480740f400160314101381483c0b000d03500d40801c00c008dc14151601d0b07840414001c1c3c0c40007541011445c0409603a81c4401c00c0c00d4684944400d007004280309050f00011462034014403541842000304408003841c1d803240e4549a00101c801000c28040548400200d00103071600d0007038600030105200d503280c4a0280016400d075001e4150040c2e0300a901241c03c011450000044039003c0f40d0b0181001299034032031056031843c070f200d200c114035010b00c56540004188800e8900400100c1c0040c0d07603048854884e200311005075003a016000e0006242805141c1e0180ba0144403841060b818400c0014044070aa01003210908142d004c0030105101c814031a8550601380101075014088030701306059448603407400001c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 172594514 1250 172593264 172593307
    0xa0306150e0405100504061205100606080f1504021c141504021b010c0207061b020d060506010302160303060812030103080403030c140a0f030f17010e06040209090a0f11 74
    0x440d19a8045400d040c0c10561a80103400060024420140c46025024408c141044210b8143c81401300760041e03014641b0500094407565a6245503540701c050318278101c10070240544501640b0360300c0dc1c406030b5881c0d200804018603a442450031401c41c403407c01044400780ea05100c8401800d80030411004414600801c100604a40050315500e6401090040d1405901c60103a59840e07c0d6070f00c0852034002542c02c080303860590f0f034450480b01d815146c048611040c80b0083d002020800c41c070000031003a40007142e001c1c40c103240050611840d920250b640c4400c042c0c0a50100707a03917003801c0c403c20302c0c203011140e181d00b07910303010b14a0365156694103100c502c528400941042200300d009130400c0358010000400306883c504941c01001c080c01d085e0380751480d440040380031929a03060a0441800384010b0146901c071942c1001d0340e44e1801c4003030f1046810040503e980716030700700030180090f51649031080c000c02d0382c488005245501c604201c0c044076060352001616450501000103d44004101da02a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 172595764 1250 172594514 172594519
    0x90a141c1101060e0f040b06030a0305030408250f110d08040e040c050d1b05010e0108070804110d0506060a06230d11070803091c020705150c030406050a0306150e 71
    0x44078001605014010100fa41003064081010b8090211010340312a48a0256010303240142c81d81e101c030750405a56840d5410000d010074010300010f00450349070303400340484c107018501002c0440f641074550303502f03482030800442e590101080d01c0300901042c0c1c1c000d002d104c4002c0e5080e03d00341e08162180c100d5400b4610031b01c07017111407144c001400c206181202134001d0002502824082446181184e0517521040c07201482c04190100051250300c101101000544182c40c0c40c801a110f9810480380f01000a1060314504280345600346240c0340c42007110030381801200a002c41d414024204107110481d5401a8108a150b6241c0c240c1b0b024010303841041d241100c0502c5560f8514075480344086e001d2903540c1ca41004010501906200210000310b210351f10030020741d10007100603401006e11034100035880005a0100c0740a00480c10305e40c841d00b480b521640045030500b22100b4005195500075040780000600c0416400d5403140c060062401800024240015800c1d90f50401070036540007600940c0b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 172597014 1250 172595764 172595777
    0xd0807060e0616080a090308060d1412090916091701060503030d02040305010c090305060106030207050a021e01021501060509040c1b0b011706090307120512090a141c 73
    0x40400c41260700c00622079031008140e51841c6000003104418003040300d10325001c00d40b02c50002c1c03184c409034404d00b0f0919038141c90340c2031a500c800080c0301d42c2e1740d47c240b1300722194522492030022220301005003200b40c403076810005a0340c01d142d105101c040300c2e001e40349808d0380cc003079104585020703042210301054503070484000c072529080403051409411698001c940501000910032a0301d500354004009407801440240822030400704210b41c0d140c80b034480601540c00c5a0300512900703200e80c004141d600e014500300d5010060384c1d000203294003400c0f05086041c00b604103401c0001d517010301c0030b161041034603074440c4000d61408101601034032a4100c241d104030754450001c2000e41c060ba40c03c642c460b40045201c11a19142d18082851404c28000e00140b40a00f18280001903400503901e4401d0710074002841c1002c00c1d559480391540c42c849000b2050180c1405444a82c1424070000c521030080b0200400c81c048150800701c0941c441642c60b482c2c4c64101100c8070600030311442411115940354034209 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 172598264 1250 172597014 172597027
    0x27060f090d17030103060b030a05070b0a052506060e070f0e31181e0606171b0a080c090c0c19050f03070b0103030804021c03050a0206010e01050d08 65
    0x9000401060390041001c0350040000d00c2d0085a5000b4505803403080350708001c040c48040402d0741d501200b880003400c96005050500c0180202c0c00036058503801d0782032950416014005903032003202c00304c0744060b520891151000c10301104e8040c0b08018030000b18100890b04094000400101c050110f074020700000c2100000151981c8070b001c00b0744504001911420300b041d0300120764909001c40344540762800c24640500d2081c120044442565210040c1040a14030070900c940361741c948942929001c0d034960b4000390000c0305a1000a00041c2e0a01800c50014109041d858841c40f5501042c0075a00415042c0110240000c4650900c9001c6541c1c216070760300c14480003500d10480a1945c1076004004040341d1100c0841307058882e0034410340035140c9500711110300542c2c2c4c0c081c814000d04001030400040000c170b8052940b070707030700079002501c034030f01d801040e43c0e403d00c0100700c040080300000c000040c00c80c2d0b0f0541c184070180c0900404c0d0200100ca501d45000509103400000c0043d011f2030000642 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 172599514 1250 172598264 172598269
    0x70f0203030d050a0203090105091614060d0606080a11040b030103111f0e2107060f02070320040f061412030d060f081509060103030f020a150227060f09 67
    0x740e902c1015802018401c030b1800c0414200031750000c0d11518413035800c0002042802201240d134041c4808d0340e5203044200d03403600b0041600c00d50880b8005400c1642044190b10040e0319000d608013510342500d6108007030a02802d800704840c9110b40100680b42e05100c1444410201c208480c1180c0e007000c0c071300c5042a000e000196500301c046107002038000c13480303600100440d00400d1107061076204554034410030700559103042d140c800302e0181d000c058204000601200c0d00413082000510150701c100c0d642e00b130b1681c0e6000035140b0840c49c141c0c0032403c0c0400e45203c602c9e0600500181000498003400080e1404842583c0303e04080c9886101e500030a40d60800001e0820569204254610041c4041d0340d5a0000201c10080c4e8026000c0d14022558160050201100141d0094607000f0080c4403907840c54030101c0d401070f078440c0100c0031401900e4081d0f0110f001c0900035101c0700030a90006907540401d98503840810f003025410140c00d0850a070038095603130f81c8800e4034800c210064009030350703902d00c800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 172600764 1250 172599514 172599517
    0x1d060a0608060f1905040f050c03040609030c0b0703050a05010801090b1605090a0e0108011812180e0a052502071214030c0a020906040504080702150d1802090703050408070f020303 79
    0x42d16049820305401c04a000d602031060304c2200c000381c4040040401c2c030311402056543c00c5405030001c010802c003040000e060b03a03000ba18024002e25000204a650f80e884000139034081e07502c02c0c002034a5500703001043e40248501401046184001c01202000741e444520582e4010031402c03442c1d014490890005019804032500c40c2c000800b0106815161080c0c0d1840507001e002d540e0310f030b42c601514101901c0d099a685400203420440052045840d0b00341251209902e84031801e01980014001960150003102d0300d00072444a07502082c2441c0202c1158130000000c604034103a8a41d1102c118442c940209010f0260340c0a011120744101c183d06110203645003030b01902c14070b44400503d01604250100d52560302602c201e8001360349440d140d08010a4070020303035002c0c0919004110364001898400c01c8000701d021800203440c20b0101c05d1001000329410302015907102138140c0d42034821458652038050b0b200720582020407146c140340e03c0780c02c02402209001402d1180c031740076a0302595001c20 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 172602014 1250 172600764 172600789
    0xc150b0301020a050c011103060d06050403200109050d02160e090c0d0803071101090305091207050405011404050a2a052511030f1f0615091d060a060806 67
    0x10002d55682c0201800100306511400b01c48026500c4c045202445000d20422a402100014603004604005460344401000701420440900070704202d0303002e070b102d1034150b444030521802d0000a40542d56051440c01c0031103c460120454101c002c20200721040050032605544000425041c280d440d4400c152609280c0c030240b551018540400c1401c005170040250f2240e03003180c0d100c40c8404660b83c2e903142a42e05140001780481c0080c800c8900034104042c021210b01240c0d002c640c10280c0c0c4501240486000381c0020401a00c04620b0000504045c080c180d0400c0d440c087c104007452140c515007281110f0f42604d89048840310441d0440c1ca1711a20a071003d1407544000d00c2042c003070025040701010590142241c1c8941106641341081c60049440b400010b9964003030800d0096082030b1010000c40e0704a030384081c130b54450000c56118200000c0545a807030a80300e05500c5400c0c0300c2c2d64070040559072006a52030090400700038294980b8024401141c00f2424810311035100d1000190b00d10880c0b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 172603264 1250 172602014 172602019
    0x121608070602040b09010908070b0313030e10032003040203060411030a1a06120309010c020f06130305030c1501081c1b030c0c060e0d110303190207091103070c150b 72
    0x100380403034290f4404c1d0043c001c0580980343c103040c0a50f21070f88981c03110171500c50000090400e03c00079100703003002c9000c040c846200b8601503203001c10500019070b11200320620f0b20006580c80405c000161103841c0d0700e054560000d407425040d886e00d40d00095554100a2000300b602c600f4036000851600e08000c079003403c2d035000c1c0800d00780800c3d80d000d1481c00d40003110000d01c04c1c0c09d02741e000141d02c0d0020044540d00c0906030340d0700604400325024030190811060450b500309008000d0740342002c0c01d5602c4032010b54401c1024690f69409110002c3c41d01c0e01d28126690f540000b54010005107100068980c20000304800210b41040c001c581501c07202040c180b4150070449550210003007560040c2c003010210300c0741082d00c0001c0d4030350340d04032080154150100c2d000b040043c444070115142980c41804520006c1c202e03884c01e5030600c40c400030070302003003456005039019401c10f03c83c1805034000c004074110800007050451401070030080c0007100d03030907014040c1d0403103401070710448100313811402c1c1d8990301 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 172604514 1250 172603264 172603267
    0x609061404050f21090d0206090406080109020f030f06040f0303060f080606090c03161209050717070504020f0a03020c46030f0f0507020a09050103060e121608070602 73
    0xe0505607110710304600c5a1185020f0a45200c80311103070501c03a1340018581464981c18803240c58180120085110011b0384c0c000c105115544555032603008400c00317896104004100304031706105010303504120054091117170700102000d201c0b200000076003903402a04402400c0c42c40308181025402060241c108440d020806c000c04181d8101c0051464040e900c191040c200e160765090518079107020681d8403c40071800e003800c8602c0c440c4035100e240c1c1000740c6090001035440c856a00c145c6085429445148141f00c208841d9207002001d00545008080c25139003503140010701d40c04915684190036240080c15170100303490318030380c100b04580107001c410800315031070b8000c10204003141200c404118000b4844180c01200300150114515401139625440f959000140450251120024500d00c0000c0000501c0400090f030703200307081d28008100032500018a5410360401c00700390380021186681aa0094440c4403040d0030410844480e420441440150300b482ca10b450070303180c460600041c103000d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 172605764 1250 172604514 172604521
    0xd060b040f1d07021209010323060123030a180501060b1309060b04050603090f06040309030201080106021908090604050409061d060108031c02070203030a02100605180406090614 78
    0x1c02a21030707001e41c0c0c010414031805011001901d61207000407510b01e00180c2106030110304881e0f40c0130150001003c141008605030305080d10800100c01020060400c1d81a410180b000d29600040380c01603a01100c503401d0801c1c121440b80041d14800680302002d556580c20f07815500c012102030004000f60b004000f8060035580b407030320308203c1e0000c0140c98041e00d010b10000036040c04510441080701e80340d0381c29604091034007007040000c1e04010252400c60207070103c101c0580606200040c42248a61030320901303103086000040c00364005030008425544601c800d1000da078002c00b05240c200380d020380342039900d05959000c5101405603a21042c0c11604018401c41003201d541c109030412040c0049050700c1865040c002681c603d02071041740c070180c10800ca01c0c4c9074004204540c00c11155003640140c940304072035010070324591004400034011f80244244a03d40f5016018600007070104803040300c5c903001e44283c03403200094040d200510702580c8502100821010307410441d02031442c0020010b0525 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 172607014 1250 172605764 172605779
    0x60d0f060c0206010509060604060c02060a02190f030207170a020f0a050d1406060402070b0c0c01150308030405010609020a021e1203010b0c0c040c0e100e060309030c0709021204080d060b04 83
    0xf00c084c00744511501e007400004040d402e2400c141c4046034030a9550040e101c0d055006d10040d070340402d00350407c60103012031014203007a03140c9500d21107900c00c0000b803030303c1540350800070300f07119281e000a010650400040235005100080b61b032407081c0c045421140320400c0d4000031340200d01c0742c0d2040744c03c6504e98503220148502030040424020030001654410ba85040800040703208074000203040b02c0400340401d804400318406003414246041c0002070300c4a011916038924019035000722200e000000800003046401e005080061042c56015400d1070902c1c94042d4407480c076001c1c04e0b1120070032501a620b034103404124000c03001551001c2240d903540c44030f0b81c1040c02d5114908116846c8140b461540c0d160506215105505450340e4514020024410401890741c4580101c0f41c10000c0c803001001050342c07450011070103030440c031008541c0c8414805441d4103000c069130000183c540305105911102c2500c1415691181d44a08055900d10410243c040200102e4100c000021004640401d645 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 172608264 1250 172607014 172607023
    0x51207031202070602070510020303070809070b07080306010201140103050c2707111513061d100b040b0f06040303080c0403060606030911060712030209130e01151706060d0f060c02 79
    0x1380c900c3e601303440318a900e030f02c103201d0161101da6515005900800c00980084d01c1000400d402401000542e20485c2d075138503510300d02d03400206d01074070008000130a0210540c3c091180d42a41d0340c50303140d0a400e940c0740d610754070345441030ba811060103241d034056460084142c42c030600072404035181c80100e41d07090410009180801c1c80f46010282d20035440752901c10168802d58621950507018420080078540c0d80e042d0140070061719850030004000c0c0c1881101d00280100001c000f1190000526820008104010f99840066090048a03040740340359607600c070b800445081d00c2e014100b240c003580318156081554803039548054007451a1210108850780c2c19002410804c2c02a01500078518a50040100a01c10020002c200160300ca01100714103010750040d003132514005100c6500c0410b001502000d035600307074000000c642d5444c1d082080303a4036000c0d6020060300242000720b424103100c01c1400d5888030050301d0300d4400c00d08241c10008100001c05a030b560154048030034481d2510204000e5941c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 172609514 1250 172608264 172608269
    0x30506090618030f0f04050d060b0a060c08070b070e090403051207030c12050c0d0614120c01020d0305040510020a08061201020a0507030c080405030625030b090105120703120207 78
    0xd8065000840c111401032151495107000e0301014610740070510072280c0ea282e004580c194013060b0b041c0800a520703902c20740c40503681805010b0100e04900c40a08000d100500c3d03800c00d50621840c084080c002c10105025504044e52200702e83e140c540b503620040da2824010007407183d20105050812080550040c0505407403a88100142e0f51078540348402c0c2e090755500100c1400064900c00c0446160102d030300190f03044215a441c140ca4001c01c4d8503d241552000d0b081840c2c2030b4000c803c903140504141000710781e0319110001a0210000e6000001d455000c90042c10040544500c04107050020a101e04482c009415008559442e054000500025011100300303206008031080c50120303e4041c02100c0d800001030f51014036020341640c0984038140c03000c000355100c890611001c1070702d4408101e450300a40c903220071220545021211900321041000c0110200742c01e02148020f1602e50041513810740c1e1040b10200c3c0004900a03105242605a91010b8140c0540782d03000014213401080820a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 172610764 1250 172609514 172609531
    0x51b0f1b010806150307030b1009050307090204060e210a0605041208040b0109020f16030201020909150310022104030f020712080409050c04090203040302030405120109020306060f06070606030506 86
    0x40042500152120403040712411340004104980c3c40460065400950b8401c1c3da600307000030703002e5003400800c000300e084400310b1000c500e1002044c005441c04000145c01013208140940c81c06080450007400e8900c904141d600480003030560012800d45440d2100a41c0351500848140134090300704040904001c0d50309171003d0001030011150035100b0131141d48125000f2150002c2c0380d1800c18408029030105a15040c004018042e060f07118084104101c00d0500075400540c07110f405204002081c98040c1030f03c41500300d034000343c000782d4401181074000f18882050040c0c440c8400302c4000c1c0010300c40c100c0944501d140341c042100f01900454082d9040d40c0e668200e03a54aa1640320144103105042001340090b04288402c0000030701e25000154400b6110b000c407410716603990501c50176600180c070b080b00581c1004c2020300550a101d1380c5940b007000040001c0c00400302ca5000300e500d034030014003014010030052003007141135100c2000310340c40c1d00c2c0c2c025000c1150ba40d0349d00341103880e6002030351400e4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 172612014 1250 172610764 172610803
    0x40f39080a0204110f0f09150a0c0212121201030507060c030c02040c0e060d06060305150d0b060a030206040801140714270604180e030c1203040201030906020a1d040c0c0201051b0f 79
    0xb40e404200b0030942d13540441c80c2c0c840329403164558003082421080e141030308d040da10603045260800e20f02e10000d40343b0244a001c4a0340503505500d0118208111600400100070b241162200401d030302041c41444207405a40020f19101b01d11011191118044001e50300140e0000ea008010113665100004a841999040242d500c41c520808a5814038030300841c2d22070400c0388d04030041200940001d0300b00c0d00040640403255541d034080388060704954403414035655215144103092215000f041d5120913103150424076080800c11110503802001c408074140311114000c400140010041003410181c0100030380d48499503162003205c200c00d260101d014031400d040e64590b5140c000002d0b155441d03684030141001c1c1892141c20040da400080090b410140c5030500580070409500c001d004418440c0e42d0f68184110070401104405014a45a40685e160200c1032500590004180881e240e0902e007032652080d21981d042c4400030014030080060107206006a8050300028500d0100c00c1d100d000007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 172613264 1250 172612014 172612039
    0xd0c0509030c100c15020705240106050304030914030a060e07061b0506060d210c031b03020309101115040c090908030c03040f39080a0204110f0f09 65
    0x10990910341d0000780003042d541c2d0030200004809050319140075417809401810030f240e03611114070b00362192202c2028100e0028052100105142c03d19000d04118107107103142d0705103036400600c458010b11448495002804003207141e561306002241c410bd4000d0400d001408010500c0c43d180c540303e10501d801b0600541150052003905200c0d0214250400c0c040c0009a0f24407003440b02c0a1503580d0200c500b046201e400c07040d02003089070700c5212a0081d6451740c500d9070051402601301004422041035040106c080440020390010031a050808240c0d0500400c14008000b507400340b440c608003103a50f0099185a00014020b185030a200d64000c03003107000d5003030b03a604030601156001c0742c018103a07803001c000156100310003800075038006108048000c90741c40151903210052041d83d905141e0841403a001c1d00000803c154142c14540c81e0540c1100000c2c0341c80800c59076440f6051000740140d80b40d4a22818a15a80b8181d420b460100c200035940c0f0440d200300c005140e4000c508480c452214070042 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 172614514 1250 172613264 172613269
    0x20708060603190201210b0918100c0c020301050a020a02120f0706091509111026130516030201030f0504260405060c010f050604140c0a050d0c0509030c 67
    0x305401030002501a248240c1d89081c501c0110003a1042607050149552030381c2c1004141890044101019640018880c004030307040041000c805007074441078040a002c042c90311b240108140626032410040021562204c03a816a0108042c0501940c15403902041040c0020103030001c000c450b000e40d0a84030307080c2d40c4180038019405407030b60f03100c1840c4041c000e2000081a035484040c00c03601a424400c0516035585080d815034001d040101c48030a101304004100c0d00341305800925191060a0904d05090000c005080440c3c295400b4040a2480c4010641110100d4564641c1581040545a52410351071003032580714220710007280040d241c40c401c0d9252410034804d00e8012988841c1c0c044840c000701d2a0109100c140c087c40e8000d201c420080000c040ea680d500070010210b0301400811542c180000f1001240e2000b030001d0300031400d0500ea2400842121141c41d03024115681d101e40300c40c06003000703d580b809220380da100a81d1401c40c040c121036411102418812074110112090110910705 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 172615764 1250 172614514 172614523
    0x10f0212090106050d03052205040e0a0204050a06050f0d06110301080a1a0c0307080709150207030c0e0f010308030411030d0e190609060c020325030b0702060606070206090d05120307020708 83
    0xd000c0c0c001f903000d1003120b00c600d03910400c0f05102d420318031080090036150800201180c29500da0104e9580c0641e10040450804e401041c0d0701c004e107440100200c510b000c000ca481001040c440341c0c4100d14011003282002526071260031850074082c41ca9880c3d68503000c980303981d90100d02c070550f1000c1940c60b42c5403100f0b041165842c441c480203504c1e00d00310344031030a094a00d01400747c211020700190980228501802900f402d24072042070340140115461803c00c0c03c207031625504800030002c4054100210214000307892411030740c1c007401c02e5a03607079a141403810511694000007070b4980142c006078900d6a0b8460a40c6190a500315120012182d5201c880740b4901d24900c2a40041224684208010750144001c1c3d0800ca00150507111400b60300030711940700c40e00c091101c5980c410782e003000b40244502a40c9081d40202180010304a50410300f001580c00d0250000081c400c01d400201c0001a8560100903941254000107d4030300d041d5581214401d5001110110010700c44e01e00000f0340b5010004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 172617014 1250 172615764 172615789
    0xf050307080307030903020103180b0a24050a0e04034b02070506030901090c09020c070609030b0c031009050708070305060a1d0a02090a0906080c040908031602010f021209010605 78
    0x80701d841045e440d40c2e00540c00f5124107103412010284e00d441c01c501140c40941480d116086281000a020340b4883c060800c5002c0c41e94404155213540f1814041510703444441419103140c020b03140b40c50303070700c0b45400c40f18000f443c90003c1007103140381104403c4200e004800c0582612140b81c0103c0349251007208454a4002410100140d100b824100310b50b00305140190b42140c00040040f0303500c0504c0d1a02c1640b801a98040c002280d030005985100c5002441030030f01030885442d00d06001d6245848400801c10082c10040c15540000089003607030881060610082c181d5400501031807410344e10252006200f03c0b80e01010a040000084207460441070890541c0c101c4484c80d0305660007032070700d260100c00013080f428484d9400c2000c690f243c0d6074040d080d0b004041c41e900100c0e42604080810303041044069429000c0c07810b150a810008001100340ea601030a5100c003440c094000300004c0f40905100090781c0c000030310002c3c81074140f04070181c0340c900c240308006c000d0000c5980d0750140541501c0c0341 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 172618264 1250 172617014 172617017
    0x122106030c1e030c27190903180b04030309060f02010212090105060a270f1d06070306140108011211041a240910091a0a0201050f040804141503010f05030708030703 72
    0x441751100e45400381091150818144100d1007010b40c202103030101221002da4040d40030a801100c2014020034825129018115075044076041c40d20355540a13140d007041303001d11014000382860f84084503200354195a1100c5c1d5141d6044e05500748002c50038001c100c1030301e80601940e400e1001007483e00030040351a51048a40250000003080d21810500824241840740d407040e880c1d144450100c140c04603120000b8404a000d8035980c200084050f0440d44598400c0440d44071f40c0c40c41060580c0c0046c0000e0440300d075504c0d010092220341c81c0c400094021103032a194014078007010643d10050f0343d01400480700d03059071010044614a052400001426008491191810002e024040c00c006040d081400502e00706001203075121250030031055081c140c2446010b034086846080fa81d42406103d0304040f02501c0305c0041d080a44403d21144100d000700e000301504120070300360301c0c0c4907454031500b00750080c0c0720503031130703585459034620603a94a100d882e210b449107000211382400080700f115074040e490b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 172619514 1250 172618264 172618309
    0x1006050303090d14060702030a1119080705030c070b0405180906010b0705120a0503240108060111120c030705060603150a0f1b0207050102122106030c1e030c 69
    0x14204004841d2050349080f80e84455800e5131800700c1100f000340302e00a00c0c080d00a19124011050005c00040103001080d41d41e074404000740c04000c0300ca9034014402c940089070300b541c440082c2000780c907621811840040b40d1160b9880018800c0c50507020303100307440e030881d581c4001d4074031940640020346040d03a00700015000311004115081c0d10704010701a0922507401d0f6100c01500c80b141000507000b07031009001040c000030400142c4442c206500c52990719030262030000b4803107400000d086c041d00800b49814070000030401d440705402040307200290040c1001d125a1020000f038566201d81220004403101d10032000803c0c2c403440c1c0440e00c0744042e00025040c508640c3c90000c0480907042680704221139982e224403c4801140e40444410002c00075001005100e00e00310009182034a0120b00c83c103100400d0200f0340c03d03011502400c1c0310140c0140300c499059125000005d040025070f200c45580044400380c480852000920202d006000440a66421440041c03d2250305104158007002c074903003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 172620764 1250 172619514 172619527
    0x3021216141504060c020108100608040b0705190203070b070801120f030905090703090203100506061c06050d0b0a0507090b0912011103090c1c030923040504030806031006050303 78
    0x7501420300441c0042503400c6100c04031003601c40359072060704210001030790444240c065580150b4102c0d0030035540b04140002c1072411a0045c200d440180009240c20990000701da40d081c4160180c0b2002498054000403481c8800320196803580a0202112164444000655182c0c010303010b541c100c0f894081c0352584400745988141590003a49403c0f418003132791070800b00f039a407207a43d6070502c80c030f00c5070700c002440c07100320300405251400680e0076919407810401040740a4032918191010202440710700c0005a540c40080f230f01410040d0425a003140c4000d6520042c4941120030781d0040141900401040d180c000c011910030321580288000d0400410249001d0b00341040b010000940d0340000044039518041009c415900588520420b0f902801112011f45020407a0f40b8404101c03902c003800c0d0345900d50340035107c100e540c4070b100004062006c041100c00c181851585684038010b00400c0700e03180a00d000f805029081e10704130302030b101e408104880900c591081000b503c0b0020010340c00c024 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 172622014 1250 172620764 172620779
    0xb1807120608030a080403120504080d020f0403020612040201110c01050406050d0b1e040c0215010e0405100f090b130201090e0a060305011107020f010c111c02031603021216 76
    0x40e503850000206540d01c00000700340d01c060000c1d0080300641c0c1c1e2074041605050074020580025202409402450a400e200014806508459800000042c09612180c80d040400d015008541c00a07412210004030b41604512140c8028401c5100b41c0f40c5681c030f501243c14055941d1000c01c0a180814800c100601209004101401c3c0c078180350900440e180c0c0e01140480c80d501882c40320010702c900c8420b405602480e0602601f01da03151684020005050744004030f0220b01010711501010440300c00100741842014448001d02c000c80400074003034000c64118541c02826010426914840c0300c00100361030185180342e1000303071a0141d40e0211040e041407412204884050110306005980320303000000100c0a0198600f02c9015042468480155006200c0351146a05c4901d0400c50030960440c001034042d40002000c1e101520311031551440c04903266441c001080c0040d5151003078203c5900042c138100c1648007580e10170f90f001e40d600e41003c50007980e13607000e0704400c80f80c0100d414810306c0b019 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 172623264 1250 172622014 172622027
    0x1030507030807020d12020601081e0601090c111209040b040b01120b211c0201050402150a02011e02030907080c03070303031e1b0e0d020604030b040f02030d120b1807 73
    0x8900082c40980401005e030386e040f00d1400350b100100050380107900108040d80e0240719a03503a4140000349202c500000e02d4609403180014001c4540031039461a1a218161055400e0305680303500c0400ca40d04001a0344214400b41c01c030710001e43c801c40c1842c0f014110760400740120030b1a0359068540c0110060307ea11030f00090181082e295812001c04140c0d40303041039101410102541d07402c0068100c91f80808092449003a0000c40715007503a050009200c0141c440e003d901004070328681100391180e00101c0100c0c003400e07481100c45040c4141224650740566198021030160b6104000c0761401c0b039403124081e440b08075103680e09500d90860081000031074080d400000408403043c0030f481b000c1400c04601c1c001c0350a44428052a400301602c201c003116001000c1c40c014440880324640c405c0005d50002d00241302d680401045c48a032a80404c040002101817040c8865005054a088021440c00200203000d059100300d6014205211003080d4101200500b503c03540160f1003444582d146141134445 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 172624514 1250 172623264 172623277
    0x30f030e1501090902010324180609050a0b1002010902130c051204060e071e031103010e0f011e050405070308090303160308062716031805030a1106010305070308 71
    0x40d005440720860351101054180c0d01030220050000b643c03008500004003100c5446001c419042e40850090f64034201e80e1001d14112605016410850000b804d80500940a00d52115a6850401d0148000d801154201c90b50044007540e80340c2034880300800413800e8601c4101c0107500406410fa50f66402d61098102d00c20f00c802d9424200c0c40c0c400205800443c07030320100c5050741c8555031580140403074075080c03050b4030041500410510300810a1210f10804800c60300c00280500302022011f005031311b01390441c60340100313090151800d00103908100c50183c18080031500004d11508013034003401407a440390f903014640001c0106a07090840e0703100d05031075100410300c42d4540b006021400e1030016142c130050020388640d5a28840782081c4040c81480c0340c8801400048200700e80e0400000c0da01e00303801952255590414000c40d07603880c5001d070700901165421a207030100d4a0781342401c1c458000010034600141d942c905051040c43c00116445081c00c1c0002021508408410000f050854020f0100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 172625764 1250 172624514 172624541
    0x1003031412011809020603041a180d0315080a05060103050106080d0e0f0d2010032307110a03020f0c0d03080109050a0b0405011503050603070f061b0606080714060403030f03 76
    0x40c13400f130640000e2000c1e04101c400b01d52611405049800c0035624006040c0c010307004c009440c01e15090f004075a612041c5485640301015a100d0103a40141c0000c88030f00010b0040c3c00c203440309240d0038108507403a04001d01059a4540c00c2440004a0860028802d040400135a6660f112620803904020b060005e0040059100000c03802090201d00d48045140010b0300c52968104014170150a000c80094000c0700c107000e02d0700d012814810f190f41401940707000c074200c14103115296907100b020b07684204007840b515214410f5003103103810550000b54504104400c2e008459600000104026000c02d40d0303900180080c2d001401045405071503008683c0080079458040f41e400ea000307001c01c08680099014840e042c01143c41c07000719542600c00c540d0009001d038082c080190600c0d4150780d20b0301c1c151182800700b1600c411503104502c400829036107520b40c000004d0100944e0355810903039841c841d0003811480043d4184035800307454408201d40c100c0f40e26880b03072203026581e140705800820352241d00e40c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 172627014 1250 172625764 172625771
    0x3100807080d0c060b090702030a17010e0103020d0327051c08041e080a030504140405331903120f2a0203060108071805010f050d1a10030314120118 65
    0x1401e42d6104046c1910540c9542c0c000e64640d0a9008001d1004903007112202c0e620390b80b40014040c0001061195056a23019030b40c0c1c440c3d02c09a4502201c400c404c034403c00400c0111f07842808000c01202c41c104003200c80031a44a40881404407807891f8080750248000d00c0d4070390030001040380c0d05043d4845040d04640c0e00100d8ae4007551a003e26003496500b190890024000060600480c3c181001d11546408141c400300044d1611000e940c11030142401e2000e043c5042000b0b515004400c149490300d00d00015040f46001a0301d2100328107070311140e01046860011107103110034081e108880d8841c2c1046207550700f00071204050380b81d6003810714104070881188200b041e02c40150b01e08100190007450014001d05226181c99161641040d885454810f42410080100020050b252410056400485000940744080d1078191003480800000c011071000210400c0047c04049507104100c0c0d0007500c0f1085c001e034007581e404074541f04032041000d0105a030380060005648525070701107500301045001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 172628264 1250 172627014 172627031
    0x10e061e04021f0210050106030903020d0311071401020a020c010203130e0c09040504141e1b010302251506080a0b0403051308240108120903070302130203100807080d0c06 75
    0x307843c1c0e1040c2c60002c1c00540d10100c03029410000d80e2003500e004011500c7d04002c0600c40d079400030344070040c85c0c4089040640300c82103052011004411180314039804003040941c200c111072040e020b9045036480c1800b5001e440c118858035400441180d070b0806006140030790040c02c00590001d081e9028202030400c01d0288800e1441e600d852040500030f50040d110b00d01035594120703c0500d041601031960302142002404141510070014151070b825902c0000550410f11043c0124020f014440300c00b00241e0280c000b12801860900c0301c1e00c3d00500543c000743d1007410107034019081d280c1c2485070040c90b9011190324004542511521600248030746000d62614413a111b01507000300841d0090b01c5d007a004101d401c010311180c3daa00c18940c1190030b40c45100d540c034012295484042c002e084142000d0005011002e5981c10702491020b99401070003402d1107040b1501e1800250022501c2d0341c05026021404940313040009021412a1381001c010848031502210403900b614841400312901c3e0f0715560b01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 172629514 1250 172628264 172628299
    0x20109030b100e0c1b070b1b0a1707290c0a21060f050d0804063603060b030c030304090e010b04051f0e07020703080a17010314010e061e0402 62
    0x400c0e003da90a0072455444101002290b0401514174100340c48552080030204202e01c02d4a0a031a0000e102143c2c071005118074020700c03410a200700304000c0412002104c215522000e031000b803d103450081149003903160003022001c0300e603540c0314140c908590141000030381181c48040146400c02e0245003850407401105489065248551480d40c8050345400e424000404210141e1000f401e0481d0410040100c0e510394803054420f83c09514100040340d003a88107031180c0000001c0c000d122240d002040402e0300003520b107140180d40000c071603050401c40350001034517001807100c810400c001e01451030145092500b0004120703540007680b140d500c0b807400c21402c3c0c0d60391050300d01c00c40c822411208101280c0111965a03c1d4640261b0294a01c41e0b050002450f40011803000383e903400a605650f45401e01c0b0240c885404401d6886400c1e4034404c000700c100208d07081c80310302011610000740b02100340450501d490710301c00c991000941ca81d46034017802403601035441540150002d429003114102c403008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 172630764 1250 172629514 172629539
    0x30705130b0901110102070803130c030c0305060a05010506070b06040507120623010c0b0c0f0c011d120a140706060b070609030f1e0f05040807060309050d0804020109030b10 76
    0xc101c0840c07002c180c04500d540c01440400740104110001c61030b02520b9500c5803c20b00010b0141c0d92124200c04248003002080c00c0b840300a1a0810500e14910380e5902c1c0081c0d0fa0301c8200d8940b6142c0d800c00740001224103044082d02c0a1503480801c0d056259240800d101c01850020220300410401041014000c0c04c28032981007e01039098403203400c4842510b040c82013920849035103042040900681000c03440050702d254002284110680d40d901c0304c80c0f81600d09000300ba50101d419480e22280716000389010115020311100c0c04191407900c107d68000058a02a00c407401c40400c800c90148c3c030088403400c0090404512078040050207584070b00c0444080d400c654011940f069480072010b003410381200b00310010844500c4c0c42e001c42c1e00c03a0380d51400c1c080c404901c2d070401c0c08000301d410f0711801c3c05601500d0203413907100210780c500c0d580c3c0c601c0200500900903003518240940c82402c0d01d802e00c2100410300c42c94060b15604040c51640c0d91b00700d00a8002051801d030460000001b0501c4804000b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 172632014 1250 172630764 172630769
    0xf030e01110d0203041a10060e03030d06140f06041815170a060506040504080403020d020a0504050c0a1107053a0b060316060e0415051306030c060f050f03070513 71
    0x50300d070301c0c241c9002e03242260843c6c0107410380c03c0320208006012081c0d64000b0300707039000345c85d0900c851031034580401e146000f480c0400c020316041403004551000c0031000850340003000ca50340f0b4082c05500b0240246403186014a078003210200c3d91602c1510b225404c408004c6601c20785044180359540d940030307903100405804980d03e8008680400a0213514000d454010108540c00c02040c20969207010b02440f451000a008443c032654035800c0d0342d103000d070103001844060300071300c0306207007010710b07401d0035402201d8190100e2074a0b000c1e90509003000408205680340030f00b1000700d182507a4103141c0384181d6070608041180c4200c04003030015a600c1100100d4900c5002004014100a410103050400305110021442c042c14001c001c441d40c4400e01818040702603400143c070380e00e80c0a034480420100d411094201c40f0702000398000d40c40d103034840d9088030b0244c008800000d44400c421100c11105a00e0f10000580500c10504180090002103030450f0b10350504174601100c0f118800c0e41041c00360b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 172633264 1250 172632014 172632037
    0x60a0c0f02091f060216050f010c020904050102041508040515100b0409060611060709090e03070b1905010608070206070815030d03090b090307020d0807080903060a0b100806010f030e0111 82
    0x4880380f02c402d41502d6001e4054210f0340003611204280e881c2a0201031500d208103441013020300200c95069008090000c12582c000c0c2800809240508205001c2d520070b10401d002c201006030003441d124800c026081c0150f500c00d018102c019203120f5108802076000d00180e0000429140c001580d41a03d001070009180ba19800b007030f4140f6000f0003901840c915090840241c000c0000c03c020140d01c0100390701a40c00602c00010050701030031095141d130042c0c22000303009aa0303060503c0a1080119102081600c841505110503038940710212210102507503c800580d0208001c140c501c1d001d8210345500c030214402c007810b8003940c800020314250003200c040c3c01295841600c0d50601c000c0f428a41c0e40034585400440c500061a408100664400315010704442030108401003007004070400c8518180c0c0c01070807504242002240785000b4400244024460301c003141070044294003c2c17104601c501c105840d060183c013180e43c820b40140900d03244600340341d5a070303000c03ca40380c948000180082d4440c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 172634514 1250 172633264 172633291
    0x803060120071a190c0305040b04030308240102070e04150c0c050f01020313080f0d090b100501030b06030708070e1020030304120c03170f1501030b060a0c0f0209 71
    0xf0b20010120b6000b0040081c000f00350b0800224070308998460100251031114a00500d6030b03c0700741021241070041340c22a000c1d1400010f000810b140d489483c50b4040c40102c84c405900308075140d144038a1100c184810b0340560449502000462503107402980c0c8240560785200500f42d444007001e045490f103000034030104808a9004003400820070015951741400c400071032450808005500c42940455801002e501e0f00082c01d12240901006507014843c034200148207003212407508642400703080b40e1188407081820f400081c550310900810540305005040c207851601c485404840a100042042c420711840301844a491f4aa502e2105e181c8005235035841400f12030a942c88101102c64104030303c0541c000d10610001ca50044c2210918034840d09190558070303101d25055500401d4045100300c00b15041c001c00c06807851400895114901c1e406802c4150410080190201c5d0810320105400660511500d0000380c0a80c0420201d5405403150030144103030b070ba0000b900464201c0350111204413 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 172635764 1250 172634514 172634519
    0x30e030a080a240b0903010e01020a080702150103021005090d050718060501080915040c08070801060504110307170618161b080d0f0e15010e07031107080306012007 72
    0x41e40c2c4111080c42c00320100200c00c80750f440c05856000d003c07034028400c404100040801055409600003030681200c00000d54540042c4000074000480450300303040540280041c2c0c0148641100c0e0b001c3c1660740c0100380c041c0d000b600e400308031000d0700a0000e00e038101459180203408102c0402c41400140007010100d007284880c0a040c406076100313a401107050146e40010711110031400310341d6914580c01c0a00543c0c0656560030401e400c4005a440400c139405868804194000190040f2003654401d44041c130000011052941861000b22000c070700240c54a07022041c06069040c2458110300e004240b010705001c40c071405000c3c200192101483e48031084c0020202c2504644480312040114000d40300c00409516120307218802c0c0050552002c1d0b98020b00c4810050035849004087d40b0741c000c07544080c1441c0d1303042030440f0080c05285150340c01c1000040788148a40a01080c0c03440b8040740d00d06201c4680e4a81106070005006141170040a81b1070121981c510f4524884454080c1c00500d5401c2c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 172637014 1250 172635764 172635781
    0xe040906051018090506040206130515280507030c03120c05030f010f0305060703090501060b031e010905010f0b0c03041d16030506010c0b040510020a0905010216080706050a030e030a08 81
    0x42081114083e50300304982c500c003040d4046000e0b0742c05a01625082c0d034500201c41d0785034102c5415007015038800c82c0348a0440d00041c0c0403000d403081a200c00c507100c40100101e00180008180400007074001442004a00c00182c41000c80301c2c6102e211341840c588122020000c036081e56140c865800000c0c074044200010711203007071034403801458480c9a000d405815078842544449000705000309140d01d0341003140c1008802d50000008100561455880b800d140311800e0309000c001ca5900c244400282c000b1448206a1140d207049a0342030100b60032003481c01c0540c400540064118003458001808001207884c00780103008410801036042d00c0c1c0e540b402c1030610030032540d180f0020080503e840100305950340c00490104d40c0f03640001064003260364038a0400d1400c1404084007030020b0010880310031181d0405410015100b0980a5404905441e0307170019500c2d84a100d400c3c1903a0108204200c114040c4008004980e000d00c0c0203d9061502e80a26117154440d802c00000200c9981c00c0003035a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 172638264 1250 172637014 172637039
    0x5060a2a02030c0a0602031e07120c0209061503130c0503030d020a1710050609040905010e0f070803070b040809131404030318050601230d050c010806100f0e0409060510 74
    0x100707400c5404c0d403405400c000c002592030084041d0060b0325040f0b006043d6080900b071040c0d4410a506c2110400072016049005294072402030b0200d000b505550301003642c520703069a600603400140203e039400c41d41c501c1d00740d04602d09142c0c0c0036039461004c0300d40490303180c5042c00141800003030704c003002d81d841d0304015008040b8030210802405490641040c461001090f0010f8800c036802203031529222040c07c40002d008041340c0e01c004001e5840c04207014600c03103021a0b114262461701c803e0300c1c601542e8000d016102c1c440c3c020300070100b19800b00080c0c0003c50b4030380901040e1a019203015100d810440b800c001300c80a02c03a00b2000300c8459002c0004050b8503001b080b41100d040c0703420001484007035548035580d00e81030080d40c44040c034120070070000080c116022420b100c03000700825001c082030700303103651160300c1c4540c810f00140d0b4180c0060b52904100c80858440009039440a0030a12201811075101402c4024030341c1c01900e0310401004100b26005d1280030340c42030b02e605900c00d03143c9104080e81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 172639514 1250 172638264 172638283
    0xa1406062b090f0c0509090f0a0201030f020903150f07020d0813110306010308030a0f1a0f1c0b040501050f09070905061f020c240913060b12150a0f05060a2a0203 71
    0xf50b08c940140c0c0420f4a01040501c0075179130a0030041001d0200c0c0000e0310280c055100d1058040c841c0e0701d0414014916515845d008041c4240c14039196101d01000300e171120b181d0785c80d00000c19002e202040c0d040178905a640385c018000c160354001090fa1000090929000f039000761030880020060011882c194441d20201e003000300010004403940e0134003d42c503a1601828140b0505440d94814456110301035208052407144484142c0e41c007040c54044c90280c8161400c0e01c41358070700400145c11a0811900310300038030002d40101059880c040310440540002803080d80c0020881140440d0723400d440300c1009080035580c02401140c03000f10305200c400384118401100c110300c071600c81c0599110500c11a00140c2d010b48103400f000c0030007010b030806402c60303a00505112500040b551418102218614000c05002800e074403040d020000704904106079018a1104ca14400c40800152030150020515448941041070000dc1088606d801030340b8280500800190121081c50861500388012680c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 172640764 1250 172639514 172639531
    0x6020105060d03030f0e030409020703111912090302060a050a0f0806060a0e010c050f03040f140603071b0605090d11032701090e0a1406062b090f0c0509 67
    0x1031850400300044041003480d1015041c181c0e02d4131001c070ba81c10290010507100d10300f8002c40703030346035600c5210100a602c010000d50029401644410f103003880072800c40011a2612028013150540da260203a22100e04007108050044160b0b0000060310f03894058650003190b515038230780b2072181610140c0340d50042d1941c84100104030040280540d039401c2564130f4009245000c0400a0980300140c41d000d0b04150041d0243c4612460740c002807600000a000380ca180a1b0b0400c0c2581d9100819003d800a103c000340e4000701c00d1000400a0f842600c0d0000e10480250102c04102d506444030703012118140e41c144516007009044105980e00820450650b040b510011407510001081e0300c80305076082e55040b083d8030004c1d014040540c0c806d142c0c100180c1888615240c1d641000300e111360040034040301d825171044003280041e4036850102c09403403202020901c2c0943c3c00403480b0181c409039100400500099640b0182000481c0c4e401c1802d1144a03c00c9020303c50850138101000150080100000b5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 172642014 1250 172640764 172640771
    0x1030618050d030b040608030706020318060403050a080a060509090606030601140f040c0e06040e090709060b03060906040f0e0a0b0a02032203121812081e15030118050106060201 78
    0x100150700041c020804035094a800200101042c00103005000c84c0c1c2e0069003180b0001c260f16040c04250b900850040408510740e1000c1c0c81e000c1c0306580ca442c02180c001e00891014071075000302a015113100d1350b004810400c0020b41c1e030344a1000510035601514949602c3e0f10003020040d09007000c0214030301610321002e010400021001c0000c505490745421a030050340c9404030f1542140c080e4118110850004006a851310384440c441c00f81000225540410340c8103d000c000303074011091041d842522074409846155644130340030b000c182071020b000705030000d40d00d01548100c1c00881c4146480d944550700a00080801400d01d2800103401501c400041c2c0c1c810001d202c02c3c60700160000031200c8031170400c2c0d46104503904054038a1801101074200841c2020010803d0b44107221100009034414191100b0720120b160003106c54a8084542d9100b001d06240414400e41c00041c8603684234060640fa040c403148440082400d50b004052641e003284a000c06803c10401d0038041d01c00580202d01c002c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 172643264 1250 172642014 172642061
    0x516050d0e06030613020904060308030c0d06050a05010c060507140c0703030212030610080403030e0d09081015090b060408030406050a08011212050f16150c0509131e0f0203010306 79
    0x90300700e8170040d0680301650380001c06400365211034001c0c000070b641094840351607180903102c08080354081c0c650400d07124071780341c8086070740e142481d90171044c0d0700113945182d00c00030b40380d40303840052001411040030300010705079041d039512400c4018040c1d1000c0301b028003c2c0c141f851902a217088035007480e105002209108000180c1c480c08501800f01000b481d00302010386960400380c00a116035020241e29000e2400f55041064100c1e854104030b03600c050885001c200409200740c111800f40741d0401c46507030300080400114800e078004103610312004110340e1410765a400c00600e0f6034895402540450008a42c00f846a500302c114103004001c99020900740f00e00640d504064550b4207003012040c8000420054141c0c0001c10031f88050a0303c1d103101c03410b0700b400c505100005c01d0180e01d91941c5541011240341d94a40b20b0010f81d0f401050280544581600c074640304000740890010030603070b40d2082c10046807004148e01400082007002200140d0f41c1d4110304280080e2a5a200da010034408a261403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 172644514 1250 172643264 172643269
    0x60e010311090d0c0b0301030c0f060e0f0108091f1506020d020c01120207120c0b090706080115050f0a030f0605010e0d02040b03070b1b100606020a080a0516050d0e060306 75
    0xb1540c100d0b00455a45040402c1850111010280d6410040f085800400080200501c0201c440180c50b1004044a08150707100002c079209074001542c80c0c0c0082591080b41c01550081140c0c0da0000c0924094501680c0c41143d03400744101c41030341d0340d1035107501c2d0b003402d41d030021070014900b01500f41072003d025103001148000e552001c442400710304009420124000f140401d5040c1c40189900100000e03150002c020014801400540181c07909901c0b8070209400c2000014800c0c100c404540750000160710703100400c1000344055a6107010300604015a60000348140000c1c45000401d0310001100100882150121811a003201c2d05216040c01920b920350340b20484001865412039005c91300c02e54200205c0c0c2040515030241d0043c09001c62041d01118400803410203440c00d14003141e09a01c61a8079a405407141881200c01681200c1e52010108404100920013043c4d941052854140724020100030840b41070300a54160700a8000110040d500c250240502241181c0150850906100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 172645764 1250 172644514 172644517
    0xe0f060c0d02070602070b070201050705180f060c031b07080106030b0a0902010c060507020a0614040b040b0403020c09010b032a030c0c010f020301140a0f062c03070f060e010311 78
    0x36903000804049101108042180c0403150003d40c00341045d51918210300d00040c50709030a49080016508100026581605c01c03000d4078646101004c20040710b92941301805016012a418103410450030001c829070001c04000618160141843d103060700c201080d4014145401f503007081e485070b4102981007001c200e004001e15082032032148001001c0040d80300503a130207600081c00501c8079050204010a06801240010903a401038400380308440d80c0750441c01c140c51040354000c1c20f2000e01408100440c00340e552040e481407290049903641c214a40c0050420301d826400305211420000c01c01800e41c142c00300e0000504007100200303416a404881c001c513030f404014100c020400340807900b10600700c02508154048040c5810856595842c0c002c02d095011076070340c806000f07040402002600380c1c01c80c5003120446100b40d56103c1d150300d1028a0758039100c3c40004400c0c5804d01200806020b50303042c880c0b00c0050084621843d9042c0c40c0c503078041d081444100030740741070611b00900c0b920420050700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 172647014 1250 172645764 172645771
    0x20a02100c020c12060115140a030506060c0312390309120d02041502070e01050405060414070c030315050112090305250302010f05010b071101051b03030a0e0f06 71
    0x10380c0400c9201c00342800300d01c3c15107488500c2c0d51110000c20602110300c80407508505840410400e010503007129070069038810743e21400040b048000300b02c0c05ca943c034400d502c142e42040d0300414107481c0241510b825451900809526220700b102d010602901c2504c00c2c07400303003240c5510503a50000d014410044010942c1420f0700d410742c4600000000c94a031018806400030342901c1c1d030000d48419820156200940140c0504904442520403003c0b069000268481c100d408030099170740e03203a00388004d000103060b0141445401c1503d80c40354400105c00807910078401e460340d039075094511440f41401000e90b0000b80c0781d074103980c0c091a0144210713680b004809a480c8100c40010a07422803502d01250741c2e1095502d03040001701c601c180c4448806801d5a050340d403078001d03402808003888214071071007104c000b8443c03540c0542d000c0000c000010109203210099031014148035052031801e50f10803044100130301883c40c1030340000081007900403180c807070310820140f183d000300180410025055503030705018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 172648264 1250 172647014 172647043
    0x1003020609040f2405030c01020105010e1f030204021207120203070e1c05010e10050906241504060306180603080a0c11031203010608070e0618010c020406080a021201020a02 76
    0x8407102d03031490303980390089516000600c0c1c0707400a07454041138540400c0c0e5240905031081c01840e0780071185600c14080c043c1070382c11015020400d87c40d0030882d90b128010b02481c101ca00ba002490020250b034661004c0c212800d8400c0441440f80791800008005032428000c01a40601c144140311310b40364408000500384409560341c0c10000038284214802c0303030b00b1080040580d0b00f0309000030900d40300494400100340248209000d9070b1035004809445200440d120310025480c1203018126445940b07000102820140000140c45a070598428040d405138002001003a00e0b5071040041c07091442680c0c900e40c038011070400c002821a965441c40b4851000d01c0350400c1045500301c1c040c0b10300e0020072048040c0c024100c80007441080e00d88200c9400910401380480e03007220000c2c0c1614041c416101e80e5031002040d680c5888551100d1340c103001c4425440c0c9041000e2004000f00581302e921070880542945002403201d00c0541c810041d5100c00280c0c42085030f401406003c0bd40d40d000108200d804006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 172649514 1250 172648264 172648271
    0x50601110714040c0528020d030b03061b12240102030414010e03070905040506100501020a020108180106080703060603060b010504240507020402120f01062609071802030906100302060904 82
    0x13042154240620840d9200700e11100342c19020362500424030f04041c40300c50f002c0d140720f81381c9201c0a80031a83c8511880742c05070400e0001800140c9980f4107120700c04141140c030b07400c151030680b00c800000012990708208200480c4048c9110f003034080c03000070080013480254900341c2010582d441d1804056034103410700c00c414902070318a580c203100309006080d000d0b804102d01c0c942800c0080da922010fa59072801c038114041d000c540d40d440490b4224080b901a11007055a07140c1c00c0f5107140404034080b8954055684080104541e40240b007a14015402558007003401821030600400b100c4401032428103000041004010091619400d00d00460b2905041c20707403030301c41d0101a140ca210700c000c02944988001140011001520110341c0a144105101c88180e03807100c406031a61001d02400894699a03c0030182d1140c04d107403143d60f48040c01e601901c4031141d8a81d201d0a005852103d03c0e0a16038004c010044281c208019955002050030010b9980f5450354020603018450004a10b00075620f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 172650764 1250 172649514 172649531
    0xc03090d0f080c070e0c0901020318190e061e030714011403040f12050c030d05090c09070f0e0604030c05120c12030a02010b040203220f0203070905060111071404 71
    0x710340c500c01d0229040a1040d5483c403107015010b40714103090050004800645001c2007402e14564107030341032242d042e0025468011180c900c0c2194031991064240d10a842c0c40240c0491541207505a0045c65104081811420107004010100050000c03410300b8002d030f44803001070341d1f8000401c201140c0205601c04051001100100c0d40c0a03c0d90891900021002080c0401c001e500c201c805d004c00d00462071020282c403d1030044a440c49103840c1d5180030380c8140700008254850342c0c049500310f1303d220101d03817080841740d000c40d0401404403925008581c81100c2107220307503005003800c2891402200e96034901801c55441110848460040b030340100c81c100c9416005020410001d500403000801c0321005519032503009039203074882c1080c04015420180c50182605181c0260390294440126410682081d0200858201e4080d502540d00300600b02200f0050384003030105c1c9002d019242d0021500c0c3c0b822100241008113440c0c5a80300540c007a2000b080701500f209080e0b101130f0011940400c8110 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 172652014 1250 172650764 172650773
    0x8150108070c051002040b0903010e120418060806010605130806090706110115150311040e15060417010218010c0302101a03031207020717060105041e0f050601080109020c03090d 78
    0x9801c08480f15240344001804107c800c1e461025000c40c8508034024048050002031142c3c0342c138030a40015043d46010700c0107000f106c0d880f03150117111703040c4a0342c001001e603600c9417240c0c6001e00a83c00080415400a001d42c0095044401c500103050340348024107413420070000c4166540c10310b1184108004100a00160080f802c1d08005036184204101c50501da442d103407542049070b8034118400c003291500041655211aa1007640d00b150001144042d141e40d4040610039242c90f45072000b03901c076404102c045034500322200d106599400380740005072610700c19400302d907100c3c540101c010b0501c00060718800c00690700041404008010f91b030b002c01d160170704c0e41e162118070054051155060201080f44202030101100c0c00740b0443c1154211420315941c0c410605820144e052900f0f9280c10410040c4000e082c160010800710000c517181010080700c1014040c00c8400d01000c01d0503003030311002800740c2580e100d040c1601418008508501d881ca1010b40151340b07110b4954074a000c0d5512554460520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 172653264 1250 172652014 172652023
    0x1305040f0905010c0e04050a1e02070203070317030f130206090112150602010e01110703020d0f0c2907140703140c030c100609090803060405040c17010b0108150108070c05 75
    0x1c1e41d02c400280504850b00718041c00b01408026030900403803a01c2c000803401c80850060450180121200e0b204156071200070a01a506c654410b03178252150302c100200080d40140b0781340d0642d000f6212141c41c1d040c03c07006600c981d01c0240c0703168040c803101802c1601503034501c800c8408003102420b086441440c040e2400300500f8140c41c1c6225415210307140058aa03806401c1104040100b000070080044440091845400350341800380059000b822281042401940310385524556401c140d035402c11607a03036682c0f80000c42004607010a030070040005950b0b130044034180e086061424554a40f44000f5a00360950041c008040d042007014140d1001510780d2400300c078420a405020f5a035074542c00d0b030a642d603071004207011251b218a489070000e1004214494440074550210a09145840d84010000606170151040d41c0c0c0103c1a540000d07070040021040584400980002c540d014800d00003408461005080600e5101d101d01c0d2482c03e40c0e40403000d03550000180c10051041c001c142000c40c5007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 172654514 1250 172653264 172653281
    0x9050117180f0c180f01030807050c030102030c0702040f1e0b01050c0f01090212030f030a020901120606120c0c0203030d02071407030606050a06051e0a050c0102120403030e031305040f 81
    0x114000c451155a8221021901c0302440005840580004c40e0f01da00c1d182401c2002c440a2004040d030000600c0081c641400800c015401601122040b02803000040e08a0b8001d580001684500203640c0c41141814043c5411858035000c003048a4075041840b4508540c42c80c031030890059407044d00d0b61690307008006640d60a001c0d4402c44d2400d1030f000002500810344a20f0030380c40313141501d130f20410f40c104c000203d03000d4880b070700445801c42c0c59a01d005000f9410582400341806210329180140d040c45202d0301008180725036900200300e21400311042180d240042103003c100f0b8104825016840000c00ca810310000039500580e501200e003052280021520265855402a10000000c2c00481d400240136290102c03041c45904c1e540d10019079151095134219800c115000456281d0b9aa4a8001e441440324600708a1320704650b8400b142d08903031007c1481903d44982c0801d0000f410b5040c807402c4cc8000c41d4100862400103119a01040e5803c0c40c480c1034469174494130062406134464001d080c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 172655764 1250 172654514 172654561
    0x1806050918010f0e13170a03181212020a0212030c0f030901051005010c02030d030c0e0a0303020f070f0e0a0506010c02090a050a050f0709050d0606031202030703020c0109050117 78
    0x1060350b1034004086030003e85200f02c800d2100094086001600f09000076009203621084440040c2c04a80400d8415046441c0d030409150b035500e445001d5400880928806c45e10841d82441041d00c400005001221703000c00007483d552050001861103500007030050b00720008a124940c9a6803140c2c1c54410500c582c0c100040b0703581001c000c0c8240600f054200300c0c001d0154280c00c10a003510350004488814140310003950541c050900565454000d501c808205000c626001000c00010000300c0d00c040c0050340120016440001c22500c01c0d04140301035070242004208000c882d0b441d11000c1c1d0040b00014120f0503a60f503441020031005d038090030010380c459502800c0e03200c40e481e0018401c0c00810007100c254002d2814100050764680108604510440c0702c1d407039401e110350420b17003440070009138404200c40c032076030300c600100c0403070344042c22096402301a50045664801903d00242080304151100d8140003006a05100e2070780c00c4031440f0404644040b80322002d690f901c81d044182003c2018215 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 172657014 1250 172655764 172655809
    0x13020d18051614010c0b1005060f0901081008030a0f05090a0609061d21121602150708030f1f0902031f03110613030c080304030209010618060509 64
    0x18204000419004003054000c1da00040702c0340d40755039280c51004048000c50000d42121485030004a92000107a001000c0142c0c100a80f1340340c00100300998840b0602414080000c640c900f100d41c0d0141c04140d018070716102c13000205203011041c07940c81c02506508424020420204c0042920034820380e40d142400420201103140e03185000380c5456124000c110000345807103008003003411300043d011821000942541004400950390b102008284040c0d07018a00502034490f82007107040c005490040c1c136035981151401e07014410030424884911f040d0080745800c0c0030f5500800c0016043d01c1d84007c05100b840034554480ca0b55500409412204040301c803030190b0040ba002183ea130280d40700d03200e00d9950841e03080110194103410304e002d20004041804440d031a0000d801e0000190800c0d00d2041801440c50384c80b40d844801034001600008607070b500100c1c0070000d44c645040c0305c4e801050300d410010b140b464030310085c0c10b001030030f8040d4074103010f40050038070125196680c0c841010141d01020b0b4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 172658264 1250 172657014 172657061
    0x2191115010617070203070507060f02030f07060c02070e0f1621060801050a0b030303130f02100e03120a0206040b0619090605030c0301020421021c140607080613020d 73
    0x10300151064900141c07000009000a00c1c4c00d03000000703c0709919000001000b259240000480e1203814071560f41003140400d220707034078501007000b0180150900c42d4201144541113101e00a00c1c10344194420080f401c000ca040c040e0100544207400e0b00610034465804036410380d101e06466907005042e8090000100c01d88040728007603540d0001c2d0a5412260090045440b0a0100b00c291884000b900754540c100300041760004202c003005544180c420a19810f5456683c0c001484046030302ca414808a0311a42e080801403800b4000c03404907080c0903804034104650040000c0d5203460051000300078880310700205510350b807550324241280003054201d4040ca5111610100904407501c1074a009101c3d25040070b0b1981f8040c020755007500e008910304e00b078100301450300d0850300010f200180d03000180c0e410b0074150310041c0150704400e2401268070840740c10702001d03490710b414401070902c0104907442d02400801e96940c3c007140c0010394a0580942c4032801c5840110003002d2510300444091101e1004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 172659514 1250 172658264 172658267
    0x403120e011d010504020312041d15030f030406030632030f06090c0f030304270608010c05031e0103170705070f030c0e07050a020a24110d0c0201021911150106 70
    0xb5100717610075020740e002039104034424500c502a6004c2c040100c2c501040a035082c101d460303001c0740e000810b0a00303040c2d0310740100d020a0038248003c1c2080c146800000782480f8082d05030144a0080200e00600c0360381c00034000c806212500000111694406d0f0340c111142e80f543d00b0000c409002c1c40c008140c40907400e054110507654035050264034006d00714503481155a1901209036400c03036404040506205011502c3c980c1b00e00d161214484155640b07a001140410092282000070801600d42607580e0038000f031040b011401e410180f540041c4844014400159260030542c1c03540380c01010691211483e10f002420300300b02d60032007030034040c1022000080c440761600c82ba0490301c809542a00d1a00c0b020710032505845101095405a0300101128000400703810b0b000f03402a00b000e070101034101416104030b0541b040010700034400400400d958003088894403c81520885900085280111050403191009110100013040c00b0420016200040c81408031010a40303021b10503000710344e1034990 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 172660764 1250 172659514 172659521
    0x14030d0e030a09120b04060b0102030d06080d092403051b0c0c121b060901091701090203160e0402091308040605181002210d0f1406090403120e011d01 66
    0x30010018a18550002e001004c0740c08403248260000e0450b102656261200005444480542c6045100c104142c031a84025441860042e204020180c030f030b181500c7c14003c1070800e05030407070b418520131002075016411002844076025422402d001c6403543e030703040f0b02c0341c428989849030700845100010074aa0400021524010303000c0102e401ca005003101060b016aa2071921002000c3c0d00740003a5401041d01c1c2400c05085a001e05240c00c3c0d0840d82c540f0b2350503441d0840418520a03682d1220f52840c1140303014444091403042060700c400c195071512104021006000e40083d006084450114090701480750f1014030f0b141d0442c10190f650380da1008010300c198450604035207506a2040e81003c0d41c6048204454911001d5004044064840301045402641d0311041c880440081080e043c040302e40c1c0c01040d09a4112680015140c400c4409020f80120010b10b20b80c030030040c070000c0200107500130701901040e402c1041e00040c1c4494072164603004009000f0300c0030a045e00c01415800e80b510540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 172661870 1106 172660764 172660777
    0x1011030412150501090207151e021908060603190914150109050a0504080405040c020709060b070303050903040503070b0f040807090902130507050a0e030c060a200a0f14030d0e03 78
    0x85c01d0030304a900c20304420114bc41320300f4162000507040b03016658005000e40318689103107840c0e00e6510344000001d04185d421a92480744070207200080380c0b0521686180011101103040d00d20502610203024424100c0300380c203240000781550f6841c0566400340b6400032400b818070703081004100182c220200c81d42d04500c5250400142403071180a540b005000d2001c55a03941c03601030030010f00380ea40050101c1469441004108401d0b100020303031400b2140c40c0070b09140c6840303d440c40226144550750145120348109440490400701541c820301c00310344202d400e140d6060b186801c100030b542045030440c1c0803c4061019002d120b014200d4411079040c001d0035620180124400140d190b0440c2e001c07000050319005010b0031701550709200c001c08a84020082120000070390300c01d516000625401062420600c50751030540c481003041e02c1f4280700d90803060100c0d4034910201d030741c2c030f0700000e = true := by decide +kernel

theorem cover : BRFrame.Cov 172482014 172661870 := by
  have h0 := BRFrame.cov_init 172482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 172482014 ≤ n) (h2 : n < 172661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
