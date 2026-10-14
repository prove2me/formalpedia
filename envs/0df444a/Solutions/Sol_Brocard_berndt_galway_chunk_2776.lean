-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2776
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:42:46.697987+00:00
-- url     : https://prove2.me/submissions/fac57af0-ed67-4df7-96d3-cad00751e1a3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 499100719 ≤ n < 499280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 499101969 1250 499100719 499100731
    0x50426071a070308090115060c0606060504120b04082a0f070311040c02010f05100e0c09010f0c03030902030d0c03080f1006111006090b130b0f0d060b0909010203 71
    0x118455511080300110565034044500c80300c020501c070180001c1c4c00741404d158041e440c4400041c201c6a50660406074080c00da00c1a408541079001c400140412409684050a0282019440c25241c84896020301c50010806810440c04c42c0c0030a003005101c0d4100d50740e00c100307103c1c110768100318030807441400040c0503140c9030648511600101c46442c0130450108494014420303040103103202c4d00b400050540b0801d40e0045543c2c03010006a02005840741500580400004031480c03412b00302c156010003c09400d0381c000700c0c401d002541071a030b8014a4119402403510301024403192501e4254003078050039000a5160186012116040f64000c0d2400c15083c082d554281d40c54a41160354070f03400302c043eaa01003000085181c2071100b9070207880072022400501c01207400c4401c0c4400444100c8800d50401c034451078440030318080500d040618080360900c0d03410704101e800720240025540606040d4200c0c010080790f2074800901c000b95100d0181c07000040d1101a8514000410500070b600443d40c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 499103219 1250 499101969 499101973
    0x902180709080109020108060d050a0209150f010212030a0c050c01090b16111b12070b0c12040e07080411030a12030c0e060708250c06090b030c07060903050426 70
    0x6004035050250130300702601170319880b05640b00c64090003c0f04070309034800d460502c941010100180c484020b101d200d07950300502160b121144504002051301c41002542c119404042400e412840740d600300c0c0e40244019100007501c4020700320540b0140a0780c101024254032b40200c41c41030001c866611485507116450f20110390007441c4003980c6564000484841c40e42c410742c00c007040c05007141440702071520000d02d540e55803031051800529024664000d2035642e080881c1203030303a1940400c0310340021030708642d0082c10a070418041d4400c0f6000103018030200030003c400b040c1070044520300d28400d45005020b544c001c40c3d0a090444074150180c81200010b468030301205000d40c828890481d0050004060502c0c1200c07035204c0d9007103500b103101080c45001540c00748002c860004011226510304c510150380b043c0d482d082c80030740545000d0b0f010720601c080c20010416441c942c04200d820040c0d00450004602da03c60034122518000e40d040703014403000f4108600394807000703402e03140911711488003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 499104469 1250 499103219 499103237
    0x30201030f0203010b090405151018360207060f090c08010b01120e190c0306060b0a080a0e0c060a21180305030a2712020703050c060a0309021807 64
    0x41c0384101d01c0244143c641c428824050f8511518050b004650480301d654080103032581190700284c0e119801003200b102003000c1c52101e0100111104505c0001c041c11154506403048c2c503d01c108003200c4201180500b105403444000483e10241e064806a98100508106507452408402c0c0140a0110b081d607010b02159400036050074140a00020114180d55000d41c021400401c0806410501541c4e040ca0042e6002904141c21102503100000d00881c1507040c043d02e981050f20440d401604901b130400004c20080300030b01c0e00300740f504d07400c100100030001e41c0c084143d1a075410f090354000441d60003640006c3c940384290384071544044000000d12058022a0b13400d880c8404c4429091503d1000b15a4907082004a13001d14051a404810448042003c040138160001c0c9002e4000c800ea2a000100001d1418008410990300e40c40c540c500040000703e01350340b103066a800c2c3c040c12103071056800150300c08045210b03810103010705034007601000d510741140102e101c61170800c840400000310009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 499105719 1250 499104469 499104491
    0x4060204080f0d0f050901050708070b16110a1211151e061302090619120e0a0203120a0212030a0b12060c0702041802060a0903020103200d02032502030403020103 71
    0x1003000700242d007090f00c848032546411300c41600e60b50070005503141800303001e12030b00c401704029200428038240b061000640a00c0c041d0307511601c00350170600d500300700101c12001c01c0700004002406192240c010a90b500303001441c1c0c408482080110007403410a00440c1090400303030350150f0025015800f54100101850780002400789440c40032600168482a080402c01c0d000815500600000d0806840103141196070361030302c07219001110801c030001b14800300c0c03c18109040d02c50070048043e1600644103410840c0c002070b6507004141e600a010b070900188410ac058003c005212080091088583d1685802010500104021403126020302851040001c0441e00441ca05109161800b0712608080d8035409010091000c4160060890300610b46040503a4800b03006d0140e4401c241d568806290440c400117058602c1e0520500c01c80d001c6503070400340d0681c640107440683d02c10000043e1242c0e6141003000520080b480010000c00c0c4001f4843d01043e4040000d2054034000c0e00c051229003806 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 499106969 1250 499105719 499105723
    0x6121c0219111009030203120304021801061205090c22050a05060913061e05190509100905010b06040e070f0804021e010c02040509011415031519020304060204080f 72
    0x1101c0c0003003800399240d401100902c0d0402c552018051070380b4040318035944070740c0424a0084001d450f43c3c04030a0103c10032045181a424162002800b20711039086545040c8000e001030303c18481c01703105aa10b43c1c00044211008200a00261900820500c4220101311000625014100c82a2142400c2000061405003940a901c0c05480c000d0b040c002c20350341e50240200a03117250b01c01103c6403034542c10948003003000c40e142403403d1040780e500002c1c42c1c00c19504405c2420b00000e84955040d0030310080080000e8040340a4180c03940c42100032170843d86514200e030041240703100f126130245001c280403a58444e01c0541620440143c0c07124426290f00d44016580c101d000c8030001e41c42580b015040c1c03028416840c03c00101401818420380550a90707002800f501d100716096682c81e136441c0061210000140c40480d0498100c840c03d650b01d50200d0003203910340380c10000141c070f9851200085055805100300000d03480213441c200715242c3c1401c3c548607010798414440c05109102d90007403000322040c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 499108219 1250 499106969 499107013
    0x30f0a1b03200a08060105030403051306110f011104120c1805180714061b060406021c0938090a061b08010e0709030c0305030904051803030c0306121c02 67
    0x81d8139071400079510500115811f5000a20407400c014090024400c0c00300d0071181c0700003410041e00c80f0756154201000591800a180d5104030b0180c2c10041c07050400203c50040700d040d10890141c50002810905164000500070761210001c218800c419400584a5500c158000c8113542e1070381400c1452224142c2d07580485002c1e000340d943ca401c20704203903403406c480242000c0810b9014200c0404018a10a040c0401100c064800980001d03041c0d02c003c00d8554508403641080204010b410a0347c0c0f6848821100e8030040125242071401108900302618042170000b11b0350783e100504c0d460624011034492000c09002c5030080c0c141a5601082c041504d08040e1803480c540e04d100b510381c60181c0354486048040d00d400d007400320900d40400800d03400c03901040a1802040110384d40c044450a10003110300044c82c7c00003502c0c082940b204081804002c0f03036042110800344a44076221400007aa030044120004e207554401d812444c009a283c0843c107003101285502641c41034803084540c010803143d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 499109469 1250 499108219 499108237
    0xf0b0d050d0807030605030604051f020406080a0e0106052d150711040b1908070906081f06090504050114010b19140c0a080408010e0102070305030f0a1b0320 69
    0x40510703400d40e294460b2190729801910392401146455842d40800c1c117107401510305072000e4200800880e1650020344c01100f590103045030441c0351500d0b01d10020035024010701900b1056441d6142110000c400b5082107000e85001403201c0d00408007824030041c031440b803940c8807900801d030f02d150320014581144103802081d911120b1904d07155190703884040401c0c0d43c50140740d0103682c829a101c400d850f103140d82000c050b08032032444101c41c180b0300c0440c52302d241070340419201030500b0130034450300d40c0c0803402c581070720000700d0140407040c11a41e8036070107000c00e500010b0106140008000504c141504521022076844071030200c540d8a40c14a0102441401310403040750110f403814804503486550415a211110312030760b0300f09010640b105040100c0c1c2c00c01a03803858400f1a003888841310078811040144a04402189410651344d006052400001c20015210200750000b40401c1c000e600461045090341c8039085c68051202d501400802000c82c44540943e552501081206404e02c201c8186403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 499110719 1250 499109469 499109473
    0xf03030804030c0f0503190306080609031603030b0910061d06091002070e0408070b1015050a0309171306031e0b180703091a041101181205010f0b0d05 66
    0x41d9841e2002e0b6440410803500701e4412075000201340114000f84050001d1400020160400c40840c00340142070300c02c280c201c00c119401030401e02a048000000322040518410180062000d45040c158000c1c00c080e60700e182c00030000030070000c1040f4810b81c01800d541c980c1e140d0803a0f40000d0f4408480500c010f0890680018003000740b95120300d003800c440c0d0b00418061040700c09181d00d580c0c5803005001c2c10340b002c548000b804104c0f4003c00c02000c40c025448201480c00700305c4646080700002548080b00c94940c107101c2c00051402c5150b06c41e801c91207909401403801c032019800b10003040969406036000c40c030002980f0034045030552180c0600078280384a221409608030384800410003c1114040582d48818844400c0300b41003101191184034403156180004e00c801d00c0d0901504c551030145103610751041d00e01c01c020005480c03920802501001780b0f0001040e45140e038600703001c0f581030b0b00440c44110b0b5600000c0304002c4150064400c0903d141414810f4000b500d081c0702458452b40401000c903 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 499111969 1250 499110719 499110721
    0x403080109021e0c0a0507030c08071a0d0c1e090305010f0b0f191a0705101b212a02010b01020d0c02010302040504050106020c100801050d140304031208100f030308 72
    0xd583d81800b42c010031100d5803d0320051295965854503001055104641c02c00110304100310f00ca00c02d215003001801d0200150240501c20b510a217002d11502c40c1c1e01c01401d540e40c444810325482041d4440c4d1442100d800d00501080e1010b010341417900f1844112040c0d820000c24185040c040c0c024102003d2000d01103402d45048201040074a82c0e03141d0504982102d410800a41c400d60003030340004080300241c07040d5440c05a41030260a0000c03010400040505042d40101900a17540c2c00b100e03018028079025400c0406036000802d042c071420341c451000d0741071035240540d40400c5e103c1d126401030044a81d502080500f2026826031350200441c1e400f68121354031120b42136001d943c54585207841494010300c1c1c03c1e2030310001800c03102c0030303081440164003803022607203a41801000400040380c141000c0485616100c0081c515010192004050840c0304d00c1003024208104191000366900a0440220b103101d02c2e0b004240c01801c85d00220016130304200012f45466021194095a405a44280e41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 499113219 1250 499111969 499112017
    0x1a10021515240d090804080c0108040c050405090f0f070f080601150807030608030706140a05040210050c12070b0702070f0317032a030a0e0c0a091d010c08040308010902 74
    0xc060655000031642c4100708071400010300744550110745104549144e03c5d103090400c5145040900400141448455401d00c000304d180300b4100001c0b100110747c0403846580e0341c04503908024011504c00741728441d0a07683e046007403000c94940161444402019155595000d4160b5102e07401e00c1307581c0b800a800e5000e000d819100da07402c00e9110000d41404180a940d03814800e24561140c4003d4424541d1924a89030010495500d290400010070003802241020780009250700804c8912109100000800406403001400421f1a43c800c140103503403502507a05001c090050221102c80c0140200030002c1240304201c0109015030743c02124458515005a4041c8844d07072014110103281c81070542c05840c14004481035034410070340032a0f004d03100d0030200000300648a20b21040040b54103c11540700701c86e1503c8050000b280c0d02000003185000030b01202c003040742030315549038250354240020440159002900b80703014520954035000140e03a2000984100c0c01010741d070000c100300360751403900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 499114469 1250 499113219 499113259
    0x1e200f01050315040c0c08210c0a0f0f0c15050414030c03120601050c03030a0f0608070b030c0a1808070e0c0a021c050c0f011b030c0207091a10021515 66
    0x180801740c1c0c1030416960070a5100d00d0155009500d54229098800300c0c0580400d03013140165410140c114007841c00c1185001c0041d0039481c04d00380303040070084e0318984030008a106651444040ba00700051805401040001c000601070440303090703541d01e94100c18188502d800004485c20310390b60101440c1130070340203100c028069801602c1c450405c04148040c0c000c0c01c00074402140180841d000c0001d40401d44500b120980d03c0c198400e81ca43e0300110342c02c11400c03004034116984944c20841190391860f02c0381c411348020030700c0003007201d014504030004a00380c80d001407500140c0e18100001442d0b503031402c003954040d109940700100103821485a0007481c142c0b108071400c805e02c4a0400c00e0404001c520301c0c03440c0c40c403c500300d800540c1d128440d42e60b106610381c4071003000558524040c03103444140c0710003965800340b81c840c3c60101c65443d04a41140148900a141203803401005602800c10052001b07550390003110304090700842900100b443c0001c0b201380200c449101600c021030804d03007080d900c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 499115719 1250 499114469 499114481
    0x3080a020c030f0c0d080615070b100803160302070b040f060e0d20120a0b010501110c040501140924040e070816080708060907031e200f0105031504 65
    0x807500c003d000d03180034035a0311406041c4a00030312000345020005120002c00031600900000e01480d0b03442c4200d964403100c60102c5a01d9130f00409240003a444280c1c51031840b1245030701070702d418040424041e00d2000828103054019010b075085660290701d880c03e00c24584110700c520001394103124030030420a1f00508030321641040061040300340340308985800d1091303603900e41500d50720440401130114500d001d842d944000c0148000411500c07403196287d00840106016850502200290035407800100304400342c036000c0083e00030f000950b5100d4081030000500340ca540c0c030800c00300c1c0002d40d0700c81100c9001c1c420510501001d08111582d8000d1100510340d4036111081070240311004038020004000d42c4c40d03408240b1a80d81c249500e0000c195003014004c4d006040b2940001d818495904800180c0c00240d035040860441060010042c10442c84100384004100c010308898080d180c44100044803a000810f55051401804401c01140d083c80200c480401d1504a50341c1120b4506080d4444 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 499116969 1250 499115719 499115737
    0x1204081e121602220f061d04230a0b0a2306130f110c0622110d12020615220905030903120702010e1f030905070b0703020106030b060306010303080a02 66
    0x20520b41522504c92800d42024030025220064a450714460340c0307110351082038003c02000e14940d00480e503090b13a1003000900500003038051100a00300b2103a850105128045184a1808130740c104011071500c075081071021a01410840c0c9480d0741c101001141c0450301d410804002c40c100349551b01c100422190b200004410905982e841e03650200141072407242115001510601540361800b80c25142c0c5481d00003080107018484400000c0c0c1450410756a046225511001a45903e1401000301e459803600750380281034000c6103c00381620ba44c003ca0054099030307110002000303080f0b550003071201880140c01100126240b2454108503001c00ea8004032180d40710b80c05692410340b5500c00245001284070302009000c070002041021582c1041c0400c14520701070b600103007074240a401c0207405a200309000c2c2c4c01e140c0c03120344540c01c04c40e05006900c00391002c500d00940300c21480c02c00038024401070004481a00243d004501e184c58001050b03412240d15583e050b03c5903898031400e4010703401108075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 499118219 1250 499116969 499116979
    0x50105012a1704050a03030206040b0705091e01180e180601080c010c1106120f0f1b0304020d1403070204060905100b0a0c060507120c0c02030c0607051204081e121602 73
    0xc0810300345d1300c1003420401107009500802c0d00781014100107451600182644043c04810019014a9190216000302c98482848880d04160307030709006030f6001c4003420410b410003c4080380443c41c81e100840e4640129800c898503100645401484c1d56a0310080c05159095405807034083c00329846158000d00292081031034200c80c49000c00818211b40020588103079406040c0c003005000d000800c200e07584222110a21441400d05080ba0112020341421140030480004001419500d030502100e94569102409072450a820409541c0b6900b04681c2248502d042170000035011000e801914000d00441c04c490b0b80007850030001d815150320a40820382480510a6410003081d02c52064078403851580c2c0762a030302070f9801e070030407021a0019103900c024800c0d26010400580c41c0010b40c2200b50400361105e613038811890038814079100340070514481c0d040b8005404204854041942d0185200b5000c2c901101130448040c03035120851114141d501c017106105c3c0007010380404844480307841c00901 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 499119469 1250 499118219 499118227
    0xa0c0909150806090102270a060c081201090203070e0a0e0f1008011107030e0402120a0203061c060b0319050c01080c090913050c3f030706050105012a17 67
    0x1802c3c203000040b0355008181c1d5021440d060001d8180941010465400310005944840d550020700c580d00c09004500c10003c9000030700f4104071b240070481c1c00304183d035900910030350380d102207e002a62040b1114400110f80d80e600c0c200a040002001d81515800421401d040d074134414070703407400c41d4001d0040c0095002c4801c0060b25241c00e22030707400c2003080b44801d56500c400c642006010360180d0400a80564410031001040740c20245485400c40c148810142c0e480d25810009000d1400300c60754501001c0b08d0f141c0d5107040001542c0420314600f030513400d40d07801c0c000b4280e041040c16010303180a8000e410203c1260b40d00c0d8480d060f29640a581d01e01c0741d9090980800110b804204212030084a015001c0015000d000c020001030f4000b003400c48808182079007180a8420030243c1200328143c1c03103603909402c0c2c0c14264030b41d080c0300140c1183c001c4980f40c000d642820300c0608002c1c400c3d0f43c041529200100c103071668000c50030180b00b8030070b000c40007550100d41e04c1100f8244107030100605c2d480188 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 499120719 1250 499119469 499119479
    0xc0c09040203190c0303200d3204170601030c380d0501090203100302041805010c0c110102010506010507031b020a080106060201050f100b0a020304120602030702060a0c090915 77
    0x140b20f00303040c0d40905081094142103142c041c1c506101c00745d50317050540d505074880042c0c0a001800a0540c14186061500d40a80844046c0125040c88081d80240014070412031aa80d08030050011600b0304480007a003146144409038032280d0038003000e006040f511a05200d1f600340c0030380c1001e4001d81c0092299842c83c00351007000b12410030105200a40f080014000c1240c602400303554090041c0c89800c601d9410040fa03540b84500355448000d015986810480c410400c08c404030f01aa140c0110080c4407103a02003500a28186501c00d0480d0300c3c502c0c00114203255441441800d10506041e1201d618140c11524282c40c034071705171801d101150250002090041c1c607424122001814110000305a0504240340682554801424454540e010104000302e000d03080308400115200d0401640da04c5c800ca55089013144520340299841260100c4003d0403c506070b8000c43c4501016407d680250f150100c204080c0e48015400381d0018002a20502c4052841d85c481d0005608440901540396a10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 499121969 1250 499120719 499120753
    0x30b13060c0c20011d0112020a020f0d0305070e01110c10030e1509150910020703021b040b01090302061c11040f0e07020607120605030a050706140c0c09040203 70
    0x400e141c00035041e00e150804014450034800340070f40c4410200329a0001c003c00007041c1817801c0c021800281120040a1010790044a102c00b0144c00b40c2410b40d40c44124540c06581c51008184181c1035105511400c403d4034864414036009074016981c500c10100b080c001117a07410b441c60290f032024003910038034210a0f50b8210900c4180a126140032901000c007c17015410b12440303c2a15484203000c50411030a9400400e0226010140195220072605c61a24540c42d100c2503c1520814620000d149410316400280191003143c5888a0002c1c9a911200780400d4641e4986c4607408110105070510041c988600070b0004030906a0700d041034004e06402d0170060b1070f807102482c40560380c00242400102c00e100140b001400c0281035500d814140404000d5440030020085410450205540c07550401160014401840020104c424400c02418103d882d083c09106100214400f6040b101c0355a400005480c9442c5404020302003c9031700405224941e903000740200c0e898002c1ca0103503a845503078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 499123219 1250 499121969 499121981
    0x91b010e130507030501090629040e010305060f011520190605041109010b030a021608070312051810090203190b040b0705030f040303150e010803120a0e07030b1306 72
    0xc03072140840c1034101000040c0c100c030b0301030b0002e584032801c01406000700c581c800b420802c840810b04074841c040040e0100d2060a00880d004280c1203100d08e00004103020700011258058074082080910036607075400180361481140c58040301249504120186042c0d10f0310040710240b200700c090310f0407500001070850441d10381c014112161139031013050009000ea0710b010103891100603680d800316541031440340701e42c60000402e1700508a400081003038440e0304140e0001411030344440340580320b680c28074026000c070408403001d003082d600d82000521131a210b1240c00c4120b00e074002c0581010800000e1102c040c01d05d0380400d0b6014031908144989000380302c1c5d00b840050303005000006142c200b40c40d0541016030040d2400302042020720a0204486012030a95081945030800051950740381680c5004103003550f01041c41032000e0800010041004001481d040c010310500300d040727980b000e4450080b076960f6007a40000b9402603506000007402d440c80207400455040320a2000d12466940d2016640c1c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 499124469 1250 499123219 499123249
    0x304060f0203010b1c0614090901022b1a0a1e0819150c050315130903080907050307030c0b090303041203020706030b0108250e060711030d0503091b010e 67
    0x500026401c6510485c418288009000002d00340446850600041c5a45141040d180e204071221004a1000b13502541190040c040441d044c1c7d450001a100031113581e000c0c0a6605006800c04c00301c52440f03482d0031780002c48807600a003000700d004e08100c0d0030102840c038150aa016581706030300101d84a00204080c45c05c00004030f00a4003910114a44031081242518000300e4203810145001c514540003030a42c0d038050704d9101815070b40942040040c41d03004e26424068074240c40d2400d501c0516502c01d9101e446610703da0102c58840d55a00e05056030303400c103840017034460980f100c81444100300c404024407a505d00102100d08280d102d000e060b044981410080700076a1203044100001501402600002c03402400c180e0b00b90316000308204051101d03401d544170a96120882d0b111214024940040142c0000c0c01058640d6442d03d00685000030709040c00313200380704001d00410540d20410440b44034600c520080c0aa403610480b1504e141d00d0000041818440c020504010a44413010300d50881c1c4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 499125719 1250 499124469 499124489
    0xa12030f2a09080316150f090609020913031d0301110408010608010506040209030c0114221d04020d0f11060a0e01031a1e0d0605090601080c06040302150304060f020301 74
    0x801c103001400c408140e51040300ca03600140302d900020821000a40291a0445034808a10082c1880d14000b01103010b102c1c0306052401c1c3c5000148003182d8801d0007030f83e10030b4076600c403182c48112240301d071840441740090018210314100580040c10300c40c8400003000190002c00c4503500c0e4001c030b000641040e081158140e5507808200b000000034092250061420b0f58114a030280c1c1c1d402003038403200c2c44041c0c141446802813201b050101020207c6607050030207443c3c5110620b00f0400440d003403044e84108035510458640c11401300c943c290680d80615401042c03080812881d64410441c1e400b01c040c10340c0c20504405040c0d24a45a202c0108000025545c402c40318452401c0058112881e55403201c001c15030766010301485840d9040168100100040b40208d51000c00b80003c00e000080d0200a013400e0501d0b040c841c0800f4002111410b032040e103000d481c03040140304148051405240303c040e510544840c171409519a00030025a0880e00901380443c3c41b610f20700d02d9000340c0c3e1080c0d10412500d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 499126969 1250 499125719 499125791
    0x112a070f060f0f031104090c11070b120906070e130b04051302030f1c0e0d020432040804120f12020d020c01030905030d020307051b0304060806030a12030f 68
    0x30b80c040d050120f02d11032401c0400108142880d40c649a020340c3c01001d000302e54414036074801c039004e84044030b000c000e075504030f49085403507030503d6483c7e4114054411180380b220700400d01d00480403440c2c1e80704400c15507031300031030f040c0300420030030a07211000c1c80d606176950303500405007681c0700e6000f19889170b0050903c3c054102600d2040c10701c2c0c0040e0005801c0141c1101c40c1108600c482c48040307070200c0e0a245009258102654006260980700d840003d511614104e1000c4404082c0b082c800e1810082c040d641d0000c10b6a840450069002154028014041040280034903800041d40303c003c94095111000c919449a40c0d00111030000c440c6880583d1140c0e8003825400d40c1085801c12802d0b00303190a01030701c42c407a6121541d0707000e0000e00000407a00407001610952142c0c050340e60405020b00010711089000345095260ba015010300b400203601d034070007d9418140040d212014030303880140300d1221018880304400410f03262583c440200c0d214800855100d000004c107508654003602c0c10081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 499128219 1250 499126969 499126997
    0x13020d0c0b190f0818070518010608010501020724090308030f0a0b100503040f170a0809060a0b011b0201030e0d030519090c150309080313020301112a070f06 69
    0x588030080c070380c2030801030341c05031a4426a50040301190400a1700064107181c41580305040c5c20203102d41c0140d504040b003c59040500500c0c0002c1904840d20b644801c8031030b9803510300498440003035010303005401440e1600011880810810038140e2201854058805a102c5d9035402581d802138074502c5140d010700c0300b400010000c40c0300381042c00d07000315192080c441c0303502005480d81c0030040c80680042510710007103060101c4c80309403903429003c0c00340203540d440ba00c0c40050000030307059400005034840c0a0005000101c5c80c4500c4011280503103c1c00c15000300d00304c458400c0240f0a0080741090f84402d10141c6150003000301c2040a80030740ca0102e000e2400310050b848413220103a50b10401d03400c1900c4040803489020601c82510040c1c02d50801840125000343c1c0501001100101094400003c01030500840500740e040c0707610841c024400d002c05844c0c180c0080c095240d05072401d034800b90300d075513a03c40070305584040d5408140c150307054150782d0f00320482c241c25103a029401141c034072400717442 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 499129469 1250 499128219 499128247
    0x51605130f0303020f0d0216050609030703140d03150e0103060b01021c171302060405090411130506190b27030604060618020c07050f030a0c03051e0304050913020d0c0b 74
    0xb50b50080340c4008c2000c441d00c1d061103004800310740704160240800095021207614180041c4000d1a0058024541c402c20b503003004c1ea13034a60800415000900c0d00d0b00790750305100c02500c1c51046070464031070461281d0071034403040700616490803241d05600c107000c100d82c40c0207000c01d000c2d0900487c907210308241184034004c2c0f40c12014014154920502d88170026030059850700180d0b0282e6009072401e5540d69294940f05856544400245610200145203003415030f065400091144e001603070010185c0580d001c50301242d44641c0a03001c80c8000600248042200c145001074880b2100603443c074004e80f102300401d040075001d68040e0340c503544410051000000d0386040e00d0891910344011442d12054080c410344894160096503c41d4901e040742c3c0c086540d007008010400c80c1c0140f403080c403143e901c0c904240d403981500050701c00e103e101036031110441c00100a4034120742015100c00702c141d40f00303070340e081441200d10401c0768004801e59254000c201441005001780840c0905241d40d0f850022043c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 499130719 1250 499129469 499129483
    0x60712021e07080c1f0804051905070501030b090402130e0a17030a0b1005040b13080f0c030c060909182401061211070212210d0f051605130f0303020f 66
    0x10b004607414803000c59100c0f0007980c100c0502d00c1d1840c6c0800f19403614603142e82880040341404003c020380654110034060003080c101c0481d4026201005040010300902040300340443d40654426101c9182101c2500c0c0e80c0c019060302980d41b4241c408007501030742e4801c08881d40b00c01c0f6490710b20003c810840301c4d0002d44038482c2c0110341210086c1d00b820402ca402000351007140201000700e500894141382000ca04200c080c042e00310f503001c1d101d0407200e48046950f0340920081141c80f9210349000d0b40d080d41455811200c0c0150b000d00341c0d200d00d42e83c0442c0000000301c0a004101d8521030107101450003525200620788589100d12201100e501d0300070020f0103c4800c458240c4003d03e4004806283c43c5100212046a941680d5860f442110358591a081c614882500307181203d0b01d803aa401e5403607940c0018015a07541c0c0008000c3c0200c62405c0c2c0003160030840c0c1703c1482007961262019901d0190f07002d8a420108002403040854550440008021203507204401690000001d5161004140061 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 499131969 1250 499130719 499130743
    0xd140c0409230f030414190902071109011a18030303010303021509010203160810050a14090c0301050d080f040305150108010c0e010e040b01020c0409030c1b05060712021e0708 77
    0x3c0200702040b4803100d849114501c2141d0071114034244441c40c0384c6850541c1d0300171014283e02c0040c070030303130341c0d10100003a522030301e02140d450706c01000c3c00d136141c40c0c40440e1506880c0502506120f0241090303420f801c552116021000c0e00000482c582c030a607500300300541c003a62095014103940c1e4484415040300d440e0103001201103074014402c000d104002d003840440b10110b646046186915011685074605105030403140c5c1160100b0070208120b80b9030f1001c482142d9040c0d501c917400f5603c60b030515031139010030301a5580c0001d03188070302004580d000001d020200c2110204600e440d9480c0c0d601440c20302d000d00b40088041078040104203110081c444c200f008104c0341000500a860140002e10700182e20003072500c00c0d82d070348201e0225644200001e031020340300a0800c00c480c04490501900c03420070784034202c0e210103071100ba003201030554144100c00c550015101c1410101d2a50310f10030010002c0c400d03d001c6100e00e16032803428090920b55903010000c0800580039040c20882140e003800da0010304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 499133219 1250 499131969 499131973
    0x71a0103030909020d02370311090108070e03060a06150c02100305040215070507060e031c08070c0b0a020c19331e06090e031207090506040603060503070f03020d140c040923 76
    0x10200601c40c089c0c11101c00001c24278080d841a41c9860b02510100700b40f1400daa0148100010040b01780c50740da101905441042c0d040b400c0c048443c0c8811548001c0800e0700940200c42100c1d040300c3c080c0281c001c190420720003098420041d80000c0020340f2034110038002d481c01c0e4484030080141507009031a4594116043d805010410b8003500090b05017211103286008010520001038240344c41444604445a8030049861082c10b0a8150038040d40050182d0001c0303000b4404a50040d02c0c00300a408892940008480084a05102c03401d142d501c000007043e10946c0c0303001d0349060403030481c03044907142d1a44942c05a0101e1082c283c15003150601d81040c098289080e940b000d054000105442074442e404140c0300381980d50910440d003120180d449650841800324003c200c554140e0024403e48005504490800340c0e21204c81071008900e10000c0e41012003421101d002c500640312608000300c0342c904580145c40b42601107011614a12400c0e00c03204440c03030708040441d894110190100c01030b800 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 499134469 1250 499133219 499133231
    0x5040501080c0108040615060c020a09050906070c0602040b0406121d030d15030501110309100b0d0f2a080708030301240e0306040305071a0103030909020d023703 71
    0x1031850b502d08480c0c2940d8140003040c0001410402c05402075400341e465055031038074065482030085c11500007520103c4c0300d0002c80b200030a401407180300d46440b0707040361002820940c40703802040c0e5223810500c1d800d0720400d4003008003080301844940280004e01e403d595016034829038100c660221196610040b040b030441889407845a0800410389a1004a001002030031030b200841002007110641c1c0000c01c15400c0c1000e003801060b198018621034402d607001d071581500d40d0000d8004461900404135406070380d03001042c010460701801080311520400c916582c00f003031420391039121100c0c8141c00300c000744d0a05c404d100b083d1091000100a10301c0c0c41c01581075504208070382201ca8002c0d40300e03451444400c80d400190a2041803546c8480c400a000d0741c0283c182400c00924503071011505031001050410400d03296100c00b07480307a0480350950350b551162410588400042d51000b04a0b1200701d400313004c02605152541c03188032213029000c09580d483e000c0d8940441a40205c0214a01810300e012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 499135719 1250 499134469 499134479
    0x3020628142d01050f0a050d03030b090901200f0d05010905060a0801091101082d0a050105120d050c2a09060105072105040b0307110615011d06091504050a05040501 72
    0x340d05907044d01c408844c550304c030080304004928025860382c00180d0108241c1c807003070700b8142c065108044002c0700307450703070300481c0d944480031400d83d0080c05034005103540041880580d072050030050711010015905140c502401e22220030107584003070b0400b210030350341c43c02440001c0c50156001402020701800034040e00302d490701c441020190100040c3d06010120001800000d41c9114004525071055603e90042c094070079416680c3c82c0c12241c0e400040d141c0340011a42d0300d489032081b081200d204c80108480c1440c02807c95468000744e4942c0740b070307108400c4520080720100c480004525106505100e44200301c00420100b8800500600d06002042001c6401304100e0800c11b00342408144503110452003607141221507110725401100d00c00c1c030110a0110b06584a004080304030080307021a1041e4031120903902c188800311001901207002c45001c400a2002a1903020040400600340c40c10a000c20002c1800c110541c4d01d094412600003405109504d40302c0c282c54042c000950301002070758144 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 499136969 1250 499135719 499135801
    0x821030105060306030c12010c0e0919092d1203050106120b06130b03040516061205090f16060206010e040c03080c0a06060b07050c0d0302062814 64
    0x600400c0c2c0500c50002c001102da8808110140582e4030252166140b0700d201c3c51114024100340b0700c0c2d8800102811600645460114001801081800803080c00d603026118144000c200e4804201d5030b00d004a2000c90402010b01d8420811030300c1801c4070041e594641c0f400241c5074140c0c4440700d09061400f4010300c07c0380d0344004444481007034214002003050b03004000039414015400598200350103140040f84402071400614000da10032002c6500c94603080c41c4507110039505000c0c030000a1442c1003000000701e4150481c0d5001240c6009a603500b4007a141c0c01801c00d9224110414070b021180301c1040015410802e290052101c1c11411089044c00c0e607031121b03c0d000c60701c0f000d0205400480c0d540407191061000b030300518ad0083c020000340c4c0c2e5800d01c030403080d0006603041e0740034002c0504605460030141d01c0c6d515196403580c0a407070560b07280a80c0021001140000b4208140c180803040c040d50600d11404e4145020a500310040d45440d1091101c102403580d040c0750103011700c000d84031104444c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 499138219 1250 499136969 499136971
    0x21c0e0a11010f022b021608030f0d020702030d05070b010e06030d0503220302010608012003010b0c031c141302010f030c030f0218040b060c1005060d06020310082103 73
    0x4240f83c48207258002c0c0904900c4c1081d5114039101d0910100b50000001c0c0700b4408400c041d00c0c1c10307000d4440c40d0009820032a509106031081a445800400a00401c4401d0500800030b4134602540181040c03082c3c1c0100e45400464800f54001c100c0c002102414404824065401802c044003442003507d050008a604c4401d1004464144400840031420058407940c00002e441d0800c10246000000ca0400034040c10442c4215100c0354038004a00400c030203c03d60300e050002d402a50a0f195918214006100341d010304c4d8424000c0c0802d01100101201100404211740c4410501040070041c104104044103406001c00800d080c00d0580c180060b6000610010798803035a060000e20201e41e41c80c103401178a001440c1c0c1e0b241c0c910021360644c0034244a5442e404400041d0f408005205240e001d00040e417040071000c0e690342c0d00149000b0407000ca5038000552144014001446142440d5a0541070b07800541c0c0902422825450a118921007001044001f103680a0740203000d040121140b05607203c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 499139469 1250 499138219 499138253
    0x90606030c0f0307030207051605150c190c050a0b031009091a15031e011b05220e0c09010e0328050705030303010b1201050105070b0a09060e01021c0e0a 67
    0x40d003c4001407410f8040c0c2d040d00c201c1074002003691480700c100001060112218040c940c4900a00c6000c00040003007401503400d12842100280001c0040c624660000034100208a402d12a00040410340e601c2d0051508000c0c003081c2081c0d900c0e0300b441c1e0300080f24000aa000307028400c1c944200c010102d600403101284000001c4441c0d802515a80200c5000d099604003c542510801d0000740140a1021f9640380380c1c589c08000704088103d4803d84441c043c121010200060418005040010104001d902d400301720440030300300c0036a58010700c0112000c102c840a160f620081070081c01544c0103030012a8209080303010b130030702c19501d454150400c0000740e9920515410b10314141304001d010030003e005004000c023100c3c4c40b5a55000780e4110355200c0002c01c0c0c4401e20303803800040c1c0c55000d00c064a2116070b104149120999504e00080e00400c1d54500580307401d078a944030454090740c284001c05e08400c1c1702079081c2c944910001c8180658118281d81081907103c01d032040302150110309140c034008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 499140719 1250 499139469 499139497
    0x80708070305250302060d0b100518090609070f050d2a031e180f050609120702030a031b02041127030604061806050112021c03270e010f05090606030c 66
    0x101f020746010005000180005070403040880c1c1d00d003100f98124024000038454582600401000d08081c031107400815505590031045490101c1c80e080d004200301e5005145501d011405c000c0401003020076102c01e184240402141e0000e01641c108203c0c521040036080c60506100c04a00800e081901000620030044015580d140c2c0307030b0f1a549900b900c02102604070b004000100d0460801c2d0b0707114a029500c0c900e42c2d02c500d0213450030011802d820f5034a8140c00030040e001c2403000d52425980031b1544007a10503c0118205520b0059549100c1d001c000f0b0b44008000d80c07214000d01c410038002c0952020010108032800c850b60307017941d000481e16030143c2d201c4804160038001c004c40310710700c0c3c0320310000a00d410b0a05001040c444148043c00004500840d80003551030000c03a2003103040503004a0182c0068100343e42d50f51001d07980741c4890340c0e02d03558019414209503988004070025400782c00100c07140761201c1d001c010340c0c0707428102e1641210048445074910b0070724008102c0c0620456944602d94 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 499141969 1250 499140719 499140727
    0x901150201020c011e1b08060103090f1505041b1215021204080d1d0a030f050412050c0405060f0d0f020f0607080703080708070207050d050708070807030525030206 72
    0x25100390103444007903c65000038002030800c080303008824500034080c076410900d00307140300f440ca88110544065110082c3c5441207180c881c1001100500028141900c0c03010680c0d00c82c400143c07250b841126410300481c8000703080d040c1454101080c601c011629888049849814040d102904c03c1024405a1020307540600000040005020340510100690f4000341c0b1803c000a01840100504103c519034104002c521031088001403c0c1018246024241d4400013a0b50b00103809106100f4506070281820740c1000d036180d094030700084840d9011140c1c3c3d040410821110f060074020141c02101c100c6040d4241d64440000c9002d240c0d4494001c0d114003805804d160654407a01820049140301410840c1d4580480c10056110380c010719044000405030000290034500c500078440c001c01c11a0701a0003554504010402c110715010020354285c080e40303038000783c4908104182e1004210b00c902500000d440c0d41040c50400c10403c80a01d9480d2180000fa002d038801d064401c0152541166000d4031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 499143219 1250 499141969 499142009
    0xa0810150f11010b06031810060308090f030705040507030b04200712030605040609090302060609040203030313020402120a09140a030503220204050114040b0612071416080d0c08060901 81
    0x2401c80d21120035000380c0000140102c22014096107454480084100c5010323a110350001d070211503a030710024041c00ca0611095105180202038409003c00007000c0707036442900c401c001001c8070403da035207402180e620421954a030500703009804251480c40c0ca060350f8003650140c8118140310300600208502402e1055403e00b9000c0d900c040050103001d00100895030320b803c5218010401d10a0560140c0300c0c40d00040c03200d15020701910b1080340e020780614156154401c1e0100c407802e095104a0340103801b03001000366494500c2d0001e00c642d04590011500245508104a008202440300c4280e500050303100000310707402070120380d00701e0101c0304042180038015003800e00c5007881c0c6038000d40c014181000003910700d050207003001d04000200d50811807010707401c080102d02e20952504c0242d180d055000142128010480c85100007050300c08640752540e203000d039010000c81c11070101c1d83c209001ca0841883ca40911903c903c0c900c00e400d00d950f86082c202d0028041010503c00c10294268400080f40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 499144469 1250 499143219 499143221
    0x819090c0b03070f090509062b0f1b080610030b070516060f0f02070f0f0f0212030406031401050d14010609020a02010204210c06230a0810150f1101 65
    0xd210100c5110b44a082c0031400800304d00c2c05107440400260485000b203035500d82081014003035038000f032070a07191140d060000c46c00b442c4c0c03031500c1d6000f00300468004c40210720400203100b910340c030850107e6403c110780207450151a004d5040b600b06075102008008119092400440a50390440c10068081d5500c4404407007610075508484115000801c9083c20403480d6040340416910010040c0311641c0070728a10400c03805101409001d01c4e440350072040c00308040b14031130b00126004071401032aa910b96000300780402030041c0521700c41d0380000342c2044965411311031450414045180030300c45501d4000045c0c90000840f10140c802c2d801450000d81e100001d40c4020010b04021405544452840790302070700039000b5121f04014a80b0704110940e070358244800c60003004c0d41c03240500100604043c0102d0307605a40429403002100d207207203400c1d98440c142002d030610400d15643c00d511031406051404080403039a204941100700a0502d03141c15800400034107080801c1d141000d0f1850300c0c1e10180d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 499145719 1250 499144469 499144493
    0x9090a05070c0b10180b09060102060c04230a080604060f06030f060528140901090c3606171f0b0f19031a1012020f150c010c081909 58
    0x3005c40c0c0e0b0140d402d41409182030708106c0e0400c03003c985802d1a6a103002c016130f280e040880d90351046400c100410300c450071000154609420207415801d40c501c01030008611161030503041a44664880f40801c01002100e0041d08510583c182c2c050045920715070b5111610351340860b0040c004ca8480000442081424140c40100a1042c40b101c002ca4003616002000f8640701120840c044003490000320014014052300a81590241da010f80741c0f85001204c0c40c1c0040041021820183c50980341c6410039040600248100030301301001500c28a0022000701009030600d80202a41000001c440c950820074080d00c00e16901c0c070b0001c2854000725001682c560160340020764807041106122921540e155035210589110781340c05405c0114401c001354030b00304219182036458220f88010711080c0758000b20840024070162034001c0ba0304588002901d1000100350b408140b5101190b20001e81c4001d00411111103502e00700780e240c90030545a509054882e031511079245a0b00c4001d10401c120782d840c065 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 499146969 1250 499145719 499145729
    0x50723031b1c0e1c08191404090c0c0f030216140a0504021605010e210c0a15091a0412050403030525081204063c110a0509090a05070c0b10 61
    0xa40c402480c10f01d41300b810346d0001c1c1103950201c020400800b41e068029803081d1001a0801201405c0a107450211400f0f0702c0356032003100800c0049042c07800050400412615018841d40142c07807c00e18183e00010411400d80c014404003201c01414206500e501ca154804c2c0c0748160f40250780c1c0c05201da0400060600c0300d2000b070031986040140c0da0284000710360301c4c001065640b5005880210311076151494001d1005003082a000304810600103003101d042c40021448812000c6078040040d11800380000400c10143c00c840b81c00307800c0108004000f80e00303007c24161818442c1c200307425500d00a01c070340504d100c0e140781403100c92031812261150900300311407250f2203100035035100030030104640c8a8100340c40c1191690304003001024100501400c07003119034103d80100c0464502c03da17043d50128210041c01500603038409150601001c000002c2c0050302503070702c0340c2c1d681b200741d40c090000d0020000e0038050a50b1600d4244014180d201c0030100426400048015140e12161601d5112550340d44c80 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 499148219 1250 499146969 499147009
    0x717090c0a14030d0e181906060f0915090608090a0b09071802030c0f07060b0a080f0601150509190e0f04060509060702030a050723031b1c0e 62
    0x1c9405140a00300b5842600740c0c00d039024088070413020f90311352140c540d802d64400066100382580b50b0321039403402d9000250030008130b4528075050011003200d40b15007141c000200e18036216822223410200650042c581401c0c202d0400084100c0102400710f41c0c01580308103c0c4000104070340c5501002081c143d6608140b035607916007415080d49aa1ba03a1078402d81d001d05045400690081051f403083da48074084a213001468041c0f03902101145038403460080340c80700d076982110242038032141c507010f002d080c402000704484074080000600e00700d4168420302c034010495100c001040d82c0a0255000d014040e1014000b800b40c85110b40c00b00c68050300001c10318012402080109440c281318103005a000303140c1044903441314442e40e900c50038102d900c100907a00420072610828071070402055118040c0383d00d80300d8060010a4100141c1e40458010791035407000c960703d07900180408100c030180c4200c40c001c00c80455130000400b543e41c154a0303044140a644006456035841d0b0760b000300c85e80ca184d069 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 499149469 1250 499148219 499148239
    0x5070605090601050a08010b240d0501090b040b03010504050714180903040303090806060906011107031502070218100621090312050601050418050402120610090507080717090c 77
    0x900d1590340320b092142d0780c4109260b5000040030001842800403824014100302c040b0141e40416407031091102104401226080088440c100560300c1080d01a01c202d0034040b881c074a901042101766041c080c90244a80d240505000c00540e0005030301044030f41e21560b48220390118000282030721344600c0d0039007080c00200c0802c81d05010101c010415a4440d0b140c4080203519513004035690fa10840e1780d50380050b2071001180322980981349613810740c01c3c0003085851090301e80d610f440c40d089010303002d1101c240d00864545c0440c89d08007405844001050202081850100e5a103131540c1407901c1041e0921498803d1441301c0141d841e603610030700d240f00405101c039001520340100494601703a110031700c06151a02242c2658810b200300c9044036403000c00b400b11080d051914170000d0001601c00c07a80301845001ca0101000244640c6121f0b41c6224500d07842245061b03e10405d0301c200811000c1040150401c2005064000e1002060a00489074481c203641d91040c449243c840b182481d2903010b400d00c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 499150719 1250 499149469 499149481
    0x5090a1b02060619030308070305101a1b01090201080406050702030d0614090a05131e050604031806050906031303170108010c1205070516060f06030b061f020309010c0305070605 78
    0x245a6004140580301c881e410030002071114444d082ca400010000b4640030082480c161281d009590402120084140482d6071021a00c044018190001c0e080301008258041805c3d95815410f40c000304582c02440001016400204240c1c4014030040040303035a10041018644200142d0b0200007401c00100314142d1900801d4040140b0690180e1181c036900c0c000034002ca68601526000e0010210031050b240c1306ca6413003c0c204c1303240459058000680c41c1c0c0c440007184042068501542c000c1d142c3e4443c0112003207a0500420980d0484810b00404022074031031621440d048903406054502d10003003130401403400b103400030303c03140100f03070320340342c280d0010030b0444040d4841d8100c0d40b06900e03009200fa82c145480400d480f01107841e6800f20b14240100b810442c003076545034620503c1203030300052000828002c5012035007944c00030b890008807641080780c00e040480c000020402e51701c14403902c1041c1000029641d03c11011098104540c9840d007000301801803041d6400b1551208052120745010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 499151969 1250 499150719 499150723
    0x2030303040b18010e1902030a15060512010207020d08090609040504060209031b0d02010302031f0612140f060f0111030d0504030801050a1a0306010e030d0807020105070e0a05090a1b02 81
    0x6a8001403080c60211600f03c0201051090043c08241c030005070403401c1000d0b49101407504c21101c16a0980501000f0f03c0000380402c101c582d8403c240180018650704000500c50f10401c2902003100980c410044200542c2d142e0480550b80d9034829031082e69030102001168590103040d1031a038100c0d00744414402001515005008505020303001c03101826002026110103c00c0c4c41d441541101d400c200100155109030029035004001e0710140503d819001080112035489074003100000e580d02c0da070b1580d90004d038000d013859900003186070741071414003014040195401400035403041c4085410059184d006810200481c1c4025003501e888045150800c405408111002c40c00a9030302c00002c00c0030724000000c07005a4030290600744070303900c2403a51030b10581d001802c4181449101c140c1126a650100711300c3c1c10a2049598040032420b00040207801c1d81c001410200038080714036200003468860f9441e00084139421100189517499007947d00c00140000810031410003050801c100e104d60700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 499153219 1250 499151969 499151971
    0xc0506030c0d0e0c1c15020d0204050d0302060a050114130905070b0f030117060f07030902010309120f0206060418020d15140910022a25090509010c020a0f030c02030303040b 76
    0x30031713200110b80345040b908102c030008090314001c080d4512651342c036080c58810340c00303007840401d5000014945615880040c0c58849548000c80041c0d010350304000d010980c80c01994018030005141004012540300001e079041c01c12000818825910f010781024401d003003101d00c00520303041c00c0e400c0d503400580141e0307005580240503181c001c0c82000070052800380c00041b890310482001c000000962141e18003240500364840069040503241d00c203090102d207a080460441c0d680b5074999401003414914041c3c1003040040450744540e20340b2404410581d80031580b9118203504035200b40250195140005d01905030444400002d46420381001c2710b0060014150700680c6c2e240100e510f0011249001016031085084003404200d40385941c10244400c0304a200011000000b80d44240100c04008680030f10a1001c3c102da034400010100090000b921417240c000d40302500a0085084605010790707916120b40000f06000e80c9102420180b510079180c481c0915401819283c2c0d90529091500510340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 499154469 1250 499153219 499153243
    0x30806031f0e1209090403140702130c030f150b2209021c0501051804030c050607020102091801230a09020c0d030507111c020f0604052103040c0506030c0d0e 69
    0x400d03029003080780749103281910160607000307282a445c0e540e1540c04494519240e140c1d03084a080c20b014440050303a0b850800d201c03103244680002001c641800005096400100012140364580b41c03603102404040c4407504181d0b81140006669884411540082c40310000400c820f032803d003000200d0610b5540e00140030b004024500001c0715508071720600c0444100384a5254010034039148a440841b0294a1540c407902030300b89054040744c203450322800c00008031a2400141d6000584101602d000c051000c001c000b07008200b0212b47c18200f10480c1008020b110100341c00141c03090107056510001118080c1c81101829034503502c00700351840c3c0c0c0f00300c80311080300480c1c00c210009000921a01604a2a40d0200010b081411560318031086d1070765641110f0007180510701c1d82e0a0445403c200040c0a144220000c0c41c07105480c100d076014240c4d469103a01d480e0300040040c070003c122204240f034165141110a59a251200c02801055100300078569141ca8107064284071940340114200030312170703 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 499155719 1250 499154469 499154473
    0x70320101d01060803121e070c03030b1e150702010e090411031501060207150e011206090212060a05031f2c062e12140703050a03020d0912030806031f0e 67
    0x14541d03001000c0c8000941002101d040d144000223982c0c02e2041d4a61300c80c960003800c00056800d4030b4404a9007852820959000840f90700c06800d1507810144502e40045004460039818038a10780c0c0001c0812644540382885408640c0c0070400b8050b840200011040c070090454048146400003c90505002d124410140c000d50340b00040c805191070304a004c20b6411fa036403a0546030260015140303502e051171301541980da201e6010803001c00d144010101d000b0b030b611448076a458100c08100d200705803504501e01a40102260001004803403070241d140c110105000310b01170442c0c600c0c0c00d26070101b41148014064148000403900a40400d01d540942c0d114866444528240c80c0104030024840346140310515000380e0800001d00d80e21014a100c42c810300e09080c0203007200c0010343c80c160440c0c0040e155038206400d024101601041412506101400c04c81c007000c3ca44500000081c015030809014001260f00046043d40e0510248203066150010f030000c454411314002c1c001c004a0451101c68 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 499156969 1250 499155719 499155721
    0x6060e0f09160509190f06060c020301060803121602010b060313051507080a020a050f0f1c090c03060207080c01141602150604090f0f0305070320101d0106080312 71
    0xd00b200008205981000d415040d03161a400e015070505000390b5021414550340788801007958140d4003c00e00101580da641481c0007501c0d004042c21540c06901c4000c2590040103003c84c1c011811203482d0b403090b000690200f510340b019600b6400340252004203030303009070004100001c4e4070407203903100c0169020f0380c11640400e50329040003941c10302c02d07100240403500d03074000581085055001004a40c805281040c1000b80c500c11400d03054000e808842c000d040003040031000c4103620341d01809143c171018018429000c8985036950783ca4440d01014000d990009a82000c0c0308143c01166a000030303040c001c1006a85a4502585d42c8005507041948400b034071031a500090710005020005030711140481141d501d640040000038081201d0480740101d00c1201000407403400000d504805009803100340c1d69400625005081e030256620302c1a0b428144420f915150b9000200c40c40d00c0750b511b031000190070381c8071a1300d001a5071502c10151142e6081000200e0441808006130035201a0302e02c2e00182 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 499158219 1250 499156969 499156993
    0x30a0e0105190507090e130303050c0f04050f040b18070207050d03270f03051518030909250c170702031c09260f070602071206060e0f09 60
    0xa89800340c901180d0356040e1030580b401c108542d480b25030012000c0c01c000042550390012a500e800c0b044600c1600e00c1c3d441d01070a401e01d90540901d075071080005c4201c41c64400c55070b000c2e075010301490142c42d0003113000d250425401d0303c43d64881c00c0c0342680104500d0b07601800c9020a04101011110030300180500000020907082a01d610b045569050319103002d01da41d025130204008010802400303042c0c84c03402c40019955a0000d040001d540504050125010000c41826864402030a284040d9503000781035611800e000c03080e01d0203500d00700c2d140550381d2100040c03d05004031044000740d0030840e020700d511040c1c0c2c1002080c5400c620401d0700181001e4801e0746030820307000d0100069007603080081c0f4841500034410614041d1392260418121003902e60300710070412001c0e00c01c0070034040303c80d0401d00750044041110300c07540d051000c02800d03c0ca0400c8002074980a0500c90590703488180b541e0130f400c11140c5c0e048400540066526a9a5860a0392030b0080340d101c15504a1114002d070681c02403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 499159469 1250 499158219 499158221
    0x40606051305130908070317011a03010603020306031e070501031d0715111e060603062404020909100501140a09060c060b0312131d04060c180902030a0e01 68
    0x181c140041c984a00e080c5240a040c0300103596024a41c00d68184e0300c50032103002445071301c05041014085d9480391942590540c0131280084107800c91240004642c08024800110724203e0f819203502d480d001d622500c030030740800e14242c5405425040050300c01e4003002001d200040300d00842c0c000340c0e07003030003000c880c58040f02007021000400e048a8008900500c24080120806e440201491038000080e002d4032508034204050340403850b80c100048040c0c0321a4040400c40280c00000c101d000c0c0040c1e0030f00d2202e6905c80e0030410700003001d00c1c1500c21000707441c4c0d5581d8155030300340102500b400420310300760903030b01d03001101402542d020802d0b80911002488061041d9100800b141c0c540000d26810018260387e60160001e0481d102e030b860b440070034520784040c01200310707040500d10416252081850070000c40d01154001180a10320b80b4222901070f00394a000d25045600402c0001d001d4800701d038202c2c1c0c1c080c0440e6060030644060311001600c400b580d1b0042d845400d84031810030100400f400168 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 499160719 1250 499159469 499159477
    0xd02100f0b03030f131d0403080a0b03060105040b0a23030f07080c15071211010e01020c06060907050421060b010e211f150504060503330a0b04060605 66
    0xa90140d1007070210800081c560001070201c108568000b54002c2e0386c5c0e0300040035500c98001c43d031265204810074841055000901d45400c5580054280f18094031400820340d1440705201d814402d6485003140c2c10107403540320040020b000d14038031403542d2030b01514807803480211031804240240b00d140348950240c400440c041050f59004d0b4040c001c100c070034074100200118003090084184004021100001e920340e80420160b080c0e9850b50b0309400b040d0805682100c0c0f08000132007450b401000640109040411600e5202900700c900310015106c010b000c98040c055600076000c07502ea00c4100301e2000c107100c0305844e21284030304010300660b00f0281c01102c80a110360f40711a00064400c104808009100216812018484049842d480e44a0b00c2d094010100d415541b40700310f81e205456000c3c0c410b809034440c0606010b032800d0020514200c0480d683e10a400c95418045a50001141044841d480c2d40c000a184102043c069410088003d80081014000280c8101d181800c006001c0c0c1c0a4403d032327 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 499161969 1250 499160719 499160741
    0x3061503010509010303031e0615030c08151203071406010315021213020f100e040509070b0901050310090c090510090e07050c03040b04030308090607080c07030e030c030d02100f 78
    0x115800f1392070b40e50145c020b003020020801c4070182d070204000c50070019104420040c0f01c2c10b42111003c14030040041c1c1220405074561007001402010000d0585201d0190180b4010030f56160703140d0001014214114004c070280105040000801b1003029a80018183e05032800b4a443c2e0900740d01140140302207100d00c003420341905643c280041c612140e001c0c007080300d44d4005054800b0418410b000208c000b01101c0d0300c030b1302040621a021000b0308140c03090340c1d849208e04000380092401c101807607580f801034038211410000f0010000f03440b65920300c050002050041418403582c50030000103010300701c2c54018075006030710110041803034500c550382420484d4003610650800b500c495104030f071154440c00d4035021a202c2040005040c28070f010003000258000c2d5180286410058500750402c50068031040401a040d000d2046285503001200d02641e0300d42000801c00f007032080406d0400d1018414039a05000b6250038442894000c244120b4144510710b08008104165010700103c1e0481e07801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 499163219 1250 499161969 499161979
    0xc0b0703090608060d051203090c060708040509060a03051002070b06190608100b0408060414030c0c0607060f0507030b031c0504030b0705090307030501020d060f030b0604111c02030615030105 84
    0x2040b842c1e001d61100703500110041c01c40102018207131261071820704048a802c0c400f01c8000104041050280302d6521350180449103140b4001d1aa15521414050f9002d1a48107403461000303d0010303078600000d400255801010748440c0655140c4c1a030080d0170402e020340c3d0000d0118001402d0385000003901408003015044102d1680c149041121400700c000c1c5171030b80d40e8141a42c04500d0941d0100608001d1a4850040c40a4541403406141800004c501c0d901071b540b0a212030a00f648011900b00c0b80e5503000e50710075440d04c1150900d600034010b0302c410807002c5032074441401704156154201d000086001e40c02c480380340d03050784061010108007911800008200b88024000558030038121a00218030346003050400059800003824a1100d60003143c0070b81d400600d40340c4a880d180101d00c0140003010074491301074950b86403010010401003150303100b43e0f0354000c800500310300701c001c1c4c03241c03c1c0c0d011b21569240104004204020340c03080d5181c5200c4c200a070241c0e4038100d0010100c0f0305803240504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 499164469 1250 499163219 499163237
    0x15090115050d17160b01050a09110f1e040b1806090f0d11040c050712090f170703051603020301110406140d0e060c03070f0815010f0c0c09090c0b0703 66
    0x42e001c0f20045510840c5980721020041c20b0001040780d0382c9090224000d164001955260008100c85090f45500228400342414004200c1c0c01d00c1d54241d0700389036001050b895452034030b40414001e00d0030300c0f2440c01d020540401d02081000400e0054080c1c11414101750180d80d41d420f080085034001c03510960b038041d40000140d001c6080184149038000c0c4188000c0d500411703143d0009040c2c40c45616003500090002c6800303814801c005e59014525881341c1400d0b8009400e150746094601d00a01410601296450341d0b24002142003010000030768000c01505d0001350260440180503801e031009038400d60800c0c01c0080c210b0b24035030072181101e0054031480c2881402d1a207200c515004544203600141d03a441071454000400d01025100c0c0e58010889a03070380c9000311010b84409840d00c1640104620341042202e886600c090780d10030f91909007000179504980c00c0c4121070134100700c00c000b41648a1520300003540342d6140c05c40f00b01148100e07420714802d62103c60601c06406404400703000214410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 499165719 1250 499164469 499164473
    0x30c210209010c02120a35222d0b040e06031606120c0f08010303030e012403030807170412030912020601060207171002031815090115050d 61
    0xa030003000220018100301c1001080742d000103031003541810901c080c0b9007104251324100301c030350744a40360300c1c9020780c00e9005003060758005203842d070801c0020709101e0f20000844051100c450582003541204a09110354403e8642c6481c5025408018000c141d070419201c1da0205401080242020340708061076003428a03203016034030349c2c1c00724010304002d03014000d88a620605035001002140600301039111600320401c08800d58046490300c000c0381c41005a15207000c3c40165100152720f04507505071038081408082405400d0050846409400b40a0280302c40032707610250310303079052048a0083d00c3d00740e806d03925410240c901c00f58921080116640040004000400c05010f40c100d41ca41c80c41e00180260b030a0f900c281600050249000160b4002001003105d10f0741040f41c0005400400301e080c480c5a400020300da560910032070340c050515008000296014070024946800d41410011a114086510344400c1541c40984030b0324819400c0c014145000c6101c00c1b912070489a01801c0c02d087d204941d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 499166969 1250 499165719 499165721
    0x8010606020c0402090a0e010b0304110f090601030b0f0d0c0513020f0a11030d092303090102032505160608010503061003120e130204051206060a0e07020f070b0a030c21 74
    0x10170404d07075000c298100c0100e002000240e825000c0c00c1a044060790340d0906041c000034810203590828805c0c00e034142c14010342d440358800960814420300340030400420100000c0c02c09905650455004006a001303141804070300454401103500540d000d241c105191301741c00f0140d05c01c060b800b0b036100e9002c100c0845018440c1d00c2d01c1204601ca80140c0b814881c412242d4011307070f081042e0994081c02c4900b0845595410500100e24980f9028029403030040c4020010b03407030340114642c968580c00c0294001c2c0d02000030b4034402c4085075009041e01e02d0361500c101c0740d5504141a01071980041d40500011440703007000501c4600900c807004010301d20364070313640e1001541c3d09407581c2d22003000401c0c0722020320f9898a41001250005c003407070141c3c403281000140700e80400218205d69280c0c4c002000e008154440001c00c9080d103203407840c010300c16500c0b60b9003a460004142841200f40c8581d204c00a003142254010b00074541050390b05001c003050f042c03002c60b0a40030060041d8207021808a848410f1303030403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 499168219 1250 499166969 499166977
    0x17070602040815011805010e1503030d060e09060726090f0d0f0e0a140d17071b060203091f120603110301050708091504030c0209090a030908010606020c0402 69
    0x414440589070035162001107041064103400e070300704060010010700400da402c00040441c0d6400b0401003120303625080c01c0360041d20024042c10804c010103040d03030f022034805104032807804801c030b1414041c007651422155140941121013030081c0c000c85020a503414403c11024100f1b40d40300d01100501c410303561150300088070241c0360544910030518080440d141c140592581e0100540312045041000140501500f84240001b07204540422080c03006e110030b00100c10340b10b28243e81d030700040e011901d001d02030031565013945688941e0200b0803508104045030b031911074900e908a6032903401c0d80e40d0380a80e81c034080d8002e041d83c4080c5010791071f5000005100070005085251410b031104480340003105048400ba900282e9501c480307a0000000346c2024013400341c001c0c81c6032500d801c2c10718015082545442400550540e00182000403d0a140c8202900e07103003107130001c2c4011080c1c00c1c25041c0070b81d036070034503070701100450444900010040b106105000c00c94019801501d050204502048002c0d0b00c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 499169469 1250 499168219 499168223
    0x50f0a11041419230406061b060f0b13050108150f0f0601021c0201150b0307020a0b0603070317070302010b0906011704051207080c0c0609130203071e09140a031707 72
    0x400181c0003818150b40302800004d801d08440d05101c80c10164240000d07510703030390496014001c50f181c100c1528038203201c00804a5402020010b4085030b0b600c2080c001d00040410281e00a20240c0304200305c0072168000d80c102c8020004480700b41c1c4003842100c410302c40864054071a4905440020050050a180603512280c144192404c0210000c20119a69040400440103139598000900f600301800040806030100740388440c1145070100000f980c0c0c050007080103051900200100f03044d51020440321000d07503800b10a9401c2180000141d90741500070140a6006608012036100b40382814034100740610b40c1a9030341c06e40d104030301c04483c420344006002100c0510500d61005001d15503440542031003403240070156a10543c0041c10362805240e0080644916010400e600c0d00307684803090120b101684c040050b03240d544071301c015507018041542422804100196900e8010385c0088a0b409071640f02030502c030400034010601652031600e01000300401c2c065666003015400030805440024 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 499170719 1250 499169469 499169509
    0x7060e03280e060309120c0d230307050c010608010203010603021909181a040905010516021516020c12031309050c0706021b1603031e0f050a030f050f0a110414 70
    0x20b1010071b0244030a500820203030141760000140014555480311804100c401e030030260700814912000c034001d2034803014108801344070340003c5036400b6820a41111008100e041c000315225a501c1034061b01a5200e80c05034240002140c40800390b5501640b000c0702903910704001c03001c0c1c50482ea4242c2c0e00031700c00524400300a40c2c0307000e880c1e23006582e0390213415645c40c810800400c06082c1241100f06013080110640190341045490030003010700219155409510440c1c1c814612111400a034107002c03a03004015009240600c2c072045c0c0450000051003425407102c502400a40d0303030302101c0c1c1101d00582c0c0c207008003801001150302044458015190301250481b40d04060034404108500c0d020b00c0118015042183c1ca508105068000207211a004050351882c010030320380e0300004001000102c40c4500703000c40840c1120021384250302c1804586105182040141400f0003c0301d07000f0070031540c5000349414560b01c446405a0f010a5070121020104c039010141c50480c200030904801d00c15000d024 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 499171969 1250 499170719 499170733
    0x1e0f040f1d09190602070c03052a040902012115080c01170601020d08150d0b0a0c05130311040b04090f060b0a0f060c0807060e03280e060309 62
    0x4580d42804650040c03003003554014100036041060052075030010070341480d0781c02c03070783c460840040a11041003030b15503c80c500507642c6055262040594081e80c0002c2c2c00c511900030080b00748034032111040300c050900c5001c801c80c40e0300c0b0420030050b00c4948078000d0000301408103240002d95040548070030a41110400301d400c0d081c0c065100400e0315103600c003210a61100c0d0340b00c0d0b01c0756004407200610380b0800360f02d40c501d490100c0005c0d40d942030302a00502040980707400150a10084400184a40001414100d125030305040c2400b20040c16034020340000c2c50041c0c030000711406801101c6401c1c90170410042001c0c610340799541d4100481c1119500b0640f80c2c600e1b440942c0d02c5225088840748901103001800350681050000c4031101c0c00c0d8240150000102404a185121190000c81c0c181b0302e400c02c41404913140c032205502a10300010b001c81e081411120010b24044007519505030600e0801980701c800c0302802d0000544035136550041202e007001c0f030219081240040d580309417000129169 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 499173219 1250 499171969 499171979
    0x20103020d0e19030806010305060a050906030705030624030a03020715021c0804060b0f060405061b010f0b01080a060e0c0f1303080918060310320118021e0f04 70
    0x1c0c0030110a003d55400300b5140d02004164102c181c2c15000b42e020b20b420081441d151002c55005160380c050940f01d07000c46000503100d9501040510090000503003950214240000001484c074408821500142c000320b020340a01e0600140c1c1103200c0c0d4043e80100032207480e2081560041c120b003c945001c6000d114140214408181c10500410b1a56030303402c0340915003414030804136a09081d059205144040c0072010981c1c0c0c1500350b40030b0399421501c0783e030b48504501800d001d400a03000200015400c0200031102085150300040d1b802d802a01c0d40e8406035a412031b60011660540204182d4450f181d01144060202c00d0103000000c440302d010a01e4034182d002d11000c00c800c183c8c42110b00342000a6078111710305050341500c60280c0d290015407440d051403000030f5242c140b0000b0441605a445240020084c11b0345103111140c2048226076240741b441c44410320f2100400d000c1c086c4042e460000544102c6040e20850311100c249c9545120720026844140c00a41e00848040c801500c0c10702011403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 499174469 1250 499173219 499173223
    0x2a030209152203080a080105040513061e05010803130e0705190905090a0e0c01020304030807110d080c010219080f18100612020301060504020a09290c16090e030403020103020d0e 78
    0x40607500902a05840326017461000f444070354140c20070703401107040806102c0744601103604803800301d60250000c2045916002041600031601c40c2c8000e4036810b00000061895010004100f0070380c4100419110580306e60a4a2003100181c5143c40000c1c8208060301c001c407441005032a84840c5803a00c0a0000e50700d2000034040c14040e00c8071020251f40b020740b9401d07108100402008140f00380065400c103851174860851034050b098014000c071549000718200b6503200c0000700c0485900102403522045140e600d54000e41002d10542101d410700294000300354040e03210725203e142c04600d010032603655104c0c0c0c2e0204110b450200c0000744206c4010078005e00309802814003400040301010b4404030b90703004041c01e403407084d408603000e2441001000d80143d4403006031030030340b800d403140110702d541c261055200210404919800144001c201407080c00c2c408120314411400c00341100b06810380b0b801d800c904507003120f00d40e035100340e008110401c019402500503000286950b000014201d1900142d54 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 499175719 1250 499174469 499174537
    0x905090127050a020a0306270b03100905150601032d090507090e070e040c1703090406090209132c0a02030f060612120403150f2a03020915 61
    0x10f0541c0110b103c10302039926104202c0100b051040d41004440601400c6c92294447e40074110101d454140110064500300002e0150f84003c08007008603012074201140c9510ac2450b00e82c61000d07003040480d08945c440e00400c91040b096029510134401080080210b00300407aa01c0b401c519107400088010404c14803004000b001c1642012481c000c000c8030181c10306c0c401c0d801907691207410303d0034400420b020783c4c03038441500d80c285640e288070006801c40c01d18500581e10f0056119042500104100c520380d0054102c00d02e050720407084800a0303603007031829699200c901d0304007101140d1191881d40d800181840e44e9401c40c6044c0c0b02492604d80220f82424a002305642c40ca61002080c0000c5017020b00c8410784d01c00400c0b01400c0c101080310310880462196100c05000202440d408014003601c43e40300704654424420b0030807121181c400d0340c03000040c910300f40c1140400b000810003404c50080c000c5031050400285001d03201e007122400e43c3c105030170420440f02000071104080c03c04201d5641c6c52 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 499176969 1250 499175719 499175731
    0x30c070b0304020d1b1409090303130219030c3002040b011b05060402030c060703020606060d021b0a0c050402160b0a02040305030a0e1c0f0209180709060302040507090509012705 78
    0x16502050502c101c1e0792091b0602c0581a004002030002c00c08464408801d0b650003040c0400300c012114103d0001400d40c4070000c8414003020400b900000800c0301000d0290101e42c90403804041607480d0340e010030281c00685a980d0b816003802d42030740700146080d5001c40009141410704a004030419500b0f80d00300d05400301d04a0382503000200b0700c000d61400f00601401d030801144d002d46064000e5900a44841c13015000d540504000b0456103c400e64540545401c00d07070b58042030291009618200b51349078070048055074080300540000c0b50714203040c000c0303e0300c0d205207010003a82c8000d1556151804074000f070203001010b030301780000f000180003400213124448580d034941109107500740411a5900c0c220340200143d2900b41e040c0030018060a50710300c034151b01100c01034101e80c2d80c0709168079220080030b1180d0f494003c075980031a90100c16813001080e030380281c4040105a55500c000e40f840c070018000c156111400e84010044001ca685030343c0c150044500d40c102880080354218800d440d015111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 499178219 1250 499176969 499177013
    0x30406030f0f090c090c020c1c0210030e1b0f030f060a0b030109020f01110106030212030d0f0c0522050402180f040b101b0b01090c0f02030c070b0304020d 68
    0x441c0810700d41c41c0c02200407052241e00d042250b00744598807115460f000d4031501104940b655100c81182d402400744c0442c0380381c042e1010b20346201c440722a021070401c0c280d04038806d92005070203245092091003911340176010f940040c8a0700c2e41844810103829600d003c450b41c01000b040700315040d43c80a00081690703121501c024003203401d0010685054803803101c880e42c00380e8541003070706005d83d4506440c42940e10003070802c0814075001c8011036014006507000a0f42111100c0b40228000d00300000400082050500402000b61b100e90a5029100c000d4140800141d00384940019a110040300001c107030050214005060350310b50115040c0e03000300051048800d006400d07a411800c1914840c003c1a0b4200c5d810402880d034880000c00002e00c051044042004a064000d000e05030101a000c80c25000030703024134903603034800700940688210f41009000410030480070483c2400041507444005418000c0c00e0814240011285a0340005009980c0060400618004982c41410302d080d003400c0701e84 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 499179469 1250 499178219 499178231
    0x180c1003200c0c13090b0408030a150f1511011b1b02031b030a020a0e04110108010b030601300b010813082d1804110423060c03040603 59
    0x58403081c40a001c8020046441041101c001c10b00300c08120f00103003031000c82d451a00b441d2114254002090701c40c000902101d442824801848081030203148640403402c0d0510141004c0e007800c0d81c0c1c1c0082e030312810070480d40740481031250b030b8522000c1c08442565031602c91109102041c0c44c50a4504144a8800303030711501c684902c2071030340600c0c04200b4580710400e0254075409640030039034450a0f44022400b4911b6410032031650307502800fa0300c00868000707003208240c9444040200b0f50801c2035070b0460740d2184004c0000b200d07500820545040301e042c03e042d641503a41307140054034a448840a00f201d110855500340c0005d07200a100c4c0d00c990882e1800000705c0311070300c3e40050032081c4013078103e0340c10104840912000400000c01c0352045c1840c83c0050410410144981886052002921002c003102082400c0004030521407801d111208543c140710110381c401d258100c51159004003c2400303809840c01d81d11194806d8414400c00000c0c200a01d0103407510403003410742d0465000000003a80b078803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 499180719 1250 499179469 499179491
    0x2070f110a0b031608040c1502070905060904030f0e010302040911070201020f030319150b0f031005010813030c0f150905010605090705120c0702040219030e01090506180c1003 77
    0x1c118400500781e60b402440c03441c10011402d103101ca111001d10f0040001034000078042081d11070706030004040c1c01c1c0201d1a9075074400c00294a40b411402000150340c9448001001440c1040b492400783e170f056140c1c0000c0c40700f5803170700b100c0c40200166841d0603d6002c21000450a034a48100b21034041d020380b900e900c6600c0d070301c0020300308100384004244540c030605c11b00030b110300c0340341010a483c10503000c0000c0790510040c84800c01401c0c0d510102c1e0020380804c04200d98100f0000541c42070400400540a00b9100c03401500c90400585404001c01202503d500029000e00c0014400314021540101700d80003a81e5441c0a41c1c034405041c985c00b07a02c840d20201000800d00910004c1c100440b0850b90514161400900c2801185d819518482070f16012840c00c07815031046078040d0303070003a10556403441d02c03c070844620f514040303003640003a14212806c11484070620840c911107500001510203074841d005043c210000c811031100060107508070300c0c40035035615460752485030b580352408201c0a81c16 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 499181969 1250 499180719 499180729
    0x2091e15010210062103030e03030109050601021507140f0702120f1023190f1407020318060a02010b04151403030403080423040c0309050105100b040308070602070f11 73
    0x1001c092901c02d0901c141880160000b000117981d0155210004105109904048001d4008500c1080ca607000c000b0002c074004246400851103a41b00707070200d6176100545254001202c0d0200c5071400001c010642206004401070010320b10510030480440c2081c0103034001900329007044250707c0389a070021086403911a024002c1041e9020b0180e82048030101a0800d608008000b4100040c101c0c2454001805410b0000700b90b2581608076208000a026460350785c40201882d54600d881c51040034002820640b0000407150a0301d0b01c04020680d2030002d4061224a030491040c020541d5220580c1e0030187d2503a10a040041e07849034448825240380940c840000b0810903540e50007038204010600204224000b180c088900c1c5c1001d0740c4000704c03014036030110341c1e140da007616a0150514003403610f0194075030030114400b03008a000300b0a903140c910002c08003420324442c56048085c144010004280031710043c0c60341c640104c00c003514111803603549000d40412030714200e4407206201c0c83c0048500300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 499183219 1250 499181969 499181983
    0x815040b091504080a0203040806010305060405370c051005030a0c02010b100e010306030c090207030f020d0c061503080408070807060e0a0e090c06040b04050111030405010c02091e150102 82
    0x101c00070349480e0624584034142040c0050014044000006284032928400c1040301c00034901d01040d1200740d6180c0c54a65100c01d4251815a058411520341204985e40c0c0c160150482c8800c0c581c184070081000c844000018082c42d06441d2440d030f1600c0003515886814000c0c045043ca960703400d90b80e141c8083e441040303d00d4450798000310f81c5001d03050945520340080c0d6007429116400c000074501a443d004034090400ca40000300801101da0000403000c446030050845903202c0c0c3c0340c00c008085940800c81c0c0c0c0c0c0d0010700c07559000420781c0c0164030124665500c03200e492500d00c5050b1b11180d449880b0301e451544213a01c203100396407090030108034500092000744050200c0d8500702100749805030000d9070240aa0240c004007682d04004a000b00b9803c0040d6200320720040d0085445591f9980030140d00d800c6842051301260b080102e4040300080802144c090b1f0760140c681c682d01028039001d2008c181d000500001469074031a032010814125581d0305803299401c0c424001c20b407880b4400090a08003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 499184469 1250 499183219 499183231
    0x20d0c17010e040b0a1524080907120303151401080114010c02060d0912030f06050108060310050612011407170f07030b062701020601121e0305040815040b 68
    0x2140d0005002464610390980d800c030380c00000002c00e0b0340f5101c002400408814905814103520380c90005540601021700000100c0208500322004454000507101c00b04102c641400b01d800c40342042c4081056500340201c0680207140001d0100b41e42c0392460341400301038016418600741200004186c1d0f0703100900902410030500000038201c0c1050019155031484000248103a401043d189011200c0f0b07403240e042550001c160045080201f4070160082200c420008c201e1400d00101207000d5001d074070f0b19400b0f180017a00510005071060100c0d00180409801d4a41c03041c9010051541e0360024020304070030120f140441040360501e04006064101d489040f2065183c1c52820004610780300128198014141d06000c21301c40c40580000c1d04d18401c514008041d0031f55803281c9030b103025480680c5d0003035030807e8003110007507600c8030b081d000300d010180c000515580b140302c5c1504c101c05c080713100c042c070041c8282045401c4c10b071503c0a050428846402c41c01e19007500c00e040006100c10400303503d400134 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 499185719 1250 499184469 499184507
    0x2100e09180d1407020f011713150216152301090c110c0112111803010b030102070209040311070308040b030f0c0a0207030807020a05150d0b04060e0610030609020d0c 73
    0x81488148243c1c601980c08080e210380100d9801e01801c1e4043c84010400a20750024403285140084032619414020281640c103010140d03416081c4031101c0c8212800121074030703840e204940d80b80e500c4890301c0c1900460f00740902d86880122183c80084440a00b43c040011001c3d0f9603981000c1c0300f40300300ca01400e110000c10500c28405e0345031f48070110f640c0c00401030030f1a0404043c101e10740014041c0c02d082c61180321510700098032903000c500380c01074400d520030124020300c2000350110405090740148000654460004000300e40000d00400850482c4e41080c0c0a03034081d1aa00c1e00c5048168100c1d51090b540040000100950320b105075294a911001e00302c20303036050000e81c41e002582c4442c0e83c04000c10b65a0001125400d654550f810003000b0030005003402103c169140751140c1c10b8003e500340c001141d0521001d0f4025162500540040c1c1e5084da00c07280c2c0c00d54602081003102660340f00e914092654418020580a8480c0020912504405008106e8400724080240200850384480c1030704 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 499186969 1250 499185719 499185737
    0x8030108100b1905131e020d0609150b0703092c06180106050f04030618021c0510050c0c06010f060e120309040507050f030702071a031302100e09180d 66
    0xa80c0c3c0d541804002e40d41c054511440c420454164503009041c641c51007100e003c01078038a41140c00c0603400400703100145003014040951b6400740f84081d0345001c2010416807000c0301c000d21500c0d0a10b005000c0072402403801c0c0b440b040d900d600340350f90b600381806400d200c1c11602014210404240070100c2d0842c4042e102d0b140c694509a01090344e10310180109000c109001441c407000c3e0b04100281d40156400c1f6204210700f071600e10310144d491302c0d181d000300e00a03c040c0c0350503800008243c14440250390441d01401071007000c1440000105001480200f00000038000044000410802c030347c007800c0c205000c80740081c01c148000d0b18805103d14060720540c612840d00c10031f804c021003944c80c1d024003620041480e44070400140d60351b008544440000b200702100300801c141c1d0024091040703a080b0340481d0800e400c0c000c003103c0140710032144416004801c446c0d8400600344080750307564900030b9191482450344000b00240110809071401c0e0416200006070084101c028424004454406d0516180c4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 499188219 1250 499186969 499186999
    0x6030c01080a0c022b02060c0705070b0304151a030c221d0a0605060f040902030a030e0f0402040306021206010507120522060302031b0408120903030708030108100b 72
    0x600030703000780400b1102d078a03580c0c0000524000c01c400d0000090303020001d104401d40c030004800c940d81c000036203401071188202050195040d00c003280d1040340c00201a01c840e80c10b1811024042d4405041140e240c14480600e0f1b0540080340306449440b404045001c80054a26041616080d0038200c40c6100d0034402d58121600c034000780b4503100b4803c00580104905c01503071a00401d410311546061550f0107040d1084c800c000c000d0784514400c41084411740440b502440500c400c40b0040940290140d00044885010074011108205001c0f0003c0c5001441902a0003290036a00950302c02c41d0441d8011800310035280400c2101d82c0d0005083c0b80c42403e00e0710b5500d07001c0c1d50350100b11425043c0107001562120030000c0103002c00101140c80c001c1d4010a0752500f0042c001d6204441a1031003501e80340201c0c0c101c00a4004860850341c8460003400c0542028070086010b51201c20125130510041086800144001016500034000500500701020202c42d4002c1546d40c4044068440c150302c0c001010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 499189469 1250 499188219 499188227
    0xc122a04091a0a2705010605091801050121030809070b0a0e15090a03080a05070203010603030903120804030822060501030506060112020a0f05030702190507290d0902010c0b0106090e06030c01 84
    0x80100f6031401e10500ca10304d400c0080c01003811b90406a0802c82c1e22040004054000c4960b0090520440c020002603907120780b01400f9488040314101061030411000340441c0c031560190f0b801200304400e0b1110156206a01220396120ba6981003b20f00002e1555403a403410410000004141414403460060380320f00103a203415550000030040e0001007059060305110b001135032065940a8000c221103903d030b00b00680b680e031a62000700c540744012405116a188201815801268543c0741c9115a03199201126580b00841520b0345c40340408040300400709406c0c0c00740b98001c500400240c2100d0401100041c1035005680100c4651401002000c09003079002c110b0a03010a110b00e080d40e1240c0b07809004a0800404d40c10b6003105800c4075031001c040c49400301d40329040310401102c4080b004003040e40744141c036010822000c0b5158050040594010494103c2e10910f84140b4000e0048105581d92103850502a003101001401e0540700b400903195841c40a030700001c0403801040b01200240c0020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 499190719 1250 499189469 499189511
    0xa120209090a08040f03290105010305090f010204030804090b0307030c061409100305010e1f050603100b03070e0a050d0209060411130e0402030c122a04091a0a 70
    0x24040d100e6100014500c000a0041400e850741c052012941d0303d0b03440d06034085103400c1d804140c80040c5148190080e0507007034a001042d00c0400da0110105038a080015070040c207000b04112494001c01d8041c1c0c215101c03e1008002841c8034403151526581003149c2c9100f2078162800c003034004d5120342c030207201003443c2284007c01c55007a8580140e0740500510380b00c100e8010040207035045a41a5140d507155074054101c0381c117840e42103207018041e5803280e05401c2c02501482d00042e202c2582c1500f40042d0414800850344000a02120394841d0343d22044092075031b000f15040d0340001c0020f5100d143c9450001c511030020b10089500c41c0d501c0e40c4580000d00c800c00c0c09032070507100c0e40e543e1092401c0210b5503016180d1981c105c0c092525902d036581582c00c2d504200321800c0348680074909614a4500e48000304000030103e0100400406107070b00514807284010b010485060320f06441040b50039515405084e11161041d581180c00b4000900b40d00001c20f03000e003002004c41d05020b60380b06000080c0320f4213 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 499191969 1250 499190719 499190723
    0x6070207170313091a040203270c210c4606020a0201030f020a050a080408070f11090a0b01050306010f111209100203040302010f081f0e10050a12 64
    0x4058800d60321401c05141d80325011651100182c0303041c0014204800307074010f04030000d0300f508070300d800002c00c0c081104070320040320385800b801c80ca0000c0303034102040142403018910041085486810702000054001341400010342907640c83d0640020180d001842021107105040c0d40400c800072004a0300400310100d84107454031625442040003894414400002d800084541404e075200e031910720094980d42c40c24802c0c1d020038140040040742d4007451080321230030b0382c1955989090010f40841160b4803c005002600c803140d0900c04040401c04140c449050075202d9882c8849850a40c01070105a480c02028416280d140c01c00c140c4069030400708032903020f142448c1801460302100b800381da02035483d0050050038455000f001e545054008020120007208450004100011003400c82e902d20907401300a000070781140c0c011a4150156000e035800c400f03c41041c05220310209030b858160700c4664445c41024907244d040c80300c42076207070302c03813034050903050f00c00c8080141401101c4064035001000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 499193219 1250 499191969 499191989
    0xf02101803030e1315150905060a0f1103040803041505190f090e0c071406150d1103030705011a0a03083403051806160605100909061b0206070207 64
    0xc0d4407255941c54202c80c24103c401c14104001381d010100038400d5000e074006c03d1421072401548480580c09464008100c80e002480caa1070418400800c0720640c034007101c0ca0091100f1000f04213250f14051024002903d01040116101c92410004c0300380041c0d1528404140b0038108410f15036a40b2142540c501c401480c2002c0e00e89032420b0354201d900c80c2041d4030800310a0303104018000c03004892070007081460f020300d403c0c6251032a106039243c3c039410180c40d100a00c5002c001c842c02d043c2454103000798000c0c0140101828045034001203401c40d844018221002e0355504420b460300982900103500800e002c0e688119001d0a690300c090451040700d00c1e00341c00c4462030f0440c1105004500201d01c4210f80707111507510211007483d019010341c1181850002629090400258a041100039503034016514206c0081106094960900500b000f0b8107001c02500e1141c0c011851090714011180070920400c000102001ca00c0394901a00e40f00c81c21003011508000d050000c1070fa40001ca890a8400100d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 499194469 1250 499193219 499193237
    0x150303090906030f0307050106030b0105010f1b08120408070213060f030201080406061a070302070b031302040b3114010e0f0a0605150301031101020f120d06030c030f0210180303 78
    0x20303203490140d000b00203030345c40001110820000b041d040300f07040300d03c0340b4920072440e605c1d00010340755200e1200d2940001a40e108401c0342c1c0742d11104075000705d180075400c000e00c0c20715801a10201e03040d044030305130307506c81c0b00040800071401d0011703010780000203034101080414140301d0320f000380b0400f9110117410469101c0c085001c0c070030160b120a00030141d188840e0049030001e10510b13a141c0041405801500500070700003105c0e803051044900c01e449400185988000543c00c200c000d0100051b0503030045803907680e40001c03c0702c81a010125048407024a0094010006620b0540b080603400b80350404141004001e2941c01c5081c15411045200f400d0304686d40340b0007114000d04255000c182d101d2252800a04003031075010083d8182c03802000081e03c02a2141c0041ea524034000240c60000d40c001000710850070503075406404072090208d40403e12655940b03d031521075105400a0724050401010001146820002d00440d2016400c1600c0400e84c80d810114052042d484080c081c440448 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 499195719 1250 499194469 499194481
    0x608062202071112060615070b010605280305090c010c021003050606190c06060611100515030a0501020a0206011505030c03061c12020c220c0203070c060509091503030909 75
    0x1e81010f0094501500d8014100e404c1112155659826210507000d0301001600d042c5145503030b411034900c1a048900702980340d2a29104854a500c204640324aa0b48034999442e0188141d45a01c0c503002810f55002c1482c3c204010a141012040300580741030140c041c00c0c03140141c03580e80450700c4502a50400152650301c01012808922035a18030b440401c407185403500084ea040490589940e00400041109035103408060310000e0140007811007035405a5001c1070000f4040e0002e5501c0002c000c00002202042c00109180203854601116243d4001c42c2c0480701c6981006014010000e841c0d00c1c0d87c100380d203001f0180c00f510016000e0702c624200040040c41d207403600c48141c026681040c99044100841d03040003a800c40700002508018028410203400c07a04d400002001584d51000400994903242c140c144028980f900c06202940002d00500e0049645401c0d80b800806590312142c2d41c0308440d504010202400420102109604144025145e1000400d444412106482095043e01c0310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 499196969 1250 499195719 499195733
    0x5090f16140114030a05010f140609040e033a200d06050907080a11091e120a0b04060513030c0807020415080c0406090b030d1b05060f01060806220207 66
    0x6800da012240400200f44000c485d81039010314101c0e4460050304d40312507103400000b0004089004000e9126206102003555403401d58001c04083c0d040a0450307140c42d0b490354241c130710b51031103190f4081d03401c6074943c2a240e501007040020128240c0c100b81040b89105404808428020038031180e00d0342074010450360401d054540c403c0014240080c01e01c00075151400d801082d80e90308440b000308181c2800d0311061104c8642080c0c0740300500c0242580b4981d40710239511803542030600f640a5000e0071000c20303400c1c0481c0511540d600d5500685010509151034108203080d1540644100c1d4141d1b03000c400c070004640c0c4510845a510707400315010356100702c035000007400380444000244d42c2800c610340005060340000307024062200c0603201405407a5850410758202c4042c4414140c160700003481c090b04242c030600e00401c0c44860b08018094442054551a141800444888144084402c0140016604901e089600c01c41c00c441c407140303602d01c410080d00070b540445002020641c01140c1072003000384c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 499198219 1250 499196969 499196987
    0x906070c140303150f03060601020c040e0316030314070903050a020603040809190501030e060105090a05090a14030714032d0418051f0807290304030305090f161401 72
    0x400d82101d44900307213070341e04e82071042c28402e40c640300f030020003001041414007250300e500c100d605070054006402c00d5414080a407100008403046030104001070b451a040410369401e1085c025540024905c0150405409030300c0050b05c110306004040d02c2c00c20009900041101c24140d05840454680d00d851405014501440c20300a0b4000601140e182d03140007580741c00f5085900c240e8051000e08008018181c9501c000c0c001c4603002668540002c4492110781c0109802900d11011140d90001c99190000305141c100540d40141d0000250882405940203104076004403600c0a1803409110000c680180750b0fa0655075824007012032000180c01000c3d9041e40d00078501480e03910b88a01181030120000c0104441c10805c51044806041031014031204d0b801c2622140b0f0010158236040c04092810303080a1020320342c1060844a482182c1d2602e1400745000368400d49010072030703090071003500f4205284503003400704583c000d5000404a0400c00102401c5a6410100d4820f0a1071b65004a8031084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 499199469 1250 499198219 499198253
    0x905030703290f0714040e09060f0a020a02030d090201050403020603010e04061104060509010f030e0f0a050607030e071404090218070e011e031a100f120c05041809020a06030c1101050906070c 84
    0x47d010100710407400d020036400c0c07245e0f0329038101c0b030301030750b58018000101d000d5041c0000069009000618600b4200d90020a4035801410030a040076525400290700e540260000c1d040000d00c036061000f000440d0164400242151680c0b9007402d0034000014214050400f005040150300c103c101e2150303001e544030000c0c100d1844180d4a01580180c01296102d0900104803924030803040000c0c09280f0911461005518480c0949009454034500d84214685505080d520680d034405c00300050b0354005040d182d602545460f034100e4a031101014020848510170f40e4180100c0407000a02c0f0300c10301307a421442611500f000250103d110501e004410400d6640c0d0350402c410103150031307110b0340100d2060203202640d07407001040184852010b042e01d01820000010800900040c1f040f88000740d001d00007641c503100d0014082070a0f40016200d203d195002c00003181e5070f544860620350380030000e40b450042400007030015040c4030403141e988500c010510f1003041112441d500400980c20601c4007000c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 499200719 1250 499199469 499199489
    0x10c020304143a15090507140102030415090b0d1b03200c010e010207051c050f0301030b0705130b041d010302030a02060304051f1b0807120506010905030703290f071404 74
    0x40c10100b1504010251100282c41602c202480021070b800e50317407043c113230303c0302c0c180c0c041c60400b80f601c0641c9882c0c0030701d000c1c07100c14004042c0010402d00c40a60190490340083d01c0d01107918900c2182d81444c020180e0f501a00b010f0810000100c040c200c2d46046482c0349070300d06030603960008485000c1c010010100024041d500001e0407806005002031007000d04035002e403a10402c500422425202e501c51280510303081e00d024001003000c122505000c1da4072440300e0900c90328103d0018803030694003075035420a2100140209040c40180540754107075091000c5030088801039415a00000d949a9030b580000380308003800000101005000d0068000010110581c20000e60415400c20040c100d10700e01804189030703d01055030658811019180200c94ae900c944043c82e8501c51020082c0100a10030b5040c0101b4003000102c580302003095000035800b50400b01090098040705540c004145100034030001145403d001d4891940083c1f5500071046040c00e02c8900c1008641c0d080314000c0350301940683c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 499201969 1250 499200719 499200743
    0x11030f120412020f0c130902060d06090605031f020a0203041d060103050f070c030f2309031009021305060d122d0c030818010c020304143a 61
    0x10304a081805a4441c285000c00610300240c01c03695074035054249a082c2d449070a1340314890030304180e801c11201c9107101c003043c01115034020031540c3d440502da01440380d03a178805c1005070460134407514000d0b140850240c48210304c0781c8898045d041c0000b08458015034000b0b40480054001c20480d0020502c04100c0ca02e013001c080c51210046108030342043c00b1038203100014401000a0946610a0100e0b0302d407014280c0c40b584040710340f41c1010302c564090105000101c02038852a0f4141105110094240c41d5211180c20030306040805114101506900306680c41006030385400c4000103440c0e500c40c00203240da031040c001030346c1ca2a1480c0c0c01390000410031003400446602212600010b01d0200c22880710061a42107010000d9003916510001054070b120940028441d080041d000585100380b1001c09c512150102c0c211040c10081340f0260b4000241000100d045001000318620226803c0c03c0d01015920441c60707404030103420200d05565031030500f00c1e09000030071920780305400c180c0040c40c2e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 499203219 1250 499201969 499201987
    0x180608070f06110102130b1e18010e0a0e1902040906090218010806130c050d0f2301060509041e0c050901120501030804030f081209030405090a150611030f 68
    0x400caa00b4000c40000030f802c6030303120f5241081402107a2100c40d5008501699618101e4000070a80045080c0d180d02c0c048080410203940e07822000d040c0c0400070f80102d07a02c82d00703c480050000c170032843c43c150003000c004804004020040240562080081c00b80100003030503541e500c0c00906c519001b00b1202d5117005404100c0e0a80799014103c4801c0d80501c03141e9a442c0c990054a4101080701c040d41d020000c19498051184a034000010341056428824204140742003d541902d00110002075116a45e0556455601d0900c0980f0038124141c0908000740d41007080042071341c0f00310000240104c0e1100c1d401d960105c103c0070300400ca03100d403003410031110003030603001040395101c180454005149110039044030b49851003a80e0490ba401a41c8a262900e540d44203c0301c00d00340d810070b540303614060000d6a0b010b18118242481500300c4d03400317160f86506000800405039800380c460703030100340780100081d0600c001192104c151260f9040ca24560081c01003d540396104035084014209008141c2c1c4c10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 499204469 1250 499203219 499203239
    0x10903140304140609030a031b06140a0c05070f1704080f1c091212050708030a0618020304050a0b190e06061e030304142e03050105031618060807 64
    0x16183c5081070803850850190800490f80203410b00203916410803500350001034000e004407090304410040c0010101020385440c411070381900307040324022410b1400c000454500303100d23031621854141001810301940d034807482d103151030222008201006046445480e00c640d601924001e0108404407602002100c1005490b005402c01110351400310034588403815000d071024034103407081210103010300c0c82c803504c80d2060350b41148006004c0c01410494900800e110784000c500c207900c0d80801203422454420341c10003580c10190011a003a02c14018400007030701c04a003076a840c5410140b010807940f64000c00c07001c000c00046000c2011403501414400300c100109120b07218010403108040301c07004030005e01842d00c11110300160301da0004c000074000c01104c0b511544000d40c014102103d039102c40803400c03172021210154145600b810001c04010181d06026090141400f9000303443d1903081c81c107003600903c1c814040c8011000c0c0d001640b070004040e42c1e01400040074000d040b501956950b4003800 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 499205719 1250 499204469 499204477
    0x905060c0a0c05120a260a09150c0f020108180105010f031106040b040b0309120a0c1e0302060109020d140c0307090f060e10030221010504150806070302090109031403 73
    0x2d5800c5941c410015551804441105800c0c080798040d140c6000d4603501c0020440d000c0c0070402806403146140ca8068126801901c0c01c560981c44480056080640048500c1100f1040900b0014901c1003c40058400750400b0240c0b582820103420644038003a40440c0201402415646986020000990040c20815000071070740581c0030311904004442c18005036208030b01400310124010841000a140728800650748004002c0a0391401c2d41804048c80d2142c0c0168805000181d05810007028000615402e0103008107500185a400c845035130041e40350541440303450041d035804950b0745040e50940e00400441c400c58901d46201c2e00c0c0807000c1007030640083e02c014001038001074020510b54180840d480907910180c480e1002404200200104c148100c4054001c05800740040078030345078004220041c410716a548440590704080501c000c441c105480d00c072400c510b8501c10440d0403008511260002442e14001d83d4034221080141c80c00c0807154801070401420362405100b55102002030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 499206969 1250 499205719 499205723
    0x1121805011a120c09040c031202060a110703080118020903061303181211040608011e20030103020d210201090b0a050f16020717030c060708011a0306010905060c0a 72
    0x24000704158106114183c0b40c009505415039002d4518680f50b45851002950303c40e00c9842c821307491945076625a4420754180300c4640159000d0410720111042c031340a00e0000a5640703181c0f9003021142e0314000c041f50010f21070342030468610041c00c8481c0400390101d40400383c028003280c03201d003800c0042031a4840790360f000383d00094040b2420405401c01c0c82d00c81f03003126050802c41c5000015511340c00ca00c4003a50349000c3c0d119541e8407000900c20400c0c0211030b01082100e48810000b4886001c0c90152104001004c60200b1106103034a80340c8500c0303082e2815250182c40c2492400d030245851209004032072643e104021418240040a90f41504072081d2503105004c80049620b5440590301640c20540d407000e00c0c0840b0400094428140300305600f4010f5540c812034903161355404d0342941e2007051591002c5a500300151000b01603108000340340d0410303d9840d00b0701c800d40c03506401180c42c40703914192131240f610000100d10260700c81d545010140000401065581f0114200559a4400c410003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 499208219 1250 499206969 499207001
    0x150f030f021804050604080313060606030515010302030717100504020f03041104020f04090b0a0e0705072102060412020f070e0406050615030604021e0a0201020c060903040b090112180501 82
    0x268400c44150751002c500680e0b10500400340c9884580da80200c03030b000140b0401d007002e51804200080703100c6008250081c642c6171000521810420001007810b0100300b441414913004209102105038031803080c601100d000a0104040d8480301100d6000883c0359200a500038000310b0f000d034841e07400d41c0082d0300891040f41e01d82d134103800d40c0050105034002e0780950340d40400248010032048131550080c0400d40002030007800c42c19106d9020340e41034081a070384d0600043c0040740d48020414581d40100c80b502d90140808400490310900966039a0020b1008085403503100f14100706a0081191030500b111034010b49601c1d54546003000b282c034604131404d4030400d0510011032014106143e400045800e10085145143d54000c14403000c1d61000041c09039813014000c454030f0010110b80070304591a2243d001681d2403000050641c54070501525441850b00200410040407038164101c40340d0240038204502e0f1407915071010402000500c1441808602440c0341c402000360641c0444210051449 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 499209469 1250 499208219 499208239
    0x7030b030d1b0201050304031107170114090d20030a03050402010e010e0108010314030408060a09050705030d09060c08090607060b040e0c210a050a050106080714060d150f030f02 78
    0xc4110b0701c400303080c07030440c0b41210b4040c0b5400241d4496001154014001d05000311201e12026101c4e1034040d080c3c0c05442040e44400320030300316030400c0c0907840b5141078040e21003541e070500644140d150b120000c400c40901c210205820300d5465095840c140c80001d070001d40741c44070b2003107101a0150000300e40490004840010f0044150f00401105100c0070040e950000b450b82035a13112040030300b401d00342d4855840240000241d6200030002c003482600c45803004200e240991420030314107203064100910135005404d0207100b20354059040030490b6898541503001e0126810311942c81d101702002141c002000054403c14014546c006450400d0141c0742000b000020b4540c00f0740b030f44604002c050b070081a01b00381c4281200701142c0707000d00c114a002030310b400c2ca1700742c2e0742c03240351000340d1a049a0594459030100805801800408010403a40140c10704104103180020b106100740c14151400d00c1c0e4404000b0b181fa1004000d44001c0c100c00c1c007544102c2c50300c0f03090005591100d20340407031141150754 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 499210719 1250 499209469 499209493
    0x203060106270b120907081002120108010204030312050c09120a03020d02060105010906030f0e07030b01090509030702010c02010507050c060c0106030b0c040503030a0c0f0602030a06170a050606012607030b03 91
    0x114842c811202403d440500f0404162101280b20502424058841c810349101203490306090001c6070011002c07100c0141d88a00c00700812080810590041c002d0740d1050100b08007194001c2c02c0007844110074640040d940d03641010440c014090b440034690800c240d4152102650b000180e40207046019400b100c090b4070b1052400c90792180240112400190102c1040040c40d000340c024100c0314140030400302d88004844d0100345040090703481540d40710200001044503085070b110b426041000341002c0c624144140e0006040c000d90791100a0401200159040604c1070038010303040c0024000300116134441c2c1440c051800781c40f1a010330f4807406c3d01200821600c40d1200b04aa04079000600034508002001009031501018180705490b503c80605c81d0318000b54951008511824072058001001070500d00c2ea00d550450521858200d41d008802840124800045855201209107001c4000e80319141c21600c0050f03650750001c401041400c05d100416400d60032030307200003100390101d440c0caa880d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 499211969 1250 499210719 499210787
    0x61403010510050a140d080a0801030c0f0303020303040b090a050109051e07080601050423070512010506070c0e0601032403031e08010303080a180c05030c06070c0902160203060106 79
    0x2403141507840b0140b0340c01042245100c01d800c242c0e17000d00501c2041600c0e0241c0711082564080c4100c100003501a000520030403944107010b03406040e081c482c07591010705581e07001c4e6503448094806449601500002085a8001c00640b024594001d0003800b81460300c0c50a01c1d9550344000c2c202030082030480c00448031110000b00d41040310790070401004941d1820041c000280011500c0d004098071111540f60017501a60741140151444c1d601c1c180d07940910241008821070607000300380704241c10805178012650f0003104a00351075a1602000240d01da040042c0c000f846401c509446489640801c2c81c1915450420030040700d009403252440f00c0b0100710004a040611188140400e10440040c00031921901e0065400800c041c030005001c05c03041c04140010f00d04da00c0c116284002c0c04424001d42c2003d00008420607000c0d61030728200216542c860340b01c4c41e0140030310444540d01045480d2444607850f00b041029401130240c2e216540c554000412805d90101d2900c00031901c605092500f68176 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 499213219 1250 499211969 499212001
    0x9050105060723010e0a050f06070305010513111608070b0105030c010507032a0f15050705180a030623011a0a0804020112020a020c03010b030a05150703020d0614030105 74
    0x3010410b0f4510541d03001401245105240c040500e0390358030300d648518040200032603035290740035200034010310170400300040c03604000402c04000c15040400420031502ca900342580005101e0328007043c483d4034034000f800030f4000e1403440790032103145540716814032541200030132401d4007601d41d0031007580e2107405040d81c0e4500c2d0304046000620400c15240424030a000c400c0703001c00000c908a0641c480742103d920400004070003604c000c9003040242c01009143e051f040d0340b12240278400c0c09075145c0a00080c059000d00b211505e900a020718440c2500da4400c074001001d541d110070200101c2d030000c4c00380500c110000f2100c529082d28040042640300d500da8a5035410003070107261034034050140201710342414000d01b0407418417030141c9080c010311a0750300290512031132036030080c500e68846008040c20341d25005400c43c001d800507108072012401c0440e200801c06811050810542c450207800c800900c1094607003103031a45010004104450100010150113004800a00190b00c0724200b00712100c2c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 499214469 1250 499213219 499213223
    0x30c0906050a05130908030c0d050a09050303340216123206090f120705071a0417060f0601081e0a1d2409070605090f03030c010501090501050607 64
    0x12000b904205a2514100382d080103160700ea808104100d0a40d07036816a90010780780c0030078440c000706003200c0c0342525101f032640c444c02c800800e1020000c40d840740c548a200103415001d0101c030b6580c0300d00c100d80d281000c0310240c0910b1003031188070510303014000b904c88131844182041c40c0390001001864a0359000040c0d6415085400b604860810071000c4841680440300c160082d07a1041c10820400c1c01840094800c000c0039000d04141c17000840703501d042940b0043d12522014003805030b800441c8000490000b0b07540e507a4080405481e4030403003620f96001310b41c81000d90b545912040201440d0104126000381e0007801c2e01c00040e122400191110001220380e0a01d202000b004031302582c0f595062136401c4041c80d40c0000707203101040002620380c890300d0003180c40780d40120303883c3e80004500742800e5144224240404001d04048080d00d807100c41520500c0c0030400040741c54245642c401c20308000d82d500080460350f1f00e08034024824041c1400b44128016240361070b000244605000c42240c01150b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 499215719 1250 499214469 499214479
    0x220c05030f0607021c210e060a1806090219060309030f080421180b0915030c181302030f0a0605012102030a06081e1b1008040510020310030c090605 65
    0x9568845d07080840c2d10b0b4180c3c2041048608150700141c1c03244a030a0b01201d0b025000007040512001c5903040c58058080c010049035450b14071581c4403890320051240b000d0382d01110104100c00f01d4000980a21034640044c52045880c0000041c4550154802d040c103a100b1b840356000307564814001e4903107903000c0350301030f00c1108000c0c1004c401c4016008070701126012818080c3d1074400da81c0905101e0481c5030030003550050001030504184c90003190a030124401030b600306145240800d032920003401a030b0b40820840f0b0316113482061581d15500d58030501782d0f600d041191203207000168405064000e5444d100c80a03e007034004070303d0794424044440340019000c1e58140c24079581d12810000d500c001c0507980095510400428080c3701400303503041c01c0c2000403802e020150141d8145003050420100c508003101c8005402c1c0c142d0302c4651215110745041d003004206651603007442c070f003440d4810309251420f920002c00c00a40030000d1a050080e00c0c05400c03c2d100d81911044000110750f030601034290301c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 499216969 1250 499215719 499215733
    0x120b100e01031b1701090309210f0c030803070906031a2d060c2d0706030c03021b0706020c0405090601120c0b040306050a05090c18220c05030f060702 66
    0x8141c40a410041500992000000303075030b910020785044640075490082d4036511044200181548188c2102c01780c00e10146000c2a00d00b5108100c88046520000400c0300140712510010300500e00c22600045400080181d40c03450070240052440d0b031140242404a464081004c040041079095440c1c6032030f02804041480444485070101c000045864082d5840300300c00110154803250702400445808100800f07034051001020341d10340b2400c01502242c600e00000400e20f40d20005030303010840700380d8200040c4c2103403101c10490192068450004401500300d84112400000144030400c41d8032940c2a602801c0010303080006032501918104180d510500040c0828682d642d64141c0341e5104150824046582e090013290540055005880c06a035400402140034005d02445070b00000c2078000e4540d803195200040c0181c02640398060f84101000005410840b403a003040181c510390002d944c10092981c9041209086a4041d45000e8010100088144500011703e0790041c140c03034014000b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 499218219 1250 499216969 499216973
    0xc0e1303030b28031a071407230c04113f151003141605090a0e0414030403260d0515030f03040b070b0a0b040501120b100e0103 56
    0x604000703444183d01010402090a4404803803200030a40755030100340060340b502c0c2d820b1005c2000510500041707060703001c00420007107a031b00c05981103210b03250030315058030750566061442d10722030700e0514070441c0a03141021200785180040c031780c540700c1c070101c0d024006810b000d0b01c403007080e0007509142c107850b10610790340304102644c1e079401440d800302c4494030180c00202d405280d0b60101d01540c00010506540c41d80049030300704000c00d2203640006080c14800c0c601103040c045000000201041c1c200701c580c05440d980e4600c51800c460a00c0802002d110311103840308003203603c210099408481d020703100004250001804000e43d81141d41100f49103103084000d0403c95070206542880841550b000c102e004460159031107454000c016041c5c0403112601c151040c1490721100c1c02074508164002c0c802000101c4190003141c61603688182c0511560f240c00c0b0a07440501410284075038000d0404002040d031000b80d8000d1100300b4018003840109442d0142488400c0401d40554140642e00c0401800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 499219469 1250 499218219 499218221
    0x230f09040906020d0203180c1804152d05100506070b0c070f1a06150a030c050c010501120201080a09200d0204061511030c0c040e0f0106030606030c0e130303 69
    0x9045400b0311005854480d2000041c0100e038000c480d07210000c50000d486080d0010200411320300240e0658098801c104030000c0e0b03403895440107000819184902214022030141d6400412031500380040c0600408495040680314540f4003014100b031500d003400207221040c0004c164000c84002078062450201c00b40c841204c2d0b105d00508050096000300a1000040e2007030b414561b040c1c4c042d12401e010364007100301000c00600f000e400c00d485038036071048004e0391180640407224100707102e040000d411a4212016641401440074008065280000000d102055980303210310540c801d80c3ca2100d541e51303e000640407039211142c0a00440802c5607040c80c4030142c801805a44400105900c507405259400142a143cbc684c05c11101c004115850b4411160401114115406c0e031801440c24109a03001040d42d8146c014500b0b4841c03515002c07203804c00901840702d0200c0c035400300c000b8400240c40b4104500640903901c0100c94242c648d0f88002030114103880014040d4421003443c20360315010b600d04030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 499220719 1250 499219469 499219481
    0x2215050403020307150c0905010806010207140f06030c040f051002060429090a12050c0606060a0908030c0706020c010305090d0c1b061206060e090403050f0d0c230f0904 74
    0x101075200c200181c00114022968442924002030804111b501c403c94000700201aa0b034046810b0025450601c052a030300490b41405540764450200783c544c40d0000000c000c469076030302d42c0d504400000107001c03400126a00a03c1940c5158140c00340c0c440d5110280003820300100c005500680180000c40d001451424641082c903c0e00c0400800c0d908200ea9404000c4000381c0303035110980d000895036010481010060314496415003445400c000b094040c1c151a50700c02410103208000025510181a01803501c81018102c14011240c6420516214a41d0307a9624042c01e400b611500c0800d100646c0300b0b00440f480350030300001500c030340640308005580010362824100d50581303419044592100a40316804001c00c81541c3d15046161401c514004851940e0080c0702003210300151040c0300d440d5a05c117075402a6152a095595503801c40c1811454060440d003610300034101500010b8203a03210412b0300789010200082c8902d4455100d0030103003031084444c8524450760600030b051b007a140981c0710f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 499221969 1250 499220719 499220723
    0x403030e0a150203090c09060a090b130c111006140904030909020c1e010c05040b160b010b09030d020723120303010f03122a050c030a03050322150504 66
    0x9980000c05039480340d40710b060500188022690102c10081408003c005403440c00c1c4007070310301841505100c00810142d031058058a00d00e02c0d116081c0000c1e1b42c444082c11890941c0f85041000b8403100008000c001d0f8881540201e80d501c1080407082000c4154800c210884810f0075510744051164001d003e0032210050083d81409000c510000d48043c0c3c0340028070107101c00c1809406004115405150041c1150001c10440d0f03141c201e0018072180c104080380c0949254006143c2c407074105809104001160740001460007000d6800006c0500b40d00c809480c446d00d0480c2501c89500c09480d0407683c416081c03240b014810161016041c03056043c04c04d01c0400b45018005816580c0d5126446145510170b90251480006401003007080c070041c649004842e201a01e0701c0d029060111044480e0407403203401024034032a020b8400d5081100811000060780c0025051720b0f1101418103010346150400c07183e2541030120108036988071040e94030341103100da41c4000c1c0b0f40b484e10001851070008000080c82 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 499223219 1250 499221969 499221973
    0x206090904030e0118150309080c030f0a140a021c03021b0d020f0601180b120109031d15030c0304140a05010605040c081315110703020319020705090403030e 69
    0x20aa5003a110460300300e104900a80b519600c0302c0e141400145aa011200c0c00b289040b04a0030034084000c0600c6900100c00b040c0c50042081c01003400c05108921a20f032880342039110000b850311484d03100c80c024200c08007141d10351002c22070500f80360fa034040c86900b417000c0c0140c00c4001c0342d624a0b0303003060050a8001c00d030b19005083c4044030f41c40040fa13131910303a0403420360f900c41030f81040c110b035040060200d100c0e0850040e0903594034114000c0050710400c40c5e0780d0380c0d0980b02c12038686d242e240d40400101c10741c4040000e00540040d0704000c0c04031078100100051940805c8860a82410001c44420a0071140408649140e03a02582d000d640d800140c02102c40c1c40d40b441403c2c0d01250104004144c0c9802000001612498882001304488001a0a0303091090301c13000c000d840c80c03259401003e16034100c5000c29075150700883c810010011038400c200b080c01c01150380d200f031681c000041d06402d0031140d05a0218040c140d1f060f41c3e100200d110301c03a8800e47c0c3c00000f4000038813a81244071241200d0341 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 499224469 1250 499223219 499223227
    0xf0b0916021e0a021f02120a050f160b090c0102030f0c0f01110406171302040e0a081c1112040305070302070b030a0e01050a1104060e01050f1303020909030a0e04090206 74
    0x8114400107045020140243e4000c01040c0298541344181d019145951012a560010f1800c8041d4552802c101c1e103074449403010440410190152003202c44000c0d0010206a480000407030340001540b185400713560321880c040000d002d15400150000200070305800450400c2c85504000d100341c0c0c048408a24513005000706400f035a8001d001d00c1111941150105481e203041560041860054503500220342080205020800d1400c50b1903070f482d1601070343c1c0481c008440b4400c161809000e128000d002400c001130440b182014181142c080c0c0307203206c1050100c2540c1d50590f13615809120144c03050410000c02040002c2d0085005260061003401a50205580e4082ea03041a820454000d190641c4035214406400f40a20482d54000754410080020204504069103540100e00aa60512120101410840e0b01810503121000a07150760a07030f03500301c1b103012a08603920510007207025181d044c01040701085e0100175a00703000c140da0340712440803916104010140842840a9800c4a4204 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 499225719 1250 499224469 499224493
    0xe0f24040306051005010216150806010302070c060201020c16080601050f1f0e0a050111100f0b061809072a0303091406040506150d11010306050a0306050603010f0b091602 75
    0x102680d40b01c0c0d07414000e1455004c0c43c1600280c00e12010a000707500f1300c8d1307920406026000500c200c01c6011929880c082c070320781e61401c2c01a8024880d1100151040c11030100000f04558150010940c002011068800440340d5904040c100c100500400d0303940d400040c01803040d0f00b0a0420110002d07001000b2240e5040b145681d414611081105600051941111080f89060000f10390005000070329213019034a0708600c0c1292240a002909502c041e00c41c00340c009005480d41058440000c004c1003680c3d82c65082103d512645c00b2051581e00800e890400202c41c50b000301b820401c10303d410545c01c0031030301015403410000844d017a012002c0c10703600c0440c2808105d1047d0f5030f2020345407941c0100014100742c02c00c0c0745010801000d1480f4510a601c1d04078080c0c035460b03942940c03503a00c1801075201c8654140180c028217150381200c6d41141d00e40c80004103020113a04514020740c0250020090f001043e1f60442c15a00314100c441e411000810200b481c0765030301e040c46c1c1c0310300c4c1c1d9a00c10f8507a1030800c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 499226969 1250 499225719 499225721
    0x1e0212010b03060d0c080705150f0901030c03290415050a14010201140a0914030315060702030109050a03020a0c09060308190e040204080a0c0e0919030903021f0e0f24040306 76
    0x80d0800a290786c40407c0a0003a81484140c00c0580340340b8010b41403c11401d132112001340c0c4920249581095200e400229005000390050004070448810302900c491b0703103540450302030a01203820f910aa0801d98691400c9210b40c240c3d5058490203801e940c02e9a09010100c1c0c154100c80700d80604543d45d40c034460740070400c1c505c8614002c0d4541d100c0827982c1025820255440400d65200c0703850b03900b0403c24402d0801c4501204d208250003900c0d5580c903280c040c000607004040b0070030702900902480c0041003c050f40441ca00e52202e205600c103440040c0c640340014111030384c41c04020840c42c410460b407283c00d2118484e00703c00e105907103004614442800045020798115510080e2540d000300c0d82e28040041c40000c0c20042d010800c5140c0451030980b0089035555041040e03100401d034021414002e0522071f0340301a0107590040c29440c40b030707a0385050b02c070204511214414001031802c818a034191500140e6042080360003081c5441c04031041e40010094071600e06000c0440e00204400000900d807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 499228219 1250 499226969 499226993
    0xc081602070e1905010f08010c14040528060503090f0718020c0f014b1d06090a0c05031912120f02030105030c0d08031501120509011e0212010b03060d 66
    0x88078500c085654a80010740303094071200c2e0324a8080c000c0c112b0954a031094030340103540c2203502c1120701d0a0000c030380044c101c0c070105c2c2d40d684030034010608071404101c03e6008001180540c281108448030760803012407040d203d0007a80280a02d4050441001c1514840390b00a004103082e5402a0380601c404508620b084031702c1c8282050820b900788020b000c030b108210841d41c407103180c0d09051200001000385540e0f0082d260150981c000340c0d0714410050b1030142041c100c14900e010000b03c80b2641000d0050698444010404071505d4609140228503410302007440100d042009a0300400300c00c00d580d030382155999801c0d0700d408115141c00c900742000198014804001903082e0016a00d5052a052600300b10300780c926540100c145041c00400100c0100440703500116029180d0510440b07100100d807070390505440b80025038100f409010b481e01041d13200000129403080e0054200108000381c40c160b00924252101101c10040104043c0440c0401035034090b40c001e246d50354400b500d03500d00c0380800c1c3c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 499229469 1250 499228219 499228229
    0xc090117070207030201120e2104030c0e010906090b0303120711030d241208030712050408030a0b01140d050603030c0307030206070f02161401030609020d0c081602070e190501 77
    0x40003e40c02c0040d96000750306140903950a400031b000014501418680da042c01c04038000d08882c041820001da4a82d50341034602840d44010301c40403080e078500125400078028050035a039140340801c0050044450301c00c011a03804080c2c091070900c5107005071a01c003508024217010038401030129500b66080d0900c010303d440a014000001e0060305100c000c40e0901c0c3c0481714084031442500180811002d0904804010313600c5604155a550351400c1142c00e00c8414030764102c043d0038102440b003041500800340d4461450fa4000f0800250700d000111f40c66440445585045002081522240d60b03054100c203511003c058122403900603110300c1c992030b50b07018030705c141c0050708400140424540c0c065002060450b5610080484046030142d034152100e40f44520512181c0004203091982d0003500004014040f0003421510307500300c4440b010150085084c0840003660400001d6140307103c04c0d8003c12041c01643c0204101400c219114407a4100607022048004240c01c008600807614001c0c00d020300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 499230719 1250 499229469 499229473
    0x140106112803030e06010e180f030711090f040305030604020708070206130510020303010503030a0f110a0b011e030b06010c140a05010b0f040218011d040e011515080c0901170702 78
    0x1c0c046040080441c1c4040701c0b00110343e044240104103002d01201110f41100031708910881140c0309100c8070f0f181400300011501240000320745501031103441048064904026290b1070341d2550b40c40124a103510341150014003080341440825500e06203035015010b090b101d00526460098242c0000325070350001e2814074207035201d58506005034145680c0208004541d80021810340d41010f0010381c03a400380521001c10495039082c0492000c2c0300f4220340701c2641d400e40c191903103d206410070616001e824040c02d2501500f43c1490045841c1e884802004c82c2e80000352007040c1d80f9031500445000d0720b01d0303105550f2406403902660321074000344803650040d4440c8000080603800d4000340700081070f84116a40c8214814002007408503100b400c1004510400d203050303038440c10304007110301c0c20084400420341c010303103401e8a00d0410401540080b02e460810146402107d9031445001c4050b61072410810001d640200800d0020040001800386003205040405811450b00580c044080b01144c03410016 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 499231969 1250 499230719 499230793
    0x30306012618120f1e030403020c19030219080d09081504050a020a0e0a050109112d0d1e020a0507061107080a05030f0a0b0109180f1503120314010611 66
    0x513111803c80011702d00f0030306001d00f58502600c001e0b4642c002042240e000b10302d08000484078042d912005006981e000305450701c00c02a59041c29107a5885014103160352299101343c00310280620361480c02c8a85640041500001d440000e00e0506000380045440e4424994104016a180704000d07010b041c8035004007c00d40340c011484020342d003040e0b11111203945021144030340140144121aa9080074008610542d14012003a0b0000b03100204608080000071500102c0c00b070301c541244960320b8080707121142d260080c081000880c8114140140424420007500f0001a0b0a41000320011054400141401c44035124400207602c1000d01c01300049000041040420b45074034000c0d00600c0c8030000300410b2440c180081c021402600440c003141425080c2c5002d0b410003502310860300405404240301d214160178940c24081c3d09070008490000c569010410800d11900c181051049490f1941e51a079180917000e99030f0045280d41c546582c01851160104885210b891039228035003121040c0031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 499233219 1250 499231969 499231987
    0xa020a1115040e090c040c030c034506060e010305010518070512011b0c0c06020105091504140a0503040504060905060a0501030e03040305070602030306012618120f 72
    0xc611004160248036031003404845180035a4103064400761005207001451945424080c0e43c03030310f0a10790344030358814101100d8050751541600004600c01094405215840c9000d0100b0303209102c48043c0340c801c407010382c1185502461000518420341c50304d025250b01040b9521540d055070450f8201c5040003010000400c00c00201740704650380452008000d040140941142c0350f02d07045180b01c0c40d48510300e40d00109202c2c200c29440a40059002842410075040f08e42d0040d2010208000130348107850031400c0000c40e94018000d092050a1100103400c0080d40741d49507841003500a801546c0c502c04040684003081020041d496220303010707100853d120b91818041000ba1080c54000c0c883c5107007040b00b031112a444980c0a4001d59000742404a15080d40f581e40c6131850149910241080c881c00ca03000814070340201c001d5000700003c0e61464410b041300d20b51903140203041d007401c0002c00b4000e0006130015019250701c07074446030b0300401d4881030400704006512982029001501a0800060b40c2c1c034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 499234469 1250 499233219 499233233
    0x17070e010819080903070e040c0303111504061a0907031b110303040204020a0302070206030a09030e0f030a11010504170c0f0a0305150603120d020304032703260a020a 73
    0x8010101c01c00244801034141040e480002c194040050401e24007142e55003003039401380020f03005403900c207078040c289140a0070310044111240c441038001c00c140d008140803400010640d520700000715003c0011503216a41e40ea80240b1034032109850f000401210000d659a8100081d8001c1c802a0380201b504010f503040d801f980e8604400c0740080c4002c0c845110904540402540e5104c1d8041700c006807500079160b42a00a0b202d0b0301f100a60101c000020860304072a01d9000d0000b1764025a1000f01b031843c03903002e00248101c8101c005a1560101030810001001c1071480002c180061420390700341955184030050301c440c00c800120080d0460307009260f25040031070f25041e00c2c42080701c44002c00e5246440b042e07215000c0340241c007500e540010005080b0344007017065507001400f201481d6540c42041d034215000b0340060390101d00103680740f184102c2d1418022584034140c45688207003003841b0b03d03603903445200418140c55060007100404010441510a60180c000c254140e000791880b40324a00d0300074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 499235719 1250 499234469 499234471
    0x8030a1407020601050a0b0315030106031401060b03150f01030e190314311a03061801031e02040905011407111609090819030f0b010306050f091017070e 67
    0x3800b15480400100141c2d540c0561142c1101c407071203802c0e607483e15407a80d440b40001d074980115402d9800c0090000c2000003821820000008480007041480d0b114840201c1a00c019501005d02881d12400f800380d0740740c0050302c0402c4203014100000c482448500076402d10030a001d501d9648000e40014030289034000d0b0843c054142e0500d4210b05e00885a184901c0d145540311007002e0420b6082040c0941d00c00c02d0700c014000e40300451003808030010303540c0001c1d81035008603040e90164400b40312a14421004d803c521341030740d9104031030035864084410104000030000740300f40da0007a06c0f4494080403440030300c54940d03400d07884820303905685801500600039000a03400700129910043d6141021040d04403640d0076210204400300345c0030141e080c01d0201e130042d0340750300e055140006400904150507600c0760010140241041c4000d02c0650015000c407405407041c2030300702401d0f581818003460302c6481c4561000420300b00304d6007140c46812040001000605c42155544602002e0001d0380c00c08041d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 499236969 1250 499235719 499235731
    0x14040c051c06181506030e0a06020706050703060803130b031005130506040c0f0c151d0105010906050406030c09021b06090a021e13050a0204050324101d040f08030a14 73
    0x2400485220312002c10044c400f44140000c250fa50b228a2080400c140244001c1a420450564071251182407010080c00c040c1d40d44000b00f45481000205080d010044c1c0e1154204411040392443c030300709241101e80d10050005c0c114400c0d06501080c180d50300c000408010070300007000529480d1a83c240701c02c883c40d540d191814030804003c0900c189a02c86100e030006540030190003203400d4214074032000303030004422092030700c402002c1d0703c449044150301c5181294a9070000344040366488091104442c2d4901010b484098640000e01000e6010b8008044003005003c40c000414414461582000f40541e80070110340c00410119080d0303d803840d02d03000410110043c003100b200c03d03280001e4007484203000782c0104540f00c030b00081c2d0b612855130545e03004000c00b0301922803849840500d01003038000210080240308a200c00301e5190000c4400c0b040075510302e40d008ea0410481e0320395144040c1c00085c41180c84004a910703c00001303140d000070303600403c081c550105d0307083c40d00241945840320041c42 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 499238219 1250 499236969 499236971
    0x30607030b40050f01090903030b060c06100f080d030207050a0b0405100501090506060d05100503062d090a1b1809110102010903020c0d0311070e011a0414040c051c0618 74
    0x14040134204021146044904400b40014070482c07520b41600039060007031006910240100d0f420503102c00102e0f4507449401048403e0160390380301c0190010305501402141407590090b5100122540a40c0c01030a0160160040700c51810383c9907240580c244088071b01b00c459801c180c0103044100064060a4050080c000342807205181c280042000b6000e101c0f40c28081a403500040b0341c00244100014000d0320000c2c05a6106103881c14458614601045400301d040b0710815900302c0150030f41542b0350144001c4000b81040b00000e44800d03a5064250a20018413990080005940c062207504908500c42c02030b00820072522034140150340070340c0740808a0542e41402c61040020ba03000c41c00701c400d070004a40d464150f501a080440b40400d484200d90060704c075940021032030410140380903040341d1050541c980003045000c42800fa5003d58420034091285040080c100341c46c068021468202ca240340090605012591180c003d80c15800185841907850348284007403034240c161180e2400e03400702c2c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 499239469 1250 499238219 499238221
    0x203010f0807170307061d06070201020a020d0e0904030c02180106030506040c030b0d060f06090204080a02121501181b0e04051608060d024902030607030b4005 70
    0x9483c41d20ba124022004010994a50790380b4081c0c004030714100d51101105085690900d030204001c0e000707501068101002d80b051024640c0180d20640a445010034064503264a648844d40c050f11520141c14040f68007003211000d2001c2c400d0071803081070003481d0a680100e1a800c00d031003803000300d0354101c008004041c1025415910350301c130075154201c41075000740c1c00151b01c000b445894000b01a00e41080d10b509000241c00560728100140c50342440b402103400001d800c0e20320a00f81d546003d15090082d24075202e50040200011941c8255642408018080303088920340d0f4105900b4040c0c0108800401c02e80c10060125041c0780c440c541d804075400c020320f40712142043c0302802464004000ba44500401044501103480d181c0030000480c00340c01c440400c00058142c04031006481c0c1c03403001c546080709150031842e03241d6410f115242c1500078001c1e01541d05d81c04130482c0680f1a01c03541c990410f03000380d01010864603510321050740c0300760042d01d03000c104000900703018418a82c8981050150400c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 499240719 1250 499239469 499239509
    0xe030d03060f0f030b070804020316030b0a11040f0e04030c140a060f0e0709020c03040e0106080405060709061409031e100515031c091d010303020d0c0c06030b03100203010f0807 78
    0x25520302e4000846c2c0c1030401c01940d461000030310340519804250f00b00e41200000000700901c0008603030080c00b502e503081c02607140c4500c540405000c0c500c0b4841a07000310382004c107c02c480c2031040640290091400c2e07060000e0f140c50b80441e0520349005107900e41d0004402030140034051280c8a200c06510409201da41540000c090b5038003aa805400e819039400140c0d003140e14000c000319801070003850310003c495a510400505020011101070310309000da9000a51100d111751100400e030b030700c41d888001d10741c1e0544403034011903000300032040d4040c0308051404642810b480300c8081c02c86280300081074031b080c008901e1002e485e4003404e05183c5071082d0703900d04410354010403003880320f001401c030f401c0078004030314403c03034814007113600c0070341c42c03044680650050f2410180c456068034001d4003241c6641088042c1100d480388035280281014051400c14400c892081d00a000c56001c0101110b4403070407101800300c100d90081c2e2000c00e00002080080000b00801c1c442d040c010110a4800f4865203100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 499241969 1250 499240719 499240733
    0xc1713170a03140c1f150602010e03040e0a0906110a020f06010b030a090c0f09060302010e0105030f1b0403241812080622060501031a0d0605070e030d03060f0f03 71
    0x84100f00d032441d81c0100d0075400705041041a803020303040c490354401c1c0000c0004210001013000d642a2844883c680a002c035120b07005000b500c400c002058004c0d440d040c0780540c1c00c291000080c20300c2150a442c1c4440d00f020800d01c1c010417001c444283c0030180d4611180001a2a0216016064000d0f4004500401041d0009016250300c420840700210f80c4444a16014000004c03d4210303141610f4118000b06100d503007a881101528400e884d1803005001960046d202400708442400301c50480c480041e0142c9404544081f500f040d41110505150b181d0351101c0c00b480c400d9090084810780b4501c10381e10070305c080c00f9103a4070f282210b5020001405070740300d030040340c115414260244080000230651607121400558002d880341000480c00d6003c80c034810780130300b245200b1180064101400001211154010b100d0711600080642c445142d01c1c0e540ca502908005107620240180c0d006c0401680e00e09202e0101510313240d039400545039081080500066805400c039820315140494288000744103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 499243219 1250 499241969 499241987
    0xa080306040c1b050c0a0605040b0915270a121709010215180c010504050f090a15030803100e0c0412140106061d06070b070c1713170a03 60
    0x3641d0100c0c1d01d000000e01550b4480341011104034000f41007410b0300074000d01082c507484a00040316114039681d60f96804070303118021405400100f5008015220b014a0b103c8a4001079800155100341040c01d0044090300403440090513600c00084280c3d00141403901c0d51000d40a46640000141c490035540c0300d080c00b10340301c4261802982c0d000908402141e0081041d00306102190914006502d01341c450070300340c010003545061840c45444409800d0f513004000351015240e02070f040306026100c410800c42c88501c05818582140c0c0d45865442080e440c13071070010061402040340741e80d242454805030f00c51410950000e120100031400340304020803c101102d08840c94020888108009030401c1e010081541c0c0000d00d1070341c80d0450020f6a15081000a0901e40261034040c0d6102c0b002000c0c004c061060034002002007071750b800058201d0340900f0140028a0080c0c002e030b44010744000c5000003079440a15294080250303028108483c07174121a00789002d02640c4040c0004403d156005010010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 499244469 1250 499243219 499243231
    0x302120f0906071703041104050721110d090302160b070f0b040302010b0409152706110c0a1a150a03030806131802190303080a020a12020c060f0105030a0803 69
    0x14001a8030040c00004900807011960700b03034190b40c4c5c03801d180c54100007040c07014465038050390a12000449160140159148000300002260001d001e90013617040107108850f078014500d40140070340340c00701e9654852403c0d40c2d0712a4004009582c0000b00305e20040f170056102a011840400000c8005581c00369109211a13000e003800d080341d21145010303030140506940c1590442d2904064106118081c140701c1c00041c08075108001d80f548041c40f01d4944481c2800c5206510002c0720213500069107540404032850000e6002802d0020f200303880307800c01074000340a80d0800c0c0030081c0440594281c2c16540d40011080051a6503000f0b080041429050b681c80040d0902c22140b000031159200c090b15022902d4041d1010008405050382c0700f1146819041c00707a0081c2c3c05c003545002021107065014040d00d0b0542c56840241c1e580d190004040d40c0186005070420201c243d04e040156154005071440400b0440074003090b14000c800c01030807040c141c0c0014400c2e80400707105808030754180c1c21250024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 499245719 1250 499244469 499244479
    0x807050405010f0b0a180306020d050f0106020706021e0a0b16090506030915040501022a010b060f1e0f0705011d160e060f03060103290622110a05070302120f09 70
    0xb017008684415260b03447d601c00b5082030700010b034480c01c468850340900e10803e0700083d0000943d80700c180480e558031580c09900090b80c40107800300d612050700d12144074041401000c848400010784d03100103200307000741d40d8814903030340310540c0034105508600303030390041e200c00d40c0c9060840c6401c140f901c3e0f4480c000080120051600300114082c0032080d01110115000c800303061101140340b031440b01e502021703100a050b595282501c590824a00f28084490b101c1c0d4250b1620b04121000e00c442c50b01740220100c541c1a02d00801c21a0200d512200c0070b03028241c00340000240c43c042500390446a40340740d00c00f4100c0d640040074403065008446220348241c13001e8480701042a522000032407420043d20303107182d9142c840d4900010410601489030890340200d05110907080c1c0b10311a03440011801a140d89500c005400c02c2c074107165592546241b1008003404011030744e42103098004a20b54042501000082e00004000c010705804018050329000f50102d054646440401000c1e5a400303940880c0d40311f0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 499246969 1250 499245719 499245737
    0x7031a01142a0d1b020609090a0204050405040f0506070f2a08040902030910061a16200109080a0804090b01050c03160309050301020c1002030a150807050405010f0b0a 73
    0x1000450140014546508070000100700c0d07851525640e003d0708020103001070002c811035100b003850030310440c01181d4050002d03401e00d00e030a020080c182c40b0013800b1004203513090000059942d51070145500850080e0303006120289075090180c00c0401c020511700070b20003514449400d2a90003c000c0702112054032641c01110041d0311050580d46105002034907001c404100494840140c1c1c0c02135000d80341ca1001c407800d90320022440ca05485d403610075100c0020840120030051320b0b50340003d250b8030781c070150701d0211000b41c0d83d24000303008403a25410305071052244050495503004401c0700c0141100200034441440c00b50340340003042c822406002c0e10f868480d01d040d80e403640100c0540b006218880196500c03003101c0b401480c80100c82280560003d04600c0c00040c0358281882284d906803181002342c104a03000303080e0039002e980050055250b466139000c001c0c0c0c1480c3e07a04421000380c20302c400900245d43c0b030101003001303460381070300309442d07110b113000f802c100d40112802181c0800d1000d00307007080c2d5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 499248219 1250 499246969 499246987
    0x5090103060305070b0c010605091009020306060d0f0b0a062a080715020c010621030c020a0909030206040510060806070e2b150209030a15090206040b0307031a0114 72
    0x500300742d80c0001c140348a00304000c5611210100a000502640e00003001025510810000d451409460601c0c6440c00d50b941400000d046800855010030301600c0b10f89020f00c103040d18400c484141000264103076565084181d5407404400d42d1008100340c2c0740071048a41d4141c1d480c0301c0c01348902c40b0b820b40d1003115000c02081001d24401d40300c5990700505546051400940c0ca00d010394045040782006503e800000308580144410704c0c080820a07c10900c03c04c41d19560640e0349699031350050361b110320f042400145020243c01920106846940585007031304051078003500e440050112409024245802031015090004001b90700005524298541300c0c6510040b5400f800100e2071244082d1124038401d403211b081c0d2100c070103158800c468000001340404201c1c0200d0060480296041c0c02400200300825001401c03c103410f00c002000040b0424140d00041055010740e02140c800d000200400c1001b42c1c2601c5641c58001e6202035600800c5441d000003441003a1030054040d035140c020800c01e0f0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 499249469 1250 499248219 499248221
    0x80a030f1409300a0b01060531080709020405090606071101120e03030112030f02070605090f0112150e1008150403020a0c14030d090b070f020315071206050105120705090103 76
    0x542d05022030b00d80021142c0e0155032540314032009a0940d06000c0c05c00000550a01c100700700c0710540881080088407160880c0784c16810007052000c00d00068008801086160301070240c60000e0820701c40040c0d4882c6000140b05190000902e051320400b400c0c09680d000c901c408002c60306046c400d1030900c80c000c2c40035083c0d100400c07441ca50b5090764403000c4000316440c40c142050a106901030b8603071b4a40c02e4405030007280c1e200d01500542c0c000440510400107141400c3c9154130800700f050408240402c00c0b42c40c103500b03c07108007408028115840c41e041000c140b1183c0c0254204884650109440f030910b80c01e65501c43d2444d03007401c0d403403141500103800d1620900c5110b00240d801201c5c40402a96001e64102000d49184064800e000310828005068002d071600d6003161040140d031414012191038800e030b001c5030000240c1e01070241c40d0f51000f0003606000014820329140c2c69812621000d060b0610442c0d400ba045036040c0b110401102094883e00c8058650000c09450000d90350912203004070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 499250719 1250 499249469 499249519
    0x1b1e091306090b0901090228050c010504050c2107050607020d050f01060503010510030b0f090f03040e160c03020606090405070b04230f0607060c0302090604080a030f1409 75
    0xe5601864080041035001d60398001080140c011030304c501260742c0381c0c00c4220403032042c2584002d130003010309401d0700c1c0c55440d0b03e100103c2e9101402c104e802c20f0a0103aa2500391403080700d0417510b50f0000105001c2d40d02d0b0989a40344510101035600020582a082d01c030b42d1130b110380c043c1030300c00d8001061550441d5140707640c905490787d002c81a15019002e0b009414003822150050300c4c803d5007418009030680701c1121403401200d810503010b41940e160b03181030600c03422000c0d0a01c1c82074020284c0400030140e00b04002c2c00103016000307e5054a150a960140b500c6060720319800c00c000200c03020030003081c1e001a4451300800100d402000907152803800d1442d08a466100d1a5401008200007401054000b1107d001c240007048090404910b1010082c1000050407085c0c2e0128041c0070000c00320345a40c1c808915181e06080040c505250705002403d1504207600001e590340c0b00185140426030302c6001020b0b042203030b0500071120415200d020003580a0195403c1c00f408481c0013074980320100f41100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 499251969 1250 499250719 499250749
    0x411030c10030e0601170a111801060f1103031e180f01151409160512011203030e0c06040909020f0a0f050315070e09060d0b0f1b1e09 59
    0x49001d102a10009005400702d0826442280a40000000c1030071043d00d0703c81c644444280507290405c0d0a0713462602e8141c051b82d103290000c1010040c14112034041c4802c0d030203000c1c2515000386180800000400301c1c00d0f1015080e9564005000340b002903008090b801c24901d5910030b018141740d40e10a050700340c441900b05000c1382e6100f0500444e81c12072065210030201c521140d4000300f41511091000e01c50013804d0748298002c4070b40400150002034502c91502c1c0f032049441d1103444e080c540000c40303842600a801c0390601c82e00529461081680500c00d88004800701400f134010b030b014036000903c690046120300170b0310545415010f02159503030680d644402000401c1c158005e81c58441c6c05400050701d00545002e0300c24050303003c48056501ca40d0034031405d415540c84410403a018244914560060101c503000620702e0000f000240304404540c2c480c900c404440314580c40e01c6000075031030205d00c1c210070480402c10050801c158840043c1c00c00c01d20003200203da5030b90700070070200f0407600c515680 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 499253219 1250 499251969 499251979
    0x1030b15040c0503060f040219031503121e02010b010804170c06090105010306110708030c07081b060a0c110a0623100e151e0102101805070803040605030411030c 71
    0x2d040c1d0040080c50180c501540d01c501d200006205110480c480c20080ea401d040d07440400c1e0701e078188a42c10003042000a40b983d103c10b980c2e2075545802c422a030b00c8182000c10b001c12030b604400c99408265413003100b850301c02030002c040880300203008004003902c00b820000942d808642804001030456171402d444c4c404880742880d2552031107000f0300e420302040360180d040505400400d610314080d5483c00390400b080900c1c5480e00c900360080303035000c0d400858051900b80018540c15074032110040d241403100000c0c105910749960010201c550070460301051102d501092120321a0001c0d40c001413aa11000014800051180d2010308203400300410540c0400d10301040002030b040c1c003103401101e42c0d5034038100b44c46d114280582e9042c542c03401d804c0d8010285600b1014200b842078020003120300107005850304580b01401c0b5805580c40c141c245106041c034490a5810001c0822003030008102d0b22010b14201410944003d0503440081c101a209007003807120b40c04984e0f010b010950f20b880e40108 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 499254469 1250 499253219 499253231
    0x3041101210e120307080703020c0a080313060e1911060706060f030c140d0f0f02060a051c0e0a0b090f3309190f020a030b101d01030b1504 61
    0x8080000e4501c00c1e2100b0901d01480011101041100d002c0c1c03809030f001902c0e110110b594844085009400201d102d00281c82440d5200b804a10008000c600030511210103284480349800c1c68019211442255507690740400c0802c17000e40030400b4856141d030382c070500c3c000d41c22641500090007030180704070140540e40780c40c02c000741e0509103007c1d0400f2030344502071441120340d459407074035144010300351450340000d110540c00c0300041c04401801c1056200e201d070f50b406204250045000c60300000c08031800318a00080c46050b0b401540c00e02c41d049405100240f1200340501d03840c94071492030f140000c082c0302c400c00c04200e0a59003070203415112000c0a0071101c05501141c00004e0f031100400c1c00c5528074181441100d6a44909001c9a1046c04684010809000310400c0c05a82d1002c440040e40d40000c00401030300103a60342c0108100440c020354810800c2e0502040c94100b020345980314981203206401c0320720b042c0403640021411a60850203804986d51a4401d2401607007002d064568014074040c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 499255719 1250 499254469 499254527
    0x3020906330406021204081c050c07060201050703061211010e0a08061e090c0a15050d020f0406031b0e090406020904050a0903090f1d06041d0c09060a030803041101 72
    0x503008030f8001c1d90840d10385005040d6100b02910440c06152101e8001c0110362654849075840a161400c842c684135240850326030304241441c40c5038010100607511203042c059002c0e0b140c01128003030503664443c0300e408e0000c4e9650310b0000e2080340b2101c1c107000640380c0c81000d60303842d840018020b1084100f6101c43c1d00e4603c0e00200841c1c00c0c140f88a8400d01c5200200f0002e080c0010840711400c800307403101b2001030030603d690200c40075000301201080020804070034261981e0014000c43c085e080e401c00e440c1c90a2500180aa80f142e4901c40004503001c0280321440340d0000c07a000250340b080d608480c00b81c845060050180c829000c42c10b400904042c00d0100544030f43c7d001c1c3d079a50780a5540c041c038040e03c403601040502c142e0300c0762100e00a4102807000a0300d19003d003050700320000a00c000340c1c104070035030500380900740318280040c03a80281c040c688280c10680e0b8074030f0340190111540402c160460b61050034034000508041c01da03070320210030080141d0007950020f1400d0170001d005112003d00d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 499256969 1250 499255719 499255819
    0x1a0117031206030a39061209060209040c0c060c17070f020a0204020406081603020a0210270b150402040609031b0e01080d020106050402030f040f030e060d0515010903020906 76
    0x1321011402e81ca14041840c241100d00082c400c044e40c1e06d541d950310b00201c0611102000c2c0c180c58030705030383c042e508001c13101007607551b03100e142e8405a90b82c88407440f1940c17505001e02141d0079000aa006e000c002c00303010105603100039440760304c9849400d254400e641e002c2c00c00ca01d400c182c203000a400ca48000b6000c9502c0d1307002060f641c45042d0550309001a0155400101d051340a07098004000d07922920f880b9941703a00c290010340107140f044950045403010446030000d540702d10b01042c7c40d02d9507a401400103102003d40e006041d8401a5000d500d418945007006280c2441884058950007100314005150115005000001c00242783c80315201d5868100040e20b44000416210140d840c04c0380004d1107040c40d0003920b00c0740fa04142911110b030780e02e8544118001c0d8140c0b00700d00300404504034050a58441001d0006002005000070352031608244a140318041249541c2c10700600c200c0800042c0e43d844002c580c083c030b09503440d803002c054242d003129410310402100020070008203103103400e0303580c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 499258219 1250 499256969 499257023
    0x231501091205120d0e010f0c090909080706050403050318010c08061e09010b0406030e0a0c031103071d06120f0d050c2a0f15090f0112091a0117031206030a 68
    0x85c1a00070408401c000030800f04458484280c000400c1c8000000c1041030266403141d4003103400780e020503180c2125990b070b0a00303e500880e022404590044280000030701031101e80741100c0d00580007004542180c41b00034002c007000405540c400c1c140e0740101030021049807107070403603000044d20020155031903400445640d00240900785c0028900880c02c400c1c03401c0041c0009010b50003c60b042d0495040d0b44660010301c00301110103416204031000018026484600700c0f610381020411480755040990400c0356841da1113070b04480990100616080d42500070900705105501c0303003056561460803000444c10b01090305060f03218030203a000e41240300c8803d03c4106190920031909501401d401c00704018059a91800c0c41008241c1888010907605142200051056050521803a80c0c0d0044000f58152420301d00d040b94820a8800344180090383c110303032240900300d103035500100e4001e90038105683e4041e07068007410203140000030422544040c056610340680024070949000110f40004440d15a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 499259469 1250 499258219 499258241
    0x91d0109050d27180608030a050c1e0d030f060b130305070e0c161109041101030c05090f012a03020607090503070e0103030309060b04231501091205120d 67
    0x503400e08240561100381d100c40070340000b0345466141906113480741c100074503000d0200906175641c41000c900c03010300708094003400041e40d5607155160803886903d07003000344806490600201209002903d800c0114174840303994028600051581140b08040015284d80d40c00071524a00000322002450248a680416240a082291209955032000c142d50a41c1140c1c0d06a0380c200510004c0b10010010382c0030b690b5240108607041c800300510000524416042c0c4003143d120780c032628242815601401058114070442c184541000004008620a5404242958100008144110b4400842045101032180741c1040c40c06454018030780a990b42700e060b256540403504480b070000300c620340002d020f030680f661500040401d928558068010780300306441111182d8458100140a840300d05c00d01c20609441d890140000c440010804040032010340501804c410030111031001c1d0760440040c1c411544403886424001c040d604120f0305100404482c0700c54034000099200201201d0740000780340d69 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 499260719 1250 499259469 499259477
    0x6270209010f05090a24110a02010507080715020d0b100212160c03050d02010203040c290a02010e0d020601050118080303060f030a050f0705090901051506220b0406090e10091d0109050d 81
    0x85040e1f00103594080307040740280060130400c502d01c0007441800c0540b0159104414405540c0013120394001a0717007140c60320215440d0f5130001c040462511300c65a400201d03050020305070195070a50581d0141c822000080b04e4544c11808000400c4001031840005682000688034841402a0024040d500c01d8a040c2d903000480fa60204960000006258400c00d0003d050050145a10790f000300743c0e0400b0300d4480641d50b0f01c055030f01c1352403001d10038001c0081d01540544030a40c1050005861582d103204075070f281c504007100a000400002003100c3c0c101d441100c41c0c0034040c02d580006840c10000d07040040c489c0c010071042c01c412840000744d1790140c500c100e45540c1d07103948001d2a603003218000c0f1400d07100075a501008494a04101004040410008402c440201c888254040082a50790301038400140f0005082041650210f141400380040720443c0c0d030349081039030b0707036101e10b044501039000481da40c1c2d4205038501141d4503c2c0601505c070a03000b8003c03c203050405545401e509200e40c0081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 499261969 1250 499260719 499260737
    0x70804171219140d06080115080c09090309180a0c0c111203191e02030f04030809010917011d01180311010f06270209010f05090a24 58
    0x840340407440c0051166544006400c2074a55002ca0401c8400c1c41107410601103020950114154500700601d00090600c0c00400c01e180b410000303508442c82016a48160300407440107000656004c10341d4000280c040703070540c041c0d48550040320300318409c1042d410b910510054100e078080e44a4000f46208071441203081103408091001034840f03601010700100082c080e152600c0d402d20b44844221249084038ac2141d0602440746810b40c008089860604041804400d0308541c100d0540b80701c08254007207202071801c101304140311071424045c03408010b084140101d441882039104140f508020101422641901c1540e6000d0a0007007a507001e40100d150a13440b2000343c40304050084080050f80c0f190250104000ca480031114103000c00c1c420b4803595210715080c1c03410b41560190308080e10307400d011510420014103025400f44078200f0710f041120300500c0040f116130b8000004604520f41800d09950790950703100010a45c1680741c04c0341c86500204054443c04c0c8007024902c514440240d00d5424074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 499263219 1250 499261969 499262009
    0x408070608130201080f0a0e1605150910051803070311090a060f1703070209041a01080a03120b01030b03060a023106140d11072109150203070602070804 67
    0x42c140c11030041d01042954011655030320170b180400381e0080c1c000348005081050703170303180c0c50030b202145d5155501c8a01454041c0101e1504011001030701070303054040c0713160034240c00c04a61741d90079184230130080c030802085210110900000c4044000b100030180c500f11903c80c0b812030840c8003d842424020005000056a481c1203032003040203440710700442d542ca0500e80b0b0000d505094000d2103802440c00140201c6006807280c01b2001d01071031203200c5e58491100062040c04140c50140d0003100640d200c00003401c00f285d009180c00c05110b000d0341d00070554040c200010b0b80680710254041d0b4242c03040c0c02c06c02120502da80c2c041d004403948a68102c1149110f1442d8444005184107c10118075210004012a6000380841c620591042503a5420309454019042c05c88040341d6208407148030000b43c0001700400c080206c2c600f2030041c0d441c03400911000200800100e840d0090106200d81c048081460030b000300251580ba5900c14020740d5101d28901e80141e0f950000e00c00c081c68141c0704440720394 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 499264469 1250 499263219 499263241
    0x1b050309070e190908090306071803030804020a03050f060709080109021804170a09080c040c020606090703060b0f0c0f0309010c081c02030f1510020a0201031a060408070608 76
    0x101641800c40104191410180e40810300e1402500e0000341c1030040050700040d001e40e01500b0030380b80c064280a6150001d250500d800d02c0e50050480007008500010640220280d40100c41a01e8040c64040320503500d0788003040d107880743c41d0005015845045014014180001082441a0090350740c0c600da51f55a1303005242030300c2d481d1000075031040c41a0f0409031808038035545039038054000c2d01840d54049900054100d030354004104600090300c0307824180310002080041603410070082c1c608001907000c41200a49404014185034891000507001c11041c038401e81040e405080200c041c150f45011140000070650301981004980380550503000007188004015106a404182c480701100c0000380c0e2003504170b40c8103001e401e202e012040d03500d9400c0a518409140308203e11481c001350340c1030403200d6103603907480040c555208060815885c40c00650103d031000e0040e50a0801140d2101d01d41c1c90b612032081000d00140e0048030100f00000d00441c00600e00040b0703006034948002c6502c0f00e441c845 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 499265719 1250 499264469 499264471
    0x4080304020f0f030d32030403091d070302220906050108180606010c03020a0605040807021c020f0103150e090a150c08070f18030308160206060f04020307110609011b0503 75
    0x79134143c2082d141c21000c10300811440952440413101144200a0003161400300100c10031807214074100801080100b580014100025104000440710312034004945098900d0006000404154010030011408170b4050082c0301030255002d00420001d0700c03120035a004009511402d40040d1154010500e107101d500720040051200001420040e40d03403400541d01108210320480442c41942480000304801344103260280d40f240b800540d40c1c101c00e0041001c4100411500c0268032081806070005980d90410203131201000c0c02d0200d2160710304003401e140c01e010307070384903510840081c0104002410041440c0c0b0100784161a46d4040c4d490503a8910103e558110105e8082248a404103507a81d004010244004810385483e2016158030084100b1010035680120003081020051101180d0700e1145403400f507405100a14003403030b28100144000070003540f01d5001c1c0780d00102060b8064480c4121100007100d4804071107190800300540e5000f0320101c2c080303102d204850300c01003210794858400c407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 499266969 1250 499265719 499265749
    0x20a0f030509100b010212041e06020c01170a060e090604060c021506190305032b020c0a06241d150102030304140f240702060105210106050904080304020f 68
    0xc0c20000f1110310282c00078410036040606500c0758040d1040340300f8403070005201070413000000b074101d00c02c0601c0340d030a1440305030092819908403500d91966031b64004038000c1682003c0c46400902c0d262112034400030a0720f81c101004c0307800300c0407c00904510000b09103000e00d1092800f04000fa0001400700e0301c0f0311111145040210305100428400e14040294403504449180204aa1035036a5112491640700441748800381c0d000d05000303511443d032921703203580c0018108415854507120382d440a85a41c048840108200c1d922803001d03e03820401e002c40c0140710040f48105041607101c29000d103a080207c3c41c43c08845008600240c000310309500e05000c4180181c0080d400c54032250b8614400ba81d1190907081c983c8280301c420740c0404420080b094105001e41001045103060903030302c0a020000810030300a40d44040b004001c1603c0380f00c0c0c584c007141c01c801040070146d04100d90207405004642d0100354000d071000d091000380001000254011442192000d0720f03c40488280f002c01c28481c082 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 499268219 1250 499266969 499266973
    0xe0d09030507091e020703021212090c09010609051302070501060f17010917030403020f1c021203060d121e0302090f030c01050f0c0c030a0503040617160c1506030501020a0f030509 79
    0x48040d09101a009840154400d0060303c900040c0d8540b00b132740315000055480740c1024a4000e20903c0082400950314400054039401041c0d8104040504402030f07520621340160042c4042202080e032a41c1941c0c8080d42c008028011195174041c120820a10f40c000c03081546100305404403c450305108401c981940000180c10000010380e840c11a600010010750960044500090703981d03c050040441c414408a0101085101280001d280100781602964401801c02c00d000b4250365890202000c160f02c048014101100c00c07c0407a188076401c07529010300c6400030340641280340c060b0090144044159580030030780f40c00c541095940c4440000c1c65011071800c00158488011210003030105454020495198503035110100c0c1c5424841d4070706854a40010405006041d0310021641214504120703c01842c140021280d081ca04092500414040300b21400420040d4081c150300e490780040c441000380e41d42d6814928080c0d84010410380000380d1a0300714107900e50082c820340e8010011400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 499269469 1250 499268219 499268261
    0x2309130f030503041b0b04080d0207030b0c03070203121017010203070c020103020d1d0a0201020d02072d05271b0717040b070309060e060a210e0d0903050709 69
    0x7015511944003a105444200304209503001080903074241d0320043c41c000101c2683d03640351607540c0d42003400d2a0307211400c54020707500400100369606881a046014025400c0d038075114404180d02c1c6208114803151151002410040684540098902100d0301c1900a0b50003444441d001e501302d1200f2074044011485503071603007000d54880ea000d458510313010341b4001001840c418500c0c0d494040c00d00b00c0d403c942c0c4203000d15021568140561618458540001c180a0741003c4030200b02003504441d04858520f51846e0500f101c41c0c0d51588002850003500f06541d40c07032800c00d01ca0f600112002485c00d0221a4070101b41c91a640e030341843c11140d02a04001d00780b20441e59290741c070a0300c50b40c10201e00241440041501c41900c4002d0a140348240c80e0590498980f0f48090210401941c200c5e1083c5024000300c0881034000100c558101e80130800039070364800c2c41c10f0300e4000304403418010549202d403000e9181c505800040903010303a409201140d81c06540e804401c41698095051a504a00101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 499270719 1250 499269469 499269473
    0x141503070c110301060e10120c03030302070302100e03030709080309060403030e13110c06070c0206030a0c180623090105040b0c012301032009130503042309130f 71
    0x3403032524009108100b0101010440d100190944182d500400b0300d0310f00040502084052074004140200160003041c0c91481181c0c80f078401e20030b0203100203400d05400013000010184280401000c010115400b04a0b58074007100c407d0b0b5940017111000003040d0101070105030002c0000540d04d42200040404d0324280c25036504944040b03041421a07002072141c01000020000360190a004081d41100c894803000740c00074035441c205c1d01400c0c45046c80940700b81c010250329002c0c00c0300e9220803045404601400c00400c11035184043d090385142d55030ba00e20001c1280c41e884131000e100782c00000c004108034554295189507510414180501086080208006500780600681030900c454000025501062420224442542341c55084418440001403041002d80e03910282481034444d1101c0001090801086000102410094400809110681c00c010301001228003520380340c4855484550098000416001c211404520445540000800401001440007215034100122140884450b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 499271969 1250 499270719 499270727
    0x30c111914060d06060509130e06010302010503060d0c06050d060e010810090302150c0a030509060f01050f04110f0c0d050c03030a0c03091a040c0b0c070b160b090714150307 76
    0x9204030b81006051201c1e83d441c0500788111001058240c40b070695640f0000100894000700018141c0000e00d4003111141205c0009101415240e0a080090b56038885400040e003014220200600b0094401004100e0580c800050501503803016424095a51148003945004174240035040341a40815103c1c542214990420144c030303406801a100c7c0c2c2e952100021a1500d41102c0e44400c68400182c480c0380c040c1d15105150f40301c0c141d50050b06031800c1a6082c4280c212040c81050311a80d0104c00503420b6550759800078104c942c4c401400c90b502c42c1e415561100b1504002448600390142407401c5622500590031180c210900b000554070313542d0b500501074001c02c0001071601c209035952202400145002e03000308201460680b60318520716003443c120401010580112509080c10f209007040c14200044410554032a400d149072509041071156032074007010b01e07020b04012000001d10903c400042528402c2c1d0350b0091000224040740030500c20145140040d1407840c0c5010000100d40c6803103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 499273219 1250 499271969 499271999
    0xf050109032606101701060c05060f06031e0705030d090503010b12060a0c020118050a0c051e040209030c04110301030606090c0801150903051606020c1005120a140103030c1119 77
    0x700717042044003460703400c5c4003102d540c0c3c091b00709401107911078401c4814040104007041c0c4c8241d141d813002d00c1078503000c0042510741c600d01d51349450703070f02d114100b09484600502c15080940405021a803000d0031942000700110441e1180e030f0f0180d442c001300c90b00a81400d00411003810203440060420340c460140c80c1d8010200034181d2000c45d540d42100c0040c140c403034a03041003803c0c0544010f1002c0d429609010310710100c0d40d030040744151500481055816140340b500070110408440040e2210414400b10341000441d24403503900514160000c001d00b04e0f000040d5040e2401050204521521101580122210b05441c070021489240040000c65903090b204600e41c155480d11800166590303841038584591114036604441c55680140182070341048002420441191941007400b690040603005120700d0a50b0302c8421909400244286403d0300411185803407481540807075a0749043c000d0405101d003400f182c0243e0101c2c5680c64a203003002c0c0d0700f09a6111505520005480d00d000000b0030f4030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 499274469 1250 499273219 499273249
    0x2514390f12011b0c030e0406080d0315090203010b13090603020a030210050702154807080f0303070905220c0c02090a090201020601080d0f1b0f050109032606 69
    0x7403a408540000c0c40449000f42c00f0f010242c4414103040018034024040448044105000b9803400c0344c00c0291044c005204160041c141c01c00244071344010301a203c48000e9a005036140c81c5c00080000703501d1810000910102d92402e41d480c000075268043c1c00c040c0d41e0b0030f1201962109070618140050301d4940940d140d1a0715608045203490702c60741c0805e0000e070f441c1d0f2041d0316003400070440d0380b15015805000900d066460904030070350300f41265000c1c9082c02e0b20480004185650100040c015401c11011003c0c18081046401c00c0c031484502550380d5004580d0040090221000007699007001c01d28100308075101d01c40030000b1000c051000005041ca44a9503007005101c62a4a0250310f030f49590034050800380f200461a043d03030b4000a0715100c8103900c010328035448080c102081540c002c2e01c000f007044c12460200c0e200743c90300c160761000440043c030250414903a65890000c10a0540c4400c072198030903280d002080142c171801540800301010b00c50140400e40f00020802c3c0307000320f43c03000041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 499275719 1250 499274469 499274471
    0xc0810030303110d0510030506072316080c0307031d0f010c0215041e0b070305071e0206030901021209070f120606030602031602010b062514390f1201 66
    0x2000352401c1c0b00c117403901a294540d0340240404140709200e000e10085500c90319030305108040591012911404170b001d81110b4034640720206441050202000c40000080d42010328031340c8135948900940d4403944421002c6001c500ea036540c04030760301036041402c3d0300719000600b14061040124010f5400b08641101260700851110511510b015218083e002804850000c0c1c01e094100d241d5840d12840b00380c010303241e212828032083c000240e000c011a42003503031103c2d02000541e00d01e000d21500130680b41c4001c0d4030a9012040050462056020340301011200740b01c80f8441c0c85580405881d202d0502541c0c0b001c020300303071080c00b84043c50306d0108100e42c8104000681d0607a203480380c808981096865034200d11042e100c1c1ea81443c2c3c240585a64103a04940c00b40c580560380c507840e9410041911448040304800041070140260118049460406041a14400d0801421a64401c54842c040d024040782c8000402801407031f0b9440d092200c0c0d0043d1010325404000410080d01c0601c580c000d0b41e040d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 499276969 1250 499275719 499275727
    0x40303120b0a06020f060c032806080307080c010c080c04290f2a0604060c0e0306090106210c0902072901030204050a05042003160806010503010c081003030311 70
    0x50b88a14100b900144003070f5000d0060f003c032200d9000e052901c05081c003020b03194107105000b29001110048410124110418000000f03200384a10191803640d1180c0054000401e0740344c28080404000c0201070750000007040308c50302d883c6040c0da903130800762a103840200051000340321040e0941c0d0000c1032800e00c0c0e807030202d14400007a4205400e0780585280200500d000c40d8001c0301c9000c0780105254100070240509942076490b0200e0b0b60f50000a201500d41911a000503092a01850400d400580c000e4180c540b80d2400006042c0030f00600d00c01c4910380110b1410341154044021a4900041d030f00013000300e2a1031610480c1d40c06500140d0040d0b641c4140c074103008001321034134119143d55414040c02d60000d0740c954010481124001080c131000c150800c402c000c00140302848d03030a25200c00d52400350b003202040e0046840d00d551103040c110b1070014614085400c200001d032090403a001140241314128004104540d9a80203031070144404102903028800240030b030300324045135003410000c1810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 499278219 1250 499276969 499276991
    0x241106042901080102130506030415051302120c090606090627030303150112020405100c030302300907030b070f0519080604060519060e04111c05060301060b04030312 73
    0x410602a0320a180304c0e940044c0c0840e0005070000800010402220308900714038141c2c940300c0c0803000d510480c00c1391030f40d54400500b0051710f0450340c41400e80c018040403541c40001c50b54943d01d61f046484540f0032200c510000e0240e240c010121028000041c1c056410501640b0b043d604520050f80e101000034645581d0283c0ca1f00c01300040e5204011641d01190180624000034100c8410f4006101040f0300410081c0408c1d214002060a4020b0b40d01e800c80c95094a401c0c124002d000b0002c0c03c0400003072120318071120b081c181c28043c15010f070440768601e075a10303024030302d660300e44103031100510600c0e88000080081d4050f400070b00191001b41002c03482c24456030710b0381905c0b0100c0000303600401d8808050081d02c2c20603210700009000305807420b8403245551a194100342d0203d1241c0410002c4504110b00d4949903901f050142101c0340a10304e031107513941c0100121034031000c000c14200a140c400091100d00e8140940000c44142001d05071030a401d41c0c50440301400e22860401020b5210440103030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 499279469 1250 499278219 499278293
    0x8192003191e03080117011b0e010e120601050112150306051906030b01050f03070b0c01061e0b03150301023703050c03151201050124110604 62
    0x1001c200520034020501140b030800c41e03001c0a8440c0e60820300719224200002908034040c00e06480c4200d03000e0001c5802c0c44406405032004c501100d405040780c100c03038841103800050701d51950030241c0394204480260018050880b50090400301da035400080100040e500469160340c4007203450070045032200501c120700703052241951040b11070543d501c0400052188100001e540010317000000d00040e46141c4621003120b4042c09118454001c0d454040301965042100c40b0003400c4400c4074030317160148141300034000c04051098001a0840d40710502800e00c181c80700b001130b43c4a4404042c116214005112112075041c8480707600340d03500b00020045c40c5441070980d69040c00d42c3c09406c0300b20802031586150707000507040751000c0c1030030002441160204a03084d60340c460f034441001c9003410f9032580050340a80c20035900d900d10f03528180c00807815000200d8400341208110941c102ca04048480454680584081c56141c0350408008100010034407564401040c1c0031003d00601d031154940440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 499280575 1106 499279469 499279483
    0x603091506030705181015020d05071a1008010b0d020a050603090313120606051c0b19020a0e1c02180702010204090c0e03060108192003 60
    0x80782501e007002440c00804000700f80e1203030b0400003408a82e222a00352000c0700900149100451030610440c00340c2002d44042d070051000900c403079021189a04415812102564582400780720b015080003102c1c000e03203030300221981062402c401642100d150701d0885005807150f20702c12000d0781c2c0341100704d0110340b4243c682d160359170740d0546214250f11407072514000501d00ea00010551080c10003501100b41c5c0b003013008100e4540c0f0344040010718051550000610044400302000150040c0700180d00310480c0b041242e80380790110760b90340c10f0b81c01c02c5541e80002105140201e54918090504511400c1980315180c00d54440b500071400c040c40f11254440241c040001160580d4401d50499008011780c01d000c00000099100040c030082e00c3c0582c03907220b48101c40012458100100300508520300040e80c4415036074460b40d9660310f030144011580c0071003600c03140c41030603910309003d20 = true := by decide +kernel

theorem cover : BRFrame.Cov 499100719 499280575 := by
  have h0 := BRFrame.cov_init 499100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 499100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 499100719 ≤ n) (h2 : n < 499280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
