-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2221
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:02:08.742993+00:00
-- url     : https://prove2.me/submissions/332d1282-85dc-4175-9390-bc59195e5dd8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 399280575 ≤ n < 399460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 399281825 1250 399280575 399280577
    0x1e03030a030e120a090f0902030f07030b0111060a06061803081b0c03070f0e10080304060302070203160603090506011a03041211072c0c0d052e03061d0a02150702040219 74
    0x1b100c8086007000070f9100300d03801a4559950303881d241d654118101d01420184041d0f90400540701d110507190402005054000c44c0101400f040c147d00341003004060f040c0c1501000c0b18401904400c0012a2141040f00c00082e41ca00003440340d82c00e58460180340115a202883e013600c6180e100045c000341c41ca4508003514950f150304082c644500f010203980000c50300987c40c503900104000c001c1140240d0041c44a00c0c8082d06850342c0b0f1520480400b10340f000c3e90b002c5000300f0340b03501740c6008200b030600a403800b400301041802100340a0600074552800010b00040580b4181f08100759000d00070900e110f41220020200e401898a9a040442581e07001c00c1041d01c890b00c0c000c1101d02401c00071000351281440c080d00d01d0812800e1010075001c0c00c03014241001d480d0312101c0340d484640c01640303030f54601942040b24005140c134510784032045a9408000d8407400c10303400320042241030086041600035404446510184005044110040c0310f41000254040c0c400607803410020001031070b400269200d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 399283075 1250 399281825 399281849
    0x50402030705071a1b090f130f051f0605030405060408070f0501091a0112020609130b0307060201200405010e100306091e06060801062304050d050a021e03030a030e120a09 75
    0x2d07000c685c48583c050b0600280e40000d41c4106807000741070404076070360588000c0c0c001140c546107440c110301c21100150340e440c0000495003400000403c40b485807200800513890401d10358505910389544503400500001c040c6030001443d042413250385041101e10541000c004c00884c20300345007942190142020349040016240000100c500482d6240c205468019080d940741101640400145007130718002100d01594a0107040c486031420441c0780050038250b0000038a000c1c04191500141c000215032186a460400080c0003070b0341d2110400c103a152041d07075460303c000c541082c2600074098030b030841050fa910344200210b0300300001007185c1b01803c540b2004c00200c0d45855080b40d072110240100d0020071110aa211840e1550561900c041400307040300a040c15184e0001075160b1007014070544107940800400b2066107070980c519417a6000480f14201d080c03c40001090303d034050ba414501c207040d61a44400300c1c00f001480080700d00401d840300255a0000101f014020802d5401b81142c5800303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 399284325 1250 399283075 399283111
    0x504081216110c0d0605061212030124050d1e020a030204031401051b0310080718050a0b0a1809080301260f0a140f1203160c020a050402030705071a 65
    0x20041480d03542c3c0d200c003034803540f800c030459200c410140202412040d00869800ba0a41c15480c06001050b41c480c0d9448000303589500d04416507132402140704d001e4078080c0082801c40318042c2c101046441c048803e03a4041114240c0180c101c080c807400e660b03030211150001840c2c100e12035269000b041a81e100ba00d0302489846034004c00d90880300111526801241101841c10b80f0b006004099907200c41d0950403d00025112003c0d98140b400d030f030b8130401c252443d404c94440e803042c0c14056035078010904030003004481558400104040e010f842805182c03102d94001c0c8101305000e800141e0919002072404d643e0b135940d8840b081e200c050007900003000708005083d06603024404102c002d15240c034800104403420340c50b102c002103004050008680e41c8500c0d80507480f01c040511603c42074a00343c0f151191685841c0300443c4440048e40c00d00b40070040d40300c5c031403030060783c1d020901025560b080da001600c80d40c039030b801510184600300c005805001d0f040c3e9014000040030703201620402c102c0b440d13055054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 399285575 1250 399284325 399284357
    0x120307080f2802130e0919020a03060f0c0f0e0f100302090d1b0b0414090c04051905100212030c0906040b07050a1104020f030f040201030f090f11010c0c06030504081216 74
    0x217605030384680c46a04000800c0e41148110491081d034280000e103501c458954039990102107a0103070001051598681442e0150107810a411600d0784170b9500781900a044160005030350350b9201c240c10b40c45a40044502c0329064404d90550344100c4024010041851042c2010561a501c201075960b441203080c0c004a0f56014071403e40e41142d001824802140c0301035410000c0d6a03400400c80c00c1c10030300504c00043e075503981014500f542a040c0190320340060501081c40b2204da4800100010f41d4098805540c4004030300040302d5000e0020700b0059100c40205000801c0362141c0d501c0200040ca011580d402403000200b00d081e001c6109a00e1020386080304400d0201703074015180c55150351035051001800f036000025200780c4c000e105141c0010404070584000c4100c4244805c00c0d200b01d000c54010508100348610055412142401d100520070803580d5402c5001e016800b0741010140c0b6240030400700040401500d03290642030303c4543c0207241890503449031107617184403503001035200c0c02444450 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 399286825 1250 399285575 399285599
    0x30402100f0816021204061701140607020906120307030f090e060109060e0a090612140102250305040806010b0c100c05041217030c0c120307080f280213 67
    0x15860b6165005640e6030b044119101c01078000c440000d40c0200c04d440c41e48020900005d2019040340d440304240144d40c0c01801400303c5c01608480c03a80b031110b12030120240d0350203050301d610341d60441e000c00702030707643c48003003041c0f80350000300a140751002203024010035401c0720b04545495401c2d510380014a40d550084000c02d0710a03220341d400b00c0c86803e403d00580c1c0c4180000c0307002110280c14221515a224405d07012107140340c3c00640302c91286030302d84003040b0121158214820301c0da402507041046a124085410444584c016080400c640c00175041500030400d0300c1c0286401006d6951355a074803150ba0400e940112003040550040b1030415061480920400744594400c3da1503500301411708850000c9047d00f0102580d140303400484101445801000861042100016075a11003210220b0b02d441c1070030000c081000300509004002c0c0042e03018a4482d405000b808200ca03c54403210340524110104484400c001c04100f403031640d1441c0d680d00201721442c401e10600680503620545480b003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 399288075 1250 399286825 399286847
    0x20f0703021c11101d1e0603090a0611251a070201060f031124070305250501061403030f090409020a0f031104110406080402010f032003040210 63
    0x80b102c1c11991400c142c0d6954002d048203a840303200888072191042002035030303141d1003025440c0040c5244922034608507042188402586080d180326a00304640352014500c20755503428640581c40100000e080f02c80300304044034030560401d00801020301d408245082d2980031007407200d206d002502045800ca841604901c8085030841c80c140542040780c0f4140b03519410140c40076045640714140440d102c40c01c82031000003140f14007500c0748062602c0c0103210024420164201c0704801e12030003e8203441d01c100c1140c8140d82c0c989030481e580d0f40c5500c4001072a0302d4108100712005510b610100402005601c00310540d081450b201c260f1005d80d87c2099500d1050300c1d0a40c400c0301c020b01c641d4855007400d4102c0400644018241525a525560044001c426907070040d11215045200d0009a04040c07040d0f038403e1031094441c2e8a000d0070403001030b141f24001b4000904004101002c40030b0390303101740e1041400c0c4400c0c403101da1280c408100b9045861b00f059030240d10501c260203420010740c0c007070712002c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 399289325 1250 399288075 399288079
    0x160c05040b010e06120601021e01151a040b07021311031b09030d0804050708060c0a03271e020a51020102190f020d03050603100209040e070e07020f070302 68
    0x211707094100c0003142ca400b03400b601c11170640c03107040c0c049002400c0958a186400d141600005080020415203c910070016840100071403002c002e411143c5100e030342240c0c203071600c0e0310200c0c0e900c40d031600c04110b803100c40b4140c504060740303022090003061281d00005c41c000e060407060311051300b91000c9000c54520a1034107807949036201c60800707501c89000740440c960141c007640c01e8507803aa948103000c45c20000c048070b0041040e800002c148000c03a4241c4940c1540081c44852030511b8002c1500c154601d41c030204018105002d03000d00c0381800c0401c00d0380182025800f0303290351000d584d161920790140740800c40b10050300854444200020282d1207072141c440c03c41684624288950b00c085030480c01c20601000c045540030856503004413101c08000c1c5004559558010443c800e0b4040281403a100d6090101018100410321a0030342d000540c01d07480000740300006a507244d1200005004151054055840780a901c400150b08620300d0320032803158074960292211962028116516002c2c01d0000039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 399290575 1250 399289325 399289327
    0x406052503090e070e240d0c0905030d0908060a0f02130b0c010605090c0a030b1f020705130504051f1e020307090e0c0418180c030c0602010b03120d02160c05040b010e06 74
    0x440402001d58001d11420440d4005103030241f42d1a0640584640b0b02c41100410420803003000070b0f042c01c004080800c0d80310b19000500500344425140c0b26800a09034000c45134960300004100b002c903070304954880c8240701c4411800c2e0782c1c558101140e500100318482d899440c0040000b094184034424910983d543e070800c03490000804015002441d8400085810682860016130000900b100702500d008181d0000c0c4411807501080004042800b04500880c034100000c1c480041c0c00020408000000c04800101c1002194907101c018406200700b044612080540c590041490b40d00071400f9401130f5989001703054842c1c4400c11410825201d181e030825080204004c0b00ba01245a008583c03418030000c540c45224107a110210500702509503400a24450200701300305501f0302c41c034000c21050009001111305400004c0c0c5591070200442d42c1100c0c001655812007a00b541107410641c0e0100e4540600e42080c103001101f8480c2e401350501940c43c148081e07510b0360007541c0c1c044001400078503007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 399291825 1250 399290575 399290599
    0x708010b01020d0203091e0910031e050c122e0c09030309030305090d06091208061e060313170c070e13030c022101090302011a01050406052503090e070e 67
    0xc0a2148007a4840b2030608062402c47c0d1076039510f00d2a0384e8090f01251401d0b50400b0f0950030140890f01c0e071004008141581d541d00705000031401324003140c81110484003c809460000d1480c0c0c14a0075140d183c0b5189100101440071703811034443c07100030007000f1440400c0892a4010191040070981c0006004a1602042000001d1007040200030382103014100181024090340c80200707603501e00c071044a0304103030310041a18080c1d204036000e5002e1802c484940c0c200940e008080030980140e10003038050440080060950301ea0f401410024592020ba000c80c4010007000200c0f580c0c1045480110387d0041c140005800715070058494080d440d50703a016848800c80d45c2d41034800d0602c1610480e00282e08800700d05003440c0c0e0226070a00d50441c4000032841c500c1616000b403c441e2030110000200c50882d2008a8503680030060f04c046ea2105e0a000d0741c2d45071b4401c807038a04500010050701c8030700401c1542e041016030280f42402140c1001c0c0824803591181d01d020303500020380e0200ca64004141c0c00e07070 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 399293075 1250 399291825 399291829
    0xa09061410150504080304030c0e0a290301330b04030b06010f020109050105070f030f02031501030908120907030311030910050901050405090a060e0f010806040825050708010b01020d020309 83
    0x42c24032800101e040813440c15958407846400c540140e03205480381082080200840e081d5082d034035a22a064407410031241005d110103110700005400c1090802081821b507050a807001d60002140c51181c5400e030f40c84921104d8801c600f0192516021211940868001004041e01050b41d0980c0c0d44659240e2440d505d6000450703800b001e41c0c48440440d03407101344c2540815000c2c410346000e2072260b506d0000c0e40307000e002c0281c00d4900f842c0003690900e2040040000000c00c03429000c00c0c03080d00740780220f0b482d022414005858010115040344041c1814184038070f2913030016020007181c2c4030f0b880700754290700e081900c203403039000c0c401c002500060140892a10303603214400410010205040644c1440d450300007082030b410003220a84221139603640c0601220040d508515031150080c1c103204551b6041c0181d45441700c0014000030444000402c1d400001c2b2000c0302014515041d900003840d02d5030040c10000c0d0b0b40d201c1485000c0c85546001d41c03007056944003040403640410320b60011403800c010442 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 399294325 1250 399293075 399293099
    0x10b01110a2d0b0a0f1a0307031b030503030c0a17060f010c050f070e01180c050f073003050708070905090a0e010219110102130b030415050a09061410 66
    0x10a81d00b20350702c8070580700068090020315000c0e200400c000509500000710032002c81c0c00b588004c1d13080c0d5180c000c2080b071030340c2c001590300305980c2d020307030320509035103942a0203182550380da040142540800302c200010000d116024001402c400c0c2c0d2030f070580d011101000c001207107065814a400000802000071030b07500460713400180314421310480e81c96103604500d103410130046410a0450070300644c01000b00c40840c2c0c52402c81640110070400c070900b114200078115215042c1907068404000c5591401d1101c0d0392000d8018040303032010550020f2944130072102032203103400300d5404a0300c0c4c0f1022403819803141e10700301e01c14010b644510307030542e00301303800c211601c1e0000b85018411602c840402c0c5803200300380050460101c00003032079110f01540c3e11001d070100c40e15204402c0641e1040c001c904440c2c040701c100404403504009065a641c5032410b0285802c1840c00800000364244014401b0b8001e0344d50090f60f1880c00340904002050906203248010041a902c1802c10f4444180610843e0340301c038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 399295575 1250 399294325 399294383
    0x18151d1f0e03120408010b030c09091905190606170c150f1b03070c0605030708060105074403010e0406020c07120804060806010f090905060307050a08010b01110a 71
    0x400700c45140f210141c65403055406900300340381c0d0f03946541c14840e0b142410041820720001c226542d00440c070b001c0b01d00360b9555035590b05441c0800c5403007600c4020321005128103070311013200103070000e00049c031400d2040181005105000707030300c0c03d080c00d07021600e07002250315600040b004040880d50703c0d0040e4a8a80b03504041e004a0400c40304002d4404031712140c988000302800b405018584844090408980004095001e4001c1c030034100100900303280c0c80820035500010900b0038984421107030511002165103c600780384040b00c246106220480054210304c0840100c92020503102c448200081503400288102d001c0c00032100d0115000540d41c2c0c0143c40380d80841d0381110009035807846d846510064804041e210104005028040035500040c0958800b0080c03c0041d41ca0400020040440c3c1040c42821031860b6200d01103041507a00b407012900501c801012507881c0f80c1c660742c4040c000c005400140d801710f41d40544c891008d40c00070880c401540d42100000c994003032408010a0200601 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 399296825 1250 399295575 399295579
    0x30c0801180e010203041103012301050d0f0515180c010509060c0a050303010b070b0601080603060402040f021306110610180902030c04090f060501081c18151d1f0e 72
    0x1065000c00c0400244045c501ca1401020100c14190958082c14219040900340703140402c1451820750107d0100c1c505203044a8040d215000c1865083c104058800c10502d4010b10302e004010f06c1c4c0c0324442281c0142401400600020440c80409200c41c3d9900e0501e01042070100307809004001a03843c1c48805029050307000800d8600d05001c51f6035a905580c4260000c8c51a0000880d0f443d0910452038503a0345d1042c42030810b14400e080c55400a50b94030401040284929200e01c107050014046405681c00e454003448501000303902c2c1c0a000c0d242643c001c0d460140c510402c2d00027042d010203026000111602580c42a100c444184c41d1500580200c500503a05441465134904c02d42e00c85110781c040311400741140d4079454005190090030b8aa060380000b00d103a11900d03941025408000010900301814100041c1c0100085010380b0b46111981c022103c10034034420007a41580c22000c03081c00006003d107107522481012003044482002e4007441000200c0f80024183c040b801948111255400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 399298075 1250 399296825 399296831
    0x105190b030f0105010f061202070b1807090c0c05011b080c16080703030b030d02010b03060705070302070323070b2a010212010b0c01060902191b0c080c090106030c080118 75
    0xa80b01d20782518000e03801100140c6000404000c200d0703024000d44001c0c1007001e001d614100d0141c81e0411b490303101805080101c1c0344081e0b21202d00c0010030000c8018920024240030508880c84082c0408204040a503510b50070810304801c1300caa541e4100c091214140c83e0a041a1142e84d00d009454115000303900c138000459440e40c021070700c2c800140c803000c4c2c420380e0042880e105000906090a0520800c0800d681c10041c400700c4035980801d4650f1310411031728040ea26401c150030200e00d0a00c1c40c6d48003501100d00c002c1d0000c040d80c042400602c140700520304450270541c0c1d45c1000495440745406d04101e6180c1000000c82a101508910005180900001d0708240620341c2400c0744800030b90020340304040000b80c00150400a0080800511001000b14208000e14103d0320000b01c04007018000c02402d000985404000602c0801d0403a412007a20906940c82d0510241c1d80c0b800d09408501c15004c0c0d40000072400c1c803900404003d01490359800507d0f9190042350310b441b404c01c1c2143c1006e107072 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 399299325 1250 399298075 399298093
    0x604030507051005090106060306060806010c110427140d02151504021602040605040b0d02040207020114070c050906060304050a0b060111010c02010203101d0c070321050402010e030105190b03 84
    0x2243c3d0294900803007819000044a91410a014045485540c055002d1150300b004001c00c80e0f030482048200d298000201194940801e00014018407143d1840082a0800131755000c00044980c2d580340c405103c0c54100d45e17846a4030702001d40da5560b903034801006a0040f04030480e0b80455030040d81c0c0100c0780b8914107100310769440c0014107927008213190000e0f0300140140c030010f40ca468000c0070000c11003034600700000e08640000c100100c0b0000d00181c0034907000100c03042103910444080100304050034200c4d4840141f482c040042c0d203094441c1612030110f00c40401c04610f403100459002c0c6600500a0640726030315a104c0c501400002c0240c1c1c10320042c0320340c030244a2400e00035881c0e03014041d070005a803450090344a1103a480c0350b811488080c04101060715616a4003c1010b400003c00c080903a2100b1301031400321005003504619101c1c1d00c2101c6550200341c29103400403405580b00340c03903103000c07180c0600c1818201e83c01201d180c1c0c00c01c142540300e0f8000003400c3d4058003d00038054284c4034420 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 399300575 1250 399299325 399299353
    0x80a0e0112180b010b090607020d1406071d010302180108070e030601270614060309030f0f09010807020a031b0302030405090f09100209060403120e040e010516030905060403050705 79
    0xb580c2d521900714640b901c1001403040240c0f1181040c09011841c004509199208001c540d0318041c1900c024003a800c0920540b00703001085a650784210403c6080300c00a16141400400b18024900301300e803941c1c402d1940c80d040e58040c6c02a01c4146840104a4420040d20030044076541401f40100b000e10070900307646039440d1801d00c40c0c103018001310f0481c000c462744140245110b00712100c10400c2e85034940003040c80801e0350300358480814001182c416469031181c00c036050640c425241051100400003c5d213100c0c500758080034000420003601d524449645054007039031154810403005000034008011200304030451070170080c41034043d00c101ea0a2645540100700c20400a603a41c0d0801c034827003010803000032410081e889207903500141c10b50518500c40040f92980c001c0c0c0c040201001000381003583c03c18400c4101007032124000b0010f020a0020401c1d29008103010f44d2030780ca00c180914030418a20340a4040c51541550050050250b0740d29034030116038a41102c80c003210345008880d0f01c400c0b04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 399301825 1250 399300575 399300581
    0x103092303090a060c0f0305031801051501080a1505060d0b0d06050a0b180106030b01030e0114040b0604150504020304030201230610110c0d05070803131a0304080a0e0112 75
    0x561044401190ba6241c41c100300801502c80c1c0c1d004004019601c403e86000803140b4006030142c80d0300d81022a244c2e110700390742855031600070500c044658030382401c0151642001945860308507082e21100c540c0d8407414015410342e944c00d6040349010040b550100001c0c240000146504030b0103000014090315050006a402d030207104003610700d10b48038814000040c00f54451409840c4041310b002c60b180e45a40c40744603c0080c1403103001c0525654038140800c9174040d81141c4407085580000300310b101c4034100c003003248400554003501c698071041c0025003241064401c600c02d02c258440c8078401c0b80c0c507050401c030196000420480465482d2030784c1c075210700482600f44074140c1140901000b07502d014814000c03440210400d40c001c0000805040da01101c010461000c4100159603080075070f85281000340c581074165002d68010310000410494584440b81514203a03240000d00186009000e1404441800240d8000c5c06542082100003041030049000028803c010704103a44070130b80d00318524080b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 399303075 1250 399301825 399301883
    0x151b110609130203180f100207170c16062f0a0803192d0e070b0a03150b0405031f18030305010311030609070b0901050715091b06050306010309 63
    0xb540e004000d0100724502c445c8045103120001c002400300207540c3c1c0b0740e50303a9a64400450180f140d4001084000d0050441940000c082a80b00d03559480c03024506843d582d581750010854440b883c2800458200c1c1f00c0d0904c0c0903028901081d94085425211001c0002c64001d03200c03070030342c3c41801c68000003e10403030302951240603c10011000c42d80311914000580b8050b10b0001601c154404185802c203011004e00361080c0c440460015590111500351032415100c0d42000180440100d801e012040d403503007000020600c0c03002c41c035410a56904001d41a03000c0d5000d10350303042e00728940c2c2c0c4890508800e0040c5100c00521000b240d002d248001114110110388030603400243c84a0051051000c1814201075552701600108004e01c2c0018684d0303203e100300e000300c1028440005160384036a03c10815603e5840e004903040e4003491040c081c0170000e101c0444100d40c601e0740342d00c7d0f820541210041403070485296481d95031540e0349000045008100a8404a0790322010141c4809940c840e0440111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 399304325 1250 399303075 399303109
    0x18030d03060501271202010c2001021b09040611040b0c101805060f07020309120c030d05030717100905240303040803070f03030b0907020601151b110609 67
    0x71407600b420001000e026480d03100c104800d03500b03052803280144820903c01142d8048181d0703000024103100484001c420203401a000244000084550514801c010012180d00b45c080300e501c81401303540d402c100d0404100c00c541c403c0d074000002e0017290060f0040c2c1c1450ba0030030740302d42ca002d4592800300610b030440045030025a111407001c041104017882091666200701905c0c1101010645e64a41d83d5200141000024002d10000c103061034020415500341100080900581a401210300340d600c0d003644a21500c203101d288942c1c10240c1c0a00102d9001c2d00541d910402e0001030a0035660070f10b180a00954050071602400040da641c42c0c0c0b00d440d0041c0d2007600031002e88031000080c403041c10407100c00f641c8a0780040100300217031040001140c2440b0741c005088002145241001e500030a9010b5005400c02412820032203503550220b5903505943c0d5002a0801e4000740c2c28041303e0b010000d000d041d03145880f0304038031404103c000d880c500d203403000200034a160020349400304030038004c41000c440b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 399305575 1250 399304325 399304331
    0x60304021203071b0e062218080d1b051603120c0509031c090621020307050a080709053d020a03021504020102061305010e0a2009070f0518030d03 64
    0x19240c021a101c4a13001040707002d8070000035043c071400060103101d0140c800340381030724a90341030645c0980c107412128003181a08545401e1203c64103021120ba4802003207440818a8001d00c0030000c0d0168004460781000c941d42c0c2401e0481419903103040944100064050204038840c90340c80c044079002e001845034150391500d40320b80d044024580781428600220340496010580d0508072540a0b40440c2122003034034261490b410b401607140c83c1e0400480d440c04402d400041080801500400140380e030750b070155207030041079079405400c41d0180018028103900004601c0c003401c040e43c12044e00300900405150000c1d441d44000458100440030f01e01c44805a00304c030040d1002d0540600245e40c00440b00d0b14141000d1a090740000c2d29240d0051555480c80c1c9600b05400601100b54030075440d400d44507044880c000c280b41400c0c03e554180000e000800c0b101030211107568106a00c00034014880b035212581340b0024a5070540c0c160700103445032850728240f4810300301c0d569400c0026a440e903074152800 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 399306825 1250 399305575 399305603
    0xf060804200916030b090705030a0b0105070f0305070308070c0809040b01020c040606030e10021317161d06060a080103060c02030c0a0b060102070e070c030309080c060f0108010c110c06030402120307 87
    0x54142d40100d03802c0e520030606c210400c07441c10340100460f40d0043d081c0e1000100700c016240140c81c9401100700282c100a102c140c0303542099041002000164000c1d200d640c50b40d070341c20301c04030344660800c0001401030809000b44080360425800130030011205005881c103640074540894125550340e448100040d485000c2c100c04081d0a20011081c1404900c09500c3d2032900c80c401e0600d00c01c1b5100d46044142850680e00f0201008c6c08401410504c8410090820ba0b4845041415000c101e1ba00c11041ca0404003040301407030490121596803c1c00c0e00c580e906e581ca152110760082c444040e800003540420070800c05603940c1030002d0184984903039030885a5042c1640024905900d580000c0000d003208000e01001c29000143c02514991505d40424507840d10b144c080d825000d42e1025a1992040e00c061060848400d102241a1804000200f09021041104485480d0307294243d1a0580100701072150707506000005582c460b0001d404001402140c180b101d107160301031401507031480c0d4081c640c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 399308075 1250 399306825 399306827
    0x180609010911090907020a120906030510080604150b04020a031a0609031203060105070c080f0c030c010e0d1a0103080310060e150c0f07120204060f060804200916 71
    0x198038094001c0341000c10200c242d20100c1202d500c0790080301840340300c1a40c0003419407842004511840703a07000c2180300841c041c01d0400b134155401c0c0c0c040e00317001c41d041c000024020607100d0900001c8440780c40c0101555140c903144c41103001c02488043c7c7d00c8685801c10740c065a15036000520b1180d81c44d42d800250404220400e407403910f40f01c2450b0307116000410041116650019a40c0e80c0d200500d10416900c1d1a0000140e8482c03103503060042000e045480001944074001c42e00c906040b0000050315029066003040688501d508070f00d841c081003540080032554245002c0388001c1900c40c05070340044601c02070341b000b0800c07400da10840c0c1d4001d000003001500395400814200410050800e882801400e000190f685014984407124200c401305801050003400c00491182c1325011058a601a4883c2d5410042405661080e4015400c007400060f000c0b80404000085500741e0b51108806c2d03d40350741d200b4880d62000b60300c2402c1807006002240a90301d94030100d00884640600e0704103082600c034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 399309325 1250 399308075 399308089
    0x905090c280b07111c0210080f1f0b0705030409020d0c11030c0a080f071b050315060f22060e040b2401050a02070f0308040e0f010305030f0d0204051806 67
    0x3082a00c0028804800004c034411548040340c01c04030741c40c4e00d4140941c1420074408002040c040d50005034000c10650031500f00e00a907002d06041200446030ba9a2800782c1541d000c0500f0035485141e0644004006031206c41e405401c03050321800640f81f816035280c0c1070700241c0c1c00948040900540e11607400d0302081c0c20444108045480001450a00310010b40440d00c032149540c014125440c0003815240607406a0b040b1100b06074010403001490200700403521a9052038020180240318140e5166107080c8805a0b40d44129130050100020f143ca00b4103001c03050740012030519410040b103485d000ea201490003448050500051514040d00c1d01e82030110070503602031b04035000b1401d40c0b4800541c01c0618031200083c0642820003540d41c8a02c210b08900e050416030050903d442007a10100401c401d000c0104115600340d041e6500e2504c407286091050070302072000404940c400c0091141c40c506103400781c1402c41d9034203c0182459904c201042c1e800f00d207030710b81c203461a0f00a0708210580c50100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 399310575 1250 399309325 399309329
    0x711010810030b1504060503190f03030908191b020319061b0f14071a0c040b071b05030609030d0c031407020a1202010209010914041107080c07060206060a0905090c28 73
    0x10b0051070800c0ca09d03440c180e4061040d0f040070301a2540c072050001414020f400100c60300c0d0740520900d603108204049090040d1149140d00006628004003402d14a0034184c010181c94000f009494404038207881e405201c42040000c449a075158141c40340e0200c00c0d400340c05901041a11080813207030740d2b6070008200c4913251603001001e0005200c00c4000c1045404032408008104841100079154650f0000c603d00880d4409080300030006849010414a0040540b17030f101c0c0251403480198132a020151520822120b00c03034141e0051201c20300a03405600301d440b440c00c1d54140015101d2140d0300c60900c070f2038100d5249002da0300c44e029036010041907110089810340036100860a01d8461360000301070000500c01c510302c40100040d00d204079900d0342c1c8038604900390040b105c0c0d90359410f03140062a5411450008029014040000a6050002c6000d81c0714910040c501003d403414281164010300d00900280c1d801d10840e026034130b03035480b003224252200d80060003c1d81c06000e070104501d110a200e03 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 399311825 1250 399310575 399310579
    0x340b0604050103080a05070c0302060a051e090d02010f030e07061e02070806130c0518040b010f080307080a030e060a0609151d04260706060504020711010810030b15040605 75
    0x840c004001042089045d1080000d80385095965100c40303041228840c8143c4d000a503100e0350000f48881ca26030014010b001d0010700f1109406840780701900d40d419070017180031303454100c500d91808100541c4241281d0003130700c66501b00011003100a800040c941003040d0000c07404140d080030044411207079112a242c203c1102c1c40207213001e50070301109540300c0e0750150154a4144407122541d0420640a004401030300b009811614030300c400d142000680c04003940d00340c80b22200b20002042e40040c0d1080041501c0003500194640034266552844650103402090304041e910681e0041080040c00207a0258250820104000342044000710803124004c201c0500490305882c00c00420506174110310070000307003036001d02003a81e950604c0000540b48041d08603450303541076144052920f40c80f02415005001d00810080700e038072101408200d1140c2c603400382c088803000c501c2d56a5588a07181e50381e03020081b612100d498a0f0b90381e462001390102582c0c00381071541008c900500e40c2c1846c0c841d0500800003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 399313075 1250 399311825 399311831
    0x312090c03020112061a030103170301080601030308250f2c0d0302190c030b0106030c081b04080a0b06270411060405060f0a121a0105340b0604 63
    0x29540324455810680700c001d040c0306054500052030100b0358004001800c90b80c01006080c02620303200502c6134402d0108507200c1007020070385c4003442d804005aa0513550000001d060780c0c1d0968600b034541000040601030701c0410101c403140c0c20012040303a6401e804090701d980e10241c119400c0030b00302d29400074204a103c1001d2101070300361841004070109030304083e140f0b00302500e21401c0132401c0a0138002083c40103451284980e0400075941040350449016400c0d1070510390720380404406880c110f642040c00984001c022500812684820281d018940200103140c6562140102e041003030304201905c2c4034030840100007940c140b0721245012030440e8100040030900744202000743c10310140c400750203114208079901d095203031101154007911303008005c10340307441d48110058031070743c0032811000001d10343c0145459202002d000b4200c075102d501c250790090508103001114550404140280c0400313001020a506220b200c1803081302410500b240110180f842c20103034445203010349418000ca203 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 399314325 1250 399313075 399313091
    0x50d1103090f0607080d06030b10060e060403060e0c0307120b01050306070f11010e0a080a02010f09020a05010e04020403060203010902040e0108031303060e0307020316150e090a05061f0c0312 84
    0x40c905904518028049516507100c40817820a004a4020100c00114030742c5000004418841c166081c41c0c45945200105410320303445403c115035045003200342070b0b0414404d0006200044c8142c100140800000044410301341e940e01c0000d1910600b07a12070001662084003060501c805100244d01400086d8002c05160900c410020b00d5076041c000803c00704a46c0483c0d26201c1034081d0084201401e011007250103005190600310b42c564003000d42d007000740d0b180c28031440c0401000d00500585c2a0010080e248803458000190707500080300c0303259540030350f003004007000144192001d0f5006e0466240016102d134101405130408800607001260780b64000c0c400025494640c450802c203403607000f800413400b42e010880c018654081d054001794036005030400f04c00c250810715211003c030b618090b01c600d05085806010342d081030401c0d0030590840079500001e0814003c0e0381046420010180550715804070032003481003603c0400f038000d800074180c140403105165021035080d08040c030380002040b02007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 399315575 1250 399314325 399314329
    0xc0706030e1527011d0109050606150c0609010905010b061206040c051c2901050f0a1e030509060109111903020c03040e0412020304081002070804050d050d110309 71
    0x24100702c510684064000c00014188003440b00e000d0902041c6070340103600d8a0660074440e011341204e0200800a000e50f64a043d845501401074040e440c1d040320241680d5101d6030248584142a6081403034000303020014004074103c200245841182100d0001a08070810700c0d01130309580c18030401da4440c10051001c1c5000030340f0316040d071350000011100000c41e480e4141080e500f034014106a01d011540308000940c036407009400c0b0754603904041c1c00d0035040e030b03900ca1003c58502c034003050250300080d020b0040b900e00c04e14940051010100505018200c002655903422608905c4800c500002e5200d00a20441c3d00e01000380f01e01409581c00e0506c1485184000100140100e200c2051000d114040516100b8040c2c0d04441070041c55030141c9a480c0d844030a80c1c1c00c101d00603907049840e0980c1c0d0b440d2039200c61003c019102580c40c90005003a04041213032289000c3d4104804c150340e000f9041200189940c1c1d82032000c0c0074144580060803001204c4030019102071071195170245907030000c101031038443e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 399316825 1250 399315575 399315583
    0x3060f0613180c03060917040b0901080a1103041a06031c030207030e120309030c0d0c0e07020c040f05010513060b0d1e06080a050f0d14030901150b0c0706030e 70
    0x70000d80c8001603408522000100c00780505002604002c10820301009102c5c107500011446405080e510200d0804240c000300607119a03c5040d0b600c400a001c0da240e150300c101c0705541c129008520210f0207140c005d00307009440d4401c1c0c4044460805002074541c0407141880d4455120f8021070140240203e000210101c140803c0b8410f1300b0180d001a060341014016090813110301c10152800941403566400956a0f07030140484600c00c0c400d6185115062500c0c050000f00180d11407a170f1642245440a00400c0100241185056000769420040c0e191100d21501c2060b074401c45010440d07500d01410710a07402c25101a80080780d0511805004040d100c000321400c41c001c00100045402414021140808074403401c401070070304207034000410000004514003558000c0c400d0b60340803000340001650301c50b120010500421510504001c1c2298050301443e0b10841700000403400704140d422341032240c00c0a40122101c8034011170b80941010b02000354030082c09190800b0403841000240d02991 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 399318075 1250 399316825 399316849
    0x5180d1809091401091506090b061603050c100207020a060c021e0123030405160e0a200c010501030c090908091207032f0604064a03060f06 61
    0x254039194040b20041080c00d100c1904100f014200801c04510f680c9484212401080c42c0c031180c05041080c04500c0c908144038101034005d00034034241c03401e00d04c001c00b08450350341000d058003404018480c54030224828818009410340c65076005a0303c103140c2c4104082d16015400000c200028403840d40016106c240510340121002c4007941c406007580c900491300510032800304c440d4102c00308102e105010360300018500540c481c84c146c401d40c82d00070402d0340c24188288160349880108201040d585015580502c070041f110703030300c807800405040344085140d0b440042d490720507030341da41c0c0108180300702c2404c400050040700d10244083e5030b040e00c407480c85024a6903010310032981580c1c9035240e208100100b00045911101c001d000c1c80c83e55038040d40d22041c0c20700940b040000b50240210a14241d0104c800b9100d03140c42d0102017851115603800c0c89040810380311640241c00f14803a801c00031141a01c420000001c1041d81d01260b803509040c1850b00c058800f105a42c0ba41c0f040c0520b5640301c14038102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 399319325 1250 399318075 399318089
    0xa030809010b06122415030c0f070516080d050702010809070e0903030108010624030c0c05031b010e010b010903020d0c1a0c0c030a0308010915030605180d18 69
    0x8549500644900500b1410040e40e441074000640c42e00440c220b664440c45074003c103a020410380301e81a2001041d070202c62030707a80d1120303030810011409200310700955044400e001c0128182152500c4085059004240558480e441380d0b0030881020b150402c0440981203190203416600104a8064820702804000074103003d1000c002421a0108004000040070303082000f441d030b401c00b00d4605440b94401e0040182e5542469408603859040b0801c0140310b0300c44844113911035080e10000c4000307011108401d41004042007071100414401c00290940360107220840e280181c100c007286085498074000200b207a4104800c0d0503940c0c2c0c0040c40501141e4052710582e298803418038203414040c4094000009040c135a41c09803044001c507134040c2020350440800c50b44601800400c060360ae42c9205001400a01468018130082e00e103504130601c080d81d0b00d01034214040e1a0b50314101a50412030751201c200402442500450004110343c0204e0400303411b00280c905142d41011a0000840c01303142 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 399320575 1250 399319325 399319337
    0xb090109090317040b0f15061e0903070303050a0207050a081e03130603090c080a050622150906051b09090403050c0a030210050c2d092101050f090a03 66
    0x181414003e00161100307099000800600780341c1464000201d020513074446100054a00001e5003d000030070315044040c0c0000c1440341400018003840e2600ca45203c8034820210042c02968940e807004c00006010354429143c641e110580701c2c00c0207260201d83e03400030b4401c00c50403078100010300c40030404403039401020140c8d10f21060f4801c60180b8611400c80540c030002010000018500c0e419030011102a101d200b0010080f9aa04980c2e80d80301d0503020090000d4219101140450743d09151003144085100d141c5030402031103442c2d001c185c090740c800b5050140d850343c1c000c100700007442c45255032000d0b0b80c02c6501d41c00c6920070781901d4203014654070580a011840049000d0500920a40710280c1108088441d03151240c43c0080d15000c2c1c000031142000d080c10003048203504004c003941c002000c0b01d0042030b0520070020000004ea03003541d401d44550300040102d004591142c03944031014503803110300240074040000020f421034500800340045c22907400c0a0150800c000f0590b446080c1e0186030038 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 399321825 1250 399320575 399320591
    0x150603190f1109240c01060602240a0519061d07090303052b0204080d141920060f0709060906050301090506120303130c0e0f010506071e0609060507030b090109 70
    0x107011130f04290303201512890081541c490214054003c941603420b662300740c4808110fa0613081c00c0c62580c0c0c02142c2c10740c4045000150852403aa40400d41c020510900800710100c1203034264200c41484c0c101e00c1e00b4030030700041da01c92500c51610342c580014680c1b0301102081e2130744d10010030038000c601d42109076000340c4c0b1100141100c2e218030b809000c02c0914046680b40c0c0d440c6d291f2551007269410f00d401186031580e400c200402030341b0540b203a00ca640031f4a240c1c0040607082c1121883c003010320b281c042d144166140fa000c100c040000c070b4490079450200d09620f0030b24003405010138559074018070401441c0f503020710180358010250313411644142804202500c0e060001180340d1021603242d00c0a00c0040200804a481a04289591400351960340c081c0764139684c544401035000c40d100010003202c100104540e00703040f0020a616405080c0c11072022520020111070b0302c0713240d001611100d40b00c854010901c807161040c00d401040340e00b0100410515000407031030705a0144502e61415507100c500c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 399323075 1250 399321825 399321859
    0x6111e0301081c1101060f03020415050a050409020d12020c01081303050a030c11060708150301090c0b0a0c0f0510050a05070806010e030a02150310120b0f150603190f1109 75
    0x1213000300c2c2042d80d00a0020341d46a82055005100707134401a4801e504102511268020011100c0f007a940080c1040500e45e00340402c1c800030b0b01c841c41049810503591604100485c1a280241d01740c5001c80e40604900012400014140d1201038100c8030744d40301d6055017030300180c2c01104032600081c50f420003141c811812081518034600c070420700f40480c0514410440d1040d07000404521078040c0c00c1085003040130502c2490308a8560f0900184601e8008500748482c0d0b070182c002e08484102490900502d48540d62446403030784144400701d42c19408045ca00c00031a206e03024060f441401c0301e004114925040c003004084046c0030740000c1c144200350840f480c076510b051220340030540d0058203428405c44111401001c65000700c1d000030008602207001300316100c6801e407108000d5044040000c49403244e54a51101550241517150004a040d1800d240c43c0c45000245111700300c1c84c03a0401034400c002a1140566103031080180483c2d18220201400d100c40c80c1c03d46042100942c3d00e05000c45021103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 399324325 1250 399323075 399323087
    0x120305040e0405010e06151302031503191505040b06131b0503010503011b05040308030603070f0305100c020c01020a0803090f0f0a11040908041202040906111e0301081c 74
    0x20752140142420001805415003141700004099030444105584144480020040c03045000b50b0141e010071813160000302d15000b4541040320380740b035800c4903060200081c0c901010030404442c0c18500074221018006d071440c24480e09001a68140441e01e400c0d40c07000003100005001e83d100e050300c030f10341c0181850b8640c40210040f02030b0b06002040c0042d600e002e0021b07002407207550700c01d43c00c001c00160040d02d00b4140c0111440103403030b1a410300b411951142c0c04c2e5000285011b416101d03a0360009881e18000c002100194022005000312200441d458019202e914400806640c0320300703d01d42c4103990001d10700c00c842e50440710740c0344c0740c0d1200006a800e140034a200c0141922803d422002d01030780c0400c44001e054410306850380000e0750003041c0001e50310364040207002da400901082202c01d0b182032000100c0d5100920001d4070b610f4a94680f8116112043d0613120842c01003050140341445148075a005417540c0482810743d07240200c800d0b50b801f04081034151201c0e035003281341d1035035000b07007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 399325575 1250 399324325 399324329
    0x3051b0304060c020a0f0305060f220c050f0a03050303180f0f160602070b030610180b180909030a030207300905060c0c040513060911010f02030f0412030504 69
    0x502500e540380c1c2c1c1c45100901c0d590482005a11a240e40b0200280649a03a0b038102d0469902070041c0c41d8940c0e9022007007202d0500100b05583c1101119504404003c103001c500e4406d511030170106600500703200512107a40741e0710348100e005500d079000034400300304000141c070b9000c420070300035841f03031101c000700b40d0304040040c03a01c1e010f6446681c207400e020550111300440d042000c4c069400c800e640c0c0c1c0f102265601443e1041d230800c3c1c001080400c1c5141040060f003441c0d2003c909021440c42c1403283c040d02000302581c04220207030700118801c2c0c135a8110b6110b0040440b0300b120081c2031410700d10f100503228429004120305240d40040e401d410403001d1141a4810039014503820140320246031385c500c0680f2a422003a001890b06500843c2c2490440c040c3e40c017048181005140180105003440300a002c098500c034003d410340000e020009225001d07450f41031303229800300361082038480005003505004100b04001e540051042c14266101ca60583d0200c50103080d81c09038010a03803c0c15a03480c03140d6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 399326825 1250 399325575 399325627
    0xf060f0106091d0c0306120f0f01050601170105010503060105221a180f03011806020c06160e040e28140d050706050c070b0f040506010b0903120c07050a06020f0105010617040305 78
    0x141c0c09140c0003c002706001c005124034400038042a524040119040c901003080c20030345030f0585005103d00e5201e0350103141d102004ac14903510f4800d03210b401d20046034040b425500e02c5403400310140040940d0315140e6940701e1030040e007581050300441c001c0c04c50b00445040c07540180182c214450300b0f40e46c01d400c00d40031049111182d00020542c3e043c17000180d400030405d09842d00c280c401041c81d94180840316800180c0b9035440382420041c0c06d081002800155540710403900c1807889080c411942c5401c0c4003c2c03c140f069000c132469080c0c0ca0180340240381b45c080b400071500b26600d07018080350090304951802c4e0340700c2c10001d45641d40f113542403100c3c05400c0d005004440040c0400113214039449909004038005c07011590325a980c1e00c540d85280c450b86402c0c03509070301701400031b00b00c8100020140040b0b44032a4152111140c07207102140c15200c09500000042c5e000700300c0140f56034801e12540b070242400c2e02d4146036084910f0380c00c83d4440d1024000404000c0c002450780031086242c20107000e060a4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 399328075 1250 399326825 399326833
    0x30310050d0507031b17060408030613090c0b09040608030412080c120d050103140129040b1f0f0e0d0206071505010e0109061d040204050402030f060f0106091d0c030612 74
    0x1858101156004d172902451044418601ea0101c6100000460500c81c9903c604180e00d99903c9406204402d0038005411602546845010b000201200f0002c0041c1c5044054551aa024001000152034940d07100d804150004c002c2488103018803140400c2c1141c02403a096654890502450718104070a040109942808554403002c2591604964100d83c0501d90480d100c1c04000302c607908984c50b480c00114030085443c0e0030f1286407050903411000940007000000c1c01c89102010401c2c1030000c4000390246110407400d42000740e0002200b009202491410480d01d041301c00c00f150044503074202c040d200e040c0c0400d0510410007008849007021148007014000e0756520b198050180e102030140506050800c2004142010710501c4032017024108002c2e01c01a0f2656000c1c0301c01030601070016600b600602e554005c2441003040041e00951282c0039034200d0317614242000706003051542102c800e506024424040c00041307103051035000b090403029a580d0352101310001d2039164890b8140025406 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 399329325 1250 399328075 399328103
    0x415180e0c0d0c020d0806090a0b030708010f0c090f09020f0d1812030c080a050c04031e1b0303020a120201020d0f0b1011120a0c0b09011d030310050d050703 69
    0x7040e2406000c1241d40454180f02c0300d842400e05903110b60700c1d4101d0000054141002940501d05401881c0d000301c03080c14001500034051001c40d0802c4e206811003032003691509150a22400f00d8400e01c2c4a001007480c007501c0090501900b0303201c1001c18403840540365004218646258800c00441c0c00d02d80c0c02501c10072010315020b1034910414441c2c10280c44510340c80000e007054502a028640780802c0554031401c0e26136880c0d42d071500810740035180440c1c9001c10322010000400c20403140200143c902d200040403076061a0090b507980e17015806881e04ea003060b1341000041d400141041c0c40d16400341c0b03d10020b10540c58200c1c0240900d6400c99075590400d0140c0da9000410f0703101035142007041c1d03003034030081d10354901c10380300c1402030082d180041c0d0201e001130b241c02c54020054041100545440c050791541c0d911026903446058030500400e966070341000ca1502d00401c2c4255400d088407014509510345484204440235580c03003440e0050105150400c200007007808104051a0f00038481c0c55964 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 399330575 1250 399329325 399329341
    0x50a14040b0f0f100512010b0301090c0e0a0c080601050c0f070906080c0603010f0303080408040b071202011a0f1212030a05090d110307110105070c0303080a0c03020415180e 76
    0x307a0140c50902076895000d02140c003080c80011098841c0103a00501d1070601d20f00000c0c03240240390307018641170740e540c0d5a00201455a0a00914580900500d1520803003818503816084e0180301074019801c2a24100c800015039800100040d8004801d090140c1c840800c180c0c8141481701c80c01c4c0d800b038640030305030300412615016442481510b04c42d1049030003101e020418000984000e0041c44201882c00108100103072164200346d901c40d04c200103a40c249079680c52004000d8022403c111440c048098a2032406642441102c400c0d00c041c1201c961000007881c00703d5441e12801c20260301820031400c40b203031907050070000803c1c520328240c0640c0c3d407858480c14860003004161418001c500510540c9148503104545072501e07a0980805107180c100c3c142d50720400184046806030601030140110700214200405070001140282ca408030703d4500820002d0841c3c0089080da0b040c1403050006001c0714010503403843d200360b81810141c00750b940600d544a00b50f0010761051740f50b4280a41044001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 399331825 1250 399330575 399330593
    0xa0b061b030c0c0409082a010207050c15160602030601090302030a05070302180705030109020310031b140d080d0203130f060b01140a1b0c120308040c0b1c050a1404 72
    0x4a8103542a00d041104801c00c01c8161521000d01801201047c8071034140b07003801e01e640001004403d04190071412013001d5003403ea82003210144c1c1d2030341003420140c4081c00c0ca4901e903000200303490324852500440070302c83d00301500c0f0141c010b1700c90369000c000900aa409820410080c54006045a165503154580705980c1d4515000403070140340c044403101c4e011110307188540c1c0200104d4850608603800d00c01d600c0004d4000515440449403a214008041400501d294144e56030840340d00d40607a00b00481561903542410405016040c8500710001142459003561069400a0009652511600d641c007a4070744601d24081e100200fa80e92550030030420754448132201e1000c2c2c0381d0400c0143d84241d5500b2034041d14240c0750120368221075112440211408142d103461240c0b2120089a0716261a02021503103084114013003144142484188041d0080c10f000421440e60410300e0a04c92141c08035006480501c04411705c0e4540000c1a04800c0700e070001160611034102d80c007664505400c00c6018 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 399333075 1250 399331825 399331837
    0x504080a080304170a080c0c1e0d080907050a0e0a060f1706090a150504030c050115090605240f090303070c0311040603020f060c1002030f01061805090a0b061b03 71
    0x40001d440f41e80384c0130f00f1020060f1071903503890340c980307002d143c0e50005c144416034011441c54a45002d11140740303e50380f001c40d14658480300020700810690458007005080007001901d041241e43c0700d000708105035030380c106044007554440400c07a00b0503112110194040c0242d41c000f00c0082c2042c050124000031034000603d10000e02c10304503002c40d1140c941068852800303d402904100e0103e0060100ba400d60700196040340c0f1034944080645e01d16240c280c2160004034907090813154040c0100254a941d000c2c01025000459030070401e41e844041000041000c070b0301e15141e4200c04240d07103411002d0b2600780d80d42c40c08041c090300c0e5544020f18003680300c0342031400110382201900c82c401703055040a11806054030742c007400f17544915078410100016500100e207202803502c21080c038030303544018900207140030346e0301203411354081c0d41450b60241408851134a100e0500400c0d80d41000300d540c0341c03a0106c0c0c00019086000030114400d0011802900c00c121300892280c9403070000d030340036100000c01016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 399334325 1250 399333075 399333083
    0xb07080f0c031905030402090c0c030c010f050106090f05101b0f0501020904060915090e03090d110108060316060e0a0e070c1401090c140301020403050601080303190e100c0504080a080304 82
    0x5043d42108400c1d289800240c070080c2d00818107c000981d007148000c0103004880110742203e041c0f400c0010700309e0a4031a036002c44203003981c8a1004211440c1c010305104050650350308401841c50078a40031440810030200040204802c091300411580d07016414038000341c3c0c1181d40905403882c1410154082c1d802200400c1c0140c1c40c10b00d0000300640305114120955401080e5030902c0c601d001c91000140201c4d03a8071100c14041085510b01a0b03541c040c40d10702041c070070058481c1101c2d140d0009044407d004203502d000340c000c401c0001e03550100e402460f0595000b401c0080c5490352000c04500b03060b071580c1002440c0c2d810441881495070308090081e246500c24810740280f060482d4500d800c0c3c8010180050198100032030074000300070b18140c07a03544c104014000500781941c80c6c031380c0742c640b070001c0c0d01c4440503420000034024040340008400031085810041402040442060f45a45543c1a0f550300507007999640302552440c0b14004a4009140c5c85007281d803c0380d50b0341443e490f01e62007920211 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 399335575 1250 399334325 399334357
    0x60e07030c030c05060a0e040e1f0501290a111c11070b180f1c0c0315181211100608100b01051b010905070e06090604060f0b07080f0c03 60
    0x3007900e403120807121b80106694440d010884000c041c08050f1550a100c021540a90364490703c050b0035524208180203004c440200c1c03154501802101c5059181107081101ca1103441000c40840110088408013101032400c0b00c120020241005d040c4013042e0013030081141c84002c01d10001360320075501811441000c007911402980c0e45640d0b00980f01d540343c55410480d0b0010003142c946811035201c144488050032078038000141500c0103c2c2c960742c49900312051030b0450414024028074000c030943c604004a02001000e4a040203041141401e450003400e60782c1d402c0b150030030340b48036880c45180010341d038080300e00e80c1802021420150509010348101c0b032240e0b102c00c4903824002e000740305c113001c41078544d146010007003440001185503d1100000540d00c2d040903c0014004200f6a401010801e01e204418200881002600c06001e82003d10032030416000340101940c0b0560344044680c00c601c07840d6262942d19000c406402070711411aa10705001c103900d04884000302c01458550807441c0701d030f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 399336825 1250 399335575 399335579
    0xf05071e090e070e0d050f030c060a02040b040e06060d050a0c0f0201050f0606031e0408070b01080105060928060e0115020f0d050d090f0f0c0b070b13060e07030c030c 73
    0x2101c0c1140148145054804014003144169000b0740d801c552144015018400c59400c03a21414a0003207404000c8466600c0042d1780038011f00144211504005126015440d00e45442304020b010300a03409180404d803917940108a05950300c3d800c542c9540001d4000b030216280803c003000040209844500c0070821801004001034410b00c5490320540c03030b0b41e01049171a1036040a004541d08014075650100b1b0708502c450b1490048043c1c0e01d845103100b42461540d9072201d113400e036000c5d01c1c1030348440c02c10703070510013030003081d82d100550240d024541480c0201035a80310481c8c2c15505603140025003810345811404210a5901681241600c4a4101d8074400800d5401c049030f56105040c032501d0150031921205104500c82c4004298001c158600800c0c1508151100080350a0080c02240c1041c40c1c7d26990041140d0001020020011425003c0c1044029200e07803170140c2c4c006011070b01c8181c002c1c012008022403036028410b03004082d0704890407039840340b40c240d9084803240016141e02c4040840 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 399338075 1250 399336825 399336827
    0x5070501020c0315060307181a0f0108040f030e060703030203060306160c08030712060e04051006080c01030b0307090905060a1b050a0518040c020a030315030807150f05071e 76
    0xb201d100b822002d40100f211801964031402c111102801d090b5050044c80760000c0c0d005d0b00ca0044203820441c480700002c401041001c02142048252900c1b4017642c4c2d0880d110203a60f81004020f584141c02007509010f40303e01c4d2400705c4400040c4003500e540480081011400c2c1941030707003c2c40c419101682222540d413a0ba09092030030201d16014080010504a109030010300c0070805036400c42d6560034001c107240e8000b5124403e980294004041d038031100d10404c8144941000552152500114208103407410080b50a4450802414003810f241d1503c00708203041e1410001580240030303148007084492450f140c090745801d001c0d01c0040c1130324140522148158030180b1036004030344094503010b280c4044000c0550b1140c0014a0280c036858410b0b99a03a000e4441d8015075000780c0360755015000a408500d809021641c50060500e080e17004c42c00300f0300000d881e40302110070168000341c5107140400743c2d42a442c086d110340c42d059030120341410140036940b50044011440038040c00ba80c0c00303200c844200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 399339325 1250 399338075 399338083
    0x60a020301080a02061b102f030c0c0715050418050f2701110a0f05041809021c031e1110020a02070f08071d09150a060909060501030507050102 63
    0xb0310101d03401400c9018014a012001054107000031121640700010164069040940c0c05007030250050311800f4180c0e030407141c600c401a0710307141002d0809031000018030022081c00000c0a40f4080c07540000d40482245080040030010180c55151450032122468010900c2d00544602141c1c01058121a00c1601c2e20380201c6110395958400a00c0c6951342400c80c1d6000300806842c001c0a005404a40211803c20700983c104030581c5c0140301e5030740810001c01080d507114041000c041060070302040c0b1502240418030300e441c2402c80d00100e0b4140300ca00000d401c1a4000400000707a800074101d000c2050340001c503200c4a10020318440c0d01c0864000d00c190352884050100c400c0e0b136000041c003007403014015800751800781034034412120460380780c50100d2500d44035500918110350000d10200300907110081072860b4034104040c485203905044804075944c005580340608802c010b100050881040740c2c0c0018000c180101e4144000b003881d003081e1008080c00c0c0400e07034241c02102c40100c1e03594000a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 399340575 1250 399339325 399339329
    0x406200714010b030a0f02010f05161101110114011214070e0a1104050f010c080d06060314130221010f020703120b0306011a090d0204020703052206050409020310032003060a020301 79
    0x8201180911b1007070740112642c0004c1d05240c818080c0074001d10500700d8080c03010b590035612072b9141d01c1400c0341000016120321640c0c04440c00681c141802480000703100900030381111192040d0407074614445c903103180044c001940610203485221000500e041610641d2401040384200c1040400c010401064403445103000c1c3c3d0740c12a15100342c1e210766500c118070500c01e060084100c1820840c100082105451859210000194490349403c00c07110012000d581c1100e0100d45010914a2590109030308058441a00c0b400e0362103035180fa41454000c2d00301d074644403420202150340300800d160103403d80085103034074070003280341843d4120306040004100c1c3c1a0760390b01e44500013810100301e500210303501c0040541e03003240b4258010401030716a40090071301144251121500c070480540703180640341c80c40227184001c5602500c10002c1903004801c940c152142200c000d641d0b03a0300e2448458070300107194402840d0281c02034010064010302e03503d8202d060030481c1a201c00f034952a44c880c09078007081c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 399341825 1250 399340575 399340583
    0x306271b060c010b03031305090a021e03040602091c060e07080601051e090a06051201060e070804230607021908043c060e12060406200714010b030a 65
    0x40030305040c07a145025150045105002044030104540440d007941c100d00642030501d01d04a005101e0303403034559030141d030002e0b81010440c10003c154101082c06e8a1804140f1402480000814244100794040361464000900002064000440804480091a441621517628280e183c03008400041210402c44803480000c100e5642400100095050401d44454030190040c1521800d40c8490005510078010728200040c410310b820b040c00b411030242040c1e41c0d0303180d1400409200d08038050071641c0e0402982e01d01000f0a654616001e070394103000d60034610100c142c80b030310512080f0000038004e02c20302e206da0968000303ca408610040c104600c0c88000c00301001800284076802051200c4e290050580500d034585151814203100c040d184204050b11041403544180126504248540003d8005403605031340da150300714401c0c0c0c6802000d403000b00125110303251400c2041d40c88000109a04486200542d220701c1c9291480070044d01c00740812155081610034101498081040300910b508 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 399343075 1250 399341825 399341863
    0x2d0106050301210228030501060b040303030e0f250e040b10060306030c050d050102040b03010b0c071505030a0f020d0c262503110d0b0109051507061802030627 70
    0x2c01a005181120305c210b0344098040002c0890024000e41c0e00606044902c1aa01c60031400c0c0141600d15031609561182e10680e8174510701080045d46210348032041001d2010402c403034000c1e0110038603990104061043c40000d010a02000e0959140a024080302d0684a1035550000350290303401c510001e019030314014070810841c14911001e1004511400005203010303100c5040084030340003a0801c440206002c0b82503204200200f000308068010490740c80c7d01c0140c044001401444020403c00d02603813241c00700c0f0703448040e42d01910314012030700c20f040c404000c0d60080144514140d10018407414001002041c202501e10341850055541105000700c0b19001d00400d2809044540e0641c10140c1d1061500714022220010300916000c508003c5403130142400014410302c42900240d115180000901c0e8502e1400000c8410f05940008042266440814200d0070b440354a40060f405004207010014144104040202c9407001680c040b211800340903c0e00e81d0718032004a403c0e290b400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 399344325 1250 399343075 399343099
    0xc0905010c0c0f0b03070801090b0a06050a020709062709050d0c0302120f0c01050f0720010b0a030b0105090112050a020f27090d1103032d01060503012102 68
    0x40700300d9106101900805014034100d070780385101c014540c1c555200703070551070020042c410003d40c0f0031211401003818103018852038003014005440611030307111710f005001c1c0014225608500900070540205083c1d082000400d655240401817040202064070740c1e0b800c0d011800a5071219486404a8207403c0300040101000c00101030b070b171400e1078400035070541c812000303405038605c110002051510424034460f0340392080c04c140c1500751000030785092001a40030b8100009164006d40741c40c0000d0048129400b0100a192411b0040002a0369181c00c1301064201005105803a91180d0484105640c4060389a90b248078884510f45001c0e002045900091040c501510f8815000085e1942c02002501d05c4038021006030303402010000f40711541c0d40e51204001c21000240b114010345080c6080c42d0300d02c03062900710991a44001000c2003e09030000108052510141010440c901003210300d44100313507103443c0003600c17541092040d03c0c80644032079054010150007442c1100000e40c0500b0300401c4030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 399345575 1250 399344325 399344327
    0x705040e030a0516140a0c1d04081c02130f060c030909020901111005040b01080c010903061107080703080405100908070201080a0209040c09051002010606120e0c180a0f0c090501 78
    0x7a00401075050004d00c00c029a202203504100340e581c4804101005022074030591410444130155540010314210a072914040f11107954010315621075440403510759100702d1020f04c0c0b0307840d88030303103035105c04661000c608038402c11a084190310a49900582c1181215034078001100d1000a1201c0100000c10340b40c000c202c1c504094000d0002000f050610316001002c20144625101314003841c00c2d0f1a40e00c44080c0420300c42c0300e6030241d0141c400807015201110035107002800184051000601156403100843ca04640d528241d40344203610a070b65039690403040c01c00400310034007900c0c15034250041d43c2a0340b14442087c4617a141d403681c080c1e603050030500c0c1500150346084008203040d502d59000c01140000340d0b513901c81d2445081d2a0f40f96440b801d800c00052154505084140d1020342e03151020600c140d0307400144d130f00b1610b4140a4003080341860703a080541001ea820251940006070800e110720784141c0c018a02d03202e05524041040b0801c051108a0203503050900c100f80030402000c0184559 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 399346825 1250 399345575 399345577
    0x6011107060e1f020a200d21030b031509150903031801020a12020304230d14070b01053d0201150f15090314070305100b030706050a120e010e0705040e030a05 69
    0x7000c2964200c41d0090510010650507d100700c41203c49409280300b524943e0030030810102c202c00765103403c03c21210520701003039440d903109948108600c1c43e20300180943d0010091000e01000210700c5003050305102c46802e03038981081d201c00204c9080200910b500303031b03814030a8504648003691611408880203540390300a600141090302e029406a842d40025184486d6a07d18034100310020002c009800e400101340d0510041103100d080300c1041000c02103030040c0c2c07015040d164110303030501011180041c032007115800c00035032082240c2403070350181d0104001007500c4500a00ca400078000303884419904010800350707014496151040040601c00c80b810f0b220b111116440e1030400080f42c07601d03511458844031465505a8060788080003e201f008001c7c0825480d0340000c0c2002e024061000000a03140d102c0c41c01054208a400328101010134450b82203e107a842501c1c13070400280d0342c50003d9a0103022245058a85031140d81800201401d10b803061a2080c0342141c0954240204620100da00d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 399348075 1250 399346825 399346853
    0x10506031e060109022107050409200717071415011d180709020c0102031e01030f150207060c1d06120a0c0513080304060305010e01060f0806011107060e1f020a 70
    0x4071802025060801b080900300141c001d002c542c0b5000d8031a0314180c2210b064882194041f611003001600351045541c40e0820303035612680c0401c013040c0700c240c50300c070b1510355025044d00944900500c0381e0f01c00300070a0115109103051200d640038401aa02c0300c009003280e044080e0760b030f01d032000b0b60400500c442d002d00003c9451491940c0c2511100b565603005501030b40c010200448107a5400002e01a240349184c818036180a01d015032286190b241d9161022000e50003100038202e0807c291820031000c1940c0d0446800c16071010007080088105d020040410144101c9010b24107a1500c184c0058900704050341d01d070355010b03011100b06503112660700b0058260711801e44240401030089543c1c5506030400800607054280040d6180d13071520740020305031501079100c2c0154000100042c4600c9030b1145036178003810214184240180c5a003001203d0074030400354440a00e004050022600036401140c0d15080101128694a40d10007210146904103509000402681c4040700c9040012225015032070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 399349325 1250 399348075 399348097
    0x70305090a030e19080304090b040b1302092d03010c05030c0a0c020a150503090d0302042d080105100509090c0120010f050f01030212010501050a050616021002010506031e06010902 79
    0x121030b9a245440c4040c03d44c0c0c0d500070207455040407034140046141c3d485109414081180c040c006c110000c004035000240b0792101c0c003032094002440c00d042e130311100006001c1e400388483c0600e0322810342854800700040242c280d84a0350800e00d640860764410815a402044582c2d00346192014500040c0e901c44504d03d42240c001c01c201e10b00041c51007003681102041041c1d034540954038500302403000d00749114500004141481408103001101c905541c2c00b80402010700d00c504402c0d043c9105000f040040e50201c0700543c2010200304600f00940640b208643c001d5a624442d034070b4840d030054440c1c141c40c5443d030010391288048910700340702d95101d09150a0740c200001d03142d0071012a1100f03840045604800b8907250200400845c00c10101160103000104020003055041c00b001034445c64040c0705d1030b0310689000c1a40d01e04004400103540300d483d4005c0403c0e08080c50140040d01078030040b02d0140c402e001e20806111710140c1c0300c01a1444142e1032000e01403507030811800800941043e807685c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 399350575 1250 399349325 399349339
    0x2301030b180a08070506160807050d1a0d030504060e060319092a060e01020307030f0e060c0f06040303050f01030f0f0804080105180d0e0627100306030506070305090a030e 75
    0x2c046400d103001444501c1c0140c01600d510714100e214101ca60000d8111901040381103010407502030703401410f031510450145008140c51485000c80103032854001d42055202141e00246020035400400800494a294881e10303d1122030a0422201e40003c658500408581c4030307810500c3c40c0780303034042140184240381684010784410200410000b026128802503941400240123041e0000010b02c190303002440198681105650010030805190103120309200141e28112550380d80e030000c1d5a81401810103d6040b920107090141c0e0300c842c191804d0b03000c00e2030900440e8809640811280c103885d08405100009000e56660110a0380011000e4440800910001c900c001080c001e0741d020300010130b0402c1f40145491030550502488440305030038082c1d5160b0f03020550300c1e003405664050980030400e8004400f410f401c0601091460071440c5e02980d98101c1d62800754166012005590160381241c0c419a1035036410b82c100c500c1904e440140780d0011203410002032044950013901a4054850 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 399351825 1250 399350575 399350593
    0x20103021e0702034c0f02030f091204030b0c3a020a0e0f0402040b04060c1103060c07061802040218030c100e060c010b10032301030b18 60
    0x68401e82581c10940c4224500004809040d031030100141040840240080000340c40850304895102c4001d80702c0d2501d50101d40541c003211000054110800c9a1500050290840a1289500950044860f0b40910804002040b40071070300041283c91410201c0c052460a402c40d2601c2d034420300020301c03511036032030100035042008030512400f120305000a082212401d2904d40355480340c166010910b2102e41c0b041c82540000c960200c82010085001d56182e0050410031001c24068400c503080b001c201c030f0f400203000402e1580700c10810209401000e986044080e90743c00c040e1250030907511000c0b062418058100850841d0340200c8503281030070b0420102c2e8402d40c0c007040981c2c210103044581d264104100c4030ba141030034810500740400440700c26841004501c40900710368003c1c003596010799808502550b500109502c003600c04c4030014030301c0c0f9210002c3d040c020054040880c000806613070712800200b14000050480b03050304d0f40420024400d617140c40c20454203110380107103422144126800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 399353075 1250 399351825 399351847
    0x7061d012118060203060906091b1605061006120e0d0503092a1c02090106080c0d05010e0115051614010b0a0b070b010605040312260f04050610030215030402010302 72
    0x1400030000c1c45000050717103a00c0e00504010004038010042800f4035904410840d0030050319246801c58541c103100b058542c4603044200c00700c4280300d00d00a207548500740c2805821038801131a07500f210b0319a03603451151301003100c0d18000d541124211401d680d000b01010311155008202650b8400200c1c0220b601d4a141e1020b023139580303007901c80c40c4110305211360031003240b03400c1c0004180108800c1e41c0c91802c02203040d07030104403041c10510503078040012180110f601094800d04807094803040c40c5040c409961a1103a5401c954400c0c0b04490110380407a15041000c1c0c041e20664149030741314004851600225100d8200a4204d2030309a281035581da102c43c19290340d5454400054020350320001c0d01c0b1003417842c080351201810382041c810b0000500040000504811800d41e503403445140107142150f0840d540580604040282c4221030401400c2000c0d84448080d42032049006004030350690700c402407580302600d2030303000194002030440b01040d202403003000111f40161061600604e040b500c000e03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 399354325 1250 399353075 399353111
    0x203090d15090b01050a060504050d0206070204090206040b0a020c0924010918050109060e0108060117010213080604061b0215180604120906030506010c0f03020a06050907061d0121 79
    0xf1203415505800503c01030402c5118000074000c1c504009280074180030025500c8001c0c1200244144000151a011506ca5400a01200c2c1c2d000e440d480c0c40d07a0304c4075001070035a0010040540107209050240340140b405d00d0b0307841c0c0100d03402c03004a42410110740c41031035040e1451b81e219060021100d0f000550307518100030080c6070a034441002590f541040060010f0b00d410364080910520480010320035074a000c1003c03811642c0001602d01c51403900c0100078060701504526512411311030301b00040c950340c04940345103d0b6100302c3d0100507001d64011884e18501440403c2c40c01a84848526000155903646c0c1c1a00001103018500400700a032405626007501202c0c101e4802c1c0710408004405500807855030b01526107400c051090303107000e000081a540d00400041d00c5400765203040b4040c0350003401403030300082d0007000c00e1050f4a030002501d50340d07901c40d200c1d410020f0f4161400f41d1895681c80f445a021040c16503030b8088001d50554151005080e0801c3c50650503500d03207400c54014000d40b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 399355575 1250 399354325 399354341
    0x9060414090708060105031605100318030f03050a05010803030a09020303130f03050f0c01050702040f203708060109080a050105040b010e06012106090207300203090d15 74
    0x7400038110a4140340709103040a034107034411030085d030002160303030360141c0702200075001d075402075542c55080003508104030081c110500c1c2c101d80025524102c40141a4002441d40e0711403c651014442a1500c141940480d01c00741b1800206400034404a403021910350042e0015a000504890406105884424410903540d1041403000c1e0340d50b60400030000103100000500342c113000030340210f452100c0082c080344226030340240300340d41e9484801404c0c0b100741d1100e08071036100d0580c01c80d06042c802c102d07506540540288004103124043c81d1042e081ca54413242041584100100d15500001d00191000741025056506001c100800030401410400806001c00c0c041d030000700340307030400742008610188183c01a89a14809030208a11030343c01001c0101034180c540c000b10ba46c2c80d403101c0310780000d10703a41e005151090700028004050040040390181d001603160402c00c0b000002c035089403480100d842c81500580c0043c448140b541c40c08801c008400c60040784030001c00000c00da031000c1122240 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 399356825 1250 399355575 399355591
    0x3020c1c0e01020610050d080c100c090801060305071403010216050307261608041206090501060608040b011811030c0d1b0c06050901060906080f01051e010509060414 73
    0x502105080e055100103207120904003800540101d0605180d038803401006401024020144103140c1420041600e0848420180071000d0f144130480c0c5180d134802030700d05030500c2c1c4002071845402050b1980107219440c101d0741e01c400100109460891020004864585800e515542c20320802000700c184401d01114644078102035a550039480c0f40c0b415075410035509a0702109200f607032840030058000e089840b410003100c203901032000c017484e003035000d0701c1fa94000c00d000f150650f1000080080d1500040d5900780b0a400902c0600d881c1e00d82103c0d5904115409409603400c500100000e210040c02c0d580186d002d40c5001c201d003c000c90b0040788552007074a10540503c40064020f040440c03e10842c501d01c000c1d202c040f41d40c82c10500340104030700d420402c080c00300c03991070300807030381202c0254081c1004100700c15007401702582e10340e010b90716101c17010511f43c00765003413a00040c1c00101c04a11691400c901d2a650102c590a007803d02c2244d032070003490f00742c005982d001c0300b1290514403180c6520400e44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 399358075 1250 399356825 399356863
    0x319050706050114091302120d0e041a060306060c0c040501031406060405091b0f0a06030903090b0c030418020706060b090a08011a0904020a03150f18120f03020c 71
    0x20070725050302240c030140c0c00701d510410310741500c05507503070f42070042d940014820700955003ca910380002544d40b5412101c40130707244240315482c80010741002402103215407c95081100e1000411414a2082e82000940c3e1055080001400714940071001c3c6c0101403a0358204e809210400020400300c45080c0c2040d41e1800c440754101004803010000b0b194001003c0c1c405003c03a050941c20030f661180722a0880e180200c50240c03800541d12208110300700c0d11001000302809590305d200107002420100416400104072000c0420040599401c4941e8409854000e5280c2440e0009110100d491841c2d48000c080e02003000d040442e8683c0280030180010084542c0c0e2100c08004100d006c1e0810703440015244d0401180349089005800b061240000c2030721108503a81c1c3d00d20000d10301200c1500014905046d0751100f04110b800d03a0702140c03103101410001c22680004040c00c8502c0e120145000300203800210340c0c80040d500c940321450301211241809070912078846180d9041070540c000444881390 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 399359325 1250 399358075 399358087
    0x10c0305161106010605031302040501030f0303060e010e010303031109101e1b08090307150309031709060a0f1b0e0a05180c0c100e0105090c01091d09031905 69
    0x80c09a031044858078035400c0c01c014000301480540e03269581441801c0070b00c20084000340c41e050322841e00a512a80c0148104119a1203107800ba011910a81d01a0002031030010046400f4102d8403203107050350340e0102010320aa10b15a0124041c0442569000300d1040a0061030b15503100c010840c0081020350b200c038011070320192210b00c012503c220049007003207140000320101d4510802081d1055411146c05559406564046442c14005134062401d4600700b090306184e00c0c1d4075038050300035244250b035210500a081c00001c00400e10540302150250011000301c0c0d01402e00754030074907010a031f400010814020b8104076210b298012488070b00480c0c99141c03c20740c146840601c2c0006000c04540e48503420143c4110003d941788010000950042c002900740d80420040200c940c200380c807c0c0d0300b8007540e40328201e02806058207841c08032031840346030401c0c1019070203500d625051355188180c820b03555501601e00f131300c5680003400f944001d010800c40840c40c160a2802e07240b01000ea41c45403035440e2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 399360575 1250 399359325 399359341
    0xf030606040f12060e0c0109060e030f0d090e07030203040b0601030c09030b0a1a0616020607171309050a0c0807030b010c2102100c0206010506071b0f2105150c0c010c0305 75
    0x205030b0001c185e0780d900101680302242c2c3e0424204c00680e6154a440b003401200a000300c0d05d4840f036442205020300c03903d0140c50351560f01946108c02e4501c42600d618183e00c900d4820780a900040e900142110341c00340010716954030990058560440c54a410920f9a94071307102c020b500700c411b0300e107512b0385500c0c0d841d00041020741c6407822031851025180c40345040f10035255000b2048401da002441740200141000c1031240d421355000c0d021050495072541c0340801c07549003031401ea0500c11045103a0421000400c000f20038818900f00b01c03070340e03140e9104942e61244118000c044d5640d8072411701601050034404203808800000030701d8540030320a9000e250210b80640342c40051031036490000e040c0b440c0002e070f0560100e201070448400790344950320760710503217404170001100d2040700141b0303411141c4c00a10500e660070010100c608864040c0300c0d400b500d0540c2c2c03500700c98614003d820359000c03100300001001c958481c01e51102680310168100100600e4440c00c5d1840d41802400180d11501400700300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 399361825 1250 399360575 399360581
    0x3c07080c12040b1f080a06090312050901060e160c080a050d0e060703050f0106020318150c0d03060909050613140a210f17040312150f17030f030606040f1206 69
    0x1154400d40b0114800d00d89201c17980d4441d01020020314a0761200c981c03804042c0560a006284250346600b40010300c3c3c414040e500801091140da888805000c021901c41100408001400300c1e1580e1460312070603107516400116406502d0359000c11804102c83c00701c020180c0b18451900f13280318003070034003420301140080a9401c040d0280c0b010001040042040320340020868524204554010103404580400a40014107804c10061113640000300142c2d20b141c04141d520800c951030b02c0070400c96840300d40c5d1904949003c08001c0c0241d006002245101000e01e03040d00811b8030a5a60215001c00300314070a00f8003262a104454200905081c403040c03c0d440c01044d0312005013441c00180e0750110f1203004021114158024207403404030750114050620600d4052010001e0750002c0c008800c40e541c480ba400300d4203100c0ca0361020740c4400c005c84c007003001111348000c0d0707045035005600300706007807070074130704980c0090882540b20000308000107400c6520603110008010580705e207494401c540c1460b40903 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 399363075 1250 399361825 399361861
    0x10314030f07030c050106050a08010e070e010503071701090f0b040b0f0f01050906150a120f020a05030105150717030105010f030e06070c0602040e3c07080c12040b 72
    0x5950400e0001260944505040d99011509454050301002c15030800e5030051401c4c0e00010781000e4425004074030404150001c01c10005010203c0c0e4590395150f000030301c00213007070007030360342c0358000181c1008078000c000e01000c035000010b00009048145980e500242c28805101111903168040c02c100920803820289540040d000684010070b250000281030002d5050040078401c81070440030070f0030398580c440c0070b0b0301c141c000710511917503400c03442c00c05817400c10742042d800c0d012400c00021038020743c180e009a5108040c16115542180d082000708110b0081d0340042d801200b006001510228804450f400b00e4420108a03042d5a5410607000402c0c2203442001c080a2509214500e015148000382d02c1e64001401d14210400703051501c0c080300603108580c82408a48810720500100400301000c54000e502c01040c02d0285628041c100200150320044040341c4061100000740000c1c02082e4160f40b15100c880f506103815400001d0301c882400680b002c1d2104044081085504101340300d0343e1003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 399364325 1250 399363075 399363113
    0x1005121623030c0c03161104060f0b1902030f161e1115070204090501060e07080903160f02040203040c090f06050d060b0d0f03020f060a0e0a02040e0705180103 70
    0x190380210010404072500c0090b050011070040081c0a01004c0400d1090b2660016071403c8180c01400604210b41c80007145410107109501d0000300080031041e81298400316290701c0000c50800f403984540300c1e00380b052004030303800b0350104000118055107c0002060020400041201c507103009050503a1365280c071044e01030049501c211224080f1b00079102c082c5074850200c0d20f40141060400382070110b8001da40009410a0811084404010043d0828400d40d04a4580000141c1d1408003c498a28085e19140700d160001c100d2048506048a8105c410900489542075000303d00da0100c0c007280d0040f1410f44a541002c241031001f00c481d4041c4001d40d56640700144031480c1000002071441005d1a001051549e441d141c3e049a0303202d03c1501d650076038114419001d1540303a410069125401500071030058002c1c0c40008007042000e106100140d82144020010107403141e0074040200f1030903201d1b1415100e81180041c140e40c03074129111002c0c0e803001a42d50b8652451030035503102081c0b818001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 399365575 1250 399364325 399364367
    0x30c30030703091112210d14012c040303050c090607050610050613061206050315070f0318030806010201090506130c0918200319020f0406031110051216 67
    0x1010744001140307191407410780c1301b45140f00e2004c0140c030074500c87c10040a0080e07052400300c000706410006920b040310b240c0800012a003100c05409800052580b000340c051441c0c2c070020401080c0310f94812030741300701c00c00c7c8030030310741401e00000403880d8005d410101d8003a4803680c100003d00ca054040000141310903201141008208103100009020038092881004581040703015030032896084200102405020f45181c5161810b0501c23800710200ca180001c00d003800c3e01da0072010705c07902ca4000710034880b4405031500809a076044454000c0a81828110b40d20381540c240411020700209010381082c0c500e842120f1040e103894003819000354040c140c0b10f40381030321500c415525020481c2c8025404146008503c800007000482451008a4107405200340000d02d10f000c00d1144038003511034000c0f00c280014984003c02c0000703940700760200406c00d85a0020205060520b0301c400f8102007a00d0902c10f003800318102d540c6803c04421116003200c00c6540c690101c0301600400d4560310904600c030740d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 399366825 1250 399365575 399365599
    0x1306061e2d061220070309060c020d02060304080c0706081509100b030414030a0905010921110604050414040b090325020112050a0e0f030c300307030911 67
    0x890781e00c0c446124150510101c0900000d8208850b805031302101801c44d452210145245001052a0030200c0c080f40468611400480c1e40343c024080030a2540c0d004003250001549942448000d0708013078822100035500780108002c980d01440089c01070320003591054841d1810010000300001d4943c04036005d010700750141700c1c810b02181a0380d07050f100c40c110510360720744403403900494004d8400c01074051804040b4114490342d610844c800700311a0266200c20a036522440440b6444091444620b0b135108003441c148002200c0300c0e042c5004c1240200001d051503503034001301e0300342c1d01c0040c58008004c03e01001c010400803120f45068104038410011420318142c2c000c0005006407800d212031a00c220104c00303108581c440d45801700f410304002820b00050400c00c0c0c1d110080c0c40084085800740c0651284602c0100e030000683d024000044010b2845011100301800241d0080010001c1c001810b80300d01e4200d41c5500045011707003211ba400084882040c101002e0030350782c03802c40501c81c031024645 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 399368075 1250 399366825 399366899
    0xb03070504270302120c060105040605041b030b04020409020c0304031a01080703081309020a03021b010b03100e07080105040b0f06010306050f0108190c020a050f060c031306061e 78
    0x44407504100e0b548448500316410700b4185c0c64140800416800a1000910a080b80d4004185181241c40a0310300340085500c0d10300704400c1c1e40b000c021195005024280050f250703440790b04902c1e42d980c0081e000628254542a620041e44d1204010144ca40e1000a040082041e0701d80490303a41c94410784841602e50400c030b065621915107100141c400440440c01d028141c1080d4540c03001001050411076548902d014094080d4101141c0401038100c07030b0888000b402c02c107008290f0281002400b40c0000008000d12900516201c0b030942e505100325840446c031014244600c40c003a50080f10300346094584680329900fa00402405541050f0516174200015181d40020702c1d0340c3d84c001d0030030070100e68810700241c0e981d42110712407a0b24103080400c035908564001c250b8040c1c0900841c1078030754010356aa007165844c50240c0c0e40d03444185003040000e041c40340748000c902903a032103004081441503032201e52411400c19800e0002c40309140000401074010641388801800c109140101241070310154 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 399369325 1250 399368075 399368111
    0x5190612020312030906012306030f0106020606010c081e040905070e0a080109120807020c100503010f060815010c050a08041d0114010215130803010b0703080c0c1c0309150b03070504 80
    0x4130b41c2c2d0140d0882e1031140003003060350112558918003e48000d2b107a140042c081082c1400a20544026005030004a0201c0d4490142024425000180a864001c41c06040d9032040a28030117454068018031000c0b03860395403405010b0040b103855079050060440d031800c02000004650003d06e040e85000140800900241d203103000010a80c10f140600d170340d4968090f0300702812a442c20b58002c803e91072a142040e0804003075816146005901c0303400d603444240c1900c003c2810340340c80c01304001014280c601c0d907128039071517180544901c0680340c02e2500b540e111102d030341007904280c000c9200102c4100ca0183c0c1d03068954010560f030140380e08044202030000c1c2d00c1d251606214100e005007032001810b4072841c001c41c289202d92108480d83d5035071350b50101c117071150003513002100000d00300717008100c070664004d040d101c0c00e0706558094a00c5100c4c00c4a1540348542c40f000e17420038141c07203481c2c1d50007017074002000c0c0304181852080480d070a0642c000301414054540c22a41c415450503a00d0300112110305 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 399370575 1250 399369325 399369329
    0x100c0801150c03140f070b090c0d0c1203020715030c1815030504020a080a03181203080703020705100203040f0201030501050a12020f152a0303040b0a0519061202031203090601 77
    0x20500041c8041d084840700c04605c02d01e0222605c07003e0000b492402c00c242c041000340300e4009242178461192803842044941c000c3c1c800058411794040c3c40038029481c0000e01450264801c0c0110b43c003296860505c0c4003100b11a20744000070035a240d00e010a41c64224030306462560018580d080c05034200928401d540c0c840c40150020190788800007021522a20b0103100503010413000c46000000500d0700800e4120711042c0c0752010000b5100000303590480142c200311180d8151215101035486110403802900240700c1520a40703d564000380d080d041d40e01c02075015034001d044010003a0243e0002500382c4006a11440c06104444400c01c4403804034801c1003481eaa040741c045204c0215000000c1c1d5960342e41c602c646a84000041e8507a0f001c440c030000c00c05003103e01400c40200a80480c0c510703100e0104031406481410310500041c1c0e10f90150b44503035401904102c8281e4590b4428140d0303022a40e10750410070354402500811000d500c1e040109140e03000e01901ca017455032400354070160b1501018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 399371825 1250 399370575 399370577
    0x60a061407020d06180309080303090304060f02010f1107020306072d03090206030a0518030403021005090d1b1e0f0302010f0212030a1a060306030607080711100c0801150c03 76
    0x8a980c1c811941c88002c8100700c0d030340154043c0b0244480d4803001400300040c42c000c4022880300140028016804400e80c0e00c03c1081c1e0b00910304043c641a410707125400d220802808655035142010f14425a40c8691b0480400e8070203050b48038403541c070503d490800701415600a10243d42901c0c103241c1d566031200c481003004005075800100071000c4c260007030401300304001d501120101c2048883d62995016608c21952280e00544c0003403004442500c9100d603000207508040c03100200100709026034000c00d1070b80e0010304044080959504c1d11364032001d44003106141c5e12418002000700e02d44006002c0040c4a00080109416217000015440c0c0340c214403000b81800b1200d040c02c45124001e100100e42c4c0d100c2600358680e01e1618580b01c000800c180d051401c074030744c00010b007042e6a04110058910450700130b0018665902c80480c1a034031254010810001c004069072900c0d215841031000c40041e0801d20703030200c4d20050b41c00000d04a07101c140c0000703003008007415521036090382c04150b400040d901 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 399373075 1250 399371825 399371827
    0x3050a0606050f010c0c060e0a1706061914040506060d0e1f060b040302090a0e100605030607030c080f2a181206040813030f030e041d0a150f0c0215060a0614 69
    0x11004205154140d521420b034450681005110040d2b003c100a0311401045034510100302c400c010304110031109000d445054101d034001040b090034154011900280024043c0c0d06000303c0020000a0fa552140d4401207074001c4c400210301d1034042d0910014140070703c20280501414000300700880c0c050345c030020344500c1007400803d140b044150312001c52400000152800c0e000c031701817400c0c041c05851054034081d1141d200000d801c0d5101e03104924050200340d40d4005241c507444089012500e001d40b030fa46a450900b290003030141c81d100200c1144000b0f24550a40741e2010200c181585010541d12900410b6480400284110041011903000346e10041c0543c44280c0030007107024050243d0070050035007002480c801c041c140c006250f50040c80080783c0c144400540c0b28140c503084011100741d10401d62007041d086000600a0724940701d501114000000e0010b2000345040603680000e4807040540c02c101040100081001000c0e0392008080d1a850705031450008018480d00c60138100c0401c00c0c030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 399374325 1250 399373075 399373097
    0xd03110f0904180501060303090e07080f16030b1c021c080f070c05060d0e1009020a060509030102090d080a08130b0714090a030b07110a0b04030f050403050a0606050f010c0c06 77
    0xd803040d010f072501e6403c4402000466100d140c05000e540241c090450a80c29103c002482d4600c50b1014a00c648100409405c1c07030749600c02096819025030290780c0526450b100d455500e42c5403000c141841d81c03280c80888054001c24010f0003160356403602c040700c0000062060101080e802401c440c01042403c1c00582d8602c103905200c42181a42e402180c0c1c00900002c203400c1150498004944601520007030f40d250040d80c00c8810f04844001c40029080b2a4804c810008280908064040b500c0c0280001d440c0c814250b000030403403c440c9034110781a0f03101085d201c0055a03c60301a03039011484103d0b0a4444803103480c1c0e54605080141031208000604418104148580003500c2d071a0801503e4010003a4991500000480003202c042c000944003440032007090300e00103003c0f4010768000c0d014031131640740c40d01c0c00c40c3c10300076115020040c01020480040001c00c104801c6203c0c50040e140041d2207814601040030008003048414100410556108040713131885c07148804170303002c0b401c0c54007600e5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 399375575 1250 399374325 399374351
    0x13050c0301050a1a090d021807022d21040504020301121109100504050c0c16080607261f0f06030f05010b03060d0212010c1806030204030804060806010201021603020d03110f0904 78
    0x407014851104234003003d005102c010f035000155640e182c55500f00408440d000c044c10070f500c6400030b4408030384541c040da000800c1504000c002d0701d2411054040180741070340710b101050980e803081e4000f030484906007a05105100c42e100301c0c40241201143e031461700d0304001514420304040b500030684526039481c089008896000101d4081c81d10010a03103e05c0b160b12400c080e041541c520500c800350003070900245850303210741c500500c0041030100318801d01c000c001840e410000c00519160301008020190f17002182d024000000402417000c0c0c9440032401c0400080c140c81c0c1c030140320a20f1600b000014010191401c00b035070b60051042d42d0040034480d1500000d42403400c2d02200303a24551a02e83c12400302d9034000259200c11507142803007940030741e139814110f00304d208601c0050810b01d0107000c01c2c001103205070b103000d030017201c14030001d1700b42540c224410420484403002240540c0c88400b0710006140c141c001d500d9a1052020f00b40c0c1032841c0c91400a0b081d200700c0000074481d66844242c40a46 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 399376825 1250 399375575 399375589
    0xe07150e0310060306050f010b0301080a030c0c0e161409060a1d090a0b01031d030406081f06030507020c041506030b040603062d05071b0213050c0301050a1a090d02 72
    0x402c000200501c45982d81c0c0c2000002040c09462000c0c1c80e600f000700101b030002c01202182e04030342840d001000d0008194804642c081d01071281214040c907141400101020455071280c080c2d010040802030000d00b0790b801030a140101c00359140044000d1190050a943d140c081d250542410305012416181c2986184940f890b001441c0740d21084090600200707040c26808003401901c02e80f4200b1480811151901c001c0400c50110500c50344200414804944a0414103401031108541414100b0002000200d502d01a80040c8000f075500d00410441d0b5504000341d250080080c1d40400584200485290032240180903440c01d140e00d03044410b25a803200d900c03a40055800c00da04204d0b880f1660030b001d00c10801a40150155036001c2c6c5c031489aa02c007403080da03020301d1658441d11034001284440d20600b1404910507139001d085445503030102d505901589116401444c01c00f60340303605000400002079140d410007540003071042c00102c0000c0340300c000c666440e60115071003180c103c01071000980c5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 399378075 1250 399376825 399376843
    0x30807080c0c1f0f060b0d110c030a020102180f13020c0f070807090507080c070609030509060d060503160810020d021308060a050c09031009050102090d0311010e07150e03 75
    0x7940300c2c2c810610300b40c07003c01080d03400c820401d12091120740003001880f010341d40c4078007401000520410000e141c07001d55912501019a01d07040481c200702c00d20180c141075030403e143c00e20160750001440c01c0c0c0030307043c16048401c524040707564601c1c0c0d040c070901085040d500d1582000050f50300240704443d20804000d0440f052508904030f4401c00d80301c1c80266215400c80c0300b114086810030f004918054007030101d091054005541d030380c0c1040041d0b2a9600175001142080d07051040820121003a42c80f030710000c14003d901c844022804a16010034540b400340741a08180180c050130009200080003c603c0800d80000b510000d612003030b04c3c1d180c0c00002e1260718003440c03036558840c030700288004021403890f204a20080c800c00c4141d642d040740350418818800703e2030303140c2c20420031866401001d40c442e0703526501440005042c4000785001c2030324100066000d07004501980d04450f4038170701c00d0040d034194010b601c0241c000f06207801600314140e06080e5106090204050303142c01541c6041083d40704c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 399379325 1250 399378075 399378097
    0x71215180615030b0d0b070e0402030c030f180c04050c04092d14060d030c08131a0a0804140a170702040b0a060801140303040f0b2203030807080c 64
    0x6409800d002000c0014145885a1040310103503200b00c2103214040c1c441d0000d069005414500c9000250391080c03c611001014442400b044140d00c41040e200c1d8800303184907805000c861652403d151300b414540700c000408013114049094207805201c600802c0814200301c2c1170320040349a403204041c40b051801143c00502005241405900a24218003142035103035030000d004881d0343d00c0c000390041c1500c3c7c3d9041001c42d182c4030000411043e042080e0401c40700303802890040c0c400c9000b565480030f194080107405020000900c0c013481021031012018440200c10020a45000e05514002c1c01c060001440603140c400c10b0414078413141c3d8103008801c7c016500200c0740042c0ca0704080d95588603000040141e0240d03140c44800000c0d402c0c100d080d141510300c0e0f0344a4220b143e02e80700007e101c5031180c3c0002c030780600080c08005000e0704046240000b80c42040e60341c940b0b0b00442140004150f0510717509d4904020403000c104007180e0424800d41d04240d0038600701c520313503640540351104bd200744203001d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 399380575 1250 399379325 399379349
    0x140409170a1701080a0b041101030e0d08010f0b04030c090905250e13051f09170d0b0d030507030f091e051f08180f060109020d0b0108071215 62
    0x80d07501c9600402d00740754881602c121020903602c465681c0e644000300c13240100034a44101c0420045440550441980801407402207000c51040b0481420100380441890100c2c621a00510841c03007980f950b1005003221122450402e0300c0c6890b080070006261113944420360381c4141e05802d1190a200c100c42032900c1c1c1d0842d4410000b001a050400c5c20345124401d0b9400100b40424108604064030b551404c0d0800d000340541c1c0181c0c20550b0414010402e034501c0c250303a40d21810005012001ca00102c8103041c0405501e4001d48107440080d5400d9485a80c0318419a0001c6000290401c080c0c0d800c00350540b81a25007207162075800c0d0307040440c6da04115802130034248014083c3d108903042d28266034040e150500c2c80c50301b44900c2d4031401c185407043e0002c03c0c03c032000201d2410030481c0b85e201e04445082240c58000310004070301d0038154207800250216800040d885049451401030004a040a1070014440d14000000130003a0301e00350007130350f01103448200703405410840542e1503000d40ad40001c0d503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 399381825 1250 399380575 399380587
    0x80f040b040b0d2702101e110d0e0303040905040218151008091504080708040807030c140f010503180706030f0605040c050a05031b03010909051614040917 68
    0x14030074030b0700252100200f1905012041000c0c4615483d4030300f00714840c600c01d1201c40391581c02c10401c0c102030544a420041c510003002404404e138aa103105e254aa5220300012201c4451060700780561803200314240030040813096140e4034008122400c8801d1490700241c02c1d240c0e0b2001840b51080b91140340f411411319001d100b02c04001c16084001c40b041140d15490701d2488203400d40b1080302c1116041c00c581c0046040c40c800300c0c00c00100d242d00922817040300c1d1030145107a641d051140c029400010043e4055882401004080c429a0010304079406091740e13a01003000010f4105542c0c100941d042003400b101144038142400d00e520317510340c09101600e40c281e4407410001c1c018410140a1a00d0500340000000d01d170925200c2d00340c0c0c01100d60380705440c02540301d5081c0c9699002800300f10503010034040b42074000580c10081c5010f440300354000b180300c01050034007030b24203031204200c07094202a15030b0030450080c0c040c0760500c0d110f409032004500c42919060003c482030540c91b142d0103041d030000303107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 399383075 1250 399381825 399381839
    0x51e07080c010b2d0f030303070206161409220908090a051903061d011104090f0e0c10020102040f03110a06050403050607030207143f07080f040b04 65
    0x9003401c001c000e030007000408581c5003002190707480b004000351810101030034181c000001103d4036141c01c0300034001c1d60b8501c1110010a18540c012518800160009001c1c85160b40d41d0008091201449141c204842c60040c00320005601c120983c1910460800022500303803015144d04110b1452811020000c144160502d81c103107510841d205d6104011007100461185060310039240a80d100301c408454041c2191b582d50020109960340107c40d5079074074440e202c0e0346001d01a000d0322502100c901034a40f0325100380c0005650b00d400c4103000040c10001071042129000030310440a0741d040b109800f03407038a001d405a0080c482d5400c040840010103c0100500004010264400382c0946044101640e0340710b00711090b00641c0002003a90b003081c80400ca8407032094018114480c02429502400ca529070340d0207180040da440d202c0c05515005c81248640c2070040f040c00f2040c07101c803402c0044030b04003000010991240010042903114080b45803a50551500195805401d6195035030342d403603440d081 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 399384325 1250 399383075 399383077
    0x60c030e03060702060a060501050a0e060f0909070e04050a050135010606050405030c010c03050a0503040503090d06050a140c0406120b0a08031e07080d0e101b020c100f051e0708 78
    0x64006c00784d50070008002695481401141c0c903058099507521802442d800801c07440382e1109221124141090241c4c0b4916958008418050209521130780301c9030b030303c190a0009948006000340e000500e000c2c0108090302c01002d481052181c880c984000040082060001003141c60030402e60a62070900042451034004e4000e00694070700700c0031246400c52800044429642400c0000c0002d40c060041c016024002ca0286411600c1042501c3c10b24500d1804903100308000003065540d107449a0502ca00210f807072180c02001c0c10075003d005524502189807401d903216078400e0740c042200300d0104640301b04480e8890030881c1d000820001e41c16580e030300425542c3d004009120f0356103400c20030345941d041c100c0e011102d10550185010f4209081170f00e03550300504884589558070b0142d402e4121000405200d80c1a201490021400a40e00c602c44000d20b1711010f02c0906000380004040b1000302900305074419012452454010f642b40450a908c008815407100000004e0f61302140a10801900348 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 399385575 1250 399384325 399384331
    0x3140109090b0901020a050405130b13090b0a06050616050304080a0b0103021e0306060409020102030d1d010608120d020c120a02011b020604030c080c0a150605030c010216060c030e0306070206 84
    0x7412520b215202d07184160300700c0c42200384040120f0b41c00c100030003180c100030f6801c3c40350358240e80d800108091800701007400f00c00c5015015101c1590341e5040801c00c008891020b8100038820001c0040300c2c1050040b8096100b00031070841c140001c802c84504010081048a010f0050306040e04e500b200507161880b8a22070a0001724401c00000071500c4010480b14041e0300e100c00002c00030405600c03000c1c03e010040100c20800da046010800901d0300080c80c502039006a00c540281d240a000b4561590301d0841e4880d410080064122840a8030b0008424003541c01c60300c4407200040e82c6000d401e049a241c00c4603080213041815000c101c0603511034065000128440d941865241d900b004607000720b84410044400501050340d03405410302203510301e8081e00310b09650b030003100c2041c803483e21002d00718154400c2d00800d0b140c0b01d500502c500d003000e20141d01d0f400020f000411019801c14000340300b0b80c0e10f5010781000c1020b0440320a0034181300c0c01924040d00805815141c10b800c00b07a10003521071400f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 399386825 1250 399385575 399385583
    0x6030b0105101716031b09050f01030209010815030703140309010216050d140c060c0f190209150a241e200717060709050609090402100314010909 64
    0x342c1802905402030348140b422501c1040c80c0c3d030081d5540d540207002102114480001c05684843d43c80c8601610802c02d00711344c2654940550f554a071a0422081070704044a00f0304050040c8070104441c0d8110020580017170035802003070340610010740420300d40300c8541e00107000c0701c2124a844a000001200800d6410020703420b81d51160a50300b80044507100c10301c2460741021281401d0004030b5019007a5120755400d40040ea80c032400c1082c00241c041e000481507410b260045d805032095404200300464041c01c01d1084000f00011700c1e000900c1d480d80080034a100400055401d84941c0d65881020000d82800160990030000c01c06100c212003000c002c40201045d9044142c19186550700c4070a4600011907030307291005949082c0c041c443c190b800340603508034482c1600120b00e402c000a8020540c41503a001004285040c81c030080c00007900d03600240c0110010000c1c07001c140c90b0003c80b542d00980540d5901c0201000380c01c118001c00c3e0014041d46145080c1001141071101508403002ca80e002d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 399388075 1250 399386825 399386839
    0x6070801030c05030304030f02040c12050c04060207170a291801050901060b0a0e04180602031b070c09020f210a0e06090a0b040f08030403020d140a020703030810030606030b0105 78
    0xf01d6044c1a5684520b000290662181da6090001440c180e00680d5142c003152400321104121081c4c0c48080d502c003545c00c2a0010340c082000d214081d410000b00005290490000483c1c00c400c0107000d480700c10381c0d040038140140905100f560102c07400b1500d1501031140710105a60710301004440d00b82c1e410002c11125950070030010503070ba1941400740d1415114080702c0145440710061040d80c944680c01450394000d51a06c2c158580102c00c00510885207001c0d00001d030343e034030301300150046203205401c5a80820704184020000300b4601c00480c3c00b950728500c80103a07108a00000c00c0150700508a001410203d403e4100707011030001003846004081e40c00050004401501c01c158482c5c1c2c080f115000107600610045001c140580e044c0343d0482d01441301504040b030305485188031948101c4065026038000d0002034a040d40c400044603030010403406a5051183d0010000d444254921003c0c0030041d070000403a429100c5410084001c0da2700c142d003000b0f00380d601e240482e43d80c0f0003445110701c40c0d41 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 399389325 1250 399388075 399388079
    0x1a10060309050d050903120d09020f0a0609061808010507020d02060a0204050d110103060e07050c07050901080d140c0f1606030e0a0f0807080324120309040906090506070801030c 78
    0x100900401908942c00030180c5401070400b101150f203504458681645886040c80302e450084c1008000c00c458894500c01040f110401d0040c05400401d4401183c012422507800b08052a1b110090f181901d80c04d141421128001c040d0300c403914540d03500000c2e02d079460407040c0841540c0000c0c03643d1000481d6000c2d50340503030f01c540640040f4042c620815810a030700c020001d0000d910100c0304044004141000580c660301c8a2070000300c18821070381c00c408101c0000d10b00403400c0040101c030f0300904040350314801c90340c141498161503202510020052105400c5100d000800c25401d44a005242d0b0b000c49504009006205581d10f8188a0700c3c003030070f07040400102e000c038402d003d5000c420240c200100109046640d0311024958503040c15200b5031028061003001540000065015001d40209200d08000020003815484008800948584a850100c01d42c03a4000305c1038407415101200c000625808606010004c0c01c131b0300e0700c028560701a010801000c1a00484064162400351480d680c0300345d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 399390575 1250 399389325 399389327
    0x1704020d140c19050109060302160b180c0405130b071110140c03070c0f050109060f06050108130c1401020715081009020a050301050409020f1203040602010b040510120804031a1006 79
    0x10f4802d00820740010f841200621455009400070a6615582d00b0010031030300c1191a001c049040640f942c203a80d081d40c00401c2d250b048104207940c00c000c0102c808220f14203001401007000d10700550001d24441c03d113000584a54007420245174180c20b41410b941e600c80003400c900c0300400306000d01007a508180004600582002001e481c402c181a071030b10100103086803a413004074410020b0440b102e45d02e521050000a0182c0500c030308029003290041000c50034030b0009809000024041d0b0394800b80c00102c080403a0040400c84200c075905444007801c4466000101d0411086400c450040c14420b42d1040005900c80001481107002c0d00340304071265107a429441c00c0c2d20842c1300400010b01c0034001070120b0325040c1e1204c045a40f0041c400c40754034008401003124045080c0c41992141c00100d02040b4454081c040c1c1c0385901c40841c0c04000d98580008a003010b24131900816071031448105401d402c01501000311800b954000c80300005043e0480c000401d500c0381162801006125a00c0c000f98072 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 399391825 1250 399390575 399390619
    0xf120506030a0b0c0412150b032a0f030604050703020f0613060815040e010509010f0207020d0b04060b1804050712030f0827061e0105011704020d140c 66
    0xc00e0010068150400c40303840e503441094000d4400c042100081000041c102110300020344960b1188080f00f005906e644070303039070450f941142803a000303401002111060300b03051428005a5116440d084400c0304101c4042402c00100c40c42c440d800d84542011722041c0f10000480c00110303442100e04640c941054018489140103015030201d038110046001d00040d030041d013080c0e0780410040036074800c50b0b4001707000506850310200213500d035035501c0d001e2051300d650030300a41c0d401d161900825460009540d0200e042c00080c0a809840c02d0722844c00f2601700111a000130980c1030300200040c0c40a84124010344010b1010307030701110684035841000400d1240d070203020388402c0e0943ca94401d12110200107a8403294003e0042c2d490071400200740780400003200e0650040c61200300105400d02d400c02515030309040c40d00124050400500c01040240e901400c2d00026040115800c40d107901c85101044254407a420020081808056041524200005d42c9080d42c003080310700c0d0000aa8031500c0c1c1e020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 399393075 1250 399391825 399391831
    0x90504061a010512041b0b0a020d090b0d1a0901030528020906010e0f0901080708010e16030210030905010203040312050a060305120a1404080a0525060305090115060f1205 75
    0x108009001c0113025030003a0b5030072980980580200401b0151809440d110241e0640000302c50030004156009241c1d03041122030130307901c1a8102140031900346540d0900e58000c2c0300110000944421261901c1c01c255589251b90080181c01a00156100d03c1e01d03940f160a0f0118050f450010b9001c4034100254460303601000d42d4018002d40300b292920f030011503401c40207400b2242c2040302200071008940f2800d41a40c02084144080c0186504147c3c0c1c25080d507140103844141030307008809481f000c6030782100d10805c80b80d0403036a50b442d564400c1000e4015001c0300c10040c009520110800c070505400c600c000350f42c0c082c80c400400680d60303081034280448031a4000640325a000070072002446103040014061180740e8240030034000a8100c04076100c1c2e04c5500070b140c0580201001e402002002c202d0f500003c3e42c1c00d5105180c800242419180581e250b200e0b03542055114001b00f48800001c4d031054000807007030100c4061890f11000c0c003818503134a00007158000b8811900003510b01c11a0700c50f00c1c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 399394325 1250 399393075 399393077
    0xc040b07060506041e0b030c0102030918070c150507090e09101d07030f0203070e0c090607020a05030f150c0c1f0b100e13050c0d0906020f04090504061a01 68
    0x1080a20940303401d0300600e4010003268215036503034a8140c03d1400c2c0c08032028252901c460200b41d1890b620f05060519034011152415076206200c0640c20750380b00d008025010521030135400132a0b94a250840388440c1440014184100e040e0080e4030b0500c00341c0103d07200d28190b4903140c14070307036031440318100008044030300d145190403c8034805104031a98102d42c0c00754142420816210446100250500c040c0f64003c4070300c443c0040c03200741142400d01c0080300402840400d610180750600c04402c40d4481d2446561282c50001802c43c02c6559160301c00700603100190840f860340c030300110b440307542d034403214610041e011a000c00100b61000d4001105e12226880e00642180c2c0c00038540403022081e10340c078110505031180c885442907140c2c402d0440c24071403680d5951406100724400e002c260f2444200005030141050b08201c901039400040300c6008003002000a040082421720100a000e0240d004a00f243c0c00039000501e031109800081c020f5020300000c00020b204a40c06884906480001728 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 399395575 1250 399394325 399394327
    0x403051e031315150e0901050109020c0d080c120403031d1204060c02120303091509030a1e030f0606090305010b0307050901031b270c0908030415051201030305070b0c040b 75
    0xc00001c030f1040c454900746204007404120030341c94503c10381c6981c00e5600b224283c0c000703d0b800c00200002c2400340324010807100b58110324009c00c03a9911500c03040445c881d07509120340b200c04121001a03900c1159580c80b90261410054207040c5001006819400012a000441404801200d21000c98210700700d2103503480341c9103441e10f000c1054500004800c8140d03400352074005c4008221006000440c4107515450180c01c00c3c4001308e4003840900360103054001079a00c1800b1800c500360b005a91080700480e0340031001075805c10300c08124050903240e4840c0e48a103042003000a41c0f1500305810405072032152009000c012901414140d40f4240d500c1030300d40c0511020010008034084030428004c003d0005114808952200b10003005089001407030700b4942001c00560281d0200c611942d190707400d542c5401c440b150300d018060346e41c0b4000c0303000b05c41d0120350442c1003a041d18001e80440d844c1d4540030f40c5811483da9241030140580c0c000c503000391408084034001416071710000c0c08071001ea9141060302c03 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 399396825 1250 399395575 399395611
    0x507030b01080f22021003091b0509060607080904090c140409121103270a080f1f090b19050108030c062202130914070509060405041a0403051e03 64
    0xa5400841342080080d4459210701d1396101503120452264090070446d14041000c0c3c040c2d1401020074010708042e42c0c20201c3c40b9000380b155030341d412105a0000c0e0111049a00d601d071500b0405030a102d143c5003660307c03502e440848402c20031800d02000c2268480312107040545a10300030702058800703c1900402c04003041c00c51038a51400344440c44510352000703081700c2c01c012071003001c0a2148288520a100003080b0321001d035051404100703001c05440c00e44050f12200216498860742e6090810407111003815078981c84400d203803103604c003070304483e00112040002c2c02d0000c941f0b1000c800300c0c018014401e041c01c0020031203040000403541c0c52a40c890003401035a0b00c0c0040442e02030301083c441c000032941d1b09000c202503030700e180c0508282c1c00801c50001c0c90031510b28200d28000c100585052640c0c01c03040b420002687c03101804c5512035429500421180d40303914103410139580c051200305c4401102020300c400c2c10390200c0607020030810941c10744002030060394a403000d13000840d4900d802609032084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 399398075 1250 399396825 399396841
    0x1207020c030a050a23060c04300f170d09060506101d06040f14030708010b01050706020f1e071b03020a0302010f0207050603190f0c090e040309090c030507030b01080f 73
    0x2d0070116888240d40c0c1c210101d1500c04046c100b000c10380c0d400c00c400c5800704092013203030420001050113041084000000da140c507500300011b00208040903115260f0001c0381c07400c0c06500b00c1c1552054240c010095030702d0301c00224030801040c0c20708082d5403880c0f400d40001c2031420180d40590040e143c5803545144c040c00f58003804616001c20200942100e0144400118a50a80c003c40d010340202c03403001c000c050004082c1880c11040341d0121219031b05042044d4030a9170402c0844074550b80001001d0307581e1a03a010180c0c0c4500c242d5049201100c00c6c411844806603200002d44285071081c000380c00411a4940915410b048500020f50b100c5824030b01000158000c41c2c0a0403007030b00c18015200103070b51b6000019150740088031210880c00b58000401c141085a20951220380d039400c100b004030b844007075001041003000740265490000d4681c041030905020710010300007026804003c1c400a5520680200076007416034030280421300700349541300f1540c00382c04018070482402d400c20801d55920700c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 399399325 1250 399398075 399398093
    0x40f0b0a20120a2a0203070503180f10080a240e0708090604051b0102011b0519021603020d03090b07030c1a0411060a030905030318062d0415021207020c030a050a 71
    0x11013002076200401004001031000d1024211a2543c03038030480d42001c44606100954030642081441100c2c05801c0840c2c0c1c94001000640000d002a0005503a000c03d41c14145455070807a840001ca07404560b00040c59000501018421140d544d0303910700640b50044c0c1c0680c1c81105513401005504440040081240207203401600c4034014400495108507006c0d8420141c121400101c001034030000700d100d14091164840c001041851000704141341c136560014801124030302000b4407a015113440b40050604c2804c522015240e02040c20340d907150a1300d0080c00010b050300c4c00b100c4003070302450750102c80c0d10480304152003030fa0484441000c61013007070704104055000e9105041419603504803480890420006548650984060b4036813800c1000051031522800900c0600c010314090480c42c210b40315030010703000c85c1c5400a007c1c80180c03070f43d242403180e201e03d0f00c0000310514400304008440c41000c00c2414018400c45c0c003501e00e003036441014507480f104e03a90400703040b99001d40d000c0c2c40001c035405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 399400575 1250 399399325 399399401
    0x5040e06040b040f090605070906170c0f03190c0305091024060e18010810050702100e0d090501020712110d1703010602010b030303040f0b0a20120a 65
    0x2030002801c42c1c10000050704848034803c0d8441103981e00c082490812509114030b642050f0b07075041c146c1500d850004014031002c0004040032031039403000045142070352000700796000d85240c00d420f01e0301c0f4a8610300c11340c08444131100c1030000c40d09149400c103081e4081c0c4283c8d40180300003c043c0280c514000030300b4018000080348042c1a0907002030084031b0032078543c08503000d80955900c00300902c9c0311004000110100c418600c501843d880c00400c0440030000350740b00b4040d814003001c201603460000c207030301300155240c1001490b4104001c0450119011511450100c001d84440040c29120f0b0012a51040740740120010b0301000c1e0b0041000c0307514a212150140d0000341403084d04991556002c003090000c4582a410036400301c014040260280584c01c6042d00950080d820345c9002d0703c030001110304600000e030a00c214135012031980f5105820580c100307510040a803492510110070b01c00305610506516001107012004030b003481d8a0760280809509880216008041d08121a043d90359503039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 399401825 1250 399400575 399400579
    0x207210e03031606050105040203010605040320100906083d050409030c0c08030c0c060c0a050a210315050105090d0f081806030f0406050c040902030906070f0c0305040e06 75
    0x1101055420350741000140024001041c10b440050a00d141c10401d42d401a007006e8452401407005000035540700d0195001c982d080900c0c80040d94405a184003543d64003480d03982c00c407402d903000740c2d219a088001d94044603065540c0030126031f285070512582041e80c4810b42c80b500c1d022010444c500f0040c1d401c001841034041c9155121070340c0c0e2030015084a4212008401050302c0c0c400303440078080b1414440300100f80030300c00366250007a4001030b2502c800c0442c121920130a0003081d00e0b4403100081010b080030550080480e100c401d6903007017814034000100d140356003078600017280603903040c8a40100401c02e030301d8148900a441c10304d0010742d0b058000304e03495a041480f00003030340086450020001402401100515600c0a4910503041d4108982e071485000d0074041092266601d140134986a05c260030150000b01c5444490700c54804c4d100c1ca61203241102e00102c2407000500001c20098024000b0352030300d00500105610a580c1860180d1016001c00c0091000300186034090300b00c1a404100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 399403075 1250 399401825 399401837
    0xe01120608010e0106060e0306040b071b0f0f020a05030d020a12020114131104020a05031609150908010605011407060203073b01051303020f04020702100804030e04020721 75
    0x1e44a19608440c120b05210754240e4592100300150354101c21180c0000c070042e40038121300c0c94142c4844e855158040c01090801ca061600441c054804403003064400782d200098061000607070410018100100c5800d074890300020400141e18500060743c5503000c04690003402103000c00b6101c400c1041d0700c190303e01e401c0d552a4400d00701441c41e0404464411480700e20302c034502caa92070408548041f6041c07207450050744100180580b00350001c06895000504500041c3c60712542d000c12581c8028550007400c20a0328148090211500f004842003501d0000c070080040c5982c030001140e500095892080340c60780304010b8500403921680003141c0c4001c090400e841124245410410903142643c2d020f003141c80100e040c41d022201145050203181400d107441400c1000e04145800e10811074440244248441d01c2c114511b904c86805844485400615552004082e900003a00c040c8040394102c0c001101604072490310302d401c0c401c1d140500d1304031500704085006041c0e00034451201c02c01d58024844 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 399404325 1250 399403075 399403079
    0x3071704060213031a0c12160c050d0c020f1c0f06090b100306200d0c0c02060c07030209130b13110d050c040c0e0607020402091503010608010e15010e011206 69
    0xb8080080740c001c601c5900c5c088002e070a012900f43c003000002c3d01000d8065001c000c2c03455010649000700d5042802400c40d20003040c031203c02a139a1009040c8010090300074048044282500202e0b02c070485402a92001014540c94082090000546c4840751080c028441c090700426034a0704122803c911a502c001007444040d162403003094401c0b9106400115000411f0003004414007901510030030606880d02c0102400394030462074007400d110400c02e55075891101d40302c070f442151a0f494013600908980d80d6070308a107038000c1e110030441c00300707070300400503000414610450a0380c411426504040c46a809842d080e0050320555040300c02950320251650344141706542d019030a062070b612a000401001c2c00020a00c020307100c17113404150511000d1156040d0306d0321800100c50001d07030304031001a91003891400007144003403a8104488000ca0100012a040740c01ca00658141e5500c420204126618241048402c00c0713600c600a00194603c101204654040c0c5c007150340c1c140e5030200104081d6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 399405575 1250 399404325 399404347
    0x120f1e080702040e060403080a050703110f09040c021603080f07020909010b1002070308030a0209061b012007210212070303090b06030a0c17010209090106050915030717040602 77
    0x2116820140c440c04000151074046140c20321601e90140c1c0240d014180d42e01e003580380646502c600070500f0701050b4994000a400d0351090b407180321000c0750269210345903031140065000680144c568180202d1038282a1003106000240380da90014440398124a642d04644d103800e1950400c3d40c503140005010300130400169200408107108030007060000441020000400c810000094283d10554001c41c000348003140d54481241c1c0c0c0905440701c0981d0303a00c00000440c4c590721403035480c0304036400e4407c00e0156018041d0002e0725142d80c294000030207010000e0079281c0030721801c1d1000b840c2032801024902c8843c2c200401d082040042d0040d122804210040460140d08c9010102c00003542c4820403420031184120182c1c10000135401803205400c02d903a1344000710f03141c0c001d00c014040d0401040035a02e80c00d4045406205011300100e5640d6903440b00913203aa081071509512905070070f901030307100d8044641940e106986030741d0744140d07080c11079600c5804940084c105031222038081060b0742c007071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 399406825 1250 399405575 399405623
    0x2040501120510050105030a110f03121306050405130f0f0204181a1c11060406030506030d030b0102060c221502060c031b0c030d05090d0e0604120f 65
    0x8201200701c41c5051a002e1601509054120680300d80c4649030800621040d03e0005081d4006a030002a40c1a004244800980144001d0102543c54171070074407044540034881001e40703100d00d18081c03840314040d04d0319802d540b103000d9402001e0300203020340b29030080648583c101d01d03c14040c18000191005410750040705987c45900200441c03003070b160b84c148050409100300c0c0c049040303100c400c1e400004e41800042416008040c10704001d168195424140184401030400c0210b0041070b06903100da440c54080d0103404100d03002c0c0d101e40070f81103a00c2c060502a015199181005a014210664075989289003c2d044001218010a040c0c144011a07071000307080c02000c1c11201c82c0091404070150300c002e182c4200103110707150440c414024043c804503040e556002c01140003052036212062103025515601440c99200c0c1d1282c184400e1211515020548240d21400c6648418221581c6024400d9500c41e61050450202c00844200c000c140c840c000184624811503000700d6441071000c64a40d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 399408075 1250 399406825 399406829
    0x150907030213090b061e040b0c010b120613080c1207060f0506060708160f0503031512010204062007030b010303020c091303020a0b0702340602060105060316090302040501 75
    0x1207035000400b0203540700500c04040c000d1010110030b00c281c62001001c68000c0c080c250b030441c0404800e0710761038021207404040e1400340040b0328545032100708400b82d0b80c3c041c1580d000c0b11400b0303c04000309128041404030301107106503120058070702404010790f1080e080d940400d980300c1c0c6a016172901c4c003810300c08150080c8084d5000750303c049514030307202c14110704540c40684490711425041000f4800509000c06403083d122100c501d62034084028101401c4101502d40c0040c5140800810010300710411158070764801d100380d5223030900ba884002a103080303108a00480001c00d040c842c0098a0300100402c0b48a0281c4660039030302099526a94600800001c2e0401c50150f000100b50400c6c41c105045c600d0b0f4030038258036140ca601041910041e4507200b010300e000c2c21512402c4005084a8020004030001044c1c1851010120a0401303424010107204036200b1500f0700207840c005041440020080c0c16290018107035031641e1102a02d406070507201580300382c14464100000130159589104644c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 399409325 1250 399408075 399408077
    0xf020a020a021905060c0601080d050412030f0309080c010f1b09170708010912020606100e0603150a120b0603070621150609051c030e0f03030d020a020a03110109030806010305150907 80
    0xc0c2c1e40d414209c4442c1449013080b100000c00c1424842040101e220700c1c051f207a034a8050401102c4140d100d0021409410100005000d032227001440d450b04000544c04082108803c26080041d2503a1b90600010700e560300c04410009240e526040c4401c40c42401c0c0d20000d1402c3c4000c0750b2041303588603066030035100c48500585441d803461550001007a018002e141e84110101c88851007154400b40c0603080141d418a528040c08001c0000f4035030000040070b40410650040c0360f034a11590310072441d1032501c81c4240440d12031140b0f00100d02e00e400d00266141c02d8401c16101d00002c143c0321010480e41a010203494000103845d149142c400302c0300074a80401800065580100312410a03051011722828224507045a81c01e03403072300d0004640c2c07113014015000f10869800605a201000091640c0103040800c100c03103100080004520b5000105441024844d40b25103450440f908107507400c0b50032a101c0030303011500c55000202c25622079030165900498240d040c900203041c0303030003159030700c2c0003160168 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 399410575 1250 399409325 399409333
    0x1602040e030a091203050406050d2a09050103050f06040b0d1b0e130b07182d08070b12101e0806090c0604090207020102012d0f020a020a021905060c 65
    0x2241155105495034040c21803040d00c8440c041300c3d6500104603100790300c02d01c010060081019455440383c0d0b0030003400c00860700740c1c0c840032002c1182d800c0c161481c040c42c600042402503800042550103030083d5441031240e10fa20884640d900000d01019013060b106c40780d4400084c013018000980502c43c072080c10442c40c0c0100319a00d00344180c4411042c0054172034035491890304060380005403000b24036076120a0a25180d1304d5800d4015040d4100030340c40d00500b1842480c0340ca11040d0403090a200403810324000002550550350b0924103071500c0f0a40164004494100305018044004030702068000c0c81c002c040308601903503109039081240c038a0400401900550000700000c1d481004040c2e0403103800c1001d000c4903901c1c100011401d10540c403610010540104044080d68001c0d804171071850003030500d441e103401e844c85040882c4501c440e100c001c40e031700d01941c0e103120360075a100380d88070948075070000c3c0200c60b220703020010700440300c244044104100c2c000106160f20f8240280a418030194024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 399411825 1250 399410575 399410587
    0x70309080d090b060d110103111306182c0403051c05180601050a03110312040e091606090905250203130e0601020304051e0301020313200906061602040e03 68
    0xf14903005020300800d102d25201031804010812100081e2486102401e00144140540c454205a401043c5242c00109001d8000160b465085058814041c5520090307041464952000031f5901c04011041108000c000c1c0c0d00c00ba00722405211507030058020f08205041070321150003108c10880d100d00b81c142d40b580f9036003480001d14024100320301c8071300903070054000c66042c40046010400e2520018042e102010710f00c6d052510140b0280003204440e18405503101e480c0d41e0910000c0c841521060386034400d80f020001e120380b03648520010348507035a032403904180c60204110084c0c040030705461103031944450b15404110542c86500c000318140c0c0c024541741d40c0071540c07900c05807005ea0f00480400c600c40040000581c0d010080342c0503280215016240384030364820b910b802940c000b032029010b41c400020300035a43c080708050310125100c0c40070050504d101c8034454500c4040000030300c0c0c100302c1d140c002c02c1c41031030b10001a2543d40c0c0f441c04448403440300c0f500080c0c10f441c2c0d0028070f9a801d410008030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 399413075 1250 399411825 399411833
    0x6030f0807030806041109040f020d090311070b12010e04020102011b031a0f060403060e0a050d02100f140604180b0f061002030c0604020910151d19050603070309080d09 74
    0x356640c010313004c807020002a0901301c40300d044e0380319102c0440d200b80d9035128255110750079170f41078412400c20640200424075041c600a4401c0e80c1d10032008440f441501c900040d034000180c101c03550304035140042c92050740380402003000b07040c01070400c80c155520350342d41c0d4107112c001d01074100c2100095a00450000c40f81c20270032841c49005e6600501404114404400d42e40b610421a400c076136201100050720b1800120080c10520304880c010040e0003010404565203900141c070781c0d01d140d155001004201310f442071603812551245081000310510310700007241450507901a0200c031202c1019030380d03c075800d540e0f881c4e02e0141c02c03517120001c03e142006009840c100303902c084103428461300003076284c0103202d020f9030b51711030004000030301ca4111100041c1008901a0082d0000c020784902c44003100441000541090303000241c111a40740000c0361001d8a1400c188100c5076540d2443c42180100c0c1401305100ca554070042604080c162a100c5801c00107002e0402007205050403900003440540d58a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 399414325 1250 399413075 399413087
    0xd050c0d300809010c081605070f110f0108090c0d0305040812031e040209040b040804030b070203030f1012080d0b15041a030c04140f090901140f0903071506030f080703 74
    0x4100141c0c90000449465a0040e05454111000c01d07d4001c492208250845880c41070b00f8004083c1007440c3c049404000c902c00b40380b04075110441e944104442900700450f030302d103800c4500e1529980000004a084d0410000345515907001780784c000d1500307450b030f04883e180040005c0c009440d880004100000f03182d40081c070301039803c81c001021301141000c0e0001002c40e20060405001c1508690106040010800466004503800300b60a105883d001d4000307500ca80003143c403440c0e0100140b0001d0744000320504444140d441c0514a41c002410b240c54030726081e000a400443d11580d80c4c2f14a0b001a50b43c1074482589403407001480307545504215800c1d030300d00c581080000d1020b60520074810b200c2c01403000d881c282c81c420000a81c031840060006807401c09d402817243d03040880b500a000070810190000c075080e980d11056a0f07000d40300c44114840300042268000b0040c1c0050000b0000035410804001b0111281a4046882502c07034452052961110004807401c480005806041581101e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 399415575 1250 399414325 399414331
    0x16020717060c0c0f0114190504150c020316140d1404030201030e0a02040501030b10060504050d1101021509011508030a020c100c080c0a050106050d050c0d3008 70
    0x3800d04100c111911a42a51500e02a16000b08040e0224207100b40e030000b00543d0700b640b424040240840720326402e55104c900b42c251950656454080d0302400e00740b100e8010fa03805240c1c0700c5101c0008090710307104103009154032881c1c4011808200512007103040003488544d0003038003c00040c0700c1442501000c0b403074842e2861140c414442005a160345030604801a0380803640c0a00f000f0842083d4005298202410a036000350701628140020040c00100a03d4600c41c019601030b2090042c1c568505480d0750240d0312445900c543d07440d40050002d240c1940d0501000810300441c0c0005460a4240c1ba0f0742c401100c80046c10382d501c0082c40d65049040450200901d1418080c51400300c0e03040d0001d40750300850741500d008411446196180c18440c502d1484042d80140c0d0701511100c401e1000703a222102458161029801d246012803d480c0150540788040d5002004081c0b6604c040103102a50980d070b0307425500078400300080500c0c00365111403000d00715240050304182e42080f44001d403c6840203 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 399416825 1250 399415575 399415589
    0xb01170f010605030705040815041203110702060706020c0f0a0c050f2d0d03020a060e03040e0a050405010605060c010203062103070308060d14060f07080f22060203160207 75
    0x16000e200d40040e03521180c40c107440191420642d00d0381c9040c4142e5162080f548401e07a688580c2210303c0c4c1182010000f00e000e00e01c140d25040c050382c60a5030480599548000c00ea2240c0400c00c000360061074480020301205105420140c10a180700c0955414070132a407544c0319003608000640d20030071450b443c030440500f40480312429000d0300da002050b003540206080f12030860109400a848140b0038205a00005008210660100d01032074001c8d1034013020700c02116640e040600d451889900402550151340141d003440680c4e07034600d46100c02a00002d8026160741d507072002c001c40c181d11243d0060080c010658005a924280101440305410307000081e88d48810310030b410303041c1003003011048400b055010b00c1c00c44602e07121080080e00ca10001e02d0010001901100324080101002c46c1c81c61065001c0c0d81da407040c0c0e54440380c1c05d0324443c0003101c6058903d909540010440c07020404441880d6604144c0e1a06450043d540e0b0780c200d80c0140c030108242d00b401c1d01120180e0794100041400b800d07017 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 399418075 1250 399416825 399416867
    0x1809010824042a0f0815070f03090209010611060f010b0708070c0503030f0301050f0904020102030f09041407020105011701020306010909051302041a03011a03150405030c070f06030605040b090c13030f05010b01 92
    0x9080c5107443d1b0103d01400ca00104000c502c0680c000b03a107e80c00100c2c2c2c0c40c0d001403030440c003941d4842000d0101da100000103c11f90149100062006ca80c0050681c101d070010111645803200607503c424031036004840882d1a0080420089100e84042024000d0300028107040780d42c075410101000484008420460312501c0352908000050b43d0100507100c0c5004401c000ca91104044000035010300001c100c6d0081c000e0350107003000780f0b45a054001c0c1d030403207403188000b49000900f12400341c2070b44000c4803080e0210301c3d22038003002241491ba10031903010350200e00401104143e54002026980e80303800743e00d850003004102400718503081c0301d82e1031024a00380f4041d000b12607100c04030380c5504800c101c01c41d40e55040c900007010300100780111404e4408800c145d60309183c070341000314107104041c00703041b00081c81c129020a5605091048085c4000300810703440c0c590340c400c0f60312a99544407079207a850748007000034000001000e5114903000d0074445c01c0081404500c40300014003501c410828400e603591 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 399419325 1250 399418075 399418093
    0x50a02010e030a0b2805042604050d060c08100e0f0a020d0203091b030d0804060c030605030a0605090c06120f07110d03020d0c03021321081809010824042a0f08 70
    0x1019075500c0c403803101d40ba000c924103020054880408da00035540607d42040e1705c490304808001c07060348070007940d481c1d03616040000c0d190009940ca01c024103028544904055102094021a10f0402e481d03004030341a40242c036018000c00b4690507600103684c141510360002040112045603540c00340d080c0c400540085c4034000ba540d40052901302c0241c00640760079581d00f50000c165100e030b000680030741000f5044803607001281c64108003d2004842940c0a80110796150602d850110110755004080786515103d94aa603004d168501e040601303000705100b07154031a0141c0030414028001150801e480060320b850415002074151403008a0320010548100145034100c80c5560050082e1440c100700c40310401d82d0101641c40b400b0306220007a0540001141e00703041d600d000d0010341c424881c290341d44040ea9a940104c02d0361507908108042d0302400c1e1886000525003140d031140e90060103010001c1c003059036040c102c075140c05680c0d1080c009002d8680240001c0100d451718a0080400c00c1c010a5480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 399420575 1250 399419325 399419333
    0xf0601080102090303070602070204020909011206060e130b090109050709020d06090203100b1e0f070539130606030e19021c0221010203160c050a02010e030a0b280504 73
    0x807086020087c0b0907039005c204c0200750f4990341e040d912034150241098005507150310001c41d8514000c034003103170058102400450300040b116038503030240404410211000440c4c0e6102c0803040001004040503669a04000300032400800104000300400d0700300591340c80703c9030340d24001e42d1380c1d903040040914010030601982046542c40641121b0000c59116100c18859a1803500c4454184d0900102d02000c52404006141400180f03401131040d802c6415002d40900e00092001801030805104540002079405a40b01d1000314521404020180341d0300f000d4451029084070350a800c4140041d54072410b541743c8078010068420011032a004210b001407003a400962000307403406404004280c00441c500464a4a000400c18280c00b9404034034035095102410b03000750021100c5203801e201400500308030f5801420f03144000ca030080c000d01f050b004141c0055034268002c0292541511521001a010a1580e002e80b030140b5060131280207100d5290322411880700d2000d12100000d403038001032000003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 399421825 1250 399420575 399420577
    0x2011d120d2007120602030403050408030301030501150801150504020f0c010e0a03170c0a12022b0c0314160e0619020606270703061805063606061306020f0601080102090303 76
    0x1c245d02000c00341e41c03580d0314030701190303503000b1039114052522001c0004020084103400160b5002012902070140f603544440303050981e0309140204030015030000702448541065001002c001120824281c9065050706481c1e0865201140090558201c2e5800e441056444407065150302c448041a1184c0e0806a1130f41f8503a22854040d04c0074002c0d1102c0c501d40d40c1150340c044c0c4116164001a60301c540e08000018061060011341c05007085103082d50000b24140070f0320400d812900520100d1380c0641c0c4514144c0f1240c440c40070440d040c05884601042c60355204402015001c1d00115100220480104080c0c50300034041c1215204003080c0c1c0301d41c0c10402d603840c85403c100d08d5204070034080d51940102600100071540000c00414180c3d01c4207124101c103900000e0151500351000b4410000c07000d552106900c0920325104c0340200a0b0052480308511001d00e030700207000070319075860483c00042c11400343c6242d601020141c0c00c2070034806070601c01840940d005214580c001d5151442140c0001d440b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 399423075 1250 399421825 399421859
    0x503010b032d1f09050c0603011a03040206220306060501050a0c110109170106140a050d0b0a1415130501051f0210060602061009060302011d120d2007 66
    0x80b9415503106020700c60010040388a21034032200008400c041034486140c054141143c0036900f5210380040c82c1c400d400d010041380d0490b52802542c01d0511500683e0041aa0000d031003039034059014040c440c03400110300c40c0d03400c19060702049012240c3c0365181c82400c3d00d00580c000c41c140041444a0b1040980100c213480100c1d9004408911071429440140c501c001150007010b07000e0301c0d41f901d00540e60700550100e0155a1880020f8003180741d000304000e03100340c1a01030641c000350300342e03c41c6000030550728076030f500404000400710741c80c140f40d000c0e80c0c02d40c041165001000401840560070609005075075501070340b00b1140600441d8141008208400f10f100300b4440c1c541171442655403071601c00c1c4612004e041c9600c500307010040c0d4540e8021340d00d40f426140300e032800190503030004609010740b18101c00c0300d034181c550300350014180c201e032641c82c0f01202c1129000701540700501c1d000e4600f23020407020489161102c42c0b4004200701e07501c1122200c01ca4240040d802980e040c040309880f2000613007 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 399424325 1250 399423075 399423133
    0x4030b01030b0601050c0a03090f081903050c0f0d0306150503091c02030702180907170d050304020103021b06070305060d03200102070203060c04090f02030610032d060503010b03 78
    0x1000e80f280f0004840302d00c180c4070014901e0003804140010035a10400582c2201c0d8001c00f0300c0321703550716480b49e10345030f10303000612200042c403210b41800040c3c01f68003d03007240c4001c0b1f015241140320303441015007070135820352020b070000381d4803001032008480034060144810f00a1403e9030a61901030105c56a90914415403c40c4d03228100a550700785100b00115011075a000d44040b02800c420b04000d02800c106851031030182c060b10700003003580d803080070b001d032800b0b0040402413500300503201040d01c10741d1000e402603041607020130407850941840020f803195410014003d00b510310304800020111140500b03010b01c03070346805254201003944030b04844414116540388071580c101c0207000f9402481490b0000f9014050a0204900d00031810b001d0001c44e02c01e1602070018064012182d0128441118041d90010108480d900c001e80b00e0b9100d1007540520018601c50078001c511140511807604c0110030b600d41d20796000b03200608007030141d40b0f459001500181000c400309001c0c0929100c450038088 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 399425575 1250 399424325 399424343
    0x20607030c05190b060310180f03051204050f0f0c10080a1d0601060305060f090c0703020114090109020418030c1b05090a0c0e090910110d0c0302130b04030b0103 71
    0x206004043c05000910400d101c6030f20414601031410701c100400c2110001c3c030038020030128200d58002030242d111a09801040c14403007070308654910800d0a489101079040150034051982a4480310a085010307038000c200a00f03510640d00342d03041c5804800310000c1c0340c030341040006c00d0203519000784d150b1122700942444500c507a501d002480040401180c400d161030621301001d2500e92000c03030300c18181d45441c0c0e81484940d46003c00d200e8104403407407000f5000000440000c1800a00a0240072100d02c03901c008500303840442d42982c1201401d403000d90071039540e540d4080c00c42c40e2a110b406042c280d110781031601d580e07440d180070348819241f400242140c0079200390027580b10701e500e07a010003803e002480321003242030461000000b402c00d0001640820103da02454440c942062494070032881e1030010724580c0e0340102c1c01000340142e001d20300c0c9030603420b000d2080c10070003a0055003000090f995006840348030100200c0e14443d1964450301e0380c414100000e1022850048a01d8192900a5064 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 399426825 1250 399425575 399425597
    0x6061906110c04020f03061014040306090f2003191205090a030b07020a0b0c120109392d05071505100801060501090819030e10020102040812040302060703 68
    0x51801c004200d10ba1035401440024032441c0c00c2400c0b001396000f04803d0351914040c0280e90415541c0c541c00702ea141c44401400e0104100040383c64000140891003001e41a002c8405960348032054810b0b1040d1b000d1440b034800c0301e1485810108050520111203441c031032140c80c1e641d2184421104880c071107104000000448030a036480d003000036002181e002c0182d030507c1c0307040c0304002c0d25400b000b00201d03414800440401c0c0c1014807a0169515901c42030500010b030f91800340d60340c0042c0103d901040030682502101c00403800515086003603c15004035110030072844c3c4800510342d04020560309034228000114080349520142e4000803a0001e08096a0719100c81c1045200421405050101181040d04108902500c240034404644e011002801510b46450042d00c000c0da0a019010003035001c0135a80c2d07086105507180780d0b030b82401b80c01c1c8103130b6014a54010541c0915071600000c0540c2d0001401c0004e54010462024880b5080c01c00c182071504650006450380b260380c0000d4100b11680d024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 399428075 1250 399426825 399426857
    0x1116020d050a021203090109060c0b06090612010609140708010e0408030a02040e15040b120a020f0d230d030c0f03050a06081b150310050603071211070506061906 71
    0x91a0180ca400600030070a03800302048183c0e45e85d100c00280c40c001414014005021401170ba5040112540310110385200e560b034a013071022001009001591102498801d20240c5200b0312503200942650130340890030501d080b03900007000c080900030500b004065401013201d09170310780d8503e4025500c00c903190342e01c0e03c0781070f840400790003030b9001004c002105205100a500c9520107a0650080a42e0107000703d9030f9510402018842c2204a00100d401000d05072006140c111b440c2200544001c0c401d00b0009050380760150280078903070600d0440f40a40543ca120311408000c010b1503584546014440350180d80c200614002c015401c1205068444011881d6848035400c40c0000c0c00c00c1070101e9803002070304410a42c03071496055959005001440c0c00c2107507521400101e0344904000c4c501510040e00d0201840b54585c4020300d1281001520361240d007583d1583d0090011300300300220180e44030041030500703504080d406800280305100d4105115200d0f502c4044000843d401800e0503c03810f960315103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 399429325 1250 399428075 399428083
    0x1e010807030f0204060e10080c040501050901030e0601080c01090b070c050d15090302030a1710051c0f0308040c0b03040f060b0d0b1303030506010c110d110405090a03031116020d05 79
    0x702c00000c480c004035002c0b4a41d40e0010400e412401d0882d00702c280329010300310559090000755070b1401409020407042c41503500032001000910418034000404156510b54242003200a8000114541020850707200701e680c0203411401900f180c0c0c2d031803032a00c0c408c1d0703030b880c0a0152542304147c0140d1410401e50b0a00c900f0074405c00d07240d190f510042c08a82540d1400a44903400300c0461004240341d1141903101c2d510841d5000d2140a050300d41c0b4010500303240802c0400346243c00e49201c0b150107809094005617000b03618104a40c030a451b9846507041500e004030010b0340319085828140d100340308100c085840303036449410b0941c0100d030014414040d0004248000d84130348001d840750707440a05100c20b407501d040c0d0808005001e603a0800c02926500011991342c0780c0007074090240303103809880303264501d0075803c110380c014403c802280381d8000c41404601510422100a9800e801900155003031503014010004c21729082080985042500c0c0d0f9180c050105588010740079440c0c680021040103c100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 399430575 1250 399429325 399429341
    0x30c0f050604030f0210090209010b030c0f0c060a0606030c020c191a0d0b0102070f060305100509010b070b011a0d110705031614060601080408090a05040f0905010b1e01080703 77
    0x200544001e441d00341005800c20125002503401031103001107404d6040400e10075140c02d250300804012040c3d1a02c4c500079025040a041c031034043c0c50800c4107410000e6004003d0421006407005000315203091070104c42100c0d002e0340b0660a15080c0712492034620340c04a0240c40326001102d00003006200134590721001202030b04980e2082e0f07440c01e002103c0100c140301400d02c0000b0900d00380700c0701c0e0101c030049071108040c2c880d842491826400500019000f601705d242d02042080034511203654030360000b50301f00e07420380c08604805c0c40080c2603006c0c4149001c00d140500b41036024999162000c0246844600c03604440307220b42a9103415418542900c5c0b002c81e203000d80c2150460b6140d44458400c60780a190b204001c680710303040307006584140080454a20320590058561511540d1552601405039003d4080c1d0355000c0c3c000c440214890b03586100b082a07400c440c1030006020a59440c0c6032707003181c5401d00d485100e0103520240040c0d010a03523080032103c140a103440b400e66140c0c0d40041d4040c0102d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 399431825 1250 399430575 399430583
    0x71101200c010b13060906080a0b0f090a02100c0302011d1c050909100e150310051302220b0102120a0f05160b070e1906031d1204050102010606020f0a030c0f 69
    0x1c01d04c52024206a900075034150307071030b030700d01002100d642d070076865940d041240c0f00920800c0060001502c0070f1455540399072150003001030351107801d00c2d6400038180b21609204400403803903201d41142032550910507402410005407901146507a494440c1e9035840300c004111603155800c0c3c412400c804d2040c1c05407100850b01526441160904800d0302240b40d00d02e0084d005110b20800009031861140504ca03600d502010300540102c02c48140306101030140202100c501146106e800d800688807580c003428544031240560f2000250140e8107410386500742c4800e411540641c015140560666046481401031800c100e00030602c0e485060342c0d60b0080f40940c1000c036a880d0381410512207000c00d9248102e00f603658411054201c90100b055400d1f1803240010007485072131003880254020340c03141e580072404902e0405103c42d400711440c40c141042c01c800020780001702c0d081009580900407240903104c14005022090b4088200a6544401010250030000383c40c1150003881610011f95072901c0e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 399433075 1250 399431825 399431839
    0xe150c0a080d02070623010b1803100b0103051006091514040821041202040504020f030a060f0c0809030a1d060705030306090a201e070b071101200c010b 67
    0x21159014000b90840c85007034440c542000110356444a846c1c248802a1851100304110740e42010f809030859089407194000c1d04407004401d003001e0740d040005101c40d00c0341080108807130800364001001e0396000b8008400d103c003070700b404bc1314490700f1420020035641a041030303218200d030402c0c04607075800081c613022003007041c00075002c00c06d400d01090b81c0d0384c005071a03640d54104a142c0340c2c2c443c07120f01c1184910b10301d0b03150b00c1440d40c006140a40046400c50300090440480f8191900000d08184041e80300301c42059856034100c41d005140d009040c2911081d0811000c640741a40740f45071a441071002e04004c102d5034000e05000c0c560100d9010032900e10203000c1584602d11450490790340d6105480b01071040380c1c1c3c3d500047e144003440c052501c204611020008082c440c40302401c000b50480c89400e1698001d485a03440714410410203410180d0060010700d00500b0062006040c04c6c0d5214880f0046906010f00f6805012034070000c0410043c11034500ea0740e805196280b6401441c441c945a41c0c4049 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 399434325 1250 399433075 399433087
    0xc020402160b070305010b0a0c02040f0b13061706060d14010e1e15010303020706030905150405070e0c0304031b020f040e060105030d02010b030a031b0f0c03120e150c0a08 75
    0xb070703070361100d00c10b00c40d50328100443d903216069010030703000d03070280c6ca1f002484d103e048400500f010f4204d0508083e0100b804103030701c4c0300c0d030b4002036020089607884070f80c443d59800c0800030442908030841c9001c001c1070280482c1e01b400008134180d5039403c00d01518100300d42402c030146e1790095002a401c038030000305490700c03960207803440c00c140c0001d220311a55900c02c080e5284140070700340c1002812240d06070001c0c4581451306100350094440008107488501801204151030091001018030807489a806086c0310f90078a0030348108010003030101100518107204100c0041e400031340b1a00102008048600740c15098800a1550343d15002c059800606003010821842c0300000d080b030580c0e604a0a0f55600302100b03c1c228201c540c1c0c031410b568541d100351031640c042800b03030754208071030110001014106000764036584026094060101c4a00c8030300c400410038480c030300f0030301b40503a0751030318064050381104d4001404103040c400c810070030004001403501d41008100220310b842c503881032549482d00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 399435575 1250 399434325 399434333
    0x19020c0309090a050906070f030b09010801020403210504140f04140103062414031c02100518030a0806210601031101030e060703020c0709050f06040b0402030105030c010c02040216 79
    0x5006070640d2400341e01000040703484003045020307481c03281d07007008000c0c1155660108100c0d43e42000c64006414182d84000e500300c1078072043c2115001e0881c42001581d150310350325000140c01d46000d10800454401101c003040140e0090450741124080003078a1013030808000080c0311444041c2c9030703170380c000c0c40d12186082084080d11058101c1e030061000700400b201d030380c52110314401184000000c2c2039550400340031801c0000303602c04180e0301c007070203c0302142c1c000c0c0480c0300c0007241070702c0da0005688000240741c4412842e00610ba403081e009058929030f22014940030750340740074000f0404188004540000d40079290b846c90b81910903000c0c0c100e43d01d00d22500c1c1e44103807500401e02003507440c0e60b81201c1c0c428883d4003030301481030b0081948001303081607540c0743c0d000c600030b4111401c503020502408000082c40011401818044c445085810f9041d0401d0000c000c102d580840e8540c3c0240d005200400403981c003c9090100c0b86ca003824042142c884c04d20000340240300c1d0780855038220034090315500c140 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 399436825 1250 399435575 399435577
    0x31401120210020d050d050405070509010b04080c100c0602091503013b010608040f171210033c140f0c100c0f0b01060503150114030c0319020c03 64
    0x2030095801c0002c12450502c100c4e22078000c4920503000c91410060051070300311036071146a11901540c1503407240c90312800014010842079008400c8102d021800b4860480140200c95003901d084444650420401e940a400d0406901e0040c080660100383c11069032100c1d000e141d1002d07405568641e9030340c1c50f07504103120003085c1d0007205c0e6407a240c11288044442c0000161401100e00c00c5420440da2820b2411114075100400c2142c2201c0c80100b24800102401c50901a66040c503444548a056032030084d20518001004146d01107181c0071700300040751000312104103d20003003440c58644452840f01e4026100404140c4992901448804040c024901405070070113240c1d005642060300303011101c40d640e4803202180e41d44001e6001d44040a2401031828000c403d100301c002c91a550360303541321044088001d81c40100460300002c2080400f80b1082800c1d0850301003400c290380d0764800702d10444124000201003031202c20700040490302407183e04458410b4080c542c4019035482c041525081c2e26 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 399438075 1250 399436825 399436859
    0x30b1009080c030115031209080d0c12180303031d0f060405060c040b0405012a0506041401021315172a0405010c11060d060e0907061701060f031401 65
    0x81d90040145080040c50103000398010144c10036504e955203815500c1d8209900500f141e00310512040500c0090340d9102804000300c4000f040d200c140c2d141115003480203908402c28400420043d54840c2c55030505a281d26050589401d0b180000d8007507030000e010340c0c0c24613105204220a104d4210400441400014140c0c45144150150f43c09602c600440a1703450285002e1041c03030000501c001c0c0215441544e4032104603040718000184003a0710790340b01c02501e070008001e0300d41c1e8000c03504010510800700c030791002e1040c4080007180b408880041c0c03011200d05501400540d0551700145031100d40c03107100501d503c0c10090103040d0090404a040150026038280303240445070151103503a02c2d0800d22020ba90860b001a1a12244a41e86589682c0c100c0e182200079070f4480400c0c8450100003a09102c0d03007015101801c02510f01e8240310b9501864400e003a408113081203885d074000002c0802d407610145c11140d0905252100081180d400e5020302000520140c40b001003400000718514200300d2046 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 399439325 1250 399438075 399438089
    0x70b031008060105060d020d02040b030a0f0e0f03180f0a1d09070303051813020a032301050a0302060a1205150f010806061c15270902010c12030b1009 66
    0x124003650356400a440b2075003445220b0344104180022046e40e04290020680202141801860329413103042d000d00c99081650705034101c039651001c401d45040144100b980b00ca01e00d100411030013203c085990350300d206405c01ca03003025607a020251081e440f40c0000550610004107440f0007540c0303d40d085000350081203a254001c1158001080c41400040380f032105594050369054a0700324a03040d07511400b1a220201900222240030350524803601e84081c00c0b4542c07559401280010031541070600404075108101d0990130514010022661100004000c60f135060f1071382ea0711540e10a4040e9000c01d410031a10246a0502c1d0802c1000c3c1da00d4405040d4008048a4480c0d0248207000110b551020441d00c6c9c5820480030008410030214050b4a4854803005d81d0010544049242045404d1071065108190314030116005d90102118101490004106a03004100544407500000e0071620220409044030b00303080349021039a4429044203248901c09080c80d8080580b0b032000030104005446090 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 399440575 1250 399439325 399439351
    0xc010f24121203020c030d0c03020a17011202040c050c0604050703170a170a02040314070501030e03070807150b0405070c03030c02190618021801080d110303190e070b03 74
    0x1164541d07001d00d41c0d000307070350300320348010059010000160001d61094000e411503110500840008100c0d9006080300e0201c00c2e500036854214104014040501101b02661403461304c20041c07010f071103403130311030191a40c04680c081000d00908005851501c1402c4410f902801303000c0800c01070000000e410022280b26600c040301a82c0c1c044210302590007000c1d1540000703a42044080083c0c407801103245c0e04039205d20790051800342e0b40c1da104000c10100c00c00100d0503800c10f207000c0040d580c1600c2505c00b5031103039034041c0d440d040041d51185854410310308010402401104070086605040e0701654407000098400c01032030604540140c04d030030800d61308a00080c100000d0340110b6202081d20900d203500083c5520315442c042d0b41e524050001c0c00e0f0032000b003442040e00c070030140e901c1074010b054080089030b448110b94100842030381400c1c4559400000e1200a0f80c4c82540c000e40002102da2140d07680d030440c045651000d1a5101030410f08401290500c510303140802d41020000096009940a804074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 399441825 1250 399440575 399440579
    0x61c0b31090822170316171803060903090102071a0f0a02030904050702030a0e220219020f280f14032203050309060c0705040f1d061504020c010f24 65
    0x1315442d03144600c0256440d002407207450641c101600507030201031b10071408600c40310010060f1000c00e41084080f400c1040e0340e40014545802c1c140840d030b81112082018618060798680081e50b01c1005100d01c941850b10642c5006491028500341c03040440e52541d0187e1310031181070003c1d540d03001072140d144120303d03060202d50742c0c0380000304a0340321082030748615581e100c0403000c1010704850b0855040f0713030103403501e627040b074084852000b005d40c1d41040d24402100341110341c0080c82e18407900c6c0c4001441e80200d545c5d05010385001b41d0031400401c0c1c81404030301c1d152580341c400359850040754024000301c3c41c4111200d4200000c000340983d2045070003030f2846050105504d030011074403071001808039041008848086d042800c01885258080c02c1200c21140d56a804102207519507000000d50030369586a0b2080890143c0c0d80e5903040c51504000c0043c0d0610101c41008280c0301e040d4035214590010740724245e142c080d00084411034000d88108800980000d11645904101c003100621040110300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 399443075 1250 399441825 399441839
    0xa0302150711010615031d0616030b100f0810060813020d0203010f06090b04060e010b07210206010609091a040b0301110f040e070219020906040b061c0b31090822 71
    0x1042131000440780003402e039610b552008881c11000c144101003010f440f042c07115a0350315444a001d02c001c060f8dd50b041481d102ca04170090130610081e040041c24015858100010307544950740c517802000e840e181c49000d042a10000c0e81c800701c103034402900741d400c1100d0421850202c1d0b000c00200ca459003402e010020010082104070b407103502a4290310400f040040c04031580010241c4507185c0b003110581c800521840000e0240c800c1c40f0103250040c0e01031001071046640c0003038801c0c01031031041000e1241284101c8010400042068001c0c0510307981c102c04d130301c00c1d5800d41000c1039104e1182802030f61031114400c402034070b071320502800d0039005030383c404501100d02c00104014030b034540788180c00b50f500c1c0c02e030b08001e00500b0140000e6440703512105e183c595a0317910703801420f44c46480c0c038140d0441407c0d11400000d84500b0001070344115040c01d55000b01010107100542480c1c03110000810100d40c40320b000c001081c1e680c1b806460040b020070043d04800c402207044141c02103030300d0300c42c00641d42e40113 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 399444325 1250 399443075 399443111
    0xb19080c0d050a0e0c1503010306270c050f120d0f03241706090d1115070804050d090620030d0507050d0e060114100e060a021605030a030215071101061503 68
    0x40c424131291ba0400042020903042e51061240b1081c4030354014082070714040052150510201c181c6461001440800c01450310041031030910200340e4101183c00000041c55881d8009010040240110490461451071103640440b030b82c035085942a41445071010800b034030402d41400740e400b8220450041043c1d031003000800d40c0c41019480010990404c5880c02181d01030407020b4009600d205900b041d01070b11074000740c0b01d0710403c00b60303496509610f89400c190349040380c080c6901c0706000d0900ea050040c164801c403807418000c1032000300411909104400b0b407440c03185056804030f041c0b0780f030180030300b0a03440070040c4400315003140306100c55011074100c951a00f80038854042c4c0f443c5040c0c003140040c20400f4244415413050704040040c0000c6001280c2d640d486402c4090050300a080158800c01d0402c00b040d001e42000c1e8000c107410750403a90042d6032024116104202c107245140021030035440303184081c0c48106018000d1100039072742c58000b0030700d0043c2d981110201c1d003042290542200c6a03c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 399445575 1250 399444325 399444349
    0x7031403040f18060b04060f17040c1203051e1908070909111309020c1209150304140a080a0305060603040c05040c050405120303010e010b19080c0d050a0e0c 69
    0x344801106501c0d0500e1103d400308004070074a0071944030100029401c0010000d4001011281c9460380d81500341800101140e4410141403e00c2c04000144000b040840d1910f40540e01040b00f400f64407406400c003651180a20310700c00880700380ca0024034601c11060740c06049254041d142c0040c5026800c10140c8a44004641900014400400800000c0419000384814881861002d45130016a5641c0e180018081c0c000d00700300c1d500050f40f6103491900f005400312150420b00002c1c2400340102c00a0000b80c1d20b140c460040010100114040c41882085041d0750b800d40001c80d20811690b20b801d244542001500b84040303890600000c1c000d01f881e50450744500c0d40610081c035941e05000c00c00c0020024117400804100c003e01c004915030f16840c5404501c510410004d580769850519083c048030f00507008041000810700418810b207030303003441c0303106a0402070030811a07550f00d07000800d006004401e0f103213400f54142000e01294207a15401000c0b540d243c5401d54031a00c01303034824060000210 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 399446825 1250 399445575 399445589
    0x130501110a021e0a150603120e100e090a02070c0806330603070809010f11130605091c030c02040f020c0f0f100e07051908010f06031e020d050f0703140304 68
    0x4030072844000b80444203040b000c000c07a03d85c0082d209840e900d48141c0030200c0d0b0340c1c2501045c4a411100110301c0c001e00304209001061800000c1940c02c140841d24020010742415001500801d0020410003c50540c0028141d550704403800d0b0b24003c0319a60385001c01d09901d8500300c0c002818001c40101c0d044e4a007002c004060805072468032590811039086000401104055580f0031881480f10442d0080c3d441c601d031030611301c680300d10210116102080140c0d020b2024088104100300040d107801490400444044480c20360580607414256070b10850020000c0d4401d2502440a01c1c0e0511940680001c003091000c948410016071585c6aa07108444404111584000000000c11280350000010700c141e26041c0c4006680e540301003070525180b090b081034041121b5000b840f002e00248200301101030220000d00c281861340d122000740800c01c25891074050800d1101000755100c4a11005040d58050100c0725800803040d40592603840390701049480c9074000d044404202c10002c1030b07030151060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 399448075 1250 399446825 399446833
    0x40905072405040b0c251d060a0314030f030a021c33030807030201050717040807020d021c0c140f0a050f010908010911010f031503030503130501110a021e 68
    0x82c04810101904003203890707909807203054100100c0030301b40420344448200180000c0307400f6081c110103c000d0b00303140f40107100401c60b207010820150360b440d409404403500409010910823040c1303406815407013185040c3c103100000106006610304550300422550f0485907100400c500320594683c1580d041d402d99684000500020388050340030140400703880751001c6400380001d070f902d903150604c0da0440d0700183e0260750745800701b10b50103401412094680c0c0006011110b9454155501e4485000e0b5050283c010780c1000c0c034440c1107454000304038041700c00044c0c035220300700c2d01d07450a03456840c894002d10210610924282501d82006095403000040042800400074140b030180124400117610303050403c03544440000d02c1a10030301c90781603024007404801d03180c031400714005840014940142004c040c038040c01c040c101100110080c061341c0c0d05181050741c9855100406900c071103100000760480d46050b050f15540150310f0000d2145503115000d07030708900c1c20700080c2c2d11084449101c214072030300 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 399449325 1250 399448075 399448079
    0xa0b060405100509130b1810021312140706021f020702010504030209130201020c090c1804061502150c04080601060503090319020c0f0901151b0204090507240504 71
    0x141503007126030300c034000710b120002141d540c10000d011298250349020405021051242c24007206a401c56400208515000703110044505466541d040c002c403041411039011442070680712941c20000010020821202640106802d085d50400b20345003103032034035200340318000030f91500210b4000c07000c044403c0030542c101c541d8100c1c070010f54851030f02241000b404010100040c1d42c3d045407103004214119212080140c144006807030910040038a510030b0710200d042000c040391031000ca0780d0784d0000c48104000c40011102240160980d9044001c44950032181c80382d005030700207103c040d01410389115000507101c4040c200c5082c4035500407147c40b0b4201c44014004980a4002160002c01400c21070f440c00d50b40d40090740c0307504000740c0030300010381000030303000e00501c0c0c10164410241400c81d2a042c95526045510081207544264941400548445441ca003000948062812a000750051218001500d0b155481c1c9a09010b2b451170386035010300a050312008048070f40b04180c80ea40300d80340303418 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 399450575 1250 399449325 399449329
    0x10f0e100c06060305120c060604050c03130606080715180602210904090c08010b010f0807180e04120909110313020d060c0206010815101a0c121306020a0b06 69
    0xe045003003901d003151103d40000c0099400c00c0814003011000d070a16446100000100303091901c0644002e10441c00c100620482400d0035003200e0704058600c3c032042c814550f034640f010203000a64090340c03c42c040d01800207666400038140460f0079145503070700e1080c1d510740c0c900f1500b641d5090181c0c100580c8928550010107800b2400360341e1403280c950081d4108170541d40054140c45c500b840440715070702e0b01030b400c00c0b2508090103014900f1342c00b400d00c80c0d46600421001054400010404810001d9200008611040c1e591040c4050b060000480b042d52030f050a18100300030341d90b245a0300007030300500c0025104115210341d11559020400441c5145c480c80e840d2012030082d18003d076881410b0600c008001741d00b80c8100040d01d541c80d000f90240d50b140130415030410501c1e0580c60b180d8440c04040204485a0407041026210861500c541c15160b8104400c03d0b4044c1c14000c40b40d911031a01541b00d007514450240c400b08000340c2d0054403030f40e110082207880d00310410000b000b120880011039924 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 399451825 1250 399450575 399450587
    0x3010515040207050f01020a12050601081b163503010305030301180612060e0c0111032a030406030b090709290c0a080d05010b19050a0e0d03020606010f0e10 69
    0xc24050012200342c00c0c0b888003020300321381c0704501200200707030305483d10342406481d2b018203944801e090a050210345080c030300094003507107140c00550240c49c2c0061050703031051101d0081e8120f581c120618803a4030b010780035010345242d1544050101c3c81c81044180c0381d0b14002504032816640d0007005942140d21b401541903040d0040300981c84910340b24180401d0541d1000d12080a182c05100c000c11081c46e2000040c0c1045180c004540c1001103030400c000754100b00208031000803a0340540d8030b0490708103041c3c480010360b803100c1c228040c1c0000900081c4295040e00b250104000440f0011110389882c3ca060f00c1d010720b1841041602146007070a84240381c21140c45442e000c0980101c80d1a00c14600c20090600c03001007011114900301164400380741580e442898003419180c54020b141c400c1e104018606400c1081c11901000000250310110701e1040304420745001010b4108940030f40e02e80350180d2a103c0c01c03108640059070440e504032106106500c59000d0074030142900501180304c007011100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 399453075 1250 399451825 399451837
    0x20d0c0f121e0503122205060a05011a0a14090d05030706050601030c0f0e0d08040f0e090a0b240a0b07140105040c1a0f040b0406110d020c0607110a090506040b030105150402 76
    0x41010400e80c40d041606c0c010a1102d19202e10007a1030701d8174200200d4012118103812041415501d10503400390010810101c80c240d022a00f0440e4801d50350b120310540c14460100c10907000b2148a00003420020008080c0001c81d2003584180519130f12079004600f1190790a65110014805894003154640610480c0607060310103800282d4104032525a499a6445540004603040e00d01c1002c0194001c0700d880a904140607601601100b80d05071030342c000d00c0070301a00080022100b283c80c6011300c10801419070800401404c0712000955400d000445604000c000340c07140340105103c072440302018407590344aa40d00160100c081030400110700e01d403144440b40381017000c04c2045203030000e00e0a903018100428400c4036880c1d403541032007002051030b601604002c405034030040c21203071141c6d008181501021400e4642c5602d83c000381c1868111988100111600400c0200c1d01094029440c0c200612401c1e0964050206180040c241400ca880840c0c4e0720500604d0001c000c09249002d40043c81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 399454325 1250 399453075 399453091
    0x30207080d0e030d0903020d0908070e0f0619180c0509030729071101090608070206160504030204150302091602100c03021e0405040c0806010c020d0c0f121e050312 72
    0x410b242c6803544e203804440701c584042d00941c0c0881d1903507444507400382c4500040e10445016080c002e00d80b903002e14041070702030240e003c61150040003400c40e031902003040404014284010341c0042d03581b08228170013030020032068075581c2810403021600307005800300c5500b03100c00f4001305007062400400e610f02c0350019030040e4501c440803050300c0c051480c00700945012801030004540c3e0800769800076181d00c0307180d805401070200b20010440403580208085900c600388101c00100d0302d03454102240d40d8421074000035403080c07801c81241e0001c44944001c0d42903d02c00d44030b40440e0b403680c400240d0425140d03024600183c0c80305c07160103082e0750349030000d030818170707042c10003608251019a414800400d000c080300f042c150f001c901000340d860a4060351441010030709195000d403c215000808601c8800c401038002c2c005021850100425005180d0090809842c281078091302c4288041901189000540b0b180ca408024030810b4841280705d100910f600900a40c981180b100c0403000008000b0003502c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 399455575 1250 399454325 399454327
    0x11508090c0d05010f0b03010c050a080c190210200a0323042a060e060304020315010b07170901201203010b07050d0306060f050c0118030e030d030207080d0e03 70
    0x7426516042e01c0414124401c8002150350092510030004840300f00a065100c3da046c036204010b400e820108964400850346018039030759843c9a00114184110301c1281902070910743d042c681540c0c04209071014802024050040d0300c4070340914a00c451015490290b84901080300f03410450107580031418545004103009419416006d058070244c404a4060b1b03041d1b994504200310300c0761707422100342101071036044c030f801406e0409038010405211145401d0050398000040b40565030200141e00d854400e004030042690f8584c440305030240c10090341110b08004001100400f00f001c682511502e41d0180d507000220313800c8258450700d51448030422a06401104c0d107907081c3c421007800950182801509407969445d0902c0c0282c60503403800410300805207009030501c6030700d83c40f10620803440c90515006486000c10b0519a00400d0303040d140d516000d000032140401c05801440000c40d002044003560f1460201c0d86003602603120304c040003020907504010351000c407011b691103401e40c0e4502c0d404417 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 399456825 1250 399455575 399455593
    0x41e0305030a0f0c0204230717060f04090f060b031009051510090507030209010e0603160305060102030c1b04140f07030908120403030b090901020f0f1809070305090705010801150809 80
    0x1160480700d030b0702d090f0303905031415148900e40c11807050311f03181c0c110520703141c45001c03544022054502c0b0fa03000b6001b24401e4440001c0c0d11070682c3c541d088000340c281c02103010408602c061401c50000c15140c40e4140c041d020716034080043c04484e2140880d0960004003411128510200c01000d441d80204440403107154194003091103d042c0c81540d00c550210340380166103c19902c000b4200c240300c1c040080c8505820400c010008286403152024946581008251900c550700141c0c11070040b00340000e410b100d030000ca82101c1106a2000c100c0b0b50064030108017000c501c1c1d0794040032050403a422a100110711021511301c0d4465800038045c203000f1052507040040a40d10840c1c070344400d850540002c1c0d107840500d0b0307551410b030b88559001030785080210326041d00340c0c00940c01d134040d41a4101d00d035480400c1d400c06140800c114254500d01c002c0c0f80034034610708404080c00500b41504e81e9001d51180010100740741d402000c03568140c1c0ca102140303860307088400740200d4180b0301c0200020000d014100300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 399458075 1250 399456825 399456829
    0x1204021f09032d03050d0f02090d031809020715050703020327120a0201021822020708090405040b040c1a0301051e03060c09040f09080306100c0206030408041e0305030a0f0c02 77
    0xa80044203101713a4589980345088100390f400d50b800b1011841186104124035802669990110320401f46c0c1800c0c400081c001880a104080d040d6900c00c3c1581c80c00004e0b042e0801007000b00154040305000b00400050312440380803030880c0412211a04603c00c086100201d0214201c07806085040c802d0440da2480c101c1480c1c45100e404c034001d100c0c0942c2d004a07060040c21a10342a0801c032400c261021314a4680818031805030042c80e03a41d00400c240e0005d141010302001c002120802a8050400e000a003481d191104809104070f4003603620300a40a000b0074080400021703800000e040e941c0e03480c2182d0801c1c0401014080c01e01e080c0444040150080c00e0b45d84040c44401d2040c900f0689194483e044202404140c42e560400800001e280c50f24050001d1012000d0301c1e0001310648400014290310002079070347c2068040084e60295001c400c0008000031040100107079401504000422004540c0e07101c451851800020055042809805202442803406141202040ca84501003c1396a00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 399459325 1250 399458075 399458153
    0x20d020a0801080c0d03020c1c0614010303081e0705030c0d060602030301060f02060c0f071b0e150f0d141510030c060516061e021204021f0903 63
    0x2100d20040703014140100a803500c02d0003806400b410a540c400036100241e0390080d02c400400d07075882d02c80d902d10313201c444082e44040d40780e900c880c3d40507d00704506464181800a070313120911040300028008000100340050440090700c6007020044c0c50700c1d0369240d01704195000d0300b0040001054803000c1c0b04103c01c0300c40314041c0c0401440b054024641e00d50400000404102d040c0d40c0c40425503100105002c0c00802005c1100c80c09410680306580311402890700c0080c000044560562101d0710b90404180b03502100c4407207019002074450107507041415824056031207415840700e6801846800e901d000f0030312101d560820b03058001c0c16140040918441c41a8000c0280d610560541080d0401d00c1000609000701c0c001e41004d007401ca0800314107a40140003400d1803003004006540780c10310442078050340c2d2410349002d10f41c06800c0d52541a0403000031400c1108507020303446104404000c8808004940a0010355040c69561200f518115110032280c200243e00810b04601210030102c204035000c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 399460431 1106 399459325 399459337
    0x3030d140a0b0d02130608030307020102040906120201120b06090319150b0907052101030812011e2108160c080c090723040605041e140d06020d02 64
    0x12170090098081d6910000076444040284504c81da0190007a00c103603034458408001c11541d40560b50810818884003070f0100d11800c98200c03150400d9040460006800b43c2024500104013021a2600f019400440081e200c03515460040024144110f0484401c1060920000300000b0000d03014400250007803041c010001546040c1ca51711080115500e0710030344c1104000d6a40b4101b00e0929400010300c2d80900320800004103c0e0004101d81154a00c40000c5000c0704a05000404c605800348649506440c1c0c1d9200c032040000e0401e07002003410b0b1442c83c105901600c204d240c10300220480e900000031a80140982155035211421819480209442c101140005810900301890300c1c5e0300040d42c01020028001c038141760010000c204440c00c105d50800c1d0082c0e04c4600d1400c1031802e0188464030200354500502c64600b00350582e0000c1d0094031b00524100366052031104076031140d = true := by decide +kernel

theorem cover : BRFrame.Cov 399280575 399460431 := by
  have h0 := BRFrame.cov_init 399280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 399280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 399280575 ≤ n) (h2 : n < 399460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
