-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0553
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:24:59.339655+00:00
-- url     : https://prove2.me/submissions/e6a55ffe-33ab-4332-a138-30c9d8eb7848

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 99280575 ≤ n < 99460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 99281825 1250 99280575 99280589
    0x61311120a0e121309090c0e0a0b0306060402090f06070b0f01061b0201050903160915060513050409030c14010912030912081f1d060307031101030f0b0d1104050907050307 75
    0x1801202540c8407413181c2c005440380c038400b081122010f25294101001c07902c0b5041080142c5070018264000074032684817265400b0740a4180c0e070380c0307000400000f5032102d12142d9200b001024003c03c40e03216a0007901c05d20703101d052818181c1c2085d00c60048950300580c800001c1050482c5450714507054117a0391002503a080c05d10640300c50780c20b00001e0130291100280c151000b080d080003c4e01c5070312604164008205041d91203480c0d912940d040f5450700c58110399000c2b03866650410050387c100340d40f00000660280c0307071a0028020a5403120340c1d26003126650001d507910b130442a0140100b10021007001c6080b410b0400a4811913500c05581840151002d010300404c0400104100114100c80c000c03100c5200c071000b6803946500604480f54180116040020300c80c4001480c1d40c01c1c00521042943c1d000b8465079610903640e070046000c1c11004000099150300c80101101e19207401d411000c82d24460002e1010b044a50414001241c400130402007246c1c0c400e0b28204002d45021900300141d541d5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 99283075 1250 99281825 99281827
    0x1a030405100902060d02120411010f080402400609090f060b040e01110d0e070639061407090f0e0c090604030b0f090102041d061311120a0e12 62
    0x943c2c000500c0c01c1c05050300340344400703000140840000119103403a0744514480c1c00c60311205601d40c07004403401c1b0054000e01c00800c0701200407c0143c07404401065145510101e0043c120120070b1101c00310130a601c81c0c0c0414550181502460004240143d00207050a0201040001c8883d1150300d05584081c402030100c0b0b55444d0949199140c40e086030032201039020091001b030364000c2e002002d40e404208030f1120146041e241265441c4041141c10854030165910340401081c08141900c0d89464440140e00f40060302140328020140d0860f070b05098010308002880b8582c610030f050301f1000c001d0942040150300c65060201d00e10303843c40b50050307441c2040840340a50711040d460109204990300c41d030340a54042030000c1006040c02400380f1400c1c09002d2541c00c1e4a400d0320b402c2c00d07402603016540c480d10b01c000c1900e00d440b1644101315400303540181010160084241050200c40e840841c80f00c3d540c2d400545401100465a00c19070065150318040000440340c05d40c1c940c9418403800d07074541e1520 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 99284325 1250 99283075 99283091
    0xe060a020106030206130504050a0501050607140a02090a1407020604080a03110405040f060317030c040e0402011b050304090e031309021b030301080a020906010503060d14010e0111041a03040510 85
    0x320075070006018650140856680d080042801e69001c206445014801c80c1040001900001140aa40d0480308040d04090502c44241da6940e5030701c6602408074a2441906604000359444250780360160014505c00248580b2032903200450f140000c00c070405562100f8140b10020710f0071400c0790540300c0303145000542007080706400c51282c810303540404d07802410443c9451440119520450489101d0042000440c2c031004c2e420f081d50000b02d80e01c90b1104002e0104020a40c2e00361034481d4090b20501d411901c010104d040b5500b008034901c0c040d10950b0000c40c05000d900360a201e5080c014407104000e6052204240c42c0c248968008d008440440e40c000c40c80d00e14002c00300c80c40f80f84c40c0f0780d18019240c07a90b0b11400202e98580c082c040581c4518a218041002c650240044a0050002400e101004411030702d4150303140032062030b00300daa0b640e02d15140c1d90498080c803a0740e2140405144150342c440c500381084c059450003207500550900100300b4440001e100150f02c02c0740b080c0e45440454152 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 99285575 1250 99284325 99284327
    0x30a03050a120204030501060501170c0706050a06031a060a0f0302060301170115030b06040f0b0d0f032c0f010908071202060d05011412030414040f0b040606050415050a0e060a 77
    0x100c002c02c0521150000c2004820004190424025100d003039803062032001c0d02907050070848409644504044d00104902004929990002035100000070008070324240d89070784607428207901103041028014400284941803030910401001000410860101581190005195840188101c00103903c680e03240d050762960a4011216000240140403496952410aa402d2541c22554148214509821400002c0e02071192507203010f80944403111403802560b8070b5581d803904000071380030310681000c1a4000c0120004003026408481007000c401d40c0b461081c00b246002d01d4560710b044c0301c0350302424131103001c1c005034460460f9058080084200c0d064008960240329180b10f864201d8280300002c5650304400040211142c8143e8904084810b10401c41d520b0b80204c2c050800400c0d400604050103180c41d8202140704054000b000030880080c2c40060200c403129400440426008503040114000780313400c40f0203901d2035003011481e02202a40007040303004c2d0351a0721403041e030000c2038016441d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 99286825 1250 99285575 99285587
    0xa020d0c0c03050d080f0604090f02060a032004050f060703021c110109030302090111010605130c0e04090308010810091221050f150402040302060306010c02060f0a0c0b090c030a03050a 81
    0x441e04202621524030913224010a6210100c44440b680210940494960301b060720544c8403454000e0588140107000f6820400164010301604003019101c860041d02d8001e00d040d0540c03020100700c88035580e24549014841a0140130f100248a14010300590011030303000300b0ba0520101c00c01940c900000e840e403100f52004106211100d0042d883c20460400701501907004121401e02620381403401c40b41e540426082e035026014140e00540800d0352911401c500c0c6d0400c11002e24941007841900c40c650000c141200c03030300b24041c0c000600c40001005aa2000c0c0000d00614284641c14000490030343c80d2505981c8841c10ba4004211000c3c05040010080503da400d800d14400c0e024401810040200c0f4041c082c1650525403040d0100c01c41d07102172525200b11000c132503014144cc1d04654a0303600540e6801c080e840c007a070b00700ca02080011000c0074048020b01d00800d55888800507443daa003003081c2200c0d0700074071074505580403601403031155900044c1c002c50680d152510503900e5928000494103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 99288075 1250 99286825 99286829
    0x31106030c040b0a0207091a0d032307060218120a020618030d030e070b180f0a050904030305010306050c120a0903020102092709060c0313030c1509170a020d0c0c 71
    0x10f00b42c010442104495004c103165086444290b402e110301144810002e800060030900b407030b8400400c0c160440001d0150420070b943e41d0302d0b4445251074180414859a6582c0100c0d422100140d000801c0151400209081111503500303491911440ca01900c8181c1d881075803d10180c03041c480070030002203e080b00740070781c050722002900351504924402030240281c550a001d00000740a80200810300711011015100311080c201c08104050302c00c3c03028450108250614650003090914020805450301034a0394011031003627034009071b1585035041c4075007201c2001d4030181c82480200320203a07546130400c8585810002000d4002040e40ac1450f05900900c00c00702d09580003c88801480841e0905c0340642150500010709400a42d03a603031404ca8540c0400c60ba27100d1402030910100d01181820416001114402d06002c01e001065840314140c0d46402d003584180c03a0748400c1c81800f00000c00b510086014040b100450034143c440d00003940300c540c460b24a804006100303803408203101c044420540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 99289325 1250 99288075 99288089
    0x30305030c07020d0b0f070513090b13051609090b010c06020901030608010507021b0a0e04150e0304090c020f010c020c0f0d020406091b08060105040b071b08010f1401031106030c04 79
    0x154034200b905e80b07080c000d101182c90407410084140001d07202801901100d045110003010110710782e003011203034001010403c516613048081c2c4583d000900089108850081401c08601c090049400400a1200c00140c03c06100ca0703061000030543c42e42c201c00032070105507202201585903490785004034028032060f40700550319820b01043c00345160f004501801543d03021803541014040754002d00c861f0801c81d1040008117682c6a00150104241c0c19000c81070307030410300703010500c2c4552104662075600203805c002450740d80d4407905c2c0200b42d0100405903000d015040248507052078058003035152000c5081d445c1c01803000e070303020022640e00ca8244160f85035004008003e00c584501c040c0000b000d00e4000d0f00100c0d4070040e18540c0c000e000e0341c003c03071003448141e544074905130421802c40308940000384126408000c0e025040903080300205200c002c0c2c408180002803541d4060052820b84698a07400041c0200d40d0b00140007040300450301c4040c0c1d040580c2d10a5480e200c0c0d0300c1c0c00041b4410765004032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 99290575 1250 99289325 99289339
    0x3030e01150f0614030c0409020901020a050304061d041a01030203060109120809040509061014120105070e090a020405011e0908100b03010f050c070201200f0601030512040807030305030c0702 84
    0x420201c000c01501000c1c0c3d516941c4021000707502d00001003c42c40140c81c0c400391501c080c8010440190542c0040c0340c50101881514104009a55483d00c1d640140c0c12410205404042c0c100c0150b00002c1e000e48150400c640a202c010b80000141205200c1e102e40c2d0340c1015000000120f40d64000e510000003040b40c454210100d601508146060780c11000c00f00c0e1246003054007184904030001000c40c0500700b0001030300c42540c41c01d441841d190210f111032903005000000c812903503000a02c60248903103215120306e42100e207120200312110700300409161030707607205100c18002d070b0760310194003000d8000341a00070b5959481094151000c4440e40d1005280340300f11079014540340e17026040440100c00a0300240909c4c150651010103075181106c814801c0e40d002c0c006a4095031240060241c1c034450445440c00740440d1302490b50034481c07019240a0320342d011100404c1084010040402a100e5540d03555003841e06205101d900c4040510028003048000310116074200700000071210380d01d40c004c101c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 99291825 1250 99290575 99290579
    0x206040f0807051011030301150309020d0f11030d020a021507051f0f06060c060f0e0f03071412040e19090c1806050a0b21090102130b041203030e0115 66
    0x1140d95281c4900659004005140c5100c080d45d002d20f03691040c80740e8200c059811607081c00031070f84507c0940f45803901016141c41c2d081c0e0160302d452508103642030044000c42640000750030704c2616581c0300c058140c000c0d070104401c46056680440c1044011354115610944440180740860030380c021404041c0071400b600c2803040c1d496a0f00340803203110b141c46a03010311441d41059034550840d41c0d14459035000c10f031070381092070000c2c41c65031102d00c00c030003030400008000320202c49031850894a07410f4070307042d42c2c0000750032001e0040100d00500c8003039040e4014242c150401130014010b014921490206c440c800340855030320642d8888070107044655140410135504a41403104811100f40b18040400c1c1c0d240c1001024120280181b8040d510081c2c06080070078586072214085510080701d0884290980800500b10102c0000c070324025180a000507884400c0c01d0400d4054901d254000000328030100010456a10724034100b103482a01414005401103c1a200a0140a4024070724030420048100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 99293075 1250 99291825 99291839
    0x150507050601080d0807170a020d180606050a050613030206090a1505070309092f090603040b0a06050108091002030403030b030a0c0f0602010b0609130b1f03050a0c0503130206040f 79
    0x103c29128010355400403030740c807041c9040d03442c1104484911004503207c4001000d01100790001e110704880d0300750010b0b2415a09884400e400e401c03140c00c03207205403070300020000e40c034080c0c0c0100054030003185d9080c50201d03066581c0000c50420720009005d2800802c5000c000c1d40c40c440000010180e005600ea041246003500801075801041c045010508081e0040f42402d502d2041000d000b01861034a100c07000220921000c08890759000420b00500308483c94450325100701441c0120b1192411a050f810804d204105030f4140d50032213070400c84004200110034000160000307011501440050384c0751520309088001d41a104c200c140c15210b4800c40300b04120000204504035061038207564601d40d1980d204a007601c1c411191a9400f45040c000690140b030000e10b0301141c000030030070004409480201103541542e40e46c000e00c00000e036400122010035014025503a002e001c64070f042100000c10352000e0107501025000300c0083c0b581c0394500085444600440c4c001e842e4000d0b60f51480e55850b07103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 99294325 1250 99293075 99293083
    0x22803090818091e1b130603050108010f09050304090504050705060f030f090601050604090e010f060b1201080a02090112030314090307022b03050d09020a0914100b030115050705060108 81
    0x1042c1d030180c110007002400c82148521040015030810000c0780d00350701c4500d420039941d9896084550808420040c0924200148040600624144d14040746961510500a0131142e8000b9024075950a01d241031002500100071141500c5c1d60003c002025125070030960700e8840310390003141d008000002c05030814207030175000d035100c0c10001040d12070031b5503019030882d1100350a00c62507410190903c420b200c100318a411580080c1360410000403441c04400e000000d58110740d219086140c0c0002e0002102120040030601501c5c90380001c0001106070f48c085060404148502c012589a85844100b01403081e004060f007815400e821000340d0404044003612544004c00485c4101c5038180e610000c010401500e0141c0c0c200c102070114050a151400d0342c1650000c0d40d0703044c801ea650b0400702f00690791000c1c40e6000d1b020302d000000d03407d603100c106600b07040405022140303040300d588001c20560f001031048030705540c9070015540020440300f10550f102d00814a00030414019140042a2098001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 99295575 1250 99294325 99294367
    0xa0602030a0e0703020f06091f08010815090c01110102220918020906040203220b010609050405090c01120902060d02030f06190302010804030507080307020714040228030908 76
    0x15410482e0001040d0002c0d07440b41c10707202c000c0d000f20031411580801d240c0038001c0c1c04013180142003a90014825203000c1c2c4142107405d241d01c00708030030500510103a01b08203c043c9914900c6510640c09091134440180c3d1580040812410404041c5007141c403104c0c00c2d010349599610300000c3c0440101940720401d408501d0b0f00401e14418940b804c00c01101d801c8002c4040095009010b01966888210a210203544010068000c0312001d00158001d0802c5105561071580a100e1030601541801d600402c3c01000c4c0d03100f10301c11401e041c1808060134010a660b0880902400d080c800c82414030b9003407014180088000c1d50012021420320020421a0010b601c0784100d080000302d0b981e122800c10484060140d1400000c1d1040b0005000650155110640080c040e084c0300b410684195070b80d00d0640e108940c01c0d40103030000c450070406140c030142c8801d00c010007140c080d070908900003034030307501d00d1402e103087d2103828102100c0c403000c1e6010741e00c00d40450b40c000d002507a072603820100c81c8031100451 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 99296825 1250 99295575 99295591
    0x114041202190b04080c060702030711010309050c040f15031b09150e0c070b04030c0317061021020a020619050f0601050c0c06030106020f15040b0c07140a060203 71
    0x20000c00301140c0301107410300c04041c00c0002d1441d0034030710351260b40c006207006200f1038075208104241c5c0030000c020019a84030302d506a00451b555102841c210741c807070f04004e48460606050032800c00010784c000c9000d82a003003003502d0018190031016a2000a890000c006d54003107020060302100b481215000c4003d4091719012050765a60364607020411607800946100310840002c509100ea8442102402e800c941c0d4003801904044403030302c030840c100c001075500700d020031215080c850405422010941c03030154038800400d00ca280c010041580c07228151070810800001c10184c50100ca411034590b0050500404110348a1880c00000707540d4400540340c0980c900840c6941e900345030482e0041520840032800042d2494641d02c0054586d608400c400180900555402c29010713101c8a000d1030080c45076034001e1103442d251001c5c540c1045803000304ca4410071008001c1001144104c403100340c010f001400629910b010905290200d038040c0f5101c0e03401801600d13411000c1c4440c58010b14016019 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 99298075 1250 99296825 99296843
    0xa02091807080c0d1712070e031011030a0e01060b04081f021305010305060d062d02090d020d0203030c0a0c170d02060601030c0c0606090e12072103060305011404 71
    0x20b80310301903524403806100943c4861007100c0340000464844081c102c0e910105641814112201c00507a01c8030412a0104001584110284030701d14080002c0342e03a840b1840300030401c1d00c0342e0001c0154103102c0246000314254803188042e0112000754000d000820600c8846a20b4540705ca0000ba16844007800d030070060f00c0c801d058015144198402c9950401d41049031180d00c514240054000e02030081c000e0f54048821941c1802240b01809000401c0040d5548540c00030103031254500d410040c050000c2941d0b10510038408076071a2140041906038040351b11014010161001a20390300c1191071540700d0b0b021380305c202020001086200310a49942454000414000ba24460340e940e0300028070800607441640440c0c910350180c0d0000c0818441460014000d0f2171589809042c1d171000e80c014118141d886002030381941050046041a2a21003a82c502d00b243c25105d0f2694160100421094244180704c801c922a02a921101c0110b074004000d10440b0420340d5514440a011182611030003a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 99299325 1250 99298075 99298079
    0x30f06010215010e011215020a0c0516030b190e0f01020301030c0b0c030a030c1214060406050609090a05070201180b0612030f0409181403040f080102070b070305090a02091807 77
    0x30b4058028140c13450500d50038066803a0a0703290349261407509080d606426401101000c0c014940010325134100d280d218040007500d0f171701c0e080d07150005030501181035661900c01400000d844a0345590030900d0590881e418003101e645034801080c0c0081c0c5001544100c481c07000344840190082c504a038060380c80b0b8540241c4c2d031030940d10503100d6600d000300250810801c0a035444e010354400300a007506071515103080c3c204005039904a40c1c0034140c0c00d104038420003c000030f502c4d0501680002d007205540e85424009454080303612900082c1401d041c9945841c00110380074800d600000020140009480c031025981c00c000c14001c5c0151802c9009111500114004582c000102c9503404459000103107010b01d008528001010800303120480214080d035058085031042c110b070558004114065643d0301d2400444014040c03141c0d00c8400640d005021a60208460b03103281e951002c164200842c1b140d4622010604121044c10300031342c0204000d092000c45202c0c2e040d225038020808046a19240d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 99300575 1250 99299325 99299353
    0x31014040203010506030703050414030f130f1a07081201030b180615220e010507020d0306230d0f05010c110601030b01030210020304030c0602032809140307030503030f060102 77
    0xb20090045076003000c020004160454880d921065002c0d00801010918100b58425541143d10088025040c0500403466540e9142c0488207440142112022070f1012468880f5080d000c0c55008035003610420007068071414800020212150011145404542581c49140422400b581a40c0c1c003100704070040110500c1d0003000030f625000302e686007d51400e140c001c5c0208141003b01e01c03034094812890701c1c0d0840c0781d8106405001c0c1c0140401c40046003910704000000d00d40465200500c4c2014146802045502060a04240c0b8210f035410084800b55000001c505441c403c0c460061481852112090900c4030640c4200d903c4a4640d0301c40c0c0201064241142d03a40383c00b030002400611107c0010401031928034000b403107142550054038102641e0381c8486440d180c41ea8408805600700007a100c000f0f0742814125084001000c00b6252281446c03500100714002a0080001240400240900c103a0301000344000035984141200d42e24540800100700c90b040503a5154098810681080342d60 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 99301825 1250 99300575 99300577
    0x4080a0c090b010e120f0a0503040509060105130308030a0e0a0c1811040b070501140f04030f0c030e0103050a06082d010209010f03050a150b130f1809080903030310140402 75
    0xc1c1c00141d40721101101070401700200310080c40244c6555211396510001807031400d1005039007140c045c00240d40c0b124542024001c40041c000c223a68100201000120b00d050030070708810040d0794001c5c840c95100d6841c02036a20042c604030071269414490002c5200c00c001c21580e024040d90501031024020b00c41c000781d000305984401c04400b0300b0040230300040c050604168054070710540901d001090070200303007078072001c1160107940b01ca030552a0307401008241a00180c402460b00f4041c541324403c0c15041c0c8000300400542c6203428100358403100410030700c0d60703180c2101c40a042e05805031841c5100c0c91a59117020510f4204000c417203035100782d156604d10410310966415010686582d5040d03205c00c1070032401004000c00f80c0b00095510042407002c1014a460072015113084244a81d0700d642c42c0c491000b89010560002d000521180b605210302c1d00e80e400d010780065060100800c02501c1854920060300802c50754541620001c4100700102410301219807c460300132281080b4494000305010030b0b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 99303075 1250 99301825 99301841
    0x323070b040b07020405060402072a080316030c02030f010c050a0201050c07081c230403030e01050103171e181002010204030b060d060f0f150504090b01060f02100204080a0c09 77
    0xd081e00601010000d403d040d00140e500c47d800400c01881c100840d40c07000c030343c0e8104c1c0c4080c9181603240240c91045a0f03811440c10701820380b00005504000c0e040d18407060465002d5402820000013030000c60441d00c0c200001d140c080c8551000340446452044000c0142c2c001c841000015820503020801c0d000c3d0250031101400d030030200641c0b82500c0d500583d1158100c6200561440d961030b810084045083c40a020b0760140b44012340d042420242070040030748840c5c03841b0618603450040100005041c0800c1c000011005c1e041d510788170b09040c8214010011188841c60300e40000040844ea50b00f900c030746003c21810200c81c80028046880e008900300e00890000038062307040b25000c40c00b10b143c1081f103040c0941c071900c40400c080b40000c035942c055400045540344201d446080711403501e03220b404200043d00d0b00307440070042841e207034440421100c1c062140000307100114510560451007400308010341d019040095503034603a070b8150560340b1003011740151340806c1011001306031400c082c051000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 99304325 1250 99303075 99303089
    0x10b15040e010b0f0f04080106060327020f03030706060e0709121218031406070305061002031206061204111f020a1101050c01060e011503060503150603070323070b04 73
    0x25243c2c02d011003040c903076000c92403440d200c0c1400e0280317204242c036020042c0083c0c2070040002c21510300d4408003409881c0a0320b9030780818000d154407050103155842030562440e804580c1403c60f6501740c00464118803c25a0180a081c1041004540c0d580c42c0340c1c6481c016400341d0380e01e4072031607580c816802c06890489002170078101e00e1440b1a10f118856842d84064006003078000800079520390b140040440130105482c2c040d0020410002e506401d44a02e036404107040d030307584900941c45000252244201d49024155090010201302c2c00e0312228103031000103988008001350f034203050501c03415501e50300181c2c0e48108400300c0c41e001071002e50790160394648034940003031a0300c0d01d645e62030300030300119620b0150403c1030900c642c0007a420240101c00c0202a140d0001a0650420300c00f004003c000c09849001e06042030000c0100340c5001910b00180c0b1800950303000b1580b15000000d00b0074005520142c807442e181120380d90440c0040c054070701c404401074211615669941035a103014082e6201d685 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 99305575 1250 99304325 99304349
    0x2011b08092404090908090a0806090f0f0a0611070f0507080c0102150106081e011418070503010b0f070804030b090f0a0b07050c07080703030e0901060509130b0f040509010b1504 78
    0x1004ca154005014842c42001941d0420000c040803a001402960086041754807510901680e00014404c120394484010043c0007d0301e040e010307096072410a460014046941c555220703c00c2d10720301d410fa0310a5139121040306034407805401c09681d92040ba004280c018000c540030009590300014004994032658402011140e1902c041074504c650000c0c49004c0012011a4602d280c0c04c25214440c00fa0042c6141e0b40081d0310b104050281c0400101c0c0c1e10b020321401001031065041c1c0000640c0e044903103c02c01c49581e00c03603180d1021554003441c01c0080440c0030100e030100800501c1a025489400304cc1c040b00d481941c0710f0609596200d42180260402110302c000c6401144a81c00030154041844211400e05990300202c0c1e1501e8110b030300a070005007111000200926000500500400081c80c3c600d040080010002e842c00351051103038802a641d1315007118031921480008282403030014403c100c5803810b00000c1d40a4408842c0c200c0c81030a41c951140119134a0b02c1c161070607145102081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 99306825 1250 99305575 99305579
    0x1006050a03030c1103060f09070e01180c090e010e07080f040b011e050d1208010608281e09050f0106030302031b0c10020a0b06060301180902011b08092404 68
    0xb030f26000b0482d02d0640761000c4001802c0e0301e5031806c103d810302400002030403150318038050540600307000c103a41220303195081d00001084400c850443d0401d00e00402400020103d1111b04240c1d9030f46156804405000c900c1800028000c903038080b8603102d0702441d114680320b5624201c20000c0203800702d80007858000c41c417006000066010b256068041844003000c81d050740c40303000160318102080401ca0340210300300c5c0b2100d40c150b8003c10307203401061070f424181840e00b48508011150003c0c10400c02030500d40118207007201100c0e40001d25802c10081c0c0c4c5004285c1c1c0c0394207030009451180c8041e1854858485091690b14051203890110380c0c050340a1070070040340304100c801044403014038146510980707080480301c0c0d80e51050612146885e400801e0380b13007080d29103070f07800240007088648100d1050004010102603c1003405126100da400014901021720050f070340e95062081c11070f49484821820400c00015600406503001708642d4540c1140100d2203412004480d5804052800c6080c801 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 99308075 1250 99306825 99306827
    0x306060819080d05070e040e01020d0c020c1c03020307060203270d0c0b0414250e040c03080c10060f03030305060d03051c0b0405070c0615260715020106081006050a0303 74
    0x4403517040704140c5040c8048014044c0060152911902102a00e03540010301c4590305d4100e119440c441c40280c0040c0070314000403c0051502561039440000000c445210f14041510034002c0340c1c51264019801c54032410700200104025003030150040340d100c68580c0e08810050000780c0f07450034500551f41da0680c0307405592030300140e203000340048030948911103644140e02c006111540b400d0520030030141c62080c2c1c14030055286019580002110b01610043c000404d0ba00d501100c281e0350005035095030380880e00307030702c1d0319111280340036801c072501d00703500483c6e0311501d601c010046038040d0354103002d26120340c0e00300806403082540060200320200103500400c1d0390082411f1004021940001c1c18000340350106040d960220740725000114500043e904100252140c12034003d03000391105051400c1c000e0010a02c20200150025020b000c811048050410002100235114803440c000f4400b041501c080e01804080c003884840d409005040e180100441c0325910032504001d1201c4081803540e18 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 99309325 1250 99308075 99308081
    0x10611150c0a030b030a051b1c05030405040c021005160f181509080307240e0a02061e0706020a0e120a03030b04021b0703021005090303031803070c0306060819080d 72
    0x2130940501a121074030000c03d409000307410000a410081c0315000c808041000108441e00100c1f0029805a40c0d01d00041132000090b602540c0b415100092407034030820b03040e80f074034204090410010b400c103420490b0840000390101d0142e169502c131408a551040c40640b514210340059041150448400b0490100c1c2d210814050b8242c50800082e842d85480100c1d056900192040e03c05090780074506030507041c0e9420030503034440c54202c1000782e070211804440d2154505003004e0f00c62031012511303c0d5080c00603507c0845a150107245035540d0b91036450f090010750030803038003c0041000c1c01864845410302c11040c080c1000d084007c1c0020b5142031380d00b640104408070f515a0496420301c107010290700c0c1940030388095410500188116455803040007400e1140d03a883c2d008200081c09031200d5514000203480d009600b6440150302d010084510714654010740502401c40f441d40d030000400e000f0b26900c10401e84503810107070744810890a1041035100c06c2d408000341030400c00c00c210364070700009078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 99310575 1250 99309325 99309341
    0x408060402190819021c020303070f050f0706030b0415030201300c05090a0618030f050a1a09071a04031b0801020a020c042003060607110603010611150c0a03 69
    0x90740c603070280e83c1c8a0b20380600d0908889103540000000c644001d065250034020404c0741501c40060100141c016800309449020300c110044c903041c1c0034100041080030038010b10170720281c0c800c210b4200343e540e00801005460030b00340e01401286444407603011801c050710b40c0d40580740c068450b40140a404081c80b03400360340c840c01d072440c080c02d10300c50722021010780e02950ec1d058501d07176200f039110624001040071496241d0b00c4001840040c03000c2010340031545c2800d10440b40c011b031440841c401c0c141413060031b090f01020001c0401c41d00e200305242454003102e60038041c0015508840d0b80d1034071042d5190398880040c41c2501076440602040001420650740034416403001621104116034401000b0b09a810043c101800b58104451000701d509044c0b24080c8a202d54800d81200c2602815080c049440043d0029008a1001401400b841024001218003900280000e943c2e517a4840d402403040b000849446c0c0c01b0f00440c00403001020a800c0d42a006200e4451240d10304424400c042d4020400302c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 99311825 1250 99310575 99310609
    0x9050312120c12070503091507020c010f1110020304050f06240418060c0e0603010b04060503070207120b01140d150b120f030406023003060406150e04050601050408060402 75
    0x1002141078000150714a113001d500c0640750203849081c00b8159070f09001c4250b1004040c44440401c0048248e80000da02444007400e0810182901d07500d0412100034010b1512990a84103e00c50440c8804850380110300c1b4038020010780303442080e0038003016101c0000b6681c0f44da4180094085242183e48145c6481c4100c2004000180c2d840c00305031340f00d01039207881030280c81166031401084002900240740c081c440f80100d400d2440c540c180b610052040c0501d0240004015000c0005480b40c0c0c008c01110002c0c0500742c07039a041d001c40c140341c00c289040b401d0050241c482004042c0c440b813030034041e4100821303960000300f40003c845008140d10017000805400c0e0f500661800c050f50702500c051014198030500b2a001c1c40d0342d14200040646058048402801c91441c018007160440c10b81040d9401503408640d551566500d84500090180056410000542c3c50482c1850741d00e60300300065031401c0106a0702441705039943c0c001900d1602440c4141206600034400040040c509000340d51400760103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 99313075 1250 99311825 99311827
    0x3030503070302211602010e0a0b0a090602040806010b130e011214071802130b090a030b060102010b04020f0a08010b130303050714250503060c0d0209030705090a0c09050312120c 78
    0x2c2c14801c5480244d00f40c0300c058401d20000d0701804615070a00a1092550b40f1100410301c180082d6502d240c013210043c40e0000182d9244050b1042181540440b03004190880c01c4407400c1d6110031820340654400340c2d03503a450043c03511000410400e24143c050480e001940203c04c00340d16502e54402d9400074000d00c403001d002e0032002042c0b50303480d544640f4811208a0f0010b8a0382c0c140c50117441003103035580080011200c1846070031200d0b6100c014030f40660743d00000d501082d440320380050b800f40c22001000c580c41800401c10340d405450400182861140b5583d031101c490340e032041c0320a11440780014881214884917000d101082c061401032044e24401c0100105a08003070450a040c001801c8981040c0244052001d503e40e4104031070101030300e0114058001810944924500c6105140c015001c0301e4011400c00c60640d8184000d000030800505404014649010b07a100101103261120740852840000810b241c10300140003a152210500f405192035030042d0b01350a0f0242c0180f203c02c020700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 99314325 1250 99313075 99313117
    0x5070206130519050906060705061801090f0311060601030506101404030602040f08060a0c02060610020319020c0102121213020a080106060f080a05151309170903010b0a03030503070302 81
    0x700e450041100321040f0010710045410302c0100902d240001c2d16291141c0310034800c00c8041100400c1152700702c9800d01e13102c031242c070599000b40d024104208000d4480d0303900d079082000341900040008100c090241c26100d9940d9094015011640284e40064001b0340e10410714482d640145450110380c0000c28025007081c0e80d9948550036039106410100c42034404150400611000b0060b040e0000794040c8140044844105c00964404006180354495111003254100307460003801140d602110078040c00105885004020390354040c00180b4a00502c1040200100c00c803011041e0f485803c141c4000101540342c040c1500c5201030700e203100f41c0c0d00070380c1c0d404001045182440380500901c0682c49101000792030400c05004e184d8000c2511001c0c0381020100000d01ca0b0708010280c0783c540445800440c0200d803040310380100300c807600c02021811024512642502418080c01000d24220003c1c040c02d041c15044c0407820626200040102c5d10900200c0d80180c02500580507030a640009014500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 99315575 1250 99314325 99314329
    0x702010e0a0c05030c01020a080d38010206070c050307060c0302041d01091508060f0c09030a061a03030f0d0e10020703050702040b100c020103230702030301090c020c01050702061305 80
    0x5141c0760811669291480740400c0360781030a01134120100740034005030051800b03944805c00c2501c03860104030109a035503111120882c500c9512111140c5c401c0303407200a01031942c4030750300101c5038070301d00c080c00352080c440000ca030300d48280039010302d040c0e200c005942030041076070701c0714090000030b5042020715401b40404142603c0041940031158041d1240c130020b03500d400c0743c40342150b10400c69034010b0049054148111000010071980100451951503503ea640d0070000304240144690b0960502406080c90203005140d0010300c0071a040030030101d1b04165a10400d41c0d07034490b110070108500e80500841c180300060741d00c210351001d503840a41d05010031046540302240d101000440100b4404036005083d07040510401091500c01e4948801c00ca9207404042c120700183c1e0303002410183c41d80c002c1282075a04050511101c80c2c0301110008030f05090001944a8009025811605280c01e280000d483e100150748015048103850b007501c0e01100b502400403580c486040e80d0500381c2061400904d85d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 99316825 1250 99315575 99315583
    0x1c0902060307231809040510180c0806040302060402010c050c1801060315030305040b0a0315061707090e040b0a1d07080c122e02030103080d0b011e05030702010e 71
    0xa1095982c1c0400c2002906448180310075103c038100100c24040c810540c0d0000f1251415a884008983c518100d6071145002e07841c020452180260013814040c0b281c6803046a90030f8480028403c42e0001080c0391280c0d0496641c6008503000760041e40044085000b40d400f812101465601540c140c0c2c01c205041800325141c880003100520034014004010898203074140308000180c443e1540308441c9520b10784005026004501492421078000030b15030a000f8084d40c800c010080004ea9000d0301c890380c030b4601400c2c12050914204500c021080010785461091404a05840800040340220744550b02d0340846060000c0890a01c1a80c4880c03a400d45080720580302c40070030030400140f4805041a00c40c41c04e0590042c44d84c1c0c080c14894800078040803000c030b00a984403003681e140343c404944070107014203040f1880001c010218030010020091001c0380c0014105c004241c403050054001d0360004441c0d000318140342c161044241400c600996100c0d400841c0c02c02031510000c41c0f0403000003074007414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 99318075 1250 99316825 99316831
    0x309070e0705030a1d070303030b030a1e020a050d0b0411150309060411030d021002071a07020a06150308123304150e19061226030601051c09020603 65
    0x100b2804010400e0181c00390092135107401c01d1414648072441807001d001d036148154000103040c50380f00c0400d198161410441c0a07082a000b24081c16028807908541d20710382407125041e03000e05000c034804180f50034440e82040c02c40360720a4846c80c559071192151a8120b0390301d01c0c12541301d00c540711001d41c41001c2002840c083d81e0188003805960034546046200318200d02074a0340a034000300255a150b84e0081071412460a5611001d0398491440c501031461408811802000f402c401090000060f800a0607242c043d00c038030400c11810340045e4000d040748e02e10344801030440404020340c0d54070b00c405499807600082a102c01084403030202c0e0341403030460b08915a488060f049600c013030b040ca00c0c1a001d80746072201c5204003200c03c14103000a44600c400018030080c80303c4240100419003030310680c0040c0041504401210321544181f40000961b44041421031062210341441c070000702d0702c0000c0320b002d243c0503103d0320b00e00150f6203819021808500407001c441c9035640442c0e009611008001c500c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 99319325 1250 99318075 99318077
    0x50c09060309010b0916051b0c060301080609060601180324020a03092a03080717130302100810090b040f020a0206061e090a2c0c010201060504051302060309070e07 72
    0x35403011303200188180c82c03400809400c0400030700c1101c031703034843d41040490301d0024118020302c0040c1c3c1104882840d02490914043c0c00c0701000000081c10040480c205010700140710a0310004d440d40310045850041a020350009910301c0d40b01000003851645034040c1ea8001505108000039030304117100c080760860f98018000c0703038403519603400300520000d511440056a40d1102c82c070170b1000320040c916074150700000b07246582c0064401d041c0082e030102c40a000b040c48a91541d2400102c5081801802621049004040c0c00540c0b214490040048501c540903015946032107600e0020428040c0642c001c100e9045503030382c404403800e202180028a07215000f42c004000742d040c9182400350380715803254181c2c05204811401c1c00b0302d07681c1c4518141c008446042c041507070f07004035418442024446044000c4011441d03019003074184d02003000d0410501c04d800070008560f0b51070500040e141c04035600b602000b10101c03042c0c01440c1403006580c106070550100c07840035481c1e0010000c00072050320990 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 99320575 1250 99319325 99319331
    0x302010f06060513032a06030b0f10080c0d0902030a0b060901080a050c06070c081c09090605030a020d080f030106080103120521070e030a140c030102030105030709050c0906030901 79
    0x184014060703015480041200340f511070701d4460000d02d0981403001c98000101017504c03100041e021074080e0a6a84400303401d608800ca4456650000074004114030031115000c0e80c1a410929400e07d002801041c0040d0152a5503200395155040c0812a601131210a20404e5403040c001016880402a83c44480c0c8201480f01d1035050440c200420b0308816808204d0b594400c02c101030000f1400700347d0318940d01003a40c41d1074a0b00c91030b1800512000040c0c200407072030b02c01e00b800405c407244215600c0300d9940310f0351690240d240c0c4414400c0c05555143c05001c0d05031703100395400f10041c01d00c40c240009590241124a041407000446410b40398801c0c0e004d1000650294010701c1406420101d40d410300000c1d050913445d20000300d91030780030b11100802e00c081c00b20f140800204040d000708c0001902d2280102550000e1615180078000081024000b5005108a461610309410140f0849050b00d10050041c00402c0ca002031380c00281500608400042c0c03400e002203611500c4850295010f520454008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 99321825 1250 99320575 99320591
    0xa060e0106080a080403121e0305060907030b0307030b0408040b0307080a0606020d080103020f040905030c030a0e03150c07050106090501030809041a131d0303040602030610020c030717010b0a03030201 88
    0x25509451664104a031641c21112042001030382035012141100c0c3e2104241c640c107038400c641920000c1088a4038040380707102c0b541080000341c1c160300092150108441448036503d500c9405c4044a64400e68140c241c0d02242080c00400d03284a803480c0d000b07210381c02d100e14064403400e1941c4550030640d810740110b8045070600200b0140e500030b102c0a4000d502c01054400070040c07000b07000781018031010740640201c1c0141c800584481c1c00c0100c600d038000d0100c0b036a0303810301702009590f0b42c4180401800a5210031081c216454041407022059842002d40700d0075495500c0f1a03681507100c020110380c15980c0d5100090b401c2d081d80229402540034110540d00e03400144281b0040e105101d0034178031409940c408840a582d05c000c02501007005404001486941140051400703020a80081d0304501c07000c42000308000140c1c00071407095000342d460420a0405400680c4e40d07001d07414090341e041c0c000f00303400d010080150900c007420880c90710010560700c000b24040340000070290001d600603519440c1c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 99323075 1250 99321825 99321851
    0xf03030903090e091902010c0204050408041d0c030109022115040f020c0d030b1503040c03050d0207030807020d03200d080105121009030c0c0e0403030b090420060c0a06 74
    0x30300105980f8038aa41d10b46051002c0507165011980b00340c00300e07040b100c0c085007503901c10303040c213150076501400c04c10040c1031a04280103107810030b108915000b031481594104400e082544103002e80c6082a100d802d503401d25041e04060b40203c10080c4000044c449002d42c640312a1070402e0184044140100000d0300410601c030580c1e241e8407180074070700c2c01003010414100d40087c11590b5105540741c0012014188400141f40500e500c05038007081001105100500c224a502178044074464402c8914a007039403942603864000c144070207001703d001408500e001d42422030004040301d01c01d1074841007610302e509002e900c0c402954103185403503006904c014071b5160000da400e805444200e4200081600d00c184050303a42500c0c0c4000e020031903ca80d81081010301409080702e20640c49010450110340355107100044100450b03040c1c000030300705160440a820150306aa005541040c10b6115400114101c5041100a444103a03002102044010b54010050002d40708440c070454002c6180401040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 99324325 1250 99323075 99323087
    0x50703090c060305011a04050f0d0501110d020c0f15010b130314010902120106080c120114070f030c0801030b040803040f05030313020a050f210a050d03060602010f0b0306130206070f03030903 84
    0x40106d08910104802d1140e5950407004505c0c0103401c84e0200101099480c1040c09000c02d20300b40403480318081032a03094070000b60041c014055a400132280820b2542d981d055035000352001102035040c5540051212040c08030081c18021b840583c04540c81e0703030b2030f564500304440801d541905659174151100452403c40408000c08001d6402402502e04080549896090448856111702d134040d0000004e030b10290031114010800c1000100e8601c0c0c45000030300251245000000000d1801364038011143c001c0100c1030690b0303000340401c034039541c0f01d0783e41c0980d981c4041c105030b50440804007080c0015a040000b03502c518541038170204650000d00c144080f001c0e0b01c0d0081388c8180700e5400c000ca41074a034104006414012558082d080c503056114103401e25901c120090003e0241c801010500c0750107400100446045500030040d803055000b07080c044644444540303502d81c011002180c10303400b04821185585000500780b510b404016564030f0680d014268003100403c0e21200302106054100e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 99325575 1250 99324325 99324359
    0x90a05040b0906040201050d0f0b1504060210140601050c0a021e030c03010b030d0804020d0f0b16020307170922060501020d0f0503040222020d0f0f020a050706050703090c06030501 79
    0x4004041078142540087c10034021045014826580e80034a0050440f860700301d00c81200000d0180c03200d103181c800501000741d0281c0030b014007503c141c040082c5051010f01c00d00b00541107070025642951540b1004542603400960205070714440ca034010340141e5a10600504031680e5801704056200d240c10525051100c5095102e229034502051000144ca0200307140001b15010728021034259294400640b51001d404805458001700b1100c0d0000c0041e422001c9000b6401509040f226502c008400c07a660710403280000c103281482c44030301e030000180e5400f4018680004066690f1140c2e0011500d1400d2000c10040039882c0e1540f200f0005960107010004804000c2e01e44016105034405020b4164031001c0d20007030040d52a038505001c89009c0307000028035038034403040c159610181100b00c00003130042c001076030b81200d14140b55030201c03800603c00c5031038020340746c0c035598140042500c5200c01820028058014142c44a0039000000c1301e1034008000340600f504c0005540d410081c05100c041c10f05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 99326825 1250 99325575 99325591
    0xf010303021606020303010306090204060806090c0a0f0b09011125030c05010302032505042417060a03080d1506081005010302070c090b15190206061f0c0809090a05040b 74
    0x6482c06120090340807003240d064a070003820100d4510840d2010a0040c0000da0100c2201d0240c142802044000860840440c001c126024a84c03243c88a000c920f4007103040c440d030801058104040c2915502840c2d41c0c40400031240305039407404220444c452140e2130440200c1640341d80c0d10009100b04003c2c4000400175150a20b021400c40c40c0603a4101c412190034500b0740c455151a02c2000c04040c4601c084502910800405417084902c0c2500c110350b0001001840002c54010500c002d070491840520500c40e00004002c0d00e54240756844813616903100050158020f07444e4a04040d6071150349a40c0c900030102961040a00c0c90240d4004000400ea504131a040600410511010501200c1010140d8408200014110304464005044105100b400f94441d5501180d017800c01c10700040024401207403602514059900c01c3d00304096121350011484424401c0002d20b0301c95840343c60b80003101840b0310151454100d01800041c041d604c00c9502416072600c1d001000104081d41300e156403c5115 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 99328075 1250 99326825 99326863
    0xc0c061205010e0f010b070602070501060e06040507030902090c160206041d130c05060f070f0813050603060a09051909050d030b040c02060606030703091401020a030513030c030c0201170f01030302 86
    0x24550f0f284d10100c10300c14529090404500034050001e1075045035012644103000b0411603a07034004544410300700f1603000b072065240c4400a0451030007402000309560b8003c041030a0741e556281100066000504061208910304d8510381c0140c44100c000c201900f9012034000c15024503642d8070508002c01860701e60481c031202400400a1f80c0b038080b0500380c52080358161f40340c00a200700000f072400b458601401d91441001030300c1c1071101c0400204a09040c408510b40c240d84c50304203001c424482960110380143c80030004200151203940300307035049194180000c030b81200d01000d0409a80107407506071400d4000200248805070184100700c6811401c0c0c1d41070007801c0d48600080e454120050100380100d0700000015201c2d4400e600c070b80482030f48034401c202c02c00e04030307100107000750407034601c4001083c6400e0220340c0c00c541ca2002c01e0401545070b80d031004195155a801c942c2d58021040407810300614504695100c0b0071182401e200d0360710208032036540e41c51420000d1420080c10326034140303155 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 99329325 1250 99328075 99328081
    0x807030b040210050c0105270c06040b1305030d080703200a082e05100309080f0705030706020403060b010207090606050a080603031204031809060506040e04030c0c061205010e 77
    0x2a41181c0c040e804444289064940340000e4501784180035117282154038183c00c1001600104000f03a80311801d5506400d22051254500303550348058a4190b41c4c448828002041440404c0006000320000141d00112503640c910101e41707094048003080c0007095840c0100000310fa403500c910081000852080c8616a600000030f996912503d00396004010002d000203403001c4007800100c030a40320007988070442a5a0680c0080e07040a00e00806102c1c4404071404100f0760321034040c1195272500505001d2805000c21100c040aa000203811140350105014840219031944043c1005500511000c0380010707148000a0800038540c11090006181c00c0d8207000d030507442429155003801504081c140c035150310000911314028102c1c10341505d01418100410503074058003962140c028a1003003402c00341ca41c11580240c0724680a001e4002c00c003408200025840076050542141c02810300c45042c501d0303900c07000701131035268008902054035512128010300b41845524014450b0000401e0181 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 99330575 1250 99329325 99329333
    0xd140303040b0a0f0c14090103112b0204060927090b060108070c1104180204020703030b190b0a1b0209100513270201050c030324060307121109090f040b01080703 71
    0x51048280d1201b0054045588000d6900036130241100d103001c03048041e241c0b40c01e0492008a80f107048500045038000f0381c022000c2c1001402910240c8100c4d0300c9d003044450074220400c0d214540900404210361f180308060010300712908c240810207001c1c452850389443d0420000d828100c02404800411402c10a0b10380802c034824080302507010111400309504940781640d0080c48541341c8065803081c0b0000d000300c101030301075118054140058134505403003140180c0300003401185100b91501101c0400035115a6481000f4948082c00103209640c00280290082510300ea401c413102d0304034480003001481180b600003032440e0410107280c424080e41d00c0103050050b03035001180c45001a0b9002041c985c0c1168019029109014002d0003100e80301d180801d20355400c1142c4003000520704808100500843c1041c0086030701c145100d07201c801d0744144201d81d0800900032500d0742d40c44140240300c100f1103039807424000c2d8010b05a81304040c0316810305042c105120300040c0d000203019801030f5420000a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 99331825 1250 99330575 99330587
    0x909061804060506010e1207030507050a06080c0912010e01050907090b0d200607030206151e10110106030302010501170604021f02010b040e030a0906030b010e0d140303040b0a0f0c 79
    0x59880140403480b0384404c80181d8003207142044486d80301091741c82c03c0d6100103001440e442105d01803001c8807021540c800038000310f8240b40c00b408001481d4400060780541c40400100380c0f04c0406443d004034a441039005608681c005c0a000c0c240b40d45450600100c0541046403001600042100b000303200d143701f0000b240300d41300c403200030001c20310500748000110798500c01c0002e000c2c0143ca4166505410701d00251031b208111000d43c01c58400084c01101c030304040c44107400d10380d05d0090b10301e04c50107298100b2040308484090355040020b0542c0f1070001102c00e0050000640c400e40003c03c0d9075051110441d0303060360305070b1015020f50142003040096174545481c0c03d4040c1540d90321000e800c41c00e80c0c08030302500340080800d401a00b0304038a1402c00c0740000042c43c52650580d00c94070f0301078407001c0c2101954400710313000c1d00240410009400520b44111b401341054403031101250304a49203140142140c004407001e4800001900c2004400d00850107204429034002c40b0400210701c0f914009805 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 99333075 1250 99331825 99331831
    0x30602030a050a020a0e130605040e0a06141009050402030f0709020a1b08030408180a0b09090601110c0114070b07020102071403090907050705012009030c03160e10091109090618 78
    0x101c7c0c030400355082c0310840f8070b03444800070301f002420500c4480c1c4030120055585c84486000c0300d040c0e142104541c0da0b03007810f001841c0210482d00043c0ca03450701e841000c030054200508141e0f8140210320801c04807400070050500241072003a0056100c036100c01c4054156481d0400c0f4102000c104140f40380011140021681c0c00342e4000900ca441e4018140241d290301d459401c40e5400801041340441c1c500601e202070308960408a40300072041d03507480011581400c06030100c4c0103551040d07400d0342441d80141140712011068040792400c1c80e820340c0b07901910600a40307038000540d6000800c1707420f00141c52207070b150010a6200640c54a400e1101003a01000010021820490003040d540c04000c4290002010000301102e440c83c64800c8000040c02680902e00240c420721a00000e94000d08000c10180080c800744100d1200c0c491402440487c500300c000c05015980380c00804c0071440c180300e440740c87c440303e5660a44030340b2480d018060061042001d4801d9200d8450761060107900d8582e200206c0e4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 99334325 1250 99333075 99333079
    0x7080d020310080709050a05061806040b0612161107030b0115090503010e0105010609091416020c0307121a0f04150204150305091209090403050c0a020a030602030a050a020a0e 77
    0x107960764600c50858500c0782d490b042600c207405054000518200e064001d64041c3d0083c00041006894020800c101558064030309290b00c50480f0000c1c00742e140651160640c144050b000700d2901d80c0c0d83c8110100c20030119076404580343c08486111000d680b1003c2c610f003080d003010051121600310340b034110306408144030340704441c1c60062080c0032080c800c0c3e001500800c8054003c0c0050458504543e002e050240030352000500c2a03000000c100c1c1d010b00030b00317a26044c2406e5a2445440329a195030b00424403045903015480307541039a40494804000440080035004e694185180007850400c000310502d401140c0c0300e0a0034030038130950440303017011290465442808a5a03d120580440e4080e00490707200008801a540c070303030300542e605070b04035500c50303401501590014110a80000500d0140321002c0750070540440000b8002400380d0700034082001c40200302d030000101c07603000510b0b0501c103400132281940c01106100b0000481d02a07503400c0107184105505003000b0798001082000c0c2412414 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 99335575 1250 99334325 99334327
    0x9020f1e070606081c021606030b0609030304080604170a090b0c1519060e010305030a05130503100b030d0801060503130606050409060c1d0105041206180b0702010c0507080d02 77
    0x1500c180e0031500700d6060030382c05031050080076551850551600d5007100c0006294148240500f41c007403021540309080c031400c0d0071411040d0300303259040303005100700c503841600300e5000c100d460f08981d010000b801c01050200c00500f0341d46018034107901d00030040030909200110500064044c607070070940b0301040d1012041c019403108032484215242c041c1500f614900d88540005003c24030744021105104c0080c050410f000865840c000141d0000c024480a882e0390818402e000d16a88602e00800e019035450000c01d040796104c41c00681030001300c001080400b0b5580d0403100781030500340455000e0226900708155903600d448070242280c800241500d030100a0b91000204116150b40460040c01000d04200b005180700d180c484001c100007806100415200390b070049104410184194200e44180d4034a818103103868484c0e07100e0081000111a60381e10303403078120301480a2a0038000c015008054410060030f120a000c0c6c2103a501c20341c640300308a4100003003404103146108035004a03013000c0e801 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 99336825 1250 99335575 99335617
    0x40302040b13061511030408030901050705120d020403020901120302060f09010e060f01031a0c0706020a0903051015080f06040b040302070302030f0307050c010c021008060301180609060609020f 85
    0x40160455035049085a0f2a000c0049213402d481c0e002c000380c00e42643c0301c0c04560070020903003a50744d020310320a40c1e185510800818401d944a100070740f003501d128008548155905820a1a40f600000d0b06072b0210381e404a01042989803e11580c2e00401c0d1440c4d03039210880150b1402500c4a200401800407943c0e0f41022400d01e4100b544800300044800c02901d506080c5420402d283d140284400d66010b90003a1a0b200e514070130700e04560103054003000c41d5140070700355503c0d00042d401c8804030304248218244000089007082c8460028640403c0c40000c040c014501c03958030101c40f03500814210391120343c071803141c0500007841d6a0131a03002080070031b5070380d154a0106d01d082115080290940103900c842821080008090175210707104006030340c0c000d84080011200e880381c2060107035105034100306400c48c02d4000c02d4140e030040300280000c290100080310480848a009030100c0d000d5a43d82070b0b030001c1c0038181c4105005007210352015454035203000d980e00340b50700640080c000748189140c09 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 99338075 1250 99336825 99336829
    0xb030d0309030504080a03081f051008040503120c030a0e030906070611090604060c03020106090b0d061a040507050403020306090106050f190812070b061518030321042006040302040b 80
    0x543d07006103d03420844088401da0701d001008c03044207440c010008401c1c454901030000d0304d03944040035144003804410300031351803144c119126000a070060307440340400c1180711142c0100079922031094001d00320803a5a8203255409a0071202c01e0b0300310840c02c1c7c2040c016030840ea44c40e2012660642e030004400b00f0103079545031608006104019071140d100200180c00640c440d041a420305d2154046d030000c0050980da1420001aa134043c81c58a82c8090100c2903c400103003203601ca452000548606047c030f9030780b1140480c0844100740d940d5408600042010000c5103010441c0b10b0380405800c00074440e007450007010540080142800c5445507403c8014a070f0524001d031010002030040c0e03801c5031234550000d0103061455001e00d6081e1400e5284600007901342c205041070101502d40d90075054504642c03a40c01c0800345c3d28840d14103626002c10081c1048212003248a603110781c0500310b4040580c28213280c401e0300d0200c04845240e40c0708600d10b0602d0540c0d03c000036039003203a805580125081d621400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 99339325 1250 99338075 99338077
    0x231314011401260d03110f03010603050615090f0103020a0203160b160e0306060402160503040303051305090f06060306041416020732181302010e010309080304060c090302030a05060a060501030b030d03090305 91
    0xe507d80401e80301000000d10300d46e02d0303041217008100c1501d03160001440c00d9003040c45441a0744089030001c00e071540c10310065100360300600d041d803070361320541c0d04080d85070300e040640d00703030101c2d0540d10034921034144003910441e541e807101c0c18001824560581c006400209444420050555205990208501030910010341ea6242e60301d90000030b490341c070f40c1c8a06d40541150040a144540786840441c007250301d00b0b11411050107134480414200d075595519003001095030000700240d03000b907268060114030740c00070100c0714060025030504d00040c40180340000e15001a035401303254003440d0460516103600d0102c02000406501400384184960b0304408034030410310403c50300480d00750344803c100b0803516900c02040503074801d83e03030841c5002100004406907261004040c0c03403003d0030804200041d915a108010b540100c1c24a05040d032b0352900001e082c541c00a40660701f0742c01c4402008618212441104040c10007420100500c003940b00210759a038000749180410325079640c030340c0c0307042c140210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 99340575 1250 99339325 99339337
    0x901020a141e0301091a010c051504150207060203060f03010516030e0114041104110405150306030c04020c060a15060f031e0f020d231314011401260d0311 68
    0x2122030f541c1c0c0d45d4550b00480280840c5814481401d42d8681d100724962042007049001360f00300c801480c200703e540b412003005045c00380c070072294400e0b81c41c21104100c515002805280e0701540d00141c80e0b00e421020b001c2022120340f80c081c070036490b0408008106039030b817601c10300d0044c2520307000441c030004a004600405034030300210445800309082004015480100d0034851809403800d0107864405040e400840c06030703000700c0e0ba2111402c1038803a280420f20000e1903000300020210380300f4107580e0000c203080b03a0140c0c3c40840b06421010030041c0103403860081c0036006155800c0401c4092400000034481809400c400741010307180c0301c0010a06001038001c145022000c0c3c42044604504070000700294045044503143c0c500b820006100c44080034a061140342240003034400c942d45001200c0034803410f0340811030b001001101200c2a8810921482c0007075030444800e00025410f29102e818a100f40148401101180340100c1c040580049810304c2c405801c0d01b004124a031107000042d4041c0156 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 99341825 1250 99340575 99340627
    0x90e0c0c0714130506010f0f030b0a030b0105030d050f0a03020306010c05072601050903071704031401021b0102130501110a0b0405160803040e0402010804060605040207050a0302060901020a14 84
    0x80d000820003690030b18464036030590880d0821100540003502c0401e0302c904840da140030601210281705014041c42e040580a040341c035001030056048170008406078001d400079a40d9410310030060000e82000c200702c1d040c00006040450030010640300491003441b584941c00105074000c0b0225070103901420b0140c07030716a400f60586400c6134072154603007482003000360300b40300d034003902c682c0004140e8040c4901402070680402541c5800c0041c0c130384401d481c0e140850464087c004100c0003001c00c054507015415445204000b40e43c42c6501280e83d9101c0b859800a400d05920411810260480016085046440a00b001d112100f0403050a034109048204050082c044402c10001001008101507084100700380040b035030951038145141d81c0f4081c0340103808001b410a00403401660062402030f42c0280f0a40300440c0c62600e5102080c144d03041103504545550005d91309008058050215070b034800d075240300031424208111401802c0e0507442c0204000d040300000c0c1c6244150601600c00459400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 99343075 1250 99341825 99341833
    0x61b0609060c0813080f0f0909010b0703020d0e010806090a06120602070203150c030103030509150c0a050105060108100e040213062607060e06030604060320010e04060303090e0c0c 79
    0x8507040000c0604440180780b8002141000015954114280d50324200d5070410310a0f41428a910303801944c99001e40407296104106000a82c001d40c1c41001e01c034007810705c55241d180c44241038507001e85821034400c0c082c403e0000d00c600d2850940da005144a500150031109681e0075103444000300f00408a5800215103841d03c150001c0600189400034001d00b0b100b50201c4114040ca81c004414070a01520004825103040004101182c803a6001c1c00e290700006000700c001d8003009030303414225801049418140d170000e004000610401f07104159100b03900f828851160310380050581c400201c04e01400314581e40f0070002c00e00359141d086030000400113074401044050f8032480c00c1111844d04074022078244108551820a42c00302103401c030200c80c42c0360bc603000801200420880030750001061550001c0c0e0f681c40000c0851001c5c15540507800d0686030244c9419a03000006020030909038129005a040c1700d810000a0b510403c0d0400b00d900b002d043d00c4007511401000310315485a07041c0ba0201d84030b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 99344325 1250 99343075 99343091
    0x60904121206060e13050105010c080d111902010b0d02100f0e09010e04051b0d02090915010b0a0306060915050708070b0a1a040902300f070501020f031201061b06 71
    0x1d001343d11041c0d0382c1011a0300131641d941e400703094801e84d0001d0040134002101201c2080c002078a240113018001d90114001c07440003602070041d401c40e0400150340d841d01d02c41140486c110340c0c082c402c0015000d0107442428104030190003188104940002800030082d50202e2100704074412101b4400c840d40040841030196503885000c000301100ba030b4142d4032401002140e034110b034050003609001001c05420311810343c44640070020080c0300100800307482d0040c2910748404103054500c05018199a82e030341511880300c803038000c0c1168074a8001c8014002030f24810b0000c100c900011000f440750515082e66a0219841c04210301c3c0100c010051540c10f0b2002406007140341e540111403104070341e001040303800342d00400304000c0e00d20894011f504008000715807261000321320344000c0b109074a00f400344096074912040f40c3c45c0160485181c4815000a00e040c0b10543e03040c400e82c1505410f400041d4207011000700d06104013181840713400d0502c42c1c00f4100d50300d01d000e000c403024a0700d90409030400c0480 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 99345575 1250 99344325 99344327
    0x71b150e060c0f0712021503070c021302090616050f070602070b0a020705150a0e04090b0a05042301140f0708070507021807020d08090d0210180210050c010c0806090412120606 77
    0x81740120304034820008021200e085190300026a07200745c21540d10000606030316004d11401030604501d032f18205400b000310000c1030f110800100000590b06490000010440c18900e04202c22a02141c03915000410100990340d80050990300365141c0c0d50015030b0303450000100741d1609159a01c082c1e000380302e410000c421a1000b6020b005a07442545403115802003078000c02c42100c1188000400400c003c10124a445070141d00055110f44601c0c105084c5e10141f407030a0403071000390460600c160391240e40084541e130029844540003421600e5180e40e50030702c2d143c050b11030540140140308114010480405540d00e8a00c0c04080010040c4d41018505141000079211420b145000c0c1c086940c1d000410307040140040e00040744801c95000e811007400a0180d40f000d440c1484017140c40f084003214240c00f50359a41c1d0440c2610309a52035032079440502c0355801c4d0a4a644007030315414880c00b84100481511582111076105602500824224a400c0300c15102c906043c000c01d801c203850140046901 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 99346825 1250 99345575 99345599
    0x901180f080a030f030507140306180c09031e0a020d0515010e06030d0903030914120304060807110f0c09060103020706060603020c07050a0b070f050703050102071b150e060c0f07 78
    0x1c2d030003070303940c203908040400059040c0c90042d210000010542d92110500700d6890b80075640015000305441d00c0382c1207254400c07103070b16816500110200380010b29405a464100f0201422100c010400c2140070a051078241d250807100c580070340603500e1440c212003040424883c502000c07016003500182561100c111040000f42214800e009104994042020500907540e010403640c3c550b907003551050030503588142c04000b410342150032004000b400306800a046c002751000d446031b40d071030130360500c2c0000c4005c250300c10000c980305246d0499060b84220000102d040898440f0030b031741085a5868001c0100c00901c18041c0107400e4234a040b40c0815410b074560000d201c0403008004441c50340741ca1320204155600301d03100d0500742c07000c100006400103142c4c1e140584420701880644000507565191301e4207913400282c1c100e410f12490301d00100101c420688850160000004200104d0b064940290120343c80306500781c850340000c10310001400742001840c04801030b0703a00341c0780595911201c0c09a6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 99348075 1250 99346825 99346843
    0x60501091d1b0a0503011401051606020f072301050f011206020304020105220303080a0e2a031b040f0e030703030509010e0123090303060114070302010b040908030901060b030c0901180f08 82
    0x2c5107c014614202641c86001640c085e103203484243d10406401355140d200a5119000a04101130280b003502c01080030000742c0949195119030200b00810000142c9085403001018120031351802d0700140300605015101c00f0070140c0c058001070762501c0324001a1404c0c01140c00d03062081c150700391001c5050368108035100880303100792500c194685801000d0001c0d9400501450300300e620043c071090050301d9285141c40c80180b00c1e0f44c2d12040c02c0c10840840e003450140302000b0030500340c1c025078083c030b03090074811014078003112801000b8a4000c1c802c1603450b0311540714040d0815840700041030b0381210a40c000c0ac1082c510300c0080117030350300c00321f900304251746030b48101c1c0a291400c4000410b50380d804012284601c0c0140c0d607200880f4181c044402d8130340c000300e07000c0d000c641d40c803d401911a10743c1c2c0701303035800c941c0540d03001c03622880c003200710a003580c0310742e04a45440d072014810b015641c09034500380d4224a0003403d15003100e000c6071500d03c2401c15a40e002040d0101043d00c0020754040204000d41 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 99349325 1250 99348075 99348089
    0xf0b0108090606100e120708030a080c09011b140d030b030c0a050f010507080408011503020f010e03060c18041802090906060306010302120c0907050409060501091d1b0a050301 77
    0x86590780c0008258607441c0444115400102035560714160500c15040a03c00900080010288401c031030021450003149812207d1b80b41e00000301c1040187d044000303240e000c80f00006151900230b9202c0001c0021031404403500d00301694041c904100f201c84860780b0403900f10002160100f0140601c000c1c044d00075050348900902a041907485a410980c5000f000c2d0f0302c01402807460180c00000440e00c0340c0c00301d0405c0e0f070f00c98024800803803404003e01440d03a0007243c0800c04500c850860040015003000b14110905208602190f1204c03038602061050b40400b42c0180c0079260000c2401c120303c43d000141d1096406890800e13100582902c441001b010350b402a40c0d02a81ca40d01c25030700b1940c07a0000c0d541681d1682c4100300400c014a0403141e043c6400401c1e00c2601c00f5107001e030300800c404a80c10f0310b128002c43c0002c0b600f0311441d142e138411071009103401d181288800e850300d01188221440486058019281d031b1000415600000900780f1040311901580f940d07030030b40341c01c0c01003042d042802141 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 99350575 1250 99349325 99349337
    0x7091a040e070f091a011103070813060e0301050708010b160203160603050f0108060112060f1817040b03010b09030708060103080301050307050901151805060706090c21030e01030f0f0b01 82
    0x40b6010360346101783c0c2541c030024003102c50054000b034015580c640d5034450900d00c92000300200d10016000502030606980e0410041e01e0440c107100700580f00d00802040c00d802603252404001d61940d010300d0260440350646a0390b503555030b10400d0015800c05107500070790140300e107802d80700c5c244240e41448001c4031046e40c0c040085840b0600103068514007840380400c00c3d44840014000402100010b80ac1c5070311a80d00003030007003006852541640c510b007002100300c8050740910303410b00c62101a5446000c0002c039441c0e00d402c0c00c1c1240c50f4034500060081544e4181d0118003040d8585003080560050b049810403030f40c0640c1d680c54141d040398024080c850090040e048000b03180d040041e50241620655140304262507030000c001c450401307440148000707544a0441c0068151211401091143d02854012030b058815003098031050f0b400380e00580c000500d0525000380c60780141d001210060b41761904e0900d10101500480141249a030300b089054608211409240c01a6110321a61103003031f2182 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 99351825 1250 99350575 99350579
    0x26090d0c02010c060506060706050f090c0604120305030606040306060f170303010b0706020310030816140604120807031103010909060e06010b090f06040905070801061e0207091a040e070f 82
    0x121410141800e009010840303003420a00054110b03000503600450192100f41041800d4480e00240d80095551525550a490500c2440d8000b401151803291065551b6490301d490301110f241d40881c41880a010005c0200101d084c0d5130f1181c0c1241c00840d0441c0041c41002c0d00c82a0324060310030309200d05c8100c9c6440c00c03c0090004808800c3c0c0f0b040f00d260050f843d041c5140d40d01c403040691710081019013004110800813000a5001c170240000d101c07044044203107a280b0789030000350340040c503684c00b040c0d520200421000601013405c11000380341c9894000910b4070380e0a010382c040d165a034054024200e0110022661140ca5801034031080d0050800340007000b050890309845040a0050008541040000d6111802c205940c9160100301500e11440d059a9000c0b035005c40d00162240c5c00050b0301d600c01005460380c00b8070b000c46034103224003031045040d0048001035650f05580c4078040f050380c3c48019903e28002a100c00785010320002e40103210429400354100d880b04042e0188120b012154400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 99353075 1250 99351825 99351827
    0xa031503060501061b020a050d11060d0510090c080109050403050904050103061e090804050f0a0f0602150c0903060c0f0405030604080c0d02070b090907030e0616230d090615090207020f060c190326090d 88
    0x750c0002000c1c5859900c516402c10315240080e0000500590920030100140d00c015140d40c0b203894002c0d030043e4400a9001c0c0c0600d0510100c081038200c01104a040004a00c08550b00c901140c048580403650740076004414004a40080501e074403440f41202c030391a000401903000300b600720b00f095100d59001d000341d840051805890042e0102039406610010000e620030341c1e080001d101000711a0100c4d03007810794940000f1700d0403800b1101241c2c1c0c0d0b0b201061144600c10708011644180142e4009442c10f10300701001882e85002da47c1d03510340b040c0b02c40e00c045031196000350b104046641115007542d8491500d09480b1442d002100b98800014800d036a03810044d051050294076800441804d42c1d1401020031460005400f8a200907a0115900e1450010103a51490181c0c0105990700e0f0140c0c8421141c0100201640302130b0f529401364000b000000070007180480c003182003c0485e0041d00400c3c5803401d040300d0f030382d0500103500300100d0581d80301611402980a658407c90f0b002e800c072004200c04800c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 99354325 1250 99353075 99353081
    0x150504081b0a0812090301151212020f01020d02130905011a090f040f0c08010f06021005150a060c05010b060f030a1e1505030c030c0d080a031503060501061b020a050d11060d051009 79
    0x2060004c0b070420309e04258001340c49940f2040e42d04d000b40c8100c449051042d0340040c01c90f070000030b02e02100c076030025901284031802d0030760704010641510100203039031600c8a119412020303a04401d10078540086c0503e8260f0380d078402d140c504d05c2c015000300800b440190002000302804101c590120701c40c0000001d100942541d2032040e501c0d958094801342ca140c1e0400000f4100242010005104100c0080d02d80c2d1902d01c50413000b0401c9540303000341401d90b404c0c00381c212540c665401d40038050810500d140319075103000b01c82e08065505030004001c0c1c0701c9520280c034a481110a401075504208410074124418103812081d02d60440a40320711a03a02410981e072100d030800322641068643d003e102c01321b061440a482281c40c203050101e00b0340c00b9440b079420b90751500e03001101c2044e80ea60050217490742c0201d0308242c001420700400c1c1415402d8002901101039880741c103200e11340c01078817601042800500c400024201801030703620380b84110003c1c2d001d4001214403000203c0b4250300011034a0141c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 99355575 1250 99354325 99354329
    0xc05040b0d0c060c05010b1512100f1401030f09140d0e09060f0a1212030501170a120507080c0a14190b040f02100306150504081b0a081209030115 64
    0xb610603038051034400140c440e01d2203d181a21155600c40182e42e1603216822900341051102c03500c10b503035484e4010b0b14070944002504c450f041441e000720500200400070b901c9816a00400e411400281c140300040700078102c3c01555070403544c1000d26280804ca0f002c0c1c888001030349494255070701c0310200601110f0325100490b0703242d4014100703404a0004e0410112507130441502030602141c043d2101401810551610001c80e1300400c030f801012115503040c41032b240034044c0170954440c000b800c1d46001d580c031040e004026000c0041142c03207201460048003211111684280e000e61144c099642c40c41d01c480102c101940e0340b54003c12031000c40003005c100c4012005010b20300820aa501e51684030707800400034402c84128014060f05000741e42c0358005000c01100954000c11218103101c07601440100fa525444240002400280188440440d00e094000042014842810040c000040d150003d69028480d280104c20000380400038000080c071040e1000c0e0003c1c042d0348040402c20307005072424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 99356825 1250 99355575 99355583
    0xc020112020310080d020309030606010c050607031a0d14120403031707021002070503090a05010801080307150b060a0203030709050603041101121d070302130501030809090a060306020301030c05040b0d 88
    0x81041140300c66a501540e00040b41d102114025516120308602e498402e1660f200513074004110000315203400c00205a1103002860310801e2000c0c2980c41a80c0c503035002c0e003004141501c0c0c0343c00426090030091607031807800c0024a04a41c244650030400349012a10741565124022a41c403003c00d241c10307004940c1129410303942c1d0707207140300110300710581c8013005010b0f80d003103015219050500305128000b4013507007802440030350303501c1c02d01d80e042003004111a8800d40c10300c0f0b4800010440840003006641101e82c000100c00091051030240030010400c1088040e4401c10200d0320003406540000514450002912480300c40c41d11a000c200342e030300040710000c06814208105410b25441140e1031244011340a0000c506d507180300c2e10b075102d807400c03241d0540c2039a441080304005610308141c0e50070514150400400c01c550458442003418403502605600484082c3e0120711500000c1d0b00403801150064411500d13561289401503510b8140d02c41c40b441a414034404044a01e00790340088a01a40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 99358075 1250 99356825 99356837
    0x4050a080105070c080c0304080706050903060609010303080c0a0c12050408100605060a030b19150e01051809041e06050f09011806050a150b0403020411270604330c0201 74
    0x4c180c0c1c804145900400c040700d034a0105020005418900300300380c902038802610352984481404080c9480c0c00001080948207520100c0100042900946059003110010600580d03985611006440c0034445a000600d0054640040d002d15503005010f00305a5001d14151500c00c2e0341c00065005030341d014007903198090b00400507162082e00030f03404520741050140205403015004100040d0621160b444601d2440c03243d070500c56440d0740802c840025040908081e810706007070600411448040a244a010b65a0040440c0500094400080d24510031280d9804038186528100c00030b82025034a030f0740700e4000030380800c4d03c030b003410b006084a010341e04400e005c54000f10740b11040a418090080c1c1201550790210030707072502c0e44100c0c000186c0801114140c1c1c6038614410301003180c42154041070078802c2400000d840440005002608909403480030980b24082d0b400149103100d44d0b4002034100346402d5005045013042000d848604079404a9207074920000f141c2a00c0000403c0030080c00188 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 99359325 1250 99358075 99358097
    0xa050c091605120703291203040e060d020102032505010507051207120605060a030917030c04060c0302010b0409050a05060a15090203100b07030c0c05030a080d0b010c02031204050a08010507 83
    0x401002050780c88540340c0350200b10915800d490548840e460b0000340001b07081c040190289007082c074009030f088050000103618040c81c0034407205501202404c01d501c5a84440300705029a03100b003003035542c031901c0c0089190344a0455262100c13204643d200840321542807030001466603000b41e00b03540c00461021100700e41c07640d64203403c4451080d540c8811000c0c50762440042041d8403800c02402404480362800580501c1c0c508150b48942035080d048559190104200040c02e074500041e181124060b0403c42444080d61406034050542d91500c0c41d0020700c0c11385000305000000425010050054080d62a0394846030450000d9a42c10034044007001c0d8041da0421030b00030030354000c5500055000c00c0c5000691104482c540039030001005600044174898503005000380300d1300720b0300204070880040c000081c640d9103007000d074016080b503903410903680c2e00200307034507401503100c10038055000b405d940002c0c402041c000b0040e042030046a02070341d07000d10301040b1070b4014030801c2e01500281c0c4840017251 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 99360575 1250 99359325 99359347
    0x1f03030507030e0301060b0301061116030c03030f030245030d271d0702010912050315030f100b010c050c06030c040b0f0d1817030a0902030a050c091605 67
    0x40000030702207030035661b0340100003040c688201c0a075000e44030903552040cbc440008000e180c80d2020b903000d031408020399403104200140c0400c110000700c0340e060503d480c440401c00d80c150003c0c01002d280310300440780c0440d06100d041813844440300c6981c603242c1c046007074580046c1c1900358a03204509950164012a0300d407040038000d07203440b104011801c1810001c0440304804c0034049109a0150030007000c114001c1c0c071a054110364103640a0228070003085480c642d62240d21176183d07800c0e04003040c403600201050300b071a1b00b66040801401d01a046800403d17217800300e680d4520905003894203180c6401c101c039450f58800c201144015401c90010244c0480d540204011544058441e0032080c000708400281354003e030001d01840b072940610bd503120440148184161400d0ba000900c2001640c000b1100040c0805029109040c00011541d103c0e59810403403001000c500b08042d5043c410210b05004000000a454880c0d8905441e07442070350b01c1e10194025515044000c9101061051000030030117 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 99361825 1250 99360575 99360587
    0xa0b09010608040b0c030910090602040509010509070c060c12020703020d1b0c050405060d0507030605040203120f19030e01020408010f0b060408030a030509030409090f02041103070504180b0603010605031f0303050703 95
    0x1020321f0805a8045942d901000e00403607140020031a031312a000300d0300b0003451504a0074240101f2041c0d80240041c030380340c8402400c0344c0315007000400c0035076251603c4081301c0c80b482c2910203030f4418403400c6507941e016042c041e50b141040408000000c02d6845042c00081e040e000c4e0941d00340c1c1c8a0050b04c0c000381000e0404c406004c00a00141d040b590749111240460020070800c0c008602407400098203040c1401030500709006002d00c40e202c1a4204440704826540c0030850f80e10b180150030303581041e0f41c4d200c2c085010300f0030345040210035800820003094211040d4400d402800403c10b003002900b00d441306201c900d009a10690071640c10070700c002c0e0300b0640690425079001c0040c806492a168442e05c0810490b6039941d01540c00a50756000181141424402c00942001c0c1070180f07815031604d070100074480d1060380079011040304008074810b4154504e40144660440c01880b0b03584942c4c46d10001001078104440e05440900080c2e88540d03800d019280d0341c4160b030740607030b6224070b004042d403429228 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 99363075 1250 99361825 99361831
    0xc060b100509042003040c0311030a020907080414010618061a03041e0b07210501030507060e0a03061b090614030a0203040212010c050d060503060f040b0702070b030a0b09010608040b0c03 82
    0x1103003038900322045080c104d0300c02144150b1040004140341411401d010381540d90001c1054000e50100b402800075a41c2d800a499120019241c140f01c560b540d450055448900c00100051960030701c000454480107100d038016450850342c508004103541c90302c11149900c20104840c681610400114020400f0400811003100b007001d0031041102c4031759210003048204031151000200201960394010101c05ca5000885040c150180101c0d419074a81030b86402c1103108403020312070722072000320143d01e40f071404100550700403004011344904940c0e0964103101c141140000179450300360120b40240548007055200541ca2046030440c3d40b07281142000f91300290042c0d030700c00c0e01e81c0401c10741c42038240180c0300061207039550203440d4503c0440395010b03101640c02c420302c203400a00800895103140304649a005402c00303240c103426103907800c007170381003d1017900100000b550010130003035154100e4002c41c903035540944266210381c0e80c032070003100c0000c0b044d200142005040e1f0b0200c1d010110101c05150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 99364325 1250 99363075 99363101
    0x40e1c0e061e0304020a060c0512030714030f060109060c05100b0a150201060e01050f0319080405270a06080d120b0402070f0209090109030203071b0b07030c060b10050904 75
    0x1241140b4420a24001200c4000c9500c80c0d00c000410803085040499440340148824141480f07859034959440d40c070340078611080c00c0321010100c00616254807400b039981c5080b8100350001d641c6d08044194001c519021a002800702d100c0030700020f5294807a407018a60702d07400401503e03c0b19130102000000e4a411707841d26500c48000035010841480301c03402c0410750320f1a90000280c0b240b819580742c12556050b4130032803050103445e0780702c1080d460118001c207010f40e440c19a0010740400f403070000d00714000e0790042600501c1e0718200d02203891039125031040341c07807144401c1403062761001404000d488240c001c43d06aa04000b034140c0901e80208000224102200c0000c210642c140b4041012608118002c0d00d80e09809845a0b0550400c0e000b10b6410080c80e000a016040c1241c601035600e2017460300080600644403407045400c400340e2001d0010301b0716140c40a56404642c2001050301c0011039080c0d07010b40c5840415603003451700c4105d080c1800c946498440c1407586480402c001809401c101a07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 99365575 1250 99364325 99364327
    0xe06100309050304050907030c0e06190c0c080105070504061403070903020d032115050d0b0606031905010626041104020a0306080d11070905040b13080c0d0509040e1c0e06 75
    0x800d46968595686e413191040796400100b5461500c0020005030242c207a85003c0c0320100441c4001d1082c2070b1150200d8045030030452085111743c174101d1072484007a403224030b481d482c15007446800c59000d4010801c4490641d1004108000c01d0408030083c0310580d01e1001098526204100600b4001d2100c0203042c02400c0188885008081100101e907441640c6481140e40792960b40700050b01100b0310b00038160503281b5800b8801c045c0c4d540c3e5081c0c1009803079140304800110004051054640c504164000c07096400d114559542202804480d91086041c14024070120403c1441006042052207075410140d6034404586035070502c8025401030301080105a1220b10200381c2010801c00207481c3e01d5103136500c800020040c0303107032420240710360081c01d034482c00d04091102180c0013456460708038a0462000c25980c045282013004c620805181209a0090158004041d60400040c0c000c080c2d080d5024800082c0440b03200e0307254440e06800c0034144429041c100080b52180b00100d40f03d80010b0046 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 99366825 1250 99365575 99365579
    0x80a0b071b0c06020f060c030f1305010e070e0c120c0c07080708030d050c0a0509100309050d0315050102010b090a0e0a1b030c0506070f0b040201091205070801060e06100309050304 79
    0x403070780003245500030707141c2840c207210801103140c2c1080091148208203024040301d040034010b161b00ba200c0a4940031134a88604081100595100e155844641d88a00204880f94100030b00607203544d0fa5100d02400d000c01c0c0300005100210400803982201d0341141c0403141c5581c0c5600c4c2c404141c01c5186400c646204101e0b000c80d02c400100031071400340440d07034000c40e162a6003804410944d0760081062003800c03007e1044480054008042e0740341180d0841d00341000f401c88000071402001041805466449409180c1c00c010f42c00d94450042804040c50488000ea180e0300103909881400c105540c0000400001a00e1021260710400c8a1030065081c1e070a51075036502c5d20010506115511880790010302010810400d411200354010481640c80c0b900381483c80c0c903040403c9140ba880600101d01210024045a21440c400800341c08088154818810742e41045941d555490103540f90a620300440414401450f190181c819040208200c40540425204074090f1a508404681920080c0304c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 99368075 1250 99366825 99366857
    0x120b07140417030c0f0118033c090503010e1e0114010b120105190302062a0a0510060f05060d0f0c0f031508032205040c0305041209080a0b07 62
    0x40912440549002103490b04c550741410380c105044250f0901e1140c0c5845c070200d007031560380c008240304250181400c10803040080287c001c0d003100c030b45420460000700740d4400c4030039542c86101c2c05400b603290307699a0240d03102c6081c1801c03a541c521a00c98981d012014900980f8180e00348804090941c40010134604140340341d40c00c00c2c0d10300381c1000e5030071000480d400740e42d514180819401030000319115500821950500e510781d09217400081d0080c040010401c1030411a03420341e0600803a6540d10300360780100203002c282c54081100044507213005801512100100d03500900080d40c5542c4980314805241000b0090554040c58500d1400764035150045843c0c845440340c00d80c900c8458940107642c24891100900701d400c0c1105104100143c14010b00a00d1000410350703414010782d5003140c4d042c0d01070102c0c03e41411629400301c0d500a04003c0310440203580b40c2c20090056200c0c91500c081108000030941e40b00955005580c3e669200c180b040c804108082035494102e079141c2001841721040c507070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 99369325 1250 99368075 99368099
    0x4050c04150b0706060e090316032a0b0106020d05180d03180306050f010b03160f090e010801091106030405120906091f0212070209010504050c0f0a080a06120b071404 73
    0x401c4d00d645682e044100700482d2481c042d650310218400246140201c1200c2740b2000c2c08104070b02804000001c00884004902e05101400308040d400701451001682d107001d5000c10824059600140243c21440703c0c20390003002a150b843d100080755080024800082c007054542014040e005c00001c0200700d0030752440b000c05000514080c441c0842c151400003001401d40700d06902801c039001e401c20812100280f003c1e05150b03141c02c1480d002d500542100740c00c445100c001d1300014000c9240400001c5c40a50540c0304400d0640300f942e01021860103081040f03164042250040d045d90440c5640380940000c80c401024007580c01480c0b0b80c20544600702085039040d00c0394010381000e648260500005404100c01101030000c600c0c01e9103441100d601185420724180701d11400f0300d8130350021546424803081515090398448a030a5100d4004140060010005882040040d032414401184561001c0ca8521003160800d400d8281c5403201d071400c442c84181c0b0a1541c2c002c00d8244004a161000b050b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 99370575 1250 99369325 99369337
    0xc0e0109030b0a1e0504112704080d0606050706060f08120c03190e120102090f0402251214040605071b0b0a0c0314090f101407060e0f0604050c04150b 66
    0x4c1000180c2d8a8140f41c204500040c99500381d105044203d206d41d003000105034104d0103d40f10f201d4908540e200d619008250340a007912008800d41015000301d441c99200707001d066401e00480c020701100d0f0b0366400104000086000e01007880d040103082400340406080140f40300c0310320204591074205010311000c0d080720301545080015081001ca0400361030b01c03682c1c45040b42c0b0f404c03008500d00141d20000542c844121005140a544c02061814028200302911248030400d4000c0107980e401910700211800801c01d1000c000c180c4010006c1c10040d18070f4151010f440d415190103180c21035545520300d82c100c1083c1466802c50a01c14003007440881c1d0409041e80031180c0d143c2610210440c603020340820070301304008003014020302001d509981c03505030703510242900741c90a0b0708042c4040f030210307a402e040d080c5074410510001017020801c00d080c0e00c64000040c4681c19209070074481807c070340d02c400342520003031309980c0300c1c0360403542c1d0b46407980c032200041e040c4e010480c18007660795464041e40c1c0c20034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 99371825 1250 99370575 99370631
    0x206030c220602011508060a090302070f03030306080d020703050c010e030a12030e0709020906040504200408150a090b01060e03072c060d08071209030b09060603010c0e0109030b0a 79
    0x46410440140c09000d0001a510702040681c82d0314140500d07240e9451002388840056620b49003c1800d160085c0010b001070319035028a070b09040c0d100e04029002e04424410740b074445c4a40c8550680e400e10104400050b01c0d0300501410711501c1d000b0044600c4c001021881303a05006a5001d040010800300e200c0d0b56041d440e440c08103044200c0c1c04654100591031740102c02c428010444892140c0e42d10040300d082d26403c0380c0016004407240603c808a0481306a10503900c0d0000801292810002070301000e02014016240c00c00e5440f9030380d8a00f91001100010300e00d000480c0144000b500402002c3c41003200a0110740d4500d07510301d94066803400d0b0b81005403d50718a092840d0404c0f807520b6843d5030049003036901500303000865450700f10314400c418000d498030001c1980c800c140d600c5039400300011a0019036440c040d0800c03130f010580301d45069400c284603601c0c04141c0d80356140a2000c1141610058481000e642e24580756103088171001841261469900da000f0142d103068040e1a412603050 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 99373075 1250 99371825 99371887
    0x18080312060a08010e070e04060e060a0e0615130504020324010e06060c060403030506041b1d01030b0303070627120f02030715020c150a020717070f0206030c 69
    0x71020a000d1500d0b5a60030a200c0703a4107001e14000ca0920010740340b42212042a080202c80d0f48909040f001001c1028544825000704414402009481e0b0031511101801c101590001d440346043c40940020040d42103410400900ea0300c440a1125407105a005001809a600500780d082508020030103007018050101a418010320485445000b81d07640001e094070304600e40540d40d00d030303282c0c0c0d044001c000030105522400060031644032504200e480034107820756004000c50060001d813042500c030404000000e0700100b241160761080c0038003040c900300134002d98640201601d40b000940505240c0d40d02000540c002100290f8035480509141385c0100540d601c0c09440010007418100080070020441d4400e0040a0102d60f0f011600440b100383e00b0710040c1e440c00c040c40310f9400c00c2e0700035810007441414030040001e4144c4580003480c01030701c141d40041d1002c0004000002901a0400245c0044510600840103013071100055410031031811880c1d0070241c0b40c1040307036203e100c11705805141c200 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 99374325 1250 99373075 99373081
    0x5060f041508012d05040809091f06050a120b0f0f010c02060f07031205040503031303020a05070303051e040311010e180a0605010305070c1128080303070f0215010618080312 76
    0x70030304da941c2c95141140c0c100b8485401c01c0d07182e0060318010050f0242c46a9000750210720308400300308040c010040251418850541e4404005d0110f8021f00810300118100c0d41403010340303c900b445001c0b15110020030100480340d401c018070030280345030481541400854500140036940c1c08010b009580c1030061107554031456898000c040d400c11070800707084a030824050200083c808010740364002ca801303040da4031901c121308080386411130303407100035006003c0c0c905c001c018154480001c001a544864208241441240482030a031145100203413224802e800050074a43c480d11010403c014000d0034110410800e8170030007519036060300d800300c000782d482c0f40411071540c040c0030707480d0f0000542c14241c40d035010725114600c0d1060202c200c03501c03440c1407000c181e00005070700810820100c046007100780d8217620354085542d281c2c410365100c1c0100d042101c400c60030f648006160103201d0901000c802c51640703040c1c02519840460000c02104055621000c100b580040025020011a02600c007400342 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 99375575 1250 99374325 99374381
    0x20901170c0301030b0403030204050607030206040c0609032019060c02030615060307030e0313030501050906060d21031d0102070c050306060a0506070f0512040801050a05060f04150801 81
    0x30044008040640c4888000c0000c035050207819281182d400807014941940c5d246000c6000340300725040b06510420102d010410b1660001d0006d208911950000e1001da480e81010754a0000d80e220040103054080c0450b1581d40f0058080d922a04e0007070080034010b501e4814080807200b49820a50005610341070007400e5240820203181c02048000e101c0c0c40245191012070028840141144145034489000e0400320b07404008481880a1030550713000d46940b60710300349001c0c00c03050301c4018840c0300740030109060703142c40500c001c01190300422441031170820f20350000025144880344014940e455071000c5040a03081502103076401d9003000140c0d40e403400c1c5010080b5100746d40016010307038403903410428544c5031000940d0980d0303002c0b954251254160b1508010100d1101401443c47c041c000c00c0144000184010f030069400c414000d0080e699950001421204200c4005510a4602d0403042c0c80b400c0c56072000d03000d00f62010f0b0f50181282c9421a490941e103038444404003000c41c03110780c00510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 99376825 1250 99375575 99375587
    0x507051612050d0e010c02010e240901020601080111040303141606140907051e1203070303050117010207030e13200405030c01020708100b060409181101020a0312051e010801020901 79
    0x704103041031040d40741c0c3c6130002042e03040a10402414401030a00d03076042030b6603007110070204612a80b000c01003043c5008800a4070340126000a01506c00d400021030302c54010302621800c201c402d4141e038105071541c1c6003159a40b015807100710f418a030400001d17a40001100182e60b00500031200800d9035200c4440c40c3c0b80b034610060940089400c03410701484207940300001c20320208661168500c004404100145424801743c40c400982d00c40054a041095010f820160481d929100c1990b840540d0511545c02c3c1c0c4100e080080000d154260300c0170003482d00c80c01900c6881c5d50248001040c1e4400c01c080c1004c0c0a40c501c0101c251030003c101044136140400c654005544203101404e0380300d1402990303680c1c5068403841181e4494840100710019211942690000d140e80300e0144007030729110111030039002c044c035000d444880040c0200c001650000510205141d4903685208101030fa0045020080c0000723420240082d00e2014864440118004c2e030350301910f0f0394400140d444a404001400b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 99378075 1250 99376825 99376843
    0xe06010c0302100b01030209030703060b0a0e0f0c160203010507020615061201090b1210090c121509150c1101060603050108120903011104091a01090b0a050705161205 73
    0x400159403444800203a01192181440440101c0894141c08074401a0040d005130411a5098443c00400100344415904a809078460a0344d071000c800341c50710708ca46200041100c0a0061203924000300e180401718500909540100d85e0718592418400e1740000d007550002e48074180140c1c45841444084100e4030b4245404076802c54400d440d00081544400c001070707052180c181559076440c11050561100e00d000c1103c942440f017503400f000a4103440304000c01c5107120a071500801900d020131140001313004000c5158024820103592060b070000b62000d002c2e541310407940001e912034a80d0381c000c03035801a960381d845241c5174020081543c4944074215400c0b40d200d0030030181010010000b5030f0021611503020400b00d0031440e5201d07071580c0424003404002c1c408440c0703500006400146030340c00368070004642e6090903056485107803030401110301a980b8014082d00b0942000400070440c050f00040480c544107000392001c0c0d018100c01c00091070030701d41c000452024001c03400801c00c0000e01000039 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 99379325 1250 99378075 99378077
    0x307060516060b03030c16170d1b032003070b1303080403050c0a1205030103050c0405010806060f030c04050f040506011703030c030705190e01091406030a0209010516050105010e0601 80
    0x200740154080706018605122202900c1155100703c8110151414811940660348000440e540d181008000c010800901e219444000d800c06c0102c07808240c010485001c0c803141655500c0c41245296960341c581c0100348400c03002d000ba560017402c81446400702a21288403410055a180c40c201c0c100144010b00040243c0801104000120002904501c003207402c0360709072170700a49070100c541c6460f103410381e17821000e8080500e408445148607440300085050789c1c4a081940d2580204109110540e602800340d06056001200006d6141c00c0000d41c84a00e42c2c4002c003104d03c60313440603021808544042e201d18005901c1902017001740b1400b00308050040c401810400b510954903501c540d220700014110600a810000100354031911440680354000454514071700c2c0c103498a08098080200e110742d250104060180018044100900e010980da10180410307103540d03103068a00c0700075481002c40906025042c00720340c80c1d28180c81034403a13009225400000721035041803107802a400300148164 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 99380575 1250 99379325 99379327
    0x130b040302030601060e03152a031005120a0803090304030c050904050a0201030207030309050d12110f03130f0507090621020d02010c060605060d02040e0c1e0309010f0501030602030603070605 84
    0x4010b0328001403081c11110760380352004507850840002070600510010000301c002d16402403181e510886250042210008110802040c01c4154601c1083c08100c80404100b0b844903401c20043c00e00d507800620a079801400c1d2880451540d40302503481c3c1056803020308a81c40400d0900410244030b00d442c0c003a06007151307080700c240313803541d03074141e4078101301c50028100340c0c02140140415000760482e0702100c1d4010705427048261007860051500740c6404d04a03010341d00341600c0b070526408030802c4488400754001c03202d1850740c54910f40c03201c3d40f50064085403001406402940420350911061003d0080440041034081c41c200501600c0c40b10708419504100f40d02c420000180d407002901855654203080a071070b001c41d2030a151006000c507900403500f14400241c04c80d82c070459940203109030391020030f4800446e140d151901c001781c051180d21040030440c1d1007250040e4442d10001d181c1c00580200086644030740d542801098450aa008031070054010007401941c0c81d00b802088041c04881c6401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 99381825 1250 99380575 99380579
    0x1b0d020f07060507030c020915090f0601020d05070212030a08071101020315130e0d0203120a060f0509150402070807140109083009030c060919030503070201150308130b04 75
    0x2640c86035010700c0b6001c144000051103404050151a005200c04c0e002040f482e400d1900900b801402000c0000040c814862480021200c1304c440c55411b0042c20180d0040c805185005000e442a60100800b80c1c1e110030440f001c110402c000b04010072680507140d60303040b02801c0030344001d090020120a243d81c507900500030442004c40008110994100445445284606034810000200761b0100307101e15602500008140f002c0d0004003c08035031100402140ca1a0b4410049000300c840b03d024010100e860030030100850f140c03000603243c0006100c209554048294000a003c0360b101e510b0403184d00c4400702d01042440024404940140c007514028014071441d40d944004600c00d9284610712600100030102c494401c05508900c8100030b250950b480c0d041090780999250031540d441d05081c829040001d2700341a020805d9400031034020505900d43c030b80da03a019a10b40c0c20003800c84003199a110030078800c000005010900542c000c5410a9441d00c0318014400240040d40046c01009010041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 99383075 1250 99381825 99381853
    0xf01020301030816061401260a020a030b040302150405060a0f0b010e04020a030e1006140a0b0702010e1c150f09050c0607050109080408010e100e0d0f02030d021b0d02 73
    0x44560585200700d081c0605800c82c038117800100041007510950b00803500c0042440c04003107800442c0b404002000e035010b00c490703050141d83e40c409180001e410200d07031402000041e038007691300e0740c1040c0701e0300541d40c003400728442050b85010100c42c2034600307500a000b07000380d680c01480380000c08181c014080c08403a891034000780520101c06021402150f0016207250300350b1290380600c0703800080c10b040d01d49004540e40500c0c0500300700d0250815485441c20254028509003c143c0308881240110904040c03c0307400568280e001161010740040c14031610040d8101c0c88050b031107031648903506144810021040c00400c80703804003030300c200d21450170800300040b4000207100140d0880440c1c400351b46900740c1c5031050242200c3c4030000c000e040c0200d40401c0e001d806402824620320140300f241d95007030b42e0b04127050540c3c44c401104505e540104200344612803180e031050400e803407640126407804d007001e15050101c3e48440d0b04020a1178401441414a80081c001f0790074140f0a0320041c032510190f055 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 99384325 1250 99383075 99383077
    0x50703030f060302030a020d021306090605130203060a0303050d06050603010902030403080912040905090f030a050d052412010b10020a050c100512100b18030105060118271503050f010203010308 85
    0x21b80603100d81020040181156134103192003600c6e10300100705110150341c8284c0440034100c20f0203541d200d41a40c4510394a102800c3c404c3d280b01e184020158170075189540c4080d0741c26442503001c0042e698880c0000700d040d440c2e0320015402000d0305100142e036880d2605000f00b0744603001c0c01407085504103524800b84004240180d9054503080000002e054443c03240c550b103007100700c11581100f0b00011402c526140e42010160a600f40604000e124030b40c0c84a91882e5640a2100e40f00c0000c050403101d035a550602c10845d00602d0714880001450342094400034403106a0702241c000160310598103a0200802441640240d210699500c01c01c010b0880300580b0900034181100102c5500d0340000e81286951640780c001030021844442e5a0110110401088500103180d50301960814020a040f54815a0001a051481002c1203201c90610a001502810ba0740641c65800b280503151a0790036454494000401e000c2044c50030352034a1881e1240c14517100342001c580b2648140010804120988 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 99385575 1250 99384325 99384343
    0x40608130203060601140417070303021b06070f110406030b06030d030e0c06091c05010203180c0a05190306050c0712020a030503130212060708010503070504020403030509090421050703030f06030203 87
    0x401c00c6d121462600e10074a80324003c0d0740c0401d109195414085075500000f1402900742da029a00b601d9218002c0468050014025110309401081c1045010042100781c1d4203082d1044c4038103150403100c4030280014007a102c2c907800981e10b40303c0c600284011443c3c10070a0111074052410244600b840e4120074030740b00d0000303501c2c5a015050000c3c0c1034010380d84200c0361504840c0c4c0300c01d80282001050501600039042194515003c10031b084240e003034017200003000c0c000543c0040c40003013444d00300002d12910078030180c0700c44401d000075140400003448900610340b0031803200a4040e1104501e04203841000b081a080c0000d641215442201095109040300e902007500c2e40c2c41e21140c10a880410010f00c81120001c01501450052107a45980020224101c0d4022011694001d80300c10400040b80708a2100402088080003100740b941131046c251640300d8041c0ea95480e88a80d190441c1c1d000408040403000020000a5850209501441903603550142003008011040c103550200740c0c1c1b101c0c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 99386825 1250 99385575 99385577
    0x20c0108060904060b06030103150b0406150c0507080d02160b03040308010308030705160308060301050c040b1e0c0a050d02010f1b0818160302090603011104061103040e0c040608130203060601 84
    0xb0001003d0141903048040d0b810805004036550751707500c1c240420150700c5120031120060424076000560314150292200b6940540d003e415128004542518288a01f90003119207010b0384500144501302448400e00702607058000d4000c0d00700403172282244c21050b0b00039600d140401d1040c840030a6118680e141501d82c4010b0701552621001c40c1a80c40b4041c0c21883c640c5200440542400c055009050b24000d00054000f48002d84800380c0140842c0160301030480140c20502c40d21103640c0300c1804c446280c1c81c4030444903107010a45060242400100001503555a010b0b03101c4940d099424881e04d104100043c13010440b01c0221414002a00030b0001c214080022030b802144291001194010740029030b40c00301c58070000a0070f12030460f5000d600c82644100c201800160503401c0600803000e454001c048090300c1c1500301002501eaa0060440e01641d5200070b01003c19007a54140800c2c1c0109100380702181c03103a1501a005069020042c1404060100b01c03240e200140c4001900d076130007100c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 99388075 1250 99386825 99386839
    0x11215020c0d0f020c0604030c03050607020105010311010c03090b0c012301140d03170f0118050c0a1404090507021c020f0706030515040614030606010f140901031b0305070f020c010806 81
    0x41d04104e00e0550204a01c61b440724000a002040040100c03d11781100c0c403540559034655200c1105a00721803003440040c05c0d07402c420003203800641c46100d035071280508c01c0c1846051951074078140100c1c0e8000750b11040c0303039a65940b0f012000c2c0a02d0005000043d4080790300051640c1880346d0707a02c200b008540c0302d50040543c083c805003018060050301080310084888015986000b0250b00185402803007042082d02141e5204502c151080c06000e114440c0945114548008080121500d0a9980c00f207903125805002c041191401c50141b140142400c0c0d000304007480e8a00702080a803852150305106540c068150b03541c125002042e03241c22a5803d090005130780c3d0b40c400e1400e800c0e001d96411107074058600180454484082103001ca040c0348180c044a59641c1c44000545016a040001d43c02151880b015401c695610300000d003941034062402081c0110001550480c054400d00d00d20046070f00c80e410446042d601141186004215200400b408101c0800103407003c00003400741c502482d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 99389325 1250 99388075 99388097
    0x17060601230405011d0402070c0306181112030c0303040b04021f1e02100606110705010c0b1b090402030103030f080a051b07050a0c26070e06040c1106011215020c0d 72
    0x415070003e401035140240056540b00e1152070410784245281c0030841d000791500d0703803104cc11201c41580001c49a4850501c4441050718420040c0005640c1e00940e9144010041200650000d00165006034402c8603070421b2420a48100021080303403840d8a5400b026610140701c44a6000d080c403041514640d4101c41c03400030440d4101d0400307022515104006041000018000c0e901c40e403244114a10702003500d040c0343d00e54004443c0604601000380140301d000012600c070501208080701103000c07001d0810300d06419200890181d13003090340b0a03404110754003031070103407a0f42248201d40e1100d20420100420315103101103052540c07a50761060b815440102d07000d0100321080060742032043c0c20403642c1c0c81c00c654172070a4802100d0709c2c02036460402e685c6049080314480002d80e00b0103075048100411160b598070002c6c0402000c4802c206820072092031101c107480c0105000c16800392a800990843e08070b018101198643c4020300301c001e41510400c500500c115002c00c044003170000314034203051000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 99390575 1250 99389325 99389357
    0xc0c060314180a050d0906021009111009030f08040305010507080925120b060a140d080706020d05010303050915120403050f041a03070e030619151706060123040501 72
    0x94001c1c1c000e10505ca1052416080354100b06c40000304d412590869048003c9a0a101d003a2081c2c600020a0313640a010322070481e1601601c24842c14101d458001001580c81d215200c051010403001c0e114501c0000c0c0a1080c41401e010300c642c080d121703061840782030418a095580e03402c0c0d0a40051007a10401444040e03c1001c4042c60340248901054001748403c5400c00004502c42641c0c0e0030702c541840342e0005001c503400a11121103100088c0b03400002500c83d260382c04203500040d001c03100240d0820407102e19080301d00c10b4901070341c020b81d203041d1904424424041108001100606550024400d0444501c608440c4540c0300d0382c541f400c1d50b2070302412480704015009940107050303d5054240d4a10403850004003452042c0c2196803070f812618034050505840d0300090b03c011202200001562031602c5013a00041070b40500051041c0f0400c3d641e080c8113255007000800543c080d0404024840c80f03690280d00b26080916004002030215146040c18440744a603200c0e160601236100500c10f402c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 99391825 1250 99390575 99390583
    0x406050703091a070314040312051512060f0106050f070f02030c03071d060a0303020d30090b0c04060912020103020921010e0613020105090409050d0c0c06031418 71
    0xe03980034243c0c0d1400480401020120002202c4000020b450300c4108840e0710301e51145140110b406845000d01e81066849030030182c04000c09500d4150300085030311400b602c503274016080003400d1801501c542d091500640c9402c1e901a40504100711301406100c0410700850101c508495103c111f031801d2105034800306c0d08040185580396410300038a0f10000d0144503185600300d01484000c010b81c440d07528032080000701141c50102400580c400112030034114020311081c0084880d1030b203071a405407480340400b61044404071102c03c2c020744406005080000d504c64041d040408410024241400c0c141d004000300424032a80f011a030014500c0425640658100c0b00a0030000d010340d140e00d4544040e2003008441004144480c2d88ad280024500f040086480ba000301d0803860044a036060680045840341c215006450b072041c7e540c0380317250020b082080042a04801c2d0b444000c44041d903420701081031034040d884041498203040704c20022018000c009903100d0588880190408400b80e007003850 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 99393075 1250 99391825 99391841
    0x8030309072106090b010602120a1715211603030e01050d020708070c0e090105010501020c190e102412090f171c06030c030f050f0303010909030f02150406050703 71
    0x3c1d01e06882e440502940b2204107040e03c8158003216001e00340c54845402321300c54036104100068a0f44c0c0b0540e0384000740365400d90400068070000c2c418114420004000042441f000703120824402142c4075200b9051140d08408418003049050b043d01d9520050007500c00001040e0400c0000120440b19030002c0c0d0581f40080d030466400d40c1c9411080c5030032030856507140540c1c031034a0420000107605030343c1401098140c5106a0281000d0a051403d0200140d400c010764a08202075074400b040004e080c1c40c04a100380d5001d03920608c59480c1c41c86114482400c00c000b01400101864005050f035080081381c417408800000000e07c0c0c0c1124140400c681a0600c0010000091078290b07044504050700030b8640302c034200310300341d600656910307a0340200e881c00e00c001055511095400c00201e046c40a0b03003252140034001b82d51800002c55141415903000341c1114000e181e9801200c004c2c154030006694600e101400201031401c0002c050040c81180140010880d540f12000170750300398403035008040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 99394325 1250 99393075 99393083
    0x140903180105070c060903060501090b03100f020f072001180e1509150f0a0815040201020f0d05070b150915040e010c05030604050a090201050f09040603020a0608040606080303090721 80
    0x4d41151503c20040078071190b0322054400c24142030001c01c1c5200d03644901c8a003448001c0080041110300b0100380c2c050216400759880c240d0342400b2400c1120704040041c940c81e0320408592491445211002d03070341c1326201d01e209040000341c2990000c0101c3c1c1c4180c2130709a0b005220552820755070080220000c10051080540140040d414400f81501030f1031a10102002101e0000d0024010700c1801b24000b1540f003904019071213103140c1007005100c505200e402c18018410383d9000034103890f4151074111800083e2000440c0020200107029200b100c40b6040050441701300e56030041d000c0000c1207144090300910341442e1310701c00280300e41e442e50301140b80c000c3c00d20001e201840780042c001c1c00c0e03600308075050341c011801c020005991080d5449001c22141c0d058503110f0a20a4903501c1e00030301d82048200c2904681d0b203140100140c4d82d4070070798034001d15083e41c90900c185001e00e05501900c3d40d591004e01680d10500c18400c8812000c02d5003400ea800b07803440104c2d0b043c42c0e440506032182d402403020b0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 99395575 1250 99394325 99394343
    0x11150a02060a06060201020a0c02060d060b040b0408013b010e01050108070302031225060e0102070b180705010203090d0305090406080106030c0b030f06120a0b0c03010914090318010507 81
    0x446515008104984074011440003006003c1c2d031050240d0a0303101d00064140040c41b80300b0b602e00145042e2010384210407409400152903621001d01c10b142e0b500030f0f08070350401c41010508001e007032024003404240c0780040d4821406100091070340301c1d40e030858449215a160070f850b020640c07a0300940c0071800c526100d40091001d1750350f40b6a0240c030388aa0340003d90282c042d28051260707040040007100c0d000014101200401000c18042082c40b200f17001c1c0c200d40c0303151a0080f2406a800034005041d03c1c6005140d448002d041c4030500301081118a265492941c10101381040681c0e004816105084030589003840807036650f02e404c41d400c3c814065000d910510300f8002240d01c0005600801c1942e10030211602956190781c0c100101e03002c03c0f110505036400d0400041e1180c1031010603499080301c00300c201c62040ba13560b6507000a00a0494518140200110042184a04034062103880400c100c091100600303040000c0742d00c074400c0111a5443c40303038414091b0310503440b800440c0e07440c40d0090445 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 99396825 1250 99395575 99395587
    0x51f0b0406210f0c0f03091502030613060602010605130b010e04050a0b0405010b070b10150f1e1701090c0c0602070c0f060522050303070201030b01140d0510120305071115 75
    0x22001130040b20402800101424500b1a03d54084e2056002d4503801c081011944c032116200c08000e58802030501d03400810340180c0981780c6449001e0701019020310340000c01ea090501040c0110030181c0091024204d007800c0d9002000c1e42c109004e40f0000384261130214181d601c01c03800002400d0000a15500035240030000a01e20724000c0190250034410000d802031078903140f007c40e250000b20302402000350003040c010707040300d8050720350640182440c1c05c0110308002070320171400d034035494404404086205d40000030481101c40603003502500c1840420840c4400700343d002049200c00c65401061036074002005030900c45064080001406441407110085845803001400d54203c0340030f00b190386240c07600d10304107104070040100559002400a50030003a46030011800340290b10101c7c2e05004030603640005819103180100707000305500134040742c141440030314140031000c0303a0301c0841081c10189003000003036400400c6031011508920607030029040c100000e004d0381500b40c061000380b100000d034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 99398075 1250 99396825 99396851
    0xa0b0a15110f0304030c0e0603010f050c0a0314070c0b1005100f090e040b07050a030608012408010c05042303010203100e15030607121d01051f0b040621 67
    0x80181c00019841078074400402001035503583d005070702009041c403810303600c01d00134a800101116405040140003282c505c4048404030100e17102034410b103003000d0000a03c10352561b054040c08100b808030804003040fa2810000007492101625001025185804040703145100c0422200c03010b844000c003c00c01c15651000050a02000c100d69900850818000015080c0001c0f00680c402c5410541103151aa40c80c1c81c01ca80c01d80c810810300c0b05041d44c400000c00c1c900720034450b280759180f8405842000030110060340c05100000d90003041e4984c180400c07241c4465204081d1000c0303c050800040310010480343d80180f000018040c240c0542c03010040291901080c81484115030100f14040d40c070741c68a03580e10300e1280c65040c00682540c40000070601d91482441021448040240c000a010000c000813001100700d940606590b0381d10f0744280440c541e5004483c4003d0f105250640750a01d2400742505c10701d0144c2e00c1003030203011180b80e031501100c01c4000d0500383d0358000c0a04100c551a000c00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 99399325 1250 99398075 99398087
    0x30a030204051305063007080f1005090a020d1e2006090306060108090a050303040b04051507020a0308100308120f060d0305091917030c060a0c080a0b0a15 68
    0x840d003840341030050720038520f09196108043c010712001d440c08a14900d08500707070301e60b070707050a2500c06d401b4030209200010b40d03401e200e800090005000904501c1c200821140c0c5000e41f00144400c01030315001c144551400000340b502c0e80f45da410307201031942d00300c01e09113100b071028034002c500c40207807034100c0310810020080e0684591a14455900c1600401a01805103d0056201681d0990b000d4004596958007580f1015484600c0340c0c01c403030350358420740d41c0c2a007540c206490031103603120760409110804c0810300080c80030481951a0140900e40808020f5544004400107401e210302400410780302001c00310a00082c40d00107808541d9642e2200d583c040102c0212030b07140941c110380c804100c0038548904014201a01175994a0030709200c20b00b040307010070380c041c607010050301e2180c0c00155003c58203850086100b9031001a60321a4900745070f050905c0c100802c00d001492502c00175030f03a20342d04000c400c1d4010740703003043c0016800072401c017042c4803083c5500124056400c100c100b060140e0300c04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 99400575 1250 99399325 99399329
    0x7090303090905070503060405090f0102041409090105070507060c200a12050f040e090a020d05030a02011505130216140304031104050f0408070510020304060506030c09040302190204020c030a030204 87
    0x680e80381c1050341c0e607100803030486109076901c41c0040c10410101c3d400d840d0a820044c0c103c04150706640c001081c2c0280242240d0040d800308042c84054150031545d4604090203da011918000900c40741c0790104008009204e00f1000800c0c2c1d50b500d00006500510800302c425090103240c2c030104102803142c3c9181ea50310101042208c03405101c215100d009841170b0181c1d0f00022030051000d0809082a04008201780014441c10040c85041c2041c009660b800c0c00302141c003800741019581d42c10000030001c0c290380390800541802c5c98190301c100b1040c1c69002502c5040d1241010068856021804100d4001c02100c006841c0e0700c803403170001100e480701000510850b440780100240c844001014441a07507000c440303c02140d2600000140820359000040c600309128030192034040b038105424030126003054605484c07590344e95040000c0d908040001c2860032200311a840d100346002d030340c02561441140390300f008500c140b0040c0300071900d494040d07500600081c0180ca48440c1d0008005000f50814 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 99401825 1250 99400575 99400577
    0xd0305181009150f090603110c030a03140c0414060d140108030c010e1204030803040309120606050907080f04060b010c0501090b0a0b10050409021c0e1507170f071707090303 76
    0x40302984a800b8015140d0310940c8680340c4604000351b28195081e001040c2440c0c001d00031400811114600c110288001c0501400365140009c0003445100020400710300105085880d040401042c040e074a0040030340880c0403000c03941e00d42e5403c3c040c00243c0c06029010940000b80d0f514400105201c1400720240030a2000f40c0020030402c41211411503403040c0401c81c2040d82c507000c01044c0b000c21030b00002540e00038001c0c1170206482d0340e00d2403601e4100d0740909003a1203c0f0750320b031020310003403804500e1580c01590718a4011814145914040e80d901c42c060401003001355243c01d0b40c280703a4091031081071410382200080100108908103c03140c05000c6821031007103031518903400518a0804202000c0d1121035442a04080c148810840258040055030f001c0090b084601050a00745018020f0a00d0029010f04081902d81e0408100200068402014445030000313500424140703480709a440300701100c5a0040d502c131000305172100751162280a1044080904101425800c1405e0104503131007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 99403075 1250 99401825 99401849
    0xf1b040b04021b1c03140a0e03040b0a0908070609051f03110a030e0f0d140a0903060905030c0705011d0913080403030801030314040b182d010305150d0305181009 71
    0x20b5804d0031011920074102d0120b01720300d2000400c0c002c1480c0ea0190a036400c030f00013228a810b4481c00500791540140c0804000100040001e20940b00140030000090455003880000c081c10400003420850b8102080d81200c103104014004581c40380d00465200f5250190326551610900c0b001005400107400858142c803134590340480c0464000303045000c807903080c0d8900916140c0b00e00c00400d03503400042c1c072100f042030b04003010002c2a00b40c450365110600c2040215135a01e00c40b001c10b400c03e08a9030042c0d044c4020b54001404a1010b46800700e52440300300d481c03050039a20f0701e01c0b4013007061209001504514000c01c002c01010b400001880c1600e00030344810200408044400072030303200c1c0c0d0086104100f418440c4801c03030780c021075401a00d24401001e0605c0011407110344200315412160460221044561090b060358040c422a03070001c082c02c1010001c2207c0301d01003032401c1c4011a0040800c0400110110302054807101c20741560b030001c0002e207820a03e5100280004010700428224844c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 99404325 1250 99403075 99403123
    0x405070c170910110c090f01031406040804090e0102161101200a060903050c060a060510030b030604082203080403060e010c0c1b0905090106080f1b040b04021b 70
    0x10451099416802c1c00802400074201d46120480c0e070040c074030064060700d01c11a000b40c3c940b50b903000c40280c4651070a2100c94559071450a00500c07010040d4884003950b000082800b0200701084116000c2c2d0301c1e090004220503290341444c1d80248940c030300440f02c0c03407408401c100c01c1013102205207d10050990702c07070108014103080902e40c5c01420010100c0c542c008a005030010b9002d0b0820080c1600a0905504005c11000c14508020044038600002580d680080c403603403604440c5800841c9c030600d800c1102801c8040441e548600103407025150180200303017041e0644240c102640e0310721420003c0e0b4100c035660710b406075503038201d0300044440b18200a00710504a005200d020300482076071b81d8120300300c0241e0700c031380f500354503c07005130103091080c010042841681c0e401001c1c000c0d81c40c10700011303440c1d00e810411030420011940300340003a04001c0c0040144031440b00034010804080324000380a6164100140091003003100b8009002946018a04920303400709200406030303100c08c0d80b443c00f14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 99405575 1250 99404325 99404363
    0x804202119060c0908060f0604150e0a0903090803070206031b090d050105010f060c051005090f030c0a0b07050408030f0327010504060b040b012001020403020d240209100c020a050405070c 82
    0x500212460921006d47e9400a91b040c81c107a008113458505a10001c0c04aa8550015425561049030070303605007500e0b00300030340416900c00d6440c80206a035070091810075085500159a901c070203420251000d100002003001c0c5a06903044034071021008007107a08946d910b15109018000911554000c01d131480c00010302a03000c1c070400e41d459503200014040ba039400c000c6010040501800700f030103620450461035860311007000201103181c9180f0060880c1c5100745080342424074024100d81c100003041c4800c120b4500700000395000c607400300348030580384d6840421030103514690010b1700f100f8445e201903004510034198400c501542c01000c050204401417420301080d10080c0001500007891000a540000c400d5090424040c410000151a00f55245c00103050b42c4000901580d40a244c52201030404452071105095403e1600c41035051290800004500308521f035801424403079104a000704551300c0c191004040e15004008004c103080520b0b0052030f0800100341100c00f0310b0803102d122640 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 99406825 1250 99405575 99405583
    0x80d110106170703030f0807050a0302031e0c1309111218100605031b1c020409050a0b0f0a0603031b020103021b070602010b1f1103190804202119060c0908 68
    0x2c8c0708586980745881c00c640c808034001d502c010b0407100400708081d9800507000c640b42107140501040d011640e00c5500c1e800880040a5080c0d11810002c2c0c50200c580544000610030354903040020f0015140581e20001100c6986881c81c1e01710406002d644100050f10420f68041d0342036810076401c0b101031074916032041c2c2640540407102130f0700c411003034504041080c1c5c0c0c540b11090f0901c084c1c00494441c95540c1c41610b00644040104c8154005d40100890f0448034520b85074000c90f0701070240030492468074044c1680d00342c1d002c5a0b60502070701c04c4d8076081da4081c0e011501d23103e0300c101c018a0003158240100d0707100d4606006160042d420440042002c0c40e190344407000341100d00040b001d140080f81015108c410380200c11240310302051101a6602e074482003651250071443d2181c0d000d515151414516808a44407100940601c410b01c40315140c45960b02d102c42001108102419180c200540300c3c502030920b451b0a90000100c2461004c200f025044204069102e0701c3da80f0351561500301503512 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 99408075 1250 99406825 99406831
    0x6121c080112020a030b07020304080a050703020f01051602010507020f0907030902120a23011104030807170316081906060203090306091207170d05150906010207080d110106170703030f08 82
    0x2000091a90600c0172034546c100342500442280126490660f5844140d13060500c01c242c26900c03900140020010741c00d001140080880091070b02603d0021108079000d810741f803c9001904111011440408544890b000051800e41c0200400b603079140c1032030020701418600310100d009610ba14241040d4040001c0c0000302e155000f05481c4048280758100d441910100004184c0e41d03407641003038100d0141040090000e14000c2d0001590b03410907003404480e8201c0120752410391001001040000d07004000d946a8840782072405100e1a01d6114a220490100c90524040381d460724100180180c1c00200511401c50141e081c3e8019581e1488615150320200c2901c0c005080d042042c1000600504008112030b060401c1d994180280004031400311541103c03522000245811444121300c1c050b59440d9000c4401d01c010030000c2e04100440b074640c2140d44d03144042c040403400d040c15005003900074a02604d0b0b9100840c880781c516040b181c0d80c0e80c515100907404540d2070400d4194113403140012500c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 99409325 1250 99408075 99408079
    0x20c0a05010b15180a0902040b030a0509070b0d0b0103110313030e0f1804050f010c051809010b0f070c080a0501020a08010f06083607050307050d150506121c08011202 73
    0x81003020100c0600c60002608184e650f000d550541e000c91516035520291019114100340d803612890b11009220403540f025149000e15407002c07200f041240c00340c0342200d000c3d00344443e0100f0301100300b000503006411113000780c4034007160110811815460858003080c400f80265101948005143c0c28032142d00c145070080364110030028a41010a86100521038001e44907604035440054240c0360242150f042d00813031000140006041c5003200156906008107060031280041294034100c2c05003881c0c451070a0f10001044041260f03804c1c0188030010200822101c000e8411941c2d05140880c000c3d84524001004156800d00200d4960000c03483c0781c1c02d69840d80c56500c82c9442e000e0a04007a0720449081204040c0e4501c032410426010725114940440100001e0003e9400c0c10100350030305295070440741c01009042140004112115a585074580300c650300025552607540100c0c8109210381030105d994464030608454801d60190841140206503683d44140e0362101c5c151841008440000b84d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 99410575 1250 99409325 99409327
    0x110f070204020307021507021501060807080106080901020c0304080a020a0b0a050f03131b0603111314030c1503060306010f050d120e100503180d1e0e04020c0a05010b15 74
    0x2801418250b000b95084506801125506024820f0860710780364211988030040c1c2220301400ea51440d992a0180902202e08001c185442c12003c02400c41c2014070030741c0108044035010401e0410298126121b030040781b404d4a0f03840361200c030342c1c82e540e12200034104d0058042003000141e48010700d040e0b454800a503600d41c0d240003e0703518003030032581000e080718146018054034000000d2480c02c80d40d081131114552641e240e0719142d00a012a808003044104190040049030a03091841b5001d07400d87d141031513029040e01007040031031326265541505941050300840500140d4244c800036501c0b5920440407650b960384c8452a00542c0d001c544202a0020000703941d90000400c1c5032070395040300496291110000c51a01d001920400b48400984c01081000091181d660f906140b0201101c4540b0002c01415545010082141124603034800d40c03d0004c5190b4040c040c41f0744081000410001c0c01992641164207a1540328440e10703a00b11030a42c60441502c0b1941001c7d1301161500c2d445040031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 99411825 1250 99410575 99410587
    0x1503040807020a0e01090b03010b0906031222060c05010b10080403050c0c090c0d060e060a060518190602010f05040c0b070f06050a0204060807050412031b150c0201110f 74
    0x625001518102d0340901c40f0000031075041c010691050083c105158041110b228180a040c00c55480b81000c0b8050300c0081c0c02c024080d20005180347c0420102c0c2c01c5d15507180d001c20b120003104500707a0030511001320008400540c030f80d030105420300704034080d1000f04080c000301820800105450416500883c0040d030014022a01500103020242852400d03a142c00010100195881c602210841c00224011070080020340741c2e0320800003c0c01c0d016547c0110703030030f22000040056110748901c85c100030002a1030081140d44102d0140c01141c00b4010280b032000800728205528024014800190300c2e2408142c10070b0b19038002d8a00440d00038404000c00d909103a100c1200350700c02c1c4010f9424a405941c09030008560340b01d00c0340710710b004450060711141080340007170500001409010070494140420b000f180c41e5030300e170605001d9150a0103510340180324500f6606100300500a04865031340503034903001c10304d140c00081103800c65a00800041005d0300301c2ca0b80c0785c05048000c1000007414401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 99413075 1250 99411825 99411833
    0xf0603020a030b220f02090609190905010b0a030c0201020a1e0203040e0a090c050a15080a0608030a03090b2d0705160809091503060406110c0f0c0906150304 69
    0x51000030340e00d203004501243e5a001044000d0381418041840c030342d280c042915070307001510991603900c03118002036151020610010b9014018480401d2140007909550f20f060041e1b03d00b900b000b81910700c03040c80785d580d5900e120f80c1e481d00492003c9010070308101240008902c18422100120349944440c005400181d1303082210f041e5445031401584001c000200f032a522111401c0d10514401d500422a0380c0c3c540340201501c0003690109024902c3c9080511100c804440382c510500f0b2589442c600655421800c480640302c20781c02030000e800001031458059a06801401d0220b006210034000c036120500020a800901c100c0540403c03035003444040d481e0000c01c42d00c0d030051142c1c078201d41812824000ca200350304114008440b040303400541c100703a134101a2460b9901440d0100c030300c030312a2010300c00701c3c2c0c80b100001d00003072003117556900307502101f030101d416182040d80f49000c0ba200381c0781c02c0220030b5031402c100200350720640d5010001011032815074150780c3c00807160030303a250550710396590b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 99414325 1250 99413075 99413077
    0x60c04060206070e03100e0c0a080a021e030a080c010203060109140307050d0822080c06120f040201170c04050901080a080403120201060815070e010315140d080d09020a06020102040f060302 83
    0x102d075160140310750206c0d103a000c0d07000751088817a200e005002040010810070144010f281d12440359074100404000259641d002c814501c3c1c44020f101c0002c810440d00005d09048805900401e816404103109002e00d00541c080c51040b4002e80350701a22070344405180060109000c262a4594800c010a02850900a10740d110880c800c420783d07405c0c420b03401302d0101290711403400c040c02030314841d02c1008070380000c110090102406496242c5010f4440c981d0241c903107001031400409814101c00302d001c69200d0701c92412000e110100000341f03401c0040b105402c80d40a40b0900c0c1c4a11007074000400c6901d0b006c40d107602e8842c0d01c08400392a2515550b2481c921003082d581f8482076541e141d100190001091050707820290a501035412031380341c0000f000d000c42198030507042c101491b194038118101004980350085e02c506500354107141d141200007410000c107040d0000e000b54804114810580200e42100700e0b958401c9920712031540d07c80341c0803400c1340900c1c0b044141d0b44140c074408201d00d42c003d41c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 99415575 1250 99414325 99414347
    0x90c09070509032a0307061107150c020a0303091406030c0a180b13030b090f2a12010e0c06160201030902060c0d110c01030e0304030809010c0209040f05060c0406020607 74
    0x5000c4d281d40003a41403070481d0f443c02e81030540c0c0c480210958034141ca45400d110100260040703050150007847da410800703a5484241c0181c000c0c1000e803000908100d4050120940c070240e0050401300c240d40c81303241c0200201750620038811b004020715000301e0246081c00540c3d12400040e40100d0609585174812141d006115541e2611495800000f0030841c0c0e081005000d10840884159296403551501d0b607080d82c00180b000e042a041403842001102c00860400740c01c10b4101d0b01c0c48804071480c020f04404000031000140d00882c611a99a101c0320190800100018003005035250490762109202c1035200780820f508807038a00d11110001503019500501c1d500f400940400d05280c40390910501d00140c2040c5c00001c6002e110800c0700c0440b0800682c0b4010f08286030510000c10240050359a90041d8040240880300100b01e1004991140c0c803250703000d503001025002d450400d801c2031081000903035002e0301c090140300c0c000f400c8480080c04984c21039186900070101580c135403108544400a003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 99416825 1250 99415575 99415579
    0x6030604180c0b071a07081308090a06020c030c010203030402010503180304050405130209011a0d0b060702221406090612010e1c090e010b0a0819020d14090c09070509 73
    0x4a01941e011512071901200a0810700b4006603644241d4142401540303054944c99a40000b22002c000da8142d002141607000f08100d1440b005070707129454094418051100302e60f41098200340c00103140b81e030000d181d403040749055060310071041282c4012a140d200484029003c035500300045002c00b584031001003801d05110381600e00380382d1072b038001900340c03502500d00d8040608000000000c1d440c01120041c01020043c524080d094562800030207a4080c0500e14546950740c3c0644210544030041151205a40108490701c00810301030f40c101e14203a04005030103071502d00040c24480c40000d010003800381c0001040c011381980c2c1c01d41040700103445500000603554071520081e444181c100040701c00d078050f000341503404054071403006001a581d41d0061452081640040100f03441c0f080894070300c1000c40c03420440300c1d40d900711000080d603001c10182801c9031001450b42e81d103041981c41080e10007515500304901d91640b0644a5a5019240c5400e92028000307011495680c00780004107000c0e000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 99418075 1250 99416825 99416861
    0x608010302060c071802180301091e060603020a0e040b0c0f0f030c071401020a021504020604090b030f0303040309050f0f0a092301030506011a0c0d0507020d051009170906030604 78
    0x584c09401710030915400350000a40c1c010520515030f000c1c0315000003400302d040e0003c000c441e400da03d80c1041c00381d1115041140000f506c42800501189400020245801601100075a03039075012034452201e0440f015100078125002080c3e40306007500484050109442e16542000c02c5000c040007541c1c4083d14028960104001c640e00248110011500b03c0030394400042e142d8a4254019040c251100b8400c000ec0711010200801039441a0584058500300500011039600044c04a0f1800c00d9400302e92416201c08800c0004160b8454108000c2e41c1c0103540c1c8011111a40c02448040c1c82c02c0007446502c10b1a40b0f4007030001d82c1c1550300c80025a5440c6840a942d60341c8207044080c4030100707070801d903020b8110300018449003030000400440000c22101d403a28040f0320030f018544404181102401308803000610100399a9494200b081f41d50304102941c4c11900f00c03280000003081d59040444001c081a6050100e1511030702c1564001c050240803c1d1850303644a00308002030644000241d29009 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 99419325 1250 99418075 99418079
    0xa0b1b04051002010b090601020111070605130803040c06140c030d050603120a0302030915190905010f050108010c020f060114240f040306050a060501050a03020306211609060608010302060c07 84
    0x76440c0d03034440442d09140c00002d88207071402c00303109204000802c1241903a0410744c01d8089406a90f080700c2245421480006d1f40c0d89403506c01281c0310941c05030142c01081c01005000038040390548100403940c1c0b9856103010340d5200b0143e54003602801c0c2d002c0015810a11604480d8191031b0080380e030001d0300030291450700c1c1c40c0c40c404400540008065000003503002c410040380c500700300000c05200d81d110110800c2880d0808d9425011280b40700c14008150304c800da44410400d09400c40300074070200c4102840690307101c0721018000e012180c0c01078014842c42c503214607854400b0580e2810b0750301d50b90448000b00031035020b01010165400c0b42000e644034103080d181140282c2d00260022240754030f016a0b9039495410704009440c00904a2814145042d4082001d680c110040325a2498a07080141e140c0d5240d00004843c0c2c1c145d4026000340c44d00c0d01806035000c99011039072500704260700070f1049006880720301c01000c0ba90700740169408650f5980c0184094644003024049404210048400e859 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 99420575 1250 99419325 99419329
    0xd0503040902070b0108010b151c0f02090423061c0b0705090a0605040602030910050c070e011a0903190f080a05030403092301030509070905041109090a0b1b0405 71
    0x544540e11600751a503021403002d0810802c101c0150042c2400c02c001d200e1100d640001400c0c10050610909034064006030b01c01e80291110320074801400e48034010080302a0380403240011754800c0820074882c6c0c0c90441840b82074030403000203140705648116201069031310b2105100910925005e51113000c3c86260f0307403c000801040031988503017101c0e600e080d04c40c1400740510000540d19040401440810b000c01d001c007035800000d840e4030b07030401c8800d0720b0f540030000700c1a1924410351010040c103010750b2001042c800e01c1d4803a0141202c865a00480e081880007070881d051340900880e01d585500031080c0d070a40351024502031103201b4043c04000004043d56515501c04e81c0c042d01c1000007240000c01000207143d081a1484c0040000208200f203440ca40300c4000035450380c80d41c0f07090600d5514408280c4c210003c0100380082d001c01c7c00100001c1c10f19003003480c00902044070040c424200d0710009600c001e00071480b507074196030040740009580c490000d003030700e207000ca2518003045160030b02000410b0703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 99421825 1250 99420575 99420577
    0x703090b0901032903010b03030703050a032a09030b130f11041d1c0f080f0a020c01020d02091f0248090106050405060a050705070509070513080109020f0d020d0503 72
    0x144c04004060202c000040506082d03032100b07004203100b60002e0140c403002c42d80143c00c8458134015072500194110303003040c441c082403640240742c48072112041011300703d0507080306501d81501c0c0501c1000d941903869060000c04084c680b10028803030343c0c85d0107441001516000d480d00600c2c0c0010000308039010b42010b1855515502001401e9a43c4000c15001201d004282c2c80f4a2850441c50918810000c0c010090708190024000d209415500c0c00003034030b03000043c1d050b00c400b524404001d5623101212a10301001e0f4010811003840b5050b00ea8003100200010910000100312030b0b009031040c00b2881200346101c841e05046042e000b4205046000c3c04806620413507030501e018682c109810185c03409010345d0780030580240303060180c03c000602180d40c482c03043c1c0340758003624a0016591002444c04a00744451580141e4100003c24180489543c20502038200c2c03101c0b59034241612a654007405082e40d904030030194100f0140703081051507041440c0c600034010b0018061004030440366488520f1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 99423075 1250 99421825 99421871
    0x11010f02120708060103110a081806100801150806070c03090315050106020d030e0c0d050a050102181005030601050f030408160503030603011415040507021006060203090a0504020703090b090103 85
    0x510311120040142c06a00481d0141d0403038000e18003084021400d69042c0814840d51050700280300c2000c00040c1c0c860266265101b20003140010b54489041c020302e072141100d22406410420f500340703004405a50241d0805504440d042030050040c0d0b00c7d800425240c4002c0f148040d8100103019038003001203555442070300d207408100d00d000140307589481e10080c1081040020182054148200c0241071100080d0440c4422030468502c2c6c034029403403410b549080c40040b002040c9c1d50012500c007031260740c0f4081c0e8056500041c0e4070808021010101200daa00c8100c03a514003140040c82141c960284031009154803d1081504500e40440c500300c1940d52105802c086070254000004c00ca03050130280141100740071601c0d1501200c0c00d010b034065007203020544129001c1ca640d0b02c002507203140300b0044856000c690140401502e6151a40292242d0284240c1b50080720700c2c142c00a12401e01340308841c0d286426580c0c0c9030304541020359005466004c401c5950401d034894004044400d07040310325a00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 99424325 1250 99423075 99423097
    0x3040b13090c0305060915181e100e010905130f0606140f030705060a020a0c080601030b1803090f030c04110d0e0d08220812190605030304030311010f02 67
    0x900d440c80c111942094401d4400107034100343c00c140c24441951950101c0c190006180e000d0000800391a0340440c800e0348281c103075100480c0004080c045151921641c070840081c03070000c040120f594643c00c80044c13001030302c40c1180c401401c00042103a41c0c100e5120359003141104601c002440c0c1e40d0344803420145480b25082d10031565442c410400403614684c1c0003008034003a0391024660080d840002c0d1140098440c580c0981c200091b850075151003441087c04242d801048095200c3e254050381c3d584000900003180e8003180071020070b01410044000070112101d030380046141100080a00a001d1480c0d0000c5070540700d01d160829a650307850055407201c002c6000303040d8a40007914184002d40740d8843c103403082c0d03800000b4000110381c0c1c425089540700e030183d072944c840104202d5140c5001c040640380980342c034a001c01c80303c074076843c1c03510f00e180503100918243c14602ca2442558003140c0c2c1d80d00c02c40d42d160740100310030000607018030030805015602d0400040c2030500d01c00d49905130b03400050401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 99425575 1250 99424325 99424357
    0x61112040b060118060c0602070602090604080d0e030115063f181707080904050a0504110109050603180312070c05060708010e010b0c0f0a030201021911120c03040b 72
    0x30280e940d101e0590190703104e01d500840134082c601500030380070a80044000e886941c000032603e0610a50750102e0740da03e800940354a94030399507441c0581d251445001881c00190003000c1d00301080c50140107240b00204907118034042c0a1401c0c1054600704985140201e8010032200b1401e84070b080030b4120059001001c0c0b10726000c2040028450440308810851504c010076440b000c80441c040b5100c0807201040d842029658009a003410261401022480c07031780a42410100180290720750031207400381e886060408101005080190354099a5009580e00007409000182e074401581d410807800781c00d00b4003542c0c41d01d40a0201515101d504071681c0d00851100542c0c0720401c60100600ba50000941c43c1c400c81550405080c007a1681041c031548958000203d110100c1c510306024070003d440c4683c0c00c6884440c014500640070350046820142d010003001c000c0c01d5001d01681101442180c1800544210b004d000500b01c0359030040c60b140300291009204c0840e61500c9407006100d81c600b10b442c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 99426825 1250 99425575 99425581
    0x7060e0601080105090706170106030504020a09050903090f0301050f070e0112051509160207090903110a1b05030c010c0b0a09020a03030908010f06051807021029010203031003061112040b 82
    0x10752910070247d104c001003180200717101d0050055282190b054a1140c6004102901c1e54000203100207421340020000c82d207070409101c014080003004103001101a611101212228400c040c2200d1044030f02d100e001002da00002e4031244504d5046544010505100f0210802625401c04890007140c000582d001880100105450400c1603194004d24603ca00350014001400003901e8010300d100303007900142c43e800d001c002c15000d49004072490b130000341180c0760300c05681081381c442c0140054001581c40d10b6200403d25080200d1607030301030784060315411913100c2a50354044a501c5d009009189095580c00340400503031322581d000004502903501d1208190400c00b0b101d085440c0148202c54903803a217a020072a41c0c5401400c2441c0c1021460260b01507600c01005a08054501100109440c5000b0382c01c022071642080c544100381e103050301d1048089180c001681e480c40190790800640712508800c00006520ba00003c043d07e03600d490807410040000a0342d903036a401903034101d034140b01c0c980170 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 99428075 1250 99426825 99426841
    0x504020405060f010219030201020f0d02030a0c05031b09040e07150201061d060904063305030a0c05060304080403051b100e150c011d070e0c04050907030207060e0601080105 76
    0x38042d004102280d40d80003055200001035071342c04041d0782c062440d0024000d00710a06000b03505032819003044031252540c0d50341040765140258022100704e0b030b03e1454406c019000c9403040c0c050b2440f4a45020441846401220007100c0c0740d00700d2800684d002d031303c400081250b200180401c0c070042c410710009114002c040c0c440a400e68040d5045004280301851001c00c00c101c43d442041c0d002101500e058030103031510709102c4080c003440c030ba08021402c21050203507000b0324240c1020603403c1c1d2100c59007803441d41750410542c840c3c8000c04003914005003e5014001494090000d5030824842c040152506aa1395a4541003080400c0040b00b01e0540449040607828607900443c03011a6030304c1c2a0b030b000103141d00098400c07024a10155004000440c013042d80c001c01358465151080e914481d014032580312840240e681c4214001c5c1c85070081e181001c22885c42d480f00564040d918001c2082456030340f000f904030700a42000030142c1d12070340c175189064501a428001203010380318410000c40c491401502c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 99429325 1250 99428075 99428081
    0x7050a0f06080f0906060609040e010606080702120f1b251403010c020d0f020f19030201180c090510120b100503030a090302040513201f0206061005160605040204 71
    0x25004542580f5410084200030110f2910b41c07104040b01c0c500c2c2c03543c5014002c180280360341c140c3c47e00e00e50311b4000041030503a0001c1e100c612582d004d900311001a110304c44116814000c10340fa02580700400d00500c850030460141c4045241d200709c080341c02c00030441100c0a01d99180c0904600d188601a0090140b1800b440c0c02c28201303d0150005d2000100080c002903442514400d00b03401c0000c0814400030461085c45a641c4850b418001c4031483e040300c0c0300e8400000241c00046002d5840c1c18804170b000061b840c42c03031048a030486681c540c018176080010005e040c00500710b21071002c852001040100310541007560190040751106544e01c0c0c01007a10407011481c0d00254425070050000c65100c0e03078040d00c0b401c1900d07030594000c117861301c2c2c82d9075228a42e454494000c0c0b80c084001c00d406580da00f408000e6004030742c01c503400400030103500c3c0c403080302078001d40000d4010b0304814009602420036601980440001c0e103061403400080c4c002000b154904282c007280c070540c0758000c4c0029854180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 99430575 1250 99429325 99429331
    0x90b01151404081009050709020f0c0601050d020112050403090e151207050d0602070c09090311120301050a09020c0705031905010f0b0a03030c030c0c0f03050f01061802090307050a0f0608 82
    0x50307450300c1c081c10008101c1d44c6000ca001e60202d40f64441d04083d080100502491000b801c0203041591210092001150190440803070212180311702000020203140c010425480c0c1070301078481400040504c0500800381a004200b5014001c0c200f60004025611241c080c0c45060383d040c44e101250054410064128600d040b029030550100c43c043c04955621603444015652001c0016990040c0d440c5c4070000310240c0e40000034640c9084604402d06422860112456065070140c035104401c0300400300007408280102c44d00484666003c1c000740b00150b0041c04050644012280020b90301d0000030301c0c1c141c003191641041e01112440d4420480e00b40200103002503091024484a1b038184045840d1402511014003000145c51000090600844a1404580d00a81c5c030061f502d8070b031034102c29407924610003207402d4415414101d00100041c030458013562825410080001980d10800f0040c0d0409413500e03505008906002509a1311400d222005040d89414004600c1c03900c01c000d0440c45000b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 99431825 1250 99430575 99430607
    0xc0201030f0c390b04230601060f0e03060106030501050a0608070c03032705010c020f0106030f03080403091703031626071202121609030804120f051e0105060f1f0201090b0115 77
    0x1c0151030450302041d1f0f9030541c3d0148c5041c0349078412902e42240c400d000c2241b42074060003100000315010303a06810030341c181c0300b0560b9034071140b96947c3c0d011103810348100c4038840080c8841c008000064403030381041404188401c92400c141c01e0307a041c02e22517421030000c12200b40e0f54030800b850160b0307014404814174110f104001c009040c55604d55201d40004803600804000c25000085d0806015521f001c0c080d00404040c190100401c4590954a42c002d5655401641e80807071302d1040c0500c6040c044440084c006c2034079008101c10401203580c0d007c007038004814485c0074094141400400c0c0302400502c10b142024415906184102042030080521040c1c100f100c051800e20102d502c9208031001c844020b080790606c4d00980c10907003010301d1a408024080c0c01107800001d401d48907000d18521200c4c024001700300d031342c4a440c2040601100144899000245e02c0304e807542c100c202c00362411900400d4000412484010b941302e1448030001d8000d00c1508182c14038130090581d0080407040201782d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 99433075 1250 99431825 99431873
    0x20103060906080705040e030c0f0c19140904060209040c0c020414010b1207050702060703030e1203010f0512100c091d0c09040f0902100c0201030f0c390b04 69
    0x81560041c2c8130096405543d00503a2218200024400b00b00704581d240c81d12602030ba11901504101552120700c40070310644100130103080e10004841008030101100c1c0038010400c480d903802402c2c4403c0b800010401e40740980d081c410301c036091b03c0b2401031141c20146c95403007d100e2610f51042200705c403404202d003464014107500500c004000a02154507442500b020842d160380d81000c2100d00b4490713400d00035080103003c00c101d010160160030884031000d200703003952510701740c189550b4406d020900c6406021070342c03e0740402c00c0b824014070450002005405560205030415100b00544208200310320000d40040b1080204800481092b00c2401c1c0c1003c9c1c0070540e040c0300c81e108510340a22000f981c03240d83e44601840c103c0c1c44a600907230352154042c019144040b540400604185600003050713002c03074280100b182045810744a208520700483d2905034010b50885407038a1024071804450102d00310721002107440040c41c7d100c20080c0c920409040132303103240c140f50410350301402c9059036421041c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 99434325 1250 99433075 99433079
    0x1240f0305030a0c050111120406050a0b03190c05120312070203070c060e0d02031006080d020c280306020408010902120f060c0d150801050406140c040b090607050118020103060906 79
    0x5002c000c90f160706449182040d804071060400500500b204c80c0c1d0000c99203c005806400d030302e42150b0b518481d80c040c650410240d0740d003207812010354190710700246e8150003100b020248201c191030340b90f07103184c001d00c100c6481584801c080b075003030181502800f2182d0f00c0030460180f0f0047c04100b190380180c00307101444c01e08010b503544c40c82e083d2040c0102414082c6083d501929902c0300101041000d400030100c49030f40d484061601d004040394010b828841c000c58104500d05400000d640840000203031540c40c40914008940000e88518038010800d241035402c00800700715280003402c0607003821000000d4200c060b04c104040c2c207504070359911094100d00214000c00d0804102c1c203500c603600300c0b48030342c3d43c000100e0060024892500b42c44040c04102001103018507056004500c174502c540c904000c800803642192071a40c10444122400c07190800c828091180358002520200d03902900d55810300b00070340d403920300355003165107000c2c06180242915419036905024001c02011129070801c0494 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 99435575 1250 99434325 99434333
    0xc0102130f241e140313020316120b06040b060d0203010806060405130b071806090513021e090f15070c0e10031b0e0c0301080d080c030a09031101240f03 67
    0x2901540d00140301401c10004402503074010525082e00003810700c8040d6032407806e0340302c1d8082d5070110081a4080d20440c03405424450310f0300b000030182da40c05001d80342c80402940d21603130501c10040410750801c0d2500f1a42c105510b450b4082c011903000e82c1c4d00542c803503040002c46441c1000080c0305900c00d03800c00c8103000d03410300c04158016a05030000c09110310b0740c0c0c6482060b4ac145030100034840800203071100001e40300354046407880644400f00ca108551400324a0f290050340640d02e00803698120288040b0380a800c01001002c60200281205041802c010005041c1c08269129007202400c00a127401c200248003130390102802c0108824800b42c101642d04600503074060200514942803500d075807030101c8080f200d05008180b400102241d520f040e6188108540003031141c00303414420786e10420707900d03801000c0c9284903d1892208600f984e40e2444075030b000d0a40288181d0074004001d101c6150440e0a024040d644034440514502071150681e10303640c4424594004910810900024000a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 99436825 1250 99435575 99435587
    0xa12120201110f1204060b13020901031410060c1b0303050c060916060507060905030a170c12070c140f0c0a06051206010302071a040302010507080f1302060c0102130f24 74
    0x10711340d001c0e00c4031029611850102c00400d243c102c1c4940c444d82109515800300069001020480000e076020300c00035092446003041d00c40c080d04c0d0306502a0b40d0301c6040c8107480c0300f4058440842e0107445504540ba041c0c0419421140040d0000d50000d0300001d500715244804001d42d40e00a11410003c100142000d0b04100402e80d2034041c810401400140e0507003805240d030044070003250130100b03982c0c5d030307048041c8064441d480c3d101d0840420110000020f15600c810300c10350f104c010711000e98200301e60700c6207012100011513441c1242d2000700d0480c0e411413400e042050041c2d0f580f8200c001e000c4020081c0400c00400c4440d44510204141003001c10155040c003000c0d44d030045003e007000b58883e001e44c40d0050b805e188580c984200803080000300010305905401c51409108140c60f0313440c141d1511a21302c485180708541c1321100b000108406001814044003c1000c5545031000608210010b0000345072803095600140c005449548140075042d401d0000090120304116010500d220010010f040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 99438075 1250 99436825 99436837
    0x1080702070e090c150406020705010c050604120c0506040605060a05040903230403141605040e0a14011d070f0e0603100b130606210b030a060203060a12120201110f 72
    0x251801c0c0742c0216003503000410500e4a01c1200a00c8201d141d0f680b0a200113403600144102d000520900e940007400d0b5003d01084401c5030b82020145c8169540d40d107800343c0802074042010100281c81e191000410b00a1101d43d0046110b000080ba850604008220003140290406840707580b40c01b80c80d00c0080d80054902201d007581c0d02d145105c2846624004016001d00e50001d8101c120000c0d04041d04100030a9400011112290203c0e440791940e05010031034210b034075000d40540c1309002034408281d507080b0b0080388007000e10012070b203110342000c0b0148010850f80500d05650211100b40301c603c108401c0175004e082c04c82c2c0700ca0180d29001e4000303907403080e47d10f501c4404030766101c1405090340c45501e60324190905018003881000e5a40300002e2404210b0408808030f81c2402040e032007140183e01915140040c020010102c0c05025200c600080d170014110350340c0441c07a4100051108925190944450301a64242d0509802050040d00b5103048000107403590000b088000000c075907850595003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 99439325 1250 99438075 99438089
    0x90a0201081504020c031201150f08130c08010c02061608040b0408070606060c061407021b040b1e1e011b050f100b01020c040b061905040e071d0108070207 68
    0x11075190192102c04103600b800549800c40d00000703030701d06440c0001000340202204070651170120b83ea00d0500242c40d41d98a50841c0c0042e00384101c0e5182c11340719407850b81d041341440ca903645e180c95946d6580c0282211552003401e02d40d440d0584052504c0c0c041c000d0991150280c3c1300b42c59180311342c0c1401042c2c034900400040c9202c04c0140441e0501c6400d001b40d50559600c0b07401000000c2d01c508018080300940003045421a0404080420491440100c41e0062407140c00520b52006804c3e40360304501c00b8111082c2e002580c4200401c0b1607611180110f2582c4460348181080c40420700a021020b0607400001404d50a17600c2c46190599106040d0308240200c000e1055440d84280380540c20401e00b86203507850752050a582c6518036021364001080340809030201ca101d000540240003d8402140c3c4296100c07000380400081c0104110300008140300c0e03031608502d0b081d1070b440040e0070b141c002e560440016009120052080750038459440070b0301400d0030400540d24181c90025580c44040c05581 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 99440575 1250 99439325 99439337
    0x1b081003080a110a0c031202010212060105090609040908040609080a080a0804060b0d0506010e07020706120e0f060703020c070b0403200a15020a0b1b0d05070e04060e061008090a0201 80
    0x103441d1081201c24880c840070070a80b00444d2550510320203000079400140c942c1e44074080144501c1e40140308450041107104051120760340c6100c015211600a140b000d074102408101c02a469592846502031240c41162101c0e100c904041d00200b01d0403080e00b1040c0d0f240d2048001078045041c520a50b1f40c2ca030410318004280f42d441d441c0200181030500300407034104001d1003081c0200040460074070b058035600001d2948a41d100d51089903038100520a55010503080346540681054682050440244801c00c030381c2d503615440c180d2480c005045a01400007680445d50003e1410b0902440000b0840b11001504080c19600d5054040d501e154409550a04515900e82161113510000c8001c081082e0019481100b012010703440d90040c01084821401d081d00003064410158141e620101040f01e615003000c003a24401030080c580548284e00f40110180c56860030703540d501070075010b03100400845d6607500700901400780d020308401500e0f0500078590300704030324010005910078801d80c0901e455 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 99441825 1250 99440575 99440587
    0xf0a080a0504051309050c040506181e1f1a030601120b120a0b06030105090a0201140906191107031e020f0402070506010e1003080307030b0f03101b08100308 69
    0x20740300d5104607480150044100040008410000d41c0030000c0c07240070b50203903191803401a0402040381c03000ca51540e4048070035491901c880e03014001a030340c0500c001c49194440c103002c58481c818403000f1690200e098424800c15101000c404074942c00505a0a6145003104840440c000031400000c211f181044a01100c034075911445070040307414074001030082c1c4c000e064019500b686640405405503800565200440c2c4141014400d2a219052100191128589030342c01181c03154035141c0e06124520702802035404a64514004003d100b0860b260740e801c039107810401518100200203c81480c0d0843c8100b040481c0c1c0d440c4c0a0100a081c80b00a02440210f5100191002141005250b040780c4041036034410171200003202c42c180d03510a945115103694218002c5504007290100404124060000c45c07510760080c1c1001c0030742c20008081054803451309020a2500c5a0000c007000440d0703c404544400140909111885048a140002d181d25290300c80c0c1c0c440c010244001854007100042c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 99443075 1250 99441825 99441827
    0x20a1a1614040504230f07170108030d02030c04030b010e01090c05131403030c06010905061f120510030206120f0105040c09030f02030102040b0304050c01120e1902030c04020c0102120601020f0a080a 87
    0x1d00b0f0701718009502803103980d04041c141500c14040494416000c41d035030821565410150062a9049500640045140070341030070444002c2e401c05442000d546070140408000107101c201280e010f4903030b103551315250f98545070300c0c00107907403002c5080001c0c0142040700c3c10301100b846896005481c0b01c071481e4150000740b140800d1861040001414180c0503c00010504503a10f411060042000301c442c0c46070401e02c01e80030600b144501040034046444000103812060391074009680c0001e0b101c0504110907540e402192065012207040c400c3c03503e0a00070031003c260b21031045409044161803c0294048001000d8030b0000c1500024181c03050510900d400c41d034007501141c1c09085400d40b0301e0b849007854640035a60b5041ca00c00c00740440c49601d402c2a01d11010b12440401c807061000910002e03a800c03030303c01c08c45a00000140c1e0140901e0b40000003035112400100304e20381d1910300050360f800c0201000d80340300c00003604450454010400c85a0b4040300003900001c00352300442400d64440071088 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 99444325 1250 99443075 99443111
    0x20d03090f2307080c10020303091b15070510060603110f130b16050c040911090403020c09160201060f0e070819060308030601081003081603020a1a1614040504 70
    0x2c011100d501c41c0020205101401103048a407007101030b61030b0701810880c441c0c1684c503404101c40e415401d40c070486c454034412103450852801e41034054041a8005d402e082020026403000030280d80d5036100c00c150050780c882ea4818680103000358501080f403c0451103156803144100c01c5d81031a880f601003a520303550401031140d08c0050640240085d60341348030b200c0d1ba41420780c0b20f250943d00c83c0a41c80994000f800c0500410310714035440400a00c002080341c2c100000114040c00540448c400c00c05c0280c1c3c80d071150301819015210784000a0840d500208000f801d40e10281c000c202585000042042501e401300400c90b04000c9500b0300031100c2c0d4400b0040c1d6000c120000720240760350309221000050080304001580902403e0341e8082d500d542e46a48040f03141c040d80300082c00e41c3c0307040100780c07144202048105a814800c3c4152136200104c0c0d100c95105242401c0004054082074040c4080042d041140c108000e0980c10100b4003a24401280c0c03e95000e0392083e00c0c00b071511400650f54144a541c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 99445575 1250 99444325 99444383
    0x5010b27100c02090a020406020601150318210c050303071b0506131e030f08060109030609060c1e080a0b0d061e0510050604030f060618020703020d03090f 68
    0x580301d0544007940040081040301a25001da015032260b8002c00d0342c6500368004c8400b03403802078005101c40d07440c0040c1a41d0500d10002c0f0001010380d1a0b40da140540c400c05034004000d0301800c00000703000401004511810400c100c0d070701c01d104070414008001a004010340e40d01c00d001c1c0c2460f40200d849600c04000f030407900c200c000e0150081400b000301034994900d16101160059101501947c0c180c004000501072020001e0041100103100d13038007241c4642032076a803000062400b0312500d40e6980d00c030030584580b4201112041e44410314446415804030124030202e03c84481c1c2c1c2406040301c503003d0054640504032124440d00c0f021000f4a6803102d11140044545c002c4040050b031211241c0c41606d855443c00100f039103410400881c0d42d2203248503600050300c000404d403514107440c40da02d603000004145402c40e50a030f1035440001d40307442c1d80599070b03125105080f009642c07241c2c1840c00a0400c003c50b40c4900a151802e03d01c9030200781403650351a40707203070b009101002c0f00c00d00000c0300504c28510 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 99446825 1250 99445575 99445579
    0xd03080a0905031b0d020613152408010209031b011209290603010c09060f0e0d12050a08010501140702040b1504140307170d1b020405072105010b27 65
    0x60400381d060320000081507404400194241c1d51f4585440140603100450350b04042c1121010055200c42d040803940082c0500f0681c0c01e0381c0f0040840203402801040c070a40c8107000c0c2e80d6002c550303034455040c20b0001d2000d18910b850444c2030f00300a01c0000c0c1120711075611601e200c03a5501c003640c08020041007042704410002c121241d1820710602107055400f001c5941e03d0082d40cc1c064014030180c000c0211005992540d1900b56440d400148111411b40d1038424855000381002503040101b8500d03524030a60904956565a54151a5002130081181030b446641007202081514400c2102413003500d8000b64102c038049960081c810000e840d460a40030b0b0320004020010380020f880c0007000382861400001ea00b48c604031947c51100301e1580d14120704d41c480c0750704a16032038103d09204403e141601030020100010603a4190003140071101c0403180e00010502d1851406200c00301c911400280401d00b0005200f00e40c10244200c000d40228103141d0700c95041c0210031f1a40c4138030040064942400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 99448075 1250 99446825 99446857
    0x317040b04120e100f0212041d0108030313030f03020714100c030902030307060504080f040f180207050a0201080a020904090b04022b030e0d1a060102010b0d03080a090503 75
    0x2050515110000c000d6404950b418051000d0300754450186480c101c1500c801070000c021004030210a9034a088049082c0c0114000d01c4200c1d500000c444000d0005844012100d40703600d00030240c0f500c00b281c410b80100c1540ea000384104030040610400c46e41d10580c2c5403502d00c203814409607042e0064000e009008041c14141c181e04200000d001600c0143d404071070f00284440c5502c040c0690403181d82440103501034008203d158041529500050340042c426000c0d0362400721041c40740180c41d08140c01000c2840d440607000c0001c1c034980f00802403000e81807002140f41c44003990303621b030795039070185402410b0204100000390b01041950541d410604040d10920a444880c074152107940000ca404070311441a051b4803000e41c0a4030615845481a1122543c0300304215803419036490022415140e40042c05001d03d400088901094a621201d00b40042c24075043c10400642580c00b8180501d0040080301c40032000f00b680030325020740040949000107002c2440e0f051190551040c00ca038036504150b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 99449325 1250 99448075 99448081
    0xc0d0c031b090515100302070c030803180604050102090102070b120411010e041508010f0e07060804050a021008040c05100e010507020a0b03010b030117010b0d020105090d0b07020a0b010905060105160317 89
    0x900d603207104d48040e9040750f81c0d000c86070004d9016412409403d60150040324006000d000003501a4015900310b9851100906500c2d80705812900c1c01d0b40071202203c1c0c1e83d401258060403540c04011440242166035003407030500000b499004c0d00403070000c002529000303408011102e240d001c2c0c40c181c0c103480c03c081c00920a42116848024100c012841005211b40ca40b4008090440d124400c20391007510380e0010b402c0c082e00d070950032910f90001500a4869001d0031803a04016640c1802030000c0d000251030761001403038542030800075506240c1c01240504042d19808a040390320400c0c1c0c0c3d03800c00e002d00384030391107031031500115100f62a01c0d0020f03440300c02d000002003103401c44040994100c5005240c00c1c000382200c21410b509840c0d482c202c29030001e134150711a00c010760060b40075280e41c0c1405010a154000c0e0383c0c840d0102010141c4504016030062003d52081c440c05030301050142908031400e11441c1800c2c400200684180f481250301c50b140c4c0c0200700101440740a42c034200701c0140b80e880c55582 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 99450575 1250 99449325 99449341
    0x3071a030402120d110f01180b090c0d06060602060f04030509100c0b010e010e090a020901090207061e0f0e0a050601030809180f06130b13020309030c0604080c0c0d0c031b0905 77
    0x102c3c070641480341780c4180011031400410500503035082060042666082e244c090796a100e12040241c141075990251070311b0040765880e00c003542e421003402031030701007031603413a206020342811000340c2403c50059881c0c0030400400d4100d002c40b6008502510842d200b040445011102401c40d004006d00390110200002601c0d0b000c4d00807141070368803034644ca1013961142090181d070391408102c02900050542c00410884410f64007030300240303015580101d038021900c202c2d4400340b100805045045541c0301e801c019840304038070800e0300c80d044920044c81161010385aa23592010140b000405c1c00f100000e00d0212910740203491140c10300f203198044000c0c10581c0b420405800101d074001e008100d100e0b01c5002000c0c10b0300410001d9a8060440180b60001c80b1700311002e540028900d5035a0302c020000c00071162001c0102d40d2185018484541c0c50b111881506801c11a4004d40540300c1c085a0210074082030003000a071003141d6001d18030254082c8824101900101d0990040352300030701e0402044818 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 99451825 1250 99450575 99450587
    0x905060c010501031e0b070f050904020d05040302010605120c040222090605010e0604150f030e0a060b09010504050402010207060f12050f09010e011b0e0406080a0311060603071a030402120d 83
    0xaa4800c2c0f51001c0080070318480319004901c50175020700b200000401007042d050251b00c03242420402d40c5001072a01e103120010809a9000b0302340311030006e03034450802c41030560a210f80c82c05010700326004900e040c06011490380d9400e600d041a07200d19400102a81c0d0030b0944841081c0c100d0706011201c0c3c0d603039030f2824428014146071203040d001c00c1c27120480031840d103820001c54082e11101c1503a40e009400f4090100c0b902101070f1141e006160340e5817004090040c040001c0d01955100d442e0100d21111204c0500c58003a0060340803500403410f040a103c0140e07004604030087c0c80300d40c03421790b006003119641114528503100500040c1d900d00310174031003426201104a8481d2543c03200900c010a8044d1489080300c280f00c0c10038455140003402000750718840c1c1d040e005003e6000b04003003605505e07511031905041c444c07030084001c145889035548070040140300755680718000310b000d001070030f01e810017a0b10f01c00c041c5803081c130b50408000700050440d9600c005080921800d10708030384080f081040048d182c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 99453075 1250 99451825 99451829
    0x100e0405060f070305060a17070b040b0912010207021005131d060301050709051f03020c010501060903030f020708070501030e1c0e030c03010506030c0108071101150302010f0e0f100905060c010501 86
    0x1d1141000000e6203140640600c078019007003d45094030941c0f400f1214503420302303101d00a0041e400344050009030020301da006000038006c500c04207681c41d9030403420401c040c081101155096401407241c0070150755510000314203040390782003640d0b07101d00400224040c000310750082e0b0f03c56450f40000040d601c0701c11110b941310740400c1c2e000708030580740c1d102d099940b03401c607102c2d00b684001e4155a0b80fa280c6941c80254101c0e164908000d400c1c00c0380c10114a003500c3c000d8001400003080020200103056111030000074026007400034101080c1441940c1d0384411460148505054a490301107080d41802c1144a215000c10009c40d139540310b601c0c00050a480c85006458407070b1192039400341051806114490007060001c5c001c045603413010005450b44500240303d1020b000a00031114111402805884c0386039110f8484140a40d04520026001c1c1c00c5540c40c250070890101d001405c55125042e4a05050108031003030000d13010203c00440da00d034401e801807034012202107010019071105400c0981 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 99454325 1250 99453075 99453091
    0x70c03030e0105090f012006042015031605040504020a03141602071707030b010b04050123030403180b0708070b060409020105180415080307121e08100e040506 70
    0x218001181c00116043e00900c1c400c41e90166007000f88042640c0980c038040c5006003600c9122002c1104e100d54075040030340c1200c040e280451080302090001d020200d660a002c2e00403201d414003844041d00440301c40c08000c1c1040341c0c0280b5001c03c008814060811f54000b004000c105540d26841914020060010184a2141c0444030b00c00300710402c00c1c6000d2125001034640c0280402071800742d895080002c440d90742c440718052684080040f410800c003103400303080119a0543c0d50b504c1c1c0400181000712145010002c500e414020400203440707081140c0d0081e415103400074509004035000c490044440e40070101200c00082e0300002c00a0709006800028001c10f8039041a58440b01800190782800e41c0090019004000103c9800d203441d00ca11210031b005040080c4804003101940c004100f541c0143c1450350000c100d00d0208480b540280c01010342d00c1c680040900151051042c1404031020240e082c400590b00149081d082216442c0080c01c041006400380c0c02c0609006480700407d43d00b0031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 99455575 1250 99454325 99454337
    0x1e0a080105150702040b060904060f03050d020601031a1b0a0216080615060f0403080a030b1002010b061c020c0a0f050f0a02010c06050c09090c0405010e01140d051803070c0303 77
    0x901da1500b820403051581c051860a4a080120b90070000101240401954480424003d00720251218422003000c0d01e41491100300c10360071070401c1407508041000764804c55000100502c0001d146603143c060810100ea10700400c1e458101e40340e4060150b0740c01c40c3c0220000411391601e42d0380c3c0000c0700da41468803040e010703800d583c48800481d240d80c0c044841c9040142c0601c5413a00d01d04003280100042c0701091085d03400c0c01d8880d0342e828030300d5000006050000c1c2d21041d40006a2920094207086032403280001c10041c048000490481d01070250032103100380c800c4c004441d0728581601201c1c01001500306441081c050352524041b070304142201a41d19115051840682000003e000810682c05071511b8802c03440360707550203002e0030300182042c2c40040b09110044050302c1e60b0309410b00840c4025025034489042c2000140780104491060f41000003500384401c41c00002400c8451120000344003080f0b941e04d012a42c0341c0c20800c0c03200324049200015820091010303411050040d80e100f96144 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 99456825 1250 99455575 99455579
    0x62406020a080f0a050d0c05250b0a0510030c0f06020f06010e130606030204090f0501050615030a0c0c0c0312120c0e010804060b0a080303040c050303070f0b04081e0a0801 75
    0x100e80d29074070103030700800c0309804000a403c076890901c09049100603078904686407800c010031800548121844c14804140045019112400c2000320445440740014400d005403540f901d40100e80320000d060b90140b41d40d90740c00b1801c112881d0a04002441d00800b40d42c5020344d550b1111030701c292580c800c500c0180201801781030380410202c3e25030704840c80c2400c01e02c0d02d0746450309041d1089034011421920303243d40c1da0300000140c40f14010b14a826009d04070b1a1104900c030304105082d558000c4c04c103485103103070401115001c1c0c1102c068a4200f9043e013030000d059282c508007070340d43e20f0074190041c102e00d400321000000c000c031855200c00307001c5059a40344008866900c403036081c1c03030f828030034100484c03107415270100309511a100055019000355000309003040d66001040b8480d45581000940360400010042403100803241c0000400c0160011440c000da6511054640d40030790000900ca110800007280134000c2541c10340301d0040c0c40308081c40c4491400246245164417014410b07000c50700784000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 99458075 1250 99456825 99456827
    0xe011202042c010501090b0c07150302090f060301060f08040f23010605030109120c050c06040b0d0509030304080702060f0c0613050d0809070b1c0f021309060510050313062406 77
    0x2d4101c400603100c40304440e00340b503421071681c0c01032329544c001c51103070100c0015440340c41c101d0300c1009008c030b0700c006945143c96010f008224100080781400344100b0401001041d901c001d0041c0d850003035181c12038494841d4940240300b11509103020307082c1031940c0c01380d01c1e481d41e41040c0c66070300c110355030001c01040e030b40c542c1030509075482c00c80b0140404002842c48640d482c0101d5000c0c04040c4148159032200343da80000501a82282d04003900003040810b0701c0010302c1c802e20440347c01c452502c00560075841c042c0d49100041c465404001c0c050400440e80c0504c1f2501d00c0c0a07140e50f80540410303a800b0b4a8459920300e0350082c0801d064402d84101003d42c5450343c02000800d008404140242a28a081c02c403d80000e40c000340100c0d00030a04202d0750362102c00c491243d031b412248442c901507a00d1590000300c82d404e00b41ea8004451203483c02100300a507546648084a2034445400c0540c1c5a40d60000354101d044040c01c4060b140500700310560714440ca80e441004d400803880c483c00c0004903183c0320 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 99459325 1250 99458075 99458159
    0x4150206100f08030f07060207050a08041a13060e130c080f06010302161112060c040f0b0c03070b06040209040905010b01110115030b15030307030f030c050a0f0e01120204 75
    0x202c1d00360f45410170030003150440a00d4004280780703401070001516040881c0e1fa02c5143c542d112a0554482d032000c2401d210b5401c1c2000b281d400c001c070740aa00c0d0b05107084003881101c080032a10800c07040c002d5600176460203464184401e01c03003000b408401c100d882a4254042c04480d0111000444c4d01201d80005e0b00c0c0d58003d01c00d0300e0015060703802c6004480500c3e540c22a80455030380580d903010f8400a103200a2010800c01288200b044006554940d403402969203800085070b000342401c91070912200b1410000001034070360164201f0800c000c203441da2401701d0003c0c4519003407240c02504000f180700520505411850f0800b600386e07036074403000302000c4070705080310120f0f0091010b007046284c040022500d03900100c3e400c420550b010030f17520165000002e01e16807000400f1400b0172240750300054000d405100d903004401960820074036007402000001e0000d884451070005000c3c031004586d1542c3d2142e00c60480c5c4a406c014115501c5880d00c412186240d9003140c0c0c2c0f211240c03103181081d03070104910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 99460431 1106 99459325 99459329
    0x9010e071d010807060206070804080f030a090506061504030f02060c061e130c0b0d060b04060c0c0504150302240a08010314060403080703020a030204150206100f 71
    0x10309041c03818005910442550300301c3c542c10050700360045402da601483c00e00e0902015a40c51410f602d090281c0551a49808004000c01504410380e5201e44682e0f1301a00c122134030750742c48904100c2221048500d01c000c620060004000045400284405070b81c4004c1c0345600380b544846109140c50000c8410012400c80d1900a200d24845280030f95001b08100c1c1c0d203014808201d03241d0000440d018401c004070440000f03802492440142d0020014000501c0c405558030303568500100600c464003003c0c1c1300b410700080000340625062280f940c00e1840c00c400685518603580170008101018985c034103009001e8040032000c00d4480c002094000c0c0b5940742c440203541541003140f01700d9240c2d202c20000381e0020042c0004242c128441c20b6000c200c0340340240c1d0f503244100d000c4000c0e000b41e501418890041d5a031000f51071b60081802d40c401d079042e84901c24880e6a9031a0704c41e00300414 = true := by decide +kernel

theorem cover : BRFrame.Cov 99280575 99460431 := by
  have h0 := BRFrame.cov_init 99280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 99280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 99280575 ≤ n) (h2 : n < 99460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
