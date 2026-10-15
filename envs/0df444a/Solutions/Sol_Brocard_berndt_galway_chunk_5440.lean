-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5440
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:52:36.897018+00:00
-- url     : https://prove2.me/submissions/cd4bbfc0-1d06-45ff-9dcb-a6f4bf9e957d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 978237410 ≤ n < 978417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 978238660 1250 978237410 978237427
    0xf01320d05150a0c03060b041401110f070302090711060f180a1a01150e010e01031b1107090e07092406030605040b060c060a1a0d0507031101030221090102 68
    0x2d003104519085007a56049401e00c0301c0c11030030740141600400c460a0038048075050a030008950f0085218213a00c00080403000d0352280d00841c507143c00484800195440d42000000c165900c107500e210407400340210000040c0c150384104220340045400d030780901003684544003448c0b1404005402040313034400c0d940210304a002c0030001071225a00c06d00020101c021070340071110404c04d05a1101d8520348d444000016400da200c1500818090b003420224021480c810048009010034508588019141ca000d03005083c2c200a403505844150380c11140415160850359060b600d201d0158006c079031100b0024400c40450703030490a0411a140110300f019450200711010608003980000003117a0760710300c14030090620303000341c500f051810317910030b0b01d8106982d0746950340e0000200100d041030380d00d54440c51291001e0711011000540109000d80880300c0f814195116415444116a14000340e0742204641d402802039442112201501e041c4000d120440f01e9038042006100d05419582000a0352 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 978239910 1250 978238660 978238663
    0x20c0d05071d090d030606050304060207030909090f060f02130324060605031501020d09091802101d030a05030a0c11041503020906180a1a030d02060f01320d05 70
    0x8401c410030308100515050419245041240407136034a01094245641480f41c5600182103a800690042c001695640f280c10100c0d00740c045500081011800c102c0854140007880c850f5000b8503014100030403051245000c16400c80c450848102e1040d902e04501300301140c04690a6200021032808071141c881409051008840890308410003050011081c804c484150f403100c03c1d50600e0130300040c01903a4810001800d000c0c7c640c481e081c2c05946500040405203402c04520440681c0035103000c040600c901405132440603240450540c889101c100d040c4039240000307044100030380100203103161907003080d01202d50f0303004130000750703084081103003951010384031849544008901301d0400740e41c803425403040000f46c0034050079080c42070441c0740c40d4090103065003a81c1034001c41d042200007103058000950b242071655142c4d040381c2c0360044402d0a03940f03a4011420714454411841048500da885210301101036003550702d204401604102c1c0e81c0d440711080c0880320000d0300300805141c42d02c00e080d507070a03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 978241160 1250 978239910 978239939
    0x18060c02040b090907030b1b0d0209031f0c0e0405040c14030319050d11091e0a0506130801200f0a0e0d03020a050606010f05070210091809050c01050a020c0d0507 71
    0x70130440e07200143c1007060202800583c2d421904030744c614031112258018841090244104849003a60300050301c4c035a0307135400c1100b81480c60481d8103281c4541c05000c00c6078010041d000c3c100001c110444c5240040d0310341071003500d00c900d500409040c1030300e007440d4410b13104101e500740300e07509440100054040381b4440316140790300450720355456599a149031108025101e4000102c00164414041b04c070469942c0701d03840741c01000b049900071402d00850300048141000743e00090300310800144a40b030082e0725006a2007503802140c000d000140b51207079040d218041010200c000303040c0c103020001040c0300200041a100c06940703001c0300043c00c80800a805ca0000720b0044016900481041d002c001050007201e41c00882424070410302d41001c90082c141d40b0801800074802e811881c940c0a1203070280415070f01800d01100d4401040c41072298000040031480d600392000c1c410341c06500441c1d8452400c440015070607501070001c0c9401c550510000088019040b1114012003101043d556040c0401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 978242410 1250 978241160 978241171
    0xc171f08120d02030408071a07140a0815030106150302070606150906030207050106091a030c010f0c230619060e07170601020c031606080c040b070b090c031009050d18060c02040b09 79
    0x40395a03a061030310f27000d00780260300340c60300f01a144207000101600342c2001145d81d009007034042d5030840320200c01c006401005140c020a02c00d404a15030240110750640c003500c1048d1041700100820f603117903038100c0e420444101c2e58100040390800c0901c80b103817180c2c02400e030081c41807002040305900c440610044c2d8507510021040050b190403401d02601d806c209002040c802030030156440d080e9040020802c21104c04043c1c11000910310105080b440302c2550904c02032aa000e07035030241001c1200b180d8002c2c610320700c0018241004070101d06c540000c0e80c81d60190080e0f851380c8158110460ba060341c2c5641c010f00325415401340c0800c4e00c000392014445490a049040c0e4883e04503030a184d005081403402a208070001c000900c0b09208400f107460403030303c110750401d4154003503035284107101f40740404007400b0581500400c0910b0700200360a03001480c17a80d1060003680d5403052501300c101e030b6018620749110500040b40c00101312650240b0348442200d030000c0d0010a590300d840c40821040350040d0345 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 978243660 1250 978242410 978242453
    0x280f02030708070e241312140f0106210321020301150201090210051303120c11060c0a0201120b0d080c010c0518040c171f08120d0203040807 62
    0x100710034075500c0704030081c4100702200c8100010302c441c10b4003185c5008544074a0624000014410160042c05805100500d807040c418079068120b442c0c80704904003a0a49804d0500c100c0800044005041c050f4200369440070f2a2108680c800003100c80401c0286c180680174895031102080d80d04030b00390741c0c02c008203003010742c050303501e51505030700c441515040b448070411039245c10079203c01a0b070b41c3e4818207140340907450300d43c3d1200c0548030790f2048007042e94002403601208400391079503107030006541c880e501c0c000c05464542c03404080c1030255a2244000e50b9000e0782007a0100070056004054501c540a41501d001940c5c3d200080404c42c6048601416a201ea9021803072022070315003401070300045190b518090b800c064100c840c003d801c41d503010a0b903110319266009204081c2c4114846808035a00d0000c110b0301c0d0a02d0141390080032510401c1211103400c2c600c0100e4900703000540040d0315098114624500024100b8030002034002074021500d0200404c0140046405486004a21340c5409c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 978244910 1250 978243660 978243677
    0x14031905191a0a0b120a0c0519052106060409120f1209050a1110080c030a02070f0308041205090102030703080a0609020a180e0c030f040f05100c08060603280f020307 73
    0x18108103540705100038889071648850103c4000800440d0140c1c1248e50035503900014141d0001c80300c24800c41c036009141c0040b80d600700000e181c00300c0400c2d2105c2201d445c0999640391200400d00080d03400362070001d45206034618103250300622681c5070000241c898900f07071415039854210802900d40588007a19554084c1c808030041c00742d012214102003c00302d80104145d452000c0c003800c1580e0041401900c402c0106c00115841410b0301214070b803942c040c20000c45001540b40c01f406240041c0d4003512104010b0200b04c903440d01030742c1260390f5003030140c00850400480da6030840341140700400380c54455455520000b01040c0ca80090054039081e82c81c0c00314a8030180002c001603010300e502070b4445c401d01c4000d10050100700d40c1241d4200c200880303510b0f40c3d5a26402c5c07500403000710f00c030020003500c104020343c80380e00550340c88105507613855038034000d141d01e0f4481000000e002c1a02c00c0c40348000070150041051603080110140205082e0010400c542050b81402c12600200c804102182410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 978246160 1250 978244910 978244931
    0x708040302010e011e270f030201180605151509191a0a080a020a050702040f0b1203030106030606020a1a0721020306040b062704060f14031905191a0a 66
    0x78015551501c400c1040f1641d646c1111410703a9107140303140300181c00ea45044014a0600d4800c0d0491031050311a43c0b00d015440609250a10047c2012160036035003c90b40c9480c0341c143e00d0311168082c5000c040320785960802e501002000303d5036207aa1b011030070900520030005000442060484075070710700d4050254450b125400040c18007000103040d04802032041044e0290703181c00006950b10140c06a80000b90302c0030043c2c4101c0140f80e620041540840d004507450514800000154140c4440350b4080c000d4642d01c8005985c1c4208402c0021b10348079504400003215100ca403c0707142d00541e40e1410030811903072400300c00100c05a404c4107000c2c1710b130000200142d50810b402102c50041c81030740d0007841e041c40c1e40c055a5407000502413008442420050a010690342d41c0c010b40054030300c0350b0b0f8401d0096511015506001004000507010740540c0c43d19101c40c2c180e4030780080b480d54000028125010050102401145012004a6140301c5180c00c2c050054007200b69144514194400040d141110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 978247410 1250 978246160 978246221
    0x5330c010605030709150e04051504240c0f0c03050f0a020a020904080304110d2a0b0f0706061215090201030f02040603200a02150a0b060708121e0708040302010e01 72
    0x2d420410140207c5000d12002803000220b55138200090500c1c00600c0c2c555180c121404a500d03240c2028132441090758400001d00355021820031941600c8005040b0700002e01501d6511900701c0203404101e0034000c10007001003000080400320b9052069486500c4a580000c075950415a416203024001000f0001004000440b50a541101b120741041e5000d00341e558003080b50000d6070500106946805035800c001c5611101005803804995058494160220003a46508041e070207032519400d03d00000f82d00c3d1700e5602803018081d000a14008031042d103100e00f9018002d2070394200c0c105035642400d094524514405800a001c1d039603000319200ba0410b011038441c050708502c0d1340c82001c003044469840341d00041c40009100007601580c4050342c582d0540300060082700496500b1020010f820020898503100405015018248550161700e407100703103560412096941850801a85000c25445070241e0030440c1d0291180c070010403200300302090a406d44070651286c00c2020001d50403108103051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 978248660 1250 978247410 978247451
    0x405010506090115030b030f1c0305060a050102031b0703060908030103051e03030a0c0507120807020f010b0d080304060b030a0809030c011803020621090705330c010605030709 77
    0x1c9800ca40c2c15411300c4201550300360702d14190414556506001403582d141808004084c524131415076035010440030340d1450302c06045549d000041c0c45d00d070000300a0700d020707400c060a40d007041c1d00841c1030042c0700c003c50680340070322401c00700c1038440d0820000000e11240076402545100e00f0304171303440703516505d09140382c0103401e584254103180d02c0004601505000060b07075409051281d0108003101072580a4440b4030400340090b02d5410302c0d51540c1031140e004000035000e81855800c950181d500b42c00b91908981c0400a80317a8040c5a072400400070901c1305003e5900315001d0a070026100505000281c0381500c966411601580041851030003071805021000000e6002c1c01c01140c2460840320300120410f8a020007889400c0102c0c1841042c00f4803910303010689071502c0002c4140c2410603040f84c0c0c034106842030741e2041e01070f500d624102c4d100c4003180501510b0b50074107450542c002e910503201d01c0d400200c1e00210342d42d80d81e5400581c40d070b41040303641c0041c50024000640740c0d0f40b040f2020f0300d200 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 978249910 1250 978248660 978248671
    0x90109020702150f0c0307050a020a0f0e161e0806040609090206031b0f04090519111b031326070501020d120f050c2d07231504050105 59
    0x14418060480941c541d43c004400800810084aa450030365280401483c0501d42000e515844040385503010041c0020780700c54a54000c0b41c03140c815503907801100c8980440f50140c0c4c94941000d42c04150100262195080c2c1c0c424641003295144034900040d00003440c002d003480b400a05c102082c0011414a80300300030217003655540030707c40c01c3c1c03498002c08c038284130103883d10007010001081940144070f0201035508190f0181085980e841e1b0f211140000b410cc2980c140030300c1612b40c00c181118221510425050009420149007006040d40c00c041d00341c2c8006034100c2c010701040045a01c50186002c0d0100604500284d884180010b0b052140e94100c00551810345580282c0342448940c0c0c0003d0195141005450000c003078251100d4140080c1015858a04c070403400d180070710001d071450801403c1742c001206900c034004a95645449d440280a000100f0f200c8800c1201c0c90116107401c0c400703020f400118410440c3d01c1c2c4a40c80603480d100307081c4c030f0410100c40a6402c0c40304100e400e020316900030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 978251160 1250 978249910 978249929
    0x2010e0621011a07110a050a0b031005030a0309141302130f0b28050c1209090a27020a0807091e0603110d0204090611031e040f060522110901 62
    0x3c110640200141e8400c131a800740445444c801960311503544c07000c20101505010703141110385942c80680000d00c0d0010364188119920095012903a800d000070382600b07480e0169074810095140000e41150440c3c42121682c2103a042e18a0403210001800104244003001140c0d0441c06c0c82c10410032014801d540024400003800c00a801c1490411250f10844084204491006401c1707240305035624425400506100d00820100311888401c40011706090207050b2201c0301c0e540d5405401030200c4140d04810300c039280349600c038114100c001e03500c6003a090344054009110f0320307120780c4c00c1440c11465a0046803da511440c82030300d01c2129400c00c07608040d21b10300501216045a641402031030181742c000c1e0207617821058440965803150401c4110940104042080207038441c130707000307140d4400c5074103140c00400031013200000c102102d007462040b5041041c0d01c190181681d1800003409000d0300b81501081c81e01190180310b00c104c008001c0183c403c03030341241b1610041080c0642d95030141e0104005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 978252410 1250 978251160 978251189
    0x50d1701051e01021e24100614070b09011d1203070305040204060e09060a060b0c0a060e01141006021605061903021606020408061513020702010e062101 67
    0x10b495445050030b210986840190001c0c8803040101e28040c3c00d103c4202e50608082041105010085298001d80c581c681540410120500b06c081003100141c0340400030080404080001d030740b01d901815485500f0032100d51070300815407140d2245e0034042c0c9020000c1d942d11019030f601c094041400701d801803195405003d104402c010242594080140584180364076000050b0071903071a030388020042c203100030300ba841c02c1c1828401980e45039000c4941c002a2868490040742881000c025182c00480701001030080d80c103555a51000742c0140c0c1446903c070f40d02c851468070110441c3d03801b01d10401290071100b600c189401c600034504009140d00041c0c031440004280003541701d42044849903005441100e00700715080b403003100244a1a026048140c582c20000010000d19400030022103544004452954498024402e15030146100040e03000581046a00c206c0762290003030003400d40141085011240c0030b500ac50707520780c0a03605244e4000f21105a034850703200700c850414058a692459404c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 978253660 1250 978252410 978252419
    0x2301150e06100c0215030a050709060905060a1d10050a080a1404080c070e0a1e0b030d081b03010608190c09180b060a0c0c0e06130b1309050d1701 64
    0x1030b401858840400c0000300d0300000b03648600c0710003400c0c0641c0409940c0c0d280340098150005060036a050710000d111000b00007401446036801200f51040180f03410b00c4c003460140d0654102c02d200200001d80850030398042c5180c0d0307d04d401c40c3c240420039200c0a5480c05950310003007140b0703801051516024a00107000c42d80501c4a071640340d001c3d500c008100c0c1c0da000ea00b42468508031983c2e0102102001070010860781002a0f040f541340c029801004d41d060b80080c010200079120000300c05501a03118945e6526101c0c070641c040d40e040291250341c5603c04540c0944584035034404d030000c102040300c440910020451580108a00542c0b45008000c024072030b010083c48400c003449000b12a19501400e80c0150606900000c8041c0c0014100c1e6a903200d0007201601d003a064000644c0e101400d21000265042d483d20854440e00c07000348107108180019110034006c02161192642109002e00d21001c0e811017841010200c0b80100010550049503070300c0148030010b85528040c141411000400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 978254910 1250 978253660 978253669
    0x60603061324020d09120909090803150a0f09020a170f01032414340c030c020904110301050c1c05040212060c0703120c05162301150e06 60
    0x1104142c41c101221201c28200030b002c001e4040c4241d0b080e142403a000510302040748000251a420b882c5888901e241c0e955954070204840e083c5030b001e08000c00400006100001a040200005200400c000e54164036201001800c1805400c00c0b15682d60019121003000d80111030035400c150700219641d00343c584030501c48010501880024520702c0f406a2a0f1054141d24000300c031440c642410410086180329201c0c080c0b228123031598542a2100004085144800c20007c0b140103542010150b0528131003908440c079490851054040041303000040d80103079a01016280542d0140d110070850710404020942100c001910a402ca6201008001c002c28810701c1d8110315418160000a001e6440d4000714804000c10401e80d00d85018240c200650f910301c0102034440c45029030b480e4940c6940070711490044864059400002c107000f03001c842c1890380c24007018010544182070340864800041d450124545012000000a07511030300c00401d1070a00b40011002001c0b103031900c440600b461400f01c0d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 978256160 1250 978254910 978254933
    0xa1d0d12030506151206040b0a0f0b0703030f0c05070515090a030e03070807030b0a05090c090414070b0f04090f06050a0509100e040803070f081006031a04020406020606030613 77
    0x40c061549610005500366521000b1149a83c0c0440d141c40c0d0b2005242d80061032440103d41540c81140341c608190711505103508510140c6000302c208100b107134109120001c440c0c204150403010981c503680c2002c5102d0950007100c003044102e854031501c5150500d4200d040c140403103904004509110100182c2d00710014805c0521601803c00030624860729002c241071241303d41291903075205a1400204105803090783c1c2e0301c00d002540c020042921142d4041e910b5002c45c00300c0c41e40c01000741e8040f41c040380d012900b511300e01d1405400c4555180e690f00461400d07401c03001e0700c0e920314407003c1410403613000c050041038611304c3c035010204001030400002980003c110700840d40034004a00000766690500c01449010b48814015800700d480d2034a00f00d5079580c0112400d10009156140f400a0103000b2051180103038802984011130b507081180031030040908200e050b0316803407c26802143c41d261840100040e0040d03034003410091406005261a100c00a0208050b00c02d9601c40390300400c0074207804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 978257410 1250 978256160 978256193
    0xd0507080a0504033c0801170705060a0e0f040e0609010e070e0a0b150d06260a0305180a081006170715050403020414010302030d050c0703170408030a1d0d 68
    0x2200003101818520320ba480d0b5020b140404003a00401c217900940000120f4100d900c0d000c06480c0b0f00e00303406c40c0c41761540e601d0320074650401d2050181031002c0707014840c2c000042001502607542c1e8540030b0001400d95490108031806500410b040c4441441c003800b0381440301640b00f00a01038549401284c0300500710090158810980d5800503c186d0755a00401410701041501c9841d11080d00c1903086c40185080c2c85080803200d22000448400300d40d4201d41040070140703801400341e001c000d46090758946d20003c2e4007040c41041c10703103185082e5036842224002e041c081004003900c5109001c0b4004079000c82c2c114503000307158001f0368138010000241c140e040d912a03540140300c0300140b0809440740e000700d0b00001e40c4982010b901002e03000700359503258101c0e4022400c9a0b40080f81990a995510444a0701c0300b05411241041c0081050140c07012110700980b80d84031b1070315075180c20203802e58102c5a102e000280c100e00381d8075000f400d0f070001120742d0601220440b200300203a40c1d1702d042c9a48110f28 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 978258660 1250 978257410 978257447
    0x6030c010801140402071a0604060e070f080406180b06090703110a270602030702010e04110909060a05030118120f09170c03010c0e0a090216030c050a02060d0507080a050403 76
    0x56101080c0c6585d0196400710354007070740c02141031502e5004011064004c44082e0b02842c60030358001000c00001254502801d090740721040c0039a4030500031a00448001d1040d150507441d540d01c55508541041c0944034980100100111030901c007041021452020f0880707410142800c480e12070000101c01142c0c1c4024050070800d404508940d1020421170940000300480e0902007000a08503030040000c080d29031007666544e031301c10340703013401c11080390014aa8810010003d001140082c1410251203821081c010908045566104000303401c8d0790b48010700d88e503103c031082c14982c00c00c05070a249618228090614004c0340141d0900207210011510800810b20300c3c42417000303203042091010180856028000f800111600c040c09440b1410060740c6074090325a0481c00900e0400c00d2096954000c4262040c501c000034a44048403040300c40c410550b442d0041000700030042c2d58160051528004201001c5185d1500078006003580c00000c1c20480194101010070000991001441e01c01c0a000318 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 978259910 1250 978258660 978258689
    0xf0906060a180806040f020103050f01080d050c150c0408300a0e0d0c1a3f040b060103050a0b0a06030e0a0c08070807170c0f121c0806030c010801 64
    0x414030140300c00e040d4083c410303d00415050005001d101c8007001c0b000c03070003030701c003408140c03502001c001e03c0341d00c24840c01c04030741c01031007103941c000703104800800010031450110f4001d2103245030360198202003651514008403002408200001c0180401075228006082c2614000c82802c052002c50300c1a164070300184200065100c10103015140341d814103480030b07210310825246840c1441c9010194090b4201441580841c0c81000301110f040719000441180c80c5410016001c0c000c550003a0782c103a0401804007501100104d014501035058402d038010314144180b070620750000342c02c61390054524030169061005072502e80d1200e9040c402180c0b000d2600040b10881e50391098148840c0d0040140490080038000441d0340c1e0005120060b0340c0304100751000d80f13607140404c00301c0d2401048144025000301405034624038110604c0ca60819018100083d0b01030401c82040c2000c0b00d4102c50050031081965114405520602090f80601c00381c0042c01180385540011740442030502c24204082c1998 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 978261160 1250 978259910 978259937
    0x130e07181d0402120f0d120911060d0212070c48090c03050f060a03050703060b01140705010905060f0108030f070206280f020307120e010c02060301090207020f0906060a 74
    0xe01d4602d6461131680580340780356210350545450700c511841e8a00040d05d095200e0a03251610f04c00d00b03140550010f8002d802c50112010b202060b00259a81c103000f540c244088003100810080701841002e650341e40d03107801c0c0c03c18548102c10900c050703070b0500d1610410700c00401181c5488080d4000a080a100c40795110700d9080945e1191041c1d00034409150800841102054140e00014011105948a403849954a8091020105107840050619400900c0400c00722701310744d01512251006143c01c03414240246100000c0d9403020408a42c141e554500c18030070300c04284a4a0f4010341d0000316040c40794544080700d692401a1000c052220000140c46800c55a60808035215119030901203408440480d06204580b00650741203c04035295241500007540b001c02281c021560112420600501112080b143c0011410086042c030840300044405a602d030005107000b080b2600015954601500c1800209044a01c809009030180c03414040d150b0b440c80191003404c1543c2c5030001e1706520b42c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 978262410 1250 978261160 978261169
    0x1120b011d010531090203061305060c07030207050d0308150a0312050c01090609050610080303060604060c0f020901140a0602150114060d05070e010f0c05060c03070302130e07181d0402 81
    0x2c141180a10340d24803a00d1145849284d0003442c0118002c0741608c9855865502c800c2c05810034031001083c54100c4000030b814601020054004079000748111240349440c0ca0100f4114030003604140c01007042c3c8410040c10864512202040c0790051354a002c1e070034619510887d01c00868000341c018401d000c03c0d140c01200095000100f240d80088040c00202c00c0703818202c0d00c0d248156034401c411000c081020541c2000081120b000d260302410541c5010301c4d103c4111400c07040a0801c8411f465000c843e00c5c05a503403e200903000c0c0c80c551750500d10b503c100300108096007005600980035500001040c1c80060380d42c911903030444d00c0880713010b41c40303203ca540000c80d244140003030a60700610f00001d000040f0b90001c114034010f41d003030b22403410100c2d00500640b5004594480100181d20031000641c402d07500c2800f440d003043c0d0740d041c003504100c107805500f81c00050315002401c403000c02c0d20802c0070990707201002c400e404206500301e10a0504144c0c40c507540d010036404141c0d03c11419808039085498 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 978263660 1250 978262410 978262459
    0x1c0b010f0c170c0106030f02010e031b040f1b030e070609062003070c0611010f050f070f12180510110316020c041a010806030c03030a1407060501120b011d0105 70
    0xf1060080007055228a4485400e03803100c4000da0024141078078114142c03d00182444165505101d03401c954400c030030411002d03111040c0310160154603000b81c0040d14a0094000310494801d4901117492030425031528901142a03010030b040212079902001740036041f190728651384081c2c0642900a040320141d00d890362240c00340c0200401011308000076a6580b024032404141c043d44001d01c09010b444030110144c078400e50310020f1000131100811460307805a030880b10500181c3c181000b41c410740040030812a03071840500e400340004007a000c0100b05051011044654882c40104180d03895452000740d80d000050140220031881c010350403265000700003c2801520040c000e020007101c809852120a61026900780884c01c1180410032031f1034042840401020060021400d0881c855000c40b50320030303c051810031444040140c2004114907000d918080c0101c0c040710743c00c402291800c8401000d0583c008942803070320320000010f83e2008106da60440d5011205055003480528220511a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 978264910 1250 978263660 978263677
    0x1a010510031a060a050a0908060c0f0c0c1c0c092f0408060109060602010510030206031b0702030610060f0206100e27012306030a06020318031c0b010f0c17 68
    0x88007245104c00700da800380080c003080b00a0341e80c40d00d01c2566a11070542d949019902618800421311040c224807a010010305201100381085810317501d0760030080303480c0542d02409009200f642d420040203000c441010100100b103054410010420822407040349960080540c0d80c0402e421411442d101622005540c090840c00c0146c824650b503450030350008081d0341c824800035500781720005d40e441d1407804688040300e401030a4145155506022468414560001c1d08100c100500800b000350f1001c02104d48100d01403600100c0307890814502030160481e0105400031907002401300001c0200c5800c1d1002118010200045107403038100b026008843c580a81c009a440d0080901c12140b00540000803000e000c52461040c45800106020038180e04880c2d464044e8800c008410004c1c000382c0c01580d00040305498009068030000b51a42558040c0001c181d10506440b10f103040b01059201c1c959400109003811000107581910240c4041c003006006864204500000301c2c020704260300f1215000c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 978266160 1250 978264910 978264919
    0x90402070f0b13030914011d0a0815041b0b070201030b060c010f27030819090b100e160804200a0315050703052404020d11071a010510031a 61
    0x14034011a09000003c5100d506400160909134001900307030f0800c1540e0701c10041a5074a8442450542c2080641044c0300350043c1c01000008000410103000d208100300300410035900000c40c1800e080c0065011151044180400c03000407040007018014802c4600072503080c00c01003541d00c1c1d41400200b1501545916180c0d95003003220340e664849541d4052002840303082a03c1c1081c10396014006004004010000c01044418000c01d07251b40c1800b00424a034400104042021000c40d80c590b034035a0000d503a0044140b0b50414180710300340601c040030fa40300c00035218007000389036120b00040c010040600060500340480c5c0c15240040c2814100307600b40c0d4009841c000c4040d03038910b002d0b810040c291507020b044500c0d0002142e00c06100b80500e0b0300a40b000f800c0e401038000400b50500c0340328445040240d2140d420001a006180640951000c404921043c6900c07142e0a08024902c8640003005070f00c0c50740c17800d005005566a0068000d140320051400040341420080c90b1a070322900700c40701e941e10 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 978267410 1250 978266160 978266183
    0x9020408100c090506040321050a0c030810080106061d011e0c0218070f020f0316080a21020304020111060c1e04080304080a1505100306050c0d05090106080c0a0506090402070f 77
    0xa1088c1510b0311712007101a0906002010b500880c116041d01400440c48005920402d0050200e48101907594000c458030f0185032846540d11354031400c50b10340e40e0241c1701044103030b03490413810040081562100032081c2400408202c0e801d107250210070100f5589018400340d685d440381552120314501e0220072040c440001103090031200503100000b41222180148258016600d4040001c000c0c0d40d81d08400025101400000d680c44001980003c0844020030a420b03520034a80804603a41c1110200540c070010ba03a4202800010555018208031505581c415800c3c485140c06070011110518603864461000007520f0804020fa0b10540c0e210818a02c000f0401181421021404a5440d0720075848403290182d0304119034103442080720f82c991942c101900820218196401c41d6502a2441540b94540180384050b07401320b54042c0c40c140c105a641d04020701c40c90104101d1803a040704100c031406080f03490200000e1003803088034605800790303402060030700070003c01e9041d030b01c03800c0d602c210701400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 978268660 1250 978267410 978267413
    0xf09040608010f11070521250213200904110403050706180e0a0c0905030d080103060c110714010c0206070609050705010806031c090b0412050709020408100c0905060403 74
    0x1900d59444400d00c00707403800d00c4c200d40c2e0070102c400700d4017855484409084c2c0d100010326524000307101040a941080300800c20b03a0302c0c4000070300103446119074000c10050001464018403103004155104418414038100040c641803e2900c0440b40f0700500c0e50740e0703d554001c2c1c00086005031040200400c0051070108010040100205011080d26125622221091050480012012001c0c031402803c0e500c00408034944130308039001508103c510781030070a00300b65184082450030781004601c0303000a425070010300030007203a800354500200844c903040c030103111400c64143d200e01503440340c00e07040e026502c0c02c00107590051030040f01d0190010151600c0c1d0440d410034402502c90380c00112040d004e82440450950b0113803a645014500240091440074010030880c1540620308203544103210700701100095400e5040020701c082c3c005581c00503100201c511300f070744ca00803941e001340c2030f0700b401817105005001001400101c10501d10b0004215014000e07410f484400203070300f180c0e03040b0100050200 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 978269910 1250 978268660 978268663
    0xc100203160504060504060c0602070f0f0209240108180150180706050702090105040e0303040206030a06050a09060519032003100e0a0311030c120f09040608 69
    0x14401d14240004208032801e1080440e1640300c1c41c001c80700450001c1c0401d004440c42a00c200d665507114040c01841c2039500d442c1c015451942c0c180454000007007100c43c07030031410a449102c1c0c01483d0114007040d120407160a00300c109000d607045c0c5040118100000c3e0a019210a01d512081d03100340080010290a00840028036032503210505194800380c0d0300d01c1d01d81c414a0000c02c3c3c292825600d100200c0038000880008800604200c2100041d042100901e0409116200003000d10b0740f00d283d44c80502d44148082103005901c030501c9140707407007031086100a003c01102c0e44903a0495000ba81d80c0d582c5001c800042c03400e5041541c200b602d01c8000b14400040e40c1c0048191035040b01c00c0601800d80034907151806d240d81c0002012100410b945826021091300e410200c0300c001001d0780c03602d00360601d003542150b0300c01050120903480003044006168110b1444458032003080051843e00700d80701ca0380750f075810401142c4c40c00c0c0c0100040341082d0011078016a108134000070400d0010b1903459018a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 978271160 1250 978269910 978269917
    0x12070b07050109062a0f200a1505010f05090c040303031104080a1112030313061104080316022b030828140a0c120203040c2d091a0f060c1002 62
    0x81603408030790449220b05134001d000c040d80700e1b261039862902c082a50001c0e000c04155002004410f031143c10581400251500f035110000d2421070400107066250120b805559000c42d03100d01d0245030305400303000b6240e0001c82114240ca415060200d440e4440d41c454141030b12441c0c1c4001c0c81401648085070420455005548070020112076040e510143d03c50a1601c078070040d20701c40c1150041d02001e00014003103030056030050311244501e83c10240d488132024110341c412000e030080720485624600c210f2170300044410308229201304e50581c1611029180701c83c000c00040c05420300c41d8010004122410340d8103c6104482c40310b42a807140300040301079001506804008030030307218641d000500800780600c241ca8414900f0b5403618101c8000c5a003410003036202401c02c0d69010742d030303090108203800705010340c11060b0307500350440b1011440d0800084074803c890b0041c003e42c41c103061180d0420104941c0703100c01e4072800c52b640c0c601c00f14268000780f0180300780c0c041039016001d4243c5180398601c02d68050b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 978272410 1250 978271160 978271211
    0x1506040305010e0c120c0d032601031a04021005070501200306012d03090501140c04180c050315011e050c07050603040302210c011407020c12070b0705010906 69
    0x2204c0c03550f40100204110300003c2c840034031044d40046024822854148550810b0034028248450901c040c1c06082d03440040403400540c42100d0ba5004008100c03101c5008d2051002120343d001c058103080e400034554030050ba00d20740c208240400c0000921101303511070311001c1d217505d1388200c81c501d070b0840501c103a0700101c1d0224085228241c007950f1003054008107045404c64001d0000a1035548441580184506403040d2090741d40e600c004901c0c00ea411049602419110589503225480e003200c5812841014509a140a04003a0350184c866004410b803900103ca6004080701c01f008400100c6000f4201450400f0290300e400786c0c111041d40242c0280065000c0f40309035442e043e10340c0c00340b240c180700503035008005a00040071a41c0d02c0180340d075800190390350f01c449030745005c074041300480c255104241c2e4120580050414030054940401051003120400c2e540394203002c3e00c110070241c40d03d6551007840c4003428000743c40ea0812034290711041c4002e6000108200d1910b00803000c00166108040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 978273660 1250 978272410 978272413
    0x19080c090a090b0f030a0b0a321b0c03030105060d0207020a270209100e0d0c06050315041b140706050c040e31140a0501050a0c1d091506040305010e 65
    0x13500341c02c010503950540358000c3c04014464441da900203000749094000c0c4d10301c003210b1041084011074001c202c0c9042d03104030100a400390500202054007001808400c0c5181102000350300c049450101c00d0340d0444008440554a038001c00034400040d109142e0025800340311032f00701003101801b202455140d0060801801a078510301c0c02000c04910621000c030307a0181c1c5c0101200e007020b10070100e8444482000d03010300d84100030f0ba80c0d06014900b440c0c020f00e0101e140070040120a201517064010b03e03c001f02c90521503405259801d200c0d0340b200c00000800c00c03600d00c0f8810340b201e031003808590b119580710204208a140024008070550401d0080b1007410740f0a8011900d11013000d0707078001c0380403c0d0043c01c0200005100316003a080c5c4c0e201800300c0d001007400b80902074032081800220005802400003181d03500e48002c10b002200c007030320320244c14814042c81c56900c03c5424101140003003002d469854994440d0b01c01008c2c0c289140c1c0300d440e40010000360106c1000300640040c00501020030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 978274910 1250 978273660 978273679
    0x70f0507080c0d110705060403080f040e04030509030615090a0504080405060c010b040e0114010b0a0c1a07080106090612020d020c0109030f02010b06180904060e030a0c1719080c090a090b 82
    0x1492a520f45c091489044d620040a0000740041420030380201010140040368603d450f0b680e14a044880404903800c1e004110042104821800e092100c141e010282222080300c0c003209000044104a0140102425607030b41ca00040c00c100742c0500b04c8000d0040285400d4032840700f54030050107061600002c5e0b00580c103254210510b6041401440c10044142c4200720380c680c2040540c6a040e080000d41008000c6801d0071800440e03000b45030444d220040a400c1c504078179041c1005400800103900c11410060500c8080200b90f6020481010703036551920050390f580c04009007900607008a081c10300c11946410340ca1800c05801020010f5150903a0300203104c0302425600700302090080329046104c1c10038000c4034144900d0700641e07180c0d029204100002d11440940d483c0361441d003201100001003050054402c060002040c00b141d46030f40000d1209140c1950201150b05080345071280e0360600000e000454081c0f04c0700c50585000c1c0b0000707044003179004d680b0721501c4c003d421040c1c00c01e0300645051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 978276160 1250 978274910 978274937
    0xa0e03060c041a2b060f06030209030d0906211113031a070e0105070318030506011a0304150903121104090b0d03140a030b041e05100608070f0507080c0d 67
    0x2401d07149010640100700d10300804140810b40380c2c2014204c2e140c011581e4a9000c13500800300c2519601900030750303a0060319200303102d050500e00355604c441442030009204040040c503030701502c040b08603d020388448110102408a20340a4074003aa512038407000049000050400240e2402c8110f0b8002c440001c2242a40c00744000c038038409070f40182c001181c000301014254002d20003441e0251203031424400d00e440f592620012001581c00031112a088640108100c1e01c8070800983d4214040900c6807443c02d02d5610014039145c400300e503030800ba440d480e01c1e405150242c1410844000344040a010b1300760303035095281d91680140900c141c6a032901666000c40c0c00d00c2801901d420b9410b0b222005a00318070b06e04000560410600360007010703110811b02c00b0703540391130280070701c204644845c0e59800070032458444140ca0000344061340034011030304100201d980c001641a003280d8542011580c5034951001240c003445801000b0f4205540000c154091000004081e8040c3c801690b9020b90032495 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 978277410 1250 978276160 978276209
    0x1101090f0f0b1608010e0c0405100e010201060618030b09070302150a1e1d060f070c080d0507050303040b0a1b020c0f10050409050903090a030f1109040f03050a0e03060c04 75
    0x40359600004c034594014020700740c1e540320030741d003081c202842c4c2410b055445d400194098a03c080c0200020b0707001c235005001c1d580900441014145504041001c440c1d0200c0c0d2a060b01038a2001804030244030700841c08066050261502940e0003402e5002c041a8948045e03455034000c550a000094904070300305280c00c05210481c200034082d03a5004084545070960320304a001401c0380a80c004010002180100e210701d00400c0041d1091501c0c28809140403100d40c14076282d80351030002c0c003504222003400541d0200840b5480b50f4400b01641207516070000c001d004004600402c0e8900c0d01c40c480e0940741c0380d00040e5030303018810b048942500c62031f101e0b4103210782440c0e0285982c0c003040c4280002d114000b000d80117294022a40412241450300c10f00020f680791405070b1040d0380d6110074105000c01d04c91100c8021180c0c450650342e10084c0d040036950103c0000881c0070240c00c100001c200885210311851041e8940f041c010304039001810102d0030a5090740c441c1c0b059660602500e610700302400003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 978278660 1250 978277410 978277441
    0xc05060f0c161a0720010603050d0807090b040b0706242c0a0507080a0207030801030b0a0b0301060b0406020c0409051b06250317060d02011101090f0f0b 67
    0x101c150780c460410009201044604030220011610703041646681c3c00c03031800d014400d9200d8621aa11203100c0c02d020080e00c0f0100c8010700040e2072503410854180045140001c004402d01c1a61405666a40c0c500e035044900c20080d422460032a41c0005000810b0b0318403801905423140602020090031140301464010003408540704040400359a4040110980c180b00300710030540b14001c03071240c007425042030340c0366004103c40d034400880e92407060128407071b40310801aa02065003e021460a0526100a030400348144001041006500c000404503180b40e04503009030300e0098000d020341c80c0c4032003000390150005d000c0c840052080044920342d5141c14001c039088150080c001c0d060102003031780ca04003451613046c0c0300341d04041d040261000004010000c5c402800d030499610038160014600203003441c20070741c000c00c84101c208050200c00d641e549604103186909081c10700e038000e40c000c4402d025111407140500459124400314092100f607070712002060303100e414400e240d9030f51a080041c00c4007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 978279910 1250 978278660 978278671
    0x2120a0e2803150902060309062a030115030f0218040f02070b0406091704230a24090801090803190203040302060c0703090515070b150f0607140105070c05060f 70
    0x90711074801c0021440d650165040385000302c9002c55441a00d80221714180e20980d0204501c6e0701150401c42c0300c103540c3e08103510b603281d40707400d000c240f000e0149400a103001c18010140559410328149404501951116181d51286041551600e102d80303c45109030309441c14050040341005175184114000f442110b070707015800602c011580d11180c54100c01003140190846900e461001c40800200c2c0c018040d0000b41a0380800040d1844d800c0e0074414007400291341a401000351502c00d211070b0a1807000701c109910025409a21091242411500e03040b41e84e02013111540303030406000a0001550085104240c4504204001d51070618401c1c100d100440700500181c120501040446075118010288240a80703018042a0b1710760000403000380324000020460700000400340f0401805003003050b4000f09841c10034070b207040050b01107182c502e03d1550441c4180000110030042101595100702000da0aa008000728505402b0281044000f900161601d220380c100203501040c880d00041d1061 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 978281160 1250 978279910 978279979
    0x70608090709090f0c0803040906150e0409050c040e0c0108100608070513050a0603020c0618210409020a080105011e0914040207171908010b041502120a0e 68
    0xa4900705441008148200c01110302d13100482004021541d1022810040c2041d10041d655840c5409100780403580c1a0340466140b456000e0030080c090380200410f590490161004642c1090601d0102c0c1481088180160f04c546040314103541c0520014031228010400c3e01c0341071080c0c0707840c020380081041c01e208540009020031300040040e44298064202d601e8210769031005035440307600003100c100c120b80040000076404100e030030806d501004900d41082807815024410800f261200d0340359504860940b0440e045103082c400c84920bd2821a002800c0d0310800319105e02c030448004000ca00c080c23082d54000341004c0f050014188054075a00326203d8545c4501007058036111103400750b80e284100c0164881da090040501040c0700340c070307034182c118100118150744062814804007803810b507445481c204910350006010b070600f00e8007107070181d030085030304110b240350607540480c070342425104084003410002c1422081c1c40c0c0c02500d84861800c041390304a210905a500d8540302000310f80b5000c00d407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 978282410 1250 978281160 978281173
    0x10521160207030c0312020a0c080105270c010e0102030c0a061a01080c1c02040506070515150303040b03130c080c0307060f02030d090503090d08040f0e010303050a0f020c0907020f07060809 83
    0x194254101c2e001083d150b00541d020011252100c001564192b44007a901e40d445504110804503a18104900500d1205401e150740b08850281c941e01c09200c0c04003814000d1802050a05a0082050795104090704040f81c6011040d0316100002d0460781080841d206060901c48880e580902d0040d4400c40c3c801c0000d5050071490107900e1020700300008560240d43e820400401e0a4442500401e12603010314020100031070702000102c56034a0007404001c860085118036000d40d5804000c44045920191f0583d0312500d582e09080341031180703000001d251240420f00003642c03110201d03080e0500c0300d0490944504941d60002501c81e041d20091180040c5c20401c0160300d5080a036000880d924004d5017240d05058840c0042554081c0c03a030020346020070302203410030043c0385c0c0b0040c240280150a02c0b0000342e51441e60094414002d00d0302580c24040f407031a0617051680300b0400b61603030100c018214005800c218030040e440310003500241546004501010811034010000540101c00d41d2005001c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 978283660 1250 978282410 978282413
    0xc05090f090a1220060f10120206070204110c150c12040b040c03060c11070b070c031e060203010e0a0f0506060d1e050c19031404020f010521160207030c03 68
    0x30000c9005031004180984203459446003138401c51603c00d0a80c0701d03c002d04031400c1201000c22010001041c08481a100d144144405803d540c1444078140c1e054a02039150440352002034007506941c014850f40c01c0d03020a10040c181c80000718882c0400c2005c44080441d02c8076102c0703621a04c40c44080c4a031805168000c2000070b0454806541c0c810700801c4111521a1241d84040039a80704e45100f00004041c0c00030940080800d0003250010000e00c0302091500c1900e9807944a40c410324072001d040300d1903401d010081050103c1815140e42d80c003c03400c65a0b980c54480c04a108082034902103c403501c0c007944000d250342c45102d200e0050b08020300301d5050445103105640030700030308a000c6c4041000c0440d07200300750b2050301a05000f9545030004035200c2c04a80e001d03d843e0f6400d400048100350805a0400800740030060058202d0740503107450f012100300a00585540c414805155860044c9036200d600041200310858003c28501d0507440041c482000700b01d0343c60013a07000140506034590401c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 978284910 1250 978283660 978283673
    0x4180e0a0b041b14101d0f0d1403030a0b0d02010c14240703050f010609090213150801031209060e19051c0501060906061d011b0c05090f090a 62
    0xb9442071150306020440169180750001c160202c2d8130500441080c26500b8500b07103001645140c0180c03492410b600910300c0c1d00210b01301102c100c1c5c01c80f80285110a00c02d00591150381e28040c00d1600700000742c40c181d10944696941c1c0d07200300d44206189240046900c102d01d81070103003c0c06160141e44240d5003041ca52500207010840814131a464031560250140c41c154030038150f01140c1003a01b0a0040e464102d00c041d0991310001c001c1c50010905074014030a6903000414001562001540161542e44104861000741121f8014810711140e040c08174500d1075001b4901411ba0380320388180c0c0c0c52000896000d0310b800200340549400b14143c41220305290801000c7c0c210b404500da0416880540d07150046207040c503002100c010480c003020001e03422f008090281d80024400108104100d900d022001000109030250781952040844100ba045030322885008070910080c0c43c407000060441d192a05888049204542c0030701c1900d00058041310764404010300c600401c4024044c12580351f0b4605 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 978286160 1250 978284910 978284933
    0x301050a271e090515070c170f0d020f18030c0a05010305040804170a110108041e0302010e070617090321180a0311010b030c031c0203190504180e0a 65
    0x501ca122840301000444522030007803c01072405079000d4064071140044c2c5c0e0314078000003406a000d001c00a07001a0025050142030f00b01c0d002040000ca890340c12a0b588002c20348500c000505003e400400e85009020440bc010b06c402c000310a44844541085010301d5202d003d800c980c10361006c23002c10704100e42e500903080160f11520443c3c0d6945855161303414610210f011500c0036140381d20205002040080030355140d1861402428030004e42c0c98640c0e034014007141c0200b00100000c0080d209001018000d4000b1a180307040c00c4207444880d03813104002031070b07030b07c1c1010702c01c40703510640001c9943d500e40401226941c003c42400545030382a0120101101075000d0004040c0703d5008540e903c14540a101c0423a00601c280c1c2ca541d003080400803040e00390390084d0b0310107110380c00c00c02c01c8903d42c1e5400101c01200072802c99500c040b11074812070990950060b16245100401c41880c1b060230075500000510588241e041c2d0200149051044201200c104180300c40345503200301c040401290201500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 978287410 1250 978286160 978286181
    0x7050f031f0b130603020f0103091a0c0c16050603071803050709150803091f1701030f170a02030f030406110711120109020108160e150301050a27 64
    0x4803034000c0314a9905550148007450224401c40d0340c0d042000051500c2d242c1d0598001d40d00c4014402d1a0454000481540c01050350505250740c8541181c20400503c6028010400300e61003068149415142051144d100105266450291041003d024450a07a028040d100082c21050666444540c29280d0f9155000581a010040c607800000650700700b01420162403c82c2d00400c2c5000460320031482808039410480e80ca400030301441c080c8ad02e030185828111115800400c15a0051400076607603500d094030404d5103200404000f005000c0f04020704880144100c022071000c452400c03000c42035014a511910068108101c5808403604400186030072030301070b0f03000096040b10001c810200307500c021402c0380d04411080b4007940f075140017080a8000954a4000d1001182a90000b000750b00d00401000468401c1c1003000301d814450041e9000a40b00907142d0361000071210301c2c14440b50001d02c29107100321004071021850001c8030081c0100000300b41c0c100c07604540c541c8600340291089015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 978288660 1250 978287410 978287413
    0x2060a1e0201020a0801182414040c0f140408030409050420090109050c0f04091d0705060d02030c07080c0a0501111c051515041a070b040b1308030117100e07050f03 72
    0x403561030505000c000c1c4843e40c900c0080a2349541c40c01301003492380030503801681d1041c1d02d03060310103e90641080060007040018500052940742c01140d80e4054021a00700c4200b9100102c0d02044108099222900481c01080700170902043c0c940c080b000758201e4107034075400909840040044103085d802007a0081020f2070141e05103c0916004030042c2c02503030140394280e0b04d444649d1048506050300c00040b0303110a001d010303001d0405c0b020620a205030214521130550020000e1810f00c40e90080e1040c1940c0078007419550f14814100503030700c059220040d555035107001e46094040c4e218808503807007205441001c00156070b02d018107200921004003010b03100103091481d100142e403230b0708483e01d00741040070403d034a0700c0c100211802c1000b410548410b108608110040110703010021031540554000e40242041c3c1d00e28403030400c90310103003500030a85031020002040c00380009a0300d9a064907a80c0c01c4030070900032004100b081d50300c032180b0320b021508202c07410b004604040307181e0390003000090b0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 978289910 1250 978288660 978288671
    0x608120f1312081c05091b150304110907030203090a03030b040b090c0301060314090a0605040f1406070f0215060f0a0b0f1909060203030a0b0103060302060a1e0201020a080118 77
    0x1c1000c6510b404a80048814140000b82c002c10000a000e80d1280c81100900402c02890142c031640d0b61035440b8074039810801c600c00e0350340c1c219540e280601c0504070030503c02c05441e030419142500001c846004001e110780c500c5400150300621030320a885c410050900281103c603080d49054006100101755183c0050300d4084020b000d484540704240110300b40d04400342e5a42c50080000e048034280c40101240300b510350b003441000c0100050340c40005400400c002890b071254540380d54106034a1400904281f040300408500500215101c2d11071202600c9680001200500807a100c008242245100700d506002085d0700342405c0c0c90240401d040a042020710381d89510540165400071940d9105407080000c2d420883c201c1d83c002c40036412840d04202186c5400d11201035204e00006000d1002035a03503805070400341c0c2c42508400c1c011038000c2c1141e0359072031003c5001003440f00030b50100c0041c50080902c290859105201301c2c0d80310744443da100031060342000b07894050b41b4100d8407034001072a100c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 978291160 1250 978289910 978289919
    0x915050f09070252050102160b03070912060204030309301707050705040c1e0e0d0f1a150a1809020a080a0308060103020f0d020304020a15030207060608120f13 70
    0x1c091313001c80b002040210b8010803c007960030401c0382600820304640001d803011500c500202c09820a0f0b80340344103a01c1e1240d4aa41085881c0f20056108400303000c28030000c6018003000d54010002d680c00b0f581c0320501c0740d450b850f883c1a280074180c00320841130202981c88008800c0d00023040f01040c8110742e03a25282038890b4000650360000e0f002524903403c503a204001c07518140c403800c0158180c505100194142390035581805086001e084028400071400b2813240359199900c40c42003980c090041e540303441c00e50508504a00256441419000c000c00101d00881501c0358103100c400e0700200b42c00070503410190355025000c1e40400071031616444015520040c2e0300d292001001c0c00b041c100a101940360350a0080944401034545030526204000120040c440c00d4211141400700c0500580d4940300c0340701041c100b0700d07140e102c808c901482d081820300d455030603001012210700501d4103000c0303940c45000307180d203448401b80d01c80c45400c01000460014040303100603056150304d00e9600403100b03030364 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 978292410 1250 978291160 978291253
    0x703110f0d09051e0603040b04050109050604060504050d080114100504120506070f080f0609151e0301060f0509040323040303020a120201020a0c020603100915050f090702 75
    0x2058020400315004000500413400d2030071a035100c00d55540401d41c5034090010210720f0512024201601c8104600c00260601100350000700240e68003e081b15039901d06400d1503001007205981c00c543d1406984e11210380d561094200c40c0c182d540300b02910868400c9401004544501444084c062040601002845d401000c041125850180c40500803c0c6007040000380201c0e0080e1081c401c2c80602c03800d00003d15046011a5409002561641607079182c10b0024250507241e003004a42c8a90105407004101c1001545142c1d1610240c0c003c1c41441c0d04c94200400e4144980106a0011303ca8400200401d105001d02c041100f1249022030411804c0c2c00d08a100d50301a41050340940d0050651314200210126000d817450388900c000c5040001e9424000c1216003211340c041c1c40b4080100108060100c24031102d401442c6802e001c0041d0000480b00500c08a400e10403140b0860b4404042881d40c20400c030580e215508a6001e13010102d8561030b034521800b0b03403130102403443e041d0302000d0204518 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 978293660 1250 978292410 978292423
    0x21c050a020a060e03120d060b0318072705250c06060f031502030c0702030a06020a081005030604031116090504120f0210050720061f08150606070501050106050c10060b0703110f 78
    0x29158008bc150804c0052764039080c0d142e40004003008100003002c003410105028001c044080884c0070a06403110480d01144003900180c0c0b40d400f00d521030700c1c00744090300948590211403241e9010b000d40c5a690f0078000d601d00903403002030102d41403844852802c624a50065034449948030083d801d005958010a1030301200c8001265403640c005002030740941c010122907841032095046407406330030140400d445010241c03004090100c40c40100c0102c80f001c1c817080d40040c400c0f0b6041c051541e552002280070b0901917801b038400300729440c0365542452003000700c03c2c0180b03281e800a019410303060825000600008180d02d041050800d281c030001e11340804201c0041866100030240c90815003101d01980c030422a039070390307000d540d00d100300584a0040b070011001001c0d03040c07440c5160303110301c00f10302144103e01c0024a0b55103030030b0003c80d00369006005811542c04d0322040f0b4050804418408046400ca8020743e9a1160103101c84070000b4403500700340c0c85402100044d600075501c04104d2a18100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 978294910 1250 978293660 978293671
    0xc030503040311060f0a0c0c1802091c0c2d09060503242a340215030a020d140718031e021c050a020a060e03120d060b03 53
    0x104005400c00911580800e00140c0c3c19040714228601010481d9003010307446814558014000102103410620685240c401c000b0030416901c90703401100e1301c00c650000e5000329015440783d6942c130001c4100114800d43c428100354040d029410305820030003041da4000d041941c0545c0f0b4589401019400750f1440c44d900700800c2801000f003081400e00c001c00d810030060b008050615503540c1e8142d190445102d8089030080355074601e0b084400402d40c2544a01200c000c4211a0180300240051184080c01646001141c000c134a400480c20502d4840d0707405c469903e0042c1d803042607070b5100b844941c00e010046410a503000d00042c41c00100150b03000546e0264003041e807a040341002080603a603000814648062101c48613020070904550b60b0250422048440302c0220190300408011525040d150004c0501ca0211300c500e41d1440b07290490b42d5080d0460201d005024203000015040d025043e040820907004024204030050f000d16000207800807115842240c3d1500400190310114000550162 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 978296160 1250 978294910 978294913
    0x51e0118170f0c0313151d01110a0b1b1903020d180c050f040e1203090312100303140a020604060902041508150108070e01140415180b011110090f0c0305 67
    0x1207002d05e1030160744100907442000c81c01c00352a414850140c0c03080949211132206607240c4004006a0012546014061a1506980f0078a40e00c0002d2001d816000b61003940c60320400740989103010380040881c00752742e20f884031040212009007502c9001c0d8003d0300c0180045800082d1414004280100f544c5542c1c4042d02d05014030b0000703101c142003401090341404400c2c0c2c0c3c10303c559181c91790700c0c503600c2c00d410b00c0044d803544d40480420307103249003801154081800c0325040c4010341820301011908140d01e10040300070072119000180442158420f4584161164010b080c00b5626915045c008d480d0a13441240c1c4280c1d81e500449aa900c040c902c1006850000001c1100c188408180c810480c0180c10400180d07100c50000c1019180c114a0f042c1504c24081e0103420300300e54000403a0160140120070300c0d010341d4680740400e1009807000e1080364610140310500c0340140c64001500c80080d10300034040a9009030071440c90b5844150001c40da540c0c802c0b248441c0200381034075800507400303a54104607084d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 978297410 1250 978296160 978296167
    0x15030109050a050601030203070504230d15240513060e0c07110406050907050c07091811091b07020a05090106020109140715030f18051e0118170f0c03 66
    0x400340b445543c0d130004013030030214030b581080d00000d442400349219000178400411502040d50b070780740e0415601c0c10000b522a0305507440914001050a0410040c2c0400d42c0c54020102a1001042d96030201030000c62010030780e250030001400b040149104080c900030744c807141e001a003001d40035051845199440c40c0b090303c900403490011111248040752034841c40c1030074002d002c10b0340e80c009041c0c0c00c900e00d03040103691500040725490a0210541c0102540e1740f42c02000c00001c05082c00304899a44185508403258504d070040040941094981c45168910400d0001d88120400010031030540000e0141d03050541e10340c0081c243c010240c0041005075120b40050080041ca20380b0540c6485025020f460368034104001d24111600c1c00d01c040d0201a112140350b1941102c3d94000c0c41e9402e02c000c2403091040003410100c0d520020304107543c07602c006403109807070035817418416140c1d06154000000f02040c0b454440980c0983e000001c241d4081040050012007814180104609071401c4055503d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 978298660 1250 978297410 978297421
    0x9030708060105100302070503250b0403030b012607030b0307090e0106050a080f031c060312020607021b06040302060706060803040e09100209010503060d0c080a0302100f0e0712021503010905 84
    0x641010300c113003e01410700501c68600029070200c1a620351046080c00301560005540701207041401c4004040e01c040215030901c000c0c140d154000061241003038841e110030f05e42604a002d0215286084096542e09010102d071540d4869001046aa00010202c0d00400c0d1509401011130380d1201030b40070300f6950742c44200035034104070081500911025000e040450030089441c1d85030f10030044a011680c804158107502000c10740c0c8070f18080c5810003466a4031049080300a03540e150f09440607009841514075102041e0b0f0380272440812148040c0c07409007054030319802c0c01140d800900048a10640700d010115003c4010000344c03009001c034808000b00760400f035400e9802c1400002d031003483e09004000450042c3d0300503088a0b04500180c9401142c80000d00344803980c1102ca4201c001d0600400c5200014564002101d40411800e41000c00c0351140001005088a1100081c00d0450b08003400130403c4410445221090f0f60000d422500c0420054840002d254807d03002140304c030b5510401d110 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 978299910 1250 978298660 978298669
    0xb24030105045c0903010f020a0c03051b0d08070905060a0e0d05010b150c07051225090c0306060e010801030b010b07080c060a0b010206100605031b09030708060105 72
    0xc580e40e41c56006030800b00a180c039412080109900f45040b104590364000c0210048030070580050020082c40150050502d81d2181c0368003229402d4460743c2001c541300300c1d0001d0340c403c444420710292141010340419580a0f03805421841c2031b0300b600b40c1a0901c2c2248858188038000d05d090069840300c0b400e250401c0040c01b840d02907003045010b044188007449006800c0307803d41d1034620381214a80251803c1c3e1600c0307805080c0d00043c1c0c94001c0204542000c3d2451004041d00c2c81062001c140c0c2c16090720341061040702d01c04a1400511544003550190102210b0701000e0382e00140c9100c4645501d031120502016207455030380c4000040c0e51170008005c1c2c2d660100300440f040c1e1003484c0c07032000c40d451512007944221040c002d00f072682000040301c2003048842d01c21035881d01ca41c0c1c0b0a40f041803800d24407035801020040c11aa000d4000d01000030024080300000100ba84c0681d16040c0c11234440030222426664545a000c01030202040003000e595810402c0500401401d40140789030b41c100300910 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 978301160 1250 978299910 978299921
    0x1003140901020f0a1d0a320303300103030203040609090c09061d0319020a0f032a0806040c1a090f06070f0212030706110c030a030b2403010504 63
    0x21440c60744103020509041000904948034410549851940302070440e03222402c0c910643c080315405883c209000841540c0045207050b4100308100c1961050002040e11084c1c1c0c0000074801d074146c2041101401c004040d52000040352403a00e520510300013450360342c0d12011420b800642c00b50f030011504101c1d941e40090401c01404601d8818441c0c450800390290800010f03024503418054505045114542c0c00d80050317103200f500500322034401144224a80c00900107080c203a0180120101c041548151010b03c08200c0754072400e909040c00b6911858010fa1200790500741020f10031020005508404101441c003460040c0086140c251038421039000305101880c91048040b01880314a03001ea03103029142c0c4402805540c040e03070360302c42c601e03190300c00300c50449000754007200000707809140100000c064400d076480395900304000c400c801e030302041c10b010366880380007582d1080080d100b80314420b0304803104049001c0c052004d0007802240386d1a81045001642015600c00f2004000c80d00d07141c05036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 978302410 1250 978301160 978301171
    0xa02090a09030c23150a0612080307210c03020d1b090b07050304090603030c030f020c090408090301110c0d0207050d02060703081513020d1a130c020c100314 69
    0xc10401860340d5001e0b0103e101050041c254040364146900369200b04201400d40c0444402540e5960f0300348400400b0104054414000f03007881c245021400c065240380144003207412030440c504542d01e0700c008070b50b400c6200c003410b2692480260200c49441d40c0f40204003107400d0941380544c4489000040908480040030444000b0186030791580419401060301c00550380e0b0b40f00c0482e40c500460420746d2540c131543d40101c080c5da1806034000103240c2c1c40925104014440c0e95002400078203410200c2c1d070307035507046691a07100c050040030900040850300182010b6030f0150020403900342c20700090516400807801a481c3c0d80041c44041c0040364107101c00c00140804172034640c070040140d00400d500d4046c206004051044040103d1041c07442e0545003000400c00805d18640840c0c140c0b00030002c1d41041100c041054204290080c0d900c4d41d0041181403294007a180040401c00c000000020740484c03c014010b44c003800031842c2c069255100e000e0b03040031351600c010441d10f4181540d0561303420000d14 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 978303660 1250 978302410 978302431
    0x2d01050f131412180a0e01260f030405011103090310180c0303110f0f30030a0c030c0219030f05041a0301030209060607080d0b0604050607030801080f0d090e0403031d0a0209 76
    0x4140700c1c0070030500505040d00c4c3c00d4440d88c42c1d102010041c09403015450001d80d4203070f20521141113115031000004000b80d441c01ea8401c0d01ca030b25208001c59a90254441066058011190b4a008204181d01a0b008810500313a0403031740603c1a11919200e48040d00309400081a00f0301e00601c04d0002c00601c0e80d0a50000000c10401c06d41d044255264091394a0841a042d401032451904186080c3c3d850158540b4600d0300790b590400d000e0020052814020400202c0d041402841c0c006001140030040d4100d0710040c15501511540c00312518a03804080005000007440082603d2603d102d030b5940e0014810440382e80c9504500401841f040024109803046c0000c0102c2c00c002a44c10f81510091995400081030a0b0094800604c0c940215085580c1200001c078484080c5544065918101c860745800c3d144017601d9034020503100d098022805004c10301500e410801040800d91a650050281c5400103440140e00c5901c0045107407800100c40c641e0101d42d400040d03207040d090300c64104da00c200c0d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 978304910 1250 978303660 978303679
    0xb031f140d080325080a150303300905160e060a0e07090905070206071403011511010f1104080d081e0a0b032d01050f13141218 56
    0x1000540c0208558400802006020001c101040130590641040c503410080e9030310403c68040c402022070804643c403010309410200890050008244402c0c180ca4041d03991000d203106000c80b0f1514802c542d500c546180b01c0020450000102d944180e03608544100e000e414040340c0d26503021400c1140342c021140024616041c4200344d5a072981546c121402460302401581d0b51542c20364404160354001540c80c0c3c1414100048079030701052191080e500d0351a003840c10382151401c43c03501d000c01d00814407e403100030b6440c5131550081d809201c1100c025000840c801505840c0d08003601c1050074114446c50f00881c05010044007805680d4422a1a19050600b07207030210b66050035000e803544070078015040274003042d410507464001c2c1c12500e8014003190f59100503848480040c1e01e8448152aa40d15440342144002030180551401540b11949a01168881c080e5031214800d900b501260004545101514041820b101c10a000204045000d440b214440d00702c042d04c070703154040d540c4184500c3c03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 978306160 1250 978304910 978304949
    0x10807081905010f181b0e15041517060f100605030402210f0f01020f0a030e030d0c0504050913030c0b07030e1009140f061f0b031f 58
    0x11055200c81920070500e940d480582419030040c070030f01d85509200c90a100c4c00e88264289082094405840781e04082d4000b40380c20390300484c0101701d0040101c040c0128000ca00e034005294001c2151000050001540940060364004a0721040d0f015141410390400c082200e12001e1100b01d03403040f5501d00e80e003001d14105000040f41441d41c02028184500440810255240c201401316000d502c1d040d00b440300d401c0c041b050b55890900d80c2d60501746104040b081c840b480c006000b51078010000a03005814a01204815000340918003c0c8044c54030040c403403400c2680081c068100310007290b441741a82d0b1170030a0140310091343d0052044800956503004480000c0d400780202141d1078001400079200d0b11880d108501424829500e80554801d034048400d0100607544a14641c6205104407100310350681c0500340c842c1c4600500008030381040d0005000f0000d01c2c1e414801d02038581200314031140e02c8810380c00841e00169000380041c03404c07004078215189482c6850018040b040494003101d06007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 978307410 1250 978306160 978306163
    0x206010f0302041d030a031a030c0d060509011b0903030905010e060d05060102100e03090f090c0a050f090a080d11030c120f13030f0303060e010f06030203060307270501080708 77
    0xd12000f4000e03a940c069110500b02500050441c60340142c041c0c030369409420740c00a0142134903004ca00c00c410841c40c00c0608502d800100c0c20000500a042c071200230709640c46910080200400352800c03035407203007031100280b0000400708501903240c0d00e03019250b42c110300b4000c1415186410041c103000d018220680c499a581003074401c40d104900000c0b50981c0c4000c0100d05180400e0070b0b004c0c0081c20940b00403407010021025124040081d5101d001c030710f0004080000850040c2c503015a410420070100480d03903c103030020214082c41580781c3d80381c001b4000200e482020168031800280d00548200341d85180e11860010030b01854800a5041190f5990046c2c0c480d01c800304010700c80788000401008100050081e11000700d030880c4603402c9681c0e01d080545102002e050100d00080c64000007007043e504c40c4902506841212b04034410882c102402940250304c054881a850b03c202e4400144624685942c001c81040700e82c10026032511030380040095131810780140c04603401002040c80180030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 978308660 1250 978307410 978307439
    0xf050c0a0e040809010215070302071709240f071a15010801060c030c050303090d091a041206021308100b040b03062206020f0a142b1107120f020601 65
    0xc000c80c600390313036414550060b840c1c4000c41c0300549609a4910803c0300d00b81c3c00d40d001d000c407603004201022540c04403001804182c0300703140840da4070100e00c0315400110340c41100c040b101c0c03d903124000c41c80c2c04440c8142c082543c1040030101e8842c02c88840c5455022462a080b64009004100c00c00c4210310b0b950000e0400c0c1d805001e40d20170003010003007a4050610070071600b02c6854001042c0c80d90703800c0403040582c540080c030350f140d40801ca20540000b2068003640740000360580a454081c20300b4240600b403400101d09180540c1c1564081c4107010704e04480b003c0c0039004103030000040107802191400503050320f42074214184214074040800105482c0400d0f820713800800101400a0360521942e0295520505e400151040703102180310008400f5100040580000c50b403030307007040e05041e440c08500c1c07486001e080b1000102e015114051080340303904040210a2001e40214511001c1e000f49050f0b9000306c401a144102101401003406804ca018241454010f20140495605112010f50030b40c8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 978309910 1250 978308660 978308663
    0x207020f04112703070503030a3c0201060303081509010924030303200421140d0e09090c030303040f0203010906051603290402250f050c0a0e04 63
    0x1c0d10b41240c2d81da8011580c04071400e1980404000c4200501d0420b008100080540a2800391149280c040340a140001c00d0711140b020304d0341e5031000d240c40c0ca042040d8003da5492085426101d256060032191b00708124414448a00d9000040b60791075400e00074428080a04000e450350b80080ca00086034480034521815618020760114101200c1c0b0441000824000c4940070700703140c600d60100405605810a6002a03840d21400030300d41c0d8003154000c190710441c840c0941202c5c031200c000803d031401d403030480b510600824020250400140c00c2d1828201440403070800a030040c5008a01f5140100c1400d8000d081c0e5001844460000c2003c82c1e541d20001c0d00103408a02c404082508650f402d400c076185480d4007010070f115904042c0d1054114907200b00b40780001c00d00300031072403078250035016908251408130b00355004680e5101c0d0900c0b000351300c4501d0b03000c2c0141a00880d074007080c890486240f40b6070700c10318404258000b20305010303041400707402e009441828600400c0118040798800144c10a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 978311160 1250 978309910 978309919
    0x60506041503110d05100f05180a0b030a02090a0e12070309120c0515030105130b0a060e04020d0606090302030d0203040803070b0c3a0b0603161725030207020f 70
    0x10320a443c07000b818001c0707020412059040100700b00f88013003520101d034104d60340c0040b43c6100c9901d610402c48900e00c1c00c0341a150181a40d170000c0c0e0501714507048692a03050182c01c0e41d4841800760007003101040215110350306541c45d00a0305013808400c10038003480c080114003007414100c01e0740d0000d21070706070391288084008105003000d0501440b000c40b0341c02001c000300540c40da124282407000c0c054100348246031090781181004266400179014540c0690360042c001c407841410008145d40c420411301c1302d00c2d00241c0c24801019011954401d980c003609464a50b041407619500c105450109031000f40e00864005000401c0024000800d54001503848a4071101e159140d00c818102030141e2b23074130303090303500100500c41c442e170380c0c2d584407102c1e108000040ea806e03075110134107805041d02c2015424903000f980400c00a844003540283c0c03428027246500e0001c07054600d03000807802160302560301108428980080c603590803200e0310032000c0c010003410306500700070346034000451450060046500a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 978312410 1250 978311160 978311171
    0x11190e150a140d1a09092808070506100b0f0313021c2a0b030402060a020a020916200c0d031202040f03020a050301063c08060703060506041503 63
    0x1180903220080003000c0b0904040d440320108458540604014041011820010644050380341491003100b07201e22080c00083c010030441145801510a0100b04500580400c000701c0e400a05000014120315000b0f40050681707052040400203d0506980642c5010310f0030802c2c90000a4403506483d40480460007508994000d800865206891140610181a0401409000c01c001c0c0c41c0f829800c20b903011071070190140460b010303408503616405a891840c006200003170051511138028038001207188140e80a16030300c0e6000c2800303c0419590030303104400c00d8018050150703000504007211035127200101000c8201c3e4000030f0b156550f504001d40a000d00e69603880a00d03012b105004d00d10304c282101159117540e5500007810503481e07800101d03c0342d14480d0000807249414083c6001741d8954041d0304000c1032842d2100141034491042048407048082285c00e01900418109001031603d5005001d840c546010003c08881054014500c10340060106005100c040340601040683d0760400054 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 978313660 1250 978312410 978312427
    0x31109070c06051e1e0c0c0a0b060f0402070503030403030513241416091418090106080d1e0206010e06041e05011d07020102030c1c02090411190e15 65
    0x2040d404c00b0042560f00d1500d0024082d0120210700032040c40c20800c0d107500100c0e02c03080210682d0341f0800c0d0303070204070b07500000c0b0100100709842403542e040400140071411042c03459000c10282d801503141522290070100800c802e142e014051294090318440c1c5070302c0084d1141e03841603078454801c0b1004100c08130618007400004010b500502d0110804640c07a401031400c183c2e0942203440d00e620803000569503a17800140c0e1007012401d000100801815018000610f0007401c01468008000d48515900c03000e001510704d80c06e00c00c0c0c0c0140c400ca07655080c0610820b11540340b5540b05000850210351029004110002c0560040c5800140450f00418030074003200c0c0f00c0f254038142131303c620a580d190000011300d0707130f9403032013032602d000541003644180d555041d40c168200d01040307a0809175844200600d240c2000c3c01c05c01e03001c000c282d60b1130040c244003900001c64102c07401050000381210b800220110b118201c4202d41a018415141c00300101090300c01080d50b2003000c107c80c078542c6002051a05e03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 978314910 1250 978313660 978313681
    0xc10020a0c1a0709050d0b07030207020a120c030614190b0d1a0108210d110d0510091a030c1002010b03100f0506102001060f030507031109070c0605 65
    0x1c503095041884051040e86050308952585000d40b070040224400510008650400464680c1c0454100400d14244d40d12a80e05030041d51120138100e0344000d0030705022601c203081c1203034104082d000301c0102c501c6078107520f000822034900e01c9041701544040030030010802401d10042c00a21100300c4089100000800811804a1000c3c00145480300402d80038840715808462581221002e1044403159100072a143c40000c1000614000054082022100300c00d10303a0400040c046190000078904041e0b091001c044803c145d4005400d048030107400c100307022190044440348107a0b491450303488104800002d5072400000f081d1402404401b40c044100381c001e5111102d00100581507c0c044046245030100900850a0051344145410085032007400d020764a05600070180c2c0715142551081c400c10300d40380d104004840d00c0c5d503484603004031b085800e0a02000043d40300e0030045c00c0060841c42e1038013406140e03071b441c10f001d03049020070090150fa100044c83c0c1c9254010f00006141d80f110803014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 978316160 1250 978314910 978314927
    0x13060513020906090d1e20010c03020622120201050619080c0108061807020a1209050603062e0504050a0812091011011b0e12120a090801060e0702120c10020a 69
    0x40325540c00c1d06c8080502800880d903400c0202c203180c0b11040c4d20021360064400a07959200680140e12010000340c0c03d03c01280010b07200249108989035001d89596503583c031001c0400c0410045c0d44403230512185050501e00c5500301d00c1400c50344200c850401105c00d50b01e086031018581003042102c0031520030344a907803918100800140649607641380034030000c3e40c0c0e0383c40c0301e03000c440407082105518109407041c00c4030703800d58030020240f601c0d6444004c10080100b0040a003007400c5081e00100509060b0204000595200c450304d80039100c40c90b080400c0820f0241c2d03406804a43c01806859449132010000c0741c40b507200c221007840c00c0c0070b42401e0440321825540d8814007550718103101550451202081c0b4240044296558040da20000b0280215162900580701d07107940120540405612210041c02030b120321482d16031451596001450f00759a040d5100f80c1d0050b03c08018861082c1d818042c0d80c6240203800310301440c01d0b080f402640e6951501d480403181c040e40c04203a01d0480351003003102 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 978317410 1250 978316160 978316193
    0x70206130f0507030309260307080f0c0d0f230f071505070e0901120b0601050c0a1509050c0a03080901051c0e010f0e2406010e13060513020906090d 65
    0x4583c003280c0c0300e18010700100040c2c0030710030f40014605005180803000491441810174807102860a0217410307903c1c0c10880c1c0008030327004840c40050111194030074003048004440c1c0055526503044940e01d2030054095600544c90907800309070742803d07100c0440b5000840d62390300690140755907070750b1050404100e185030503050714410b2410401800f030722036403007210041c181c1000c031150021a41e0b10754100020400000b00217204141c1400001c20a40c06440a01441c121441c20b07221200415034440d05480c648007002800c0070340e01c42c01101030140070840307030724450001d440e4a0816415520780100314040c04401e10304100000547e15040303030001a0b02071546e800d90070184060907880780c40502801d06c0008103540c2c0740c9424181036803540001107800d220481000c400521101d501d43c44809004004c01546c1880b08001e5101c041d03403900040300d640500d0055001440b54280010421003244154500721860300511408005603141d800300c403c18041201c0310b182441162074a04800d0051544 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 978318660 1250 978317410 978317413
    0x21903261b1c0804151a040606110d030c08040f050106050a080309040c02030a120f0902221b081501020a021201020705160b120406020f2a06070206130f05 68
    0x58003000200009860302e0240515000c03140a2001450032601a0800caa010307214441d10028941e0045040e40284c0214440008480c182c4240b8408a01580c4480d402403000807800b900440e04c0f40000d001c3c11495410342d00d01030003031442da4900205068005080600412070001481041200035800540108800b030a030b40209980c543d070a5440703070800c0940d9030085041000098a0900c044200d844222aa848041029401c44055001461010023980500d51350b064001d01582d6654091101001d03501d02400c0ba032424444c002c02030b5510240f5401c100790585405006180d0014010740c0c0c80035082c913102e1800100d820040385402210240070303412812202801c0c0500e0030640042c910070340a034046405103d460f000802c1c0c094950b00c1010b1090343c05000500c1803116046201c0d4205004003800740c1008001c8400704e040b07a22404980104190a0342020754282d038106091010144200140080e0319003840e000c0e4907508000c11240301c0c103141c1400340c41000318100b155001d1301e400c4030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 978319910 1250 978318660 978318697
    0x1b03050106061e0f050d0b03011e020712030b0d03030b0301200301060f140d02030402030a15020415051201090b01230c07080a0f0b061302030a050402190326 69
    0x64043d041c0c006078004090700e0f0346490a02d40885014050f09040c5081c0e40d42c80a20340040b003403c640003815465449581075484d031180440d076141d50507144591100c1d5100051b603c170340c0b51810780c0d015941001c4020605041401071b060b00da54401110200c2500f508022a0058074480001d0041416a11441d030607540680c4c82c1c4000c040e220069416144c4e26140c40020301145d88056a00d8020804940030130402000f07903050b40d201a4000d96040b40c03010b801c43e01d0000031039542c08042582009448009980803408006010090010102d4141d580c10040e181070450107800082c0581405000c03411a1031300d00e034060591144818940b03400c1440c6c8042200d01e45007041e40800e074045503086000d84501d078000728070904080b5503050700a502100c0c100c03541900c0c0d40c0e1121070035030060a050b4006880d40c2541141c1d001d0b800154071562002030000f0302c51400d071040100550303102d842c810180000050902c009400f480541000c1402c50081c80303e02511304003512402d2040c602d1810b2020101c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 978321160 1250 978319910 978319919
    0xb0a0605060c1f270302030f0a0e030c010804200609062a0d05120a060906030b0f28020d0e0319170720010605040216060608070f031b03050106 63
    0x4207540f016050040040344030791000781c504005580c05522403001541c02c0c44000059210a042c03040240d0380300e401a2810680e2000140302d02d60041210600032400010721100985401d1014602415090816036103508050711000402015244103a805c9059030f01d403200c1c0d03540d42c107040c1d418450006104613621204030744818940107804200d000390080362140314080b000080f95400c140f00569980302d04202c81c560194419000160000541c650303640c00c0031030920468004c0304050b5008046120803400c041c450b03500105002031440e010000344200e1400b00011401e8000d24601483d200582c84844205030306004003d210508180da10000540c034650914251100c5011410b5484004456240540782d81c9810811203640c0c0000b0752909480e16071425000c050340c4001c0d80240009403d548501c045001c980c4021a010181c0c00041210010000203004200190511001070107030503141ca000c00e034a4182a00004040014a0014a034002c0c2489640b0004541000007440815035a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 978322410 1250 978321160 978321163
    0x24010c03030f020a050702030f03030105060f1605120304031b030912050c120d090803251104090605180a05030405060f0f1617030f041509080c010209040c080c0301030b0a0605060c 79
    0x10749013280a03000d00f00703420000c489d012040d20b04843c0b0103001d01d8500200d440110410f031f4003100703032003483c034803040381d09004610100031141110501400c0a40e407820182405031000f02088080c2c0000400480400d00080d4420581412600344030070880d4031905d5071030010700341b2034030540c580d070020b48000150002c14000034035445c002c0c5032501c0e5000540c2d19550740d207449128004100000d8140203003880079484180340c91241c61030059016a00c014140b800040581c0e103e03000c01d440c6540c0310400e0004080802c0b181c182e0701c0001c41c0041924542c40d0380c4098484c0102e00c40d442c41900041a01c07040d140301d805c215040c40c2245030140d0342c1d40e560f980000c11b080318840700988451450400b4010038509010440303005600c41840398149a4803982da0ba03614a814554030381480d500c81010000260f00c8002501c41c14551400150712030b10f1000500c4112101e002c0380d602003020000910144401400460341502d82101288203140d40751a9060068242d550000f604042e00040d0a1100b820 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 978323660 1250 978322410 978322417
    0x222020d0606080c03010f0b090127150c0515060409120305220b15060d0f06080d02010603030909090809090702011e020903070b0c070e041a24010c03030f020a05 71
    0x35a120000c2c1901c4c1c040761000d840c0401d02403041541d603118030601004107040050600c07428149030400100101c545942c030300d003107040300c03165890541280500c4400550221920403140c3c43c500b14401c8030198403100d0f5251034030005000981c1d1400007003122900c443d0060000d842c1c01c4481501c1111184c03c0040050074111580710103c90056411440c11b56008c00600c40580c00c1801d1180c40d0b12030151004100610903243d0b540f12204000304a80c0791000d00030b50300e07440001240082e50034600901141020b0b08a1015011640b40c07034414400a0f402c0b04401055075461580012b07004050300c1c019a040c8190245541e10003a428200724045505401c0940000f00d1410703000c101452201045040e8040c0051080d4180c10064090266682000141c1401e51040c4211444c466980340726041a0b1403d5900f500c40002c00302141040350110f45000790440a200142c84c0c0e00748030818144801c0c40ea16407800e041080c1704183c5002e01d8400c0e0848414071000d00021503841c12000805800da0f071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 978324910 1250 978323660 978323669
    0xf37020303121602240a0605130f060b03090d1d0627040b061813020d061d01030309050105030702100f05100506030103050c0913060e011d0d0c0222020d06 68
    0x82d10f0001001159101241d20245100b8010f00748044426216113441a0030006010790840d941d1a403001a965551031900044a481500c0008100c01240f1502c0f0544a49822041901c8002c105001c000e044c00980c1c810003051301c4c680344906603411000384504c00b400110640e400307c80030800211000807090200400c0704410403e2407100031000c240002d40b10f800c800164480e0061004811136070107001100910b0900529141c400034181900400720b800000070f0492499039504140100d042010191a2b4002c902c1580c03025903255641c01000501e40b4018181001008408582154000c00000030080011f240500814407211060320050400310b420300118000a08000340d00d041c81d5084030b051725000006040420303c01070900880381000341027031000c0c1c0805080301b0040340091050a404034010800400d1511048480c1104a148008590750a801c00e0701c0e001200354016420291169041d540c001015030307065481211a0043c030340c0d81e21110f0000800600035507099003c8810364 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 978326160 1250 978324910 978324931
    0x901051006020a0215090a051c06050601080112020409020d060e0d09091103010b0f13031b0e06030c01440a0c051b07180504050f3702030312 62
    0x107655190480e501e00c02000044d40041101040021484505000748008803014050346015a542c0300804c0144024a03c0300d000c2107200c2c8498030801081c0e0064542021092904640c11f5042c0000c0d0395034209030a5000b842555100c4101c021900c900038500401504118200140704000f011191107480211a442c001100381c0e60102d4100a60f20480b44c482002e004410b00b542c1c201010580f081d40650066131907a5030507c0071034840302e01a030a8002862007840002d80e403000d00380c90a070307003840141c000700010b12070f50040041c0c9440005503481c0d003010929002c602d1140c0c510005080500d5661130710151001824000d070011280d4044c01c14010000d07282c6001661134070078031000c40b0145d80d15900048c0c020040e16403e00c586041c5190481c3c00002681c40c500c0d940d10717250040c0112110242600b17510390702040144001403000401d01c0c003250020f820a100c007040102514444510340380403041101e042100c103030103499102e0001a07070140880765618800e03440300c07544520403241000309 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 978327410 1250 978326160 978326191
    0x204030803070206160e150f0c0f0115140616021903110301061a0304081207090302210d110f060403021c14120403110a0c050418020a12050f0303090105 67
    0xd02c0e80100d001000032143e95070030b0641d51100070800c1112006143c7c92103440d080c058046c1c00321000004014241c030074801000049200142c40713094a1140c590b440010000071000c000764070140c50504c222002c00c40d20305a0350b0310950400007000e044018080e401c0030354000040d0a100c5200e010038241c9014414800f50740b03841504241c00d031841e41c0500b609001011340c25031591020350300550b40061140c0c0c0c0003804d0001c00e51410030030080031505140012071a000400135401c24214a002010300300c40540100380e1040d400c5a503c600c502e4440c000c00441c610a10740540090054442c68800e00301a16841d04141c14021b6492401e041c126280e020b801c88030002c6140181d183c51840c0540c400f92904000b0646050304241000410940902601c8200e0070303a214024052400810722038482403500350300f41000d000441b0b0940d1444150b8003c0007250001503a2507240042c1200d00c1c1c0750503024a03820a1600900f00b141d00b4a41c040c00d44004810300c40d2040301900050b1003036003540d1202a8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 978328660 1250 978327410 978327421
    0x110c040203160c0312090f0b01060518090702010b030118020111030c07140409320f0303150109050303070803060f01051c0c02071d040b0f0105010921060204030803070206 75
    0x100d110a46441c00c4680750301e5100d558450140d1024a0400d019043c41032042250701c05c44c0007910581e1608841050700c0c10400d900b0132076008480c41c05000d262402c0c0b070408000800e10ba0346410b1420040d4840e1191070005030b26a4070035049920903650190083c0411100f1303083c252030030004464102d0100d982d0a00c16031801c07070700100792842c05008400030440f09107405407048504081140d0030790400d440e0b1350780002003506144500418000003000a1000c455100791010ac401ca80d010070342a90400100580d0841c00081034942024203105444504081c10700140d5a69410f03622440c1c05010109049041c0041140650b1068001382c561311ba0a404110044549215042c1400000e40c106221105401c00e6a4481201c00110740100c0e620207032903040131014281c407a10150040c0b0705400400082181d03210015400044070b8140c060136504180029203074495a0194440b55130300700d190600b00421800e1000d01c0319801c044c0c1156510b85909080215a10842c0c9903009071190001041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 978329910 1250 978328660 978328669
    0x100e24061f0c0f0f0b011d070302030601090303110a060606050a1412010905063712080a08040c050904030e0102060f01030818122512030c080a03020d0c110c 69
    0x2070005203641d9030314240b180541e105180e80d5074001040d103015400c0284e41c00010f500e82200d5000e451030550a01103190303032441151500340c00501d03c0003014010b000344840380c0d130410320910517a44d16041040c3d40306075000e16285010850782c1d01416241c18900700184440e00030004200c801d0042e0341380016640c001c0040c03441c900c00d10310400c100003001c0f0010820803c00c0c0d44030301e82241004007905000f01011941150305001045041d1403081125405001d00c556007580030000d200d0031f84501160031441d1a02e1016025107402d04060100c1800010100503520544078040c040c000c210034402c1c00d25081c0181848000c240c594098441c00002c0b80b840000c4560717440c1280d9008685500c0c180821403140503014600e0040d0340c100c0303078403646800645401d00418280d0810003020440c182034111150000e00d90340e07070284034025406c00d003010100394810281d040803500314205542d01c2c0c07c136080460003031007440e01900d5914a40210302201d241d2004940e03c41f455550200c1c0d8950b1003650420 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 978331160 1250 978329910 978329959
    0x1b03060f0b0a0e01050705010b1503010504060e1b070318060806130e0a060b0f0d060203040b1311010e0f27070509031e01021605010605130c02100e2406 67
    0x2800803e0345585900c030302d50f201e034000305412449000042410740038980822181126a150740f442c540010005110a09041c4511001030011001450050800032030807a800e066010804101e8100041d084040c180a5043d074421108174000b400052a070703d0300c00030021007068544c1c41c400d043d0759949882e00f0340c09000d017099201200c0040c04584000755910b82c01070045090703483e00454020002b03e215a103c840c0e16804a00070030025a82e4541481c2c030203086000142820b048440498901c00802e203845442e001c000030a003885418402040c0000e40070260002416a0141c44080c40d071001c0d020380c4818156021004d42e00140d19159810160788502640f4442ea030598403540827441000d00000302d021500705c50310b000602d080240310680f084c2000090054459a45445040200703081010350f01c0d14016500d1401c11409080c810000e440d02010300d400161103031202640d00c84440b00f03005001d502e4010810164501b00080082190b402c82100c015108000404144605890b4540d10 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 978332410 1250 978331160 978331177
    0x2040b0d1220161409100e04020d0609050f010c36052d0406061e031b030b03010b060918071103040e010e07030902130b03011b03060f0b 60
    0x1c080c003010810301c080701c5403020b1400011500155101c940c1900105021150f00b40909440c0803c0c1c0905000d1041020443d840c02e450058084c60300700440722081c404d40100b516445400e030320243d2280c0c00015200d8901000141401d480c1503400c6041007030004081c2c040803518802440366012003c82500d500c01e22680c50302041076841101d0010881c20402684203120714800c685400c1e458101244101500c40641108030b4104d5403c040850100c20072506401d0049900380011030410780010504051119049440b0380038440d19913003540690000c905d15981c00f855240c10008140e0010b0142185542c6140254030700b500304c03101c1e801c1000031200d5140c8050310500060401e000804240c0c4c0d0000c041c1c070100705d41010491030001d014801000142a42d000000441d41002141000c901d006083c0c2d005061500d0840c1005803100e05819031560410540042c802c812280031a000d48102c0c45103c4802c03158a4018039101d4055026805440350001d0b00035000752244041c1c6814400c800c4c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 978333660 1250 978332410 978332423
    0x506040504180501240b03150f01020a050d05030115051623030406050a0305180a08030c07170403140d080a180b04051c091a0304020d05061302040b0d 66
    0x52080d814180c0109440e0228411211020062902d039a03084a4880c20281d401145130038002c0c1290001048607405012500006441d6040000d06485002c540071803150244001c5c12006805a000b4400e030502c05402c0b90542d4202110901d0040c0360f940240100041c1d00c0f0028a4003007446c0c03046007079039a0010300f0f1803581040303507a0380c50304407100070600c100c0e01403507240890100c80340f90188044c000074120754031034648901c0d000d04090b0564078010110381c0303044016800400e030300100080b0950303500c1c2c0002c0c4103135881c2c07611001d1528612513600054200d25010546407490780d04c0741c0082c4100c9004506032078500c0c0020000c1501e800003014100700180b26800400c82c044c809601000a161040c0041700f0b090250382c1d40c04031211000c460980e415081060841454107c17580c1c88054007815143c023102d041d0404056403481c160000142d03000002c0031000508545810b1105000315810a0803294035151401c0c0d0790461040d182403c0340030340e003011160360341d45c14821030505e4070303651044 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 978334910 1250 978333660 978333667
    0x30c060902060c0f060f01050906102717070801110d0203130204181b0b040902090d1a09120405210c0a2303070605040510020a0512041805010506 64
    0x111810050024204160391081e0104815801d542c41000f19a08000d0a80042d00542c501110b90b5800f00b07005a011500034aa90700030002940e071001420122000a403c042025044401e100d10549107240d880180204e40203c01007408000a400d94010341c484100311409107844e05500307800c0c3d070b9841115043d104801d1109491550300340d000b5542c011585035030140c0505040d000282030b40e69245030481660341d0303090a44140500f4410800250140a0360681464501241c50101d48500c0c45805004d50b808266024507655010054580a4101501c600900e01d184048003142600350303240b84c4c0740d00c10701c40860038054214041da400c680700140065004440c4100b940103001a024034036605005950381c48641da9503141500c00582100c001c8030030002c0e18041d40d2183c480c1e05070700a9100b42d102140411160750f2000885050f11030640b0b00d503035001c540c0d036026403814846610003041c40c0540d801c5089010408400b620494054610049040b002014003400700c420a001e916013140707041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 978336160 1250 978334910 978334913
    0x12040b07140f06100e070206040809061e0a020d110606130c030f0905030d18020a0302040917040305150a0e0a0b100b040807090c02061e0c04081608070602010207030c 73
    0x418026100300c60110075908460451803902d070801404403891240c9500c281d00500064403560700841d40408280010002402e00c2d4580d40001d0054400300791150000080c0141483c01039249032440010426660752521080180a500d80c0d981914001c0040c0d50034080d501e4a403c005103076802100040d218054500032120941e025101c100b004405068840d09024500d80300b6110380c2d00268001d0016603151120604d811064800683c018048102400b03002000350342c8014441044a504031000203643c040c41c80c01440d500d0580300c403070056810100300003040c02804980c2c19140400288030078031560f82c09019404840e0600500d100320b40c05030148000107543e4071034050304081c2d44a100c209159941c401c02c0c02e00e0780103400c00c02140e00100ba040204640310701981c040300c0c20740d00140410380707030028440d1048088040c20101e0001c0c018082101148000e048402500584091350a070034940c0102c908d0700c644c684103078441c40c81207130400502184103109a42c682641990b607a004205103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 978337410 1250 978336160 978336173
    0x6091103190204330501081b031914100e010f081b0102160f081501030506070507030c12020c0102061f230d0b1503060c090415170f12040b07 62
    0x1106045001e184072030458465811300c0b050a2808422046800907080c01c0030001002084042d086d61280c101d051101c81c003002451013a1b0354848200c0300c003100325140550350400904081c01000035a0a030050500c0314100b81d030724095003a0750307642c403010b441e50340e0b15040d464161800c0e10901e921900b00c08040301c0d40201405898200c1001441102d0f401c041001e89403c011005903c03000c0b0300d00d5002d10030082140b040c80304080c543e5000c41100c3d269803460311801d4482d41d0040c080000c00c000010b0b00b00c01c1500905032100e115804c0902200030868101004e55240480340c0384a000d445001d0005490301006c504445294450920300c904152404401215180c00306d0b1a044161808000000550300c6082101d080719006030074403052070400c401c80340660fa0040517094080c0c2c0140042150140c03010045501c0602e0680c0d0000790380080072002010809640c02900540b050181081c4007000c0000354001c02c0c1d082c10060387c01220704003a8800182c4224410381da4050713818004e04020401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 978338660 1250 978337410 978337421
    0x11040209010905150a0908030a020a080f0f030c030103201c11060f0405092a07031b0b09010f06032a0806131505040218100f0306091103190204 63
    0x10304140e8003482d01c500010704c4413042c020009114442c04a0018800e0b03074401065401084c419000c1d5103800044100213407a101c0c0704502900400d000a582c0c04800404803c41d2a0117162852643d1a400c000074014900e074401e100a40d005114003c40c6106041083c20503441c00c1d100030042081c065900046581d0f200c25058252540e040074903900c1c850f0b4444000a1100c6d10020100b17550b00c1c0e05150030007805182c05090000020390708024154500e40c22040c43d110140c540780c2090302d4810701c0c541100c901c0101030412000702c2d800304d81031042103040b0681a0003561104000e10041c564558950308441c2c5030b02c0003030441c0f00441c40c1103040540c408510100741c1403100b116034029454001d26850080165030207480548940100d200380407411500c0d89407071001070018865070801341c002504450340b0340745c01d118403c240001b007010048200b00c0da03401000402d82001600d503507403c29000030254040240c80740d05005203a4400c504d00401d40c002103005224400c1003007040b07074083c80000e01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 978339910 1250 978338660 978338677
    0x210c111b100c0219080f030408060c0d060305010e0a03031a0306180a08040602060906060405150907021023130f0303090309050d120f020c10181d010f0e04110402 71
    0x1002070203100c0582c03101144005001000711182410a280c0200342c0e00c0d05206d494410000d401c01c6c0030502004902103040c0da04181c1389080d26445003640188e4030300810302c07035000902c290302c1c01500e654203610109203a0b0b1a18040d0b03c04004201c13a1040c2c91000344413041c2c01d180d040c0c01410020380400000140840450403d00807190b204c507403580d50302c1e01980700350040d50250740241d04210340080304020750780e0700a4090303409120600f417030b0b0140400e0b4070401c07204c40c0c82000c03580008ac0401e03208010186441030201400e05c08851b522003001041094400b002802154000010784401c901c071030b098003420760088000c1e0a0401980b81140201103c00040301000416400003070036513a2003560300c0c040c6000da400e41a840800c10344c09403000103011516400e41d00485942020350399031943c01c400e1402c05080103120105600244403d050700f40d00501d89203118200b0b042500c00c0005801410390352030700c1d200902203071035010004a601c000c80740100800740344504043c1d41d0605070041e000d2075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 978341160 1250 978339910 978339917
    0x20103020c032101030606080309090a0507120203010f140a030f030c0303090b04060e0c01170c0c01060305011523031f09121e030b06070f03210c111b10 67
    0x69a64018070030481514001e4030f03611201a4014003c0c8041841000c0041240348010340c5003503001030100d01030b510010440b0981540e250001404a400780303800c1004181c0a920456072503031601e14040d07500c50759004d020b220440d40c1200c0707034842c1025046002070fa42c0140900c40b922045560490b900ad480350012403c040d107411000f40000d480c00c0c0410b000e0351244002207007414003595100d1410f00c0c4c1002050400c083c0405403090480408034036500400c600703121075a2107a92850b4180503100ca07520042041d8a001a10ba1441142c06801c200740c2d05110511180b80d00004448018100c1c1016507aa16070484511540c4a900c41c0001c0305401c0f028040100d911101510f41144000084001001281d4800e141e000e82800d403050058164529003000c010350350305440895054003c50000400410058040400741401f4030300d01001d4410982141000d00c1c05180c05034040c004d4642c82d82c0101308000e022140e2014040ba0751921103000752410348000701c0344002c00c05240208055031051 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 978342410 1250 978341160 978341167
    0x63a35030c1b1009151802040209010e0306150906150a0e01030e0a060906110406090306091109010b070c0b09090a110d110c0610081b0f0904050d0806091003020103020c03 75
    0x1680305200c0f483e50030200e51000514084c0c107040114071040440c4092402900c1c1c60301d4005522400d840070811250180c400584031f0414100685000f000e40460907894070031441000f81d00a0780421501e880032003a118002c56496040a00400040c000d007048824441402900380181c461a281090128149004166440c074140410300348281c0c0d00c0151103094960301c1d4101807002d030b03001c0c00c840c1300c4502c440b01e8a482c1c07610200504a03141400010f10403900e400d1804240701ea0740b83c0001e1101d20040c80b44d141541c0d55040030705990710503881260000c0b0b841100181c01d03035288081d62140306001d4041d002d241d85d03180110004140c1c0e0b40e50300e82a2101440081d82c98609031180308030044008d02110780d40c0c020854001d291032001025408116480c0307900384a09100460300d141c0c1c1003019034003900c0c2442d009000582c1503012804560b0010204420081171080000c0c80c0e0038941d045454050309601c410040c46031091048504000d0000960340400c0154440d600030050810281c064a06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 978343660 1250 978342410 978342457
    0x10503040f110d0803070e1e041d010e06010315051b0703020a142407020c011101021e210f01062001090305090a0b03063a35030c 57
    0x1140300603054291340c46440402085941900841c02d00614141200c10400c6010003c500c1441400004109405039803241c00c1b584c1c004103e2005960b50f035049030001c0c000504041c03400c560700c0409100a654400020f034a040744800d00703101d450b0191001d40c1400701404401d020b12035581c0d214400c01c82c214440d00901e0008113680e109640d849068031005403103060000508020b50305130382004d0640111681c0d0510400c4c0342c000039201910700013820301c0c1342e806041c4231940e802030240101800081002ca41c8104900e1380300d00081090745003da002c1100005410308044200f1000c0b10380c4000790113182c1c0184855401040c1c0c0c941020360712401300103188654078216081d80e4820f82d040780810301c089001c00e00741c82c0182c02d0101034a0082c0145085140c40030025031a030410181d910790300150300340030120398481101402c0060398812a00c401d200b0544c0740841c0100e00c1d803050302251203017402c10390403000b501c0102c0310341c0845e8645421b0305548842244a40641c80040a40c0094086003a01301 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 978344910 1250 978343660 978343669
    0x91509030c16181e0e0a080a0903211d0d1b081e0d03110403050a0c0302030d0306060c060e070807080f12090117060a0506120603010605040209010503040f11 69
    0x101540b41c0785207050301440d18507101e80304154480b220203000d041a0300c9002007094130280a1212406520124a00c00ea030200030342890081040070304241400114508000c0e007201001c4100e0b4411030002540c03412900c806131036162141c0c1c0d4140011071402d0880c0908405080398003002c1c1008003507045aaa5641d9881840e85010580041508203482d0030403102006004045080f9881c0003550a00701c1c0703138402d43d0340f640303070704588207007416614040000c0c450340c5001500c006c1d550140485120303064606002c085c1d02a103100481c40f0740b00342044505480d20038060101101c00545130311310b4003016640d50002620740303180504410b110303107140000c170050204443ca00a144400103410f482c0146040142400c9511a0100c03400c00c040080c000140d901511800046a5880d0700c80351644582002840c0851943d0140d81c0c4504049040e906101c4421416402400f0440c02040342c44e80d03e50521007a80902c0790410302044081c400500414004001c07007400744c0c032030f00b241550f1412150000303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 978346160 1250 978344910 978344923
    0x103050709050d0c080606040c08071818090507150905151e030907050108100308130902040f1e06091a07060f0504020f0d0b1812180109060305091509030c 68
    0xa40344c80d92081800c100e680700600c002500b02000740c41c10b00409400c8840942851000b510440400050345000321006109a0980340504494000700400d10054080d00010b0700c1c81e4101a1024060b044002400416040c03680c04544842d03111044c405141104220360116040101700c0c1003c001c0161803100300900e03032254800003040c0d26403504d0b400c150b8059803410485420050500c041030080c0440803800340b603181c0031264030400c0d407540c1c1c41e15000c40c03110f01c0440d644904042800032502144449000340c0810035580950780020440c038084605041b40000792081030007280d440541400b6440c40440114001034002d040310307240215a42d5000211000c184000b00360650b140180011403803d00010030f80b11000300c030580f45403070003515400d8240b80040c01c03c1c0d003042d0100e46001d000480c24045010b001310300d5480d103503d40102161000c600c0d03400e050483d00042c00d84d0808100107020744140d074000c0650740010300d2000d411101c01072003047c000e451500c540c481442070002041042061 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 978347410 1250 978346160 978346163
    0x6161b06060f082506050d110d0911040e160b1e042c0f0c0901140301090203070315080c0d080d020c10051e060d0f02030a0605060306150f0103050709050d 68
    0x40004521420050741c401013002054410742a000800f00101076110050302c0c0440c0b20800c0c0080c070050044652a020310487c07100312481404c01100d0414070803805040c590118080d581440143c3c05c80b00c150307443d40c440074041010080045428440f48800f0405003a04081c051300c010f425210340001982d140d001079000940201020b8518141901c412506400383d480c01d5044401e5814084000100c400000b8000d00c0103000105005009a20448110314040728510513035a2380d503103802d0030f5400b0303520882d00440800d00b0b10102c5026a80c0e034040c2982200c0b01c00020300300000e441020082c152500b1001500c0711a010b110058012507148010b2158103000c500400c0e60880312600130f015108000c2c415103404814901250701041c8251030154000c2d07088920f54020310040c81c201e292805480f1020b90584140e000f0f4808202036940700900a0104404981459130b402d0080c1300094a0204001e030001d0300c11f480e0541c0c650007a042981c21014038140502c41c0f5403a80c01294200140460 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 978348660 1250 978347410 978347413
    0x1180f17120402030c01050f07030e031f050f1605070318050a060e0415060507240c0c050705030c0a0311030a1502070c05060f040e15060703030c0206161b06060f08 72
    0xc0c0000c5140400c10030b00c40d605c0c00c2c01e1840c1480c40140b4001c01c02e00540c2009018000b003800a40d296990a001d021540c81c031040440c0039541c10650410b00502044404000040c410804110340100103102001c0c07000b200d5a90500d00001c81d60126186500301a1032142c031200513101080c140d903000e078114080c203581c2e0b840c5c0b039089030400b04000646040d4a00180c0c0003103911801e010a9500000b12408150031071100e0000c6c00e026208450781c600c8800c00b41d94140e00e08084003040d1544801440c8480d4000e40c01c03070380c815031641c00309500c562031541c056501c5245c01508000141c0030700c14207910200700505440d00b0201e00c1d104c41d80d8414120080d1aa4640d00081c0c500422007203c40080143c402550940d0070840c80c1c1100a07180e00c62401030405407104280083d241a0304484da0070354840010301541e071140300d14540a0302601000e0240405406800000b032076184c1c000c0304603c4c00300744039620703e0210f0250100300e6100c9400c990701a984103444080c00b01c0d0590000c1c0c51180104030040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 978349910 1250 978348660 978348697
    0x20a050d0806100e13020a0509030102070f1502030105010206040b06030c0306090d020d0309080711131505010305070309051c110319020115140108060609120a050f01180f17 76
    0x70001d6500c11040400c00380b1034001320b4031040d901d40070441c800c01d952400005070398200360384042d5070030300031491625451340c000140c0104011002c40824a040e00c641e0300403a0140d4501c0c0444280e000034022240164055000100415466428913070403100107420b07150b085108402080c1030850881c1c2003161070340094001c241c810307410004000c2c2207615140401c00392109551ba038403070f40314140c400f40c14282005900203055903108a626070003580b4510800900343c07a6280302040f840144101c4e404203141c200095401d901902860361415408800b50401c80010041082c1c0e41900240890401603000313403101000d88100000c00c01c6d42c100c145110892008020300030b0954516000d0101c61504424040041810700ca0900e55281c509080c04102d640e02c00340410440e0003203811240e070020132250146084d110200f400d0199038010b07019248000520001c0da400e0b5030b000b04400c2d15904081078205c1c0403540308002d0380d050350320604519001040c10011001c040d0010b501c070100c01c8210700c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 978351160 1250 978349910 978349921
    0x6190f02010b09061e0a150f140d1a040f06080c0f01080c0d021608030a0c2a080c01150e011208090402090102010b1c0c081b010f020a050d08 62
    0x800100554211480244506181a8041042c0000c040d1010b40502001e55400f101351a05200110800b8405040401c09555580050101840704140100440c80c2c500505030450b214504c034260800c9050f081600c1d143d880b0f45643c008000105070340700c0b40d9000e9220740e24103079142e01442c5601340580e100418102e0510300380906084540290314868a0031020f0100b090341c0216103a640968400d2030b40d03803110494121180070348940c08140d001038820290210402100c9400780d13004000e2100100328001440c001a00c2c2003240700c0b50241000f000c14000d20100002000d4038000c070f88a906c10710704000121803140d00350340c800001301281c900030b10800d00c0b1000c80301c0d411500401c888036601c441044141c076a5015031061840140c012600010704d81c281c0d900035000030034122000303403c10014500344000100c0300182030100300c48041c01f00d1790000d2070782c400142c100c19856030703240203a94502c0d5030300c015035548822022541c01d500075207200c500841d405102a12020b80d0b180c84114451a18 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 978352410 1250 978351160 978351167
    0x402030c07020906030d1e030b1c050c0d0c05060f0706090b090f0d080402040e03070c030501150504021309020a120c050304020906010c0309210b01080a0c05090f040b0402040b0619 79
    0x6004501903401906d4a400c56031703005407401e92103070444425007001c4107a034900302c0c042d040320401250081d1058030180d103103203003000690041902800c01e07918446030710410441030340e010090240aa02040e40c0a01041c5040001001c4e0340800000088ca05001a03452034281c96143d41c05840800000c0c04201d0455414845407843c0011a00500080400102c01404240c000f401c064003131540c8030180080e0b50b00c200101c0f0101600004140101646c92070070a018101d040d0800c01610b10f0ba40001032642444d0003614452805408034000351414200081e000750042010300e0704001e103020101101c0c06107446100d0011b826542d82030f9407440d0a0040c0520400d014252504028901d03d80307038042035014002505a46801840346440d280c1e60307000004005114101038010f00d5203400008105c140010602903242c49200300e1181d030380c0d490f0b081024000303080300c0820b4032060610000340000c00c031550882e405031000b000010400304910100e64a80c012656141d02e000c4104000c0051640 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 978353660 1250 978352410 978352429
    0x801090b0903040623040b0c0c0f060c0303041502070f1506050a080a060f0b12070312030905060f0703090803010b3f041e03020304410f0402030c0702 66
    0x7190002545498a0104014201d0b540c00481c1740d500711503040318401900301e00b02100d0007450607603112a21104030507041a107503240707100c00c0d0b8401d400c0125501020306140e4207075a0100d5410001d03504540e566224a807064505c044801e80e556030800c080000111000180d100c164000d5030000c9800c03500d1038502e000c1700c085400040c800c0c0b04d410000c101d002c40000b02c0c070300c066501500c003142104100e1000b0010b08200c01c402580090b42000c0c0d24000c0c0320000ba914220303400742450003202e020704501170b0115807220101400ca504600000781c040f207a11a0030340e402c420989000075074041c254a0b402c62a80003070f080140c942400098000144401d5000b548400591002440300390303030044e40c039440880301480d1224185140d01e0004003840300c8801c85900c61408021000e0581006240080d16540203014200c3e2100d5a082300c26114040301d00e0404a4121811824507503441040c040b810650400d50002c1c1c0c03040340041c55030310130780307031400518019a00400c009849510a1041044040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 978354910 1250 978353660 978353671
    0x1211010f06050d031803021f1709191103060703020903010c0f020c0f0d0602130303140406020c12010f0608100e030c0606060714190308010501030c0e060a1106010801090b 75
    0x60401c501480782e0f80c0c03020940701c95690300d4203020a4220000650580c007605591000c0d52000c0040c51005070300c221100003036100c04090b03403600036150001418004c2810150307082401d50b0b00401d660805120141d100c843e80ca0b0040003034208510841001a2915208132840c500007074010410a20f9424240103613444440300341041c0c56120b40e000310003035585090940365803017500540414402034580f80c2241b140284c00c40025952080c142e004424400081e100c04c400056042c1c07012800c400d401c03000e481c107445d01139000d0160084040208010310001980e0500c06550350150090403040f00c0c82048028842e4901400240f0704001c02e1404a89840300c00382d038680c20800151042080105556612003412112503440720b0160810048005030316074114918410b000e15005100c0014803140003051003a502c1c820396030380742d1004509841c07040c80590041740450004a16a2a200380075111680b6946000e01080c00c1d9114401d2a103a000ea2000f18640d640d8254807051000d603c01056001 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 978356160 1250 978354910 978354941
    0x4170717060f0c03190204030501020307090b031308071103100c020d1403160c050d0203120a0216152409050a020c0307080a050409020a110601050405090c040e0109121101 75
    0x52811070b1880c640390794028491000100c000002441d130304841400984200c02d005070840d1200d46034603045000390b20a803100d4001c5145202c001580303254810440b80300300741000003650b002c0c61680c1ca402050700141e00403548000c5040361055662820810030314001540c04000c200340d00340342d1004e41800300101c050340c10002080c030b82e4046444104100d90704001107050500750003407080c03012618150340c1c4c200180940904102400080c3e800400380058203c0f800d940101074840c031140504070720407204941121010030030041d002c0b800803103c94400340da40540124023445191200d20900851180340c0b040b0000d503000600c411b80c460b01c101580500c820004605e062b104004190382c0c4c1c0034002c001002220001194481544a0030584004008150f000d41d10380c0e26a002c0a04001043e10f8100c543d44903802c000039035454580074180c091400107000d095652081c00501020307008400090600e99214462040010604181c0b20301480069a40000a82c8580380490035500510480b043c2d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 978357410 1250 978356160 978356173
    0x120a020711030f031b0a050d021f0c080708040c0806101701020408061b040807090c020c0306060603130c0b03040311070915060f180f05100c11040c0504170717 70
    0xf01600000300d0717420308119200510001c528024180c070303107044580300900380e0240b0419008190f0b0001001400c01c102d101d16040010304c6820f0b448100d542003140c0400061030724020803140350142c0f618a403c00e002d041d00d00b4416807503511403450801c051303c007040c1d00341139200100682c0441c802d0305c02010072001e00952826140c41c40c040d5481001800b07000f8a800300a0700214101d1100d0111070040090500ba00c1700c0c56601c042d1301c8020106c0c2280f6002601584050915500c1e01107041441890010b00050030745d02c41c101805805210601d003203808040c03118002c1010300c80480618441c610990300c071820320041d41c2056042440c0340c0d214168090504001d0020500d4100c3c83c80151509441c2561100103200070403101334007114070420303a41090b06404151319600d0b4694009541c02503c140000da07503d844119001c88001034054262548400c3c1c0340c0843c54242c00041042105260a60a05840b0113031200003104404002c0070b10340c480f0008005518880324201c40300900130f00508035 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 978358660 1250 978357410 978357433
    0x5152406090f1206072d020d08070c140304050103060e100509041505150a06090501050f0706140705070213020406120c180b0c060a020316080408120a02071103 70
    0x1003030302941240c1e91041e00460070a4406440d21503a00d078600611000311a05420b0130000076140030072040700621104401c4a00042000c0c81840c2158034070354603402000001c80d1460200d81c540c20141200c0c0410520054080102d40d40006010900922401071035440c0d240c58005811102c96a102040d800200c6081144500200c1044011a030301560340c1c15030b50340e683c035200307482c52030080c2c800240b9440c0c0380610101e0340b41d201c003041ca0b0080a0380c00110a585070311081e00d055140348200340c006041000041812100c0c03030060040350f44203840c08950480d51044540182008a07140e60014070085130100c10745c507050b00485041001e682c0210b00c1c1c64240403000340602920201c40c404070ba00c40404038552031203603c030310030509080040e50b040c0503110200c840580d40712000d5200c40c0e1250401103845a144c910072240070303080414181c42024441071058641d000010403d0310206d0301031102c01c1d407030030b000c032401c07031240b40700c0c0780c0040e07a0320680e01d0217010b0184034101450195001c080d8103070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 978359910 1250 978358660 978358669
    0x314060d050703060f020f070506090c0f0307211a0a0614060a0e150a050c1e1509030d06140907020703031b11060706020702100509031c020a051524 65
    0x10143d035000540400d8051501e6000b4010703108800075440342c948002820001d209002c548140180507401c155000925600c082000c01d404d52150558582c00c650010020f0130040d11085640000c44ca0241800e5038260700c955881600d42140d4604090148080000c074843c240320301d074050008095a50030380c1d080318022030b00310300401c416541840035001c44001260759038143c3e0f8100c1240c030f001d0580c1d90030382120010802d0700556605217007480360300000ca90401c1c0380b040140d4081c408400400a48412419840e81d140c03001d40038549a0104002c0368200400318007503d0b0207010219141c5003040c1c0c2ca181403243e040c8004250720110342040341c0600002c0c0c0d0151607200300785001440d5015890031403c007010030b102d020b00c0c00c5902150025406081100079009080824000c44040340380c07650060064440d40304445805030b050304a0400101210542007103101d103101c0038411034248041c0c0b983e429281c84402034014a900c41035904000c18001d4640d040c0c1c1f18500900c80d03403000c0300ba070b072070218 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 978361160 1250 978359910 978359923
    0x639140a120b030a080901140301051003021c05010f061d01020a060f0b1e03010e0325030c0b0901060f060e03070b030601031116110409120806031c0314060d05 70
    0x5508200c0d00051001c1000c0407904101c400c648020150b60b0600702d103103003a500c668021214540800c1c3c158614410380c0e071980098904030740000d0301240d500e244040046009502c040d43d4030900207861401c85004074803c1c40703180d01030280d00c0c0d0050142c2d400c01d000a0405000c1201001051480c91800380325a40d0200320b80c02165444000400d02501030540d6070040e001001070140c11180211070307986003041080b841d4007084000d4000f0400c010039032090640340d104038840c50468803a0940c00752003401d41001042070711400f03881d141c104c00d10b0716a03440000c0360081d61890810381d10340c40c062042c60300c40386000004200c2d0b070409441d61181040446d46070591803050a43c42d8402000180240e4080d400c100140c200d82002507a440c0140e004414a1601103003046d0340d0400389410351358131030900b40b1a40b1141600048170861030f8103510380031520f0303000050080303805000340071540341d21040c8400c14101480464401080e2459407204e0102c080000030706843c801c1100f41d200b14041200400c14 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 978362410 1250 978361160 978361177
    0x70f02100c020a02090a06080f1c1817030d0603060b040f06060e0d080d050910110901080f041a09030703021501032a1a0c01150b030112063914 63
    0x40c1c2a070ba1011b200d14010580d5510511203800b47c0400a1124480410030b06841d00c064140300b0b50418007403800329141c1201d41d05440048640f86400e0041c008940700f035503840b48908003182d141083d480c42200c00d03035410740c0c401c032451a00c540036803200e481c050145980040000d20204000c51820f07030005c1003000c100c10024000d00e0302003010f405208142c4100c2c0c400050080003071180307050200d11203584031100d034040c1040301d1800703c0500c6a00c0c40d0200302c5020100507036403c4040d442e0007040300030018006d08111707200085000c1c421a42d000c5004043d01c601400c001031526900581406801c1001410480c03140200a1005200003000e00744c0820704140e0480c42e1280070410b40307070940c070070174450303000300e08114400c42d010405210070000a14141440c01e0080c448140305e0a00c07441c9880c018000d0b000c01100034801400000864503054007001d008074008201040342b402002685030a025241104200380031228a19000c07440e03004001980925004c0c420038803800450250f8040d1105 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 978363660 1250 978362410 978362419
    0x32009130605041508060106110703060b0301020c07260307020922080f0a090509190b010c080f0c060106050a0f0c02060c1b0f04020a08061512070f02100c020a02 71
    0x1203210203800207900c540c001e001e02810410240c003c80903480b0040741c03940b107903032054412034001080c940c1c03040840801c0d400c00d0200410382c56042d03079a040c0149c496842d00307039015075083c050881240c804021a00007400c0003c20700100019200160319102401241c00d002c550003000090016260514034950290403024a41c0c1c3c424004003041c0642c0b48000f074068120780000c02c08501c0965101c0c005c0031103044546074150819500c50500921000444022090798018425101070030b05507000f03c00b060005240c09080d45a2560701e1a050b50414201443c0ca10008035883c1d240b41030804c180c5025014605200d420300c50398203001041a9852022202000003c00d101030031510750f0415200240c601000380c50264030b072039000301003001d02d0401052081d071001e00d6000250402d84229205070003035030f5601c0416a00c9000703001a20921024001d0861410050f400000701d00e860301030301804440d902c80303c0b03107210844000d10301000e0010030068685820001e0805640000b6006d078919416074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 978364910 1250 978363660 978363679
    0x16030b0109020d02040e0115180302010c060c05091203180d0b010b0a020c06030f161103070303050613090b041106040b120721090302061812070c0305031207032009 72
    0x490020103801641c0c040398000c1e0707665001081d08e1400c9443c03036620300c103550340b09442c00301c003000714056051a0788800303408681541c40303050119146070040f21210000e410a01c1c50034500c0804a03904e40210910a0450f80000c00c03041804001c105010400e041c00301c9803034071220140d4035000c00750003040c80f03101d0f04a000003c0b484482402444188412000240034581742e00d411100c4000000044407690181c942d0140312010417805906074400d004240c1d8001c5042071041d0b40c05074014400a0002c55004280da0345c920800c401c035000c0e080e0941c2c0300d25481070003800e140c0b800b00128400380c2202441140309000c03c2c400c40071588103480901da03940c50100101d48800b001078400c003410319000b012a1600305030696180a42d900585006407095084030b4299a48a154200d00d402c004000c0c095900000796800c2aa01c0450250600038010a2003420440d5071b5600d0a00d903902c000340b40b032000c03800c403410040c1107030701881400c0030390401480d680205608483c200c0c115201e0340d00442d11a41048 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 978366160 1250 978364910 978364927
    0x90114270727030f05010f09030f0f0c29090106030314090112060906140f030a0201030509030c010e0c0406060c02101d030619150f053105010302010216030b010902 72
    0x4040301500c00c0780700308201107400d03242c3c14107640d42400f0384c5098903190308001080000e8983c901c9070401d0030b03030035a807a403844040c802c9040710302400c01c482078001c203c06e4684007408501c642031600144a000b400c180c401070710002d0208160480189060b0319a45054000c00c00300b0b400900f0b22207180714803290399a44414040060310750903510040812507d180410202d0141a00e6009000381c4d9040404181d086600304100b00500f899100001d8054001114100040d4080c0c0c0003503401080c9041a68200102c00202c40d0071030b404019200e203a42d1020b1490195802c0a00c102e6018100500c4c050f144113106401040b01c00c20003200c800b0410030f400e100c2440d03182c1c85c448407c030b0800e402826640281032490001001d02d00311248604c3c0607181074517040c200300b000c80d602800c442101a0340309807149000700304441c440056007120070f4001c600d40e4001000c801441c1240200f07000c880001610b50441c00024034203c24164400082c440c564014800300340c56400d1207044a0355602d0150303403022103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 978367410 1250 978366160 978366197
    0x810150302190e010806030d05090f01030603050a061521150f020f09041401080604030806060f270321091306060819090b040b150901142707 62
    0xe00b900c04005041d40b0780d00e5204290300072000707a6100800d0f40c0321031054a44004050300c844550034080c020030010466104141400f03440701b010350405060016034155aa11605e0030326100c120211811951521000011400c0c01800d8001e0145400b40c42c1c40d035102c0d9540009107040b00c20700a42008074a043c035400748580c6030003c08081f106c408041d901c910702541f180495400c030781c09080c880c1c0d051201c02e0140c20035031100c884c1261180b01c010300702511140c40a0700d01850240c0710702d401a6003000740d1b45c40090800000c0c407510140c411080728150300da1070031010803601c107804d0601c0f1780c106006082c803142c00d44040d1003440781034103090741d40c0791007440c0059290946c410071040600d04000b00060f403940c026070410300c200c0301c550341c81c0315a01190a500c2d04451600d00024200c05401e40807030003040e00d0b0150f030395003d070610700300d43c207644500c03c00100c03d120261300c06e042c44080c452a0394524148109440705202c5480306403030045036155075801040000070484001c1090307014000c7e8407000c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 978368660 1250 978367410 978367417
    0xf1a2d280603080f2a07060f030906110408010c1d01140c07031a0703020f0a050913060b040911090f010810090c18360e03031509070810150302 63
    0x3d021000b01c1d0f0f40c0b0300a00d0780c001c194101c003c0014418120300300083d803031604054216407803007540002c1d0003103508241c001e540ea41c0100c0a00e4080554484a000c0084c0d101e1084060242c1c5201c0c40c161107928203002d142c01c1d1004403880b40b00f04410b00340050014140410410301010003404c0c032001000c00308841d0207160142d10410a0b8034407481d00e000052104080242904400091051010b07940d48101682079204180d41402c1440081200401141c400c4024114000d80140708403004c004004c080010b4a07103035040f900c01d500e400030f03081040030110b10a09000f51640902e140c2800d8481c0005600050094491418810848001000d00d6007030f001460280c101c4010401428a09400c020440000319074170b018604581c860219901a1004600281c0b45000101d9910680d142d2075800a108640141511164407816114072200341803002c1e503c81d20307641000e401c0c00401076003085018240030b005901400100700500080490040c07070401a102c50358144e200300191701000701e00074030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 978369910 1250 978368660 978368663
    0x6090b060420030c16060903020c030715032a0e0915180603191b090504151d0f0102091305040206030a020a020715050307170907030f1a2d280603 64
    0x21005003404c0104091a44020007c80c029801c5802003140f00741030550300c03113013409090000108060b5001c46c0b544642c02c450031400d598000f11503144040101110400030030200d000201d45441c59840789420b01a08456000358020245607000020720045070715240101841c10408108070001405504c0411000b0000000c2d85081c900074650360801007640400e005880180150a0300d001400c2c88032406243d02a03900680c5d150800e0f5000c4412400070964503030304120134a0515640c0d120460280008d9200f418a0f41c000369036150031400b0481103c3c004212050010324000c2800003507204d55080d45d40c042c81d80d58005942d11444e0205a1424a840e440400c920b1610000210700f1a400000396000f0121034542c5100d00c2d650440401800604440080315a40000020804207407107500c0150310074016504824401d80e89075240c0056002290414001c01c00c907030b40b5000041400100d540000060b0016070380500b030007103106054148140c5c5200b0028410f1100028034149980b20710001c6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 978371160 1250 978369910 978369937
    0xf02032404150b0c010b0102010209210c061c050c1323040c210c0e010e0a0905070804050706080906010308180306010e1009051308032206090b060420030c 68
    0x59030f0394800b0391429030101180e0b10680d42020b5030018154014000d440f40b801d001088134000ca0310000b01042000c0b03c401c034094491140c500c40c0307442c1707444950017800e51a09502d0340c0c04c00e1a04814003082540c41c05465a5a242010072007440c1307a0700d0300942d69054441101d08420340c20843c000308000035a90441e002d60140c546420710f00101d4104661130155820030909031011135081d10560129001e9040c21008210680b901d05001d42c4205031b46140c4180080482240c1c907240d02c18102212401c580d0600459491410701090080c10800c0400510320307403400d0300042c03802804003610303031806200c000c3c0002400702c0c0700e85003407441d01c94054100d40c1c052b04948681da901d4428008050059541c090303c180510004902e90900b0b002c0c16200c0c1a00140310440b401483c4d4a110182e80004d18000c000308d881c0e1226100d4061854651202078094000072411403500d0601c2080280c000d011180310f1440c01c00780c00743c5a40030b0b00f010442950803091840e144e56071481d615025101d003d8942d0b144 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 978372410 1250 978371160 978371201
    0x90d05030d0f0f0902130b04020705010f0501051c11060a03060902071b080a1a070507141609061503090606091805010b090405060a0902011b150f02032404 68
    0x2601420380c0004101d070003854060000c0c2d541000c0b200f04a070445403010390018005030310344443d0ba070303103800840f101d00000d80014603080c11516581d00b1150744a28107030b07045454030300420880c5003040030403004040207400e03003e09030b2003036a072180b55100020345540906008034000c003e031402030b8403101c010036207020190742d60030301c51820003030b10041126803200700421948013240d01c91000900340e4410344c0c403901da00c0415445991204222100074960f008010041203408002204601010010385001004041c00c807a80d0660600c002920340240340403501d0560101301e0021140b40c80c91060340d590a00040000c07181c11b002001e401d860300030f04015030410b160404001021a8941da0442c0208005c102016240003041116a41510050055844140450482c42d131a40c4502c81442c4141484010316213803400305024800c034080d054074252130800013000582c1280c010340785802440700c4210f10318902880001e04442e1103d01d904035281c00361407014280d4aa59000451411200d48a40074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 978373660 1250 978372410 978372427
    0x60b0109050a08060601022503060504140706200105100e191a0103060b04060906120e191101170a0e0102090303031513090f0b0c0d050907170a0b010b090d0503 70
    0x90310001a905c260061080c0c5440c0d03800d0000c103840d440640801c0b081443d8665103103403640c1d00505805030080c3ea600320202c03544c0341c1c458400c002400040070b00f6110b540c00350070ba40c82400d0002505d010020242c0c0d052500b0090003e064030b0b4540c2c19114a81103072801c603210710000c1000c01640344885001d840c81e00c110f44c0c0c03843c5191510504601800d0703a09000313498840705103000d40d010703e120b61400301741505401c2c050540628540c038209000c609000030b003a00c41200c0545081c0c44450200502084c610360802030042000c000f400201d420b013440c00c6919641c030184520458001c0c5000b10003a035690803000115001c1d011160b81103001000c4944900b0b24038500070415215640c001d1043e1814100c2e526030301814000c00c04900c0e004a1004407240c2d06031104040c122000b0000051414100091200c05c00c4a00c544d601441580d00241082c0b03060a48034042401d04c3d14207200184e10141a0500040080344440d0544845060302c40d10780c0d8546010400400b01100001c0040c00089000328 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 978374910 1250 978373660 978373663
    0xf05071b050307050607150903022514040b010804060b01020102041d10170307080a0302121302030115033207180501050126090c1e03070e060d060b0109050a08 70
    0x101901d608a094800e0b1503524010407800b0700c10b400c0c0c010501492040352002c3c5035600d90004004034003030700640e9141c0c0018602d0042400f4062540d0301d06000880060201040360482480a034900350781c03c006040030800080c02852000740001c000588640010205d64402c0d015580244409a4285803d0107198811540c1520031128000f0002c558540011241e410444180400520401841c07801e0b943e502e500d40e040d804442c980381815000c00c41110030700580205184509034401100300307401694410542514a030000e202c000e24a00314090000c9406d04035052002421183c001e600790700422190000c1c0c208000c43c020040c06684400504094000140b50524020071410807550ba00c580c010340d9544011104502c46d00030401001107000d00c1c9800032500200e82c1011112185c44078000070350703c4e0900c0c020030903910b4103c0a25450700d080c200280006424040742213030b050301d00000800c5d000c20b0281e030080c2110780c4401c0320300036a900401466029040150503160b00603110388100307 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 978376160 1250 978374910 978374963
    0x10090b0c060118020405091501031b03020c16060210020d0b04140901140705091003060510121b0503130f05011103040b060114040b0c07080f0f2505010f0507 69
    0x403c903543d0034150070400c00818400c50702070340c20081080315540c4814020340480d121280d920340c1416a9030643d5840e5004501d80e84907144c0032980d001da90360461012490600610710301114202110708800d00040b500030800a041d911447c0b030050715103801e206c3e0320010381446458a034005141c220003605550003088080e10503180e1100074809035079a41c02410001e40111605000590309100c20070441c030302211640040720a03450042841034039080040c000d0025141c5000114174002013100d50300e00d5034051003034220300303c06488070101240754004d4040e00c0000c002c50119850348400d14104002e0101240c1d40d2504600200100c29041508116035402682c007034030700c0b10170303100000c8643d031107091011542945501c041d4203051500e00b82540701d40007040c4041c4d01c0d0060300401b04400c0010410344140e158050014010100154506402d001e60001c8403920010ba0070110052000d08103c00300840e0005e103040c650221030110200c81034041c85000070b0403030580c200c0d1402460390752040c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 978377410 1250 978376160 978376169
    0x106030c0f030b010e1504110306010908190210110d0306030605060301180201050d2316141921050601020d02190215040305030a1814010e10090b0c0601 67
    0x444850307150080700d14018440d100060001c50010010f00c1800384018605411240808000300f040701c010b0002030a03904408800d9001c6100401082002e680c00580b0700014240c1001410f40180380e901841e00e241032544c00a801040396108000305c4a105441103103410031300105a41c4d00c00e890310001800341005200549803141000041002e031b00d01031181c04031421030b6410402d03404180d580191030036046600e08907400c9540d99042c140300c0e203240840190645122856030a13901c1c0c881816000e0309448009041044403007010540c000d05a00122151000301400c2040714141d04181140d0724102c0300c05120507140705a180b150002560341003980150760907001e81d140e002010008036030f942c60b24540e601282c52128108030260420390070411840103a00f80340380c42c2035100d48449140d581704248120000d4001c08001d50250340c0d00010801400030305501210b88200000020700040c045190240300322091007141102e107001d940315034001c018800b0029114803d1001c9a91107003400d201c1d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 978378660 1250 978377410 978377423
    0x80408060702010c120b100e150c03070212010e0303191d0307030f030b220b03062a270102070f06050c0625080417122512090501021902010603 63
    0x1203041c0442c0c076000b0301d007031b280f4040d041400924680408a400230f202242c400c0d00403d01d031582c41113039403800c1c0c001c1c4600e40860004665601d103a2050100c4650b06c50b04a0000340d25000000c0346d0b114000c0203c0b42c214102e1030b017501c45018040c06100c0240707210602e0040c2041000868000100080050204c10340a034590548819000c00181e00b0b45480d40422503128041c501d2112510000c081003040b401c288840000d200c0c10740d02e020900e044c0d01510300500745403014000e01d101c2c0ca0000c0810207201c04600409062204a103000854440d45181c4038442c4201e200c11300c011640700308900d00080101c40c1c540302c042c640c2e40704050100c1c0d01103d00e91880c1e0080900150194a0a00c81170000d40c0c0c1c10103010001c1c00d1480740845440c1400b6008540c0c200c0c00c1c8000d88821440714003e803685051141c43c41c4d205003401003462522502c078891307109440345c0c1e4083d0802015005040c08404207004140898551001e14040d07009101d501140c20082d0b5682280d503001650543c40441542d00c00d50 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 978379910 1250 978378660 978378677
    0x501030b0f0f010b032d040b0105030d02010b030a0f110d03030c020c090411240c0c0f0108040201091e030515010f080f0a06090602041809061104030b01030f080408060702010c 77
    0x4607101d0310710001d00030036403d0a810800704030002c1c000807000e010b0303595551610010b855550302e40382e0070650031f407016120f204000c03006000740e140070b2080303d01d0310407180000c01188020740f001c203071a01031102018202c80b51401084050140c400000888514020b007110042e80d01c5183c043c004110b580c1c1080018400d500741e440040c02c000070090b010340e8000300c1d400300c0d00921404020b00865082d403811103e0800900000e5010302c0e44e03001c0c008182c0000c01405103005011f0901c40c060901422080c1001000414040942d80180068044c3c0321003014180e402100002946900c0406d980002c002c2d02c211500c01080b00800782103241650503111645c0fa64a5481c030400365110b81e0385050024a411071810b8100043c2c06501140455201c1c94000d800c1542d29440c40d158040026070058442d43c81d40454010050548a0b255501d06006601802c20381075803104059508140001007075803810000309000e024030320003a00c00070015070045940b54509007030024040c11001100401140408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 978381160 1250 978379910 978379921
    0x70c060c08190f030605030d090b0d02130611011103040b040b04062007020f0a0e07110a0c08030d0f061202060f0f0412051614010302130905070f0809070303022104090501030b0f 78
    0x407c016082148c01d50758452080e0905003600d07920340c42051826180ca908100800d2507214003403d00b4002c21a03a00c0e1a03c8107019002030b2420765003080038018a0340300401c10480020046541c1c030303810607008006480c55903154070b00300f0010402060b0681c0348003025001d402c09043c4c042d00600c1e25520a0300c207410007004840a101049200c0d0040141b60900c400024024070310407514100f606c4000011a03400c44099110840d051406da0403180b4107400001d140191040e1502480c01404c0d0281020060507140c065000310b50002507800070f110303800010710f0000750900c030000e071210f040c0b1340c19550340c1e11030703a8600c081c02d030b0b0013912401c4403940184000200301c04404040503048807401401c2c00107600c045001180250f00030301003100c813082030410109119030280f14041c400d050588410103110120200905111001048807280341d02200042c000268041142e6a605c800308003504e503001072210100910b40160381100316181c0c5401e00000034081d00308415401b42e010400e0f00074140e00c51 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 978382410 1250 978381160 978381163
    0x1005131a190302040f0b03061f1a03071d0a050d0203121303030807020a200315010303030e071a07030807090b1201050f100c080f070501110403050f03070c060c08190f03060503 77
    0x18a032102d03416048940014600c0004005c807048514a07040c01400e0241c42d02d170400c1d012554002b0b0400d003004040100300c455034101041c0c01400000180403149404108005107104005009041c081c040030000d86085490070014400508402e4100c0d80e00c039040400707400c210041521003900010620000b08094500104d54028040c0e00b001c80c0c0000c903041001d820002c02000c0942a4040c1300310500e50140d11880310219018610075a00810802c006503422840e100043d0003070340c3c82c0a64013400c1503001c003124040311081075150a2510b403aa8a423002581c0d28020780e07014141071603001403200d09100022102c235050750b0085071059801300a9a0a00c0301c40c40458007100c001c24a451071040c041080c510103450200c000d51042d07440d1001e01c0c1d41d0b0b6030a43d066004203280483d408901070003000424007040c0720001d9a50300443c1001a161942e04902d145441103809121202805009000c292421905c800b011046a96070700c40b00e44000815401e070a145020000e46481e00c04109840e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 978383660 1250 978382410 978382421
    0xf030e090f01032004140604201b120a050c011401030803180c060a171f0b09060403060216211710030b07050301030b1005131a190302040f 61
    0x25030041c82a00d0303a08550f40c44442c0524070084040300b5000d000c0780f540d030356542d0003035904511240c2e4130b260a600340780c802d10040d00c000c0001160a405000310604401180c0700076200b401070050b0b0381c000340a203541c0c5103034200303100c440d02c075903502c400002c1e001c4045800c01c2c000c040c10112403000308602c018030b400180d058103080c00000c14034201040420201c0c0a01c6906000085034402a0f400c9a29160001a181c0d8450368820380860f101007640340e03095144c41155a0f0200304108020b5040c8440d00701600c941c0d40354000c40c50140340c08140b030003241c3c59003010b480213503034846c00466450005801506a0f0144a401210f805d00c0280307844004421829071a000181251541007a500b01d503030340c90802c100c0060050800c0207031440000045a851030591780100521780740c00c1d81c1d80d4150f04000c01601d42c0100201b42d09848048104580c2d21024590ba4903614a10320000d082c003111091410107080702c402c402e500c030302c0740d01201c050359642ca522001140d02c2210100085204110204160360 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 978384910 1250 978383660 978383671
    0x20d05220b070b010806041106031b03090106030b060d0b040f050c09070509030c0a060e0616150203010512011802060a21050a0e0f060406021309020415080612120c0102040b03040f030e09 82
    0x48d8a0408005800c25402030b54019004103203580d00100340445142e06504129400c14040c0e4641008000707014092410a402510941d070f61006c103e00c41e20782034070410300940001d1050550050110070700105200001480000070018a45400c00b02c50040807a0050b07403085101e4011264400d4007403808402940c205e58081d00c9466101404000f045401d8001201d00742550903080200700009010b09a064014030030035400689035410302d018000c581e440340d858111980c0c5001c0c0000702c03e2403001405501203604a641c140d413804605021142c041808013081d5000d03030704030f03e48048140b00b0f8000502c120b5503240100141d0040f6226580e403040c0c41d003080c00c080d401c1040402d02040d0309070010804440c0b50480d0100c081d58540501c4102d9000d40c0c81014402a0442d22288255102c040b281d0448001ca134450400b0344000740050300c44940e046a514800300020308030485c91001c5d01641e0081c46254103042d04d0f46001d040100590f1000003007200040c1c064a0344a40c2441e044a1060040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 978386160 1250 978384910 978384923
    0x4030b1614091305130203070306020301060e060f04050f0f13050906070c0b010e0702070e0a0c090f081b0301060807030c05090f09071809020904060902120d020d05220b070b01080604 80
    0xc040f82c0c010005103000382c40e10b1512101d0710a0b0901584081184400551042c0001aa40d600d4079900800222140d038020b4450442004003c20811000c02610151181203501800020714040011100e42da010042c54118a066102202c90300041d0312841c1300e040700c1d1043d03500380e0303035201d0381200d0000070000018000010f04006001076442e01e99515442040e500403910299103400b5443c50041d000c548442e24541c680c6c00c60300340d590344a040b240091850601c2c0020103030601d92141c0e1905030000301120005c0552a03908a10350702500600000c003500825200403039100c1c144000060101e0003031b28021002c0c00c0111795450498802184594140d4001d0100541022485014100d00c4007103d0580d5480d0742c09800580d0300d4440c514090361003424001000451481032101c2303618070100083d080d80006010208958000c41d00031900811780c50301503510480076192518005c04c1c90345040c0c0011810a0114840f12035800500f100c03809122442c0a603a0380307900301d40e501c8500300c0f0000e00c403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 978387410 1250 978386160 978386179
    0x31e010917091315030b04080a0e01020c0109120201410a020705010f05070507060f030f151403102322061a0409060c030b0114030c03040804030b161409 67
    0x1e80c819071186604e0f041d50180300c000150307280c9a40b60b078048196429100804000391050000340c200c218098a03400a00252022052200000c1c000d83c003544030302c0da6560900100350f01160301c03072441008404c8030325101a0001601d2914070041c1c8100c115a071a581544400b0040e00080da41c055801080940c0d00400c0200d0510740116034113030302c5050f0002030140a1062100185042c001040500340558404e0031106200400505440b003140080c0c4500d890000b10080c149a20a4444161044000c20312950000c1001180c178100458421452540c54014040c0c0304c1d000e4039070780c4200030f18120648101a00c40071603070b030481001d145080c540710506890520010b442900724541d114080540c01d1900c04840010a0036503940355030072109140d0314450480d001350940303d144402d03c000c0c81c18654685100003c02c000b0b01c405000504401c1c4080006010460520f0031100603640c040b80d918064141441c10300e001c6000c0c0c508210110f805240c014035604004019030b107002d60001d022044 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 978388660 1250 978387410 978387439
    0x60105010f1b062711011403040327090608060114060a0c02010818063414090402040f030f0c060c052d070b041d010b04060e031e01091709 61
    0x1464000c043d000303070b01094004c441d042955421080c00c3c25000300528840e650350100010055122422840b01d404002d0060002107548850112400807002c101500c42141c0c0d00151481000d00354070005003582402c0010907000b0000c14020304842d1204000d41f6090403880801005001c0c01c0c01c0f000000c0d445048903005507104404294206d941d001e80d415001071480316960500200321206101c0c40d0341080e90b00304c901414401ca0044101c0e8903110b0358a07400300c0034018112101d80044101c44540862407000da075440354125030060071804480409560340f4504030064550582c41503031380c4004640d0000304076010382903e110b49540040584503049041c2154500207268108540301640301110410501034104005000350111742c0e11203448a01d004082000e1104100c02c0d526a85c000200400810284a0a90301078900c0341c242400c0f04590540070a10f0000c0c40601d40d814880050b0003014003e1042d03201e4204640101d4507095101070365000c6000600c1056800c035006800d03810b0000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 978389910 1250 978388660 978388673
    0x7242304141e071406032d04030c050f1911041d0604030905310f0e0109050c0a0e070f020316080403020f0108010b04170c0312090109061103040b09030c030d02060105010f1b 76
    0x3038404111780c11103491459800070714080901110304070041001e00700ae00701882020003840c0300f011108402009044102a07daa00d29000401c4c02000442402e0742008140d55039006642d401144448881c80c1002c042646507840300151010740208001c1c2c0c2c008102d60920640107411250b0301010328071201c80e103183e40d0701005001c1c2c10010b02156100601000d071441400b07181c0c0c04a07403000002c90600d0b4582480d90420181507001d80c46004c6c001d138208800d56250000b942c1c4090542016685201810004e9056200d01201010030746000302d100030411541c0000380080c0d9000369030001e01c41b0b440400540302c20364280100720000030180410454481c400040200364036842095070041258400440e00d0075200c024204000039000c41e10f010203580c442101c000804242c51300140340700302003030311540328070a40c011901444400541240035407820003803142d103000c01070111017814070b68450003500e07944203005850000740d2990382e22040e103101d01420042c907582021103a580c030240d5540d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 978391160 1250 978389910 978389941
    0x1080304051c0609080301050a0506070f020111161e0602210c03120a0f0b0a4407180e030f13050607242304141e07140603 54
    0x4182c8142c969620400041c1c80c0d014074121a4400c12a568a1f54100030400c0380c11481500700a0103180140300d49800b040011969452203902828040c0d4070240c0100c800d0300b443c0444001e00d04416031800c1c00185400403003150140700d804c1e04140391700280c59040890311034a202800401d10b203084501c3da01c200c03200350003c0505010300e4045901d051401072400d030481e6800c64100b4500e0342d580000d00788030b8166004404241904540b542c60042c24090320a848111340c1201212002c1c18103403451824200344400f42d0f00545000c00c00c2203040a140c0c131550303a00c4590041103144540400c14520b10701d4940030f010307501540303240910305000646030540c945d0340107551500d8224070200c1c0000b5241d11042c0040000c0c0d40110082c081c031501001c11200d25505074035101024518240f414040400c1d84031803d16403a0b400d02c1000f44944540c2091400c940d041603070110706015002c406140c1106031864649000c954000781c450240c2d980310841c1d00359a0808070280c01501c1040090080c07814101071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 978392410 1250 978391160 978391189
    0x50c0f060a0f0e060c1b030106091e0e0309040216021002070b070611090909030409060623030402030c1513050604120b10210b0a1a0f180f16080108030405 68
    0x34141000d041c0d4105c2803a020300c00b078044503080520301880311142421300400016107100c1c02c0501c9011261514204d5640050481e261074a0fa18000d1244e411001c0c000c8031410000140b0a6444170b84c0034041090303860740b55908078810444d446000c02860300102c1c2c0310045034180c2424078101903550322400b000e07001402c02109110010441001c280e51f6a04999001e030406100540d00c1d82d0034103c411003241d0031504043c0501c010004211031703603544c4104050070114800a160740b40d403180c0c4042441d01c0c100c0c154007680300400f0400110b0300f040d000d014001003441a9a52030007281d0700c1081c03082d41d118a00582c5014482c42e00c070310020610320050690001c03020b00c4a4416142e0b41c0d1041c1c4c191b2003c0a0314003281090501800c4180440c82100c41e420034010001002134500c0e40b4040b0404910820355140540040b560384011070f82c600c500c4441701d100c0c40310b8038080782c81d0034540403400708400c9600d03d031030602c441720780700341c90f807007010450b040c0c87c1203100540c54141803100300320340c66085145 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 978393660 1250 978392410 978392419
    0x50d02040204030609050c18060609010c05010b0d11040b010c08090f03120f030103030807111e011515030513110411040b0d0e011a0d1506050a03050c0f060a0f0e 71
    0x400000036000c2e100717821001e40208060110f001001041283d5060310070000c41090460030140303c8960740e07450031500080c0342401c01c642003821501d051805000070034070329940b04207400e07035080c1480700c6c02c01044610103081300c0422400c49050015100c071803040b04054002c0c0800d000c0c0c1025424980900a5010001005c0307805807980d030250141c0c2c55110703c1c1000c0c01800040010801c01d50810040c030340100c40380c00c0802441c08610900303982d4401951540f0101c942c0350500104005007941300310b8043e0105081070000d152079004460440c00544418070010749001c002603101c4404442020310740d6030100b1090214001901004003400c8a004000d001c000b04000008103150000001c02c0310300e100c40c0002c6282941c29003102d08540c01c5100003074144c2014101c4d0f00442e0345070701c650301c80240c0c0600c044900c01c82000b843c40041400350055608862441004030500c08001050348506104a0700d001c0003542d86424842540150b01000012807030800b20341e0f00088c0249120314013040040c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 978394910 1250 978393660 978393667
    0x30f0e061504091a060f0907030f05061c0b220c081009020d060b03101a01022806050a0e07060801090c0c080409090f080d0b190b0a08040f0210081905070801050d020402 74
    0x10001f40d2200360543c6d190021035a101c090010800c02401010f501010403500c907041601080b958485000300b440c001050104400b0002e005001c0002095a4001c1a550082c82136051445c001c02c0380d800c80e01481240e84a014400da400940d64094848407a034041e1480344040015a40d4a01070301140e0600e59241c059400c1c000c1010340385c0c0c8248020112038a101499102c544800a17003480e80003407c030886010283d0346102e14004003a03c48031480d901107000070b900c1d43ca046002000f016070b42000d032814019000700154050703100003028181c82c00b4402c1001605150030303003520009050032000706440404d01c001c100c151095480312101c140559504650b9803501d90320350070b250380500d000c010056134842d00c00290b41408100c00c05a481c0001803100c00e541810340351070300760180d20340756400c01c100c0500042c10002034095003030851781e01601240305880c050f44041c150200448000c0c0786001848503503160a4058003d443c022802901c41c2a00359091000b4010203515041050740c00076000c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 978396160 1250 978394910 978394939
    0x21e070b1b0304271416050703172a0a0e1c0b16020d050903070302091b0a0203270d020126040506040501050f0403080f07030f0e061504091a06 63
    0x4c120941c000c0d0680000800300c884031111480c2110111a03204000503e020300b0404281c80300e441610520105080c5640c880304145001c98841e442c0002144103d138260302402845106e401c0f040720503080e0300507489007040244800d9400c50040d0118840021200764034401503041403480440850a084815030f2400016102d4400030201503030030035460b1034054031103420651b06000064494484e440c0c55403401c988140080c0c0c0d039a0090101a10640d8418003042006d00014403241003480585403050f201c003411100039481e0341000e01041001070508601d0700d41012264860726807141c004040d4090102c2e590011190408074200119000010200803001201441da59500c258410710040005c1c0c41c003454520700303441d8042c20942c204182d003000d01000030340005006034070850004821045694500044018000c2a01e0a6003802c0c6854516110100d021640311710894106008030640c0c8519410301041380c5111070b02400e00020600c040e9940b642a054294101000405001c1a070740d01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 978397410 1250 978396160 978396179
    0x170106050304060608010c020f0c010c0803010338040c06090b0d0c020c03070b0301080d0305162f010b010906021f09080d06080303010303030b0307060f18030b07021e070b1b0304 78
    0x1f0040c100e800f603800b800c00f1000303c40c0100101c071551882883c05509201c0035995a034200c3c0010301000340800700c00340b88100c28034035a20b009178611140115100d0907d80d00c05070b40141c410107647c291040302c0f180101040b01070040c04800c00b21aa02404185071424040c0780c00010304040052500f14080c1e00c00c1c103070750343e03808000c8100609812101142daa52404000c503240c00d08042d150801e05041404000003042003503040c1c2c440c0190741c2040303524445083c0440e18203060348901c040050380e1240040760250380541c09840c0221080c0c0340e20203116142c0074107981e101e0130345100d103980b0340d8281420700c01d55100e03070451040e86120340340150400318006150380c2940c50a0b0841c901540c40800104181907140c080c10440340c405a015142c41130510000803d44401b442c2500107000040000c040105503a450000045030400700f41000c50404035002134460082c1c48501d004000b815060086442000ca00c8800f00d4411315440e600d040d440c0e5440245104a807e1503819a00043c0f0000582110 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 978398660 1250 978397410 978397421
    0x1603150f1e050a060507030f0224010501170610030902060f070302010c08070903030804111828060815060307090507180e060a0b0f070203010f05070f17010605030406060801 76
    0x186880119405491200d4100001c0034580c04180b1071003000000300310f002d40120407100c0c0560107280c9208944035400099240821407085401d0b6180b242004007034995105614906841c4240c0e112000a07840440c4600701e480141c50300d0754007043d8008040d6006000741c0c410a403843c07000d030440e0709100b021071819141e80c10403a020b801507515000303061034942d844580180d200e203c03030134501c140509644005000c402c008100030440c1c0c446900310803c41c0c0e680b4950004458440d0b1000240d4034202c80031012180490702d64488480c042c400306900c3c205140240d00036551054001c03e01280002c035130f0241100050a56605030058a1020843c0314560080030311801031500c4110b1000544541d0325403101c001d500940d01d1494060600403a03955098005049904091101d50aca5030011031100b258402e86200a500d50321708049400d036010039800044c41840c1940b508691200e00313010035100800c40d080d01034580481e0b207005005040c0120040c54105001340350005002d5120440142180d2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 978399910 1250 978398660 978398669
    0xa140303010f120506040615150207060201060609210204090f0b011d0c03070c060f090f11090105011e05090406080c100e0109141302070b0108070803031603150f 71
    0x10000801404181c1941c070402c4000c1662a00d07a0100030240e4451513290a0003038001021039407900d40400c0b000070300500000240c180d040395282ea64140c071001a542d01c0705441841c02550801a0000700140190a640100c0302c10030050003d90604261012031b9000809080303078060b644200e240701007440d52405107281c6100d400b0040c01755041c01c07005505219915030501000780000100b105052180041d01c1c1c0004103414824a00c000d5481d01e00c01504c400002840d5207440c080c442002d01441079440c1603414058031032110508411414840c4100b001d0294038007150f160440501901091540b0104400551505909200c128000201510580c0c1d0010700d442d4490700c2400704510301040251450004ea040283c2d030b1009800029203001d2032072049441c500000b44540416880703400340e10070f02c81140703d001c666411036447c080340c0c1d9683c280541141c5124040010491500000c2282d008014501d192800120700e007008601a004028801072100200c0c940001c1034425200d1030000b60 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 978401160 1250 978399910 978399913
    0x3030f0304081e190c0f080a0e212d0706030903030f0903020c22050c19020303010e06060d15080303160212070210052215021f0c020a14 60
    0x343d403054095101c0202d80303090601d002c40300300000ca411550148031540821618280a00c29a4080c1460a03d10340c1021016201410000c0d04450317040d07200e900c0c80280d150403550b22111702180000c003003811210030313481c0071160300c440501c200300958050000c2003454001013080d01c03107002340314483c101402c651003500840d80710380710641055010b001d540200d51518200300540c1125440c02075650b103180342e4040c0a0950b407408601c072000310426110030310000b00310501c202e04203014442c000c0d0b03100540c2c45141003c0204200e49440c404412607040f280001d50000741c170340301c800801010341d2083d899509142d60301c41d10320325521000f42101d00281091000345032039241460a0651240c04880c109046411070306451481484000c1580da1041d0162151007503054070400c01d07181da218040c860782044400482480d06041445401001d07075211041e032113901d40c0f1118060f0381c0e524200441c00e40c07034015403d0840f84600c176035000d803810004920494407020b4158a4007103a500d0411685102c9 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 978402410 1250 978401160 978401167
    0x1303230f090a0905040b0426130503060108060c0a0513030609050d110309090a020d090b190f060b03150105040b0d0605030d0206090d1209020a0b07060f0501080304030f0203030f030408 81
    0x10b440d01001d80c01c02004076002c10300040c54030307a0f901d0080340c1c030060000b40911442c810f10003a034028a032100c0309107220b070342c8003a0303540c400c8810703110348501d0320320489210344a84000810b2045002c50580e0140d0342007100e89080c070140c1101602d240c0c0050000c141ca5070100c043c000041070700d41c0100d2282c68050b00c054001c42d807200b50002d041c614001d9680c10998410012a1041c0d01d60b1a54542d000b890303d0030040e00e0303852040d80800a007090a0f4041c00000710441070150007015081d075484020f403402010002801035010301c4050301c00c280f0400c15499018400580b0329002c5a0a100d5103001c1450258030303181d01ca041004041d00517080e4a036110b80d481d803060120b8241080120110b280b42d00090032240b40031804140d45103010740d0384500f04000d04884542005064011094596000744181390040d1601203095098111610940e113036030400d0350f11185403002d8807600e4160f900a4018514040c15500c03a4548903502c680304981510003004450382010005e4003860145124544242d41c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 978403660 1250 978402410 978402427
    0x5030a0c02010605031005100302060a020d0e0118061101110c250b03010b0708040f17010506010c021005070312090f0210050a0c060b120109050102040614031303230f 73
    0x111034105400300d081da0701d81141800103503000109080100740c1d6480c04640381e61a0b4540400901850740001c0d040701001c21040b00d907680101d0700d9007520450355103040041c408100110741102c1813030561606108480f10502c2024813131149920916440c0c2d0001c100545622104141ca50000d541095113401150343c041e00c00034210410801d4504108109080c181001961807040c40181719050307039220b000480c901000304290a403002003500004585039075507a40c40c104910444140c14002039440c0400041c1d8542c0514203411000d40c0141032020030600141e000c0e02d003903215460a409200c1030343e512100701341039030081004c264459004606442083e02c1408030003404129032001384401440318000035079000200d010b0460f00884003041e107540820200d60040d0700c0404040343d550814400100b813000540042044a4082d590010303102c1b0340a59545e014013040d945845c1e803482401402c0007191040002c076001c00501c2240c0e0701c68024401511381301e944a00d4211480c800040341644 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 978404910 1250 978403660 978403681
    0x170105130902090708010812030f01090203070903080d0f062108220b1e180f06090402031003050d02010b060d1d1c0f0f0c170904140a0608030c030301030f02030a080a0503 75
    0x203508d4203154420a0030342c00c00201d0070103404070502458105070340c08030015030924482c0341801c00039500244810b0362a000720503400c02900c00c440400705410304009001401c54240703250301c042a0b00c03420310700c03190203102d03580c5c200b4540c80808505086900180c840382c1c000c070001542c6008203042c03802d440d07030b03403141c00400d25100600e000c0554404d002071103613038003403968502c051881200c100c840040c1140c40c0c070001101c0c0d0041c441520341051021080000310480201c3c1c10b810b42e8029422940c00402844049003030740c03020194190020002d115001203406a40c000e02030031b0f0700082007244406601c4030740520303091491402e07034000c0e44c0e100c00050380c0e00d81043c0000748018941c601441d0400c4c0481002d1f04410084200400b190310381940e1444020b20304007a10020f1034010414415a042240300750944201034644803001c82c900030000070090400412036109180600186095030300e1070315820038076140e800702030b6014055101903600080342d0600070020103a1036201d1680300e041912084 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 978406160 1250 978404910 978404923
    0x3050a0f031e0e0f0609070b0903161202010306050301110d0203040f0624060207140d110319021f0e0d061803051b070e183a1701051309020907080108 66
    0x244c2c802e030084070902c07000310000328841f01642c1180040c180e540c01c80c1310229250980070100b024204105841c042a4064400d9a844586000366001d0201ca9180c0081608842211000715209001007102506021840d0040c550103405189014011211525001c007910100603980072250101d0211106404186240c1400b0f010f2510050090508181050700e09038042c810442c4a804041e15940800c11001205110000b0250640d40380c202000101d0721445d0412204921a083e43c00c05450203030035911804c00c0000d03042ea12503050502d407500380200c1207a01da00c20340d038941e25241340f0003180c5850880301807068071998450ba510660108840c09141d8289244050707901711400401c0900035070300e071180d0048217518850300c000c4441c05002c0d1400e820902e100c11b035006046410070580c2001c0404001c400b0606c541c0c070602c454035041c1200c018080001400007000c03000010700c074909084c512117940209040000071044400d0b0002500204116403040010b4031020061080542c00c0c00003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 978407410 1250 978406160 978406183
    0x9050703150b0f010302070203011508161d0a0b06070615051e130513021f021204060c0f0c03150603150e0c101b0606060e060703050a0f031e0e 63
    0x700150780003000082c1c0e904000c038019034105078012856906558080d88001c01c2f800750340403042c4107507070b56504040c3c0710700c840d403003140d500044000005002c9600c05040b000c00d1051655699a0b41e490b04141e00003002e801c40c0c0c2d550060000c0c400713407000170190310440b20100501c2d090b401c0010300e450104211411246041030001107082412a50b035181d0449030340c101c00844002190503900d004422107860b0303480d08040e40c030130340720b9500700040000300c229400003c01e41e600340c03085c101203000c00d0740c3d50303107c1c501c01c0e400000c0c2c0c1d8203a84000301c0e0000d40e401401601c1104000710083d500d8580303030400002045010fa0482d030719907041081182c0003d0421a005044c00240701071403d542e400c50312800d160703c841c1d005540d061018611103102c2c1300c516655100c82a0880803a240c14101003008048900900000c51215030851070706240040a45040a525036151071810609440c200d40d0300f189110400f00380340c0c071200702c03840ba1404900039820411100c580007031404851120140b401d07850046 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 978408660 1250 978407410 978407453
    0x7090807050a08100b0f0a0e0405070f0f030f060b06070317070e060702120705090f041101080408030a0f0f022d070b060d080d022b050906070c03021009050703 70
    0x4110844000c5010b0500700c03c0504c001a003c155480410221111000b031aa40028002004140c910700c140c81c1d64000c5005404580d205900e80220301d2000c8010700850a8001841030b082000801101600f080c0c10711500000c02c250080e1004a0300766084481c0403000314408010040c05c81d071030303844000e034041842d00e4501000f454520204004d03100d0080d010740119480400b2035898881002030200402e006030010407030b0300e03001c5d8840b41d140d94140c90403201407041d500c60500c00d41c85009101d00580e04081c207186142c4420901400402c404110070910716280c00082c032440d2542d10160036440d00c10085403144201c00701d40c0f03491280118440c2c074072501050054102003003100d10a00d074042c01c10303204070807500f0181c1031008448c091940c00b48446070002450548403e14440f48103116000c2c200e2a178440004e10303141009480d01100c0819141d8040800a002a881036806e0620b050207030061701d01441c04441c45d082603030200300d025034156000300030030002c00500c05101084001c1e000d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 978409910 1250 978408660 978408679
    0xf010b060a03020901050412060509071409070f0c0b0718050306190504020604030f0c17010207030206070f05070c0b0a14210408250b09070324140709080705 69
    0x10010305140070740345841081641c0030aa050f080e90044044078060452240003203401c00c0c1c10325159010f418121200800e6000f045400039040e1902e80e14071a20b000000d04218035984c82e4082210b034046c0c24a1420b08012130700c903c59000c5403c980c540c1e40134011a82c1d400c200071038180981e0b255065142d21460207036010380100a02610800c149802c01c8d9080d070b1010949807200e000290241c040c2d0340014120000c2e05070f0b060f08100c0010b680c0c8003281d18030303000c080900c400d0f450564200d0280f400043e000d6081070000460031440350030440c0c42049542000d50030440551101c1020401c9a008481002ca0014030541c10a07000f008201540003480101440c1084170000312400c0300702d00c942e1040c01008030010030100700c2c4e0501030740c044112949100e06070480c02c0c400c0d20b003403000b01c080a0b04c0900d00040030614034280401c44200340d94001140c0728002d44a0035420b0801e440e40c8124208007a40c4410902000101340c01c094080c00c42a501d50f500d0ba4207200030030f400c000560303001c0c0e0711a40c41c21 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 978411160 1250 978409910 978409931
    0x601020601050a08190311030409060905060103020711190b0f0309070506030c0d0b0303071502030a150b09010c0203010e060709080607021609051005060d20030402010507140c0a0b09030f01 83
    0x342580c1917002c0180c840d10015403603c1c0a840901d07052481c099070b40008500841d10101c240d200e4011198075002c00e0101761120f00c0190124400e1490217042d9490f00200a034013400c1192007041007085081d4001201075a48030b001c56240c02c0341000c3d2100107400004d0024007a020003446002d40401c90310f42c2d15500b0a80c61440080c494003142004140d260ba100d484155410300039940001d401c82d4002c40048801000040294001c031480345040c0c1c070307080000b001084051402415500c0310a030940c41e00c6031a400544441d512650304176819034a5036a6807100c44820301840f8050040703030312050402410a100c060030701000504440443d4081c8149d440c02c540706c070303004108417a8a03000c0001c00e0344441440c00c00300c42d03580d0080c5802480016021808082d00c0e4000f10400308550507a0f203203a1510301035450140300c01d40c0c1c01380c0051002c0c08154046844101050105c9a0342800c44904c50035500c04901000d134158848e003021940820700850501f070031b1103003103020342ca200700810101059 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 978412410 1250 978411160 978411163
    0x216060e010c051b01180b160e03100b06040308070521090604120519030f03060b07050c1c061a010f0302030609010b0a030e030c030c0d050711012607080601020601050a08 75
    0x443c01202442c480400004e00340040a6100d40081140d404c00c0c001c03180800c0c20440e2101c04d09441c00542e80c0351103605c080049110b40c02a10401c00014054203454100100d148098004201407a070301203410000040054203d1000b005541d21403009021540c40300080c1c20b44503080d200f40d40c80381460400c030001a503900c07070b02110195074030036840402415260070402c7c5403040704ca46149400d007211491209054001085002a09240d6000d10240d5202d045000c1a40039401004056912050822449140018119800000411007041a00c12588641e015541d54684e0b41d00641d00862008000d035074480e0009580c2c0845040039441d5040030f1020921501d0144209440ea01000c145005158429009001c1170f8524400710707038841003800480d075107a9101071075152152084140303020340349001d1811782c0c03403164003c10103102c140c2d1124015036070180701c5100b11000c500c460111451203424006031a024032000c1d951412a480c142d000a40b8288068104900c17030200c004c01000910300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 978413660 1250 978412410 978412417
    0xc020105011a040b03130506041a010501020a02061c020c1b010212041413020c0f060118051603021842040302150409060e24010e0f03100216060e010c05 67
    0x880046135690740c1d04d4513441300601e82d803034100501a01404080c0030038450116603c4419020b00445c00c80390b030340d80e403005aa17180034046009401c50000d0055402c0c070280b00c0305580390543c022501610b802a4005443d04280d0703004051010044050020030396540d0401c68003c100a5812205d40f9003420031481900c4d071030381508014400c195981500249210f41d4042d5040c404a000c100ca090801c1500d603651504024003c0b92000320740c61950602005460080713600071070b0401040d000c0081d04140840103035100d41002c41080442c0c2c610300c0d01544441034101a6080055402a000000140742c43d003851202c60184d906403400e420718100c424000d8045070f044980c11603a450115061044000d440c0c01254080102c0e1803401c480004e001c12030840481c80b80301004280b81d240c10b01e04040d0717001012818a4280091125101c1c8600c03030805070324010301140004c1c222031010780859848404d0381c1c442801e4217040c603220040b5004010960050804500c0e024000307216481d03004800038a51700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 978414910 1250 978413660 978413669
    0xf0d0c03150e060124020a1b06020c040b0603041b0e100603050604090b190609020c0609060a02071a060607060f0213170604030e0a0e1608010503160e07210c020105011a04 75
    0x3010701919045c042c001c005114034030782c2c440807031181d4980d802d8099000e200300303104032000340c0107038400e10340710340fa0522400908480007400c1a003180c41d1503c40700c1c2c40007400d0600e800e04281c0a0808960381010500c0d5520940c0003241000340a4104140202650405000c4034010b41c104004007000070008541154002c0070050440f140900c06403462000d086a0360164800510004902d250306a010815512400c481c90490b000c03521000c282000304d1207941c00207800b0b5280045078000015156007541d800ca40300a00309820841070b0340b82d41d42210210054407040c41c1e0300041030010303034038217800080080200059522104502c0c03800c1c1d91312070500600080c00c002d400c00031014169119420a4050900181c00030b00c18604aa810100a40480b400001041115000007074030f190000b00c40c81c00000c5d05008800c0e403031030190200f15040d400380c40315060241565045a48201041d40004480003640010a01500c441c101034212441a082035400111401e0b840100c04e603110222003c0f107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 978416160 1250 978414910 978414959
    0x3172703072f190806060d0b010b03280c090510170403020f06070207050a0510020c0f0103060504090506010e0c0c0a03050705150112020a0501020303070e0f0d0c03150e0601 76
    0xc400340c85050b0028040e050041e6000382680301d0070303000c030030201d10460075a101c000840d0759540741d00c001c001c500c000c000c40083c0031049400060050310b14403800340d81c02008200d0400d030b5070007084045681e130104800306c00320754a66031046a0b44036940038140200410040d80d00b012941421600141500c010021003208010700ca03011030304140c800c0003c0300e14070303c0200542d000380c02d0060b8000d407200b038144245d0380724030842d080216152804c1c0c03e2081c203065094004000c02a2a9000e02098020078190319040c1562410f0000d4540c1b500d0203280007007440341d4007800441d03040c4031070481d00c500007410136800f040051010103403100d030015441448a0701420110f4490040d460038900d40561a800780070941c0c6100000101c100c0c080748020a140d03c01c40c0e285c80c00076292001240d9078001150940002075844400c0c110074185160741e640f00c1940a080c000408400d622907210b400d020707038011500007040340503140c42949688904800d4605e00d07800340c449540745c50140748009001d00c5241405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 978417266 1106 978416160 978416213
    0xe070302030a030915301401060f080903031323100504021e031e10140609010909081e13060e100201050c0f070317270307 54
    0x35001800369201b02182c2e240d40500e131000a108110109540d60425561410007442045020308074540300c00d107083d82c92207402040400e00400845443d00140180040d0b40c440060782c00f01c02d9001b401d079082200d0000c20300000a450000c01584600c2000c242e403140f111f007504058420b034001c0300e9a4085028811007000d0340c15031202c45680c540c00003a42c0306c07501c0c000b81c540042c170004040200c800c01031030312205a089503082e5050070040000c4104210a503d055100c1c40d002d03188000060100d88501c0d560103109000da95002807039964007241c4203054a1002060303a9215031081d030000205641c410002d86621529140709009070310300c509011250340140900b87c01810704007a024988401d45507404469048400c049081015028814040ca03c240b01d0490003100c030304012a00e07012070005401011281d50241d05242d800c1401018041004a03624024004640030020300c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 978237410 978417266 := by
  have h0 := BRFrame.cov_init 978237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 978237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 978237410 ≤ n) (h2 : n < 978417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
