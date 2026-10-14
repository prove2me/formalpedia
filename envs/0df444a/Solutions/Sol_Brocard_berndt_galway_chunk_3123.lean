-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3123
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:43:46.725781+00:00
-- url     : https://prove2.me/submissions/f432bf88-260d-43ba-8eb7-089cf9cf2274

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 561510791 ≤ n < 561690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 561512041 1250 561510791 561510793
    0xc010608070f1e1a070c0914010803040e0103020607080d09111002010b03030d02071b090b0307090b0d03121d0610050d050307082104141b030a060504050a060203042102 74
    0xf031448061011640144944204443c100140f80c0420700031008803a4040e40c0590444a40313501c90741d500c0d004017034110040b5040303141e020020480c060b000080740c0641d1030f00f03038941042e13030b11315420030840742e01c200c0c1c0440f01c510042c0200c40e4000401e004000c0239074071603884d2280d8030460409010320f01e0080c01d4172100f1603041840c902001d46010040303441d55294484003694071340703003414040d00404e80070801c0201401c1088000403e5a2a644203041070301d4101c044e6241103548a54500949a0a03e030580e8442466002e500c00070b03006014400800034400b0f0f010a0752843c18070b045a0104e00c0320a61661508400108558105a0f12001015284c22180c55102c042180c1302c0940d603016004000301921300008001d08101c064044c901c6602d0341144840000f443e06151949220400c00094400f174070800c0c13074604d641c020528044000701006001000c1604140d183c00c000f400d8040d00545980c014003507c3c6010424500007144244d0043c1c8903103a0200b803000b005541164000780c0c4400f1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 561513291 1250 561512041 561512069
    0xa0203031819020f0d08120405150402131d0d020c091b2208191e031b02011103030c0316020708100b370e0121080c010608070f 56
    0x240720200080d500c02d198056511500381d800000219107007901844002d031180d8804181002c000302c44c0d940103031046114100360341c1a43c3d038080c0d0802640c0e0095500039407010100d240103207600f2155019514600810000071542d0b100360001300c1c14402182d8050740140c1040e02c01910500300482d00c1e0350000d120000c180048460030404202c02c1c05800a2a80040c1501d166a45a0340039000d505003d856207100f5a41940e050a00b9903201060a45049403400c4080020211001e01c41000220b001c0d015210003409030070303420100307840400c0d40000302e060000080070442201d40403c042c6202e8190082d4141ea43d040c0108201e01d240302031180041154442c207814000060042441030f083c3d44003a001003400c4940100083d25680740c203000400d640440111502610103101c5417403521810040c02422054a901203c001b042090040c58101c8072994014000e00030f80e45014040640100080c07824030310900103690a40700540e222460b5580203000034410300003411128030042c80d4403c0c01d820 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 561514541 1250 561513291 561513313
    0x140a05060f0307050c030c0105070206060901060302031303050c070911090415030f0f420608030f0f040e01080304030203010f050f04030305091609060e09010b010c1205040b0a02030318 81
    0x75031000070280020407101140042c0009000c20907280f444096000910091404420007075030342400b114214840c809440001800b180207208881c040d0355065007001401c0082d03241a6a41d0340725401c1c00d04140b1851200269169003485441401c6014040301540e812501c010030054a142064401d160292001c04100081d4078a00201e82a9400400c0c841d10300041e080c540306002400314411070040b05009561050a0021180d0805c02641944281059004000c4d0340071101c039402030114075801041007011291509014054201c03c00341c00700c1c9899100c50740f18401003003e0380096901e0388003040500c00c603c2e00780244d030554861182c04100c94075107000e50000802015102500741551500402c6110509008114000950402200489075920036080092906129038034244841001040341020103014452510805a60b000e01080316500d5103c09001041d0001c024000104800900c581070300003d004a44220340146889190800b00440301c0d0b82d202d604148140c2115003000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 561515791 1250 561514541 561514567
    0x90105090a09020d0807030807030f0c09031704120f1703043f0c0b09150106050d02131404200a0516060e060103020a060c03052b06140a0506 62
    0x1070380c02116080302064900d9a40003040c04039680c03103000340c00700500258036000e06400411040c06001d15030b404020000c00350400408030b458a00001000880d021010400b0400c240e105040410b219400145007036554412508076070b000d08401c81d118170040c030000040c0221508403e40711000003211354518941940c074010b009150040392444390040c8500302040f641d101e2040710041d40d80d01d101c3d240a2800201c0500600d0a900b021181d404894000500030103001c200482440e0205a68103e40d0b42000c800340c5142d004815031600141c0c0c20b019201030320000c0031082c801403000740c082d9000d000d01c41c000d003c103403601a411104601c1d42c02d0264a10032882000312850640340f40391060325001e00310100d6503034166411014110301d040212440e4a0200483d03000d040301e02c02c82e4112134032580c0390000e440e00c1c13540b890301601060050150080c88406080b0020103542143d4890400458402000b000c80d40b840c0c01002048a00826040150400c840307054060300048500303c1c20311118580c01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 561517041 1250 561515791 561515809
    0x61b0a021c0e10030e0d0c0209070f021c081803190305090a0b01032102060903031f03140c0103050105040b03060606160503120403030b0607030c141c0801090b090105 73
    0xc03080411200c00a80c0040d4450b401d800007840009001c07680c010030250300103000c1c01c02d444a480450188294003180c0c103000740000c030310960740905411290380d6010390565880c0b031007080b00e0080d0301400c410b0030701000b1100e104e08600c501e6601c544459060031440e01c1d0b001c40301c3d91907500740c55004100080384021403501001c1e4801892801140f1070340d41c05212420003040800c0100b05590304c40c000b000300560b00e5400c1c0c100e00c00400342407007651144001241e49103070943d504c540c517400401c04211070108141e401b902a1900528104a242d40c0f540c501c074500c1a481504204e07600402c042040070343e451b014090060134115010300409a4441c0003d84500000e80440d1141100290341c00e030404002100030b040310b030418160703038590138554601d546190085a007103002a10f030001303482c0d242c600039054816664141d500e02c0314141a0760384000001c0312031300e401300c410322490301da111101842e410507011b80c0c078541c1d8400d030413945455100d02c20380c0d5102c00c40a105660700001030149448040c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 561518291 1250 561517041 561517063
    0x1031a0f0c090d06060b0a0908100b130b0409120f090608060105040e0a0b0d050a0302070902031b091914010e0a1d040c050d030509090603010912050d140405061b0a02 73
    0x508090881c2850138000900d045da00c100001c00c0c0102c0e849a40507003042000c0215102a020389500c5400d2082c26811201504207a55201c80080e0f00305001c3c80d503691150002d50005400060482460b03103900c00665054800e00c40001c03160501d041410794015400d5008112908003d001820700d100045c00c540624000c000c41607010700e000503c5100d46800c4800c1030030018011030004816810640c0c0c4400a02d40c1c1a070240c4107003080000d121085100b1680b041780f10641e0762809440603402c10f03050740c1c0400199031740502c10408082c0104008502240104050ba2980001c0c4881800141c03005030b46c44003607489100d20000401c0440132401d9103810340f130b541010441065880349010201d600b215000311350440e40a403a08410150060020140400d00700d41c20035050345d41008050aa4440080041140464200c1000664000d0014010741084a01e000c1842080c0d440405040d02c03089406a42030b610502c1070144803d2a038070007142202d14810030a24000310504065030303d401d4120 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 561519541 1250 561518291 561518299
    0x20c07120213092109150c0515040c030303111308030408120f0a031d0a0803010e0c1603080c0403020d0609290606160b15010906020a02090a1503050601031a0f0c09 72
    0x1155014504c226040070180804011b040192014248010071942c50050111682d20440c5e603140c8a4080c07411540d0321507a07100840101b4141180d60031009402000100458078000303000c0824074121409803500a4201c2034021b5445e207160051161800e440d601c86a17107080b100700a0509070f00c2d41e210440301090460b003404144110781407040d04581e00b01d0001c41e20280613030003804040101c1d20340114100c440d00c0520380b0307080d11240c400301d40324880c0c9440100d440084e80c4001d40001e014400e41a80b08181303011090815941e0b4012034103001c520281222540d83d42e20851003004405103105c2a081d0035440b00c1440361031040d810708040314016006070300c90080854420320300e0a00050040d032060b4402c0010a444c1004000800380c03c91480080c0d0100f80328141c0450090f00c00249804c24a400420f645110346640d4020001054039220048444407011008004503404100312402503125420070090550403964030302003000302803d0342c140440031600340721080c2e00280580f40c032043c04071 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 561520791 1250 561519541 561519593
    0x90c01031104180203040503120415060b03160e040209060d020c1006050d030e04090218040b070302030c040e0910060602160503120f030601020109022206090b1c0303020c0712021309 80
    0x4140307e4614080c1a910b1102c4112120412007000341d00342c494080100424400e110b03c54841d041c89103180011a560000c1c42029500e00c0302c00c1c0d1084045450200700600010325008019000c40d485600c01c10443c180942c0008038800340701030410620048801002c000c0001c94240000203454140303a10014040028840c1e80d00c1c00c40d0b80c1c55022900c5540d0091503010014070041c1e1a40f0044000c85d0156203078041500015103050090007100e01c070b00304c1544101d260900742004406402c0e009800310649108101c0510b00c810700380c0c42280042e00c056001040f1500c080c1071600c0048115030051402508038000c110900e4441c207003960741810980c0040380e204d9641200403801440c007048040e50048081001294500140f051000da032510f5000c20b2010396124582c40381980d41c07114446400ca03c41c020f55024015115100004240c071914025103032002c4038944da0316002081d00030445100d0004c0302101103251410701c4aa050407003101c00e0020b8850750b100d013178840c500042034205044440c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 561522041 1250 561520791 561520793
    0x108010606171e01090912030902130c0207030c031103070614030103120e090a02033102010804020a030b010603020a1101150315060e01080c0f1f051b06090c0103110418020304 77
    0x15001c002c544441e5042070700d81c04d60f076401105e405060407003010f403140101d41c0c01840c42c40f13210b40541c22a00fa0040c015a5040d6030042e0084001d010308031443c0c085015081c00400040c0c2c81c0080e06000350301848400c0002440c000400d401c048065000d40140702c1c01500300c0c0b0a9000201c00c0d02e0440303800569800380d503c003061090320170242d0124441d601c07620010400000d0b2210b070340039500402c25000070542c03012005da9000d040c1900b00000b60950038000494100540c49445982d0b802440984400c021a50b01ea507a284901802c7e004100801c1d00800e04c00c803120380c4031700340301000c6408000070311101300c100c1070280c005401408050804000a00e98060554041d0040c40082514410101c403a6940c0c0d120349480c0e0134140b01c5688502204d10920100746885c0c4100303082c5401400200c1c0070008160001d9485910444000050840c0c09904000c0c140003405058407454603070014010401d410b03c001021112268400b4183c071301d0520041c41585c1c400c003441384100d101e4460041c0d60740c8407 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 561523291 1250 561522041 561522061
    0xc120a0e0d0c080d050c0714012006040b242b0503090f0a030206030f10150503070f02010c120b1801060c0b06030d0e040218060d0e06010801060617 65
    0x80854a10342101482800404202d030b40a16041210100029110500403a03c021907a9220380030f040b84482d44450018020b012801c0d03002014014141020000054200002c9603002244c2c01c151030703160401e03000c200a200c030000b55158400016039202c228030729450104902d99005028581c00742e0198055048039003000502d40002203800e604900040361203140095607a400382601ca4022104c1400398a96420000383c0c0400752580140700c141103540b40c2205114807140180007458500080740e00040507204c00ca4549411001950b45566074600704001a101c420001c40742c10440e031604801c000015884021010105e00f0441c020440d9048a0000381000110301100d040c141c4901c000011188d40104032108800d104503644040ea6585d80308164031601c0300c0000b000422070203800210786140590092174018031681c01075041030710031404140f090700000402d01e282903403800120050881000098014120364009103e281c2c200303100185121800b0000340201000d10300413800c0b10354 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 561524541 1250 561523291 561523307
    0x3121a03070b0414030f0a0b040323030103060c080603210c1213060f08060f0d0f080c0106080a05100914030a030f0501080115170c060304050f010605060c120a 70
    0x2400900301d60085844115000c441d502621034111510140700030b0100a0901042c6240c08048040c041c081c2d0414949541a036140300501c2201007010745200c1c100a00350341c41c00c86c901c201e40f400010b40c481d8110b24154040383c0041c149201070000c540200b010b641c0d000510180070b0035078121050700c0c15418219200e80342c0140c03a07280244e40035015407509c40b02140000780c50200d542c2e0301803541580e5a004195a20140205803000043c441700001c2ca00b82000400410304450141c0901c0350340c1d20740e031140c010044640d0821104c0c181c0001d50481071000c01d000364405002114080c08188100d90340e410313611305268000c200707a5a207820b0148140b02140c40c01c1c080d2641001c056036034880381400300400170404030704030000d09440d010010841001c14400d11000c088025900c0c442c4500300741018810881c1a010300d076040c03060380454511030b1140d10145008074071490091600109001026080d18125081035000310000d0000100403400081c00589040d200850266076807032040003143c8a00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 561525791 1250 561524541 561524591
    0x120c06070b0403140c0706030c05120a05060f0411310f030611040803070215040b0409140702010b030307150b1c06050901061202040b0a0302040905070317070312 71
    0x12102103040000e00100360030452080d031003603907a086458900440160740f07014040d02d0003869800502c2c140009070081d0f1140f0b5a03035a00d81402410229a030b602040030550845000d0300c9580c5035000e026240c200b13190121000001101c086c404540c50140c040300d20300a040394003a1403a43c1c0091009652001c0e004002c0c4021b401c102c030f510851f00c402c4401d46000d0640f004461040c54444121180d40c1c1460aa0301500c400c80301451604d6056000c00c04811020f01d49018000c0c0208070000c1c07015035403001400140308042d2f005c60360f001300c03900e1181d11000040c000000d59040682c04c0031159004011988000e52001512180d42c0c4500760800007880c2c0780b01000d4000515601c4ac08004c00c0051200790080e114110900c0296a080205401e03629a0f20a03120707440141e099080061520307410000748207002501200c007841c0d0340d80009056401c190b130207a940e60012102031051000f03218030b41b014444201c1d13556290001e10358005140680e03100c9440105c80d41e40260160351901081044204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 561527041 1250 561525791 561525799
    0x142d0406060308040e090d03051012020310050a0e010f02090109060c05071203030f180c05010c051204120213092301020c010e010204080d0c0503072d151a030606120c 73
    0xa05d86512040307450101c29110001c0c2031080400d84c0d07508610038001c851003003100c0406900c05a06c0d207210881c2044030224100d0345401180d011181301c40240c882d6078404c6000c01804610520b10400880c00c58950355a80d040203401000039005a0b43c000045400300d07000342c9807003884000716092a600b482101d400084184580d0507090042c140c0c583c1045001464900b020071101047c070a005060340186c18005100c0880648100070b251300910341e03224003a010700203079152842c449414682c142e1040d003200d111744140200b05015410714205510700d0016542c810010020291039a8920003084201e22075008007040e130103008030800790140e520700c0e039203003009108250b002c00c1230070b022350403c0c09828040d201d80c1d20148000362044501449042e08039014620384080742e03c9650901c0100c140ba00541c0308801c11444201e5560112550850700500700000d01a01c5206d4200c152a4100c804a071001c1c4208400a00c0d941c000c291250400030880f04a00c805101a500605000b41d8080160344 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 561528291 1250 561527041 561527047
    0xe040614061e0d020702130506150c030c010603080a03050c0f090d08040b0d050f0c1c0b0d0203151501050304081909170f060f160f020c06030703142d0406060308 71
    0x43c2410703005064210f1086804130b443c0034040010804580c0c04503801c50b4400c031144110902c0b4103e5034024601ca242460a403803030b1610307880c419801d550f282c0e0300480d911080000c205405941c1441030b1a004200c040030149042c41c10400d0030007600641c0d81c01480741e850b5480200c1001300c03c101300c1d40240310800d1a551900d40300c00e00100100f1080b9600284001c8840000c0d5601c107001003290703038001d07003a600003080c203000c040b070704005140328000f0b039411151034541000581e80810480d840450600b00c0300300580ba159901400c081614004141407003801e200340400074202c3d5080c1c455224111008003450051030008172210880c41d4081d594508000c2d041c100e1820740407410f010410514004c42e1444c1d10303a019404450b0f48110361b0715091207000b11404068a02c11b2034212000380b1284100c0c0c0304a44203c0c00141541d001b5507511000c1f13991112104500c0041c0914241c1c49900c040c1094654100500503090320b00342881c5282c51100344000203001c100e00303907002d00d01440e004003007030761 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 561529541 1250 561528291 561528307
    0xc030e0a03150e2d2e0b0a080a06021c0e060709090c0503010e0703060b030106020f070e0112150b0924090f1b0f04080d0207141809010e01050405010c0e040614061e 72
    0x5e0200c0012103011309801c10340c000031780d030601040700400ca94140c03000b4030090341c81e604c50304000d41004c80b1400d50015000044048045a40951020100705034054000d40c20440d00290500066038049900781e070500300240c15a580140c02d90b03045421890404c1081c3e51107100441c0200590740119049170008000442c45660015030340d030030308002c00101da944644400751700040c21002d104000400c003200c0302c10400a001c0b81948a440780c1c0414020441c00d240d0400590310460845c0c1610034aa01d480300c8085082c014910075400410940d03905085040004088400c03080080070819008800c002c00c4444007600c0045450050103150240d4a43d03071210006a2505030070080e8100611401d0310104030069806012094020024040000203103100d041914240c002401c100f959561540000b407458002c1c0240c51017244524000034410880d0740001c0d165948061541c0d0040d49000002c1c030000000101c1c481461004540541c2c49003000218014201c0088006140041010070084 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 561530791 1250 561529541 561529603
    0x1090b150415051c0c03050a03031a0904470103031e020309090a020d0e01060f0602030a120b030c0a180b0f09070c030e0a03150e2d 58
    0x40661011a000e02c075142e66011800ba00c2103a0307004040c1d20610801c003100b8001106015504601c0c400d000203001981d6a8403054100312801400b130700403d8658500c01c201035000c6014141c1c004048800c140e42e400c0c0f9454100c09004ca031407950282d20300c029105d2a51154411640c00b080c4480383e0329655522407030304840c0001a080c030044011620030640200261a056100680d80138030768000c60038485450100a9020800b0741483d040c140c0c00c02984280407000d020300364840c900e0360b0010410071300d0103c507620310301c00640c0600115041440320f102d001d54440200c2c404100a100c000c60100750400009050441c4848403a62103203503528001851484e0a0181d211515060710400c558258201488180c2d03800003071207540224440d001840550040705541102c50003450b04542c020840c4e0041400540703990426189155071120140c0c00800d98025401221031000c00b400091042001514001c840c41d0400104021801c1101001040800911001658046100c0710071a5a03980300 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 561532041 1250 561530791 561530821
    0x1b010e0a08120f0903030408030a06090e031309151a040902130e0114131508011a191a18061207020d08190f09060c050310120503030a02070501090b 65
    0x8035502c2003020000b500c035501180116204000c500003440c80c556541e5500c40c2c05601c006c00e06868030f540c0c2c04000c50810b1461080f9424a0240d4005542d500040d8141d40786100055000310881c5040032020140c265401749101c080710054904440e296010110007012400b03240c0000540174030100d400101400302c615480c0403222280400815a62511300c03c401c01c401c2460466002521100004c554001c1d9a0040d11400403c024284806850b21420760a60b20480e02030513211214420b0f1440d03d10306540d9460703801c91581c0c05141110315141010101c2410300b43d51501e0304d0400303d190038000c4441c040c4000308820003011241d80e0b000304200c416074440c094034904011b11440c040344548600a44c1cac1e00b0b00a80d15018640c0c0c1d4142a0000c070405170001c00403240c00961940d0280c00004d400703004005c0b0640b0240c95080e103d24020600000c0c146c8243e00511020754580703014070105101004036500710108080c0581e81c2d4044d4100f941c00f52600c0b000007048021802c0801070383d542c080c012 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 561533291 1250 561532041 561532057
    0x602041a0f1213120207080c04050912031315050109050c090a051207030f0501270b0103030e040b0303030405060a2415110f010507030c0908031b010e0a08 68
    0x1030551280004548241030060000340500c4000c01c0000b10700c18002c0c010519402009405050107040c2c582e07860080524100000ca000b5074841c540030b100384c00051001c5640b582003642c0c10000c82c5403801e591a51131036000070901c001c2c04000085211501d03452403031080540c02801800225414114000c02840c09114044c0b4291900e03011a55812071710301103501c13140004081c00b09071420401003088a5800070811840d600c140d440000015020000140450b40a00d0000510503a0000b00f80d0f0980c4807141081110300081c00303440001801c54102c18150313505031814456030300000d4007140090901d880f030b05625101c0407007000204100003903214807600b80100144000007005c8002203030560040c0300c4031505840c1d0041803020082400c3c4e682100a43c52511000d402d00bd940b445003000820894034501e0f94440d4208564590580101c0c101341100d40b915980303061802c10309545900502200d20784400c0c8800d440540c0e4a130941068425141e82c40c1503c840c1c0c04c042c50486035941c4000c0f0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 561534541 1250 561533291 561533309
    0x70513050a03020612151215150102070303050306030703020607060b0f091302040e10150e06190501030c0306150201021b1c050d09050d080106080f01240504050d060204 74
    0x9408941414140600c00440f9405031080e818801800035184008200410000e4608101100c004030b40ea10199a00b1201c007840000e08103034802c0741000000014010140820030340d51305100e080e03d0742d00013240340490f905450407546036140d00340024240300043c1c1c4003a5002d140412501d00b4001690701019100300c00316050b60307444a400007030003a0900200c81c5880300c4805004240050704040d0403406c003003c3c01100350703000070222400410483d081c90b00c100340b1a07901c0360000d11000e24400303141c0750440c200704c4030b81c00c440c0c1404180c031050490034000e103410035880314044c0b1502c03802500070304060700030224210340320001204001c1c000d40000b0740c801450072480c0300c821280c22004c9403c100d400c01909802984000e090030a80e80c9500c1584c801584958030494a008114244482c285410142d9110030040d494220001d09903a0007070480f11140b00c82d000100803806148a82d000c020310784003c0e4211509103181c0c161014044c40e4405070b00000410002130410100e03500500a07507056031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 561535791 1250 561534541 561534577
    0x206040608071b0c14010e042c0102120a1e0c020c031002070c050d0804080703030c0b07020c0306071b08030108070911041505390f16090911090705 65
    0x40740c821400411207005005111340700018000701d015000700f40e26984060604002000303a07000030030116181501154440c4c00c01c0d01b83c1c60750030040c165001d413621107140025424141010401349800c070700030301556009903644503849025107440c42c01c24243c10425904101c080305c101e40294507403c400d02421f21a0191159011704075000c6d10070b83d403c542d00401800f14140c100300501074a40c007221000d0f1130b0000288000200c0ca0003c00491029500c01c0d1b4503000007a140e03182849940c8030203880340c41503412054051036652400500540d101004d890045031030100e050f502c034010003015101070880c0300000004241e01500254035001c8400c142c204104400d040c4102e2241070203140600c081d810301d80b01c542025607100324050011000d1107410070403182000e440c01600040d01541c5400c5e074441103112402d03c0a010b002010346006c4c035502900e2802111694a00b036150a07002e641d0750740e0780c1d820504003030004001210b248d0900c003808100d418140500b000e40f4680049111081d680440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 561537041 1250 561535791 561535817
    0x60504050c043002030d030b034b10140702030703050d1e0203010915050303040506070201111c3605060a030e01050c07060f0207020108040f0c03020604060807 70
    0x484100e400310350710030004896050700041c81110005882e5410001d5000d03020040000d643c0a205581b68103031107032000184000014240350918040a150014a01109107044402004840e030804001454034810001b031882080f0580746540d0146501c6a600c5800007500202820317500001800300b44c00142a4680da504c40101d80c2d0344501140100028000e0102868046990b040400c001c0600685056202002845c50f4204e030000d9001404450300d5001381001912140800e0019000a03000b07145070070f0920780414418800c09034004d04115012401c007092080c1402130150303084400e0024000c0501c1410b004001501b408501c2c01040c082c3c904005d6a125101e0a244c411229001c1c092030051030001007100d140c01119858007490f455503a42900350000307201d114414a05002d286440c2e50850500300102c07030107650b40f000481c1c41000b0304401360382c01c0310b1040d50095000d110003441000510384040c0a41107580300941206000c10b01060b010340106290b0312503402075449142505017 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 561538291 1250 561537041 561537061
    0x4150b120108030901021509030c060406060509060d05030316050d0203090d080c032203031b020601060f14040b0309160e0f0a09020f010f091206020408011401231c050106050405 78
    0x2580c1c2c100d400340c2d2007a804140078203514202694440310322009c3d28209081c1c010040d04209048a0884400395520410302441c0fa0041c8515004241550300c20998246507503815aa0b201c090504c65007814420701690b0500e100394204c420010700030100b50749074206240001d51300d052450340c040114031000000390791540c501c42030b00d206200440405203422000003180003034002c0070b4820340c109910b0754101010b040508440b030034864503035030007881d00c3d61508200034a0200b41680c100108494070f00114284c148c29000d0301d0940f9814280990b6030f450324021913142c0b1001100c441d50022440070002250861008118426002400058959520074076800e0454001e008020f500101c80c400000c041c1d40f058407201c44a030440d0603c801d20310f481e99500d60f00c403001100102e50b610740010302440780e08070a0082c802c081031003c0090015505080308054041c84140101c2c803d00902d96280e0100e56030380f00c5801400104440c0510800035608009000e0816030003400e0040e03080c10041643c0c420 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 561539541 1250 561538291 561538297
    0x50316050906190303030b0f031b0a081626070801020909160225081b10111e030d091b0501050408150402040b150a0e0604030f080904150b12010803 65
    0x20f0300610480c240c15590305500910751444140d410003c104040c29403510100701100c9202203001425071103050840820a00d80e00e5900480e4158210480312450058660010029030310410610399078007114400d1840071040303008804c0010701c80c445001480d40d0f0103600506009500790341d504941c1c1e491060f4004003801c3c140400380143c1c00000105c1c07180940303440c0c541c15900c8048d0071400700b40e07842c2c40c4a80340620202602c2c2e40328688807044c0a07940b400d2a80380d60801620b05010030394150b040d0407141c0b0ba140a850352081607910701c05914001310f0510450785046181181003281d0b01711410002440401d500c04440c207000c602e28017251560081c410f540482e420354008050b200c1ca41007581d1288013010304101c1e0415100c02403104070703a8800b08602c0c4541d0000c45544c0d01c03000420701c02090340340b41518050140e00208024804900c40711001e0b0802908a0b0b0190b56503964000894000d21300c9900c1100008a00080401c2102c251710040c20040c0c070105e601c01c0d29989424031750ba100c3c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 561540791 1250 561539541 561539569
    0x1e1035091b0a060e011701060f020f0c0907050c0102041d01080124091d010903030c08100f0902281107050a0e010e070c1b0e0702060702070b090604050316050906 71
    0x30b03a4000c0410070107204503181300703500c001894040f04644101780c915004900c01c0c0c0249012840500400c120b1075410010b1500b0300300068002c10720805400049a882030010744a201044400158007010003000d404503001040c1d11210001480000300c1803104a000078014400e4075420b150040011401c000c0100c180200350001c1030380c0003031408201e40000e089018007080102c12601c1c00c01c02462007845140d0080e0b000b80c6021941d058030700e400800c0410014060400803e581c001413003984840030544068420103900161788020348a19203048200c0220398449450310071303000c1c0d803680d507005550300400e1002004488020340c40b0001c10030f688801d40645e441507050300700100303c0d202c1c001d88101d80040c0c850504259891042c0c95280301c14029030306901544010103c2000f06411144185900500030310141000d4280010000e494171898460400d200e41c010918907995074503081203034010503006040701c40440c496405d10075400c546101e0148501d000c400080d4030303810011100c217446 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 561542041 1250 561540791 561540799
    0x40812010f212103091b03030816170403051912150e0c1b060c0408070e0906040b04020415090905070b130b0d0209060301030803061e1035091b 63
    0x854940315204103c0304410701400c040507241e502007401310703202c001d860416030180160144010300703508001d845000c01070443e400c86007801250f880000c2c4d00660021801c60b10003104c002c50340322401d040303490740100822103d03000c088002e01003c8039000402025001003180c5d0a200c15511081d81201400051040c988043d080c1000680c64004103c01400610205465100a4035650002e40c0c0780a000322411415140c0001e001c0c45010350030801070000340b800c0c94600f2407510300404807d03204c3e10040d100400f0001c80e00040340855031950020000c100100381c0174040590780300600000780c8181c49d0b06035480c0c014041c011070400c1c1c12604882c414a1203000359602280b07000081c0980746e001040ca50b079610b44c01d001a21940da00d5400a50086008900e115100c0c24007400300f141043d809261080c8413000d00f40000b502d611032028803000e003000d0f42442000343ca521952445600a8600c00441c1c030311600d14003001d603807070311100540201805401c4034000480320340e00360f015143c02d540307042d40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 561543291 1250 561542041 561542063
    0x207270615080a061401050c07090e03071505070e010e04060b03361e0c0301060306141e0604020f0d0c050a1701180e030d06060f181202010305040812010f21 69
    0x1703540140c00604a00b0120340c1181d40c0300d580d420050f005c881c1d8101c0840c140c0e802c00900c010502010340031a58039420740c0b550803c81414000c001034040c1b03110130059414012090071070b00f102d80e03880d4000300007485680e404c01c0d942e00c0e0130314591a8980c07900b882036088951100c07015070744000c0a080080200741d004010a000541391007180600d90b05a130743c20301c040c441c841c60041251828051100118420380c07000c1f403c449440c000d248000d10083c4190020f1384828922076480c505041c1180d04040300307490050769241d8140f440009445040c1c540d02c443c50910701c0b0b80868a50220042980d903803a80d940034030316901c1c210046440d000a00c81c1546480b003110390760113101e6181e44589002c4004c20226864800110184030a4032150750111010850844409485541000708080c1a00710b881c462080c2900f012010208107200000103810103640d000010200b0000d2400c499198105480942e025130b500c5018440304e1403240520b0340c80303021a0001c019128007880c0046c46035070b413104041072 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 561544541 1250 561543291 561543329
    0xe1c1b0c03020603061201090b330402090d02030a080d0b0603070c110103090f030f030e0d1b080403020a0305010e2e05150d060209100e010207270615080a06 69
    0x1203d9000501100d030f02000280000d07410003400d200d140031245c400c060540d290f00d00450300389115a0b00da4080b41c0c0a12948040c110b0080b0745040e84594084202d50050b194010326000c00d00165841900a416204884010040c03020b14000b5012000c41114203101c03405200e800e2141c2400141c0c1c8882c00b0804030086040010b80d4070b54801e003411b206240004150101e83c8903050710584d481350550104445c1281c82c2c1640d6818000c03840c21440780401411040602032000749107091403540c000452500341c101e00c0400c0007441c102e400541d00141384070b001c0d5880381480c90007404c038035440603090300c9884044818041c1c003042000007201022150514400e07860180d80241100400032084403102c154210866a140b904528615003c0d240042c1c42e500140d00b40590144c0884090302400380e1011481801d80e400508042035134072000c64201d000c043c0340c41440360607020201d104240390824401041003010340c5483c002e603510310350706c1c48965110302100e02d0881e0301e01e020b031042e0581c401c804030b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 561545791 1250 561544541 561544549
    0x7170c21060f040612140a200405010e010506040b0d060b0c1b010906081f050603192f0f09030304180c0819020901020309031606141201050f040e1c1b0c0302 69
    0x4a403018180c405c2e1000c00201d03590b41d1521551450710300c008e40b4400180f244050070544170b114050014082062803039410840025503901444c03040140100d40060030200d003c07216080b580050080e141c5050300e03501d0603140161a8181603028890750944040c0c000e0207503204a070f81034101c0b8525140c540c103d031100d1040406449925281c240b40701c1310020f0000340760300d42000440c0300c1c0b07030f00d0204000e45003c01c0607020240c54602d11046401400200c0510342100301c4084403d24032034480c6c0740c2e0fa64244c1442c40c0050782c00391074802d5905000100300003805480398640c0c201d2120b0380c0d0030204a400c0c59034805440c084026216000f5028070340349565180483d6030b00a0480c0c1005004807800d102c0c00380c0c0001e184c54801400d400140c4c0f5219002c01640e50051107001210b070f807000c581401c0074404502c801102605200303072031055001071040100c07519580d020500540041e0199201001c5040451782d01c2d120402a0500007260044110300051084c0c44580000e6408101e280380c1d54a190200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 561547041 1250 561545791 561545813
    0xb0901080a0b2410230306100c0809010806030f070e0a0c0c0c090e0114041b0e040f02010c0314030403030c1206030302061918030309050c0907170c21060f040612 71
    0x604d003400381c0300035a043c81c034991180c58480450704a6019a41c0d150500502c0030106058038610140410146060005003805060f41c041c24803e2910455aa0340c800000b4944000c588048000e4003074920040749202598a440e0f10600b8103403c00c0c04600c6158104075100300040f0005007a45200c801d007440804182d4101d0108240181c0000c40d807259120a6940348040942d01151449203030100c01d840b2000502080c0002c041070000c000840ca040d0b00c0f041891620444003e041100403580a000c241c003801190103c0d41714500d6884c0c41e450246005001404100444004514151100b9000c03400320f01944003901d60640c050031458031001101c158500380c040707103403210030344980348000408024061512510301a81e00403401d60b842d03082460030043c1d800e00042c0a40c1c6050f04102c0c4d5142c2003070320960300300310790401000300b42e0b10b039070310081940100000301c040164503d68013422010581070f2980510021110b2140c1c00c541c40007000200d5800780729001e1070071960321500011980c84a64 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 561548291 1250 561547041 561547069
    0xe011b0308180111040e160c08030403170411150406020a08033d09021206010e0d080a0c1505010807060503070e09040b070e03070803090d060b0901080a0b24 69
    0x1c20640582c0d6030070010f0035a010780340c00e0311100a0104003003001d207400103502034110082d00d00d8480701600b5690010020304404c8005000c6aa000001c0307410184200030002d400c2840340c0e444040c5040c20314000302e40602c2481080e12603003180e0803c80b5080a04003c543c210b1320f1607001002c0e021a25a559007490304010085100b1080e2400394002c104e02e07803e040054046000340a01c207240300381824010307078a078540080e1991803041c0800e00e81e80d50080500f9400a00900f4401700080f000400181c3c2d68030b00d0400142003410100740c9a80558000c0140c1c900148140030701c0310a5602d42c450301080b101d0911031140315501829003009124041c07001550000098030700f0182e406040004507036100300c165421240e0446000c1080855503001d00c01c042c030454120b0107451602d250601c1503036240640e1002c3d40c400c440c4802c00c0c80130410300d98419504800b010306071414560b502c18041d9180e4940c0501030f00c41000d00380010f09904045c101c840c50141e00c4100642210001c0d50611004d4030905107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 561549541 1250 561548291 561548311
    0xe03030a0e0705100203120a05010803070303020702030a0c0308030a0c0813030e01180815090307030e0906010e04141b0304051b01030e03130303022401031509020603010311010e011b0308 82
    0x203000300710313911030785443c0c0d0501685070001c607a1416503501d1003089203c01400907542901d40401442420b0740402218603283c2c1510f0003503214220341c000030f03041c141030041c003d144000c030382c00010402400c0e0780a1071154850182c2006222424001602c0e1080100c0711034a21100f502489000240100b014045540041c175012440300b0000546c3c49160001c0e400106440e0b000741c0400300c203801c2d86228554425607120186040042c56900a849204d000031424884c102c504001504c907449a01c0e02d94003031a0003401445900004d400000e030f03a0000761400c50a00841d0f02140c0010500d407402c03240203a60017001404034822184409c0550180d080c2c40c00d04041c4c0b01c08a0034510b00081020380362081c1030305c01c480003c1e0315525001c1e00e007001e215031244107031440b41002006400020101070440303400c46640315400714481c5a580003000b84800007540b01c48040300100600c43c624002d09403090082e200c0211404003400103581010000c2c6500c2904041c02c048400068030407400310b904020000e07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 561550791 1250 561549541 561549553
    0x110c131503020d0f060b010c081b0313230406121419050615121207060e0706050a12020310060c11100e0910060801150c020303040f1502010e03030a0e 66
    0x140c00144203c552081c1075603040c40304000c40d8140b0009100d607211103c800d00b41902a40c4147d070310005203001da40903840111004c2e60f81c003011108203000722002006c4410b1098401601d801c50b040039002e81540d001d03013180000d140b00c6920b041a00c5004262040c000c40302c10342000c907648200050074450000540b5025600c540708490010381002c1407803034450700180920b4505908051040b0304c4c0301400c0f80c13203850a001c0240c0944004106e203003003210740c141c0490780c1e10b07010309009014090610801c0400c0c49442400103a195008000e0158620280e84803286242c0c014205070590105075950080400307502010000303240035085424005204040c0d01420601000c00290818402b40b00c841c045100441a44103c1c075021a1140c0d1141c5000122035030b680c02c11300000e00c10101405103207072100c0010007402030079005030031981480d035004003265a201d84a45e031001007800c25106910b0540c0070b40c04a90440c0b0700600500c2816009440114255641c816514000d8480521130083c240a80 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 561552041 1250 561550791 561550793
    0x14070f0812010e0604050403121a100e030d02010b0307151704030302031609081e03070507080106050411030424150914070c050712080d05040c0303110c131503 70
    0x200c00a40840041494215501c0d0300d49036520b003c1210041500e44500d00d010200030000c0d8010980c1401d40c1e0340d129000800c4503443c2002c4949803d144080c0341d01c580080e101c0d80c9055406030420701030a02c00d03400d82d0081a40200164285d582d095031040d8141c0004000344001d118080c84098000fa4914001e01c040c0102c882d400003690055070140c00013070b00003080014210b00840c0d01844a903a41c0350980d0020721700740e1010b45403250041d41900d01060300e415005115010019240c031030350424203607140e40c0e81da4840640200114411107001d03900304802c1007281c405001c00c1d644625081042450811003035030b41c204c0c4003140c800d618446160b40320014100807800480200c085c2c420564000780c001180c40d4903000c2c1d06070040203203080101e644120000544003042500c05c94000c21080e03010021540b410764441e005c1c100240b48454941400c0001f0721840341106402c8038026210345501c8a102e0611a48956011640e07e4000e440941c1c0da40034941141d008124040402107441302080c1c407 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 561553291 1250 561552041 561552053
    0xc0a12090309030201030606090b0306060d020708220b0414010e0303430f120905040c020a060e030309071a04030203031b07060e0d060203091213230114070f 69
    0x300e00300075070000c0c20004051045581505c500809040b40341072444806207807050441c0740d880b0090840e4000e150120700c0c2d03641c901d41c5070165040a170b070202540745c0310340c00ca1024000480420240000314140d0850000d95200210211001d881f8030380e040a4103007001e40019208944400c0c0304c580c140c13004010940910000c4030910441c01d00c02101002d0404031031030090081c40d40b400d95070f10415002180d0f1400169564110010b00d170b03000c440481644468181038550191030351040341c016003000e5810802c0b030f502054121100344556030801c1140e4140e0403442da2808101e651464a912009040c4044c089498145101c403002200246c500764a0340d01003400d58001e00468043c034038807c2c0056200302801c0c4050300181c00d1350b1818000c0303454031400007921000c4514001c0c011070b40c0000802e18559090002042c4100d0407030a1941d507001c087c3c0440c25405092003504c03d889c103010030060211696030349030708881d5816900da80d440c540c500c03440c1090742d01809040f1100c5c0c582100341800190 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 561554541 1250 561553291 561553301
    0xe04050a02180315040201080a02090a0b040509160f050d06170307020126041103010f141504140610110f030901091d18010605120f0c01020d02060c0a12 67
    0x300d03000c0158650991400c0702280000942c401c5100e500400c107107140e01c1410061145d8050740910f8a08100e4540c211000024443c0720701032600401003807000309000c1c000c07800910454000f41c800d42c2c01946e0301d6001d82a109111800302002402c03441c074500446103e1000780024010703041c03000404603514000c0680d040f0102d00500055000494448159070700040c50068080308507540014400c0c00d030b1101011360340c004000070504490340c0320241041d1001d41c4440b4500074440740803c1820400c0407000c0c0034241c01c0f540c0c074058404400529800c1c1c00c1501501c035000025001d0b02401d40c858008001c50010241d041030700300a1200044440e44100304040383c40c200080c5c01942e0346040b20b100042040241e0307001510303e140c0e0402d00741118881c07512003543c0900590500103015414a1710103024210a07880380b81d02c50011148450201c00102d02429001d4148040703a500e54458801a611074a90b85500d0f07001d0380080d00082c0b0a0074810000701030b151000d10700b0120292082c5501001c60b4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 561555791 1250 561554541 561554551
    0x50a020d02190f0f090b0d020c0a030815150f0702010e100c02090f07020a03030f0605100503010906050d0201082d0a02030406050903041406070831090c0e0d02010e0405 74
    0x2a402080807030a034000042400f04041490011070130204203502820038000740c130903100d02000002d09001260303059415100035812807000d54044d401503040090120005907403070700010001c54102c41007481c0600810019003002e4000c02c0c10a0881a44480b42c0c1e04940381c2603040c881800380c40c81155480401c0c3c0e80c40854a600e41c50030200c06070040c412142802441c40c2e08129400050062413600041c0350015164145070200307801c1002801d0328040e100a40c800d40c1c200c0701c010700610240383c01030042c50584d22844400c200e519039900c200145801007900290105401c2c101142007440c400d181490451305403103a01c002c8005059000498800495005983c0c0da4080203020411016000c5c5c0c0b500161281c008508007410500036541d00400075013020b01c240300001e850b90400c0400400da40480c41644010161055000f42c0c001081c11050340d00d0030032105211020564405074814070076003420300d03a104130f010001d0005003c540c440c0007000ba81400a8038140003015506c0340203080c811 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 561557041 1250 561555791 561555817
    0x1902041107050f19020d021309060501080705130c1704080712080405010b0a0503120c010f090602041505120c0c010f0f02040f0f30060e0a0b01091806050a020d02 71
    0x8102c2d10091071306101314440a070303055505407440040580d844140080402d6011500000e01d4081101b003038004000000f0003e2085052100000d108030012855504a49040d80c44c102d50704030405140c000ca85001110501040d242041940c4501e4114a00b640c02849110118078000d02c0b134582e50444202692030500284c00002004104a001e000709003494a054400b09034090520001036203c1038480011418140007041004c4d100380c0941000358000e4a40004000c2e1105030b0404401947c40ba00800f900d020144004804072031240341203a44005100e0300b031304000d440c2c021200e00703140e100000b584642e64803452100c5148409105035401d00039007040040c3d4441c60000a4001c0b05510390103600350116010042004071b400a48c451f402103074040184003204595042180e81c140101c0000c0c2c807140c0f506009c9000400001072100a150090141c01e0050b0b1742c50105c64103441c0f20140204081c402400c1102c0013030160340142c2d030000b060070405818004ca400380803080b41c004200300d0030f40c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 561558291 1250 561557041 561557053
    0xd050a0605100522022d09030609060108070513090b13020901060f0203030c03090106030506010e0f060a030210030e030409021809070c0b07080702031b0d20190204110705 75
    0x14240c0d8025a9900401c410748600d04a5010f40740032603181c5007a013008090700764000803e400d81d03001e001100c1e20200304240c0c3c2d404101d15511039814981d00880070940c06842400f0220703022140000b016412207028100506a090030007041c030000c0c0400210708403106485154040c0040c000038580c0b4070035074404007000c1c2c074001035004121075004180e101c40103200c0b085c140c201041e98040112648803001544460f83c907210000000c1c01000b80b42c3c805821400b0788000801c801043c1c08940d8000e080324100c9400341d8035000c003000364801003448025405aa021100da0780c490103601700a0117a2070313560540341001d658910000036079011030f844884d10701316003c01188500d0000c0400d038208007540ba01040e03d00c3d8503a19900c1601002d070004003400450000030300390510802c1261066200c4d00f445a10245210720001d40c1c0c3c2c45010040008980c403900c0013400a82e04003103000b55424400000e15110201c07181c83c403900390300d0240603a00107841e0346032a0480b204c400000d01e02a8070400003010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 561559541 1250 561558291 561558301
    0x2190c06060902031611030d0203010b0706050105150316140a02010605010212120622020f030702011a0102031b030417030301230306150d0507170c04090c140d050a0605 74
    0x1c0720070310b81020006a1061017800014070040f440710701d42c0c14032400c14903190160000660b06d10f001d00d0010006d200d00000000c41e0010402000d0060309201c3d800500c0240d8072a0b0403c0705141c00d40d03021000079002840001d11201c200d032180c1103111024140078a20949508007007407540d000d40c191901517915418100143e590400030038645030500e14000b82004074515040c6080031001c2d02e11446105d600c04d80241c4600c0014220f2190301d09034408543e40c03c85a151071842e03801c1202d440d0055445c2070210341141a4031401c0380ba0980f4160f025620317151114501119042201001c00b015110600c4041440c110b007518003840503880030011502c81d07140c42440040c90070026981e02c40800462208a20b0f9240010850741210000841d04140008880815a00040c45030043c2c268819010002501c3e0190407071190404200401d031085040b0300c00500c010f03580c0d201401440c10503401c008001c00d0004c00021405030718020101d0800c808141c542501d009180c45c07040c1c0b8003a1791101400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 561560791 1250 561559541 561559553
    0x2130902120c100203040b1b120403200609130203131406090d0207083003040b061f050d15080a0812070e010e040c1e05041806030b070e030102190c 65
    0x10f40080c1c07031000314906810072001e103440f07005001900102101f03d0368889003039030040c80b8400381005034228003921282d6908056900100049010b408038034408881020b5040260450300d040c000036190381003004913a05c0d800c00a6000030a103510f14071180c032190001a000c5110400d10000c5c14004081b03600708050000d0810041e0310480302035620092003002510350100e000c1d01d1444000096001c1c010110a040440040c42065503141440000411080103200f0329054080e0030141d405203001c0068010500d82c11a9640c00607011a0342072010b01d0b6041d489070010003d1108100c02510b4890782c0c0c0d021149000281c50307007211115004114030206045e06900b1075805201441e180100411990000c3d1146410303031100c50086448614044a842c012000001d024504110344844040d505100801d250410302039501003001e504040003e0500702e009440550343c00240e070b0601919160001c3d6030001181c0a4143c065400b404003900803030191b0b8024080384800c2d00e9181d6804c84030306e444 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 561562041 1250 561560791 561560809
    0xa0303030914010507080a0c050d180308071d060f0c0f0a050c0303042d03080f0405010210060b090121090c0528050d02120303280507020a02130902120c 67
    0x890342e03a141c00100306405600100241e0040c6461100180b0035990100c101c64501c1194004403900341010410200e48840084440b80140266628829512035410844542c80c40c079158050100361807900040919140c0000c220904105010603e0003550301c0245040250401000c10070b9001448601c0a0280501c80e0050002c0e0480c0510318140c2000d004804801c6030341c80701040d40c1c0361800c61644142e15400e003a00519082084d60f501c40400b00c0c0458007a6016002c1c06005005852509840900d00c1c0580416a4000e90105007400311b42c90045400800701042d0000030b030441d00720251404054800c00c41c1030740c01121080c103000c2c14141030000d2044000d40310141c2e20320383c920310440403215221050548108030b07440b13001c0340141e000007890154440300329405030100000344141543c440c401c00640029513010803c0f100c3c40355440b20103e0380211100c8016030401d4841500520708240c0c9440b120702180c40009142003d5004101591030f04140c070003445d40454280d008901d054680 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 561563291 1250 561562041 561562073
    0x10e0117030a02031b010e16060f031b0e130203040f290103110607050708070608070203130e0c071509110301090f0b04031e0305150108010815060f0a03030309 70
    0x110302d4040001e100a50300e100d86401c14101c2c0c06107243c040c0000c54290001c00c1c0d04070b40700c800c03614098004c2d8203140d2204128800c0d01b010580f0009a00b020318017a0264108010220350002d0090340d0310300d0181e030070840240c405903210800b180b610f09281072520195005901a2908025001c4246020310b03101e200d005e285803905036440043e18500e4120041181501c0e44050b080b80c00030302030000310741d450050f6240241180254140030071446c60005041c0122070070780c0d503005a180c968400a984a128540070003507205588034041c42001010b4420680007485005460710b04441516064800c002d4012902d04c115154107140c014494100300350111004203c008002a0417103540d0a4420f00785c401004014802c000300213018940112500e03021000c000143c054030f4040364200070010b00c400c480400310700c43c00c03950007403540d40705110a6060300c00440052241000c0c20f8058107241ca8001c140e40d07400456528981c03141d07190a0402d000031803080d00d004c1000c80303c914018400e0201168 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 561564541 1250 561563291 561563293
    0x7022806320306040c0908250f0b0f03060a09020c060a050c1305090a14040f1b0605030105130905030c10050f0906041e060501030b01050117010609060302130806010e0117 75
    0x1c9401c1854008408981c1c100408407000200d40070140010350b4214095800031034940521031040001e680c12074020228003c0d4541a400016180c8402c00e40b08803040c02a43e0245006024102e8100606c9004541000d0014684000542d03150a5002a81d0010200d6000d5400210030712210007090b004171508059101001801d10300c87d0035072400690824407030940305204c1440070882c4c0750341e55800040d0060811a070642640381c20301b001c070070950440c00c0c1190020481c2c449084e200c1080190001611166500ea80c0355900e01b10030029401c24400080e0300140d60b90240c1e40005008000400760301c1c80b40c3d4054842800c070103030102d003155030082c42011041e07802701c2000450000030030500d40c050b074411b03400c8101c002090b5003140310130009070008003080e14050021092182440d03505040b640300f66190140019001c4460414080a10400002c10940c0f60706003c118040e80291941a0303140b0300f6003002c0c50b40c03100a01d10b000400e0788100d9058464000511103030a02990b0350300d488501030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 561565791 1250 561564541 561564617
    0x1230d021b0c01140d1e140a02070c0509062106100503071404020708070605070305010302090703090506040b060402070c0b070519080405040b0a030f030f0e0102010b010507022806 79
    0x180c00030f040305400c0190920001307000952202c01c0807107035101200310760482e040e8140d141c4032007000340000c0c000301145a00381e85446001800786022070085900302a80079800340303c124a05014020b0b452000780c40c0c5680b0039455120180c1e400005c00c2c4410800002000a000340c0c00c1031074814584810030707003110f030098122440a204070058a00310075a100416200141d540d04da0b4140010180104040200b0190911040c407140d19850340055060320b0003254018001e40796030005408854200703c006006410400010303010424082c26550700044c068000341ca80421a40c4000c200c0d480364000046029000c01c40b0014407008006400501800c031b55500c1600d42580ca807100103018501c500340c8156202d1400840907242c0c03000c02002181d01040344102c1c0764003403402520300014814510300103446c214581c211503205000c0e02410716010b0b16400e191201c0b03502030040512541440c81d00c449000007580c683e001c51140702200900c1560380707035100f030fa060f070409800c40f20000701d07010601c4e4096 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 561567041 1250 561565791 561565813
    0x506030f12090d15020301080d031b0c0312021b10020f160503090405070c0209060f0a030b06041401030f0302060a0219030e01090503030a060e0a0204120201230d021b 73
    0x500035040300c050707a1079203072076440c1a0002100700c000c03031000400ca0003525001e2400448a5000703981a940f030003080c0e41001041a034210102c56001d80070040c094404101503444c0ca00590480d26500d01030301c0c140079003070001ca0011059a0042c150660700441d500100c4440002c21f1095044c079044d03005c2e0640c948460306c01780310154002d6282c10316042049410300310401c0401c208582148402410901540c42c081102921569005c01e060340501c40c41c000065891810401641152500a200301c0f059429601e403810400340013094180c005540b5035006062040100c1403034021845040072101900035850b0003800c00030013030020280540144001005840160b1030282608150720340059007142c1c050995000d0001260003502d5400f0001c00d21842005513001401900c0105469480c0c42d228441c0c024228071407489000303800c2d2062401c0000540c8a001400498130300c1c1203a60740f4248540414040e1030b0b01800c1c2c1100c014ce400180c0d5441036031540c01c0300e1551603201024003c01c402d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 561568291 1250 561567041 561567043
    0x15110c0105071b0305120c21031b0d02030103050c01120605010c020f01210509010c09050d0b041403040b07030e0306040209161704120905220b0a0e0a050402040506030f 74
    0x140541c010682014083e20300041c0c1c603002084801190003608499401c1d8480006201583c8180c42d94140b601a0b8100401585807110070780d2244e6000c071800c1841c44e41d0b0710f030000040003042d40002a081108001124480c1d1701070010f03502031402036000d410a0144100090302d43c21440c2000c041c55800c00b0002c00c456070b004103001c0c5506806613086c05450040c880100c40340e4400d980303048102c60440340218204c80c5e003580304038468110038000300b00c1590710742000d961003a81c46c441c0070f900c40384140e1080006801102d841e034000d13208040351a9004210901030341103070801e800401034a8800316a001c01c0c950720909200d084e6106070301400e0241000e40101d460100018140c0825044460941071110f214550300d007069840c0f01c02040c82d50a292410003601c0495400300c50029150240114862510030310a00b4181d5100d4081c4910703405070502c51008e401c80d01040c0707074881d82403130002030341480440705640320703200400340010781e03250038130400003150b60207054035000e9400f07842010100b40d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 561569541 1250 561568291 561568297
    0x21e04060f111515061803060612060a090201180303031a060301030b0708090f0d020f0d081014010912140f0f0a020108090106120c210f06020a02070b0415110c0105 72
    0x1d001040391403140d589400c00740703280e2030b0442a01d130005c4000561100c4041d620340d01e10700340c1000318290f40e0151910010803402d403940c0d0f810042a40c0001002c11041c0c003456000030b1290344181401008070002c0954011035048030390099010070f4503440c0503031038510a801074001c80141200ca480c115415070300da40404080c002c010400380710404011400091007007050070000c18510040b41e90f60390269000a4458031940c2744080e491080300c100c2c000039409020003a1003494030b281d5505036240380c504000040c0d00950a440d051001e45039000c6a0b54010144000c1454020b0b6102d05001104059282c41c200130109402d110750020055189190b0b00481c407041d103150240303820000c81d1100e4181c40d0041c2000d80c0030030420203034080008200706400304050101c900300314512003241040410038142d407070516802049001005490340009515a0117031079203110307501c11600303103a07107502c048160395215401442e200517801101c8510151f00101e03000d210f01c481400b0304604140d10002a0080c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 561570791 1250 561569541 561569563
    0xb030c0711090a09020f0d0b0610050d05161d0a170106080a0b0402030d080c04030609150501080f010b0117010306180503070605060a0608090601090f021e04060f11 72
    0x1500040c40d4024007050400e041c9200c6030003004110780d4202a03c8210050104c58001c90150b03c0302d03001e103001494039151905803250040d00b06502035840c4820400f4088010000101340a02840340300c0154201c0d101e043e1185101005012a03030b50345550240000940400d40c00e00020404201500380d100d01605408603400e07001119040480280701c50f01400c51a04a4030340d034491440c09009200c450b0040e640218000d0303041d00d00c2c46c1d6041c1c8049406139011102030490f10410842040003c41c5644081c9425000c0c00c1c080c018503817000305140a8460a90020382542d0010804001c805400e00c0381019200302400c0502d000306552060308114a014440601040c2d81d44900840d440e0242e091510b66542c000280e0355280601e00e0400c0040005407041405000c0020012503480d02661000c1d000e08001001804940c0c605043c0c0000340c030250060403815a0280003062041000e038148e0700c20503140503040c0e902c4508006000300022082031111042023994070f040d507030406010400b000c1344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 561572041 1250 561570791 561570811
    0x5010905120d14070506040506070e180105060d020408011508010f2d091a160926190303020c06060d0c150e061603090b0903100513020a03031106010602070b03 70
    0x189680f440000500640501500314050841000100000400c040b4030035402515842e00426940f0244a000074200303441154078101c502c018003091401ea4040c2502140030f0300d001d031074184c48104071802c0d11070340400001c911200d03441c00e0020110170301034043c05a113030030010042290b903240d02c001c070f000382c0c41540c1816448644000d0030800c1680c000662190300400841e801082007003000418180072501840600e10101003184020f00c01d038070340000c4685008141018052071aa840c2d920500404d0140403072241e12940342c6501c042d1300700640c46070300030b0f14010b0f1200c60b1080440d0030800001d2015104044800c3c513100011700d184450b03c191011600c942030101c20010064801c505d1141c8030942c07220010a44045580504100c45036244c401da4075001c80036900c0c440202940034468101340d05070041d03900e0714038900840e4003042d44903001c50440c4040080756000305042c2d040d030341c200b81c000400c00c45011441003000c0000a004042d0b520040804238a0925455001c0c00050500d02c10307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 561573291 1250 561572041 561572057
    0x636120f17090a06151505040b04050609240c01050105120d05030901140a09050c0a030c090b04180506010303020601240f051306020d02120f030703020c12031005010905120d 76
    0x49040b0811003111803d0380464204443c10725402d2440e0a040c09100d958035200d130102c1c0c18845030f0301c50010b131002c072900c508015040c00d0420741000341c5030b080194110b81100100c5180b40d607502541140c81c845800d8500815642d26211041b83c0c00d491058020034021080030880400e1014000341e0341e00541c5907890596103d4880d070385050302404403a0811240301e6405801d1002400c45544081c0032107109030708030380708900b140b810b11010100ca44009000c06002e08420080740e562034002c919500703001000001d041c031101042548118905070181c2d074507031041c8010700c1010340411425024102c0404541c04a0840c50310024510311740034525001c01840324101c01c107150190741a01c10b01005404189416502c805001350755280820030300c801403042108440c44501d8003421100f400c1c8005032514a142e40f401001c1c0c02a41c0040ca05401da84a0b00000415020070880954010801e2142c0c1803000f925100c00101064a00c0d0001da00c11040c43c03490003680d810014003034171416418101045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 561574541 1250 561573291 561573301
    0x1033209030403050609031c0c082202040203010e16080408090103022a42040215130509010605030f161407030e04060f0b070636120f17 60
    0x4290b020b50303031004105102d91000e2000036000031025003000320a54000036071800110105905440240d161140400d0341c100110b0300e1400580305011380702c41c51540e00740b01608036a021400301e9100341d11420143c1c281c08248a40c0e000d03042c000b60740208884c54103141c1400c00c1c0d100d00300300c2c1c45804446410f240e07000543e0075401c54641d4140c120019003180c10b988070744404004a4031801c100c0c2c80c4030b11030745040a422002c0585034041e0b0a902400b5401c03112040501441c907034100801038020303a88907140512100c62504020002d1411003c00d0315070900e0b040c0742c0014440588410780000003440400d004005581d0011099203038400700008007078840d4001c0f07410a03500003404910700039940d03400180741d209140d0800d041e01d011100640341044220307501c0c111100d02c40304038026182012010030044010807940d400c280110340440c0c2c0302041024610304601840f0741700449014080e0702c0200c03103009010034205010b41d078000900307012a426865440007400000601da000e0681d0b034060020503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 561575791 1250 561574541 561574543
    0x70b0a020c0a0f080c0609010e1005100803070c030b060103050c0f0a0c020303220b07240219120513022b08070303150f0807150c060f0203010501033209 67
    0x401e030340e400141c0e030b0307402c3e20042c10240a940e20041c07007800707280310300000700c0d04500c0148590b280394841034020f0311800f00c0004403240074100180c14003d0b4014000c4022400e44000c1c802814000e00c210079155030305155142c5101600300040500e414586088100080307401001c085a03407031401c900056a5550300100e0035a000e280d50a4041c0d007602c000b00e05484038040c801105080c0004c0c9007241e0040d59070395400d050461240a5005000d00d00c6401c5c45c985001d00600c140d00c081129500244c242583c1003081c50310900070324030301d04c0006c818600060941c4828401c2c2134000780782648030140303448160041804e01c040260030b09103441e00e0503101400a10f9490071560344a0b40801c0340703580e401d454280103000d0090403801e4000300302c1e6200c0025050440f100400201c480d0080980301480c0380c4910500c6045040040f001408450704511001072024403581c901146004001a104d50400000404880c40031030007840030b40900824580008034810400d1455841940641e170b240c0e20401c084e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 561577041 1250 561575791 561575803
    0x2402010216060515120a0b060307080a0f0b0702010b0d080903031308060106030e1609180501021218030418050402120d0503041209121101091e0911070b0a020c 70
    0x203418050507080381c1104001c00707500300d240a8810202c14a01c070364121410403004819000000c001076020342001000a00001c0840c0c1c3e22000042c2a2004507503243c3c4414103142001500711f07801c6814104000412032490050f640140180c40200124490715011800300c1840b44400f6000000215083d41240c0c0c0c10002c8694003150301c08003a144a0761645079541e0f40c0c2080c041e00000c00d08000c2d010901010001d1145a0b6403520304003c90804d02d0200310070010040e02108240d950842ea0310040400c90900040502c00604410001e0034900066029035a1050701055070860308200801c000c40d4200c02c21b0040005034009002030f83d9101c030710001e01800d40c91080301c0c1080c00341500140d8041d1304880074620490041aa580384446203403012147c1c43c00c0c034040c000031210550b8081020034403c450300d0414202c1030410140090300d41f5134104000882c80344012004403c104280081c0010b4003555804802a0a8070f6040908039540c2c140185001020001456400305407207220240801513 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 561578291 1250 561577041 561577057
    0x6020d0603140f0102070b010e1b03040809030c090610080a09021207060f030207120c060b0a08010e070e0c12100e0703020d0510050303090409020f1c020108090724020102 75
    0x3006055a24500404201821941c0c04024040c200321500341d124180205e4211342c1d0702501006d4a81e003015001c01032070700702405046004014811940e2000d98060003980240e0088a4072074440b5410360426140800e0443c0c0d850240000c0c0c2c0500c582030300c40144201c031103895810100b080b540c81405000062085071000313544450810781001c0300340004110601a03513a9a032355030201c0324680320140c090744602e07100100651605101001c0043c40b03411040309040c0329142c0440c1c03039042c20f000523000030040e0300600c0050355a000402c40114041203031000501c41451040a2464541d40c2440c090241030b032160003107044000001c1081110301145000f07803105210341101400d211400600940160840c00e4040745400040b4042034640d03000c1a01305c0d0402001186000802010b010180400d11b400700d03046030310310002e00c0700c607500c0d203012107554480440c1d048802c85290000500b004000703041c1402982000c1800d0003c03221f441920103003c1408580940c0510341241e00301d00a2182d600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 561579541 1250 561578291 561578317
    0x207020d050a0804031b0503100e03090d060203010503010b04090b0402151308011406010e09070f0e090a1b0f090b0f0c1b0a0902182e03090b0f040308130602 69
    0x164000708851200504180d170f009000186e0f4003c03480321102c906d00c816028031035043d40404850200c15445030859003101e0800419603040c4950f200204a21303001c9404103c0d0466000300060280c0d003424401e010115100302c5e400e1294001e16169040c01240107000a4003540103580e24415401c3c1101c119000d14003a011040310345650b0350f00450080035141d0603800514900400300b1413943c820200101d0050005000a26903200c00c0341c2604c140341142c404c8000d00038000c01141240da80c035000c5c107104a604103004a408030b14030b078507400d00400d0065a8401d01c142410b4408210340e00510070740940c2e0b207001907256690494500500c0d01e00811009440308d02c284c01401d070344034841000c00340c0074040a42d28400c0450302d40e0141001d9000f01e9034103a041c12040201c44116203450a00518201006154102503c69401213401080b11031118200401d0b2030b0816003040210590503964004840501e20701c5500305903800610078100603101c509180d1290341c000084c0049a41220007444a5403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 561580791 1250 561579541 561579553
    0x21902060903030f072010020303150103181b1205060411060d050103030c0507050102030307050f070215030c0a17040213020901021501060906021605011e210204051c0302060a0207020d05 82
    0x2c0303000394400c2040d00040380320740501c01c0c902030181400c0d040c5807189161f540180d800c691f111192140d6440d03503090030b0b504158031400018040c4140448042900d4098000b81d03c02140c000184005246164403060001c213003441c1c102c0100d0320101d5219001030344004401c00b454003250006159005100c01113581c64607000c000803c040d0403408544045103c0e20584001953319001a80c982c08101d84100206100300000c1d2402540440241400c07803004160800c5080180b0900249400c01c641107054040c0000300d06a0132604110700860105130406084103910303051380801d100d48030402c40721079080e4000c01d4003041c0381e0003445081c2d0848113252001001d580c0d40c50008001c40843c0c4100b8015000d90229070404441c0035080c00296601a143c1400d18141d00884410010241070703140100310511030700008080001c0c0860800400b803440240e11641004200500101c0c0c40000034000041d070704081c8002070300450311541c040000c400060b281c42040c00464000c0f880490010103500030ba03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 561582041 1250 561580791 561580793
    0xe09210a0e0108040c1a0f030f060a120203120a0c140303010510020a021c08040308160204060603050601020a060213030c0b03040c060f0504031b120309080d021902060903030f07 78
    0x21802038840520241d48455040380000015036048005983c0a000011300c00014001c6941c14144003034901100b034061172402c10346400e020b050b508141d0725280040c8400040c40b0062800c51a904040c0040c00350320b2409100640c00203546990000d240e01c03c02c0e0010821440072401411020f40c03031600f0000305501c83d0240b007540c0c0e0300ca44c000d008a40c0720300c500c40c084c881500d100054210403158040c04030b42c400408041c900d18403540c09034080303036072900800021000501c6031014041e00e0302c90016803406540f580c0b0401051301c116401840400d0b140c42c0030048142c2c1c0c0020001210744c2c00510040e662004402d01092728a8550405841441043c0c400100c1041e074000030f610950141c0c0c7c1a40e4542d0701c4841c201c4120421130140c0300003e10501c01070000c00d45d0700b003000109003003000ca4130401c1d680d90b00350504000d98036082a000305002c011300300060350061100e5020004288060310110b403030400b01d00b010440c40c000103802604c01040d225419142002220040c4003015651500d490607 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 561583291 1250 561582041 561582103
    0x30307051f02070807020f030f0f060601080601080f071d0a18060801020708071202070f0b130f06021002070c050301062706121104110d0c1d0102070e09 67
    0x100c032880e00141040072040030381030098825254a6913118540c5850302101c1d03000c0004009210403019818000e800301458800702c00c00018940c4054000904680e251900002d4000381004101030305100c024030810440001c41094103921202030304220740409070207119910309944405410383c014102c8100402c2c440d08111544c503541c010b0b60000d03c4240d0f190b40c1c01034241e0150710401048840240000b10004180d1509200749001d244125024180d0b54603107441104010352115024280009000341c0b1141d440d910840503080c90149080d403d458000300a41e0b03400da030551b400d8000d501080038010422000a0540106002802801220384403081e0708080000c04900c05040018080a000015981e01400003141c1154400c1d004808403a294413140d17050140d44d041c0d1140e95034090b00d803010b40340e40180900d40750300040010008801c030800707170081c1e1042040c20030814411600c4940d13aa0b00061a105503115020348034040c0d26907041c82860076410040c1c010460328080802194a14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 561584541 1250 561583291 561583303
    0x31c0c0c08160f0b0c15041401110a021c021902040905103603031107442d07080a03060b03040c03020907020c03010906090209010e1003060c0e03030705 67
    0x3d0410003088941c1d00d20010400d031041000d43c00c41504201c1c3d101040c486c5180b03903198444e01944030080c2030720800840c5800c50300108800c2003030400107d4a4006241c1c1080348068820000c01e0354070421105450295a459174804400307500103103406100110b40341c9070081185641e1003001c0b80c1980070b081040303101401d99120b814054200c2403140014102a550701407140c0e94504023050386e400c0f800c1d10210003918120300108407c540400200002070400085400c40c40582c04210485c0980089020700c03491540b2410000804c005004848003141c440c01c0300c0c0d81c2d0702c2044540010841d4401304007038400d00200e0100404078040b4a40d4140803030000207001041444e80e0800040d5103a05409038030f80400c2c2c0d40a404089076003401c0c401404e11444254004041d8011540c00120450009007505e514450440d83c03652100c100c0e40450030310100300d5000d4508514500079a24040070250b1503e6054400900101d80750b0400802c518010340401c01510806000d0707903641e000504046566a07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 561585791 1250 561584541 561584549
    0x6040807061b03050f03250206060108060f0616030e030601060c05160602190303020f0406090503150702031602010e13140a05010605042c010f08010b031c0c0c0816 72
    0x1144550480c001d41040d2200d03030340c0140d142d1100f0b41001700c54040382449400040100c1e00300d800450100300844181c0704442001e461540c001c2c0030a02d442e000040031402c000d00164000c0000fa0001183e55403501c0c2520ba001c08029084000c7e210982001c81c0d000e848040c80700c0c1c15019080001c200c9942c80300000c104580500110362500540312024200700840f48201c20040c0c209524103d24408c00e0000921101d00a140141c10402c1e1854264010381c0302e507002d480400d0a12804001c142005d200300039241500c8100c64025192031400a0345a00c100c0c400700c0c10740c42004007080c085a002d909500c06001d405040e010441e5403001035480102000342c98100e034006083e000688800e4a0701a281c1030b00c00980e1844d060074984000b60201d54171107030300c004048403850f80b40c000700d44800c81114020070b07546d401c00814610b84a245c90031501007001d544d00a4020b462103907001d0f04900c100d0950071100f03240461151241e4100078050001c2c5420030380700740c015540e144800040417540c0724265 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 561587041 1250 561585791 561585797
    0x40f020d020304050d3506210a05010e030a08040201082a0c011b1209063209010207020a0302121f0203011d010f09020c12071a010b090307090c030b0604080706 70
    0x12085c3c6000c20140c9046c012010305450b104100040005462800203031b410040c00740c88416648524594038808030150003070b41d10326500c0380c7c00c0342d01407003001d0046080e9640b151f03002d5840c120084400074030046e4000c0010b81480030200109040f003030820800c00000d0007841c1c0601d414201d5404e040c040303600000d010805076003006000407a079800f04901048230780715500d400352120b42c81036000015040042c1c05845080c0e542c54120003c58104032a1942581c030202490580e10b003030955003140e03004c003421030071440e0b02c107202020040e1a10509601a250100c0b40f40e900d08144200701031030042c1c4092440d22a049201150710b03031482c242c01941c141c4920495110799440c07403000440001c0000d2181601002ca203102c20450462558000c00300d070300514040d035030b01e0032038020012807551201208450b6500c240e000d44415115828841e40500500d55000e494980c02400103680d4507501e0082c0c008055a4012224509009a00a081c0c3d03604c050802130b2a02c0d9107002c46038031841248500004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 561588291 1250 561587041 561587057
    0x30415050406030e060f0402010e120f0a0b01060921020a09090311060106111b0f060c150105060c0a1401061d010e0a090f060902010e0d2010020c040f020d020304050d 73
    0x180c09005c501180f017100b01e030f00c4114141d0703125001120428900044140c200900750f4484000501c28000004c454800400406c031a0100e841c1c400759807181603002100300106c100050000f0100200c21070344607049603050100340b001c0c80c00018005c1c40c0c186c0c06482e00030f181120500c105504100040a0105010103892081c0c1e0b0b5020b007502c0704584148404030136007141c450b60301c0d16849040c21a080400c0580025001c800401c04a1103d500c5268044900d601210a1802d40c4000c07ca52a015010a8508a04044110001039650021040d0041130440201c007004940300b03003580080010003950755080c45240301c4a0f80c03a0303c0d40400303000304005a10f428001a010031620700400c412603600c41a000c0446480b516203500a000d5080f080341081105501c50000d40e54030200a0740c0c02e805031045066494800c030200340c810400c3d92030303980a0350b14008050607481e004641c0080b41c41041d10045070b80030f58a5800e0000340310b0251403188561011050105201e07000500811000035a02d9a040c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 561589541 1250 561588291 561588311
    0x15090b1c0f110405010c08040504050c030a0e0d05120403140a11070e07090b130e040b0a0b01090501140a03060314070503120903030a0507050307020a240809070603090503041505040603 81
    0xc250303280c480034030b40100302c104400c0002d07510402040c40003600410403107080c0341d15800002c00307a40050703e62404542010090001084092244000c040e10041c0204041e520b11072000e4403500500307402c4440313000c150300040c040c14000d000c0e8041c03c411816500e681d0f582030000280c0030006c0a50322807018803503000d02103494130340002c201d8004c0d29651240000e16141107a007100961200300b51890005150300300103907414000c40f14134080c80c452025201c40e0f00e4019401c0080b01e1501d4003d504100c40410100920b980041186807407140f0610f03400c0d07558100301c1c025401b0b4112a4002400c00c101030aa0080a000c0401c04ac001d03201d00320142c1380d00703c808050300b020901801c007515a16070010842c40180c86e019800405e40d40d8450340c203490411032103800182000310303240c1c0010030115440030900300c1000e005c2220382c010340ca01c2c10a0030060400c211401d036108024024070062690b5040b0400078054100259801000f14049940401c0d6a6075001070094100f4441c032004a0f040c150512 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 561590791 1250 561589541 561589571
    0x311060403020d0216121e05060a02120a0917220b030a060e0121030c021804030e0d030507020915090108100b060f1c021905030114011815090b1c 64
    0x1006c50305050784100e1290711607160b0107906aa1642c072050010351009403400007840a2020500c20740e41c0360710040e200c0700c0403007079000328040040040340c1042c54400f5402c0042d02080c6100390700d0316021100c90f1240c0d000b244098800407008501d00341814100400550b2441c0c1078000c0d072040c400b040090103050b984000e26229090280504041c080e02c3d10b050015041c0701c60143c0981ca40245044c0820300340307039004103c009403401c45c805240075138403040100740b6030010403901c0c098000791122883c60109880041c22405034820081c8201c00e0140440c1ba0303902429552165020010120202540d540042c40e50300c0b000e00c0d405003401c80c244140c1a42514000c810b407401203180c003005600c1c240d0586107002d071940c192081c0c03041940d8280048003000c40c1000e100ca0707401543d515101d50300c0d414010f641c0d0010020004540c100000c041d010200140040704550031650b6402010801d0503030390740c0644249a80d500041124400400c15940d040010100004030130810201005908448a0300c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 561592041 1250 561590791 561590833
    0x30618060d031206090c120c02070b0d0504020d0822050f090c0310080706090801060905011214030c0312010e1b030105012604030f0912030e010c0311060403020d02 72
    0x2290744001451049004203028100412010784a0710000031820f40310b146850032900e401ca83c2800107120311070b10b40101d81661091402400180c0006c00301c070b0303240c450280c203103101e240b80b0500c29640764004a011074441e80d00042010b84c1c80752a1071b403646030814050040c00b910300d40ca5004c62858001c00501814040000d400e4030303801a24500d04c50b510204d0500190740040c02c4403600b00c40d0f41d03900040090b424442500500081d50b00d039454107183c9607904d4252820360f04016540741c44c4c0300040040401032034506900680c00908220807580c05c0100b030b4110301405440c0002c50100007025441404000700840c180d51145410003490b8503003034104400e00541503145280c0d4042000103001035030040890065101404051031078155848021000614041d10210702085022400e031a10035080f0702e0010191280e405103c00100240d2002018022401145d505020480413044103140c81030b155144108881c6040b2015400d16103002503848552080c810018014101c07601c000ca4000e0a407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 561593291 1250 561592041 561592051
    0xf0a03122c0904020402070f15061d010b0a081902031e0f0403020a110a0512060a0b1008010312030e0102030f150303120117070e090c27071d06070602030618 69
    0x9280340c5948070f60030300001f175000110a8858019400c05580011400e00c482002c0d11201a000300c2d203145003917240c4170700b00392a202c0000c8803010f04005024214100095902e8072100307190802c00d640fa505260b89211880e0041d040d0b05600000c2080094a90b44000b5040920b03040044860b55031034041620700360340c0c16100200180c1011400b407021545620303200c0140d450081407400301e503607036500184250402039000c0015030010800c04c144407003907200ea00d07502641a41d81500002c2c40c520300038408001404010b00700203000300c8c1090030500c07950290703034915892002196607082065083c68481012110800507030b641040541c060301307011055442d10031040390354841c20390034241105006002d9000c0462503104108002a000010300203d600421411010340f1300d01001405100e80d000034002440901c080c01d02c40d10856030b4485a00c0c42e40481c0c240341c0201d500341c51011152104101c110f10580c000c0001c2076003014004c1d183d000b18000d0008641103412807180c00382d441c83c0c000703007261 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 561594541 1250 561593291 561593299
    0x30201021009031e09080d030e0c0a031a0702011b0201090213290328050601060801060806011d040510090b03060c07141903080601110c030c0f0a03122c 67
    0x901d0016000a26510030703240c0440c5c10301e105296111a0407038039204a4649000000313490b10a441e0749400c2c01d1203190706800c021745551902500f55107400441c0c220a556403d038141030f9100042d89903100303520210710903440d420241809550b8820083c064200810240d1040d0801c0b00c400030030301ca9611420f4044044a500901030301c01841d03035400010540c1c840150140900d10020fa6442107086842b00404103c1500f0000ea03400c0d410702c2864110141c20140034410700e2070050044607041005603611410928029689200741c2c886030514151f1100340700d40050424007407210282601d0300180903a01c4c89003003040f060490104252f03807504103840e5088201d03410840403002c120740203c400343c02d0b050141100d10140790880b22082241100c8425030005640c142402000d69212032103400c22014403005050200000c1d0009496404d480801407040481c1d40c0d10703000c40e486100d682c1c4000e50700700c2c2d5071080259210502802041c141c81092416606182195022900f17031004400542c4010b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 561595791 1250 561594541 561594557
    0x301030f1e17070f080409020a0f020102070b1302030c090c031902090901121e0c06030f0504051c09091e2007060203060d05100c0233041e06020403020102100903 71
    0x1030b440e980e907584400d60035a6400c0582c10400b002c2019078006000a000c0c115005955035070349580242840009003003c01164010040d40c4041180c150005420502840320f440008501d480001d00e4904940700442d0080c6504040017803809007180994420205016010b01e902c07031204104040b0301c540c0f0701941e4004204001444a8900b0f070b201082c803544550800c407980720355981d80441844400400711220700f9504000c0c08026070500600f084400400070510450406544080e103d241018103448009054a600400c0c50711a40003100140768880b410001d00d0605445030b014560303160394811100d420903001c4019001800b03050682013050320b890509101d059610380000e94401392801c0c3d4809010207002d004550103110309a6041d2021b1070006940300c14400282c10451071004820145002d50b800280c1c2da0302000348408041701840d4446016030b114900400d4003210030b241031035102d40d160641d10402455500401c2500e000343c013104c80540012200ca01a1840c80c107009002604c60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 561597041 1250 561595791 561595823
    0xe0d09080703110d0f0501061511100b060d06081b060309100902030102120703150f15050904060801090f2a030f0f0b101a03041a0a060b0301030f1e 65
    0x1006604a060004113131038014501a11038005411070044e065806035560328041103494880c00003940210100c0c205130422403105654203498007040421202c41300d44801e0040315a503a22030485480104000c4208940e54503002d14680e105a80c100c038a40d1030552035081400c0d4603101081d0781c03040480000500101d0107100141c5c028205c0c501c01280c1564081c0003400080b04580845032080343e0130366001800b4000740c0810403c03140e46a001e0448002c10f400184801801f5000302c1c40c104009051036a134441c000000f141c020322003640000c0040d4a0b01000c01b0420161105a07036509000324410290a4120704c0030111465070028400e542507088541000001c01c01301d03c124000b8007034140e145018100d41c80c0c014903811b04503042001461182401d010030011984e000400e8011450328604502e070507600c81c024030f24600100405076010300c0001d04488404c1d0032100c0644540c20245890707580d00e05d0900b600b180d81c00d03c11210b45000840031221814a40c4444514903000000b00551080b0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 561598291 1250 561597041 561597053
    0x1f110313030f140307140607141608090a030c030302060907050306010e070216091d0309060906071407080604021002011404020108100503010e0a021009120816060f0e0d09080703 78
    0x710402c11511000c510107100304001050001d0540d5600500140300c4014540e4886800e00200500e50004c1c17101559044010406401c1a81d844402c420380400545184e401d04200c0c90107150040c0e40d018500800100421800002030340c200ea04c45c2c0c0032280700707482da070040c0f541b1a0103a00440c2c1d0540d1080004120030b001d0342c0c1c499504a401d60042e503004030041194220790000c01d40202c0815919002c0300c140852000700086580b01040d070141d401c2c4406017000a0042c403074115414442c840214000082c44174580300c1d00402d1000070304464525503140310707164407003000300c070168804c0e03120120340d04945006004080c2018138000002c41c42da80c2c0c690054a00410150440c08200d9100f0000700300e03a20244980846c10038000c00a161001d010b00c10000c03410060030310a001c01416810400400c42d00b8440ba001a6621519554507001c2c41c85d0041d810145941001c0c0500b41403014040c10b50310286e001c00741022000d425102070040a020079503481c0350610a00b410303507110300c00800c08603603 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 561599541 1250 561598291 561598313
    0x130b0d1a0d0b070507030c1209030302070b0f1204020a050904060906060e010503060414030c12070606150c1101170f0609070504140103150308030c1c060506040b07111f11031303 78
    0x6c03190610b44d541085540700d07105074507031100306c1c0380c003080c80030509009140e0100980401050369842d80340c034241c0503258627005030044d107490386280d5048101240440d590541d04001800f000b41000d0b1081c54141080d034050601d065040d541d07246041004074245942004050590300301034000c024985440d07940000313590780568104120301090260483d100002c2c0309660f00069a68038807519003207982483d004482d05940315003e401c503910000740c1015040380307405061540201c41103030038822036030040e194203e02c8028070365020082c400b005599000465150302a4105030307000c1c40b56603550182a1403d100318000c400161b070162600714201e601ca9004a0001c407244030070b100e6040d5803a80d50310100e030410303515042c2000001c140848103084000881000b4422150306000c0d6500d8100425050322a500804125100000e21a0107018040e5036103600c0c4c0d0f0028003141034400030007142200301c039005a15100040c0328811400000070001041e510780125070348408410700d14607036038924800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 561600791 1250 561599541 561599543
    0xc0316020318190e0709031e03020a0b09010e0118140a0215070804030b070c1a06060409050919060b0a0614180102070e041101090e0714130b0d1a0d0b070507 69
    0x9004090209402c984c08070882d010304896200c138401b150851a1082c040e245e1030040c0c120140305021400086640012480d01341c0b90000002c0460341c642c0c0b80e01c2400740066940501c110360901150401d040b514014880a090092005905194141c03810585070350009a0195020344d000c82c510f61840c1101e4018202a4400c6104601e071980e2969600b0342138008032916004940c1c655101014070554040e04100e40b84000c101c00d215150160008030f480c00741c0d0061a82d000e0750344c0002802900204245001c3c0000d0400d450038881503407900401800e0021451400b81094400010721207014042c060a0101d8200075076003001e03031b048020061120500450760452140c0680012502c00b880405c0e4015805140826900e090103c0090002c02040c0d21120204081c1d20802940b207600c00301e1141a01c1d00340f4205661a1103081c41030309845c0b0f40707400c1034440b034070006188036200219074080c5126040c40383c401021030000c03404014050300807090117000c0301d6209002840c4a441100148111 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 561602041 1250 561600791 561600829
    0x90504050f012102131401080f06010905220f0c15050919122001050414040c0e060a0c20010f111f05060301051b040302120f060c0316020318 62
    0x618854000807901c0880700324510a0b00e6942072801604016806e00e2809000b07203400071300d800541d14142641d956014495a401e682e90703540401c01121000b5031800d000120182c00c0d111000403420000680d954100e02159448580380c0d0000321600c1c0f032598111500210388506007094854014030440030340d40f001840d11340714000360100d000d841e41c203004220b0340d015800101c68605c4510349070b44c030031409185240c148035007071104110144000c00c03004203440e800e0718003054000168805407601c9044110b15980810041002c444032980807408410083c0180e64958483c00e88083c04c02c0b050181c002003500003681c655114540178081e14180c4076400740c01044402c5400e01071040700900c02c80b05181403541d601c07101030064070f00d030900078590005148041101d03008540c1044084511503071000a020f84c00c0d82d8140e1000e00c105100d481d445060000c182c1d4158504191054815401240c40b003075030440340340090121600c0081940c4600e142603224100700c9043d4010042d101058068103542 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 561603291 1250 561602041 561602099
    0x305061804142d06061011010b03071d0a09030c031d0409060b09100b16020607050f0d0f050f04061d030a080a02010f02070f06020a021501060906090504050f01 70
    0x1c0b001000000c4505100358000c0d124900c0703107594480c50031101c045040d00307948500705019882d40c03803960020f1681840c0c00d0064203e140803030030381e0240240001296160158040001c0c4404449000b000344410740e9418206e5503a841e4448401c4034240540a00000c82401141001030700444401c001c82c68071000d1101003468030340000f420f49000b04011160a034a42003520054201a00e0807608111040da0030a0400d01b030042d66881801925100c003101d11009a0300002d644501c1d00700c91400e40c01c142a1f4004038110700d400741c1da0b01c511020010004144258081c0201e100d5401e5802d0001003c030300350300d00b910380300017101c4201110710b01d054950107101e540d08050754200889040240b283c1b40b00c64a81503181d101074211400c3c030610000715070041102d800000c501444204440d588a07200685400b401401249041800000703115114900320000c1040c540011408044481d907540b00c601e50750b00d440501c01503904c181c54111004502d240107010b0000100324401c4a09000303141249 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 561604541 1250 561603291 561603323
    0x20180c030601050a020312041a09060735040c0302030f120702010503071b1b052710030c080309040506120309040b0105090301090305030a1803082a0a0302030a05070305061804 77
    0x146408183e4048980810603000c040d0b09c0d40c1c801c1305240c0c0c082c400c50042c010300d19103584043c200c10709074041503003a2400e03080d00515088442c2207140390a0382c0c2c003031000142c1c074051920810140250006038440d110744410410900e01c0010000d40035891010650300f001d030580d005462342c4e080901a5000e002c280300c0d00c403503043c3c80c29040604880c003c00300d0113040c0200540303400c8042d846030807140c00345501501d071520640c902c2a680c0c0700c0110a107580b446564031000008400b4203982c0004059a81d181000211084000003420a220084070104200c0e21840d04020401440e96103141294000380510071591070301340c0c001e0454040604055181814010009084070900c80044003c00d0001c030600030503605602c83c0d00c2c1d0b440305504450840f50000c0d00d0180c8190380041003008008242c841d1400394090b59400840210820762034070340c81d400c3c0c1a01c05000b0750400c694ac1c0029a00d807000045409110f401841c0c000c00300507044c98510107036010f40300c0720000c0041c4156100c1180b13203140c42c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 561605791 1250 561604541 561604567
    0x2060403150b0402030a020a1d01021f02040b0c1506010509090a090201030f0c122f1815191e0e12030c0109020a080105010b1803010920180c030601050a0203 69
    0x9403003403002c40780060303840c1623881024016001c10000080042003200d1803d0382070f41c00240d01001a50b40785030381101e00807880280ea000e0721039a048040180804214035000c40310000c9d0759100b01c41c00002030b0480341d513003500444040c06505003660740050b881d00822040700040c0d10841495006241c0821201120000001510000004800020816803280f64010841d01c206a459840c003403174104800202d040c110701c04d020304d40442660240005480110413650600c8440841c0083c10310004104000c524414a40244145050050022542800d807620038030280306640100c5a015140003807642c2d00700c41c01036100000300c0e013001e07844c42d50181040e4100041c1c00c25042c0140040341c0d10f103d620600c00500715a50180e5403e0b07040c10018490126208103680800b03524420400f110711034500040d000d0551501c1c094a00005c200000040d0041d40e520b42804410a490410300866140300e65901c0e50800c031080034400c081030012035001e62003100205801003d5104403030404203003041d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 561607041 1250 561605791 561605797
    0x11101050f0a0e1906020a0c0c0e0a0c0305091f020721030605030d0203030a05070e090405100b221d06090a03020c1e120709020c0106030212060402060403150b0402 72
    0x507a1003000c4074081240751800c034042d9800ca40100d20141c003149190666000004510050041030030b40c0101d03e803e0305520413036110b101250071051421105903113080480700c0d40802d423501680503040c45080c10030b260280c043e041c00390100100805159410b818065031a04001d0b0303001c62869000c01c400380110312080000d8000010f488401039100b0000a07020381101c84607840319002ea001741d0741c5182c0c65034010007501d038882c04940010966985114049400b031042043c099488801d060600c02070000000701321708146d401c000c040264080860800c00c00d074100c052101c61603105003080c503802c0c0c0c0b026000a148d51800c4203648010045d104045410140110390420580d40001d0106040c517a041120f2441c590040d40c8460701030000481c2d0450500c52802458091064004541c2007240200480c0c0020700c0e100d4011519803038a0034040380a040184001d0388a0341c9a0150b1440920b030201d1418003440e8008c11a0b403600d451981c40401c0340d40300440c7c030302c04030740e41d42010306e030b140c45078001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 561608291 1250 561607041 561607051
    0x1020a0306050301060504060f0e0403021906050403081b040b0f190f0807170a0c0c05011a031c0e01080a0204030501050c121825030204110c100b03030f0901110105 72
    0x101d4140e09040c103240c2103c6a65100c0c500c03a81c1400c0e800c0080b0720900040c01d054510100303490f02d0640c0c1d01c2c01d05034a003411803048aa01c0d0007030003007864103122081e40502d0159100c7d40da044450307110b03444510920341c45a900d00a140804000801c44045a90001c211043d10200c0315818071b0201c19191803052183d86030b803004507092034101e5a8560b4007a508550290403401c02c48100c01a02480d80c80701c010082c080b1000c03070340d0380c0700e0003103c64054100154403035230001c02844044c000d02c0d040f68078548500c405a00900c03460036900710390224501a40c1c0c619446541c6c4c280702488074801103801503005000c0c9406580c1c01c020200c00b00d10300380100c601c02d0702003441c043e684074000441c0c0040c20200600f0540c0000b8444210490343c40003151525051b0450f020540029500c102d034414010a90781c0000e62291801c0c4e800790f02e54031614060807452140205031003a050212a03184252140d0284496050b0020441c0a0700e140584024001400e81890705031840303c00242203d0840760b0580fa = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 561609541 1250 561608291 561608297
    0xd0f0915020d080f010f15020307170405100314130f0b010e01050108060d030e0918150f13050a081e0a09082a3a110f060307030905070801020a 63
    0x2509103881c40c0c11422954002a10044c3c0104561529407101240c0070240140038074500e5000809540d90720030000d40d034506401c04400c0500522031075401c48503a205201c0c0b240150300807051004520300a1007202201e00c5030540d007071103a541e425889540070904090449040d01c0103a0850046281e0413840340c081d01c11030094a000d9414000003610b41ca4008000314030071400300f0505400207a0200030400d80c1c050560307845a82e911130169482500302e00e0310380310384240304407120110841800c1000a0040d83c45240c0d070b651176100d0b4960020303803924141d405441540410324610004414400428006403115006070200c0040307401c840999201e180b8940001c2d40c10740050215880501500e00c4c1c0b61803064120b0071881500c0d00c0303080220b480b11201c40c071421000c1d103680c0a6880e42d52459055680188090310340c2140c2d0444940c0040401005849024102000120504202c9408040c4110050109007103030fa80c402c086001d014118030841c0c2c10702400ca40000d800d5424000381211103802c1d1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 561610791 1250 561609541 561609553
    0x30204180e06010b03010605071b12050a0b13021e1809010b0a060f0e011413030b070908030306090609090723010315211a010f03230d0f091502 63
    0x290510b003000c182c00c90140000108010040d1582210865000d00c2d0300c80d06844600c2083d001c0b5016581440d441412010740b440703001d0040290110340f40b51928400c980d54140c83e11000103403070030205480d4000350040c121211050f00d20010300504c991120f4000c1c03c40c1d035002c42074441e8642209c0240c3d141c00700c0b80e44a03241a030480c80c0404a80c0068022450002c00503203400a00034010302c1ca40780c5031414001e1640f501c03600ca907001e904441c8800060b403441360601303a403803400030b81c0c1e12800c503030040010751511800702d2014800300859014000c001c08607061a100c80013000740c5031101034101c034102e118445001a60501e4070348044001a1010980913146003050300140507102c4081a064101211807000c1c010340700c2a600009541010181c20a1401c2407480e005565280e5094a07520318100d20000003182030420305007001742c030701c0b07030140c8406920019000884000c00f84410302c0750f50050844810750311f07c6a818404511038070328126244940d00d5005c0310b107515004040c0300060b0000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 561612041 1250 561610791 561610811
    0x4110703020c09040c0611160e06010207060318060506060d060f140405010e0103080c030d02030109020a0e01030903092c011403060138091e0a060318110103020418 72
    0x5002c80d0703181c00010b032a04010b0307150507500c010b50301013079016a20601440d1001a2981c800400003200385c00354102c00850181d8490060b14401107040321200e00610800d080800d940f0720038060708a510b181030714014001009980d0b1480903040c010003239030b000f44080c000c00003070003814051000140644940025440c1c10416030b00c819040105a0901650a00004200c08070000002c0360449802c8000c440d2034129414a09007180710f0401101090741c000b02c00842d4120313299009195454190b01c4600300442140010b40a0f94040c0382c0c003401007490b80804218505000110181250440808405460210250401025083c1c00142040541d0301004500c2d0904006040c00b601c15060090b107420025414001c0300d043c002c8001c50920f1001e0388400042c88000c064410300d41d8024041000c5030071101d0b80040411181124612404a0240000c0e07c54028413414058890364a44280d108983e03440391046032040f90801d90405508220005884c5c0d0a90440007001141c0e0901017111110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 561613291 1250 561612041 561612043
    0xb0d020612071805090a0504230c1306150c030302090a080c040e0712120306030209040510050f061005210106050301230117060a08120a02010e0f07230411070302 71
    0x400c0061010100f183c010b11566079072410716640650038a9001c40c440e5600d107498044462003400d8159102020030700700c448080f0100300b01000c1c1100b80c8079192483d844050000940c1c02c148123106240d003014203091070103407091060600741402418003510700f182c40004160145d0407903009075003d0308404a0303103007286094041c60f42e0004440d80201034280c20001407000c80310b501103005040c013500500c0c000b0401e0090300000300035500100241c506d86041d04086880f80d440150061001e4070300400aa44002d604118500400018244400c9000000303016920380d0720404c8101750700f01061000402d00c0c50368185860280510f83d580e030341c5951500300034542c6a02d2482c2c44003407110150307403900c1d50303640d01940b50705c02c2c100d15000d100c12607103d42020440003121070700140c0380c43c040c1c00b1600c03000c00c000c10b0081c5003000103a802042204c03ca21040c0303480c0d4090880b03002c0f06400c10302040000c00790007a41c100c0340b0700110515851503001c00c40047e0031900d0f000064101c0503800314082041c150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 561614541 1250 561613291 561613307
    0x120320160515030606031005030106030308221e0f060c0228080909150411130504050405150403021501180b010302070308041b0b0c01060f0501020313090b0d02061207 73
    0x180554107181c0c04020326001a0b03060000900c201d000d02004000175100e40d0540c1701c0f038030003404042c0082045d20707203a04004140c0b00f0119005e80380c0000307400440740005101c8402c2d442d040c2d00a0495101041c24503254400003580c00000e840c108044400080424114030800c2208070b0075070000c1222204001b400d02e14a03000b000d10380e036400d0b12401c144001c2032070740d01250b281c0c1c80104c030080c03070710343d00c204071801101803400041c0e42041c6070152f02c2d94503583d10360081100d40d0300c00c4981054603030740d4400c000994404070790060013600318074003041c21101d04221058105100340103817080704401c82e03254a4140000d0f800f032414420000107046075068a44a403854101081c602949461041d4a020f41507a501510060504903809100ca12090203030703480d8005080c405444c103546100110445002c5c0c403070784c0600c69550040010000c0c4a42c00001111a0300781c0b043c003444460b44c901444640140f080e02101500721850710002d10043c0d9440c801040081c42c2101d5100842c206180c000341405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 561615791 1250 561614541 561614549
    0x16020f060307120903050c011b1e090504020c0a021509010807030c020604200d061d07062c090406050709080c0a0b0919080706020d021612032016 64
    0x600810a10264070f50154115084000704076001c10f50303811501d01102c3c00c1c1301d030b160f900e8810b500e02690041e03100040714000118000503520390034820000b031a21030a07202100c0b500c1700800c40c0004200401d0034190060700b50108100c003911420b25494001c242403400c0010300314544100001e5038a607a41e008a9000c0c0c010a0f04c0c9020405130001c06006540c616021b0000303020a0241816400441e46200700c821001d42c0c041c00c078900301071251074128080c0c601c2c10100c004a45038600007040c9924001b0b402c1084070aa0398031000c02d09000d01c0003801442c2509145000c0d0314225920f9200b94070303107002041c007480c4180c10025641c58408401081301c071141c0c0000d800f903040004466070b030395030710541c681c203803008500656640da540100103a9000300300f803c0c086400010203400222020042215003c40d801a02540c2006c1d030002000c130b0700d4480c0c8940704071103010101014403001d042500054105441303410074038140d214000070309001c0f0a00c006040002d034007059980e8044c80c000c044140081c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 561617041 1250 561615791 561615799
    0x90809090c030a140720010608010f091e02010507242d060f06120e0703031e0504060c060e01230a0c080907090c0918140c0c100b0102030d0216020f 65
    0x24203000c50024410b401b0724240c89201030252080ca010840298030000c004c0207140020000c0d1500d0032220000703400d0342601170720b0101c1c5291100c5c03402d400300d0800d00303603c5505035941c0c1d00d4861140d664410110300c07040755203a40d40043c40400e0401d60030f481010000404051078555010f08030340111034111905038500c402a060640400501f0342d2542c030031040c0c07600d500f40700d01400b04984404008254030228002148103008000082c1034105080c0281921030001d020400442148241c440d48118411600010078091031240854203e911608059110a001191501d00c6400030000070030380d09801469240401c040c000b80081500c2580c0c0f0200d2542806021890020081c58942c007141c4030750802d1a4581000501041c8110809170281480203504070004400040c0071005004145810103215000004204081c455100380c4001e4405a001007c6200d80c020b084d8000e4910800494107600c414004048084014000317481d1a941d141c01d0984001103500400580582c400340c45402 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 561618291 1250 561617041 561617081
    0x6090b0f180105060d020c01061202101107060509060c031309060602010c0c0b0601030b0603040f030801060525080405150712080603030d15030b0c03101a0d090809090c030a 76
    0x11410542006411140100c1311151107440c903080c0d6030702900c5011070300300e5113510f800008a080001c000c4590300d03550094403501058500c00c0c40070b45103c4604058030700a40d000c0e210800c400f034450402000c00780b202420541c200300307074101c2551860708900701400010b980e0700c5082c030000f842441200020030300c0744000d003c030b040d280703030007a021b0155000094544050280066244c3c2d0003500105844040645032039524507040c10034244049109000b20005030080c400051294801c1055070107074112100452120100350440001c000402c140494694034203110004655840484074650821581401a640c001d035182c0400341a840d12020400d00c4207500c244541d5450010991301c042000705800100702d0304a0307201c42c40058860340000c1400443c40c080290011841010754040e5400e4203451070403070307102c503130445002a40c038801d084100024020303044480141d4200700c003510301441001c0d260440b0b500204003a58011540144c40510000c28000314021920840b10b901e2110f801440c0303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 561619541 1250 561618291 561618319
    0xf1504050a2001110105060f060f0f0712030b01020601380c1f0203071e02010f1104060e010c03050d180f060203060102060718060c02040212041b0b0c210d06090b0f 72
    0x8448400707081024040c003002b0551460010341070782124010808030010584501442c81c094a41018034040c1d807000034240048403001d0350001803640e041c2d42c2d41844c14001442280c022807001806418522a04101000344c001f0704640d81004240d14651a0054541503079035903440116640841c100c4400d20384104200f0001c16400803079000d0500c80900720684a11200c40107d01600300d40c01c0110a6518107109200320540da0b034000d00031500380da100c40d890070841c807006407089a8070b02c0018010400821402905e800681d10001c000d0000a5903450b03000c8035521a500403803158074003125200d900200780034941da01086410781c411483d1500500c80580c940c41c200814085200700c00c00c2c04500f0f0364ce8421940c40f501520f0301c038541e840f402c110924240c107107555900312200142c030088901ca000490030481c240121814295048010132440e4010040200640403080c0405c0803c0c0003400102100c0c94030b80562002004180c1c00030906900d180c04100c500700440c001c0c43d1255a031410b02407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 561620791 1250 561619541 561619549
    0xa060509030d0513031509060b060a0f0e030a05030d0e06240d020103060b0c010506040c0311040e07090e24060421171c0506030f1504050a200111010506 67
    0x30b480b62843e000d601d0785181d0340307108010351441d0801001e064041c556988115055484000010f014807002d102002005041c84090710540000200068141458006450151082c0041048003134120341100b81039464041c00e60b000308218459858464076208001c803000c01c212604200c0010200d100340080011405620300c0101210f0300a0600482103019a0301076840b080003442e82d1054543c0da010b81e19400c50080c00d040320f800d0312132440e01c0140e10065109101c0d1440c60700042c1615407805003003181c0c2d80040e84009201000304115548045119141300384491b004400320f4080c2000c001400b0024580b541401c581e16000d030106006c03c000e04c0500c8880110381d2401c5401300f1005104a0a001820301201250350f010100c0000d0717051040c00c00001c11201084031120f0400080d1950b00816480340300801c0f1a034a168002d103100000b1000e6007010ba41c0042c8034008a0304006143c1d40c5104a0300ea100c0000d0210804c1d4500071080340d41c000001d0080c1e089000000c12840c60550005 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 561622041 1250 561620791 561620803
    0xc06010812031f0902030915010f120b040203010b03030c07030c0e04030c0308130c08210903030a110a0506252c040f0203010b0301170a0507060f18140a06050903 71
    0x81002e81c110201d16007100c5843c4a10a02800c50f00034103664a142a051069882c0400c0100032601858103000040e8425005a0b40302510384450040007800040c0c0c40300214400050800d03070703240d543d8400c41407103503604100800d078405034080901107079440e40c200300100d035a00c0d6124000c4003100504001c0060b612a203048042981170824202e2a11a1004c13821801100e10004000040c40880070450700300006484107400f04003e4004101d0304105007050f03040c01150641501a80b0030b112a0084d00d000d034000d089818120803c82e000c0110541740c152a08500b40c1d00608080c00d130021001d0103000301d04140402c42d055007400c0b18415448501d10000c4041c802202203040d001159165281d13030b076a040100f00c0795000d1800d640300c1d40c540c0403c0445030320a10580c2444480c1c0c1a00b4402e0b5900411a250129004000360807540d01d4690305541d04400e0f64020001c00c04d20422a0380051601c00640d405414801c003c2292800081d0510044184680009090202c00d02c500341444e60b0000304 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 561623291 1250 561622041 561622051
    0x15030103111806100305040f020307030b151c2402040f0314063303010e010b01110d0507060903200c040f0e120708040312020604050c0f060711030705060706020c0601081203 76
    0x40fa80e41f40d00300000c03c83c10032000203505014049000050182c0d003ca081c3c080c1c603070001440e000d80d45440c108022048462408030184020310024008900c8038440081a1700d4609106c3c56001d004055000c00ca9000e1b030482003885651400910038070038034201521514541d800200701d64117000320407004020a805450b1101440010b45010000003c10100c850390070240080c4032224000c403c842c003078650108810300180c0303601c2001c101c90200048101e4000c0058403154944a26916044060b20440310103409100c1d075001d640c0c03107080d841812201030305800c6000c0c00b29550344404100a81d50030329a4505001d041014001481c0d40100f404007000c004918586d64450043c5000384060085504c0500b01801d0044d400100a401152151065104400b61822011810104100c019002c8039032600310300c040c0010000510104013490840c18001d0896410560b10400500c1c03d0f0300c10700048528a4010807040d81e604410003002e4090041c80c001350074100c0150081158900000702 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 561624541 1250 561623291 561623297
    0x6060f0c02011709100903050d0b09010e070e04061206090215090a090f0f02130305100c0e010f020a060c0203041404050103050a080708070203070617331503010311180610 75
    0xc202101001c204100c1c008000d444244841b1741ca038100903156821101540c00303014180b10310461980703401c3d001b89050340c0001c10b43c00304540720704d8401c8900084800b03003036400c1959440d02040d0b44c41c91480000030103204140c0441d1007201441409845170440d06051910601405150065620b0602420a45150541c002113a40752400c0e801c0203801064a1501800d100280b25107244c0a0411441d050380d002d1001c40d00c2c1c06100818160444144075044800641c03074829140c20f541c8145103c80302a04644116840c0026a0302c600d001c44603115042000740c2d2000030700700130304040242c0c40700c0084411a4100041e61640d110385440e445a850700a20780d51000810394101b06c1118140c801041e0042d04030750a25881c0c07040035100c03100b01c00104c0740401c0d0502c00204040c030844403c1200c0344012070b80003605414501110b0700c5506046a050744101c0c0e81000c15030280400c00654001c602940300850589040f8041c0250794001207510907141801c50200126a29281208421410146 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 561625791 1250 561624541 561624587
    0x12110d1209050313030b060a0b090102060406051f0620070b03040605040c030b0f040605060f030d0f03140a02040611030c2a09040609050c010207080a080d0212090106060f0c0201 78
    0x2180c02c900310301c0f030318004a0a200e0103030b030044180190241d20a00c41d0a00ba521000ca00342c5170000b502007402100c42540c0180c0c4100b00080004406410003031b0024109480800000560104800b0040710b5811900020740900d40e00e0200c0c40a150021540b83c017480c0107890f0300c909060a0035003610005001801c1241c0300c0c0081010002c3c4001d1403801140c01c03504400c3c07141007026941a1151080e64140d441c582800080f80f45841c00050319203040c10001d004250140c401002a159075001501507414183e03180080c00b515906411100d12985130312034010f99179400c00d48007514485054454501135801030000c00391022000405030307241c1c10802d500003490890180f1604096401a85454110210f10180020007015411235001c242c492419522007149a42c01240c2e101c1d0544a11071050740400b62440201e01600002c1940030050f590161500200c100d41c0c010510017a00c01001603959403c0c01c02071280e00140c040c2c0246000d00d0405c1084100782c0000b45180188821080c1000b081 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 561627041 1250 561625791 561625793
    0x4080a0905060d0c0206070302120601031d030d06031208010b040b0d020405131a10140705100e1029041503020319050f01060e0414070f0312110d1209 66
    0x81140c5001800001e21050f0ba80114030500b402501c00041d0360b50240c841c800c0070403801806402941d202c0d403120356004103a503540800440c090000052002507014105904014100042c0002c0c54181d8526502155051961400102c0e50342c4040f8002c0410102c94010b00020b0310100c101c400301c505012419480d6040c1b856264021b1095034491030b07001e520084000149503070380e044514200f6000700c0030700c90760410700e00f40040d6054034a224400601042c0710072100c0d04007103000d418111700600c00c0b501300b611140985803c80d0075000c1400740b1580100c0d030041d085409801050f4418031080340c030f21440300c8004c2c5110307107152203200e02900c11912051021840d600003c1f480008540040880b103040c0310162540c001312020740c809a40c00c0c003804089891a00050044401f2070f03504038116602590b5945500c00c08004509284020740910030b0000340705c401064411010f10300968014006800484010380300030b0010b580040305420038603560101c5038101800c221040d1002c0d001081020607 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 561628291 1250 561627041 561627047
    0x30c0f0321071110050105040b011d1003060801020c0c0910060c02010f11010638090d050a05010608030a080619030213021e070b0606070b040602070804080f0c03120405060304080a 79
    0x3039110320f403e0b842118030f610100c900a800440c121041500e0403c90501c52600440d10f151a01d14101c00074012a07025180e00e04001600350006a441c3c6400500182c403803651030300360ba00110943d07125500209010203145012104140c0040400151010701c1f483c000c4090000b1086070006030501050848071561a4040c501d02104401c16400810205131500041c1080300c00416240707a442c2d5004d452401405c803021a03441420080b40381075400d082d802c4c0d04000b0140c0407000221094005e0110f0040000c809004001c080d10610001d0754803042d5040c40203281c01c00090006105000c50070020f10140c03424004041544d03010303207020b0030043e104815400030781b0076010030314805010280c000d03c901070b00902521401303204484018a40d00c1e80c10403c602c2e40541c05000e0b1507400600c000c5000130740a81c0c02800b10030710990a1030b0078142e803440400d003000d100c803405800c0340d01b06142e5440e45281c24000d001c20000400c1c0c209003081d0805001c680c25000040000300071180000b5010711084c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 561629541 1250 561628291 561628307
    0x603020307051603020703050d0306030515090a1b0501080604091a33030f0106150e0d17030405120a050f0315030303070f0f030c0509240c030c0f032107 67
    0x902d02e00300da031443c0c0c00f526000756240300c0c9100075100c41c082c0548070f00c030040c800c3c052402144c0c5c2003070041c2000c5c024040d000780301890142161240c0d1103060ba0380d0001810920142c102081020001f100c050f103803000141c40c160006002ca03109525100904000412100509481242446104549907103000429996903605018032600402d01c8424502c00b408840c0c01c1700c00341c4000d505a8003403045108006082e211140224050404020803012030b45206106035030f0100030042150000c50b58a49440440c64420202e1840d014000020007050000400681c81a4694401003a2601c40380d030388018624069030340e0041c0c200c040000485e4905640c0f0401209002c001020303a0307540e00b401d1801030504d4805143c4a400300b400341da440088940a0b106a0090a401e6180e151a040c80300c010003130040b1000d40348006104c032a044504000881c00050200c20040e0401590b480514081d000c0c41c0262182c0307142d000d0b52040100d44105030760540c40400380c0c00d8542e45600c0c983c80701351084d40c1074a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 561630791 1250 561629541 561629557
    0xa030b0306010906090f1803110a0b0a0b030f0d021b0a0e010e100806370c020309030c0915121c0e0103060506072001120e150606070c060302030705 65
    0x220901c000071500b81c6181d4840422210b100d0400c0000514120400c8151415014422401c0303134440340c0c0c4008070340078101c3d0096810b03075141911801d403242d9441010428060b565050640d03568800341c191818200304030300b0303c481500010000280f05240c001d569019001000c2c81a80301e440940069484d8824031074086c0043c20061012580c5408000032884021100300040c4030003d1400070310b0070001305a180c0503001ca1503210340340030941e140400a05010b82142480049108640700684165100d500030090f036550185d59100c110608142c6080c480d4001903202e50458000c8c0818075082c28031000f14400265100310030b039220550002d051543d11400d4030700100d0002c060024141e0b00c400e21200f003c100b40c9007080095207503010702a5900460380000c0c040150114004c0440c2052590304035000d605140401082d000c00c2c40940540e90040546021903100c2d0341081c951070100c2110070340c0300c00262074241c1004010303210545100e285103c1c0c041410707800008180d03018801c90469401c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 561632041 1250 561630791 561630793
    0x230402030903180a0b03040209062b0203010c050c0709091e0c08120a0c110a0803070f0606050616110f0a080d0305360c04050c040602010f200a030b03 66
    0x60725051000d15125440a0b04605a400003442d8025103032415044600544040480c114116602c0da0b003400b00b0040080c248039030020f0b101c541c501c800d04490b121811451042060b07400050b405205050a41c0c020342000004c2c00b0050140c4881b506000a41d4070407103001100110b6803800c141400c20a960105440007200040b009070030041c040c201c00f00b101101c00203002c8450100d1340c0905030189010340340003000051000241c00d0041043d4414000c0d540d40001c205100340350b55140d010b80f42d07520130881220030410f83c1030601c0620502d441041c00034201680d6042c40c1c605100c2c544410400c0780c00c00104031212500a00205880d103c0b0041c0700c442000d001c0d1241d598440f00000c1ea40c80300c0d1000400000e040c2000240b1003a0701c2122030081d1103c1008102a86010441800403403140080c110741a01c2421400c0b5101d40c1d43d401694010b0001900b260303912810180001c0c02c0d00e1038094921541400e1200241e00149a440103280180702a00c036581c44014a0004602402c001b003072041d41 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 561633291 1250 561632041 561632047
    0x5061c03051e12071b0f110a05090106031e1a061e0a09031b0302010e060a050708120105101b03050f0915031e06030a0807050a0c0303020717031201230402 68
    0x2c01c90703e0440b0740d4080c24441d180e54150106090b409006003188031300007840d50500c50741403000901045501154414018991042a900d40307000c00c000000c01d81c000b0b000603454034034110081820b40c0080d1004280c1c2c00d8180202714182004c0e2900070f10700310040d07000b0341000440c2c10f030740c01d0384142ca4144080c00440c030740e41e180c004050060040707500f4003007603a801e000080310003100021501d400d412290706841c1c45041242c03900070450603070400340341041441401c00030302c000551048024821070f030021401d0362540d41040c050101503410310032440180310180e0182882e0014082c12840600d5040c640a50b0310408080880d42030300400b14625008010316400610044480c00038501c58004030900030243c025448181046900544541d900b41d0403803070161000c0b0f042c9100821540e0300640803928040b0880e518500d034030f0903951090b001600046002d01652004070340404aa60f144c400450034103507040c20100c0940c1041c0701c3e482d09911240010107000344000390701440620000e1003151 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 561634541 1250 561633291 561633307
    0x501090507150e030c130b040f1d060705030f0604060e09010501210c0306090c030803010b130b0f090424030602040906060c15020a0509120109030305061c03051e 71
    0x1946110a00616414207400d0840c020024070640181a0000c3c0040c024002131402105112444040c02168541d05440e04400d1312280c5590284c1c52102c03442d90800907800c0c0e845014003d00c150600f4120081c0d800c01c0d400d0001d030780c2e44031041ea500900690444107103a06e4100004d0001d2150342c0c0701404480c40c070404c021010364194041812207806540c96160000888403082d21034410f29030040c48414484010b001051072a84014849440b561212414070b860707403218240d54000b60b00c40071071320000054070080075045c4030900001300900c0c10010700b0040a8100f4031194090881c9450040d03079941c01d00810515803050a024058103100b540406070345070705020b4003a40c89405a02d8856041840001d0940d20885d0300d1102e00b5080801c1102d010440e240d88800386d4811403c0c0e0b0104802808a60302c541d840301651406800e0700400010b03070f004203140c060191000242101c1c8250030940608ca07000c040455441031303481d07041c0b500c56912072001c8203042600700e804001410b05180403440c80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 561635791 1250 561634541 561634543
    0x809041508030a17010503071e08010e1e0606090f040c0b0d1d0a02030304060f12020f120a09150923010605150c0309130e10051e041e030c05010905 65
    0x10f0f20401565044c91040c1c1842900784c14410038070803543c044d40021020425214007a402c0e1a098104a948003034265881407080c1c20b441031540440d4140c0c05c00c03145442c60882c20f402182840d951358014110703e151110001c1c0c1e080780010030303242d85400c0e40070009040050490400000d402c4160115858440c4914440000d00e40803110401c621503401c903210507036000190344036080e540100114134203400c02c00116a01d4081c0c40d00c08040c04071081d1500030b4815140043c0c00c004141d00c0c140d60b10b4a10320175a0750003034403000d001e401c4128030f001e04c01004624845202e40405240c040d000c41d2030300b041c0c42c00c04900082c0c0288401000c2a04150312180c0406412040445604403074511003c4144002d0001b80d1040c012415040c0d0b00c10800a03140d814041090100a00340400001d0205465081d003401c1c082074415125409503100100a82c10007a0031442078044801d503002501031625035034090a43c103001c2054040401046001030801d4030900c205600310fa4408020722944229103845 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 561637041 1250 561635791 561635797
    0x18100b011803110f04110f070c03080c011b051809130b1303031b0207050103110d14010602010513080924040303051c050601020a02102303040213090f080904150803 72
    0x407840f549071300d07045810920385070103050078050f1128602c9203482c03801502000380b507100c0b480440f4241c080d0800003012928030806000700044540000c41d190310140190300405150310108000c0c0017042c030040840104010012100c00c03c16a20016603480703660222220040412000b0703c02038202c070421411411541414418034032a480c00d00141000904030005401355101000040e0b0080d82e01f027001c1d6200760000c90341d400341350002d2460b2803034000100c41600e2002c0c0b8009a44809200100a51a42403282a5005100143c41c01e414a866038034812244030340d01f503051213a042072569407000c803008640c0000030030260122683e52a601d10b0080d0443e0445074a880300808085481c1e404460b050203120f2203000b05134081d100080c4c0320343c00c014040c5c0719036100404010b054100c6501d5040030b200001e0341240e04082e090307202e140920400c0500c0d807108880120042c10100400002584051004040c43c1d006074419180d110400c00f080060030a940c1c40c08402c4a02d11000407190408802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 561638291 1250 561637041 561637073
    0xc050721050c0a0308160303020418140c1e0c0102040b0a18050108010b030f1506220b0f030115050715090b06090c09040b01120e0d0818100b011803 65
    0x5a4444580c0c1c0c2c81005159641407101034401d1504111100300a0491200d51798803e200303040c0141810b03150b1441032020b51000c490741008c1c540d50f003001c1c0a2100c808044a034405141400180f4140141d02c0c190341051001c4101c1c40d004102184402c803030768003901501c010701084205070ba120320013914000c0442441c2c080002c1001d00003500446c555100b5041a41a99100c0300d0041c034580f580d450103417440300d00601c00c2140700d02003940124507694480040880d500f4089076076000000c400c400c403910848130707030000b04801ca04104007014071090740d080c1c0c1d044606500951106034030002040c1c0f40c03403281010050650225425400c00382017203038880e0303041500a85a11019640b40303014008441c0003a141130003a02d80602230b04800e0701d49600b1010b2003ea0615104c800914a044c03a1410354002c0481640f042e00110181aa55613001d400c42e03a004e2a10160078461042012115440700f220507000c048507521102d111499902400100c00d01c800d000052110065490030403500202540388 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 561639541 1250 561638291 561638293
    0xf1602100503190b2b060f0f060905040b0f07020f0106181d0604110402090619030e161503091406061509030c060903011401030614180c010c05072105 66
    0xc10070f440000c092107180303d04d00c070182040703d04c104424a04170340031845400b2030401410003107071000000c8a40c002c0b40c640158a410100c1c1003c11100030100780e071856000050a20310b020108030114a449141e96007003240c0d0401520b840d1079003072041f42003000700c501e680c03502d40c03c103400051108880c5180c0141c0000500c0b0070400300704000c0f18150480013250418070303070340d111a012801007107100c4070080c038501000b000145081ca4120103e6015001003441c03000742920444410182c6405000b010049501c1c0c90203031904851462040941a01754003960844040b85203094207070f0340c041d0780407207203140d04104184150700111030079641c0e03004102e8416004d2403013051450701051000007511040030004010b0701a00f400d03441400800e8224a5115a0664070380d02603040800c1102023640c0038501401d4082018400220030742900c080143c0070600580c4c05803a443d24035040807c4803883c0503400d20b081c0703c80342c109040c054a020b00d40d8201c0c101c2c450f0801c0d001da0036000e8903140003600c184550 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 561640791 1250 561639541 561639571
    0x90b090102070809100e0d1b050607121d100804110901050603070f021f0e0f060c0d05040c0504050702031809070c0f0609060e1006360e0613150b060f1602100503 71
    0x4050000b903010b0340c440280307000c1c070304881003330003e01440034041c00d400c0c000703010000f81c21440000390f607030603144940c038012a10b94018401400224200303c50203107170940f88500603503d0000400e41621006105804221030440d0f8205081c0c4203201c00618006130f20381600c501244844568004d010b41d840c80d81c07451080b402103100826010802c1449044030180007410582c0c0341324564050403000304212440542920302140130368441c403503c0e0103000103900a603191110f5051181070440002e00071441840a90108000c05602000100354294405e04405980c8294a0408054500c0043c000c18003030501390f0740c550301100081e00c043d00c109250000d000072950b41000484610441c4803410468041c0b68032400318000a080158880820b903c000500282d2201040d0500d501a01c3c5401c4503203040601d0360500500d614240c1c103002800104101010003180090b00900c165042c01d10742c00e5000c07a1030080620780080f80007031150003804a80c054105c020000f8440d41c4111004640c1c4240c2c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 561642041 1250 561640791 561640799
    0xd02040f050108150f12030903010e1c030603080a0e0d0203011e0b0105120606160b0109020d06050603090a15061805090f060403080402060f0d0906090b090102070809100e0d1b 77
    0xc200c02584c1e842d019240f04101a401000c1c000c0c40c1038112411103240c8810441c6442c19182445144c1602c042540541001071896030107100c5041140002004c041c2015410b002240c201000c503a08030583e030600083c040b06030804520b503680e0b240406989940703020168012942d101c2c00c114000ca14560003007003804c602e08010740d01c60140308104842240c031500015200c4c2040700090000c0101149511060182507440b4a031012003608100c03940c94001c11017003000d420300e005d00c00280c602200d02d1419803816100c41030381c03070442000240200040140302e488180b0154091000307841548a00114034900b031a5510180c0700a41d0704841d140b05150000d03490b030801103900b038010385e81a55280d4054503a6003c02015402007808401c0c01c0c01e0422250889050314031403104410300c01c03800401c00c00c04034140380300c802c140240310f0741e06a40100101e10014540030211503618038100c40f5030300c01094610342200d4990402e6119074002440590f02d6052004c50a80c108805030301c503461288550321 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 561643291 1250 561642041 561642061
    0xb040e010c2a0503040b070212030403110f0a080309010c021504030c051e01020a030503042d05060903030c0405130204030f0f120309021c03030e06010612060509070e13020d02040f050108 82
    0x10254098502c4e001444140041c01c9202e00a080d4240000d000090841d00b0000f250308551080e403049400090044591040b400c11101c0f8006113001140c00d81e07080c41c504243c0035100e2084100050400040064000440d541d019041b11840d049041560b00c4585a240c6032600c0015801050b2292209101c0e00080f4000b0765a208202041030f40030f08640300d1169404e40b101e4001500c1110000c15560710f01440400454002c0440e541d407580418105489003001400c0c450040c000e2070a94004008200a8a1000c0704070707811514181c40d02003414403d40d0101c8001e000d5900004e10002e035890300e150500c00002c02d49480c0c0c0e4040d030400c0300c8181e0851416412107041da40c000f50004500c04028002070281207602000a0107804c0208404005810311428010300341c1001740411058182c02c00458034a2145102502c825078100226081209010b000980c4c0134003030a1081000304180d4182503029015a011502496400d64650303884500a00e80109140211800115440006050b01503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 561644541 1250 561643291 561643367
    0x120923030105060406050d0b0a0b03060a05010303030c080405060106140f0307050c070f0f0e040f1203230907031b08120702090c030601080105040b21010b040b011e030b040e010c 78
    0x100204100d00b90320b075032399554404440007091012020303690120030030b80b500c0500440f40f00f4446017800092079810b45c60301900700c4215041d04000c1242c0c5104200c00902c00081c1d041c1901c036141000d685031110400010380c980305001814401d41000701c14000a41c2e0050007034031107482c500040e035084988070702c0c1d40800c03819248921704c05010040803c008000ba54440150824000d003052691022291181c1d01501d0b181a25030001030365503103040c41c048a461000e8115120900c00f13840a03424007210282d69070485020180040581900300500c108000c2c0081d0020005c00043c1c03001d0f82e1142005440b1070700983d030103074000c00c018800608950511012079118a4050715640100e07424401800000e0045c00329460700a40d6510080d91001125100100c2202ca24000031651012890500c001e840c8201c0070030b8184582410201d032081517420315402d0005162a0008100400e440090302904c010001854039520f4401ca000c01a40d1094001106a400a2801d001a64900c2200d08512 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 561645791 1250 561644541 561644549
    0xb03130524250c03031404050c0f030d021c0306080607050406080a02090319020a05060d0f1a1e010e10020a0309081204030f2909060a020702060403120923030105060406 74
    0x2204221000c4140d80241c1c0c905080c01e000e8074001541b140030150022010400303850a45140e03000c0a54200c040c6091103180242200650152901c2000c0d840087c4d6150003030001d07005140c00504294050610035800381e0700821f0301c40221002ca0422282c09011b5500502421000411001c00500d038002e07240215410b42c580070700148000c044221288490240d004403c82c1d02c00300c2018001350581d5240003038100302500c60743c0010780001e4606401c04440e2400111302080b0f10445080020383d44000402c2822509400120702400d04d00b001201e40c1900000e003d40c6c40031011032300c100c00541c0041c40402c407610a40711000c040f61600201950352031030903240c81d0814410082440010000c2440f00b034143c0c4651285c2d009245002c1c9041400c00420400300f441c40901810440000d40400106070046029030f001c51609c035150b008a009485103020203881614490041074000e882102c405004200e4402081c08408484018404143c0c040001510960809000c10407528141c0b142000311 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 561647041 1250 561645791 561645841
    0x1902041508090102070b0411030f030a030605011b05030301270606030b102109110411090102070b180d03020c09090102030a15290d06060801030317060a0b03130524 72
    0x2035030f502d6491072315039140e041e10550180600075840d401400e0030030140a10015948002c10024144030004085200c2840039040103c000880003010030004000c50381510f21f04e2025408031f40700310a8101401c2c1070801d102c2a0289002d0340007603121703071652084071052001c03540785d1045040e04008458501030501115000f10321500380d00300da6070355a0300003c2030701d12880d03c0b03040d04101c00001408445d1403092401c014200000c0360801c540e4180100405030040c48083c40c1010328925803c010f50b01540c14190207403600320b10103002d06008101d585202c1200070a8004e075842c104410f58040d40082d00c94254490801c4507021102c840c640c43d103400d40d02007200c104070450a0080d140b20103c60318051603500c44081198010b11a03450003101c001e418140c84908103545549070081445403244c4030300c20302581603000d1000c0da54400da29102203403d040c480d01e460781c968490100c0054242c0f0002000c03842250503e142005102207444454555a100040641c1d149000382c005070403814480c01c03d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 561648291 1250 561647041 561647063
    0xe0c1003020a020106030512040801060609080709020a030b0301020706140c070b040204050a090807080406090f14090903090604030b0105120109030903030c29060f040204060f0305190204150809010207 88
    0x84520a5000d04000c80007840003142081c1c1c0d030b8844e581081e441c0c1c0c403805110400041c041c04006401d02030324005060701e141c400c22091a00c600147c8500da1409aa0740841c1c0026000c41024070079044098107000c010021992242145410001446020484c1030581219000642c98440f10760a44945642124000c103c81c0d940f6400c20004140060601203050381c0e40d171115000c25401c1000d80f10281c890711780d10341e0b01d0b801e203040a09014503a51100d40390f055852024041c019103200d901110320015220400282c81d250320540c254011401c0c860340007000440c000050002110682d41224020f61b192140f6081ca18400b6086e03600314640513002c2200024200000703882180708211786030207512217580461941100b080100d0211020b003259038000380c1444a5031401840780e41210074115421403906250200203002c00341090217840a241c0e43e14002808102e07144012001d9008003a41155525221040d01c0d035039820614060700081c01010004220600510803100c14580082444071 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 561649541 1250 561648291 561648319
    0x11090c0405130212010815060d020d02060d0f0e0102180d21030908030c041d01062007120317070306030c0b0307020a0c0303020f0c06030f010b1b1603060e0c 69
    0x50b072401005400702c0c01d68204080d0070800300c20089107010301015806840f94289141c01a2240c22000d4000c1c2d209075285001340d07005940c0c11810b06021941a10381d03646924040d00100c0080c4141600201100e042c9100d180030b121043d8001d0400710b4012450516403201c2d0002d00c01d100c0030b6000000c0c14034811030022100000c051841082940031450082038102d41541d031455030b03400550302040f40075000b1809019118041d60640b1468004000c41045c035803502c040100b0010070520b140c0d80d02d036842c030780850300340400b030010802505441420001c01c20051030b00401d40074003480d00000107001e0030082001948280520000c5941005000310078600340341003104030758400b0300440254441d102d000310014a0280d0404e000714026005041c01e9102e0b42a820b0a08600ea460240718607410820030403070030903602205041d128440040c0d0340300c40354580c20300e0305000e059127460024400c20328140492000310448000383c0307106449c01c0c0030403105d02000f581d0b161044025964004043d0340c01c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 561650791 1250 561649541 561649549
    0x513030816150f060b07050c091e09030c0d0908030f0306040f050a14010911040311010903080403050d1803020319151a040b03070602070312170106050711090c0405 72
    0x1c050111079034400703548200d0603680c6001160110a584030a20f46451241610044500c034120043c8503000d2142d00c4c204240e543c20341c03101c2410958a00c41c607560004141d2982c0e4071000425400418101c0d4000c508104201d55036036000350880486a00c00d0460741a81c06214028110803108031100135410702f840da65900c0c1c402e400080c0300d290000d07910541d4805140050003400d00030418034900061000030030340244083c0c40e0580210703964909120040110610349030031078007101e0304a81201291055040101c500c030b1581e0f84050308198000c180402402030200310818000013a4440c03030321001c0e407058882068511484042c0d41600308801c1404e0002c0760f09820081c0c2032284c5150001d13284901080801ca078101c075051003a01050b041d804010b820948101c50162404400408080c0d251200003035868003140002800000b0606541c2d079524080c4c080240c04003400c1c902c0304030b5980c49810003085034000d00c0c8152180301c5001d400038094100503000502426042c2003091074903017440300380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 561652041 1250 561650791 561650797
    0xa020304060b060307170601080c07061d061807080a0c090f060506130515070c03140f0102030703050702060f040b1503030c010e0109210207141804111005130308 71
    0x6603a160344480c2c514400742d81d4840158400d101c503458a0702c6440d00e00c102c026500c0070042009051154030000d21605001401c196116554058408940004c6204000d0351304160b040c1048044e2141d1018405a070070351504418252050b1011a84542d40d148a955510200807801408000a000051151110980194100341c1c1400004181d0641d1a400b003403465001d11442030510920510501007850992088101e1001d5002e00a0512071162244400c02d41d47d840024054000202c810448100030b0040c0c065400504008640303900d01588040d0150400321000001070040100241d1400700610340d03280200d80050f48400c0680c1c80c40700380070510b41011030307007541840140210440c0c1e81c424004c0390b68034801c590020401824a242802d103e400c19600d01d00e04c20003c519000c0880e50006040c4100c0714143c00030800e0300074187c042000460070440c0503089404078804c22040c007c04901003455001d09480b030403007194410100325064016400f00394100851540d04001240ca40009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 561653291 1250 561652041 561652043
    0x21909030f291801291017010b07020109050315070e010c0507090b09010b07050d03020a0309021906020606060a170403170901050114011e110c060d15060201140a020304 74
    0x550900c071580b00c00c5805030540101d66110030308001c6481c89071580b0080c004c190024070841d00501484c13116070391021907440c4064005000342140da10f0000c07890b01c1007440710315100308101c844020303507120b0561584079806460241c1c040f6450f00800119800d001a0442a00380000081429912204411076130000c58070881030411046e006200c0101d1403d12180006104c09c20340000c00c1181c650512241c0c030016481000402024404c810210f100480c070078814010301d140c0107940b881d020038264001d2403590b00103500000010040300440340b40500c1c0074240c2303109400f140da841c3d0751042003100a21a10f1000d000041c14190003003a901500c81d48150014842d090501c0d07408072381e1782c04600300360045980020a03919200100200c0c400503008a041c5030080c80c1044407880c0d80626aa410011a100342c07081240050300694007280500c4500341c801c2008000a503500d480104041c081c0c01d002510002d44985124001070440c014803d401270401d80b0349230100342d5a1285180b6001b5000200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 561654541 1250 561653291 561653333
    0x408030402040c09090f0906051e071107030f05060403030f060f030809030109060e06010f09200d0603050316020f042a0c06050c040e10050916020c03030706021909030f 74
    0x181c04110a105c1c1c5c080c503071b440c00200da80011403e85504200d0b06885001e0100000c03410942c0c0503105180c504651a6400061820700e0503002507805c00040c905103450748041d1200a000d18220100180842c0d400c4c040e40c0265028080d418110310340400304e130b64601c946440c070003da00b8100700140070040606144880107000040b0003440352603460594002c1d0003640c141c2c0d04408018440706166035880710242c0381404041081c42c200d104540c600042c2c0200c0005501004142d61b01e180d00303580c02c0f40c0d020b540d0201c180da485d0325818180344446511180704a1050b142c014100c182420705104d031460074280a2500d400c1500811040700312000c910020104128100e410071020640b207000d800d005200d01d0f080503594500c0d04040c0300440134045c00c01605211074881c20402942c3c0c10380c5036070b00320155000000c5c40c0c07510024103038580a845420705030540400305180c1c00f403069a41c0034107600c3e0100811540400d1401d881218002d01d6800f00600e502d03000b103801804241e4484000001d1101c1d51 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 561655791 1250 561654541 561654557
    0x1051c0314040803120109180605130c080d021009170708070f120f030b0a1703040f0e04020f060301150509061b0f0f010c1e051309020c150408030402040c 68
    0x1800c2205561068001c8083e9501c00110f601075a51144203450040400c0c803804c10860340c4040700541914070900e80070700296252000300704070a940a1030601e880e40e20003641d025099460031490b45600c036004154025004424920001a18601601e55003d0340024140030319550b4080d0701142c0d400c04601903c0010b001d02901c1c00160f01c3c4c45045610900801c02140d052108132030003496008896280c004050400c05904011b898008034541031f02d40c80e01800300003203010107000380385004550102c0560070121310009010310270100c00501450080d90b4880d0710108110074030030248001c1c031510072009000703a00b103d1158454005861a02c000502191610020316220181090b0b00d24409040d0f41110f402046950410070080014400400c001c0c44120315881001d00162440e00410f85030070300c80480d44803404d2107031089501d2160302c640340e0802d641d1940044802500300319a003082c0303882039440c2181440e1504840742c4c03107164498009407950344d980c1d0a100160101d01c020030306010f500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 561657041 1250 561655791 561655817
    0x305121b07060e060106090b030f04390503162d06020c01030506040c17220b1f05221407050c011401080c0d0c1206020d0b010801051c03 60
    0x40d0380104242409108045100e1042c041602d00709001a0701240900c084041c041188134503080c1620b9101c1c00018845507690b4860405c1072440303001554101c81c81080c00f83c1c010700702c841e06042b5802000c400d0030b10100580c0b10300a0541c2c1c0c202503122800d0758400c2000810030b05c80000e2074040c014059085060b490040550382c0c1d16890740b9034111802581000350040401d5a141c4034095000310120b1b4140002d034090032001d80b03a6120100f881c10f03543c089200041300041e4890032131880402c0514104541042070030034500c001e1003a1007005174403170070703000001c0403a641142c40d0f0b0950740c0007401034200d188600d5812601003c20030f031452965880e4590300c00c080500000d00b034850340c0c080e15107641d28403001080c00d00b12a003001d03650a0407192000140b01d14000090340c0a011207007074a400000d842c17541003041103002c01358484400c0c1c0a00341c0c2414108151707234000e0305040341c1e103900074050140c0d410300540313500d002400f84907005284102d04c94080d10f499290241190300a0400c0c115881741 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 561658291 1250 561657041 561657091
    0x9051507020a0902120907140409020105070c080114070302030103020102062d250c0b1512011b17060108040b0703201e040b0409020702040e010c09060219030512 71
    0x183c2d010b08005a800b045060b00d5030714a2440c5d0742d02070600380c060044070b4280000510055004226140596565140b0b03504590080d8202c403003d03030b040a003810320142e40b440103602801018000381d41440c550000300f40900d010780252030680e6070503005041e10390f270380350b6000703140383c20764980c000c8500b0b1103843c60030041101c40c04107402200012009802c0400104031000e40881c08010001001103240191011034540c0b21003680001c01000c04080e5262440000b90304544019400300480d480c259442e4441d0408020b6035003610b641c2d458150801040b05242c09102d58110303034160124270620000340009030301007849030740314001d420006401c54161101603842181c1002034008840300080750702c0c9000720340301c0141e6a4040006a549880d0425400c000f950299201d485609138000c5808400c5541c1c6800840c684210b00d8000c12403100628001403a60b1110301c1b0310f50150051145c0c0c3c03021803011800d00b031015034248c1c41d46c070b15051301c440242c0d42e800001060450705a4170f9000300b8100c500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 561659541 1250 561658291 561658309
    0xd0903080f0105010203120f0402010203070b0c13090506010c122006040203250b071e03080a1d03070b180d050301030302010e030a0f05071104050a0911100905150702 73
    0x40265203401441c80d10040c078200503001078210505650090060441c182400c1c1c44c2140d01c804501c0060606403240d1005074658040c0b107000500850380101005641007840e0040c08900c0705641d50312000503910003c480488034280d89840c0090340720713590800170038607404135a050511185000b04415141c1c0c10044c0c0c160841c0f1034080180d40000051005510b070420140c0654142d043e00c511314001030005030759000346140f040710700c2c062000c82c280042c412013101454002c400c6240b90900413166190003001240c0480c1c034105d000d49000c1400000c0071424940f40c4584a12000544c5030800c82e4581e1154104000e019041d00700402d000700d800c81c3e0082c01102c00d202030355200c81e41c07a5411807501900391903020081e0040f0f54003d105401c00c00e5072010302d000c4641d0850615954500ca541410042c0f0840c0c0d910140c2c100f402e040601c0300d000a01d0303002e20101030044901c00120b6040b0402c01c10740808031800c0782c1c00900114018052840c0c0150b64031105400c04020030b1421403030360f020401c1d107a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 561660791 1250 561659541 561659543
    0x130503030301090236010f0311030a0b030f0a05070902070807062a0f0f081e010b0d11040e06090612010f02070c14130b040905070e040501060506030c030109110d09 72
    0xd50082000c040750710440c061340440c03109001c01420040d940b40c1c8080f07466092020803904000c1c5025a139503d090007582700c0300040c4901d401e81035980c07504056180180c00e00d084854001d20078a16862461600482c5d08c40c0c0d829400006031101d6464030014401035040480c060340d0300401000390000240c0b40b807241448142507100c1425840c851144808c180004144810040c000300d10a031503002c0f41c7c005802000b041103401c2070032494032034080d958000e01c03004000942602440b4000726009000b2409482d84101070041801851011107003c2c05c44d0059104400d42e5140d4140820002e150441c0d80304e030301c5070b8090044000103843c1100c242c2946c1ea04801e501034141e0010309d00d4280300c16003009501a0100c4a6503000003241203000c240080d401300d6100021a07901e095901040e502c5070403004c5002c0d001011181350a4480c0d175411490601079400b25600e43c642103001a1604151050300c2c4644460076889045a10f001c20030300c040c0c51040004010440200b000f00c00460b0340784034000a0b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 561662041 1250 561660791 561660809
    0xf0a030f0218010612050c07050d0e040518061b070516090b0105040302010e240a02030c010f1b03050603010603080c010218123f0c060604021e130503030301 69
    0x444840c014491201d5101940a00d00b0300c440006002594100c030100b51107034142a0005900c2d510900148468060884000d00b02d00505080403000c540c4003107842d08941c0100d400300000c6d21204034195043c80032400055440e086800011200c460951505e01c08039850801c079464500c180e516181070001d211a44500c01707011080501010560340f0403c0060542803c0c654034060540e00042c1c03507080060545841110040e1140b0080e0040003203003c0d0009407001c00380d03260801c02d0b101135101d03009100d9111481d1b1038010b50284802c00303070040c034012b060515505140c03501764400880213043d004050035010340d20b4450000010741c29000400440443c0000141c0340c56203e00340c1060803080d40d224030b2080300b407100c2020040b44003090b0003030800301c0c0b400d0141450b9100b1391141c0100c12507080d4032899020042d07220000a02e62001000c500c6960300541e012030b0b9501040001f02d01900d0440c96000c049c440e42c1400001c4901c008200ca0001d003040c003c51180c1e0340d00002c1c036592090f0440007403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 561663291 1250 561662041 561662063
    0xd0f0507240e150403060b0d050d020a1e080739080609390d03080105030f0f100f0209041b0e0d020310020306060d0608010c0e090f0105040203060f0a03 67
    0x289034090503082c1906030469810710114404041070116008a010203841d250307a4010307a0156550340140c070a00240e024054400e80d00078150080d4035581514802c0d641140c0641c100c400c801c80e05100d41346001c1c0e00904c00c5007802030ba900c840e11082d001c0182115000500c5014a00800c03540024550304200c80d004400c0315401c004425051581c00381800007240e01c0303440380e419200e0481c05050003e489155800c10708518070b1540c400380c44190600705400c0700111442d80b05069024427014140d450a038220740041c001000c0d01a40c03070400d4000350034580c00c1101180c44500180d0000744c41034640f00d0026080c26441c07030001c0d00300c4151203a4030b8001070000060f50040c94105141d8209a4000c5410f22074184032a0007082c0ca8003c1142d4075940c0d1a4000000344082d41c46505561f9464030f0010304100860b1642241c600900140002030081110b101c100e07105442d288000c8e81c82800d209a88001903440c19061101a420241a95601c058184070709052a16114001c2c401503000710940b0755 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 561664541 1250 561663291 561663359
    0x40e0f0627010306020c0c040609050f01150206130204090b09100c02010b0f0904030917030c070b03040305160804120507050a090b0619030b062b05060d0f0507 70
    0x14a011410704610032440411141e600e40000c0000141140d4001c0c00141c0d403200e20805407400d1440140c885035000f03150240106400040303a016070302c02e0480c505a00c10598950143c202202d206146680040c0d01100020b1100082000c0030140c562002c0c00c0030840030041d584403807a1500448452030107610064440c090300c9150301074455020340703a0008208455101010400350482081000d0041044901180401d031241201e80020041109885103100c11804c5180d103d40c816140100c075031080000100300c030014001101e0069506071501c03850411382d400c41c4107105d0070800781554401d0091000085180a44d0220320b802032080c006411240c0c10003040040c90b94540c0c1158480c10315022012140340c403044e00312003141034681202244100120421809020700e100500c0d0400300114100c1d190315201941c546c01c0f00c900021100240d10342c00440c00481d2811141254003100310501c19000c00c848541e0603501d40c0c02202a40e458607107585180a1902d009924000521810703100c1c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 561665791 1250 561664541 561664549
    0x20a020106060806030d03050c1306090f050a0608180a14010209010305130b0403081915060314040b1302060720090a230a0e0a03021b0a0b0706020c03040e0f06 70
    0x44040d140b14248081c96082c18000700340e07101e04c451102c0c02896619404100804070031010782c0c040c030410107075442809440d410014000140b600c034600440440c1c2401040740d00c0d01000c07070001ea0f500d0750350309815955030070501074060740030140c440780c1802001c0c0b9280224020740c40002d1504994400540d4900000c00011b0446a008000a410380c1c9081074001c00680414100c0c3d80191b0103280980d140d4441e0801e03040c0650510040201d031900d00307500644551540d0030b0940441d40c4589081140e40550350060f0f2080c00200d03030080c10032402d00001000242c00d20b6aa02ca1a4009004a814540d20340e880f5404c0d4402140c1c81d148034007001d01d440d04d0515158643c26070058102c181403040c0c01151107044102c100c1d241010245003122000500d1011181d4400203940d03401c0e80883e0406c0c801400d01030740312020b11a000082c180300805a081a0404180e540c0c2110314004c095132921003d611500d0080d0403501c00240c071804204400900e000c20400310702d02503145043d000c045030902000f04 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 561667041 1250 561665791 561665801
    0x121605060109020924090111120406020106090c030c0e0415031a04061d2a060316030c090803030a0203070e090f160c02010f110709020d0915020301050310090c0f0801020a0201 77
    0x40c400d86904405940b074002840c0282c4000c81c01c00c0c00d0041950b031170540c0380727410042c00d01d03070507490403101040c005542541500300404032000c08000300403050301c0c007008400750382c0d04a105a0120b10191041c85090600d0b51081010044180f008046961030f5500e0f52848a4011070101c0b90207030000500003400498072070008800384c140c16088101c030041c4015a2610444d505045444425a02c00750407041194102d0a051000070415503503840c0041d030808080c1c0800000000003031030504004074203406032004205030f404d460001c0d400e60750359200790406940024007440400603100650072150716460500c40c000e81c04000c5144080ca40612149820540300032281d08010514084402607600034440c4503110240d403505c9a441d40c0e00d200400c0c038050355a4080c03580140b0006100301c1911565018000d500d100b80c19803c0c580d0080400c1d07006a0001f03004140d4150800b5260b110403040a500c0001098811007005401665403121000c80801e154804222030b50009240280c7c19420302ca8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 561668291 1250 561667041 561667069
    0x10e090910060303050414240c0a23070506040b0708030a0e0d02060115080c04050d02030f06151201060f0b1b011406130e06163e0c01021216050601090209 68
    0x32310300306030441c03503a50383c01c01e0f40d959030200c04510028520100c00c10030301090301c400d5040390048080c0700f2960705021540d130f02625400c1c0540100c600c0480c141c900a8110350484103c8141c0c141003084a4880c0070b0190304c040c01506800703540700c00d010341101080c0070700507640759a034002d00b01d5503141c894030f00000d0714542d2040041004035001c1041d01411641941c003550b205490808089815201081c60041400c03400c007214400d00701081102040012507912144055401c0d984286104003200e081e11454014854030f054070714014090310b00b646010b03181407800940e4a1040760482d1a4840c00c4a401660310340d450702200040000d14242510b030751118060b626802c1001d40100401c56072a00005030144c050000f04104820300e003072040360030312081c20664040ea0509045400c1080b0484101700020720601c0e200c1c0501101254040380210f0150410f030040e01c3c1038061540d81e5596580094000c0f1800015800340b040814000c00200d1702801890070b0060ba0b5039000b00400c1200c0038000c80d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 561669541 1250 561668291 561668299
    0x7020d0e220c110a02010210020c24150102030702090f0c1b0d110c0f0108060d0602040f05010219111507150608010f06050604090b0a0e0906190b010e090910060303050414 75
    0xa41800187d80c00074000445000c0444010385500f20039504038144000800e021701d08048004910a060703420f403030198010481d9070341c4040e48040e41e00c01a030300c90203500b40195000c8049000070f120790b40a00a010703807081d1042041c6280c410b010b282c050411090464180305075000140c1300c1c1c1e1090b0400d508114100c181c0c401400341d4824040011134844249401504202d1040f0200700c1d1034483c18084101d66501620940d00d46483e10f03141e0303202c06094807410f40184910040c00c0781c1502c004c8002a4429001148003510a1010701800a50000c04e81400c076900d2040202c130b07022405120303410013480440080418220b281000c05829601452155040301e0b00c1c0c004100030a41e00c0d0002c0b10101e035514040456000201d20000d50301401d00c0d403013103004440c0c000401a060a00bc10309038032a185500340b07800106211001801107038025031400e40403941140c1820518580701428542c440306490465504103611a411002c3d00c099038800c502161001c50b00344400d100306a040306500c00255 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 561670791 1250 561669541 561669553
    0x1a0f0f0114060d0f0b040f020d1103010806010308070201020309060d050f0105191a1209030a0305010b18131b0f120509070303051303020a14040b0907020d0e220c11 72
    0x10340000c00e240308000f00071001e55500c14004a0038041034220210384000104100700d601640080e0328060f42c000d072103121140340781080101c4007190a01c1138034141d50401e0020720321682036039602d15183d8482001a410741c4800c0c000401d9035a40c43c4011b1a034a26000c40110b41e80c182000030340c0b84810180c000d14420194820001046001e0390761800407940c1602c101501c0084400000a051290707400c204512241c0804100b0750400c00001040b6201c00707a0f60811047c3c0e03175040041214050035007c0c0090903803059203000c2c0e80c601110410f59103110483c00240c1070418104044050711280d5040c40803461101700560550f801c14104800b55002d0781c4180001e00e82081c85e80e4403030310170380002800e0100120710f83d0030054072200036801443e030141107803640700d8031640d0300e0640380c54211140d4442c41c1050350030581400c1c07481480d0301071764840e001032153700100b07481030304c84103000c41c02ca0b038016004040808000c80108600c04030b00c07502e0140028440c0d030303100005014041614130001030b07501c01c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 561672041 1250 561670791 561670829
    0x2040c031b0e120303090610061704021516030e10030209280915090606110c01050c0f0703110a0e0403090306020703140c010b03070909080f071a0f0f01 67
    0x64410444040052420b00d0108940c100001da404108100c0b01c5038500c4044100201c200300051042d001e45c1c2c04240401c0301a50700c0d001201c442074051468a01c180d40400031500501b00f069400308040343c000380d083d04020a540c081040040b82d14001e500141c803000c3c000340a03003042900c1d4404ac0301c032441c0562500c1d0604012400701c0e984050314040504011003504082955010a40060300c00640700b4810790f004040241c1c0000c02034010684114070b00388000841030301a4488420102d041c1000c1c10002190748019601a0000c11440314240550132000c44600703c288884e20155204e2a03410039009400000d01203914483d420021400b401c2c0390a0102183d0070001020480380d002c640907036500401e1400b110340310f03008004c04180c02c00c0402d00c405841c5040d0482001180c3c25002c135103c80e43d0f80c2c001c0c007041c2e403050707000501140010050340040d0300600c03005046903800340c603400c18000034900d100201d14070f0131a441c2c0030003030303d40c1d0501800c0810441c0e0517006040e0308600881c0c02580b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 561673291 1250 561672041 561672071
    0x6010c0804140609100c0b01050d050c090405030d0204121a0403020a0f030c020a06050c1209011d0406030c060c0b0604051b0315090a1409030a09300f02040c03 70
    0x5503010340b80048485848403603543c2d585074110303030100b08081e00711414443d08040243c0441d40c09601218250255000401d09041804924820325000401424a800705105010701010081c01c00c1d941c80c0410031481403c0c008a000400003080e9105604a80b00c80d58240180d940c110501140f14a2002105110201c1d0b4005414485c9e10f802040d001801c800038581070740e002c0f601440094003c4402900000c40380c0c2c000e405403105140742c005690a0780700c8d408010740140304c3c1103d010301040c9268001100003019113030102c1159805040010030a441c0d485a0181c840d0139480b11002618000080040005c40d042c0305070042c4064030180302c503040a00d906601810f58541e05046c240c0084006480b0100200c04c444203250050882d43c200c1c2040c03c0c0b0500546000c034030800c1001d104002003030003c0b100000b16000035a11f941c0300310300141003c2108080088180004c03402c0325911200d5408100b6909200341141d200d03040c0c2c00c0c0041c1b45441030106403507a0072000024103141030100e8040ba40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 561674541 1250 561673291 561673297
    0x90605090708070306080a11030105070f082707141228060221270d180b0a021f05040f06050601120207052b050d1107020612060906010c08 61
    0x204a052542c010760710244120003c12407544043c50522442c845c0c00103018440103c541c9a62007640244419074a0b00360a032145840c400c00d840c00107840c01c0c0041c0c2c3c0340b10580f0f003169000542501c00080740b9942807405292a8958000d02040c80418003a01020316001c03035083c40480020000c6c29455800040021050841c1c1c41d010301c0301d400c3e100c1030b141005183d074103c0f1800200ba15480070f0614000c421440d13404400c884105015031001c0010f400c0076079250400c80d0640028008010451048004503141311800c0d804446100b550040401c101c0b0300d200280021231155401060b070001031010404000840342c103403240d02c0d0f28040604c80030a01141514205075040300000c51951118001280c1003e40d084c89203400e06c3c80032988a0800801140240611400100407540d00201e0510101e020074481c500340042071041000d000f04403040e1f0440050304c0d05815009080042680200b0807591041c007090715410b4401d0100141450010300c43c98001c04c0030310342440325a8480e86d55403a90b02c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 561675791 1250 561674541 561674551
    0x319030215040c031b060306050303070c0314241006030b03101d0d0905150307050a0e0f09070807110105060303160512070f0606050103051e061816020709060509 71
    0x440c1e0341c0e000400f80600000c19800440c0d000300c8154034100f0b49501c1007040140c9009810001e41099400150340c0f03030000a441d1040d4102010103070b01440c40c0d80b00c0b2100c003051401c0c408580250000c040c1d1107404201b12280480d03080e002d42c4018035095880c2e9000342000e810040c01e06103080c0a501d5079840c0017035131408102d0b115400041403940c3c540d14280c800442d60303501440f4820407c41d65500d60b80038805a08a8000795000001030308401108071250000300c82140c0042d9061000c150020301c03d40030343d0041070b406001250519080c10109008000844090010070603c00a0106850380303c0302d440f41103802c0c0c4008026a0130000000303a22403241500d50941d02c0555224030050040600c648500300814882c616600d49091078040000844008107840301846c1c550000351950080c01668442c0c07134556443c0c1680d800c0316452140442015121a402801c909464403020341c0420f4050300610040060000c0c0b80710b0550000e292038019044040e1940c1403482c00c110720380b03030020415005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 561677041 1250 561675791 561675823
    0x4031209060804110117070207050102120a0503060d1110030504050c01030614130f050106020a1407120204020c0c221802090c1b1501052d04180f0c0503190302 70
    0x343c10340e90040700c843c044001c0701c06181b41a0018400c40075000500c24040b030b1820f07000d0300e022210001c804080c3c2d01900603040301080040000881616010742400407280c401c18103030014105d0180070600b0305440700e0303516020a58840900c03091100c10040408007081c00d103424094a41040d006400d00c82e540f210351401842e00922090840d881d0760010b01d110489a102000107607036500d0025a621340890f42074410b29150501070804030700100349038065030341c1002c003841c01d9040d590034070000b588008056070481c01010103031071150343d56140303100000c4200747c6204000d42540490408441e0651089000c9181055080d0016103c441d0500d9214141c01c3c03450361291160562441401c4400202c81024003c865250b402001c05150007816524151020f40700c054414514194a2421122101d407507a01201342c5816484c003a080481030b500c01e04000308074401681e8417405102e50645040702d035100c83d10400d005505081103c9000501102c681110526a6440c0a9114001e0409407200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 561678291 1250 561677041 561677063
    0x10914180c100c051c03150b190509030303070c0b070f020a02040515030f0a0b010509190b01051b01140a02160f05071502060601080109020f160c170304031209060804 73
    0xba00c0d000e201c10384401ca421a060300e500203038400c0744201c410010703c3c4400102c1e19040312800e01501c415116016039140d82401441d00450000715120144450a0003003001005c00c400c03003280c1c8050011310f014040c0d907100e10a0b88801850240024900186000c0411407450244004c1603030000d010360390359406070740004983d00c502c00b030b5030011079203800040c4d014031983e905107a1000e400070384000031a010705201a82642c90f0300030082244016540101401c07101044000084030651203844001814100303503142400c040e02ca10000c1d200044200743c00d0350344090710100000c1e9030344103961041c0c0c001c004601e0030500d42103224035004da40c1c0000d0700d4140c145100b5001c004d8100505000780000c14441514006201c41c001c0d43c58100b03c0b2080d00044144c00000f554101900998828007980c00040e400c000c0c174411420b20040c800c02041d5013a05c00e0b850000b07003101340805407030017100191010315525411170400100707501c3c07172406040c10801c00007030070444640d100c5900ca400c281d118410502d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 561679541 1250 561678291 561678319
    0x70b0603030403052407020703150e250302040515091b040308030c2701020d050a02071a030108121315030f0515010f1403070503040201120203010914180c 68
    0x2180d40190f4200800714842d6141240400010000300c2c0a02130a40f1074410076507580a40403030303c850726840010000d810400d4045085030594104228005500d4111039140d15230300c01c00009101340c0d0707803004c1215600307140900650410f0f000d081c3d130000000030304214480020010612402004040c0074000c01002220b15408600e1f0341124011900324500d42c1d12400c040d40c031251039500c013401c00060400340c590b01c00070746041c10f690f15401000580103400c90181035003041d030340782c0d0143c0182d000b1030048240c003041e0460b150401c074884230f9901e6081a103940c1880322952808040b910310507080003042c00391205240c025414001503414150a006600110710405d4003d0030401c803424641d035013010100300000741c807207000035850b940981c1d40d01403034103d14070191000d0031000c41c000340100e820030000384001c2c02a002103030002e10615011002509513400401241c00c00c8c0c0100c5819501c80200c0d4104645100400360007001c50b110941c0341300b60855000380c2e030396101c40c2514081d02145a0000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 561680791 1250 561679541 561679543
    0xf0a091a18160302060f07120e0405251d0306010f06030c0c0c03020402090a21120c0f020904170d0e01061401020c0f13020d02070215041d0903071205030907051203070b0603 76
    0xa0030550784081c04400b00208e8010160401902c402c9041c0601e281c000050401c003840413803101c42c00e949900c40c02c00d000500400711091200036485040b00c502c00015401c040d2020050240240541782420001a0620800500b9500c4002280041003201c221100100750201d2070001120742c11079006903105148404aa4115034a5002d82c5a00082c41c409041c0901c1c144096400e540c803410300c07008500c0544005070341d050005040074203207601d4402d1510050801c074070010b800c1400349590aa48000e0b00c11050701d25807019803140285511900e18140309082401008054098030782440d03066809400001e43e00c00e42041054410449081c1500c0700391a0072800c101e41c40051101950b60fa080d140c80766010794860f640c128041c44408101440d1034031414241c5e42a03031160240c103081e50341007040401e142813018040c0b441e140000c012010010700401424000d15400361038460310f81c0f8006c44181e042403569440180207840d03500f440320031074901004440f019948000d00c48aa070321000d000c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 561682041 1250 561680791 561680797
    0x40201050a0c1e05030a020c1903060b13022205010203071505190c0c021302030603060c03090c060d0501140a0f05011206031e140a02090f0a091a18160302060f 70
    0x381004090f002090090000c040018520280306800300d68545440200740300c500d014030900710f41c5907412018248002011500618619480188070400b4840142c41d580f00300d9010160544002d05202c4000040c00001d0b800e24004000c01d0010307508109107034448100c1c0d90b8080c58449640c1d9625000240300b40d440c01045004ac03001ca1101300030780007070302ca00a40b021245c036800340d115010702c15200c1c14102080c000c49100f143d024000c0d102c0c58807084200c4285030400ba214074100c1c003400c2c0e00c84800f6102c00f005002000300b01c1d000421154581000303140382c0400002d1450090381c103407e0610030f0000c903407000d0013110028a8220a80c1f0f101480030b500900706a04024000c9040c100d641c1603510340200c845000071702075041400902c0c15024010f40d21941c0032002500301402400107141140c10412056102c1100e03240444e160341550389440400000c00c1d18040319040520a111420382c0107000b4642c0700e0328880080084c080d01300e60309000f0210611000303100346d000040040d880041ca50070303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 561683291 1250 561682041 561682073
    0x40612091b060f02070b040f0b0310120825030207030219050a080c0a05030f060a1518050103050607020c010c120c05060109020702040b0607020f0f0a120b1905040201050a0c 76
    0x1c200e015450b0380008180650340781c0003000502c02c21401154a89000c1d048030102c0ea61f010891502500d03101c0a204990030041203183d80c1c030302034080060061000e038003450361103103da071040f691800655044000107840f0001d03162200300301807560380065000503a4800b80d940417524214100d040d01c0400309458926002a608005a0400020456800246803d142d05d0071950030300d16545800615a0f503020030070000d001640000c000c00c01c01111684422601c41503900c034241810346801d0817118612079128a5a4100d0780d500c01082880003e10032203030481c0300c80c07010380300e0780000f080000c0120490801c0600b0030030b55507500090890150f603e030b14032a41e1203003d4540c50b42e980c1036134500940009400764041c6082104912282c0b030310404a40707480764024080c0768607200900c1401180c20071816002d03040f00e072400d0085003845840099018942c4201c2401ca8640350002000b9419520100d01039583c6040070709110050307802000351060f01c00149000c02c0610420f0510030805400408 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 561684541 1250 561683291 561683333
    0x405180a022203050c18010b0d09140d0305150d0303050915040b0403090504050f130f021306180b010f0c080409050c0706230a0c050c030d0b1504061209 67
    0x8a0351403041607000c1841c00301c84c000c00c01d6400d00301c00201030141c4051800265440f0044200060010300c0580b409402880029100050081a41d507a02c2c0f001441c03980c84001d035a4000e016101a15030700d401626880b100038210240000007210204098584500d40201415121000920802c42c2000401a09405090303110b1190801d800d101d2080c2d582a03400707800007680000041510704083c09110f000300c0e9895410510f696a00d04a94480b000042c001c030740c1c0c07a0100040b607000d030382c4425407900710401d21180000c84070318100c20440b8030302291039240e0840d030408100041c1681c11041da518007111900b410031006000785001c0702d05128a41040c8089440c01d000d100405103210064519140318560400c480e010404400c540ca4000d404c0e182400c6005c0000502c1200c110341080810418900300f150620194000c85811600800941446c2c03980d40d00300c5081d03924200c0d88035460f60615600452400381807610007031908250925550005403501030341000c10140c480b8100144403901 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 561685791 1250 561684541 561684577
    0xc060f09130b09071d10020f0604060b0109050f0310150e010b04030311010509070611030c060c0910140a0c23060a0608070e1b120106050403060c050405180a02 70
    0x1032aa00028801c1c000a60f0040c0b40e190000340340180180903e58102029119110300a40b00d0410040c8011500028004600071404c0b280e540701c80c104030440c011407040d400071030f250a1240c0014030b4910550301032441800b255540c484035807004903c0119002c0079030f40202d1960300d000328004600020790302c08a108001d00e800012070081603000340055078425a60307000c0001a0007091802d1712030944900f00d10390417051007004210b0281c4205041c6000c040305032800e00c1d000141c2641801011200c46101480005a036038551410f8000100c078805e0034101281341c207110100e021a540140c018560500002204080078040c0d034201251081c1081c801c1384503148801158940c407a8019076688001a0400d0800324010001003200400d6030700d955002541585c607014031200c664006400303003141080400ca0924041081c61406000c1c000303c0e1141955107186150503002c4442d07000e005010481e0600044c0f085954502080318011820f0b441e02c440e0b6240c0118440081c804e18242c00c1d240c503120 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 561687041 1250 561685791 561685819
    0x2190501050103020102060f0c0a0f141b070501020312150a030204060602150a0c0c0209060a1a040e011a0306040f060e0117100b1c0c03050a320c060f09 67
    0x5411142c1030740c1c401e909441039501c071350000e503d000c142034510050210301030254440040c400d40d02001c940c0c100c0c0c0b41c900c80c0c1c5a400e0300c100c50a9031000b41d520141090b0840074114280c5d040041d44003c160a1000b18548440040f03070003c0d40070040c2402240e48001d4001e041e4580ea0300e00102c0c06903070014000c000c0643e1f03d62010303544000340c48021810741194400919044041c1c031031460500026250214051126420055996002080b040d400100c0da08003007a16220701d00e4000349044004400d8fd613850401c101c1e216507078016030102c1020201580c40380d40180c0c00ca419a604a070056030045405252001980d001d031559030410340d0102041400010140d509400608060320039805980c09010b085030f00c0b00555402c40600c50300070b074491008000c0010740758842108a4022094001441d440340d582c0c1d4108207600c3c0054078010b006090707100b020364040c41005c454140c86aa1402c0f0080141000d075207a0f1880300360648109004551811118281012a4940f030402032554aa43c00780c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 561688291 1250 561687041 561687043
    0x50f0702010b010905030706032a0302040305120309150403030e0105091006061b030503040804080d0c060e06101509050a030c0603050906040309121104090b09010e1501090c021905 79
    0x21990040158240a5200459402002c0001c01d0b240003902908079075081800503070260510700311030b5a00000d0319030303200410f049094060703028480303a560241c0c0d10f030f155080051070920350001d4060405020014003030800400110601802490f0105604503540c42c05c0640051900001c108400d500f00010000d510304040795608146c50380f2041000040d4031a281201c5406240003181c074903440c0e8030001c401183c061406180e0161040070302500e45501c42c980d10342088a070009850218035520000c4042280600961130541001c00007000070307103000e178102601001903115605002c100f05000d9000e0038403a00caa100038040140c130191400356a840e00e5408a84244144e000080c070700008200388410100c1d81c240102d40503074500712003900700340a010100e06c2444040358144c50100030240e031500e4602500202c03501030000000319142002040b82540c007405641000f58100b2005008038009002d401e90540e00800c00010b0480705203403050345855100c85146240c4103446c0000d0041140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 561689541 1250 561688291 561688321
    0x403090302100c05030f070c0f08010b09011202060a08090106080f2a0915011809050a0c02030307170a1409030c16060c030f031d010f05181c0507020405 67
    0x2100380c0d03189440e06010b4000325000082c5070801001c50f0400c204840b20302c42020050401a1f006484000f4220380e03c101140360100300d45d1201c0350304e944808140f922494000c40c82c5004043d009002032440325141c2c0000d080b40303e4425072030305001c00c4202080d203000b402d41c0888050f020980464090140b5803c506540310501e15020603600c0d01401c80c1900c004142079024141e2001401070390003619506800b07942031498617020303030411a1400400a04c90301c50b06480c0d00030304401100003000c0c108980c2c0441524500c02c0e0310b5040d54010414031061561025a8002c500c5020040e07290301e4a491010001800d03010b80114801915042031000c0b8440c040000c0c00000c440e20101d8081d151031510341c840650140c4201c4002c68982c0c60000c010034018140c03000380c500103240001d40c01a0759101e006603890451070208150390348940500d00c44a0302c0c8501a0030407040c0e88003218803890030041755941c0192498040140e40040d0701c51030514000c030161752465a004000340007600d42001d800440d04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 561690647 1106 561689541 561689543
    0x30a0f0312141f03030e04021b03041e09110a050f0c010f0b040c0822020a17010c09150f03020c030c0709020a17010b030103020904021804030903 64
    0x2140e0300c503200ca07800314001c0c260141e08191105145421540403c844440e258072824008207400440969400b08120b40250b41c468525010603c1080d04900d2921584000300c4d001ca080c1c9070743c104e1160b25000003004080c0c1c840d03a0b6000841540c0c1c004c03280e12075a840c1040b503c800c6901c1000180901c0101050451500300200e24003821288040d001d405526070340c640c200d4403450a4026074010300c529142140d11030130244541030612100e003031140c1c03146501503e400115240d90384090001d014414900700800020203840380602400d03c03c0c0000168131047c00f017001100741c1c82d41600d032501c40d56903004c081c2c24601c047d402036010380c2e060319441c401404924611001000401c0c05490180c0025031030740748240c405012001c0c030800c1c041c00da10f4180c0c0140015901d160980741100d030104da44440039103907800400c0401d8210200014650300704000c2000341504034080908403 = true := by decide +kernel

theorem cover : BRFrame.Cov 561510791 561690647 := by
  have h0 := BRFrame.cov_init 561510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 561510791 ≤ n) (h2 : n < 561690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
