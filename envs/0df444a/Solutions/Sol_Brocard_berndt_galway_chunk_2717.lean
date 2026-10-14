-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2717
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:31:53.442113+00:00
-- url     : https://prove2.me/submissions/d94100dd-a5d2-4d15-a7e9-e3bdebbf7cd0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 488489208 ≤ n < 488669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 488490458 1250 488489208 488489219
    0x602030c0306120f03040311060405040e0f1209030304030f1403030a0506011b03051c110d02070209060d05030409020906130e0613020301051c0c030803010e10150c080711030f0106 79
    0x3c2c510309445000b65401c0000b00d003140c004000207039030542e0760044440c80e4201c03174000484e585010325804103601904010a9122901e0046043c0e10160344540503981daa9640038030703e030003d11400e84005e8255004210410109181c540440741c00ca1184265010585400c1d503040d02d9a001503403030a407480d555905001c0c1540e0402d400340c641e111018208600f0306e1103502d010388035025030246c034007062015031089030180c020341e03001079050524440c020f41c171144c0c0360450000942200404174000d490f80d0006c1600c526100758580a8541d200c00110710782810700051601a400440c1c0145c0c0061041c0010000341e41d811041c4000707401c2d0600d2003c41d601d003880402c1480f480341c0703504e141000d1040005000545490402045424200784168000080f078070f801003072100c0960018000a03030102c00410320801c001c60841c01803444103400d031003003500c03400b0582030741c0303104c400c541c000c40c000103d1040001e0754040a0700c0064001c22aa030440c0c031003180402d00701014001130322046e95454609108 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 488491708 1250 488490458 488490469
    0x10b04022106010c030c020d0201120510060905031504081602040c0302121509061002070f080c030706020f0703060e0c030a03030e15040b0f1b0d020702090c0a080c0c0a0602030c0306 80
    0xd10010900e8449040d50454030f000d40341400241b8047c0c01000c403001030b4025640225001100080c60744404c200342d1821004172880e1824500a038400690310b40307400600c5190026401c0c5100342510795842e0103440304d43d150700c0117030711960080d60031910446002002d80c3e1140300d80b054000b81600c001d07940b40d0443c6a00d00310032000034421103000244031007003407240e1140504158070100981d155206901e401c04107914080349648040400701d1580c40205204901142e034503080fa1040c1c1c00c4920443e1500300c1aa104c1c2007171a011042540b0504042010031030603040321905a00c00b46c20384450300140000f10341889628941503000c00e0720340c51030310005142046070f91404502581800c056007400c6c0e40c1c00304110f502402d40312901c5246008030385c104880b1612000c054180720f542654540041610401941091000b6489100e860340012072280307802085641c00354407556201459905c4007404411078100c000190381e00e00c1110440b100107a198070066005090030301c466034481c940a0704000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 488492958 1250 488491708 488491711
    0xf0705010203040f060f3b040e06071d0d051c09031212091b0f0906050105120a0212070f17010e04150216031106060a0b0d05071407030804060b010f020c010e03010b040221 75
    0x8d00803031130006041900540444e406070459401e00d01701500d222a4020f0058013034201c184d066100d041000b802080180c00140c54410030b07a80010407201110801c000c0e1096022440041c200901055000180520441c4000d00d401c001100024210384291981d80c558520030440300e00004044e1028003400405100c40300051150308002d006250420000074003900504c1c600d4641e60341c03464041808141e5907016202488901e0000050902d40020b0040c4403044890001000c110b01c100802c0d2000420350b43d076070503100e241e0703107007a46500c542c0e44005403404214044c4d51501e6007440201d503491407040c45000d91600995a43c40004805401c05007000c0713025100034414500382c1420480c60b801e034810b07a560101903000000d07407966480c50540311030071081c0c01000007590000b903100826820400fa140038a0080808000c211825401919210003800300000540d0007078907460b1682d88181c1c44421074201c0900080351103114500810240c1e048900041d000301c4459a000c20b80050f20803915 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 488494208 1250 488492958 488493077
    0x120c0d0e06191211032706010501080f061212040504060b0a0206071407020a03060c080a05040809060a02150702010c0f090b18041d0f0705010203040f060f 68
    0x903840c0070301c2c400803188201c50100d440c81c10b100081e80c04a91221807039200500c900100e1102c29030703a2030721600f00040084101081c40807401b0521600074084000075a0a06803941a190840c3c036846160055200c807a00800642e803052501c4036003100e00109209000507041111103540d20b5604103401c00c03003520000e07004290a542c0038008085690381c00074803590003101504100d6583c42ca804540c0801e0b00c2000c1c8040e4200c00c071420000100092584022007101140c5c0ea0b40c011600c030500d001d0103440b0140d034050403048003403001d003035103140060091955500a00450381210743c828180c3c04d00140c119540805070750f413100e101c100c40b0b400201c4004038006510b84402d607039040c080240300324080d040196800341c0004c01c144a8a45542d0321441d840c101400d54416852000300f02596584040c0d03c11070301030300469000155030750001040e181515843c2c141260354505200d021201d482d030080307000d0b040200301e031000b80301c0754100c9041060062000035480c894103080c6400300c00502407507100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 488495458 1250 488494208 488494219
    0x302070f0203151501080f071b1a01140906012f06010f06031104061202070303020c0a06060f0b0703140c071208040e0c07030c14160f030b06030109030909090203120c0d0e 75
    0x2c20911000103205a2342c003070300034141002030700c4451144140045071884001c200c046500d1031030f010068240380145c101ca07840380b4080c84011034201400640c0700c043d140c10b804103221921320b44014041c1101d42e00c8165913418207140c80d085248a0f907261510a074440d0131001506642400b015900d4041d4614007400824040e2402e8a402002844a445a0410300e251503010920000705442030b01200e4154601c0d001721082c0c003c0700c0c20a50010728081c410110729840500000440d680404d0239900495015200c248502d120200e4865599210002c0540d01c2d005003000460070003611a0030040031805000003e440f181440082e140e43c1c030010340000202036046c05120002540004038080072580441c041116042c0704254520b4034031880140440002c41c1100400c03c414420341c5481168007906400a03a83c80364801e0500700c940004c0c028000800f5400c043c00035005542107904e101d840541110a548464100c000d016001a00059603503001320b041140341c10390080150313031400e204880 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 488496708 1250 488495458 488495461
    0x1413050f0301052e0f0608070905030d050d0e012003040b09120406050d110d0e0106090b0105041a09091905060109150e04020c0f010608070608010806070302070f020315150108 77
    0x808840c00448a814558403c000c0360130421030b8207004a6600040c0030319032100c91015102d00e005400e40c0d81c00c0300d03240c000503ca070000080300d160010340e64410740d5032038588515000d12450b60402801049003403009541d05d4511144015054050203ca400182c3c52040d482e810070740303881e060000f4050000003144d40310301d54101c00041181d00325000c407199414201c0e950240c00e130150f0080c10079820810220308001c60781d4ad1161000e9000303084040074600003080318580340e803103103022a210303a40c07014000340c8180300911a0415108107078045060110400b41030000340c034002483c1c1d0034102c4803079601c490641e106031040c03000380c029103800460900301085400e00780500100740381b9540c2c00c42410499461350540c12603c80b941102d0000004105440131240318078007181c0a04a184207a150b10b200300c1c03030000341c1d0b0b0340b08481003030580b60040b000c0e00c200c0d110040100c010750000403040e149102d0360808400180d904001440b01402c42c42020b008a00d42500c01d907400b01c11140c0d400c0d060069040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 488497958 1250 488496708 488496721
    0x1020403211403060d0c0311010f050f03070f05121509130f030f030b06070c0e0c030c04091e09050d03050108010b010207031412041e090207030206161413050f030105 73
    0x15851558200d2194143c480c0d8a090010304c6405003103030050040102d280010040c0000715103003900001c3c007031700d48100b2840245400c46a0344161070034840860001d00108032328030311849101c00c0901561070f00c541082403200030081c014400341d901c0e15551001ea0403408a50400150344c07a8051488441c50400030b4103030311070904c02040d101c1d0003410000310311000d85540d030280d8400b044180020740240d031110b40525150ba0400324901500084500350b0300016480c001040490748540040c0002c80d0809142540c00000303008841240d552101000c400e6905010942c403aa4036028000c40091a07488110340d0003604648040e00201c04690400c1c1c8000d07802d980000700f0000326503000f686030300c20703a1140c0d01840c103020642140d00c016140c00900045c8014000c072206883c024000c0c03400302c400e591061160100e1081400c02000b6030805000946100f000300708500c40d0110310700700999040307140210810f03294400684894061455101804182030142c610300c200742090340200860304050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 488499208 1250 488497958 488497967
    0x30a1e0605040c14071104021b0604020424090f0209061903060816030803191104060905010804030801032604080a0507050409080301030f0312021305010807030c051905090d050102040321 82
    0xd20b006d08503103000c002552030741d12164101c4605014444d03215940e908464841504da00c415602644190b040405070111400781d078894060751509002c4501249140070445000b1384200d404040c43c06500b4800104540ca0f00c3c001410030704200b0008104012060718050101c1d05203030440d010990000c0000e1121524140c004002d41f50407000301500c95803440e10414400c045d4145042c0d82c0e9007050361100303510308110301610071b56811f51560410a926113004440740d00b0112006000101d120b00104086075081d402029a00360301e030800071190f01c02000010300c80c1d1107540154100d50054081005003c410311400c000ba02044400380400a03030354507034610354041804040d150b0904680789404142c0116450300000b0b494003c25900c5115110300c5d80d14200c3d50703100c0c0381c0c0030598180000d130000b84030713100304220b0301c0f90303034035480e0800c281d000858000110310601a0284041040180026038801084081d40781c40783c00007590b43d50039868820714081403110301c01c400f003403802161a60103401c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 488500458 1250 488499208 488499217
    0x312140f07080903090d020409060603030309051c05120a0b0a08030c0d0309050a03050f04091401050906220b0f12071401140d091106120435030a1e0605040c14 70
    0x454511b0700f1050107000140060607103203001024546409000401c16425400c84ca1819000700f0a40e45507440300381c2035030001090540c1800010f14104050f00d113120300d447c0322942006040301c00041c030300c0400d03010421803101504003000c0350303001081c0b83e0400d0ba020080c640308055546418800d441940e540c29954010450000301800301c0071407020050641d4500b5074006001d840e0040c003107401001c0726001c2d214420700459000c0d4070f982e070005007a400d2403220b0740440303541940708000c01c2d0a0320404000404101001980c0710100c800306809030395640c2c0d1140b058005a0001d0002035181009030f40001c0040143c10341407110003a002c085585002d01a141f507001c94075400300300d40e440ea10705503042004096069a00900101d00c1200700e50590840c580b081c7c1c403598865102c1e8000300791801841400d8044c0301000282401782c007402001c0f503030145401052002c404950403010103266240031640c0982100803070765544040082d85010b00074502900e18905000010503603006115140d40725 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 488501708 1250 488500458 488500477
    0x903020606060711090a0f0b010f050d1a060c07050a060e030a1704030f120e1903020d1103030a081b0a08070809070b0f0a1205060f010c0312140f07080903 68
    0x1010480d0f4081c040c0c1c80407200c51130380000300103c2c40c03072401e0328101c002001c07511015038141e450030501c4041540035403c1041802515150a400c0101161481c405441803080005044480b00644075503a00c40301d000e4104c200100d00a080d119081105101660b140c6a101804200141d031040c42945c9002c41e04800c507c0e046808038612080043c0034848a20455000030b0800102c90049801e004090030042c0d01d00d5280d079102c3d840000341104100085850030004e00040301e480304108014504040400c400c04e114480ea50310480342640040d003560407100c64000400e10b001c0801940003004010700c01c2d086c20001c0d01c503091603070414006040450081c040c00c2030041c0c440104a01d00c0c802c00c01c51009180b0341009554554800c800c120640d0004003242020070300c000b110740d914940d5400f9940c0b18282c0548041143c4040a00444641c0c06c44c8200360244202c0d10741c2800c01e0180381c000d0980840c40d01d201d19085062811343c807200d0309001041101002030202c28413041a06c01301c101c820052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 488502958 1250 488501708 488501719
    0x2d04050f0d03022506020d0305100b09011403040f120f17090c0a03032a0f060b060409090302010b09070206060a0303051b190212030f07030c0f140105090708010903020606 75
    0x31003902c0d05a00d000c81c50394800041002020855090049124440040d00c81960a851a107150410305030300703a480c107540d40c807051001108240944c0381000003424881304c05251144403184161202000f9038426501a80c1c0c0750510101e6600b0b019907112001840d00061604d808010030500b0300600c11040070349155080b039213100118020840400071301c08005801420107160701d50742e240c0641608024494175000d102403031240b03103046101021000b01c41d03030072042d2030817000440d556180080ca0561400c2d5030000042c0004904100684502d5841c244641c00001e0703529094010002c2d410703001804001190300460400000b901d130040403204481c2e05090241e1904c000d034180c2400c960410644c000184101d180000e0b81da140c150070200c8960080d503405500300810b0405a4607881003640c02c401c004400c02c480d50000344101c00070004d4602516105c00d0400040e5140c4094050328500402c56070744501c00e10441480a1007080010540c03080208685500f41d0340103521000010070403842034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 488504208 1250 488502958 488502979
    0x9090a0615080615070201140901050412030c03021e030912100e16050a0e131509082101062109120503043e010909022d04050f 56
    0xa50203500110064810450340001080e078180009040d164100c40051040215180029035001c0a004440320b194060359002502c20300019950340f2075100c10305030340c1000410840001c1400601203032518151282ea0b40d04070304406410000e01c1c0000d0003180304400000e0010300c00e002c1800208962480c4401d84091110000c158090303800c0c030081c0e00402c000c650404690317805404000ca9a104450921207101c916140c940042c000c44000d5030040c20b9820180c9004242c1c041900001011014803c2c600300d00540050000070051780c0c0c881004680484010070440300c0d40404102841c03c0c8030016440c402a0f41c0341c094005d00c1071080303c03000b80d5104406003684944a40c187c000d2403556410031440741260300503003001002a0300072102034644040c90001d01850795610204505020090700340c5401d1040c0441c41c001d0300a00c000421411f020040000203599003072400030f055800b00c10340044190403c810300f0040200710048101004002c10041800140daa800641c422002e0640d04071440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 488505458 1250 488504208 488504221
    0x5070605040f1b050a09021317070f060f08130c0603090f0606120311032a0307050f060108100902030601030602031008010509011a040e1f0b0a0308190804080909 71
    0x208a0440c0b40a001d48150801124910700f9500307400003264400c0d103400d507051351348880e240102d009401c3c124002c0d0101490801071180342924108401e02058240c0380c1180c1d50301c40d0803032080c1c80d90784014007046040425015040d04040d1541d03000e5200310039407005400b641c0c1c1e01400802540124030a02d039440f048013051216038100d03007207040e078070100c10800c02e0348034000d0400d03850146904800291041c844000c01f07e9002c015240d503020000520401480c4000107800c511454481c7c16115100070b00a20021800802100c001d03d030030040507103000e5040c242e060b41070115006603500c076030b800c0001c40401a1000140c042c1120341000340107889403220820380c5411680c1342d110b80965800c0c42c05100442c00c041d805040324041005941d5070b1540408284030550300780c220340d00001d801c14042c0d2040c00c0003050002079401040500064400100c03c0014000c4400360015a04442d02180030310b9206031190902c060708240c2d0529601600d041c2e56030000610a95619070300894040000c69803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 488506708 1250 488505458 488505473
    0x16242001110f03090705220b06120a0603020a05060406050f0a020c090f1e070f030515150903010507020c151305060403060e0d0905130207020d0210020d1701060507060504 75
    0x1114806112402da40c0c92810000842d02e07041039401000d98028968006544d00d04400102110200e001e045548021410000d8000b4203401840682203c0b0822404c4a4140b42e200c0141c455548604006100c0381180140b01100d50301d500114000c2c0c500304000e04c8010307008026217010002c41082c5070307600c1030884012030030300e0890892f05030400c001105220720981245102481070700440c601c1d40c1d100021210a00340d82c0c50a80b815000328000004150125100382c0045622a15941c1000c1030304010b0b80c0170810004240400128140303001c1403081041c0303000e014007500803e01e84010503816640b4000601401501c0742d1801c0d001500082d10090f854401031900014a001003100d0b0b201c03035403801c03c2c0007d00101501c904990190100901a603030141e69824191130001c1d09000400340c0f15104080254041d504c2681c0c03205560f88175800695581100006501c0c49502900c0c050401e00c07005030020302c1c4881840883c0040200521000d5803200a80e40041c0d0440d07004203458849040202 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 488507958 1250 488506708 488506721
    0x170903070f050609010c02160509100f060c03031d1207141009060e0106150c060f0c0c1a040210030c034212080901020f16242001 57
    0x80962412140c1e140c2032200100f1140d1080368213000a200d809280743c401c0307845410025140c002003244002c140a1402e010b0900c0380e01c0300d20a43d20501c0780d030311807600083d000c0d0305911090001c3c19074100c400c100b40c3e050080307100c107065040c005500b90040d400c440d0b48401e0100d024400d5440045601400e011200505040359099402550000d80c501310880d40500144001070340d4030360809001211200301403144004070b800b40690348201303504c026421500c142035241d058604e01c1e00d408a0384100c4100340301c3c00c40000744030b84844600102c546816032030100d055246061550701c0354108400340e19a480c9552a02180345800181c0d42c1c480c03881500140507105051b03510181c00701182d1000d0720054512104400341d000080081e540721040c0031b200c0011805050b15101d948640b400c0094075810140090500500681c3d403844109010b241c46c11840701120400701c90b40740c0c41007100c076442e40d4901584013074003004400380200c100000f030415212802c642400d0a4640c0c4080c07480c503002c0d800f40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 488509208 1250 488507958 488507963
    0x10c0e010c02091b12041a01081516140409060302120706080109050403260106020f0316080d06180203040209070905010c02010e010318031d0109081c021204030b0a061517090307 78
    0x500c451b040a003041f90b80441521803101e46000d00000100d101d0f20005060b5080540340320940e58142d4422080c0d000000010719003a0500003907400c2c0c1280e030494400680041e000a150005d00d261443c010403a031090030064000341074012404c240851548a9403283c19070b05402d10224a40d00c03545800c0302c0b40c131505d82204490b01c0c1290401d003800282481c480b0304881c003940c22140310041410300c031a12807290326498031304031000d1860a4002100c48005d00340402c81d08000140442c2e4803da1440c07141540214006032030f034000100011490001041c580015491070180042424113001a110300090030010b4103101d41340140d26901da100381c00040050141c100c401418031424980a4807444d1000074010858041640c40c4d02154450454802103403440300003060504620b4000380b070b8001015010300c2c00c6004030070303480d0b99640024004000031449004540410300d840011070048404540184820303c508a4424841e80e030f00550615580310750481e070860940b00c0c003910034514441c02000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 488510458 1250 488509208 488509237
    0x30c08120703380d05030409050c030703060608150405040204110c0a020a0e0601020d0c0602091f0813080418020c12030601080108030a050406030b0102100905010c0e010c02091b 78
    0x100500d40368503402250b00c0002016148000f1102d40150f0b88000a40c0740d14458142d142100c9a086440c04440c044d0302980140140d0345850f460f05000b2040c0c3d10b0032103014411403000018080ba140e850301c0b6103001060a4500201036041000741125015910704001d441151a14003150a550f182e0388900810350000305082c0e603402c0b403141995100c14082a051f403003121206c0c070000d050781450810f5032042c181640070b044603204c03c02064807040da440d1f40c15504280c3c03c0c4655400d035226001c00d43c00255183c405845034041b19003006003c0040101946180d030340c001c00ba00005142d80c0d06a500b6105140292049170804400780e0000307000300140440180b0512021450b8000c40b003005500445003a43c541e20705a80b06c0408075500e1203444010030010748200702c1004094440d500c1060a090144103440705452206c01440c103490340004162416507540c001c0d002400c4d0000d008036011102800c0020168189400103112864002d01040d42c00340d002448054000584085460001070a0310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 488511708 1250 488510458 488510461
    0x6090706081e0406150b09030d03020a0225090c050c12160203060a0e1e1207230d030b0409080d090c0f080c10030504050c100e0604030602120a0b010903030c0812 71
    0x8003040079140085d41c450000303046010102d222005141201c2c0842c0c8064020400c00c948000b0440007503100103500c0c021402215040c01d010b41400c3c9054081d260841e00300034002d8100b4540c801214030b43d14035034003406010041102029400302e48554450303245c2040e1612114180302002e01d5004100b0008c2d458050f8004102c1e400002c0da201001c1140309004851000110107410b200c61030280100401c45e07131042d6203032068135940100610030340b4410040000030704040105200e110280040c2c400c03090b08056011000c0545c148142c0a0404044400b40112450b98807111018071450b06070010103a115141d007428442400b032204002c0c040c23000d5080403141d5800f6110317121380004417624441c980f6400441000d921a0180b0b50240e42c1101c058800707143c000c0b00b00610084650b00440a0000c41d1541710810345d1407001400c0250300403a0b000d40d0f11003941166003006a401000c0c072555502d402d8900d80540d034410785601c1a0b03a0325040030811551103003042c5019015200030b032201c1c44002d20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 488512958 1250 488511708 488511713
    0x806041d031b0a1703150d051b04150320060a110c0307180507020a06051515030c12100f0b0405030c010905030c040b0d0c0e0402090906090706081e04 66
    0xb000341100400195081091601c40c054584407074103405004c0a10076807400b004501c10350005e540001011100041000700c220100702008104141600e4642044c0c1815400c2052403000c11048542100c04000d6019100504586c07841c0320b0002405002c104140ca070704d5aa0380100507180d8100040969071075111102c0010010160410b02c49403a00a511140045090000c3e00005403030216214000421840815070000c1200401a404500c0f40104002c046442481120300582c0c060400e407400b40c000d5002d020040080d050b46c0c65003054200104000322a5003020b5031051010308115644176100c40078000030880e010b4104460f403190002000030503210610080c07040381c0f0f00b038080d52400b9580d000103455204a6200d01605074110f4501454549840c0c1e00421184800900c0d5a103085425140c00040301081d81004022000349802d00c015890310740501a40081e000e4002c016a1411f030620340e0b1140154401d1000b40942407010441d842c8502000250201034034003201400d20f820b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 488514208 1250 488512958 488512963
    0x1002090a08070308071203020a080a1a090f0915011d040f08130f060e030705060a17010b1209031306030504020a03050a0c0f050d080913020c0304061101050c09030c010806041d 77
    0x2568101c0b01440c0300e03009462264001d00a4842404490700c422b05140c0d00e160f4424042d00c10303008100c4001c4d9515800118580d01d0468140c091021200500224035010411510308400b0b2680032000042500040000f402c2200403040c0d1004a40b641120a840c0c5e860062060b40520340010308100c07001c0f407222202031255180740100e4100b00f030092040c036a600c2054503c4180320005a0301508000d0b010300003401c0c09002000700c15640c0c54000710a04040d80005004102030b004030f08140c074009640c040003002003d28030f410202c0000a98a4510815108200c00003030b8440c10081c991910006802c4d961f404040c4402181c101e000c0e120724010a2600c0003e0078460301034154003050b14180802d450900302d50112400d94454101854116100200001604415011070410781c0811003002d444400780080c1004217507035284c144c0f1009220901609481c0001e0645041c10000c2c80070000950300050070500128081c28421381503100ca030040341c09007000411020304040b0342440c441d02c00781d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 488515458 1250 488514208 488514217
    0x8070905160f0507030f020c10030905070e0708040b07050f1c14060105120604090c180606030506092703041202011b082502150301090506030705031002090a08070308 73
    0x42800e60038485901c801560080c00607218000080c206001800001c1e0080300020f601460600440344800000350000315001034130b451800000341c0307548241040100030850080076041c0c07031603400c441307240070300000b049108010b00c0a0000201000070030080c030301031800c0310b0403110748420b01941c520400114200b0344010240d520790710792400300003411100e942c46285004002c141c0d0354501d0682c04028085000d0005000f02c0e900698411008001442c50560140100101e80c5182005403000d082c0108849483d44a4020b00d0b0501080002560700c03c2e01441c2c2c031680450743d400010b1404010b12910101641c0300d401c89100020b0042403039840750565418152007642e03040307030076240c0206400200410a0004007412018401c813414100090700254440b00e40d203154007034181c900d0f00001d207103403c00d0074400e1743d160001005215142960040607032081c4182d0050101510303000c0801d41d81d40d8000c07001c155155010522182c3c40d0f451a00000091150100b01c4090540368100182940d02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 488516708 1250 488515458 488515471
    0x20603040305070203060f0603100914060f0f07090303020c061804051524070210021006091a0103090302070b1c0f1a09040f0206031b1306090b0f030103110a08070905 73
    0x1090005902c0c09240c8005920230f00e00600034121041c4000c0c14880030700720f103a400f15400400305035018001c0408002c0036101e804036a0201a19080030014110100800703841101000b2001c803061020940010301881c29800c180d460507612101d00145641c54180c102240e40e00600307040500000005c151480105104201c03450b40031000c46d030709506410315501000c1700100382c00748181c00142c0b400d181d9026950380c031030055030380b1419481d030654100c4105400424046548602c03105174803080c0c841c1c89550340f4003070030100310034407607500c02070b60b2400715204e100e200380c0e400a8114484038511610030b00c295040c04041c040c0450044611003c2c0182070428400840c460120703e945180c00d140c12400350750840304150a403c2c0c1030702440f4850384014299154041820014608000303100c008208003c1a40e1480191605003c802400c000469004208104043c003083c00b400a0207001c0b641125400052240451003c00106044c0030582c1e204010a00490100090007801070700240c2c0f103002c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 488517958 1250 488516708 488516713
    0xf0a03020d02030703080604020d06030b040501050a06051818030c01060608040b0703020f07031b02061801200705010c05010b15041e0b03150f03190b01080c0f060a030207020603040305070203 84
    0x10654074040303030781e07006050018001607540d02c0881c0440c02c2c07e0307004290312090b0148c0800e505499444a180051054904a8032695601e04001106940380314603009814211900c10f06010345c40082004200090080c0c5201442020b403007203802410801c442c01c400d00c1600034851103565800185c495a000c84003994440701c40d070009178655210344201d40000409616050400030592000c58150100904030028103c54090402c090303960800601030511103804a03808059400c0001003507507105541080b82808001c04140340d441011400784184c420070b191062403100f90f410410701503c0203141c00343d002402071070000c26942c0c20700014000d85407806101c0340c80c2c81000e035040c1d0404a882c460701d4040a0240085a00c21501c0643d610880750010140028211f19600280c101020300c402c1303500701080c0107659020400d1800c90140100803400180001c00d07243c0c00403c4041c4599498944900703c000b41440146010303030b054030b192035009070091b51a403a0514018060354055071080c1d1003031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 488519208 1250 488517958 488517973
    0xb090f07081510090612090f03050a02120f0408101a120703060603061b05040303020c040f020910030204080d18030b1b030c130e06241e03071b0506011806080f0a0302 73
    0xe501b601034028500c0c0c0c0010f0701c3c5402261030711b01f01c5058024005c42011030040c90030380021101504050280841c0b0101c909564500d002000391a00564502c01074016007400882c031440d03032684403640380300002940c1c00300794144101c07281070522600ba080200003900d4510301000f44180c035404040f50740a0080b120740c1c4000d170100150b480f03015070320000300164030584000307681d03040c41e0b0880c9640341d10120f00581040200310024011050813242d00c000250301240400050b0000c000380100c1d9000c90800030561072550211000e01003039404042d280f80c00141c046010741c042c0c225446c61245101401d651242131a120440140e4040b07200f084184140312808125580f02c88101409010000c100c0700a11306d03905413603555000414004503183d0000d00083e0400041040209469104005034950368a40a2000382c0101c04140d141c8070702800c6642c0c140001000000d9080c1564010b1540704d514407031108401014083c90380115030f0354010702c00e000d19809400541c500e00d4901c01d07001d40b00342 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 488520458 1250 488519208 488519237
    0x705190309050d080a39060b1c08070819090311060307200115060c1a04030c030e060904140f0903031b090a0306110d0b090f070815100906 61
    0x4007410340c3c00c09001020204802c46103c4d0007041e0600e25010709110390407088008500d1442081c0c0c181c41c14081e4650441259002c20045125405907600700700d40c0001c05041102510280d202c1001c001886081d0009030311301448982c1043d10419402e07100d9a0307014540000009041104ca480101da1f0303c903202c0c01c40c035110300e00203040c3c9100384200d544682040c402d4490640100c11410a00310480d580c899040340070740d5106416101910395500d802007088601d02e03010100c00101c80700402c402c25401d0901000a41c402036140c00e1503011320b000520b40d614800043d011313101d500c000c190701c02d2038624150042c48085458521400489801d0310080da0f80b405104d0300c070b1004942c542d00c040040d04c4050018812a800380100020140c010740c03960391240e503288101c42040b004800094400308000182c4501400364030004201550f0100d054100340c43d0401080d400601504148185400094000c504210884a0910b001081c08803040510840501045c81c02d000d00710020780d1982c0d01c9501e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 488521708 1250 488520458 488520469
    0xd060f03060b0103091a040f12020312090a1a0a0b060d1e0b1011030d050c07140a05190807170307110601050307030602070c1a0a03050a1806050705070519030905 71
    0x8898100d0007071b84d640700084451000d80c00d0010801c84000f0070b803810b484003160220000100046907030300210b035151a4080380382c00c9141c2c0204030071038036070040b881c0c4400034001441011800601c60702150182d10b6045007540902030200c4c040760001c5021491001c40c20640e003105000741400501c03260380401c003c61203002e0310405000c542c0c002241d00e49403290302d44211300d140c0e0388204285c00e680c1401445a02482540c0041c2c88401c5848008603e050501c419411070001c542400001401c03d014580d0322a91a480002d03020052101c4070071000090200c114100c800b403035071003000003103100d000e803c04a115810540d00780340026140944086d4004c030000382c55069400090042035118a0f50741d90b08040e500443e400c50305920000c0000801d01c0b094002180c810111000c00350700d42c08591001000c9030801090300920f0b41c1000803444640740900c6c144a40241c000401080070340c0c401c01e0070b5821340304c0d144004100d4410f4041076032210b451031351400c9203503200b50348880c151a510400c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 488522958 1250 488521708 488521721
    0x103090b04170d020c0c09181b010311070605010f0f0f090c02030c150618060619110703060501091406031f0b3708070b07080d060f03060b0103 63
    0x8080003180404500030500c1d848001462035003000029180080403004202a03070007001c507840d229481040c11001616010008a030300c5400d081000940c0241103040f00e41e0307106059100d05a04000d9480c40200fa407180c1c10000c4454010149965240d074a46047d2004040c248500101c2005030300010400011050196085404030b407610300000e42020b64210050203001c20040c15480208907040c032209003032103005a40032440380c1d406200d1031b20009000c0086101c9030400380e42c2e00c8a600700030456480780305807072010820803501d0681c00300e1494146c454140300c8401c464a846035900000c20402c0d150003250503a00d06c560144040c949580d50250f5030303042511401e40c9500f0140d400041109003070b4042c900110403007004203030171f404003000c01c1110861607213803540c0025070003a00003804001a500342401400030780c8a4045450413010a44a4510b4000d0356003200c0002160010320222005442c46400640c0040009690321407003001500143d100840310ba80c248041c10301030f58028410306 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 488524208 1250 488522958 488522963
    0x90c03010609020f0f0d230412020102190503090a060501140102010b0a060c0f08090d030507050f2b11070609030510050f060418050d020f01060b130e31020f010309 72
    0x490403c1c00b1200030121941000c0d200e480d102d640c038982103181c80a8a40420a0503008660b507c0c1d240c00c1c0b13801c002c824a4000c0400c241568010400118207090096071000b01d04024503120352251a890099410b20701d40300809014a030420002140700c01454505e1a0303822026002000782418090602488074854841c140100b41e81480c440c011441c254060001c80d4440d060301880c00e42010001240d004014806400040b00440c5850070004204040320701849000002c000304120404420520100814071020380d204810807404114003900d1009261500c42c42075805031030301c400004001c0081840142c1d6688211300301180e5010040c4901d500070215540b01416541d96101400042c00520703c5902e80c60461012482c08264280024000002903a006d4141460882610360a440c095000413119010810891204c04414002d41d030882e00d02c000c0c0883e441e6688040b6a26545a241d182c01d40c4500c030980e6090211001312403090348034070890f8240d88031480000110120355607103100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 488525458 1250 488524208 488524237
    0x709090b010b090a090f020403140a110112020c07140307151e050d05100e060a0b071214041508151c050705130621021e010e0405090c0301060902 64
    0x10702c98484103100030000180090161030200d580c401d0240229003200200401041d8040b506004000c000019422640308403002045010300580b25801c0c400c0c150314135907040c8507104441c50b4542c41c4640541e14041c070301200f65034500d9030303e8800d268004030b9880024468050244041211440c2402491604285a80300d0b041814400d04c0355451480038203402083c004c0a20440317104006038003885200b14218031017409410704c0d2000410400b040036000d6072203500c2e190010302454a10800340da00c1d007500f00390210b00038206840b09817154103e003810080880380000780412040c15500d5000d580000351394a21a10303588070501040c0c3c0c00e00c001c02c959031161201580489800040c0d8200a41d1030003482a520301c2591032000900c040c00040345a0740640c0c550a04010341d6142e06004d84080c00c04a08070030f041c214607400100e080c081940d20341c04004201c0601c407020391003041c1c4e00c0e950400103401008213040c4110341e940e40d001c281c04c2c240d10940c01d181010810f10201d009450304202c01da82c1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 488526708 1250 488525458 488525461
    0x91d06010f030b28090201110c0105181f0206040c050a06080105011112030117070e0402010503191b03062402030a14070501111c02040e22060504140709090b 69
    0x703d284000d8400340c448a000c4882140a5080b060000c0b0411030f81e0460440002d8a00c28910014107a4490502004050b0b000324070a2012030340c0220032124440a0602081d52040c4110b0001e4040c070000003203185a01c000d901181201500051b20500450081d8540241d00c0d82d40e1003045454106402880000313801000100510350041c1e881000010040c2c0507503401004400c1c42d00f505070400d81c0448000d19245501016450040c840400605100c100f01c2945180a0300084c11500c0f01400d041d01c910076510f4070450420060b07020a4a0400741c940400300e4559052004020300414064008282c2d110200a103d4801034072032078614441d260061400d04070392142c2525884803000c0f000c1c0380201c0410005c40083c00a10801002c103000e803e0980e02e03403221020b43e4400c2c20b0408036581e89540704010512407207000750007156101e030501c0c00b0030500c41e00c09150500c909601c03490040c105401c1c02c2c01e20003003000d14902110310710041000c03900341a40d00c0820006540480d400640490310000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 488527958 1250 488526708 488526713
    0x3021e031c05070b0403021f0212041209030b0f0f1518180322050a061205062206050f0d03171e0c0a092309040318091d06010f03 57
    0x380780d496041102c0c1421414650503031034105400b901100c0c11401600141034805811068015018640059002c02c41c2055003012081d81c030350902a2014200090351819075405034403e00b81d10001d541d1200c801003050400600d0354141403010b071180310581d200c420001e5072a81d5412440c2403803a10080c2110416410105e0008181d14050003040144040360b021014188080009001100c0c1070f0380c01110701203021408001501d030541049201d8000318804001140e401000070304a85a110000107013600ca80000888148030398010311024044c140142c80f120300d90707900000459405440c0c10030100342c0d041c204100050008001004104903100004e0754007940391002d644000404060340303d01074881030b4006d810104980b4480707a0540041c0604100360304c49c800c080100740410004400d201d00c1506800600c40e007000b06405101541e000500303040c4921402c950600d04040344034015600d03006840c003c1c00c88000288030046010032449071a800003d1154101ea1309a0b901e191801e046a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 488529208 1250 488527958 488527993
    0xa0608070e0f040608011a0901050307050112054605010501050d0e010902090f01080d2d03200a03153b0109050906060907051605030409090c03021e03 66
    0x1002c0c03030b4101d03954001c0410850024400c20700c014051840c0040741c40220410402c642c50140c01c000e0280d0004041000302c0d9803c6115848824200712010850b80e41e02c001c3d4440c0659444e60800854290080500d82c20744c0c1c04103481c0c8900445000b21882010b24071120041c1c03442072003254000707401000602c0c1c1507480b90b8010905009490008503d680f1580c0002c2c0314007e06440318141c5611820040021500c2000400d40303d03403003401c000001c68104450040000c420082c20000e8040e400e01800065120354031411109110552040440000700d480704015044009150082441c01c201c2010484450701444101c030f1404c01540c100d46411401c41c2041e0b02000090003042c0c4840c401c2508a040c4c159149010b000c3c1c10900184924000c0c1c541c42c40d0000182c0401d024004d035000780010320f13502c44101c40781c040701e1240800181c803561030000d145124640c00211440d00d0108030400700701400d6010401c590088030211101608100842000e404040c40c0c964182c3c0011012010030252 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 488530458 1250 488529208 488529229
    0x50c0a110c030102130503070f350a050303010602190f03030b0a09020c0d08131208100902070c050f01091d1e091c0320090d120207050a0608070e 64
    0x104151441d4416560209081e608a245034904000c0c0c5840d003840941010460100200078003070401115a00c0c0c03821081003228034a101c07074500600820340300e68850034810000d0500c03440004450406605040084d140d4101380507820060140098800030040070012054803180c00c4140000780100a6805500400c01d0790b819641082021320000390000c000d1026050804801000d0070b030044c2880c000601e0300304002c040139035070780c114002c0c0b5010550304488900300d44114104030107140c8071481c200407211050740c07083d04103500000704601045460211003046480544544110102100065544123140d004121a201c018042c01e200c404224060703d8001d01c01310700c20b0510440c428078100310b4a400301d601c030305136921070080c52000314070701c02d0032040001c4185003c009000a441818038484891b0400b0044072002042c1d580465894520079080700c4d40c0a0070013091307485c460b1030203521100079118440c0b0640101800050160044030854840c40301903544140d200e0b4480b0802804c00300 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 488531708 1250 488530458 488530487
    0x9060d060b09041208060109140f0418030c060605060c1203131401200f0702060d111201080624101e0509190501080105060f0c070e0712050c0a 63
    0x40350840c00440361034482929004074084c946012000d808541d01400f5444013800450400421040c100641da030034000e2030050020413114a80b04070301c2c0b400050050f1900c94010300c8001500304a401c201a00110023100042c807c400901002c0c6d600d404001150196071076400030ba030040c4001c007000d40c548000440d80800405040b40800e0a15200c440610300a16140c0003182c1d0346641000c42c4003040b4001d50b03900740b1017540d403901d0075203020f03110000360042500090040501080329484500a9003021040481041d041915101141c900e0103020200f032050700c0003400341001051503909402201805907420391614070200c0c800030180041543c680b140c031810414840000c90944600d070002c10041d01e040d580365911030b0b50141c03c0080754401c0001d04032a03480740442c1006541d8000454604461080b00d4494441c40003213580c82d0750b840b0340c1440d0440d07130051500100300900b482c4296030044000f5540c01c090200414030001c100c810940d044901c82000f0b022012503940300d02c80801e80c402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 488532958 1250 488531708 488531711
    0x15010e180a050a06020d0510080319020a0206030a020a1d06042d0f1503090b0a021312080a030b011d19030b10051021110403051009050c030c09060d06 66
    0x100d07291503103801d000865104907907040c1c0010300c0c40300c42d034002c0c081d20350080740d07a064040601b840d083c840e907584c1c0710306010f1120b40e040d0091810001d5000b070110395000368000e0041342d40ca00c0c1804c040710080d8852038044022a1b400301a801784c03011404541c13000b4000c00380040340752908000ca118401c02c54850740c0c5c050740c414803240c800c0140350303486448024a50003809480329400c12400c80c0740a18210494800c040c90f110303616000c103c0c0e1541103500011000401680e50182e00607841407144145c000c003442c00c079034841640c104580c1c41c006005825103543c0420444d040c00004441030058211155a400584001c40c10141303054411308001c0320b00c0c5501050040d0b07072503447e05400001128920703115110a40100b007682811803440c0c0010200c0d103091400e4103000401a140c001060ba10000b401c1e6407000042003400c00b4030111000f55420038211340001043d6480301c000780c020040120b8450090500350b15040c10006090341c99000b00402c0000a60f60b001c00b4070a11241d00d44007683c0c4036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 488534208 1250 488532958 488532973
    0x70b070308010b07110414040b0603030708070b0c0702030a05030a0305010e040b0708150a120209060d12051303020406030f0201090801021306030b0604090c0f110606090a020c1203010902040815010e18 88
    0x42c2d5a501c2030407d0614001d101028502c1c060428907a544002003500d4004d400821003400001c40d104100c8500d035912940e9078041da1500112892140180d240c004d42502c1002c030002c0a201340000900403c10990b41c0911090780c9441080400c1e10095800416994001010442450084c1c02403580402c000c0c02c982c6c4080140c00006210b161154060001c40a140d141c82e01941001d5803019403049054860f510890850b595403400c00185c00826020400042401068980b40c80781c030350010350b0020420b2010b1f80e1642040182000c0c0385030102d001c2091080c000410721018000d562951240710319548000f03142138416030107842c000c9030a48d48000208004a6400414441c0301c403a1900d40e59580039049421402030a000c80080d10003a19034072540801c03030a41e4032001c80d2940712141d03500168a50700101100c41c0381c280d002c80300e514002d801000116440ca03803a4040d00441e480b8208031250300c102c0e90303a2260000c0d028045e60b15070204000004c0c2c03541701e044010040b000150422285003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 488535458 1250 488534208 488534243
    0x403021f0e130603050c040b0105030601081911040801051008030409020f0408010204030305071a130816051e150f0708040807052a030d020703030807110303090f070b070308010b07 79
    0x11201108440c1e03a94802013401800b00030001c5d000c07400d009680c200040745080b800070340303d80002840f950410418000258500c400301d01d1035003540d02c07403180500ca04031800c481e23410380d90894010f441081d0310f4040060065000728a40d4022110782501852410b4281608500039500080d0a40402c0e80c0c20440000d504134248014401076001f592102d85a20341817400c1c0f0311010950781d4849000c8510400d204418610028100120351b0040d00c2d20364801e034001346030352040c3c0002c40160440c01481100c40414102401c1d07020042030480075a42c3c2d070781810a082c00801c03801e9903228203018403400001d50850007581266046802144418145111543d603d8030b444040300c20300c00b03446108501130300f4201001135401001d2404401900b0f811709101350080d902c1d04e140c4400303400c00654078081090f09000715000000c14140c102070b44c3e0b0701d01d400361301c4584c2c0c1c61007a11130112a1180f400006038010403c400d803400710b585070b81c903081d4a920305801891301340c021580c140c8070505006c0420f42c0c13 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 488536708 1250 488535458 488535469
    0x7050a06050108070e0115030c030f0507030e100e0c0f01031d0c01030623092505030402150901020304060f121406031501060f031d030309100b01050403021f0e 70
    0x46500c2284081095810500c59a090080720760141c03411151000c0180041c87c0c42c1101528005654039000a40503000501100a050202428a4010f28002c180300030785915412949079002e1b66400c9070201400c4a13031803402c03907001d03000c101200c2e00040308000300c92603c0c40010303903d50700500d00402c0b00c56100340740e9880c50392007810001042d40311b000228003a5805003d948002c0ca02c034070b41030344e07484440c60342c0030a00c4500301c1c8070502c15204200060f01e1144c060001c2c15481c2e0404800e000d150618520250661b070003035400f0381c452070014031040740c0306142d00101c4000060680c003035400c251400310251143d440c1c01d407200003071094404400180b85100c1c4a580620110b1042c00780c41403e00c07100381400d00c50720418406041500a005000300c5801c542420a000102e150002d00e661884d00d5408540307109846c8185036000020500c084180002080d541d10340f1030100070031598065000541d000c5c0309501c4000d4000e128600329090700c84180d291400f07081d610341001e00e515400240000ca = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 488537958 1250 488536708 488536723
    0x30106020d02061303080103020d020114190806190501050a09081005041208040b220b0a050910060e040602031e0a021803030403200d14030a1b03140f0705 68
    0x40140d00107040031804940c100801604220130202c0d80c4621035850302c1c0180500c00500020303010300c0101da624021648900c522030002e102486820747c450016042044001c0c2c4403290300000188030002280361803400d00c2d994080c900e40d68084111651400c070040d9078076000409114180103102e1000210242c00303020005102d10401c000044915003407030011682209030303190104212290003004009010040c61642100e5405d4003c800248400300c040d440d402000c00040c0211a1a4240002c0b03a0a541195024144070000d88805085020303904089484520500300e9038040c480124012816a90040d030700080c000e007030b401103a180b0351403a03440700030141e407001d03540e3307500254450319110525426038900b14101c1c0074603c0d0a241d621860400904021010a0081c2002c2500388079556210840000e960041101034110b001c20700e41038580d0016a0020007080b846d62480d454004541e1003524074591603140e10705800a03182500c40d480c3c028020500003010200421000300d4020040301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 488539208 1250 488537958 488537969
    0x3031302030f0114040308010b1206061605071203030b060a1209030c02030d0e0103051023030a05071202040f060e0a0914030409050136150b071203140c0d1d01020301 73
    0x45901d41040c6c50020301da044141d004825501c400c0c0b00c500284140d540e142c60700258112051078482a4690001c0c020800d040001442031040d1038002944100003020900d0140c020340341003080145501c14010075204200c620800030b0b000895219003104070b03500040c46280a0f2420705080a0b66901103880c10380e03000340b0700740420034401c5500240d603030500607583e000800c80d80300042945800307409015410504030755170300c402d0700c102d182103030740c03000c10aa0701c14a4105080f50742140d698800c2a944640002c400c1e402242030900d036194042c0c175805600c0480d4000100071585581d002d1401c001801c2d80142103071590304100c912070342288104041c02c00707002100c200040c0341d4901098208500910583e81000c2948110411880400180d60900d810f58402010072104101003030f00d442e02c492a001518541008140c25090042184504800d08595241003040300e001e5051035000c1e0504988070005681c0400401c0540400c0e03421009280c000c00601c242c49440105065080ea01300341c004 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 488540458 1250 488539208 488539241
    0x213020a092c090d020a020126310b01060c05010e030f13080703030e010503070201060503060a0c1b0c14012105040302210f1c0614030d05090303031302030f01 70
    0xe5031901050700d40503030740140940c8010104e0a03404000039407948444500641030003408603000320001f180a0b00070104184c1c00b12080401d18000c1f00341d001c00c000029190421002c98003484219103c108015034045800210100c5c0030f031700c1d21313604a407003502c1e4440032145d5540360400300081034002c10141192040341e44289849020b026404685802c0c0b80c0c1c0300b800b042c0c0c0700740c00410100343c0010520401e00e60a180080e83c0355200d0300280d0147c0607039840160135101b0f90f410014107004a5104500c0c070b044036518030f03203101320440b6200125120304202400720a4004800c000094013854002c01c125018106180e201e20300e00340c401409000c078401c107524151039004020415505100c4025010840ea042030091403034040c0c00d1a5501917003000340302040c0001340c0e91104c04042c000c6000d98241f0b5030230901245071904075940c00e001e180d00d22039010384036020080390024041c409403180114013038021410340e50b82810010090780d03500000c1e6094010030001412091003030156030240608a1130 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 488541708 1250 488540458 488540519
    0x61201090f0f02040b04090e0f0601181b090501052b0510050603010e1515072a2417040c060806040c0509092205060a0e0a0213020a09 59
    0x140d0701c1c1611070592216064502c104001d22204203000705540640302c11110010f0151000f1102d0f510b4020054101d100501c90b074000020744031540071081268000300e03201440b07089588090249031544601510b0003080c05040c081c00654484ca014051086c071210030000b0038401d4007042980100c0d8209400140c4c1d44660410941d01e4401c10020000d0905543c0c2d589550315017841e082149501801d5951000c5165642d40b80035030b14449406401c03807402d890079a0fa00000e1030459542c81d841c1c00c116442048060a002240090038250b4084813502d1025404001150011090340d000c003945810a102c00e8072030f0755044440c030798060b85c030951141c00440c600e04d0510b00d01509850005006901c0b9909112003110000c1d40401950402c0c0000c5e211a0300c3e0341c44540310340c100070758481094040d000c02030000d84c050080010f00c02e409541032400070080108644201038403490329103001394110494030700c0003048011580c0100303104610361401101c0c050b11901c107501850070031242102600003054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 488542958 1250 488541708 488541731
    0x120608030c07050d0b0a020702030102041a0306090702010c0903060f060e0106050711030303061819110a090b03010e01061101060b0406050a031d100207060b030a060516020105071d06120109 83
    0x500000e00000c542c0c0401c01102c59035005d400071001000008000d07008140201107441c250140c4005c2c001c0e0089101e80018603811030130150b0012613034580b00766140750200c0c00450040c40f500071640c28a5664600460564440d90301400c600441450700319681c031000509a03100358080c40c0079115a5071a2540e13407199082040c0400c51304144076110b07070810000d0006903510107220810038020340348650900d5031007500c91f100300040d4640744484c190070210803010750781c000c0f8020300300341c00151247c4070701e551558001d84c1c1d940001d0088122020300000107010603406088008000c15140d00003040300368544051040a800c10780c89040800c2d804243ca2900e10b4145c05924010407031240240b07541c2400c03210095039114281580b804441d0b000034080f00b840700d9904075135807410b00a170480b460380c4410b21f0504c00514048070f41d2100c461743c00c1e0300f1884841c410b0190500030784280d603610600050302e41038080d4030030031207114680c440c4e03041280d03d41c0340000302081c1d400ad000405002612880c0320 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 488544208 1250 488542958 488542963
    0x30a080106030c0504053313170c010e15072009070c1502160b09060106020303070207140a080d0305060102010c030b03060c0a17040503090f0405160807120608030c 72
    0x41e000181418241074051000590040556046900807600541107200840801911000d420040703130346d00f0300b45501c40d103410ba460782c02040050409440e20f43c070103648841c44001b625540a5a21a03908181080b055a6204420b03c000400c4010726155600011007404078940d4007424088400d40c05468441540300c04030010301c64036070b1060b2085011440c1c14030004004d4202c8246c0108a540341400000b54000c40d6816181c429001031058010b040340c0d410030310040502129594030611841d0700115145102000b9a406401141c000300122400c0c9035584089001d60a803082d041510900009813006040209072810203075511b000405042800009003541e10340000031041c182084400d00c40c980300001c90075403100c0701c2c00da41522090100022101011084020007001503d2010f201c240b050110082404110480d00c091026030b026042c8820f866045500003210501d40c2e070200310041c080c8200c6a4040c04a107803080224608490202c101c1d6101d400c01d40b55540041010231480808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 488545458 1250 488544208 488544211
    0x13051503060112060506010f0503180f010221010f23030c0409030e0301140105011d0d06090b010612050402100809010b0613030b0c040b04120503120717060409021309080409060602030a08 82
    0x2860210320044a00c28040d28520003d08500356641042402f200303403036401e1028024481c1000001d654441000405020107000c07866101807441041c800000c43c0d60010b078001040355036030b0f44496078110302c1c0c43c107160405030900c44154150117900c90000c40f640d41c510480070303041e06c02d88841c043d4070060f074113040c00c680300007041000c0000a6001807000d6a04001a18141d11000703281c0c0e0289000c01d400f05a00341e511150092031b01c1c0c24551041f080003200400b0505a82c4595103074501d401c52520f000090301c2d0241e401039004008880c04c00700191085418a62042844002003110902e2001140302e607400307440c00321001c9400000c00d000300308014040c0c0d5000450000918101424100700e803042d03200d544103080c5406640d49818082000c20310a460344100c41c40d00d01140743c548a14003a040030442540d082814910310001219072030184100d05c80603801030209409821819014002030801c3c03001682c800c6000d00000464440b00e00803080a0096513000d103848a102c40d0018009200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 488546708 1250 488545458 488545471
    0x304141005160b0a1d2d0628060b0f0304051f0c030b150a03090312150f050105122701050405010207121b1e0506090a051605130515030601120605 64
    0x940d9500d41a100c00004100307070b240c10a0842085107010100e89046c1000308060409090300840f01040492040020405c0116080340c829001d04010125201c08484250044c2c800002d001e00000081d904860051540584140101c40c0030030062081092881c82e0512001c0d040398035200100d500e26418010b031484075800780d41901d42c0e00b032444904045030042000c9035040542c0c4040400c2410f210301c1152110703c0c041c0404110a465170800003140c5c000b18003a2281a81e80e46100242c80d51190b02110f480c0d030707140c0340c045040f516083c445081a03c0d1001d0b0b006142d403c9103160003a40c00007885002d002d244180001a50b82d0003c0c41c141d000d82000d1100710302440303050700499018540c0c1c1184401c0c425031140d00003005241c1d1040b080d01e060035001c4040d02d28840d0004005c80c109000500c03822060160085031001900710000c0007001e60a4050070350440c0c1c003140b00c00712010107504815040b82044658040d080071090100e40b800009034454800f031070007807482100303204052250726000354 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 488547958 1250 488546708 488546741
    0x312210617121b01061e06020d09050d0b19062409030206030103030507060212040b091e030901180b1318050103030801180e1c110304141005160b0a 65
    0x10741c4010944a40c0160f4501d0200d4444030038280490381000c0d0b1002d009420101507101c1c40e030120340700d1499220640d00444000d88136520741c2c1e082441c081d04e060710450308001c115098424043d9241d0340101c1000c1c0c1102401a41003200c00980c4e800c0e40907550181000c20003641815400310400b4120703050b0203054000744901c4100034005a1145d10480341500e8150070700c540da031141880c083e402841001c0b4000400c00514041c00204445108100d016000f840101e400324808203010505024490300c011086504c1044040c2c02940030b01c00703803030880c0105280d600410340e40b203180d041c103607002111502070300101c00001c0c80a9201314400d850b2444804004101560456401800c003d0044c0602c07807104101200781d440303418285d000a0080030004042d01c11009151300000000c0c1005980100401d10303030110000d8104002040e203007150401480c40803c034906009121707400754081c003c03130208182001801f4410b01440d000886842c0304004009403850240c010f0400c4500118440302c0c040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 488549208 1250 488547958 488547973
    0x20f07090b01020325082808072a0f12080a0b0a030b1510020606011106100509090f0304080a2d03030e0c0d05030901020f0f03040312210617 62
    0xa990000a45e18800d480040c80144100c0d410a9441810703610310300200345c09000030310700d00712000401c0d440959440a00f4038005100100b0010750b8070179402c85154000880e60107110b51502180409102e04c17150510703d00ca19585507880e2900c8500700c4c08001d485e601003412003c542c081d40201c00640c04a1241e070104404445c1c80c002545404030b0b440050300180000b03000c5886c06e441403400d4104801c008003031710703520407049902039102c1c00203c4000b4042100c401c00a0a14100403590900c507414004030640068180820003502c040c029212000c43e108040713099214103410401040a81200002480007038010314120417001d40005441281144890600d030364403c02c10340b0202200d90504010030300d0b0914a10451038100c403000200d034082d04040e06841031210202c014010a1800c0c1e095407200c44a07030000943d6003482c0202c201460780300f0042000440c5080d8030a9a01403203e140c4002d12480400040829410995400c400140c4d11442000040305020b41074102c0342c864000340288 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 488550458 1250 488549208 488549231
    0x61d0c0102060403080a0209060d090f171315030212040f0c05061804050a020f0708070c09060501140705010204030b0f070315151202071e05150c030a0216020a06020f0709 75
    0x4040150500c600c0d47c0c2c020400103115503d620503a40000d000240801c44845103041c4513040d07403103000b0705803074941c10300c609100008628001c4501481c0050b09024040780323031400407400c3c002c02440c0442015030903c03a00c01c61010681e00d580c0503902032002000f40983c281401c2c030042070a0341c407561085108011080c5211043d008103101480c1c225400150b82da10901c421002c0d218180f0f0800328481c0c0051b60004110491010740035507801151100b00c140c1e01e5101850840701c0c03900440c1d0100b0708210150064501800061884a10500015041c01c1d030b42c0d40c0e400088181a01c030394911440c2c00701005555607042c40b42413140e5a01c81c0d40080d01a1030404100c0e00442d60340c9240d010410028041010040c60303030112010302c3e600c0700314550140002d81e403404a4601c004411100341c06001a0050010604d1101500501c01d600c40d243c0341d80c0360344901c48002d61041c8800c95030420361144c92405a0b5071580318a0003003980d07070064003240c042c00d074401e420007080c0e1300b00480162034401c03590310 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 488551708 1250 488550458 488550467
    0x5040b010311010c050d11010513030203070f0f060f020304061a0f0f180a0207021008010513020318010504030206090c040603050606150418061a0a210603061d0c0102060403 76
    0x11240c00208030403896160b400101da1004001c4005401c1d881000d000c0102507500c243d42c83d541013a107200801242c1c40781c0b446544200000c81015005900030302c003050226581600e042c2c011440f41c3c0500c040120699101800c0d1248200150b050344d50110402080c8074a034003541b400d000340f80c4008005c03c081400040c1110540c1c18549005103450000c03000385450364100300e21807003800b004074416450711603d400003030360000c0f100703e0090000203442c11a2500a1048506a0340300500b840d039018410001300c80207400c001c00411a40d02800032100d6211428441d00c0c3c00f45029501511541c500381c0d40f068074203054402801d020300e152810400119601046075500010210f5a814511210600f031001c180580d03003114a840110f002c1d5000c401203664052700031a101d180600040301d0b484080e44d10f05004448202020601079030840c072059102c0c1101242010031070200045803030306c2e5281d25003256517401000003040d0317048541054041e01000305139682007091004004a24040c0d40041 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 488552958 1250 488551708 488551711
    0x90103060e16080601020a0f0606140105030c0d0c05070b070e09012309040c03020a06090906240f03110d05040501060b0a1b030c0206030f040c08030a050a12180507080c01020105040b 80
    0x102000700f04030101e85107a02c244a031401e0340703811070300d090759880c0c0c1c8e801c2c868014949481065070904e00403504948950160064034421905500c22904009a20361940c0150291040340810000c0c1084920001f07907504407554000c00705640d131001d1114020742802003840d41a041170125245250603207440200c2d40e101030708082030503a02c80301e03542c49515000003840e4030707504003d500c40710318640801c100758040a074008840d0100c405104059560030f03005035100f6000c8032405100068544403070054051240100107113494580007130107801512200302590400794981d070100c0d8a5605000500c03509004050140c80d00e10200c2d4076000c56000090002c0d012109841d4810426050311018503000340c80b580030b1550090005035a9290101c040348a02d0802ca034103c401041400e0041100500041a50160081921414600b04041e0b10039a03400e40343c0e0b1a061032164544100790303148c0714504015544c8501c00c0e4002c0c821641014152401e1910303070407605045a142c2401c00c4003040025080302e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 488554208 1250 488552958 488553001
    0x4080a02062805071505070806060a0c0b090304180212060d110402030115030f0b0616050129150720041d031b0c030307141c05090103060e 61
    0x2155155140d903806100c0e182410345022445000184088945820400910280f4890141959000610071804080354400d551f8100000c0c1300a000070b017641005001440c400806040c6495004051b940381d849114085840800d281c1010508202001c054191400d0030a640d202c29401c100f140c1402c81910800101540d1046101805010501c844100d1043c0300d01e10142c0290b64075a1900002904e10801141c5030700020710305503c15000b43d00c98490210031140080549241885199403521802c2030303460300b0b40c0c01707550f1a1421450400249822194080d5030401300802c44640c03010020880346100c54020b90602c10421000001c0d541c01034200213030200d280b8a41ca054901c3c01250090001c00c01599038001382100c0e5440342980000034209440c03510000040c02d0052074075480d1100c0140e070308540c01d58814455440080c02c010235480202c11640c0484e4059580f004003103410640800c0d034100424400103407004156418040c01c4d0280491810403002c5040440c101d00f110340c210b1540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 488555458 1250 488554208 488554219
    0x61d1516031115060a1509031101020c03190b1b160f0b040f0b070c0209151f052701020c0f040609020d020d0b010f0f080613062904080a02 61
    0x1024105802420840402c104a5085811031218402880158507081c2d540d0352240e49031040c00980c0c0c844a0154040c03100c5550348490000d031441c1e032010f1031b045034035040301d0550280360b0030344a046e1801c00c1903588104a11242161013407460400c101002c2004c1d04004010140313000401c0c55446080440c1c001194400b1282c401100c076040c000e2110450b108010000440241030009000c1425891244c0f1400303407a00d5155a105c0340819142e40c1c00c0c80d00c0003904110080009650414600d03d05160381d84054000460040c8007202942d0000c070381d00c50741c00419408261f41c0c01241d4020840800880d411003800011144440003135550f4200d0000240300311002800d520503a203550700008001e01c400d01080d074480000c00c5410020b90030101c1a40c1030760b45009424000d540c41000700c5958000f054481d440658041013044960304401001700d9000720040368040544d04080c03240200a0800448003900c19030301503440d400c1c0c1c52140700d440001c1c0c0c805010510a4500c046111032469504548 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 488556708 1250 488555458 488555497
    0x120804061b030203040302010609050108071e08071203030c0e0d1b0e160e19030206030405010608030a0504030b07210b0109090e2413061d07061d15 65
    0xa103103015200390120807684940e1038080a52942c1c142d005140130f03501ca60005d20220340c40b8a041030846009208016071640440e50420944200d05a00a599540300182c0500385848445080c5400900ea214000d400c040810300c1c001e0550600c1044e820341304524012204565400019900d0b40039100c01a21418200002c1034402d5030340445e02c0d0043c080000c440002d46001041d13074075000351842418000c990b81203031021407440c0c24038444001840300440400e05074215000c0c0b101603000104102c880b0340d80c074000425000010406070800075150350303400e5591425445c00c05e00c12940a0411021701030164517034400c440940c540c440d43e46160318800500c0340b6102004a07680f0a090b071144100c0c03890851035900100001c40c011032901c2c098000388104a20003035010301e11050441e0140c11011000078044002052508814002100980103541c42161007042505002c0d0690107400402c403030002405034041c08800784001c04a0071100c1c1410000b003084103482c070744102c0540388001302d0f031a032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 488557958 1250 488556708 488556713
    0x2a150506040b04050c0301060908061b09031002030c070c050102030a1205060d0f0b04060e030307090e0403140315010e010323090a0b01081006090903050d09080c0f010207060c0507120804 82
    0x180140c0140c2c000030018445070420140445041c1d000380240b00008100b0200803415080009070f1602030407100c840c0358041c01d000d038500201604807070045075050281010b0740c0c17048d40c01400514010003c4c005500d46e41c1c0d0052400070292242944180d05540041c4034034000280c10031402010380400c824041000c4d60ad070b0300014901d01d00c4220044c90001d02c7c2100000f400382c041e0100e0310407849110200010342c110b000307641c1c3c0d034001110f0010000c0c000510074030079030b0b1514074184c1d04203109003024411034107902c0f00000103400407540b0f404000014070000c40c01d5a408034010020070000c0c01c01708110300005405611094210b008499075400040120309281002c011204046401034044149035071140c840d03540311503200c28580385660802c0404074040402e0711501401c40d0f850b4842d03e16181014207848054a0760b19801d41d5b041e4401d00c0200c1c2c3c28001840511a00e0512400042c0e48211601d4281d003112031290304041007013800e009810000710241c141c81c50f82c10582c00d2100321a0388c3c40c07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 488559208 1250 488557958 488557961
    0x506031b0409050a0b0901080a030c140a110913020a031220030d0b041122030f05100c050301050108070e0301060b1305010207120b043e090603011b0c02060408010207032a15050604 79
    0xb04040700384508440d030003d01071030303a5484614030030441e000201434540c8001010108a0041b0203944002a401d041001a04110443c028500075061001e90010040d85004600e80e0a8140160a4000160b040c0480200d44504a21104120f4003000300841c039803a44140c0340113a0405034550518800d5400401002c184588c0003180d0001c4140b402410529105880c2c13042240358443c05414076089040d04d5005000b9207040e66410380d605c0d00b0a9079222800c490301150180856015562060081a87e594044c000c00c0c031030040c29034809071145450002480d1002e1a400800010307403c405910000e401c0b19130080e007241e04044881c80c03001c5180c902c02e003540c1d01850000004500302490703061b10540c00c0311403060454201c0b004c0c00d4030f940701e005050903585085404903d006039012a4003900740607498001c882800904210309081c0c489190318220b0348440d2085c1c0c040355500701040901680380c02c400300c0da803584a0100074801c0a550ba006031b00d800050000203d5a03c50000a03020b0300c55 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 488560458 1250 488559208 488559233
    0x10b0a0e0d0204110421051504261309060b07123f150603050912030108010b0301051b19050d050708012d0506031b0409050a0b0901080a030c 62
    0xf0810400d0355200c40312088603504c684140b15800c030030004141504610440400049034220004c0e081c5e2104000c0c011116400041c82101e206030a05942014201c0c001207445c0707954680c150855482482900841e10060103602a620040c02c010f0700b44042c600d0401610b5140c1e602402c003040003511102c081d100e0710b00c3d40d0120320b000c0856a590329510004204042403e10380340880d07101140c030002401c019504480744402038199106010001d4500c00da1020364000011000c2d20010b03070030455080f0a5900a074401c0308940c1d100d10803480c1c02e2400b071042d15040591811755042c15010250707203807554040c1c001e0710b409031401400904c00caa8048c0f011990382c0303451010100994078203124003a22009085c00303141400b100380c079107030058241000d030426010000e204205a00070301d41810007031036074802061f2503410000e14003040c08900c400320203400600100d0780c0c08241c0746044410007080741d203400c0e240d9109065000042202400100312921000d405240545001200c1d00b80150070114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 488561708 1250 488560458 488560463
    0xf090b04230c1512090114010f0302210f0a06020c010c020a021f03060302040903050c150606040b16020402030103051e060f0117010e03040f0e0606030c032707032405010b0a0e0d 78
    0x40d81c800c100c198031040d80000854058040748511590300c0728548009d0480c2e1780402908101e0341c0c1015140a4429500818100c28407011554010f03014500306040040140040b00e0158002c9075a0030403500138042c41144104510050840e01e015800049040703080d210020704071341104021070445071103600882d019640182007401615094a0028207981c03111070122100e0050250201c080c0f12610313072480c09130800070312540c2041e040c0050000941d01004c0c0c44c3ca0b0301901d40280d200180c4407400038600860061026044403500c0d001400040080c80700c1040850304444200701562242856450545803460342403000b030b0846408040c0140076031940100c030b40c800480d0001c3e20480d85101c0034251600c1080100403521040c084c407801d0300090366184624401800050500c1c000c1c10348441289c000c42e044141071100c90481c20b0700303101b0702e60820b494102d51407900a08910138507180c48010360340740d1420841d962400143d18000e004000c2c0500030400c0000790807400d581e8901212000ea40c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 488562958 1250 488561708 488561737
    0x1110708031e010311150702120106061d1e030c130b010e04090507060c0206130608040303180b041103031308060405010b010518040f0f090b04230c15 66
    0x40604001040d6001200c04240c10341c92081090400094901c0040c102c0b07a102d4420380550307401504024955034241c0748801c1d44c0b4014489880035030713500b0500c0c0b00c071a0008000012081e04042e00140b929070590403807000720a03c0c5030280207940300c036a60311321000340350340030031b0000f1152400190030030810080d02d03a44031390a2000c00c0c00c3d016541d848130748074000c2625080c03c501031400030320040e01c11544000d04a908910010003000b8002d021081c1c01500c01003020b45003040c400501c1d2860052a04076500040041041000700f50701440380c0410b102c10301c409a4029000395884400708680100010100002c0c4140a41d80303880410540d55082c10306405a2581030300c41e0301d110307510b400464040e40e4070b40c00c1c0034a04820b0350084003141c408001e4030000d5021003514400f40006061b4200501402c5551a102d1205190f40c1c0d200d8640100d10500320368805061a091445180420110042e580d4111001381c0100d03100004a5030f504c41ca094804e030441c8085101d009400c0d005800f01c410b03211 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 488564208 1250 488562958 488562967
    0x411150409022a0708070311123003090307060c021014090d050c03030112171c0605090c0d0e0705030a05060702010f0c09050409020f100504080105061c0f050111 71
    0x203031001c00b510040c2000c03e088041401e00f64196998001c20710441d8255006014140080340442003810722000015007400f20011100d000036203080c0c4180350144480d054590740b21015484103034801d280c01c009281072411410100c0f141d40d101d10a1303200c002e0203555510342c4c1c407403110700a0000c04031040c3d0900d01001060a01101c1400c03480e01288d1248050003003401800f2643e0140d42030b90705140490300110305607802d00c4043c2c0c07071040e074825068500d626915001d0031000201300c02804000003403a004001e070b0504c200520244c42c0640c00041c860f9200c4401c1285e9240583d003a90104221807074003041c080070f1040080d0070454660080c2e50075020f030316183c02c144600001c40078040d42166008203c400d420400390011201c0c14440c050005000f050100705901d42500611042c50004000485a402c0a4002030055210031100004100702103020001d41d0002e11507142d00a9080d0f4000350710104040032240081d6586c070000b01800385001d03031002480403d5000400891190a406a1341c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 488565458 1250 488564208 488564227
    0x18060609020c0f0607320d020c0d030b10050d060504020f04180b010c0b190608100b010302131e0e040503030a2901110c030712050f06041115040902 65
    0x79500155042c505032194074100041c1c4030000074001c2c82100a9540c0070300140042e0120f1041304010302d8980c580b44080c0824040c03038403941005120360000b410005999404002015040882c0400540c00f03151806694103541c0d1104004081d1160040c0b406943c0c520140410000822a6400103908944046080e0344503a094500910540310b0180041d102148014403450603644544915400030314003010100c00584400825504890300344d00d000310200003403000340d04881140e88075100f1917110020b0b1900e80c0a8078803c089810b0000c2ca41540b5200406854a00b800928031441804102c1500003103138200100d0b00c0304014010030720400c0c4580c00d103070504a41e250020b942e0b0035003c3e450411b1000d501e030100d04400c004200d00100a05015150200555400380020004580341c01400754203881d6079030610100020f402c0c4040d50a9044526040040c0390621010650802e580311105000c045003600d240030300b900c0307030450700d10700c40d240200c020140c03078019640103900950010580190 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 488566708 1250 488565458 488565461
    0x1503150b03061003050d080703140a060608060303040e1b0708040303090515160f0201350117030313020112050705070b07080c07140106050901030b010f051e0418060609 74
    0x6a0000071011284141c88050307003d41c0d0b40700184401442a882010401c4d0002e001303280d0075601620324200040c1141d022140062003c00484540308081e41d1810144140b5402561803608030006a00079824141005100d89100030f0140c100c05205c012204920602c2481c407080701c08440e48105604e03207035a13991401811065880c090385209000880312109044500003d0f0780c3d00c040ba0041e40d500311207803903e41e09088094110113a040054821a80c50700da020504c01203040c20038601101d0341407d990170b00700e022001c103800107160841000304d46001d40c10b00006403504900c1008280b0407008040c401a2901c56880843e424032501300001c0002d4141c03c14044d14015000703554061041e91a410115039600085030f400030310007420700403c0042882481200380e0076180e0000003502607100e000041c10035009070b100301c4c2c41003003032001804441c100b0808440103100a9401d003000c084403001e08544041080c42880c0240d585450314204100104946501e958000d60108074440d2550030590 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 488567958 1250 488566708 488566721
    0x3051e271c020102160605130203160501030e060112022106010b04090b010e22060801050916080616031e0908091005090a0e040c0e09060a110705060a150315 69
    0x400305071001c05070071424018021100840f01c0c84801d034000c2e20056031068020800a860031951517a64041d00c0010f840400c2003100501501415007440e82c94032000400b51610050507071030340c3d081407004000d02d9100205005109904688104030301c0c1303045c4c40401d00800c1001000d1118400e1600001e84180030000820954500440c00d001c1340c5000e00054446032140a4540e4206085c0c0c205401c882d0100b00301d01000ccd0428075004900700755144145d90070340b4001e07147d803801070300180040c5140052a546500090101d213002e4011032038045028801c034810400c004043c980c840100720301c02175060b440c611444101e403000700040c00850400c0c03034040d0000000a4022201400440100c030b004d00c00380c1c1d2007910000d10404006090800c1020b1850300900100d07042624100c020520010a0100512604280c402000b0306d11300303102140140c600001ca44403c40004020769400300d0f00204020b07520202030140440c040c2d0110b038045c0c054180580c406010124400d10403003c076116500500d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 488569208 1250 488567958 488567983
    0x1203100f050103090302150604150305010605121603170904140103061d0709020a0203040803030a0209031b06031326030a050105030c010c0f0f0206030c0c010c03051e27 74
    0x40040e40303641c01075040300c1c00480c000d03000d43e000d040481c181610f0041c00560099000d030011170a03061050403181090340c00c2c5c10490f1903944681d0240014280f441444080704d5008006040280203080c0c0391500102501010f031564540c907901c49518101c8404032030b921000908108031034800c82080c4502c8013003e002c12152030341055a14801d112400300d0703c01e00070007032030701820b00c052400500000941c004030a001c00d601040c080020b080c0e80c03c0c409584111400d507009aa140301c400e0402d1705105445040444080c0f120f44050800d0711b5081c15241d1050ba00d18014104000508000800d02e0f0f40f101917020403580f00d858034110b02040c10156014201454042c011662680704054580301111006400100780160170b5001c940980041c0070303454041e800d805c1507120a500800c980d5442218140e560720400144410000002d20071411a42c402c1d180802450400d801503046070858000c0c51141501000041403c0c01d41d0b20366010006440c00c0c3c00c80c6900001c3c10313241c03615101e940c0f018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 488570458 1250 488569208 488569229
    0x30709052706060a021905460804050f0f03010c111c020d0c080c0a0c17070e0a0b04020409140103020306180d0327060203061c0f020909120310 63
    0x410b81900308101a2100707440e240d006010f00b802801e070140749500d01c1050a450610a01d04142c2c1d24400451841c00d0701e0314032003c0b851002d400d4030301011059845d000b00341c2510040507400c1700030400b400103860688804444071140360783c0440002e000181e410008640c55403070b007000319000c5a0400490322000000c0401d880c80755180703606104608a0181d0000c1c05604070080c3d082500c0c0c458411070035007502c0341040c10306281c0c040c04482d1074031306204402c43c1c000e80c80480074008083c0382441001e4803200c6c1c6004043c05400d280c4000f41581c40a0070602d03032951070302c000d44415910354050b07030060700382210104601c42c08903a00d000c806400780b10680c040d0140b00c0100303134140c040b0045d220310010b204005241522080300120024000c0d964a02c01044210600c0043c000100380540b11b014016000541c4038205503040148080700e44c0883c1610f41c1c040d20403c4002032082d1071024141d41c0488483c01c0303540d1035505803414500071502e9035110351000002c0001d4241d81004801c10303100072900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 488571708 1250 488570458 488570461
    0xe0f09010302030d3f1109220905030d02040f0605160305160b070827070e0402030a0b10080c010c081204110a0303020304051203120106050307090527 66
    0x9004a0080030700010750940c1014121180050280240144603c0c002c0901c00f481c24138a201c02d5036248030781002c509000d010071100004800e0901402c4a0091110403441c5021042c070001041035440c500b2103603000c0342244c80f0b01070507003541e03112400d030725080426a40d03140741ca0a4030704000c0d4043d00502c40202c0c00000c02040c5240300d00241e850030b401111003103200780619141034800d40c021181e00b10750380b07050040d40400940e00201c0c80e4010b000a45551f1140d040c00c040001525044a03017041016500705114841c400000811000b2100c00c0c3c04170703880343c0d152400404d0804004840250003045208113100d41015110b040764126a41502582d600e43c00c4800111070403039a004010f0700c1000144079180290440b1001c5a40051140e888108036503e0040460a603800941c41034001d60000f0508104a0400c14140740182d07080e0b901840c40d0508070b54400c131070044180200820000088006000a80540c10103800707481c2c024450101c041d090340d1340d941440d60f0340c0142e4204041c0d510 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 488572958 1250 488571708 488571739
    0xc070b070203010c0203031003240603300e010305090708030708070b09070b030604050603102412080f0c03070606090f380f0a09140705030c040e1f060e 67
    0x2050308d01903220868820071491440d1500d4000901c000e0810071031002900565150002c1c9100d803400840c031031342168990300c903103040740e012400e4034441d880e210b15144000b07101301c2c0741d1040507008030b45401d090010b69504c070165624038001c1c0702c2d000900184400200f1200b4004041c016155140c8100d1141c10b080c0d44400c0c030552110742511610721010341c1070010450700c0c41c0a40055911a4001d001c64103000d0213105c1c0103042d04c10441000210b41100704106036071035a10090790f00074002a90f480780110181e80c2e1060490b05c24040144003032203002c942d40844144c00d00880c1d055540001c01407220729210b019000050a107074445e21981841c1100200e290040807520040c2400000c8030009003807603000400d1044c1407241125640020480c1e144e80d01555004c001c0d034050140054002807003410640001d90540000e0051824481c080c410005010001c208032019140c058a42c090390b2388030300e8480f5042881054040360403a20340c800120344107a101000c06082c41040301d80c41041100c030f8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 488574208 1250 488572958 488572963
    0x5090d05301819030b100608130201030b01090b0301150801082406031608010902011412010918060905150604020a050304020603070e0a08030304052b0809030c070b070203010c02 78
    0x200c81607020140c14031501d91460608442080c1d140d2010b050492400440a01c40382c0c3c0720415001200d50004e100c0c05e001303400900c009140b02074107580c1420302c1a410411460341500000c3c03803002381010303280e909260184e441045058010901d00c20341c2d54495845841003020424005a51800a10041e000080c5401c0000e03128500723002d610300f1000c054034030030309551040e1001052681c0503c5981041601000d1509050005041075000000c03107144520005209085000000f00080c600b4454640100d11404030f0f14119000c0e41000950200e03034444100c2549020000a0811803401908000303112001c03030042448034101424110a03a504800c02c81240a00c80c08940022020320000d40142001001076401820a007484140c1c00d00320000600c51082c5508100d0042d040031003480100a0104580610350b8044100315a071460220307008102500e212442400b0442c0290124050003414807c403240c3c181e200b8190703401c0030386030002042c290780170035002c80c065841d101050b01c0e5140302 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 488575458 1250 488574208 488574283
    0x203070206160216030b0406090c03060e151e04210210150b0316031404050a0b071b03080a0e0a050d030605010302040b2d04060215060d0c0522090b0708130c060f05090d05 75
    0x3f0503a90030300701044041c0542070700081040314402d1000308001090640c081e9516401103040d402052440d80012810054035482d1400c4240c1150966040c0400c00780c3c94150b91703000c141c0c400a08085003241c00700f10081c1450204000409101c442840240403011800c20309007801a00418100d4860030f00480d1840400440080e10444151002001034402c0301c8482d0007040091020920b021016074850525410600c1102d19034821103c1d41c2c43c13143c04d400380c0c1005203c242011070905142004640451113201600701103441840c3da040400300c0140811312840790080301854035142c0301d01001c1c0d901c0d0030001c10482680c50480000e00c0700d00d800c180d0010762075030202c08612410b240c4400d11860855104076a0b007100c154605400c46001140300d13904210b8014110485141440f6001401540300078000542140d1507100302c1b00420f5074144118111259850074840d0701c2104101107849000c0c520900b6440100307441d030380d800c2c4500041c1d10059044941489000000241c8012080c0c282 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 488576708 1250 488575458 488575471
    0xf0603030c14060f0c1315050403050609010605031e010207151a0f0d1226060a05010309111c0206030112020f011b020f04020403060203070206160216030b0406090c03060e15 76
    0x10b030740000402c8001d001001d0700f1205444007451020684a24805406c07e115000e87d0307000900c00b0a003001444400c00c0b040740c03c910031600801c031860500c4040390b15580880c0c040800c68140c04c0600d1440c003803d40c11550b040c0d410000c04804114500000b10141c0400ca03043d02e001802c0800c56002440c05800899900100030080d48500403950780d80b10b0b0042900c030041c020302c1140862a1440221034a501c0380044d01540586440d2030f02908010482d0800d0300002e04042c50807460030006480b007004061040011510103107002010190105241c44000e0000d40081c8040000940d40740714142403040b1600c210360150842545d038004440b441000d81230961842c01e580c0d030703040140c144a11071030f03424040a07101610341a12516241c7c16030344141d4842c40103a2103d4100480c0b0200307200ca40c012102d103880944440c41000e0040300d00c5aa0b20f000c00f0700140005004101004035a5102c0e901c0c09600100089449643e4209180109021540c054407070042c5804000440c0781c4d1a406413150300d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 488577958 1250 488576708 488576731
    0x51b01140a1103041106040312030204030611040e04172b0617030a0c1505010e100f06120e030c0a0b1b041d090f0712031404050d150f0603030c1406 65
    0x1380c40742c9820302c400c400d258260350044410403022001c00c2ea172a80d440e26120a645026070b13a03e1031481c1c03220482d180d03070b203c11342c88980910091029890a16070640c101c1d80050030b2605401503103104020b07030300c40c252240e808400c0410b07049030070386070542d010803120381600020800c980d51030080e4076544031405000c0300c00b80c10400800711894050f00c3e000742c40900602c80d013100c1188160034541124002e03007144841c103100d81c8c00c1118119650344680050590b03940345032012480e211005d480f1200c05001025440d488200e01020b41d0420015250003d61410032100c0d144c00f6410a8490300d8030945124800301000e0204201451080044400300d540c0b00d000003409a400c0500d188280e10040c1108400d4000c920540c408058204140d0010304440c0c18185c818a003a460040c22003902c9104584566205020403c00c9540300440d600006803c1101d07101103080800200c0c00505108482c42c1200345892404018036900c0040d010f0b80b6446a10300c15050060074058941d14070f01118140b5445 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 488579208 1250 488577958 488577961
    0x80f0d0207060507051f0203060916080a1d0a1407062a1b06080108010b01020a17070c0e0a0527060a020c0a0b0c03040605100e0a0c051b01140a1103 65
    0x580c8941c0040084601417030942c0c401c0045100144074240484449801c2c0035004001d02000d46010481c0340d0300040f2541c4141c1c100c251000006d09a15001840d8002d210303980e01458401107110404128259209816541c0d40d00c00761604804801c00c008203403160340715180700030070058060007000109006080101247d4060502240101e04041d1402c540c01c5440070300100c0ca4082d030400107400307801c031a100c540181d814420500d08607281014039504561092400e0380114496480d002188807400c07805030f0351841b40d81040698103240e0361200d800ca513148403c2040828441e0300c918066640b0702d00440512004c521213030264074241d44503801607000030300407a42840c4103a00078030300080803c058500c1403980740c6034580b5848044411503d0307413000008020801c6554824191300c03c2d554400c0b002a41d0420052010442004043ca1052640e4148a004142c0118245c90654038500c3e036081e00d8200c0e01c10014040d0800c05d9032048045e4880c00401c800c0b03c941e01070030382114180801d607810b6 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 488580458 1250 488579208 488579219
    0x6070b0f0601200a0210090b0306040b06071e211d0f040c030203060405090f3403050f060a0501080a061113030305130506030609040213060b0c07080f0d0207 69
    0xc203901515003414480c41620365400e0b54a04541e55180b410868040d10b9190040d0042c0041103045008034001c1003401300c01480319040140c252a04a401541d00040500180000c12618072514001a1012980c40903203c404406040ca981c071603481001e0402c0e80c0031244503e0104201d403403283d240031484800b8006004402c0340403825250200030308051804a0060204040b209201468000a90000104001410306000c0c403500b10003508024100b0002842980c0c0c2c03140955541426105151402011200b044034440d54030156a11313641411640c2d2490320716a98081c02c8560f40c1c49014944c00940c040780c003841460f04881075000076103040e1140b03270359000042c4510212068805c6090241074088003168850300c010b14820380318103903a02d0149029512450003503120394499a01081009000c0d110141d0342a04942d040c5c0303211903482d0300201c0003400350021307030422407450002045a024248000800390304442c0c41c90159203503101901c0145885500d0800120f000d0b07400750f8010003d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 488581708 1250 488580458 488580481
    0x40302010f0207030b101a090a060c14011b0206100e13020a180524220b0904110a0801050103020307170f01090606030303110901140c031c05041106070b 67
    0x411080c0e2043e6a61141c42e59900340301c10701d01307882070541900ca0752007d1002c0410f0321141c82d00c2020108050b4180781c21400003c440342650300920b020040380c11112010400c40888400c031391041000280441c020b03040c0c40c00d5a034180303186035000601c01c283c08941000c501d0b120000907101e4190100b810341d40c0307681202c07548114081f1700301e822a6070f00b1000100001120300c00300f0a507103c0c000c003107168200035240d5101045418151801003440c0d20500301666203009809603542c44003090518500c0c0500d900c1e0000b060b080c050307681c2003a140c2d070421003081102e800c00300445008640c0c2c0e1040b10346130207a95080752024000250036502480040c407501a55a103160340010b501700c00c503840030074040d44060031340d142d450307044071000c1d01e070813040c0105600740c000c8614018000080d2410901c44400080c80300b0110f08201c240300c00001b6025410000c10300071251040044d008450003414240583c0e401070104950550300e04c800c0149010842c6000d03011190040d820543c040e2660704c84808840 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 488582958 1250 488581708 488581727
    0xa020616030515150708120f0714030f070306150e0a0b16020d11280b09010813051c110715020303240d0609060c05160f06022104050106140604030201 66
    0x5911200703000000005a00d06e004140505040031304140a040000300c403e110032001e050031090000d20384110302e4001c0b424090300e501104050140020382c4401a05400814030b9070044006040640780300194580c11080000b1003c400743e80c4030a02c26507070b110000705802100c0404140103041d040303c00c00340c0340c8109110051800341c00c110071401d0090000800358088008107101e050700140380d015000044004c00300c01003418a03103251800404000081c00000001d1148414000901480050040c05c00c0140540c1e43c04200106c6061514217010b055103035004400d110320300c100300002c286549650006441492140c008500710f441c0c250401007034008170303000404c280e0324084400d0856600ea000c20610903008090006580b01c0d2400d001c0162181d00f000e50b4240202001000d0819184034080a000b94100d40e614410030410b140003800391043e5019541c40003000e9107809014115403c0003401288a00c00810035140e0300c90f40c1404e401070b20710113250720150078001003000d54026011300 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 488584208 1250 488582958 488582989
    0xe010f0c0602091302031612061203081f0602030903010e010204290702040914010b0f0102120f0f0a02150915280c031b0831080a020616030515 63
    0xb04c4224100c05680b00306c0c3c1049a42d01d01d01b981a03c9013081d03564001034580610405d800e0f041c000c607820302a80c034032410708000c40142004080e00c00214803200f510480d00700f040d200340600034032950b1138100944e0b981200344860310079460096903c0c48510140700700c0d0115101171810344000c01d2803c03110824030010b55602064200f00708080703401a03685100e2130300102d06c280e650b4100007180361503103403c4175150740180340039583c00b03003040304960b80002d603803484501d581c401c042e40c840c0c0c2500e40283c2c41c055440c141d00e060700003203040400b40c3d070040340b000000207a41e403d20140f59288604517544411500c5500704a2001c5004106401e0b0360300c85c080308080d118801150500c40e4030201d2022195482031010000e40c0c0c50180601342031007000c1c1616820080c3c60052080c0c24a0740c01e038540d07030b40c0c0c5006808030608040d043c10320110a805c0b6601d001904641900e4588100755006502c8040488018580c0609401030542c0c9030f00a2107200d00407581a500400c00160036820b1060040f01c03000c0c035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 488585458 1250 488584208 488584219
    0x60906021617241815011806091401030210050f070611090d0f0605010503010b090a0902011709010c03111c05090c15130b07050a06090c05040203010b09010e010f0c060209 75
    0x800403060724014020120a41d1000b043c00300e152000400c0210180811020020303084005213401d0041034451080c19075840c800d48080d607000400a034001851641e0040c0d03c1c40f424400802c100000b800c134101c1c100d074000d40d00c041030b002520004441d14030400d000203010f900c3c01c0c0083c90100704503512901140710030320314041c80c110050b0000750100d03204800884000d070801c00102c04000c0039010f02030041c4402c2e0b0007803240d4000240002c0c03180800829407504c940d0356207402000e6a02c50030050409101c0010440c60604210f440c4a011f8024102c1134404a4145010181c0c909008002c464000e00065414004503c050091502902c00070703003080c0d000e01c206450f442c0c0c1076913040d8011030071400000c00c1c03580c0c9101c0e00c000c002c03110700c06078800f040a0106200e03600203d90045052124a903103c1c0c40025584411314280b078158440780c100a401c0392000c0700100d0041580307401020f100701c00340c0b900c00f6620400801180c040140b400c0c0c84000031200b0030903000090042c2c0180001060080c130 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 488586708 1250 488585458 488585473
    0x30d02340b04080c030c0105041203030509100c080702070e0f16020f070b070b0f0129040b0a0c0302011b0210020f07051902130204050d11030307050708010501060906021617 76
    0x2070340d1160b904160031100d196004507400f04000d10701040001503028003828441c1c1007619011005100214203640a010715031100001038030200300b404038400e65a200c90003000801041c2e800144030ba1030850704940980300b40030300400d103100725044051090341608402c0580b55035050000c4200000d00c414003040d48266044541c5004061001101900c1c0380080c40380c031181c0346c5c10b10300709044024081848640241c0e0050044155610741c02002001c20321000c06140c0404441e12118400c0f540801100e60780402c0030044075500c034a040ca0000d00a500900c00c2c808110352510300000b0301d02e000009039000c01060b60014000d40c0213019a4400011024249501c50300c4140c20982807414000200d203030003011504510349841c90810b45888800304604140c140804640f903102e000780040c0c165040704e541c0d580680e42c104200c8864075805021355650b0f603564860036010340828020300c0b010900c0c0c001c01003149440051030784820340031001d524402034a00021071030744002125007140240500d41 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 488587958 1250 488586708 488586719
    0xf0118110414120604150c09080d0e0310090b04141b0f011b0c030311060103030c03080c1b0c2b2603090601060e0f090a112106030d0234 60
    0x10312417240d8041c58181e0002c1e22030076460070484601e0105031042c400c2c10329060000c2840003071000076411a0781030005c030005110002030700d0207070003450350b00721740d82000514000c0003085441180511b2141070341075038600340c0f031040580350000c070181036040030980c107000d1440d8980601c107400c1d0300710103050164640b41c2505541907000b0520100380c0e036110700175408200f015844034003c4000704042000e01225411958020310080d458000681002440e01c00304103001d200c030080751442240d4868015074806143c141c26150030000c1c00780c0f13200d0092002c6407180100055008900d442c2c0102c000c2c00580743c6c66031101d0603c0340c5c072544550854007480040c0c514510b034100450003510100014209580362403801003a00f944022078901071282c90b0007900712529160140360b04121518004161032072402d4112903240503025944031640c1182004240d54500c070b045480c0605402d0f42680c105210000050385e0f1401866510541104002509900304c1d0204c3c0c501001c1c03810340051100f00c6650f5a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 488589208 1250 488587958 488587963
    0x904061d010906090b0112230c04020c010e01050606030105240f070503031506090a06050c0f030d0b030601050402090a06050c0102131d1308030c07020312030f011811041412 76
    0x2030742e040341d04983d01c1074001c0a128402c029103004040502c000040c09a031907541001d415181c070b1030604130704c03036400070030148007400d01071101c81150240c02191160701c0c10525601805540a100341c09519180120b0828200310046038161140a4424120820b0915040b07616555012072098603100c10f01884111400c080006c041c628068030085803a400c0203041807611070741c2c18104c5c2d031140c28104141803c5883c0c100341c0c0801c540013030800540720040c6048050130800030396201e0200d400001490f518801056204ca80078003415030171598160388500c1400101d20070303c2c024951000c0300400400640b80b18600500803001c1450000d8148041c3c02000c800c00811034108a400c0c0c1c040050240550b200c4101295000364003081041c00c2d03d109803150340e101e10010b440c0c1d180d03c480014402007951010000041640826100340e503891074501d01c821390b64407003070040041803c52500180125141800780703080d46030f00d05071014075003841c0054041918401e40034507900911404040c52602105 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 488590458 1250 488589208 488589221
    0xc0d06030b010e04050708010605030a030e030a0c0b04080c060421150f05060103050f04030e01081e04060e0f07060801180605060309010b0f1917151906060e0904061d01 74
    0x461000484c100340c900281800403580000000740c1c90401c040105a5001420b042c000350542824010b000c0070070042424003000030009024000d005600040b01550180184210340656003038454500d64007041000c10302c034610443c003c0010000020451782c000d1004480c0e220321400110b1240da5410701141c081c0c0f0510b00d41c1d9005540c1e11400c00c102035816009048d030040303d5000454403840c241d6405001303000c0304d824050420640c280003d00131100210b00198022100328400e0701803034a0f14000015010b410074800050217060020766041d0400226202a40c2b1140c5449071240e080c0500c4090604078901d2042e071140d1207540000d81c586680c8011405036250f0000824403044000900020301290400c1c2d82c05900c0701c1d038201728107601190404055407000201c0e0300d00c0c80d0543c0d0005180c41c100500f0103613440a120180048091582c811810020401c5000d010303465a40c0c0050b50355440000b4583d800548010004001848075841421110f2240050764400003209005500b101c3c00d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 488591708 1250 488590458 488590469
    0x40b06040924031110050a0c1106090414100b030115050a050f0f031005060906040612110a1106070c0812060316080a03110706090533120702150c0d06030b01 69
    0x1081c00071290a410007170610b065245503800c210385040e01e499401880020440703c05442040070030354000303daa4407002102c049400040080c401204951b45a1031500403d44184e4184201d0030400268891004c007070303d04a91013032400641940c03100c003042c1c0340341e4444151641007010030099902c0b90007101000c0e2140140d100c0f040307600c80c5849000c011b04032029800603442158148010b4400f81d8881048606a811a00e405204424000c050202034210046e0030021444c001c10500303070140c0c0c468a4426900c1c408412901541c5071a030003a101d110001d50041c2c01c4480401c600c00481201e4042c2c29000a00074007103130107541c011500794600d8030b00e03074100207010f80009042105041d440015a800a40158041d000c1c0502d40440038040e60749620809000780b1100841104110300c0100c94840c000c42030f800780c1011603001102c000b1300e900800300c440841e810b42001c943c1003407001610401f4030994181c00802130b101da020100c150b07008004a200d12030b454500c0400000e01d0004130a0081c203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 488592958 1250 488591708 488591723
    0x705010902210d02010506030d1d040207050606130e06071b050706050a140405030c09060105190906030c0e0f012106090e1c020d12020415020615040b0604092403 71
    0x1600108890805405103c0d040c216030401c8180805a90007240d00101015a81040c9070203001094005810384030f800b94144d48144040350941c1402408a01d05120307403030845d0900d20307042c0e500c41c10a0869414512640b4554428030029020350f00580b811201c000d0701950304540c0d90140d0744c805191050541104d40040c20200d21040c189820540d00007190100b449440d05190800001c6940c40369207040e400c0c417840f07904010440590050b001c0f2164002040458610b907910b014001d4402c802070310603140005d02d0500c210180505c604560b0400101c028080c0240164000c0119a100380742c51071520798074a1700c007200403405000d200d2070300144645400441c2243c1c0d183c095605016407411683d0f84060310b58030035500305601090700140e03034107d4100f201400d6007200d001c0e402402607401491461000d07121401c0002d800180341c07840ba00c601c0d80e42c02d12503840030b0180b00642c0d00e0480090340050050105100184050300708544291822400c0100e202603211010708000c0c40341d2080e1a1407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 488594208 1250 488592958 488593009
    0x8040e04151a03160503120a11030c01020414041826040303080105090c03010602071203020a060e011409010c051614060f0403090803030f04060b0406181e0b01020d050705010902 78
    0x1800c00740070304c0d0040a1844280303440b051800e00400d44030740702c101c0c00301a0040d000503144070140c01a1565140c000400045a40750840e81300818001e5006000d9081d00000210400e88989014010552a52812202e540d40d4901c20750b1800c08590f1000031311166a804c1508952004850102820085010344d40b00032407035240905000801c0006443e15a18030300800040c403050b5000a03610f400c540b406080148284d80c1424102c1c20a02100001050b080c203041e17402c00050b00c15042408603070401c8103403030700719121075010f07500301d85800c410440030400a1200c0c85902c501c0c09940200d690041c0d4050b880b50780c04075085401c0240490350446210300c004184014103510204400107051070100940c07039420103001050786448001d200034013264031026484250740312134001200500d179103130700145054028611000a400b4860310300d4046540512201c602000364002d4910341c2c841038000c0c0c2140c0700410b400711000d0740305207802d484541d250f00d01c100060300c40c4210000c0c0b18007a003010000c074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 488595458 1250 488594208 488594261
    0x8090307030233070b0403201e0d020f0d050706061206020a021e06040b070201090605070807030b03010510050f0d0503040b1305010216061d031b03060702060408040e0415 75
    0x3c1c5655409000e4894414800700740014661201640c0081d01801d0200d44070100001d441e43d14203081b4802c82c081e0103035140c840242e0041c03000304480c9050307a009403a6880502c1d0710403680e44010790805007441e0f001c0a825102a0301a03c000c01090380168000302d1080c0d120740384503048251411080b21456800101400f4455040c0301c51460301c806401004100c40ca40300941d83e448402403c040c1051fa000000f01c1c00e642d000b503010b001da03950700c500300b44144d20348004080c080c0f04003100c01201190034810411054601071050034030070080c0b4811b4101c4a4145024020014076060030355800c500500b0a04020590070800781008240c070704101030f50342e000030004869034a0242d0155044d0b5012140039084c000400745140295044c601d00307100984002c03218800b5040342200c03100e03014003c014100555090754404503c0000094048070101d442d00d02089a948400303c60142c1912010310062004805000185400601501d021506e020034a5100011203894000c180c45012494650038075 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 488596708 1250 488595458 488595529
    0x8061006090b0901050d0209191712030a0e150a020702010909050403020613030e040e0313150804031d06030a0f06050f22140709080c09010b0403080903070302 70
    0xd4401880d19640c0709140c04251801da000d80b20401d0705000d000701d044105071b034003903040d04c1641100a1804208003405103000361501c4150060300d80e1740200c04901c03500010002400d980300b04160a010b4074580c1c0316240742c00202416590002103006060010113400c520000d07881c0151404140166a034404d0300c0090705508032a48110801d504060802002c05e030085180e0380e01890b8941d15564040e01898101c4000008004480c0d002e0310b0024450044130002015204030519846030b00022a2120001d0b5162401d000464001a10020002e4000382c13065404100d0010780001c2d404450f024480001c04640040300c880051540e28404800710601901400000306410744250030385480560102c4c200006c1102c1462422401400403113840c80f581c0e1001c041c1030f540313404070301d40c85c100b0501c020111600c0f40b09200c264442d550b1a40d0581c03a282c00b240e81282c100744907451030030f4515038500f015600034007026a4103000308000040540c50300e220a900244a11202c10081c02c4912403044 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 488597958 1250 488596708 488596741
    0x301140102010b060405010c020a0f09140c0414100210060b030402031c05030a15080d170f010e01060c110a03060608101a06070213020c0136060c0c05070806 69
    0x341103a0415400391420b80300c071002c0310140d4100380b0309030311140b950b80080b46d1078130165800781d100130001e10b80008500c10780364014040c084a0a0001e411901d4201c006100782c09240510300c00c400c480242403600345441000703480c0c400102d0050b16241c00b0707034400010442d4025406584182c800108220841c9800e0041382d1440103e5800890041100b1700b0090031030200074001c0c06981e80d04c00700748110304081e0341480014040c0c0001c490111003070300c400400504580400201030350840010400704489601d80b141070341d50400300c80c04107a203400001c584522040c0b03c160343d141d072007180b11401900c1c2c0781141c5016502554020803414584204180741040655202e01414581000319100c0140b884504040860823210151114414000244005101c000c80f1a10a00c002450b504007071064010429020140d214588001100b00040309040b0301e0f00d1610072030f003852801580004a03590310808990010785041d00b200c107059134400c0d2500e14143c010b411250b00c0701c402c000b20550880d0545 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 488599208 1250 488597958 488597999
    0x602070507063005100816090612031215030b1e0c090a29121b03010501080703090302010e03040b0c06010b1306030b0f04060e0702060609070509151b030301 69
    0x30440c01800d0a543c201280038039550022a80340d1010441102c0c00300080c101800c80c107000e45052006090308025001500e10447c01e9842c14131000048040d034100066904640544440542e55581440307400140034031031800411007514440840495030700500300303116400881e403000240d60b4006000d20001001880c14aa41e031042100189903250032401c2c101700c0791800c0c210408aa030401d040312003614046c03044000304101181d03101003c1c688076182c90099284000000b0441d004460003007062101740517642c00b145100c0d0210300d02c039109600c51040140248000600320800e41401030850b0f1041e44243c801103408111007003962002d1058500511509503147e107020f2800c181100c0e1403a0a116501c245a030b0b5050400300f54644400e8034a680c88024000c014842e01c030f0180c0381340340c88280c4520b4014800d52001620a00780300b12214001c6140c0d44030542004840402c000c08192132070f4400107004018000348403444450b110b0352541204103005141c0302e40c10045445000b1507400c400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 488600458 1250 488599208 488599247
    0x1905090102042324030103060609060614070f06020301060c03030f05070c0308042409064a030a020601031208190c0c120206160509061b0a060207050706 67
    0x401c104200d14503e000303c104030412440344012040d00043c032441d80d00c900e94034040c40d506001406500c69070000e40c182c0b4800c0100300300c1c40e6114601e41040794440e00601c0041420303400000c06c412032010107840340c507100358048105200d071070b0f480710f00785e030420381c45003010424080003902019054052881c2405039800e04011503d0555001041c0800845000c0c082c408110007050a20020300036039050303e40d0407005c18801804441000000b0645ea180545031a884d01d45040a52120a440440120307503c00d0f16150021651441c00072112103a081c214100b01d14950303914045400388090098011180c01030040e81d17140d8285468480c102c0d0180b9020001e0000401c0090040151f404040c00404000018154a400001d445011100902400c4040001d680f0304d4040d40c0014200d204101e80a14045070007400c8800361554000c4400130b6501c02002e00c0610080d100c4052084000c041d01e0084503d40002c68a4100891740702041c10b6450350000441804290b1304081009190391901c180d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 488601708 1250 488600458 488600467
    0x81309020c0606010c1505160f020d0f0509130f0902190e0f0601090e0a050115020703020d3207260d0806061308010b0a060302070f08211905090102 65
    0x20314603101d000007001071341440041c5901d042481021207007180d0f2000401c41c10003060a20038000c074041c0103842010b0300010070048540c0822840859695000b503250b032118000d181c03140c2002d40303607508429425a004100e11000c0c1c1c061001300d01901d0601410032000240040380f50051000300808419004070140c2c4040b03080011301c0c80070b281580d000b403d07212054035030b44074840100c0b001001a4050180c58422030b0601200c0b00f01a031042e070403100c1540c54000d00d00484a010f80c2c0342c028074880658000b180100d0000030817403580f403030011140354000100d01d811110381208406a400400420683d001c0342043c00310402c0500b80141d041d82c0385840341440e055559070781e0750724001d030840c110812204e01c0100380700b52682000d070340507074410f00c403002b03030154568122900034428442014803580030038500103401400f034030803944820b4204200030a01d05050701c804079560b00c1072039245185900106441219507020b41c20500030b8112001c2860525586154803098440241c80d0403100d910411 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 488602958 1250 488601708 488601727
    0x20030411151b031e13050111030d0e1e0f0606010512011203030906180203070b041212020f07122a090f0b0405040516090903090b0d02090d08130902 65
    0xc00b034941485002140c0011030301601d030720900b107010700140c404101e400310244080f4502141c0c0680501c140c00c5c4405000550380e9801140c02c1c1c00f003032040d0315440d0804c000101454031150000d10340d96031034000711420345400c4c020700c01268100e82004441608a0b03e00d024400005100756900a0000d18140d410440e4002103120b40c0745040c0f0412403121403100b088420540203411407204103400c810100151088504064110b0308691400c912a00800383c000c100e182c50403040d18140e84402d00c508401a401d0754440700000405461501135100c0c00448038604581002440c5c043d010001c1c07000340e180704a01e03040305d003444607074942d00c229501d90a040900c210341e840d8a9084075000c150114914000d80c42c100000d048864599404c02d0400d402c01051140015000e030030301044043d81c0d00c0040c0e40d002c6060031244100c0380100000e200401c10008240d520b0054685840e18540061520702c2183c00103801c0c1000a50440e180c44002c1a14000c2844601e4542d00030820400c081d4030341810003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 488604208 1250 488602958 488602999
    0xf0108030a050904090b011806060c08030f060d050303010602210316031104030f12200a02010819021201060e3f19060c09080c0d02030120030411 64
    0x1071585081000118000110765a240c1080c1e6190760004e440c0c40381961601150700c091200b01c004000c81e40c0c142000040c0c0350344242e079407c041d1600400005d0a58982c94085184000040c16080e480b81d0242c1300000415800c1c80114001c16003034004040700e0010510000c0c458000001c48411b2410074410400c134409808100707130440c205490000303003080035818003030700d0740c0a00d80015000c0d0b0440d8140348204502251268181c44942c1c80d50f075038045504501080b07801c946440d4842c00d800018620b00154040c40d6815000743d4042c000420902881004100320b070000c82603500c0030640381d0010401603801c600307202102c24040d10b81004044422681c5200061100201007aa0740341002800070342d82c0e1100300700d40c03c9074280240c901040090800c4200c5009480051700c0c06447c00c1031840d00c048c0205103000c1200d44810207010303040000707410000d02d650391400c00d981554079080c4e450350b6104141c421032559080c0c441c0f40da0300c0c1d09050804c403805101c40340320a4000d01c4104000035800040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 488605458 1250 488604208 488604217
    0xf06050f040e0319020a0b06040c14180909010c0e0907140c07030f0f030f0c0c031104090b13030905090103110d0f020d060212060405060609010e010c05060f06090f010803 75
    0x3590701003240304140360628611310501440b403180c07a400880c840b01d400e5000c100265161b0048441c4a01a141c09040101f1180c5540200b000307d20703000103400303e4003400405440039585c0c0082c07500c42c0011010125005900440380d51036140d543d0118074414681203141d1072038041d01921841110716154002074290a000c207041c081c0740320045122154144200503050103994815680701841e40c1c2840d0a5019040b092402c0300400c040301005c00c103032841480e5483e80d5641004580701103034519140c0003810b46c500c26015402c55101d890a60224508140c698020390382c6d1a81040315900f20b013002031503e400c61b00464800c00e548401000402c000050350b8891b43c800711580c280486080c030705124502c240c504002d4004010180340d100f404007550250402d440c40003450f0759180e68032070401084600c110f44985d400703501405075072215403107410400304440741030400242c590001c4d04d03240e14040d0101c1d0b030a8400c2c03c40384200001410800c2c289030700140d240e0000e62107541820310180d164020f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 488606708 1250 488605458 488605489
    0x90d0207030b0a090c0302102a0c031101050904150f0b160b090a050a03020c01261512030d020a0329010f091d0108010e070e011205011413060f0605 65
    0x2100c4641c8001d001008405c05c0c01140e0081c20b400300d8048481d00a030102002440c0e0240c800d007144801101c442896000000c129440380d0007800f45402c40e41c0e4403404e000c915040904129007408500c81d40d4560348140c003003110340300743d0344d42c15649403440340c8421507000e400424450500b800041080b0b804070569250b800c1d44841c1c82c0c40306130707500d114440c038050b81203070090a140719410059042c1030b004908801031103000e99035408184200004940c2c07d003006103a0403400c0d0304100004041c41640c01e03424800000c018545606c411025507182d1a64101c0604036175005e42c001200f0700304d95014821032a40e44040d14441d01c0303e200b468640c0110040301016141070024034104485918490f600500280c180784170b40c500312900031160109585402d005810840d0b1802507014008807000070031000710754540207220140c1e8241640900301c07014207401160907641740e8800c800c50542c120303402440b43c4490240c00c1d003445101d0503c00152541808014019440c2100611464540849001c40c409 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 488607958 1250 488606708 488606711
    0x203070504111803430503030a120e0a03030b03150f010308030a090c03120f02300d020412060b04050c120403021005130b0a0b0a0302010f121103090d0207030b0a 71
    0x2084240405d06004a602003418500d0000e00e81d044921082a100c0004d52250443c4021005100c22002c0d5204824011203038568000d0140c0c0813414810380c0312800c0181052000b040010000701a580b6104c218202180441e4070742e84820744d2810200514075584942c281c114402d8140046400c00380302041c080900080380000c0000c1805a02d0340111018aa00018001400341c4d00d040c40203055000240110011305460400a10342c0d20019042c032034060116000200003510801c0c00700750f010441c00d4004802014400e03400189010b2028000400c1b02c24907485e060b000318603104040320408480c1600c43c0c0d1070201800005401c03803050307481040c41d68844580ca40c40c1c0b401c0c1a454844603940c003d003500d00700400c00640c03403541d07140701403000e05ca4000e010007611008510025500b4040c222074020340e00c0402080990b220303840c08244056641424410401100c24620944641c41031003441c801001092121840b0f04015215410b001c520207041c80324110f5540f100c0068000d0300c0210085d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 488609208 1250 488607958 488607997
    0x150c03080c03130f0501090c09020a110c011b020a0510110d0504030809092e1d161b0c06020705130b03062d010e040309050a060f030c031d0a020307050411 68
    0x5425405042c7c0300d900403100c0415103a031484248042c0d4007041000700001c90146081024100c0022072034000d41c0141c4403501410005c11144c624042c01e442c00b41d9000c00380c45400600d9856044a0f814403401980e03501c174803011065210341c03400314a4000d42c820403030100001c0002c00c1003d0b05038bc0032840c2c00c0b0741400142e10741000540c05c5c1c0b4042e030071100402d080404021813046a4820a008580707000c64940700440744403003000300031401222540c852100303040e04900c02912601ca070103031521003000429818001910740c0c600d10042500100c000d0380c030141d0140300529010042c194207003810082440347c00100f4001c29110b071400340800b5000a808140040840083e600c4159185010105840b056030740e0000045070240990302500030507441c280c04221420325150500540f0866110300000606e00321048005128451140c3d08055a07074010080941c911906154112101c3d0010300c4c220741c00d401014200f402d15030160703210310316009541c51050b6074041035a10316410b0081d8148203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 488610458 1250 488609208 488609213
    0x9060a0f02092205060103090816140a06090b061f0c03050c010207060b0f040b060a0f09030f050d030608010506030a0602180306010b0309060a02092107150c03080c03130f 75
    0x103809118078035540f048030342d5003005418114020850b9543d864410a0000d51650b600541c02c0700c400510141505c1070030410000c4c101c420092046103035100701c068001e081111a02a42841409441120800d4464103036405001c40070301401d030005030844806000c58030950900380f900c03d54444010a003c1104031034810302d4020400d66826607070140c001e40d6149650b1610320020038509081d20310881000c4102803490400340701d9019032603005010186041d05d0030105443ea0061040b000302040781d80c2c02c000c00007031200000f18208a1143c40140f101c40000707040074080e1201600424007503858a401c00c4116500012070010403a001000160b8891030800b1100d4200b81000d8014ac01d485040b000050341400e08006600c81c130b00d0b4900781d54240c0c4901050006034030443d5242d03a400041404103004010340c4051442c0d1303524012088400599440c0105a401200311010350b0114440701d81003000c1c5a00003503843e92000310340003034501c0c41c40c00360300c101b082001240d0060070360105050761108 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 488611708 1250 488610458 488610461
    0x60102120720030607090911040308030708040c030f082a07120501090b010e0714120a0b0d06050a020a03060e040b0f041506080c0109140112022b0507030c0809060a0f 73
    0x15401024051301d030640303000c0e403002d4a0080648a100c00a9290880300d20010111f40151026658003002c120700d0f41c0c9030110100c071242800341c02605c40b0b040141c0c0001c000b0318040c926055561141824589401c900c19a0011448000e0100300d0380078452482d040343c120000c2500c405484500d429a802c1160b1410312500400075080024407503c0c480c0c00110702014200c42451003460143d69001c8910302c103001d0009030740030b071220180e040084d10380440d20358070031030b00201d41255000c0d040041400351511072905880040c1d4044d9020340d80000c420501980c54000c60000d00141090b6500e0b0341040e43c0e440044a0006040042c1002100003003400c0019a07044803044460f014401e022031500c440300141c0b00e9126040d4640815141315000801d09049008040020816143d1480406024507681d01a44c0000c61103102841121b250014003000d80a650b81c0160151000040c1031a00c00405000c4408204110041c40311040c100000380c000045c00d19808a114032001c500003075009100ac0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 488612958 1250 488611708 488611763
    0x4020d0f0203130c08030406020601050f04020702031903110102090112020a020a0c03030509030129040c050d06180c0e0603070e18090d03050601030e070b0f0d0e150601021207 77
    0x8140034000014450045201c14060f0b210754021120942c0b02c5a03611400c4e607803449640310701000368000500402c07007498000480c2502a80207030001d031500301c499002078100100c5040701001c0030a507144282c14554007036a01c0c043d00074503e00840c540a505800a00108600c2e4005460030f038000891002c2d0390300c280300385403246900481e402400d80d10780c80c000e081c503048000b00768000d43c070b042e801c55030403140c401e60100c3d4151444445544403200000b48806400d01c818010141b01e02000708401c0d681c40d601c00c40300108540fa9010612201103100300060300c601c000014100700b03071040d41c28080d540f40c078102c0741c0103001404d102040c0701d2014049407003c002c4045080104030f100080210130f2102041226142c4043e0354100b1503a40c820006400b02c4e14806540d0045034041081440329407180001401b2a84160810b1803d10600085034010b40314280031614264015030780805e8450804962a0382006007400035159054500302c60f80c20a01507424040d0284600c041500c1100c501d400030308 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 488614208 1250 488612958 488612981
    0x902120105131104090b01060f11070b0a11010203090d080a06050301020f0a0215010b0f0f090a121203140f130b040b09210417160312080a0203060a0504020d 69
    0x911461400d0608080c032000c1c60b96040ea120b0034101c504031500e14043c0b02d01042e29500c1100d80d94607908040d4115030b1000940007a009006031440982c0d40f089080240d500203007040a1019660070b4003103070052000c03a1510a9a0151703005000b441100000841c4a81c402070f010302d00040766603034010550b4050042c0c1c0e48090780551002441d1506884120700034003c0b00303025003c880d140400038042d2400076109200c2c24006d60014002e2540c221241d0b0008c01c0c0c1c000b0707a1360400b41801c510500003042c05089501000404000700c08200402101c1500c180e25815035090170048020078418060f0302c140b0040000c50805108800541a0710404801c0307040c1603000200110940b034030345020380d032001d000c0d51111024400c8511040600750302070000703184280d101590905003460000305005000201090804a00500843c12031000c1d901c2c4400f0003c1d409454450342c54010468040e00b003400141118400f14010800c109280d2a5540c2110450b68251001640d0b0354200d04040c0c020103c08030070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 488615458 1250 488614208 488614211
    0x51c020f12010e040f0206090a1d0901060f060c02010e0a080a140111040303051902120f03160801051f0e0a08100e01090b160926070602030a050d09021201 68
    0x19030500d80640005015014a1480000c603541d03203441e10070700d810030704480c010006010701c42c0b54070050610001500e80c0c0c1c98060601d109250b101c203020f02180d0460851008985c080c2010008058800d00a080c02072a103200e80c02c1105041440041c020440040041d0600c01020301140d210b17154200300348003c000003c10f0358011340b110301c0d020308051b00b034020350300b002d41c20122f04140b59447c150882d01100d6141c0c40311840c08507081140240d07007070a84d030b641007075000780000c160102001c180100340389130b201010a40d59280070000100341203d0040c0702420042000014402911952a80c100004440f500e5885401d0750301c20440d540c1d0010480140c010440100010711810b000078460603440e401c000078410805036440050032503440072400340c160074110b400704400600c0100248242d007102c0c9007495455440380380d000180c48024810f01a0707010058061610100f00f402000054003840c80034524002c14600001c290f40501c81360380b242d4a6482007400215640d0b03015094031450030a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 488616708 1250 488615458 488615467
    0x2040b030a11130207020928023c0a030f110705060403110601120b1b04090e01060e25020102070204020f030612060106080c1303061109130204030503270a0801050610050c0d051c02 79
    0x220307018110008960082e00c0700d40350080742e4a0b0008810380000584040e00e2b03442c18800c190b80c0840c003400703200c000000d4440c2e07035141590704143d41b80000d00c00305004e40010101401d10303280003440813a907400c901405c0c0d0418001807040c840c4010443c4681c40e04101c140c000c40d150101100116036840303000400102d0000750014001c2116040f442d490783c030f2000204822560341c2c00d00302e0f2090048912540b0351465078850901c0c0b4140c41903013045590548001801c040c9158041000c90340150031201d00d82d03001000300900c40c9420060007000f90f180c0c1d4083c02c155454907074058150803014181400004002c83c0c60702041c0c00459002e00210b403c45014040b0074405815020303541d110301d42d40c41c05071503074200004203c0440c0c000c4604480d400701c020b510300350035585441d00c0790001d20a10711f17880806204948403552651b0909015080d50000019117081200c10004c41c4021a061641401001d121656004030301054602c0c8546060600643d01e000c0d013a8280041d042284958090b14070214 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 488617958 1250 488616708 488616727
    0xc010e0a0c08010e06060904170705060f01030b01060c0b0604020903010e150f090a08090d0c05040504051c0c0f060b030703020a091a06160f02040b030a1113020702092802 75
    0x4407981141c40802c0200141c0c803090548907120101203c0c00758001d80c0e014007140c000740c00c40504202d00f40d21009042d0070301c44140c0d5220305054042d54100011001c0d0001413050114603003d07503004024500b440344250145544032040b003140204064801c55012444800d687c800390454150b982035481076464a403a00d20f954110780354150b841079000c80c000c00026420500c000740031b808080e003007a82141003504c080104100c17080090030403140c0c07412840000403692101d02856000764887d001400844011410385004100716011240401c041450701c1c60120b20300e0710b43c030041c40d07401800203e02c20449030082443c092081c0e100a4000c0c218500000e0034800742c2d0b0251401940b082c09810500045c20100045130241c10320400d1207400003c0b001c000550741d000c04002903032000d0404103401c00b003400040c6c145240b640d4141c41c0442d06a4040480740b030030b160010540b00d0080e2046082038002c2e00810100e1400901240c9410303080180b2040c003508030003440c0c00748110210155550440c55 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 488619208 1250 488617958 488617973
    0x5060c030c0c040b130f060909141c0e060d06030b0c0403050c0a0e010b0c0c03030406030b01020111070f080a14180f0301140c130510050703120b01020c01050c010e0a 73
    0x2402460703030500032070340e4403039582c9054040e0740c00b6020001c20f160328040a40005100504401c00f15040342681c5040c0019000000d0280042c0507000342e540d2184052086066818000b814000300301d07030b1100588114045401294140094100b40c42440c1c5844800341c1c4a80180540c1d0006400c4c2102e28040200c1c1101c100010403d5a00c160280e5030039810700c40c00d1008092180c01101c00c00508178006222500d11203020b41100c50441044510040800c004a401c692068020000080e26001a543c00d542c09010700f580712904e481c000d07480d100440c1c980c4200f030342d11b00c40000c0811400180207004140b245491408602c03850001303550702c3c0d41401c404100b401060000600640c1244805540d910341031080e6140c006108880c2c0d01c0c95982c9182c5400c0b90341c0f0490484480e682140c50218154a0b06401024081c00c0d9442d5550ba940081c207003e001c202132070b00342400e0281025640780842e640494000705504082c01c10700d8642c0496010513001d4170610040700500c0c4030713082164043c017810 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 488620458 1250 488619208 488619217
    0xd0f270510020c030312041a10140a0510080717090709060503150f0c0f0304060213230f0d1a01050112060305071509171c051602010c0c05060c03 64
    0x11507000c8141050600c0c141e80301c1007038039075041d4103030018440815007060001d01c1a80c002d101e41113400c1c81164100340142c140e04141e4440590050784401482018508810344c440e420702114088406440d02001405a20403020003030200300e5480301054009009444007001074280d0380a542c6507141500c46076603a0541c078401c99501c04d0820340002482d040100750f03105070180d1200415000d684100004540c0c01000d0550122000100443c00e400e6030762502550056200c5c0c84090303075a442c0440030303450203111030308100804000d04000c2c05800e000c000300903070506019106800902e40107400290f0071040c41e08040d1581c03044060540241c0c0381d400002c0d041c1c0340240c0b82c4150401d082c2e5000811100c4501000f815640b101c40b06000b005282810356900c00c6c1c8030302d0403060842d01c9481040c200d0564440f480c4056100f40b44400d00c1032001801100c11078040c0c64824200038194400100c5512240d401074140080200000140250b0188000c0a0100509130940c3c4075180d51010307540c4da11 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 488621708 1250 488620458 488620469
    0xd022802070f0b220911090a0b0c030a0e0123030f151e150a09030c060c0b060904021f0504090e01060e070807020312040305190906020d0f27 62
    0x181e00000c20280c490300880c80541e40154400c0e4140040d150400307040c580c14043c1ea10b6000c000c0c920001c0c900d0041c1c0140300303904a014490301e807540b803d2024486107900c07540000d0101c4a06004031121030354004191040310b4440d203081000340744070200503600102281c0700342d08030704000f080804606403031030015402000010721440180d80c501e211100f040071111031159011013858500d4104650b407000c94085140000c0411011600084a00e8210b90102d507031440441d039240300c10020703c024a4594001044603040c628004000c5585002c4a200014102481041050041002d6440f466458406206d20700e42105400003603080242203600070340b00701c0c04c6550130702c500c41003991010f014080032904254030780819034646503000c2d83c00c508000d101508500c014000100e0040900b0f0440d80643c0c040d840b00e035528801005440c110280e041e4045d42489040706003046595070009482107807050030701d0103d42c41c044041c2c00700c0d0807030004202100604041c22078a5492005041c10758100c88 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 488622958 1250 488621708 488621713
    0x603070c0f080304050c1f0302130b1911010b06030103061805010903020606031e0c06030408070804060509090a0b0d110a0e010b04210807030c0212010203090a0605010603140402060d022802 83
    0x80c2c90100001c01200d10b00c01c247e5103030740000283c28140250050040102440b07281011503403a100d056199820020b04d0300c170f120500c422400c60b10b0760410000715154860000a000c3c04d00ca45022802d548010303c00100f015030340d03038a030400f62201902c90380101a0b110009014420302d90400a40d500340c10364509201780602c06111145440d00c0243d841c00b08819405030219010103010400b0903003008000fa160f180c0f003045510005100701d4010405051103843c3c8503219420b6a0038404ca10304001c0c4000c448920b001d40817250350303462144680744550301c080740c0d1003081c90000104428451640c00750710203507001000860220407003030290060311441488400114a80c0c4502c1d014104030010252400c1307001c100c400c0200e071160184002482c006440f0f500d0480f0900c90403400ca07401199020300a4001403c0305e0204081801094014011803500344042101002582c503007180c081c0009206a40000300f04020408507016118036214210b0040707080c40102c1d0344c624896861b002a0030060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 488624208 1250 488622958 488622973
    0x903081314010906140f091002060406050105090c03060d02040b0307091b0c1205090f09070815090105011209020f090906010e0115080a0c02070302130b03070518060603070c0f08030405 81
    0x2540720740f11507401c4540725a2039480504401400c24810303440000d0f480d507001e40400400606456911b500107445415a00400c1c440c80c150415604603401030300144d10811290041c07250f4002810182c92b0810011110890007820b0382c800038000300f50616403070b074060180b0300c3c00080d240d8813580100300c00e013070041d00080f18000700f138400c6a00b00c003080c100401e0f1b14201c04010500724400c0d00500604d207400703001c58010100c1080010400c210469029002411003810091a4858280d40e44038419080d00e603410070354102000a0007040d101790501d25519940d1140c0001d66440e400342203030307958000c0c04030111410609415a190782090040e010080e540800005942e0541001032032501c00c0d60365113001903201d490b5443c02031301d040c040d0081144078030311000c0056950118480b207011080c0300d0000c0d810516074103040c240001984040e101e00c0b81e1001c0004606504d42ca0194013601c04c170f50540d82c0b903a0b007000c00d031380e00ea0210750081c0049401102050422101100550107203008800310b1310300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 488625458 1250 488624208 488624249
    0x50a0c140f0105090114160c0501061401021c0504051c020603090a12091211060717041e0e070e030a06140703050a0c21061205010903030c14090d0309030813 69
    0x7038a04440e048442600030400169000e4107d0403030400b00482403410344002010381e01c4c0c2d0b5094489580105103805110807000841b507030100a0790108144c842500785850400d090b003e041da009503c201c600406c41c0340902088803080580910001d64001c023120f40300d00785040e50594510014001302d0b011101d003003201600900800c40c00040b2086000c03400c610042c40d0b560041e9095144e404180c021905020b510005441003065000c0c000b80e4849164459160040440720111185c803644202d801c12181448a810590071303559001c111070924895880d05140800e1034280701c081c002c2c0c07101e07150035849000c0c008401c0304d05000340159501070001d03031680e140d000115802440020045410381c034074503004900843e0340c03414002000d000020501c0c0c0c0c03081001502e0344003840480301070350350302a20010103816109203040000d642c40d11f100d21044010030b01104d07109400700786100341c1c4040601000c040c403400881018691200c44103403a000f9400c000c5004100d94010300c01031541b41d0450544 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 488626708 1250 488625458 488625461
    0x14010f06031506050d0c090b01050903010905010e0d170c0f130b04030201091d041106040f03240615030b0604050d21140715111209120a050406050a0c140f01050901 72
    0xc01580004581b2017a0303140065410043c4111450113042c04428001e02031590340030b12030354211600038000812180d501c03c001c0e03820030b886c031404202070016403480301e190203410040c095403040f00740301c44a580d0145410f0382a0310f03004004584500c4040c0050205014020368090012a4070070380380c2c003060580300c240070440c0315880c40403c0f001103450320014020800c0340d0f031510340014024021074600b03600c9a038412442915500b040e68100303100c0301c1c01c6200f007455881c0c180e55505804010003000d810050038181411030000d8500405440d0420503003103560f400116002444d0040405d440706600d882c2480c0004400300e0111010b503000c0013009082801990050180d0304681101882d100c040e83d038030007036114554803e501207aa00c00000e011030710719000810b15100c072150100711614205041c035180650740c0d081c840d00c5810a112029440da0808180c5058030602d0034030744c3e250030510a04035110a141c64014001c81c16034042d0054051700410a0090400c802c1e00034085992044070390b90 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 488627958 1250 488626708 488626729
    0x80412050f10060e13060e010e010614040b0a0e070537020d0909090c080601061106090d0203041214101a09010f030204091a10091b080414010f0603150605 68
    0x4440c0840c200005030b000000c0c174082100c480c42003100140c00d404211660f0300712a501d40f403000480c0c1d9209000c1c001c5c070140c92608030810000311428410300011402181c480d0601b44a520508000c280100d220b85000c0c809072220481c0914580d040b00326007460020303001d00041c440d20358800c030460035001020300c0850303034800340c21580d251541b001746070080d04801000f03803050954003480907000124900030b080c02540d00922a1b07607101001c0300001d9403214103105018002c2e01e09a4030083c2e03600c04943d0044180d408444180300c01e001059641e040030404c0401200d1107140074004c449007141480417590150307202d10980451142112030010900c1220442805072071150060300e07508000610b802d4100303490061199481104034420507001c2c0400c0350007604c2c41d2420703c050807070901440d0503501c142c01e60085503008961054100d900040d252409c0500701030100b04850042c406c07445001d40209000c1d05100720b04001c11940c07402c100240c89000c507480c4032110708120700016245400320440c23 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 488629208 1250 488627958 488627969
    0xa05061002031201170703050105010b07020a0510021b061b0a052e1a0d150507090302011e0e060c150105010809030d1e1407080115050a0309080412050f1006 69
    0x2000d1503403e01260b00036450417580302460328402c42d00003000248003030042d18020040c0c8a006512050148100803000d00705e40c00c024018203800d03030b0216080c1d0b8001400b0021560412410b0b071503a010001182c50341c840c8410100c0e182d25044081007510310b0000d407003140305015001b520082c260100d1785200c00c0000c0d10304165440c03c0340300300341d4401d407081d407003c504a001914140407a08504002c10203007200320100b0f17240c078081d80d61254030f452214040c0c00d40c85006403402c01c03452810365001034170701071407140c00315101905002014030035400361441502440c002021140c5804205c1d5149681c0d10b81c602d228102210440000241d40d4080c0d09500d00413550792001c0d60500140d101b01070010058031040c1e00418820000b5154485514031901c0444031010700007020034036110001802114042e400049180c03145031a600710598442c050f68603100840c079002c100c41801d8105202e05001d40d401c03010242001c18542c20802100185488070340020500362030125610b10b0502048440c41d1054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 488630458 1250 488629208 488629237
    0xb0609091606050f0c0d0f030b0102031903021605100902130b090c0c07051507110f09011a070501020c0102030105030708070503100e03130f081902030c060f120a0506100203 76
    0x2e001c00c034014406800701c1d41c12403a0b96400c101c542920340b450f000b400c0c0703074140100c3c180c0e071031003c800c0f0340c540a110340100080c0000c610b0003400600510071021100028801c155000c10703101c42c4500d03880141c00505802408070f900201e104000c100c028804140102d1244d5044a00d034412080540108152100c00418010f456640c8070103110142c2c1c03003090b0140c500d000d6014042880d43d100305042c4020242c404159455800c1d9140000d580d078800845d00784a0000c007945e100c11030303641c00025410741d81000c0881b4403144503030110803a2070003010b000400340e50001c01c00b01c0c0031110550180d8103d44d000c404031460960307142e00d2641c45082a000e460342641210b505205070216980124080170304c4001124a04000b804000d145480320303802c41586008043c0c000c00c60f244e020414102c580d403c0c0707104410707036090650005e641d03100c42420b241e01500c0d01080c060f03450011340c02503820f9454540035401e036600d008507041c0000c7c10308440c458460011012130b0a59148000241c503070200c441e192 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 488631708 1250 488630458 488630503
    0x515040b0a1509030f03020a0201030c0302160303020a0e0402161b08030d0207020a120302010f061e18060b0706050108070608060f0f03030408070303050d06080c09040611160b060909 80
    0x76035000c01c1208141902c144401c81c03a00000144000400c8100140240d001c0c150003100b5100060503201c1400c44002050b00521084080c0c0190300380800c06250302d03003001680e07496118019201880c81210045d0f116201240c100510601c0c441c1c40022248210303001d12102a0b41c0c24010000740c4103020744103030f942c014041d265405035103030300803c401c60009207107031840d030340e00d62400103558041c20040340181d440c0c4a00041c030000314002c41c00030b40342d55289030b01117402d581d1509017042c206d48180400031109d07400c0b6012031011a4048005043c0e139080c49139a0701070a0400c4405003100b0311503440d2a224600c0c7c0015080e01c04c120481c0160401414405080c030000c0400644003113900c4a00d17814001004002103150041210758001d5200e51503042d110a00c2c0341440d01240c0040d444505a504460000b0a040e0b403148407035680590720100000c0e210215100d24006401a240c2545403810f8005500c400e03c40b054030000e201e079104440008695441140607510f941080c450201c1100400d071 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 488632958 1250 488631708 488631719
    0x100203161b0803041218050105121e0702030a0806040504031b06061806060314010b0a08070e0406060504080625050a0203070b0406061d010e01061b150515040b0a 71
    0x260004251508075150032051505500c0d000003a81c8141c40845251668000a18005070800ca00c5084800c0c030341100d13107245183c000081c20f148281c488002c403e991000000708107041c50040142d40c1c00d0700714410000742c50301500c040d5596010125031320125140c40001000da141c14001c0714811507156480480380105400121030004a4620848586032248400302d100e020901e08107401c10f48902c00031900924281c2d0240c116002c80400401b900c900100610030743c0139010440341c50750818588103103d0342d500c034000c4510100d041c64007588241000c000003551984000944190f640110660704280c43d005a04000c2c1190180e0b03600034910326a52120380d2500410150100d9507880c0141c0340752140a51710403c003000201c6042752a2945c8400c1030000c10a41e0488800804c80c1588201c510b505200042c0450f0703005120b01010020540b411a00300c451a54000307102e50351008500d00707511b4492403003501503c3e0031101040c080c0000e0700345190514050296024510b00030b044030705480d00b8030b03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 488634208 1250 488632958 488632967
    0x7021203060d030c110d060f181e020118030510060503010e0703060510090f02030901050c0c062d0906010e0c071a130f0b04110103231801060905060310020316 70
    0xe0b00242c444240e03101a02e006030300d841a0b0700c034070644a6240000c0300007142c240f000480c9e000703d1009812034101066800040c8086a0a8407108054019464200e1461004030781680c00c140c80c003c0380d088040c0001003044400244e2159800706400e00340700480d1541c06142c06c031180508501c01d680c1c81000200007181942d0f00054001e403c107421141905c1e00c81d4004016030304084007800e0031550000c1005141002845800d4100d030800007070302d28000d000f60f81d03140e5640e0b010b40b58080100805030311503608807904c074000c1141d21711580007403020310700003480603181c80f001d100d0340c4803c8a1682c001280100303d032040f92280b540c0144108100107000f012030740b0300f000080034108043c03070f240000004250b01c60f01e102080c910071003184049181ca441d20341b40002006050505040c1000030b0390341941e8170030021601035a405859040c1c01d6aa4002200034080c1c003529600f103552900c180441c00c20241c3c1c01c10341c441c00003a030840343c8194000111600b2407000300c0d5059520b800f56203a036004d07288036 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 488635458 1250 488634208 488634227
    0xc0604031b02060d11041a070b0f010e0117010603060e0c010306060e0d140109080c3703080a15080a0b090d170a0603170406080f040c1707080703080307021203060d03 73
    0x2112201c50410b500c07100206440c82d1f5007905104120000300e040c00c104040700380101da003c03090703010340d000700e5240c5449008000303410b002e60741c1580344d03442c041e03010f090007503002400550b00b00307006101514001a5840c2c03164995004140000e0600c6c03008607003940101c201e0741364a1b8015240d00e064109949030010000702d02d1a00302d041d5500e0b8540d88011136081e80280c0b01d04940c00d8003030500a03036045c40e0642010001c03802404600000c0d005400903600f10040100e5503901030030a001c1d15a20340070306100418440140000082800102050552001801c070f50380f01c0c4580344000c0c040e101d90707905682d02c1c0405090040020394120400000e041d10003010341e0064010040030680079220740d11b1803aa101c5030b41c0c40740320f030302c0c80420100b01c07143c1d00000c1c0c19001521005c030114281803e0715000a10f0484d801a140b0701c03504c2111010906504101441c01044100c041d02c045580320f18242680d40c2c01035482500611520314400340910001046a0085000030b01380900341031075940c1565401c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 488636708 1250 488635458 488635481
    0x90d020102011d072d12050114091f05040c030f0c08030c030a0305070e031b010e1804020f090f1f09020310080f0c280b0c0604031b02060d 61
    0x103c0d00448090401c03400c4a03501240c140e00c0280c1092814040c0c60006101050350118000c42142c040c95901003511a4910a07620602c1070380e901481d843c00c050f4050701d2800c0541000032a010200840d00001181101c1c0203000c140a01d80c00d2080361036007206413003050b03402804519640d0700c10400240c0140b100d030a0701b4030600501320a60790364009a42150402104100c5030f81001032081801c41d41403103547e84c04960f0b0700300b18141000c8a40825550b03010b07800c089012a0709100b280703030a603008907010149048000c003482d0100c010448424109981078604030b004000c0c41c102c62030145045040c003032040460440401c030b80e9882101850725860951500fa50071050410042070131003040c0021841100302e40c2005030004d103440d440300d262110800100485411111018081d9981c40c401e81c0c03c445410521003400b1000801e0070b460141d041d900c1040c441000181c242c04620340030440034816402030301c0d8110700c265070149001c000c0e501004c00941c000e00c00c0008110300c19056020000c0800d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 488637958 1250 488636708 488636711
    0xb04050a05040f0b0603130204060b12150f06131a040b1603051b1606140d0207020a0503011b080c070309050103090f060c0c021e0303030c0f0708070303230705090d02010201 76
    0x81a14003c11502d1b40161221513443e0075400c00b140960405000e104010140c201c03613103241105401101540c428007030081190741025580680c070319580c0c0d049803003c400c40141007940da03018215459440010a100da50104100901c500c0150f494803801d9904070307100c4001c0d0301c1c98410794420291451408000440c103000c420300040230381c50105614808044081002081d01d04280c2640c1c0d2182c80c183d40c403800402440d40030150403aa00e01060343e404940695000d070321b484103407000500301c849540000da015032034821900d000c000c1c0c18901c181d880c042c58448201607114101680040c1c071901e58090301184a02d6810001948a50710044003940200740620300d0ba004c680d501402c0c0c0342c44c96002c01c0024001c1180c40c040d441c140100d000300349091030f4410850010302020944900008003010001d20010500c1c84c1c200640101721040300717920001d1159102c0e018a80038009042c24261500b401404200c1c1d40ca0702c0c0480e002a5000e11404d40b01d441c20103180800b003004903007614101700e0455 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 488639208 1250 488637958 488637971
    0xc0c06030c0f0f041d06010203041401021002030907150504080316030318051f05060f191e09060902030601020601031b080303010e072a060c11060709050103060b04050a05040f 77
    0x402c400c1d00a084000008451641e90342d180041c07800855200b02581403072090400c0501045030f80000485003100c280e619034001075101040140e00301038401e009604110700020800203507603408184c00056030141001680c3d0b580d1410341c110b801d80110301920781701c2c0c0d00070011030100450b07440f0110b42c042d1003440c1c007140e0080c403242c00c080b0f040d0070200101c42c280c0c844516400351190004451581e0120844204074901c3d110001904003800f0080751400303141c5680810b50f4402c910078603000070340030010380c13024104400104070854095512400380000d00e03280002c5103060890003203e005c1d0344140e00038041781c1d00b5521164000550290000140040320f900000c42120a20180d0300030652100804014070344190003504006070380a61280780342d802e030030340314a0800c0c04142d8402180c001c8400184c035a4100e00c00e80d207043c00142104014411c00041100e410707400040d58040d0741003a6020310000380e071076410034024000e900036a9888012a00c05002074107041d030090800745403069001c5441c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 488640458 1250 488639208 488639227
    0x12080d050c250201270902070203010213080c03060a060b090424180e062202030106050a030f0c060e0307180f02072003031c02030a0605030718110c0c06030c 69
    0xc0401c59074142c0ea01900307440b04805540c1c102c0e50144443e1601d151300790035440c54500070000300806020708541c0b0b80d40400c80f541076440950507950154202d00d80701000380d031503101036595641c211940074070034850500001c10312b09140c018a02200c1c075a43c40d19080041000400002e003000c1443d01d1814a80d030303200c440d211070403409a24010142460740c030003002000b410803002d86c0c61201001c003441c0d00080c24404504049136203010004110207a40c0e00c6096644000b9024002540c0310a90200d0f911a012045c07042e903003000741203548241f102840003661003a068481044840005074560072038042040904072110000300c0070001e003d400203409003000c0912003280c000090a980c860030b05544c0b00c4185d0012400b40741c03400c50440045007081c04108080105201811620403200d401202140b00203400d07400003009800000c080e6103c80e07450303066011480718401c034082c41042c2040300480c1e0152004045078002695900034004504944007401080c1d03101034041c00407950200914040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 488641708 1250 488640458 488640487
    0x20d0b0106050409050a02070804180e0102190f0207080606010c0201050d0e0a0515010b09060c0a060e0d020d031506260703021801030506130b1c05010605010912080d050c 75
    0xc0d1080b03850342522503003001d08040498100a000a42c913034410040c0401003031920341554219030302001e1110b4540b800030f40141c09000002c840103c5036001050041c031a036420380824141880c0c503903565906c08a00801240c0d02c10003807055514641218008c01c0455124a2080044a0060402038906031150b010305017240c8055482d503030f46401283d03000d41001400e0000c04080300c80350007214100d5044c070110241500c00e805070a449242e000032050121170041c025480259085001006140310300c0e03900c1516540c14102140050054080d00c0d16200d00a1003500324881810280110380c03420408103890213041a090011303e407001c0c10402c01010740401ca042c0c42203107642e0300076885002c2010803a0031400749655450505003040100310031a00c49124001a0b00603100010a161b542c54000c5081040700c80d216030700400c1c900b21000144141504120304541c401e0341d41c8045141d841180c00046607109000402d1500100403003079403110340e0f8002c1504030f10341181041c80c081c41c0c02980b04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 488642958 1250 488641708 488641711
    0x90c03070e19290f0304030903060504150501150203090d050304030c0b1c02250c0b0703030209090f1311150307031d010606090308070503130e15030d0813020d0b 71
    0x790b50b80c010401800305001410180981502c0c01c5802c4500d580c4800c0b0030702032401043d4802d120a00c1c00301c00102072500c03d04c0703040015070300304008004506040c00c0c08400c0c00301c2c00ca10b00700c5560401e0300000d21982d00100481c0c0724000380c2e0203103040c10001c0c020803003508010041503440303103c00d10000c00800c40d280d1094009185079080355036903800c00c240d00102100450000e0803080d1061101c2d5418290380054105160b92821181c80320710f5452818106035000c68102020444000c07039600c0805415a0052804803400c82c1e080c801075071001c09002c00e00c001120b50840c50300030740c1c21040000e03186003508001001c0080140d4851444d15000e03da036500101c071401c3c00262100151040c85c034200304180052210500203110490070f00c072000c1e025000500c00241040340002e0b801c400d001040c429182054040650740041a658914442000c1c409840041818101c0300c084101480c002914121128007900c44a146940e20016042500f600c000705a03000b202c445c058a001412941482c2e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 488644208 1250 488642958 488642989
    0xb0406140d0e062d0711150a1a0307030f0b0a020d0524010809070519080d020c09091614040b0405071d01020304080a1b090606020714040b090c03070e 66
    0x3c00c614034100c1d000000b0071100c21080d0300740780d00c04111143d8030402480c0755079200c3c0c032030709000e0481c90744407240034900103500510b0f1915900c281c0911a59629036000b502614041500c509462040402055190030031448000c201d80e0030b0b10420000103c0d039529142d4004840705005043c503280c0c00021040d150100e40901d0100e00c0d01c8421141403000d8200000312541c00e1a2010040c0b40140600e903a13044c19029042c440c18880c8010800c02c4440c82c42140541151030179141c0e074600d58500030755151420201e241c42001020001089914000381c1148000c003008881c3c1070b2149000e039461340c1e810175001890f4200d516078a6035002038a860103240c0c01138290346d842080400e03181e022545401c01d8811071a0440d0000c210412000c1000a090b80405802c40c0c19140302c1d00c3c02c020040c02c4010144c0c48418001d0400c040054803079008034030001224005821101d8103d07401007044212500c070105603a0114581000c2078500004130702030b650165103400e14050200f8000c1c001a003960005120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 488645458 1250 488644208 488644213
    0x30f070501060e090f150c04090614030d020d05040909060e06070e030c010c0b0402270a0f0f020304031b030318050304050a050316090c02070e01060206090c01090b0406140d0e 77
    0x4022000405036042c0e0f11894410240c0601780950805544404580c1c0000528282182c00300b001d6039004021600107081100d010060b140d0303582200c600113070102400314443e0044600c40c100490001c9116010200c0d15500d0b2450142401e22410003070007086402d5555039922020390103101400c0080d94010384c62511039516046a4500f09850300b030200c45428100441200c003d000101d2480c2915040b40d03045401c41c00414205110f08903001907080c58480c030b00340d628240a51a1820342c007550340714513070030710130b100d2000a0602c04003644400d4038020f00203070355043c84600f407085694a40410724460b03c0c01152035103035100d940080401d4080156404d400021b420407452030240f460303100a0400b50064003a00500d1100701e1074291840c850940029158511f8101d0705100307000308005400c80380c12800d07495031199402540c03440100ca0440503071003615541c0d14103600881c0c1c90012202c0602c1403510305070801100f00e451051030203000c12500810700c01511000524000c101e89040034400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 488646708 1250 488645458 488645471
    0xd082101060509100930121d01030603120f090504051e090d051b0c090c0c0c090c03070e030f190203190203120714010903020d141317030f070501 64
    0x2c1101c1100400009010b1040c174000412201212601d4424008050240e14052000c0e40381580784540b40c5290041202e20402441100a90004080891450001c4125081c0000781005500710b400c81d00016003503081c43c115140d03403907100762003ea001e0b14583c0317454030b9a990f46101107800c0da00182c42e07640b018010706a0321044010f01a850550244420b0700030204010340e054080c0c008c2c414084100000401c4900084081c00200a103502c4a43c0140036199145812054035555802088502d002d44c004c0c2c6410721202d14290f140c16015400700c0b0741c050701e15220002e064803d01c180301c00703030f40d014050201e0390301c1100301c04d100c0c900350205d44103041800c40240303204041c28910782c0380004080080310500a0003688002614034108011040302d160b481c009802c180903120840c0001c0c10709907013803941c000101a40402c00081c2c5a10a0322600040c0103142d40c4c42c0e8a601418510100f1780c40307159010407990101c100d20302030f0350b80400c094030b00d0300316142c3d071019103a07000c1300061f292070303441e5030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 488647958 1250 488646708 488646727
    0x50f1c0c20011104171203040305030f06030a05100e0f0703050d0f08090d05030601090b0c070f120302060402040504030c0b01150f0e010507030f110a0506040203010c0305060d0821010605 82
    0x1c92011448031800d000300030403000c111004465000d00d01031140d01c8400c40310708050359007040010b0407601d05940c0d0240e48915141c90024a5a03104070382684103200740d04081b8500e0704001500440007940030340641181c031314a81e100d0005044503070030b14009129a50005c3c180c0384003846002c020f9406640a0051181d04520203800150190103003002c004025041041001c00800c02c40e00380006454541d503252144001210082c00307039001144010030000380f1800409001034900100c5201c034503580250b80d9a840c441042407101170014001da081070001400501c0c1503444581d0051203420602d1448041d0b84542655038001d82258041c21038200342c2103810b60700035115003a8090f0500c1c00d114000c45000008109005810000782801034110084058902580c004031044200b00110745100159060240d0b0743c1a0a032000e902952070300c59880480d40c464000d403481520301a004e5990300b04a55074480556000c107181c1c42308296482c4201480304241c0300c08900811164bd10940c44d01c9014 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 488649208 1250 488647958 488647997
    0x30d0e03070219050a1502031c0c02070602010209010e0405041416030506060306071e0201110a0f031503112404031202060a090c1e1a0301060816050f1c0c 68
    0x300c0e900d044143c090401c0081e980c0d258400310640f40d07501d041c03011503109030358180d1550081c401d80700708803105840d00600c0b2489030b82c03004462a049600310396503641d45180130381c200d104000c50140000c6803400c510b000c03801c11780c0006130800c2c0301e9448a07424101026000d401c2981020340b00d4034170030704882c1c00c10500c1010030032560000411005007415051120b40581600101d07d02e869201c8000313425000b56600030360000c6c80724010070304810743c0c403204800c004141003203406940c2e001c245000b0b15070b80c0c403490b01981071096a6120700d00012010402c0100028807200c10700c80900c1404607902d4400c90440ba90142c0f0040d4424001001440e01001002e070030820b00610100c51103152903d03007804959030402e03031000c40e5a0b082c03403621901c4041c0344c40c10a2482c130750881400b50a038031103220380c8407100900540c1200e00a98407401079440d4418003000350009601c500e400107406000d04100751107204020060042c0441102c1a410440c081c0c4d101680c203020314a00106940941c1c031007000055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 488650458 1250 488649208 488649229
    0x203091006120b04020d0203120a020f0a02180c0d06120b0901020c06150609091905093c060709090f0204120f0309030503162609040905030d0e030702 66
    0x300003092286608100110305003080d50400070341010a5400440e09648500c03070903442064010341039441030000d080507c180d03075100340d4030380300103100350b10018510309804a2220070159005040f014481c928802c01c0c603144001810710380d1954402c110301d1003807520901c03401d001440c10400503801a00309040c101151900117210301e8203a4010041c081c842c40707010610719484400104003d0260003207402294060080c00034858000385100203100402c152a003035940541d04a900901550b9500081d0b9504e8900300b40e00119030b550000d2502c2071035100300a45101c00742c242040311100441000c111440c241c000d032800c002041580c002401101803a00a0256006521100b50300c2c0a01e0814650240b40d1008805098105d1091062040500c9907500300002c60701700049030f48400003c4140c60389082c202c181140e0400c8101454910031441000312103140442d48040d07400c001d802418800a0201300c80c0440716808208200c00d10100b00348140310310803181000070343e1071704410301c18080a22007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 488651708 1250 488650458 488650483
    0x131517060601082a0d1a0f060a0906080a0f110d060b0f0f030c0c07060f020708070e0a0902030c150702041805120d02190806031501081c0207050a09020309 68
    0x90400801014003c0030700d04013500b5040d02008032840c8130b65003512a2a01400700702482103802c4c9100303802108a07614241e045a0350403540303a500e0408400401c4141d00c00c100303c180c040384104904120460064000c540c0c032506a400108502c1c06a1107240b04440c1105028100598045101c045100315031140d040a0070505040f140b810001030980d213641d000f030581c081000a000000106a410b0740d8003501c00e90f4030b03a1803c1b40c2400351102c0c006001031140190560061140003c0010000310014010f41200c07001d070070f600100d0b04c3c2d101c1c0b460043d200641080c4d07018403c0b401c43c4115502c40c007001d00d0301514806100381d110fa01a1040000f9030304c8415842401e80442844000855000b20b90540203625145c1c00716541c62103032407414083e0246120060b0409000c644030f80002d038004216a105000c02c8081c0d800c2c1504a152200c2003030301c28081e84940ba4814035843c0301c16414802c00000141003401241c0072541d80d140094203481d8683c0180c414a034010061051084081100d40302091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 488652958 1250 488651708 488651717
    0x302100c111e04090602040906080d08070807050a0e01050c0d0f0f0201091109181603060e06130209070210050910060e0112030503060f27090d05030402131517060601 73
    0x404030000c024142c0181803407544035503618603d941c10096142e040358004c01d80d01c08144183c0342e80d840e103d5110192070a03094049154640090307005031007103950741e201d0f4003192640ca0034500c110b20704549400455510b103050000410000140c1d40c0c0405c4a8200800c1c2c50381c0d11481d09803090402024064103050000a582c1488001d10009010400740d1103080302c02d4030140d840c2c3d0b03035000040031658109a919051802454440442c0c44a940060300503a0300030302c000e00034100c03412500c036070f102c170111941208900c148601c3ca00518051030082d030480b485e0700c100d8280382d140d0046170341100e0b81594086102d611a034003c22405c00d0b00d0140100074001d0b04010441585801071105400024480007810404000005166903a07220304400c0d102101800410214103903c114162200c80901c02c40b003500e2020340013805040000849130298074441e51100d042d52165820711115075022210001461340b221041d06032040180c103041c004000e40c8401d180c00f1348803000d9444c01c00401401032810030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 488654208 1250 488652958 488652979
    0x1152c042925090b0f160c030f05010513021c11120f0f01050421030f0908070212010e0c09060628031a010503010626130c0806130b0703060302100c11 66
    0x12a11054907402c4045c45641d50f030b1a0500c0d80382203c200000c01d401003101c4c04500b400320030300c00d200d48613814030f03886980200156101c20483c400c105030300d1132000b580140414442e0066031601f10341e1007002841810284a05009800020520f036211500350809a0014007412002c004c00c20136000c3e138404a0008001c0d50406890b8034044d900c55591400c0c9030300a00f61141100c41c421307030210b502201652010403500e519840c0185a9034008001070b8841c43c45104803840ba400306100d1074102c000700030000d01c60a031044040c80440361004081c2548150184069680c1848504c10414101280c4079a40c1d01c081103408040c080f2452405895940203c808550b49103903003201c2143c0c150391240c14540d411107046010b440c0f4200a881032028400f40b10400e200702e210070b86600c80f030803610407124004000d03160301039540d07520001c940800510303804604400102c2c40c080402504542e0328034012958944980100310a040450103400001e8400b040c0b08090100c0b5100b070000c40c5000302c0f02e18044 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 488655458 1250 488654208 488654219
    0x190b0f01050306010c030e0409060507200303070e0d150e1203010807030809130f0b01140c0a0209190c08041101020a0c0b0a020f01152c04292509 64
    0x2903000061120b130500401a2820080c14016020365a01c01c00c0113105200c1e020441ca0008040d002c280c4100011403071405500010000a003010714090750600c00039401d40e901c030901224142c0165102c1a040031140c22240081400e03001a100d201c8403403607004c560305034140080e81c9020400b40556003000d17418401030111260200c1c0280449403c41070540e21520554000798000090b910301038001490b10b080440b945415410500d5005000d030cc490001c12400301d10300d0b403140300b5070404041c00c2d00503000c148014680a1502034200c008901c00041c0411100d005004030341d0003180c2c03040416180000c101c01c0021800200c0d030171420a03c0a40148801a5680c40040300341c2c0c010b0340d113072040114034034150b64801c001004e0103640290007800040c2c101d4a070440c00446500421281030038650010101c0d01e104500500200d0712026219101d070f481d0349641c403034600307420903040da054110139140701c17000c80503214140030f00e10307496055680d4020000303580404905807602c4005d210074507008015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 488656708 1250 488655458 488655467
    0x506070b010e04031b11090a0e071e0b0a050d2a0807180609080601080c01020d0507030311041d0a2c1903170105030a020a03031b0b190b0f01 62
    0x4494010102c01819107a614060769021580078800c1200040b84146100340076a00c8400f11103040705851140d01c0d5190102000d058806940c1c820340702d175112a00c00c00007200c900340b03100c00d41301c8a40301d0b0b03040440c0c481c1318201d81d6034001e20740a00020300200d06c02d00e07410014441c90101400170042c1205980c11aa02d2441c4064010741d40c000740200c100000304440d01410081c01002181d40440142d542c89410281c0002414040c070513161040030f002040010000a201a40c904144c00401108854000403180d49d03204040840415860398007a881f8121028040d1000c0e01810103c0c44030b54031800c000c4141884014100394400782440e04c8a12050201c2030905242c3e07400c407480642e0068010b881c103181c0300d030004d036035804142064805403d02da809881d24820001180351410940d980b03c0406542c4c0c0e103440d5010350301c0350035072004100003070003000c19201c040c00142111404501e981c4a404200c0800c0702d14001401c14110480c0130300c0010b11588400c9501210042e56217403481340002d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 488657958 1250 488656708 488656711
    0x31410090c0501030f0b090109020d11070c120615091b0327081b0d022505010c1a090c040605010305011809050f010f021801080f04030e040207080409020705070506070b 74
    0x41c181581d03030f51881710f0884150003207120041d000c0c102c1803070f80d6580e090300c00080d440210910b124920b1700c3c00d5203601c2d030140b030112100c8075002000b400d482424500e5440072034901c4071084070f0455036944410b40e9080e40c4e00c040c00041c491000c0000d1045020708020b901d0244090951080500e0141c0303080c01500d80d0b494165180d050400030040b54106803074811581c1c0305002d0203040f10800c0c0c002f024040b0100050700402c2c03d905030300342c40c21030b4032500d844080803282800c2212540322511052002e5445075540080d035030b028402600500c1128040341c00302541c280c0300070340c403604845c20b00001418540110002880286010000d41d80f41c03081110a0024002402d2141ca4903049501c00b0301c813080010b40c5070050a1070081103022140000d0000a40c4100120800c0110114010075150701400d4000e00c10120007000c02115655640d0442c0c4107001804c07403ea1181e0300384801c0300402e00c244044c0c80640441c910040c7d1f1502203040061820903181e110a1155404200b00000625940c0c20103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 488659208 1250 488657958 488657969
    0x8040b0906040c1401020c06040803210f0411040b100801030b0705040e130201112e050f0a050405070b210109060515030604020d090b0609060415210c031410090c 71
    0xc101c00504c041c0101d0030f1010140005034003141c0490046200403011005002c1d0041c81820f01000720303c1d2400141d80d80c078088525160107000e480c00640400d43c075141c111f91442005000107001d14402c000204100202441103000806040040c41000b40502e040b0f81c0200c22070402a04152816041c1000c2d10f070010b0039241c801d4002440d0380216402075004081080c400b1f8155001184101181074103000301c585040e4100740c01078568000407885108650240036515904255550f44a81041c0502400b902c11a914460342e203002400782c255402a203403e9070703843c84041c80c005003045480f84508041c0c00020b00146050002c0040782d43e40c1e071251010085540c016074503a07031884000740c000d024520003a220982042d0400040103842044644071f50b00c00c82d00303d13003d903c1d00740c18803080700c26000b00701c50160701913034051007462100102104800c0050090075003402460b501c03001425800e50080b600108021640743c5040c00602400d0706102200008101740322079501c55002420307452050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 488660458 1250 488659208 488659229
    0x7110a121704030b07021006050d081b0705060307030f050a0b1c03181206140c030117010221010302090c0703020709110702040c082202130e03120708040b0906040c 72
    0x100c415916905542c02103801050004a03441c004d40040d44598216002d84a40c5250407000304051400002c018007080e04034a1490600e80c0012405d506000181c048448a114400c0c00145076a03c00c4000d41c856031596801296008411030003105440c0082c1c8a240b406040100c84d407866190b80c1c6086017010818401e0221038a0241000e540351040f042d80c0450758170008130042180c003032019000443c00d03c1840100180c4070585503000f2403a04c19100688011810030040042000d0400301780003110016000600c0c2030041d0f00034410300079803400c20800c0c40343e0580041082d8075003840c2190b1f000c0741d08480c4a00d0002035582c001e48600080c041c000c10a42d640c0611110105194103580f011640500104844552400c1c09080c2000c01c50b2500d03d54141450002c2a0100384648001f400340c1c060710024070760346540306400c081d02e00744041318000d2000744000c89003a2903000aa40c0194469112840300381042e041000100d2401003421040d42d010368140400110f80104000880d14070454 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 488661708 1250 488660458 488660483
    0x30f060703050403050c191719031109091e25180503060703050406050a0c091a0f16023a050c041e0b100507030c02130504050307110a12 60
    0x10f096030103014421b001c0c031840c85080d064844848078440f9550b125401010030381100c0c51000000901803103221070815a100e00102d62060650180d0846080c850210300400d0800d01e203d404504003136000ca60300da8002d031041404100602140c02c01d140c01c120024594000300c0d00340c5002d000c05020351420f000400c13406c140d00b020210703c529403a03009004002e054500c0341c1401300300200a80700c141d5080c0c6401e403410000c5040e40019114501c030210b4581c07144c00c0341d245001c5011a0050324201c1600c15417200b00032000c00c91248400800c0c5202030705106001104450040c42903851101140c0c01c090240003a0140445a00c1c02001d92030918201d600c201849591400b5402d105103481000c1d041420040940040c2c3d20703062003100240c03401c0724104020f82c40541008100c0c2039000d04040891030030080e40000c01d10415400035070328005410138541c0c1810702c4000040382d1003280c0655a5420200b008000c11506040131100c4d000100c41910300181009461810042d1114005040c85503840c1e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 488662958 1250 488661708 488661713
    0x1a040b0f0315120607090e010513050a020f03011508010920070c031202010c02160e0f0907050d0b0423070b07020f06030a06170a080901200105010906060e030f0607030504 75
    0x101010340d8100c2c0680001d8680c00070000300c50b59070005032941004114a000c020440080480060381200c20080c800040708000549000007454050302c06000b06808101416034030b000e500041d8024103c00400a14045052400829906c0180c01600e6807a0a000c600840d101600c0d0920602d03400c5488074913074a000c40c2c50b002d04418280c8c1d01c0100009508086204a5a0190300960328110b130f0ba029031350700001d4407918440c0b09050f801280060b46240c2d01040f06102d070400d1700b9030b014190f402110100ca8075440020003e008a400031100d800928007080b080180403c81105040c8a40514402c0141009035980d11042c16010720707070a502010030000b080d960b50318001c0400c40400303441256603040a0480b040945454020b120750b90007054500c9000c400700258405901c0c3c1c102e140a4205080c800044400280d1741e4950707030001d00031003e2104c0384a8280324190080211420000d549840e185d4043c02003c2c002c0320180c480e03005542c4444803000041881a8030092a2400160300d03507461 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 488664208 1250 488662958 488662981
    0x8090606060d15090203060415080a031b08040b0a0e030313030209060103020904050c04030203010b090c190507051e0f03120c030a0905030a030f1b1e0302221a040b0f03 74
    0x8082d00940c003d040001440100c158004c601603a8203860a101459a0b0501ea0180c45c04610448045601030302c03800011a00c10408400f000413078007010b150000386900c4102c1660442e411070b14105da00081c201203100d401c90b62182000c0d00660145041a1880b52030391304008091001a00800c091000a54213a129034106c6143c0d00d0010300070002c509090110400315000350100703e0281d80b0f402c038403050354540f401c0c81c07030720429909401c1e038900400c401d02401102c218800c140280641031081500098050080d4008034002e41504141c503040140414544901d4804c6d03044250020440500024100c44010380d02c440d0051070259650ac0d0800040300602510801820600011032800303201a85504403404845640d10306100780074250352178104040784200b18802148403a928501080e002010102d400341103800e0050401c81075a0010844c4483c00035035070b401c440904021b01000b400c44001380d501c1ca0961002c5810181001c281070002c0c898241d41d101c42c0380b000f100062441003c0c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 488665458 1250 488664208 488664221
    0x3150b092b1b08070f14030304050915090615180604030f0b09070e16080405011d010e06091b15091302030a140708010b07031106100302010f08090606060d 68
    0x40d4a950304081ca42401c1103054003009100100c41810411000201e015000909a050321400900c403c0c10702d140c041e031010310748180a4610342500051200003080e949140c00c10344034601c1c1c1000c00201914500400c000f03004000c040301d22669611f1503400d44440d0540680f590040315103400c0d00008a4180002d6290080da40700502015410840c50100b0418042c3c0c6801480510100e900083e1911045a100901158002c0500c1c920310181c0c40c483d03104070700300c81d0082d01130b500000f15100ca00d100d00721003117400044030b525a0b44840141d490728904200c2a5440080302018081036580401d01021005083e40032a108a04001c111924406604216543d100004120840188005400030043d40040300d40e441414030f00180039040003903480303256118000d180d440c10f555a0030521030201d2504800026020045041000300e200c0720100b02c090301960b1b841c140c4014a03807440c400141415040c07402d91f0200081c180c24058428000169103030802401c54200781c0f64442e524086c0d006060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 488666708 1250 488665458 488665519
    0x9030d0c020a08030c0a09060201091104050c1c020405010e120606011115041a0924070917070302040b12060430030606030e0f0703020d0f0b01080d03150b09 69
    0x4001060201d501403030002006d000741c80361104203a181d503034401030b0708035007200d500070301020580340d040300b0b1034901580220f500c02c120040903414480301441c0c803429040d60100c8038040a50016003442a0f60700003154022000003112031281302082400307480d0321a40050324141c14420741c0101a1030442c0300f4802e43c41c07401519041c0f0129440c0500b003401036000d84100c1c1680304000d20000c0b80550078049542c0e0104200c104260361940c45d0581d01500f607480007030040781000354140010441c0c584501ca200c014182c00c0f00142441030450041008680c1d208001600c20312074101c20300b00c004008602c00c1d510580020310091140c0c2ca0750212000c0404030303076079000711001c46078248503065095071218064403250740d0108600818a090640ea40c551421140c0f600d50200c2c0041005140980804c000300d4400d00c410755036041a980c3c0c05154207400e0f0800380036604560102507072a541841011100005245803011603442d10102011903c00c029040f801012a0100c10540102c0343d20492050413 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 488667958 1250 488666708 488666723
    0x10902060f0a03061d01030b010b0a0206040b060316030503070c24050901030228080a02042312120706052202040b030114010f030204061509170a120914040509030d0c020a 75
    0x400d203085d401c2c1754050034081116442e0004e00007280010703d020982e0035503005a001000c650304d45803542c0d0311011000b00710a42c1441048808155400702c40a91001944a01d006646034910340c80d04015403105a0403030041d000c800c103400c030300c010f07250700c00c0482c1204141031645c1d0b10241c6d000100d010344651a00528100d1144041b190020082c410b0524080030303030b60304c0c9201911800200c1b010ba2244c2e20800c00112824074124510310316460340c51044810060114a0900107252079600b0142c26841e4408102c6001c22104d0511486005050f0700c0400b24606d45c0c803007d91002e0301200d94130400e0002c2d018075902c0031100b03071540b425403148100a4051441044170348c1c3d5882d102d9020541404124003c0c2c0c00d1800004000c24154485501c01e03189840b10349003907041810590346100d4080c0311070414407403500c003600800c96140d40f0b184200c0d00d940d600c070b07151030800c0c10422141c1c0f07083c101c0c0c0e80154982000c02122110200c00d0714a20010482302007504014420708a1401c90107400140150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 488669064 1106 488667958 488667989
    0x1030e01151e080d09060809071203050702060912012c06060111150903031602030307210b0a14040c08130807210e0111010902060f0a0306 61
    0x2500065502402c195962000f145402c040c580d02001180d401e80c028032a45510114060344070613810002c1091500d0300300032043c0406030500c040c042002c0456240c04669075602103503134440000b03111003004413a880250340200410360110614465840c003c100d00c081880c01d0f1078400c0d4001000e00325a6960000550b030003c00b00c0900b80680c0100420007280002c065811350081006800a540b6481e02085d4142403d0401000505560090041081c0f16a11082460040e40000d881542c81c0c50601200d9024003048070301c0c00c0d4040340c0c035440400c1c0881d88aa10403040e2004072803d0089003d40f04040d40c1c40300c03041da50303050b2510041c0c0c3e8800200b42000c0c001c0c4101445004c0d03045400b10050b13024032a0744060004d03840000c160019005507580e10071b1045a590450400821132880030758001201c6115a107e132a43c5083e010803141f400d03c3c006c1d84400000c0070131860b480d410 = true := by decide +kernel

theorem cover : BRFrame.Cov 488489208 488669064 := by
  have h0 := BRFrame.cov_init 488489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 488489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 488489208 ≤ n) (h2 : n < 488669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
