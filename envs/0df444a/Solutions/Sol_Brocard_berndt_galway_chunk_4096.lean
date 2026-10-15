-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:33:24.980394+00:00
-- url     : https://prove2.me/submissions/984dda2e-c64c-4449-bc34-d57db49441f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 736510791 ≤ n < 736690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 736512041 1250 736510791 736510793
    0x18150207051807081b040915030b04080a0e0f0906010c0c030506180f0303220503070804090902010f09080601060c11130c1704150b0d021e0f0307030b0f10030f 70
    0x458140c0c040e80244e9a034050036250080000c42d114050520a40c90700000c10082103848440e82c4011000400e10442c0d21441d175482d103900384420401c68007521081b0340003c007041066032000791901030380000c95020401954080110b0201e41e0000c111078107000c24180300c40107020101c01450000c41e40704089030064038004041c0c080e001e0003000b400f0303401d1041c0002c07002091000300170f40707100d01304181000000c4840e02421109a62441e6016211408100b2204001c188a50010000340000d0751010070b0052082c40010040042402c002c0200900f481c81848111000303c2c00c2d604641c0d980c609400000b140c0e08041000c810144012588070184200111320700003c0c1d0404d155210306522484061040c0f030901d13003001030302120020018941c4580d965058640d40d80b000c080701101038082441d0007181d902045080c1c01242100d0803079038601d080003949203440115149480000d80151404a19641d558008050040c2ca500403100c401d0340010102c5190343c5507000115000700980e4034007a91 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 736513291 1250 736512041 736512079
    0x30b0123030a0c060e03031207050f210717070818031303050c0301291011060f0411040b030606040504022202030406051003021032030907061815020705 67
    0x3e64070035440880c0c44000c01c905a80780c048292002c040012012805560f5034003c02c0782c40303a116007540f80f1160401d201d40e04800e0b02115a0140d0000700c440001d4490070210b40150803440e560030030013101d0b40c0170bd00704205c1c42c1d0b1244603541c100065070300c4d640004a81c03000c01800d60103440b0300020b510003540c40c00000c3c013000240d40003100d4001d600030020f550729aa0407070980001401c0c0c000e000e4250940a2a00f4200411404690902c0341380980740e1980c1414801e0503c14281c40a0351240321907818403045c81602d0201c0003114008030b40c104641011503001c80d0321014000d03d042c0c45659203c0c005001e64960b824028040d200382c1001148403240341c1d208a00942007030703405840c0d280c50b040001d110b1003498282c1c501500e400030009451028110380480b410160714802040034407511030042e0720152151a802000d5401013900c5850707141c09490f5034540b801a5100004200d003000300c179104a030803c02d111782a075001031000ca28086441310103910700070041d4070090304030100c0802080b240c0303c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 736514541 1250 736513291 736513313
    0xa0314190c020f03030c120c031309090311010506032109120a03080108121c1512020103320411060d051e0115051606060e010503060c0301030b0123030a 67
    0x2c421100354070518061000c0c140c0d40d0290706800b958503441039200e0001d40030480054032407250190200e924003600301e1110002c149055106011098a841c5600308142c1c200c003440700585c4202d0000c22051908000280d1385009a54000020031503101c1a495403940c00800c80c2c1b0507000203081002603400d5186d5080d40c5401c41801980081e0300c2e20004201c0e02004030701d20348980800310b20b0600700b204202150302d060102440b407002880c3e0703429000101e500c40f009042d0041c400382c03200c5105022030380009015904000d8412040c4508400d299516004c070058103046540d01903070750905035403545040c8240c18889100150712410108040c0d205554540055101741504480840740c06040d260442d0160402c2c02005584402c5200402d0518403d4018050b80c10a1100c00c0ca8401040c1d00c072213088682a80042e02c40d082030301d00501c41390904104d2503811000d240625443c0d0762450b00c0740d5500c400180500740d040c19800345821010340c660b00d1031070701407d0000d00392403500343c2e2840c04d00e003045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 736515791 1250 736514541 736514543
    0x3050a0c0e010e010303021b13050103030f021510121a0c090a0815071211030405030a141801080703061d04060f0b060d090201170702030a0306170a0314190c 69
    0x80c8590003ca4640002d081c6513040300d0b07054000300442e049040c4086006002203e0b41500000c44006850f0102024003e50307000354080d840b071079420b030414403000781403040200301c00725858a90300902814142504507401121100741d5885038044113450440035403601307030b035107803040708555020310070000006070040c5080401290340308100c42c5d66861707558841c1e40111703040305e0301102d4600141c000c90244428200d001550040000d41650384284001260001d54041d40c56a201060b80e40171580c0100c0c1000c1044400c1d8411f908282075101001601203034060054108451b020101380020300940001c00549060300c1c000c1d0300d203074408814101e01c5101319000d03100300c4d08055004070400c00340d00c65401c1c5141c01400091070240b0fa10740010240c51420300803810485005500d2043c040010a00d030301960103540a156039011140c802011f90b07480c3d40040072a6542140e03071702c0754250000f0b800c04041d941420314054040c40c281001c02d40d0f00421141c010b0581c0b203996070071a20740d030010b440380100b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 736517041 1250 736515791 736515809
    0x5030f0a030609050f1810020c0114090a080d0207050309090108030c06070f090915031b03060614062b020c0a1e02030312090f011a1804110f03010603050a0c 69
    0x540c1c1e104070f10001d5410640b900ca20b0403107810082203070f002002d01e203401c0c0c40e207400d002c0345c0c030304982d905042c0126840348105100c0740c0d40d608001282c41c166040c010350070110000c000c11140c43e0540b2201c1d02c80c400e03210400da405a00048000401105005076820034030024401c11480d80e44440164881c0e0000803810340c68041c50b13001035034050090903034844007a0790742d0703400348840e007009020002032829070300301d035644003c1c00000030002e44410700c402c3c912000c00c60520011440d601d001c409440440d0003040b11030725403440b0150681c5401007591a03240c0c0440b07144040000031403584c0c101c1ca101401e0048080d000140718078014200040440d080d500c500301d0740b0301d84003960804803203041a02a0081d0f051300b042064091031030403154115042101d0805541e07995550406807400c490303007201041046c2500191300c1038140b034200c07000002e0744000404ca101038500359580c1c1e41c03080c880860951003007000e184c0c0c000c041d80f002d41c003150155034000d044500501070ba0401b409544802d12641c1c0c41 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 736518291 1250 736517041 736517051
    0xe011506180e010603180203060a02070c080f03030606030612070825120305070c0e040f02100302071a1308040b0301050913050a0b04110d03030b2719020705030f0a03 73
    0x803103040490700c20100c07076400d09800c12690034520220040c042c1c60180e100c0d001a90015100940e84c1440510f0052100003001607a8205514183c4001010baa00c481069013140c00d034510241c801000f200d600800c21030b07141c4e94a92b107240000d1400080549412020b11070900049091200000d014910b0381e40b9008a05000100c0000c02c14501200c2c021251026000111080043e018101809500f84100d150401807501e4103d8443c3c0094211010356049666120000c19420400500300503003110340f500350304c0e11200303455110310354803489480b010192070030000034504001c00040500b1540e1142601d59115074840144000303400a0003514803c010b41030103e60140f945003c240b400a5000d40034196040c501d031a43c50850100410a56040b4681308440c0c65a07941c406085803428825200001c00030010024001039007155214202005080803ca28043c0e6503c40040d1b480404140b0304068032030140c496801a008400300145580300108045c2f0b81f0f0302c403242c003424619500c0c0d502001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 736519541 1250 736518291 736518317
    0x10f06090606120504051c0513140d02131d0604021203041a030703020d0c0807020c01031e05090c040603050d1b0b0606130f1e17070611010e011506 65
    0x8484041c85480c0c0402c21198441c44080007980243c0d9015014005036660009a03000c4288070715104942000002d40c002802c1d140003c407940049c1c040d04065001c08640e410041c04500001810b12010b44181c08484660b081c00722203412180b401701111004c181c0007003c140700540c3d51402660100c0c03080e24506201283c205000050340d04072500c0c9500413914031216064408541e00190040702050380030846c0c0f102c440b0407805038480c044ca40da0f944403003a1605420007810808644021070406090020b69903080003041c1c10b8040d0300281e0280000d690302c0e0f4403c19881c064440d03078001e80081c00d2120000c14007201040e1600000f9407901c404034400211181030358101d07540140140206203c03404540e581c241080648804c80080c2c1104404903196405202070041c0c0343d0141e061241d01daa1004c40d20f1142d80782d502c0040c51094040f03410450524501a141d05140c0510420020100700084588009403c500c5201000200810007500d030300102030b801e00c0303030760240e500482e00b4414044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 736520791 1250 736519541 736519559
    0x20a090e060d0f03260408070b0901090309090b040f1103010e0106050c1506191502010e0a1511071703041205070c03030e040e070f0807080d020607120914010f06 71
    0x1145290b114003e2061199241d0b41a69040481104c0d07090f4448081d5102c5180c000e00500740d40a14000c1c03040984940d4145445c600030000185070407800d90506d4450400260050085416500e80803008a1220700d0714020030002c0103502c249141d010b0624004000488100e0f00a5058460301c1009007510781c3c0b103540030b0344c50348102045442e25500420759411a442d440d150a07410800041c5001490100d001020160903444c5d0045602001901e1100a006409108490300c0100f10805005541455115050b014243c03400c8003407015103030380346000b40f154181c00301c0d00c2907940441d40c0d44410722454400c09507500120307000c90708846440b01d82280d6500507801d4a40c0d00b64030401c0c4000c00342c1503640444104440f0341c1b01c15005519583e000341c40f003d050000e0b1000c0c1c032090750741e00195454401c04624081c2545c0c003d0301d00d038210300d0005200035400305640e98070400c9400c2510756002c070124060000d041e1070710060308130a1100200c0c0440300c0e064121600c04e21400c10103118503a100c2283c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 736522041 1250 736520791 736520809
    0x50c041a070b1308071506090b12031b0a020d0c140f061801120221010608071b0318270522020a1d0118060f031113020a090e06 56
    0x54181010302d400200d501d0080300030440d81601c41c150303150030014190303190034249022410400d01c1e036131140b60a000e025181c1c0b04030384043c0c10072101100c4501d0042c9010780c6034814032032450803c14081c6100d002021082251042c1554060140c824000c1d190611804002c02c5000e881c00b0b00c40e0304140c003c4949880ea03c41c60800800070b003d01e25000e001044e814880d1201450b00b41403000c203c0c0042e03560901c3e0b10182100455030340d04958000303014004408000c005801507400c1c000d048007409141c0790310070b40040410110764a05e1000f500b1500702a54a40c2c0404070303445c1412540b000104c1d038072210710b1027000256050268081c05031b03800e0400c981912011074000054112002105100c034030060200d00781035001070900070509881d480b0402d40c2c0021680d8040e0a50070610041000c1c490703900d92000d10702c007042c40400c100b505207180d0b607030030490611010b0400c440d500c541015070358030907044c001e240e84440400c41d80e030010004007410660712303440b812918000a0000031242d050614803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 736523291 1250 736522041 736522043
    0x150105040905040c2105070509040c1e0e0c0a1b080315130c020307030809010903080c1b0601080606030c010801080d050313050d0c060b0d0203060c0a03020904050c041a07 75
    0x10541040d05029941c40180b20050050700c444400f110009401900348455800343c2c1c000d901e10704403004050610700d2410a0b19400f907801800001d04000101e40c140b05040c040c0d42d2241c0c20044aa0390407a00c00d0f81248068100c000d241d80b00d08148500b4140236070040840c2d1005131505881c0613046903420a4416440304050074034801040059880700d1001c810200c0104000c02d0b2802200c0a000d40c90110350550101030302590000400764180340e040008994080c072800000e20440c0003644c0c009000c490040e05d211007420010449594200341000f4089c080e0030362300112076035903a40310046a40c5000c10740380c09001f0301a1801c44d00081d44964036580c16100c0113401802c0090a05004075810740c40103000c0246560b1044051000603000d05c48485c4533185a559080c492030720341080801c440400641c103200f01070030542c0f1801a10041440c540c84001070403001d480d004a00c105030007070320841c8101a0312620301400c2020610100000d0025112001c03c019099000000704840c0ba105590b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 736524541 1250 736523291 736523297
    0x120d0302090109080d301a030105011710051518040c09020708041403030705150f011d04030e01020304050307060c050d0327020a05061c0507020d120f0e120a081501 72
    0x2501149602c4805070b44400d20b1141c441606e1125040a480f0441d4401064441500300c681601025481e01340500350240065101c83c80078100c00a080943d541c0280d4400ca83c0c2644450000b440540000f81d5402d0141001d000e1044203541814040290002210304591256040201141a076154401e0381e00d800e510503c03ca2810307081801b40c0402a598003107050f032501c0100000800100180041c1c0b00c1c005880d5206441ca04002028050226050f048107806601c600100d010748101544c030700760001e4244c20304055884902004034214401c0c0e4000d55094860108002404c80d48840428a0707180508107441c003c00c0c2002045003561400c050340410414040086070018a00100d40761540b4801000d030304649036504c010941d1a001000d41e07081c985c8181820300170007009409003039400300062003e0000001c40c410090b0821200b00720160807241c0e1202900c88c43d2020794084400c0c168140304803162022640012500350313203e00c0503200051154070201c2c5045036000204044004161 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 736525791 1250 736524541 736524557
    0x90c0a03060e1303081005040e0706030c03020f030a0216121d030303041109090109240c08040c06050903150c09030d0801080a080307020c0a06020106080f060c090d02120d0302090109080d 82
    0x30310102e03038012001d400c200c07070300c251b00a0002d0a075aa91240c482c5844182010340740c40c914080c0054206d880600c1c441c818180100f00d0300c3e01d400c46010841e50b00a44a40c00181c80f402e003441d040d2240312481500038148603c1004401138a41c02c5540171803400c40003030345850410b1515050503144d01041e82c2c020040200c0c81460140b92824000f2103138072800003000040d81604070b13203400d9013800269511302e4041c1b0080c0b49841036454070f8004c101c11041241021203150500e85c0d544000311469106e0703442040340202c0c2c100e01c1c2d0790301803100b071003401491140c528a600b4088410100b55000c488100e21078452001c514a4060040319298101d42a003000ba06d081a000e46070119603500040031141117008000d0201d00350780d5007098140281030075a0000603605d0030450403a1801400b820303412045c4c0d116008000041c40c401d000c1f03800600c0c041d5010b44a80c1c84510120390050491032109825005580761009510781c107601400030000247d9a44241560310805c442c1c80328025065034000179840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 736527041 1250 736525791 736525793
    0x5010f1a060702041d01050106030b0f10020607030b06070b0a060509100806010b09040209040c02150912190c0803010303030e010b0105030c16031b0c08010c021f0c050702090c0a03060e13 82
    0xb035444504401c220b80102c250049174441004c0c21900242c1004020a9540080f2311f500d060520310010300c10070075200340b002020f5500d800303551030300001c013050200341e00d03503d0b080141d46500c4107403180c081d8001c2540c0071504004800314081d00890058170b000f21000000158080f8800c0c01040860342d464002d06016400c2401c0c001d05907000030a9a50441c2d0201720b00c6c000c50f2603500c034114825146501422000034a075022802030b40010304030a00a910403c0030451a081035001c486181801246070012001141b605407002070608034050411800071000205042e0550440015070340c1c2c2030000c00407298040015034845c082640c0d110000441030040814080f1086000c0385c625002e41840c01c003c0007108a02c90120280c100215a603202411041000f03d0013402100206912130000d0110600b0504d445107030340030032000b80484a511100c0002c8100d009201302c4040b181c001e4075454252500c41e64041140e44141d12030f100085c030f400d1300001c46030020b4944a0083c20f40700c600080150103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 736528291 1250 736527041 736527049
    0x1306090e030913230c030603010c020309010f05070501060e07051e070f0204180602030c09090112030f14090316061106011809080d0e1e0a08120a090f05010f1a060702 73
    0x10025a54005a0020320490081d110f05004e540b2030086152296924501041810b088d140c030000c07843c00395403050084448617030300030091401550f00e902e005601c2e450142402c9000d0301785076002241c1140740d4000e008810794410300a00c1665800500403850360b280b1380300070340c003071040c0c110141a03200c0140754800145460b800210030140341c01080318001c0c1041c2c030390304202c0e401520400b540c0790002900310454100560744500509500040d6078200e006e80c2c030090400c44800c4412820403100c42102c07820b484852040d52000c02c80a4201e4000504150413040c007002280900808940b900c8a0704501190000700981610b56004001042d0480d5003c054040c00d001c1e03100b00c508540510503140e108110b446003d4041c01d401004184500e981d404848580c2c070b04e003600b44d03104d400a10115001ca82a07a04403070051400b0740800d591951074400050041410610040c9548d40b0150101c00388070054101c1c2c5603d0709050810451400207030942d00c0c42c0320545001a8000b4401c1c0300002c00340c50 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 736529541 1250 736528291 736528301
    0x515070503010501200d0e040b09150409020604031b0611030c07050609062209050105060f160c03080706051f030c03080d0b0604180f02030702061605091306090e030913 74
    0x80a001030012124045ca1a0f80c2400d24407121072000911010005a181c46c083c02015a403403c1983d1002490502c1809003c0c508410101d443c0501d495007000021501c0704401c60b001140c200f80801e602d900e0200e501c0b84007556603c40c0000140c0b498041008068000c411203494030098001020380d20316080911070365400ca0240d09034001014000e0b188800384540d0350054981d826003981c2c03c40e90605041100300d80061300040d0003a0340c00c1c400c0c00011120681252080c3c06400344120204160b441c100f42850380c103400080c10004046401c10030808142c0100c0c0c0600034001c00c2c0000c801040d200404402c14030b1002030240d403001c24041000c10b012034000c01003d1588032011071034200d00408503556901580c425420320505140310300410602d4031403c101d02c214504154918146510000d40d50708001e041c00025a02c22813145030524010346c00c80e54242d00280c02c41c02100b84000380e00008004600c40c00c0b1180d402c101c00c1516520002c41103a41c1003800505815481d901560400020a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 736530791 1250 736529541 736529567
    0x1206040506060a05010c15110f03041415040816061103100504110423030d09031707030816031407050d2406050a18090207030e091504020702010318030207030515070503010501 77
    0x1d0b40e5045c600c03400c422310100500031a040802100c1c3e40381814640a1180c1d00701a02c40d003503503000941d8000c0044000000503030031a80240140c1d440e0f0021414111480c950168014559454a08070300c14444c1d290018521800c14035201215103030f9107405000a54500e0070082d10318035020030060000c3c440000c503d43c8140a03180e40220240e44080100340b0b000303d031481e40c00100f52920410000c0140c55204500b007807003040802810404180d03009442c1d0000a8403030414004a4115561964800da100c0003003003602102d00005814030180281c07080d4880148100030382e040ca4003044007040381803402c83c502c003c21a60042110310305042103845400c0850312204010720500100c01c3d4041d80040040a003021420041e40c4010514018114032100f84500303002d07034442000c000c50352648845078050414250b4001d80e648006100480051a194032044071064040c6000020b0560000310300f02504e100d401104c211201c6c1001b11014a20704031166400204104018071140d442941300181d21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 736532041 1250 736530791 736530833
    0x90705130c050c0d170c120c0c01091505090d030501030f020942120a06180b100e06030303040c05010f14070302011401050a030503040e151206040506060a05010c 71
    0x60840080c5404c0c03800707050f410000141551101d403000c0d1040400b00350448901183e580c03424860311003145911100804030000f181012030900a000d02c04e400c81503006034014103802d2080b0300e441c140001010141c0c1e55170264881d0010158296002e413080a05030398120103195100c2d4030315400c0016039030703000302558545900f02145071001500244c400c0501d0005220030480d404401c6400b606842c00e46120a2203000c030341756802007419001c10035540c1e0540021004c280240b5070011070044406c1e207103005014901c120104001504550510800d40711140c0c0c2e038246d1a101d450415a0300d000c2030720090300070401c0e0301b0108a0b960050032038604400c0b00742420031036143c54159200f1785401c281e4003030300545d45440e020000e540c0c8900c4d9a070f0151000b211015600c500b91717100d4956030702940c0500104404640301180000324503021203040d44900812a03112645100905a1260f106840480f100c2c4940b030085210341c90101c5600c0c0560300c3c10307998440725107041d0312429034003031000d0003000c29 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 736533291 1250 736532041 736532047
    0xf210d092c1015030c020c040522060b030316051207151a041e0506030718020c03040b040b040e010b0f03041e080d0603050f0109170a03020d0501030c03030305090705130c05 76
    0x60f494501450300c0203542039240003440d000e890380068204001c400c401481a440d040c00c10003400e00074103030411510440e4155080c01c404924003140105050403101c0d500d40301c045095900b200030345c00f07071420706413195003962044210b40041e040203004010000340007408400b41e0700c0f01080d0503030090a01103003000c8200243c001c8d86021034112840c1588522451507140c150300084c03071070307030046a400c132405a00902c0748602d41114130844d11302103001c0390106900000c0b05801f003542081620702510a42c2041035484c0e94812408409034000d1007100480c0984000001c3c003c001e14068820074031024404610715500d83d035a02016007480b4050201c441500b440034000310300d081c006814025000703000010620f056061007072800b022480e03030503c20b0b814900314030009506294144414403072504510f86802a070203080c0c02074003039112242d1b00390b803801d0b0001042c0a000008042180d010392010040c0ea00c0d5a00b6040d101e4050340209504011181515903d1000b2a80035003c2e6480900d49142 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 736534541 1250 736533291 736533299
    0x1a0a140f041203030204030b07080601020c013c0809030a020c040b1903060c020f06090d200f07240828090510110c06060f210d092c10 59
    0x11038110b44003419030001e82d0100303041c41001007034800190407004a080c120250324005000079518201822901d0400a6030722100c2e07103c0103075118403209515143c0256038450b800380000c6c0d0701621624000c7c0300045841c804a200012301004031341044007241d001d480c02407400001c0c0806080c4400c005500440d84540008030900c284120740007451060720040782c01411010001d207443d14018078890b194000d0401d004000c080002c018004800904240c008503000281c0c0728042c0100d40b0f040817490084840d01c040001c0007050b43c005482950f1405035500e0303140f030b0ba0b160058001d040094041895036006c10075200c51241e036101142500c0300c0f19801c2d01c41c030f07903400d0059944c1f03490100e426501c4108a0140000f40d405805014103401018a041807030a204a55988074050400c500a00704082d48070304a88481280c80d0400d100c81c00381002c030400d001011a560f0001054900004104100c041540b40c240100c44d07a00c040c14104c410a02080001c2243c0340d0040540300c1d0098003520b0000007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 736535791 1250 736534541 736534559
    0x15050d0c06110d09030b041a0a0b100507050303180c03030d140105060c0d050703030221040203120309100b0301090204060b12090d0c030e040917041a0a140f04 70
    0x1900a104428030000c862600c140945800982072110039030741c220400540c64a503010000d142244d0b0015850b800584440c28001900c0300341d0269190001c40c68030420264403140d8003d0151088181c0700c501600542c41070890740c0f802600070040103600100003145007240318558810f12106c0300c1003031b140d1100224000a166602007106070b0300894071210414144600100640c4c010101030b550a441d103182c14040310388071220703001c80e03d00380f11002c00c070310043c188240e05490524961060103460300d060790408900d00d00c003c6408a10902c41d1042318008000a2001e40303020b810700a00400300700d40c807a12000041d180c90380c00b65070199603900c000e00251703485015040c000d00701c40940700d0b91007000b140c40c1d480310800103110007201e03401100c50501890f800001c2200f282c0c0c043c07614062210080000030082c00403841c001d0402400d0f60412042080d200d0000c001b114800700030315003580e10380f08004469014000049002c105210f00d09070802034050024046d007081c84d03182038505a240d585003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 736537041 1250 736535791 736535809
    0x5030115111c0f082a0a0903080313060f0c02030306221d060c0f030c22090507030e0a11121f050709090b0901060e1309050102090102012007061505 65
    0x156000840310200300f2052a00408640c0e00081e010002c01442d2241c400750240c0945682140d01c104070000840722115032040c09038101840c0c0c80344000d0382da8100612400b141d1001d021003a240f407460f0640004225025203e180c0450656030040c41c190b580d000100000c601110b40c0680c11702411184050201d07085100f91071150140800000c030503503c1c80c8103103140002c0140589406002080b50090100d00801030302e40c40b010280307849580309613654108080b950740300c4c100070302d01308034100c04280f24045800843c811003280d038042058100c8045256683c10001c140a0064075041c03007090014100051044441e040c0e460445590011504911034503604640005002d940c0e03c0c014032680f2a07010340708070003c00395201d09114001160b4000ba060000610450051101510860307000e40c80383c1c0c0c05c000700c400f40c4a001f00074440017410014040e512050390306006500c2c20381102c0b4000205008003140b0400b8803030312410300c3e400365107140081070710785541000d02082d0b14000815030307954402 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 736538291 1250 736537041 736537093
    0x10b0319031b0f06050c0903010c0f021b1804020f09010e06010e1e10020106090c27081209060d0501080a060f02040b180f040213150503011511 63
    0x11202080c80141801041076605441d2031668881e003001c1d800118100c108810fa0302600901d0005681d01c074044002418400e2030714480e05542004014021150021a02000016683c081d84c1010088404140d042040101c02e103030701480c03000440000c0d1203040191039000b8800f40029959460320f5001500000d0241c4c0111f40ac2a02c010803c0841d50303005e156180c100c0320a40c0d0b00b5000720384ca1a00703285000354000b03505009081c1e80342001d008071f03c00d420510052031022410007035980c41c1d000040003c0300c000d800e041aa01a8811a016a80441020411214928003070105500c0c08080e0f0741030742c0e1050100ca13500200500c100d1106c842d0b24400c40d070003003041c0c00080440400f203151910a488101c000301840a2040c042000108400f00032a904030030070070700b05402d580800d000078001568811215401520100303840804100e41d0140b00140c2d4003050004070380c03075440740d0200c0d11480240541d00c42200c02408184c0380c40d0003241400d005807203d40980c1c5803489520040079000026003c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 736539541 1250 736538291 736538323
    0x902032a091507142d0a06060b0a09050303090319030306080712021c020a0b070303140f090709050103120503150411090423180f030301060525030e040509010b03 71
    0x20302d071401c02c200040264090a131100284c0300e90341e080da400c608018440228800c000f1000480151601014450401c10540c0000208560780e25a16a51a1a0420444140810000310010405280c000159516190028010080769480da201c502c80c511072250101c0070f0544803000440c0f07003402888501e014114815900300d9030403003401004001c0c01c650441d09009000080c40300c002d40c50710704411003072302c0c0c0f1070126503074031111480d045004149202808045940500900c00541081c420700340c0500031020032105515101c580f00e00860b0803c1c800100f260b072144011b008054041d001039540030f91503041c50b41003126413801282c00e907581c0ca0b0403c0c01401e000a082049480e091061541e4841e40d203409891154504050500c002c40107840d1210098414071503c8a008080054030140e015040540b41c488d40e649201410707030b4200c03607403242c16801081c0489010070021000e800d00700750183d642010452041c000c1c03000808001c2d05201d01d5540350400724909031400c000700079008100e41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 736540791 1250 736539541 736539547
    0xf080a0903050d2102070b01270e0f0d0f02070509070c0b040605061504050f062214010201060b0a0503130201050903010923030405060f09041e0507090902032a0915 72
    0x4450b11845136050340d10030082c0781c8180000c0001c182c009003034a040d2801444081a400c0090890784200b0079440c00f05d10549040c00b0841400c984041040084050309800b242d0208884030020784071102042101c0c00140d01c041000c11142ca81581c6580e0800540e04184240c8501c64403403440d036000c1110180c428945540c2400064103080301c00103809582c3c3d42c04282000c1c10715000420004101a60b24400c1c10003044640c03d079000409000010443c1024628060ba60348040301c0000040130100f83c00f6510340740c00064a80751400440700001826566207103140d4446445560761680408140d0400009000202890300c0c00d10655020031f01941c0d92210305c1000348007030b50160586900400036a001070101300203079124807007581c0030200002c07410381d155541d49000c54024a0074011f01d4511440d05c400b11540c1500542c06280107501703964924100300c2d1140c0800d0242c0c4015207100c15042429040c0408031107036405025034600490300018075046400c40020128014941c190340f41039000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 736542041 1250 736540791 736540817
    0xf10030b130f0c0e10120203060a09020c0706031b08221b0515040b030408030406150b0c1902090105041d0a05162702210406020309010b06070f080a0903050d 69
    0x40180080c80007000c450040e041691840005c1001250003e84c406e51074011000c035003195540c00e13000c3c2c040c00c0d182c1411500d6504032a8000d83c0e03100a4490000440d2501c40b81401c00200d422500341e141c00251242e18807521a00c8410b00300044043c0072084d04100198071a0008440380700b514074110240000c1d03514503081004200948020080343c0b180c10008100400c40c4201c0c0f482540e600942101d0f4803520b035076032810400085d2030414448026024051404200c060b003000141c1402800d0204a519940500d0040142190b03c17101c0a5840003004004203d14545034000b0036800c10306255440e40415400703001c620305258944211130750303040198810285a450b20108009084012000e402c86100341c42c120008002e0030240034401ea00010300c0080d0000c811018803030f450080e02c1b9a1400d150608000d4006d40040d95120019400d0050207620333454550203076880d181d00a000454100d00ea03640388543c0d644840900c00502c2801d00c0700002140f800d0104c51400100c0e030b2100c007041d0f803070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 736543291 1250 736542041 736542047
    0xb2b0c210207050d0f09030b1009050f06030a17091e01180e070f031118030606010507031b0f0b01030f0b01170a020f041e1a0f10030b130f0c 62
    0x4403181100d0880d105001c0c40740815000600f1110140960070000768900c013070b0f04100c401071100d0308042c0001240c002071100c0c100100c405402200e03200003007000a51a20b005109202d070342550307010f6142d44112401d0b008500804002584412072140c0540f0f000c1c405408195901c101001484c4480c50380000181c0301c1d42c00c903d000342502c18400c0740e03c007900d00b84000401305650140c504002c2003859803800351600d020b0381c0514400a540d0a4007903d420340c00c4a00740c1500d80c0700000e94024007991011995550040c002e65507443c0d496202e4030307101685143d00710400703072200343d013a40c420212407080d0b408034a03007544c00384c003850041c0030a2100c00d00c18104000b2510041c0d001d42c801d05080f65120f50f02a1001c64442c88183d81101d682e0000c0c1c81500024018100300c0300900d20074130204101c80c82d0030001d5404101c0440320000e0070a86003e43d0303810081e00c007414581c07440d002824505c000c000e245c407039404003104c2d241c010281c2c455034403001034020885240c00c4500d212141d1b42d04a540038160 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 736544541 1250 736543291 736543337
    0x71706062803061b0c030207030f03051c0c021605060f090a051810120308010905070e0a171002030403091505040e040b25050a032c01240b2b0c 63
    0x40b0b85e080c2454030611503940255110306a100103082040791144607010544990111100c0030803c880302200b015406001c18001d002c0b0721007440c05889004210361001406110f10402c4500007440306040849001e40c0403100d5203c3d50200340d00c1010610b0214140e0380d00c4a2002c4100b1440840092030701e46a0b0302c07103102503020b4200c00000f108140c030810001c4e600504003410744240000105260715920801d03540210f548001d9644045801d0000c104c0c00100c1c024580b42c24022821200c0d01c0d00000c0c4810124407065602034002139140307006002d0344441e02d060350540a45442c200e071410340e82d4520307100c00401c1990200da034111040c06000c04140340038105040c854850080e10307001d0000e55806002840381004010070705072150920b8030025144107825200c0d000f030301c00e0b1540e00c03103030040c12900800200610000700250303007145800c3e51070300b1001042952010240c1e0f9181c609a81868440d020760160041101c00c079505080d40d41c0e4026001e60b000b071490f2510346040c8201c458050981c84a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 736545791 1250 736544541 736544591
    0x30f03010b0a1404210501140c090a1a2208070b040e01060329010207171c0903050703020402030c0d090b010302090c0f0327060903030907170606280306 67
    0x18100740710521005805c0003810707031060700010169684010700e1400501400c64160185060021042002035200360003000b072103241b20407203c00044548803a441c0d05003400000c4103140281d81805400442c4140b62641c0c0e0101d0030038400c5580c840d0352403820901e000655040b01c00001c40120741042880010b040140c003506090809010780c03952400c8081401c095506144805412046095803030b90080c0b113004c0103000390301500110122000c4c00e03681c0d5604032001c00300700b0b200504050045548101409001d80c0d40c804064200070307145408010203034002a20400050360108071486d02c02c0b245100c4e03840b51610982209029615500400030a144000c0107924521400c00104000c0c0440000f1641d0042c00a842c07200b045481c002c81070566804d020305103000340300308070030b0004011001001d0341c42a401c0800311044162071790405244901003ea00981980c402c0780464030929100d901801c4941c600c0d00c801401c103412203558104000182d105450f030650fa2910303001001c110203041c903000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 736547041 1250 736545791 736545827
    0x504030818010909020403150b1201020a022d03030a050a0f0903030c080109020f042102120714060a0c03030209030f030a0c02091e060d0602071b0e0f010b180102030f03010b0a 77
    0x11307e0340c0c0354005690b9002810300131712651120030740401c1ea108811041d00d102004000c5466943c2e1103c007955034078802d410302038218100c400404400300101e840c401c4c03862500e4040e50940d158006800043e00740502584003031616400c410b544d0342403034031441d402d060180d90b0202c2c0002601c0c03400307402400180c010800c210700421403400d10007503100485089945824100183c181040b114101800180314001d41c46082c811f0010240c3e200050001c003515007003a15042029060000c104c07240c8605201c40d0041480d40c00c140d4040f0f4040c1c0d018003444d03003015041e244c03440c08140840b81543c1c0481c81c1280800e4000307480c0340550401143c01980700c9664003001c107109082c0d5010994401c00140194031481c81e6210b03a80400c40150151011194004507001031a50702102030300d0b07101414025a01c5071100003000441345c410015030581241c8001c00c3e03080c03911aa000603c10b03545d21412016055100804c43c8001c45004000114003d00f0800e01003034592907448801480c0e11088072041c065 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 736548291 1250 736547041 736547047
    0xd081f0501051b03040302091e1303140c0a0b0403120c180308070f0f0501090b070c020d0623090c030c150a1b02190311101b03050403081801090902 65
    0x1950340c1050403100d92125110f043c4030400301002549181d445543c2000b034118141c502806600034100140c80c4148072031062040d00d0342c2d102c101c2d0308031001c41c8130b038040d000591250a5240c80139001005014078242c010a642005e412600d0b0402201815542140081d00d4510304100c03002c640c0c440c0c0d0754a090365240030500d000240d8400e2545103098000030380303070103000140041000100c480e8010043d511000c0ca20f402c90f05401c00398000d001401041e00c81c414124000b03100e07207109034084110607178010446803410b0040e4650100410221081c80401040c000145034158030b52901148030341c0e0091f0007040014071503805e0504041400c01306034040c04c8510f84440160189806032040081d80b442c1410580f103034a030401004900000300a90444c0f920f40032102c0b0000c40180c117200352400756080d800401d090707a05110201102c1340b0030500049542a12012001b002c0d42511368450092a1850800d5140e8a03000c16071340c03180c500c1b01302001b2250040c07400d55070014045c1000301a400d00c1182 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 736549541 1250 736548291 736548299
    0x8060102100c0e2b050f120913090303110c21040e0c03070201090606030303020d15180b060d18030e03060c040b07170310030b160905210d081f 63
    0xc07030300c42c0000c0490301c00c80d51390038555036050ba040490001c001c103a124510b168085400c055848408048100100303003c0d0a00c00c103240c40c0480212a40701801511076281c4c10f040c1211305000b45020f07081141095183d0041020304a0305c44043c0402100030b5000e00808121030204640b444075843b81002031910500c4100400d60b10b0310512580b04628001540c4d603a0303582a02203005203440f0400410b00e0385409000b1042c5039143c0e024100110a00004010507103621403655401c3c1c50701e11911205c090107608080102080b60030600d00341101030555814107800c0d011901c2038171224100c50300c5881101500c0d000b8164021a81d9000070010380c007030200342c1010140c0300024401d5002c0c11594110009130201004a640030089150803080e121948071f0810b43d081c1c0300e000302c4520050300c80b0b0342c1c000c0119042d440140c0e0440001c10041c4c4a80f40340038a00300500c0380e08002c54000400c509071003c01841c400703600f4400842c11010340c2d59000c4a5142c0b0301e140d1403003200c00c0740051b0005200c0da04244 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 736550791 1250 736549541 736549547
    0x10303050a050c0a300c0c12050106090e01140a0207020604090b0f03010903021e1504030e0607080406122a0e030a1401090212030307021902040f050708060102100c 72
    0x41c0400081d00c1e0055a80c0344840c003180c030b07040d0010001890b10f1110000c2d0503503091050103a2400b03944103c1c140501200c0c403141114283c40140d00074000074a0f50a0408c082866a01c3e001d100c98480c40000c9031a9944036a1001104c40d03a07202800c02d651280212006945c02e204020350058001c401181403068079004120940030741e001e10154150b0702d43c0e040c01290744a01c6280b00c9031100500901c540003440c50f000303407500d00d0303120500c3c0060348450030312510f54000700741802c51844445000d40c859a403601d044800507003130b81d00607801502c1080150301184095004002821260316005000030780c0560400884881c0020000030071070203546c26107041c0c80001ca62088810a00d041c0384844004400241040c440080043c030704039070407080c0307484404107410040446000302c0d0114084200f003414241c8900c03049421781d005800045014958284544030030110701d00260000a440c0c10269804045032400d40d4490007284502c2d080220075a030400100a1210034800141b00c00c4400b80000303 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 736552041 1250 736550791 736550797
    0x50a060801050603060d1e0209070912060f0e0f0105100512100b030309030a1406100602030301061d0d0510110c0703060207060207121101060f0e070309050c19081501030305 76
    0x9603ca4071001000c61160303640c00c01c5400c506a008200d0f034400850008a5410034020780e40c003240038054101c00030303d02c0d81c05042e88100300d90494100b0340b8522241d54070200203000301564804041d642c1c09030044012000c02021420507041c000006650802903813045003111140d1015100d800c4042015207120408100c0340990100100085060f426001c0080e065000d06202980c0500c603510004003400007061664120b003400005079041911125081d109051756402a8405a4000c200400c05144501f90750000b040c1030841400032241404c1c0000c3c8074814003002a200c5910105415000b040343d0321904440003a02c44109240c4241440402c1d00c1ea2413510001e4420f607808640103040c03004640407110002c0d0301088078102c0040c10305015010854401c07540b88251310b0001c1c0031a000c00b8440a40040d18111080821207580d480003c030003501c144c500844441c002e00d4100901e503100e50b01201040c411a045005103d13050444070340c50040c0c4a28542102c500d400c00400201e50040c0071 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 736553291 1250 736552041 736552049
    0x81210081b0618130204050a080105060a030b07050c0706080f07181a120f040515040c0b0904020c0708010b0310091109060a081b01080708091005090c060d0b0901050a060801 76
    0x41c1d112030b1000a00740f00040d040300c140d50800400c2d01016503c2145500800540d002200d20314000c98075103007400e00301c40c0101d4140782c22400c040002c0c80852024450320340d0020440c0382c401e03e400307030788201541001025071041d0302080b04034060003032844c0c90f900d03142c3c6d000c2d20a10f411403002c6603428502080750303d0352080d81d403100d0107000304114450070301c011281c0001d00685d83c0c601d51b0915003421140710104413000da95500802e0101c0e4211014010143e02468000c1043c22a039400c1600301c03041944009000f542c019400c003c260960f00b003d100711002070401400009030480c040052509114242880314815032400c2443c01c00500b0f0f03040c88456014003a03441d01d0b220ba4074500418141625604004002d2156190f1440d000e9003440c005d007117a45080e6542c1100341c58402080d2024201600c003808183c01000b060000d81c2d070580e1020b54041002d2003103584107001e2002040940e40500f0195800c1611210700621600380100454010b04054500381c030344c1e0340b510707000038131103181805 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 736554541 1250 736553291 736553299
    0x702071512060315050129030c0d0e150a0606140a03060b0f03041b27180c050a0f08030301060c052d0c061c18081210081b 54
    0x90320321042481215409001c0c0c07424030042000e02d4503420311445201204031040c071601e003440c0001c40c0700b503070340c01d6602031a42409041c3c0702504078110ba00743d00c6803c0281021b022140600103940040742500846c816003c0d00303c050401903020781100b440145c03000780721480301420050b0400c11503070b1228241d50340c03000ca4407611b0386400b80c24034218042d2015a004211000300403a03d40f040b034403010010743c09284150400c1c80310901c40941002038841c10701c14208880c01402141c0c40395500b100722014030b000c200743c000135165100785041449182c40c610a651326003d040c001d00c030504112100070060900c0220301c2c1c0c041c3e0300d040d0342156203201c140030721010402444014010060100070211002074900400340400c000c00800181c0c0c020400c2c24000b5500c1200381e2035419060410484800c03003c21141040000101050030001d40258815107821a60b862060380c00305903400c01801d40312420b1902c034075031802e080d10030350504100f81d0409403040d0007010b05029405207280d00c95a40c184141c0d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 736555791 1250 736554541 736554569
    0x17041103100b0f190308030f01240503040b130b09010603020f09010f0302132d0b010807200304050303070303050906091c111608030a030f0902060f09130c18050306070207 75
    0x26225040c1c1c450790004048210207c1445440c100c5c800040341030344c079034104024010001a6003410643c100c0d20b070100c0403410400115000c60031101c03244da403040403001c801c00c150784241d640804005080301d41110302d0350359a1003842145001c002c040c1401500316040704565040c0000c2007a035500314440244203140c680305060f04504a07801c5200c280ca442d5460804007840410a4895103081c0d1801132040c5e890241911510741c001d50400d0b01601d40c0389d407018074040c00540c0050310203480c080e2411461001380400112583e00700000c058061003a540032038a4103200e803400d032a1000140031a51186c01070003c0d07a680c031284041c0c1032900e510520f00500e5200d0012081070500740c003d0b0290782080d0b8024804203404400100500d1030014a5800304020080400001c00b01c80d10b001c8000e61181080260809140c2e04402820a52100414420030703407402002e0b180844a250302e948011804c04030700210542c56486843c4010319043c0c01030305062500c040c00075200c1007180140380d4510010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 736557041 1250 736555791 736555819
    0x1e0617010b09030f1504020108131a06010e030712020108010f060f0c21020a032604020f0f03070e040606090b131a06070501020d0e070b1917041103100b0f 68
    0x10031030003130007a0045050b0b45511006441d40441410116016408107001c0b101080c96000080b50b403801198120104045411903107010926024010b0403032810003101c0c2420403071030368061215100401c3c0880b40080c0e807070300034400500b00300c07030592045d1820341c450340041001070741245154101c40424607100c4000c089a00c1c00d0606400c05400c0402c50412000c0707803181e07094002542402d140c0c007070b480e41e42001030303150f0702c0340c03d00d00c1000078891028001801050050410420a03200b036100201108420f600c4c00012a2504240d544150f44080400c01440b0074480d16124400241c26540c00030b0000180300c401081d843c120450385c9480041c0c1c0d072400342040d210030321540303100c13204003d21003561a00c0500b8403602035013002c0c59182c1c3d20b074900549800eaaa02c0050b82104491751007801c01d090a49030201c130100c0d407040c0010300c0301340420903d4041c401815803002c107104030b11410100025840d040241440c0c20380031560130507464500912019240e6035840e101d812540d0031075400400d9121 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 736558291 1250 736557041 736557043
    0xf02071e0306050a05190213050121021207110304050f0d1502040b0a030b1c0f060e100e060f06130b03010f0509030403050f070509041103161e0617010b0903 69
    0x18541c03001c0c0025240c0001c0c8511032030580c03c403a014540724895030381034241541200040b480380140c3c3d401c003c009104208002e50155801e41c0310345401d61481000014035900010aa0344164001004101510100499540c00c800600000b500320b40c015400c1606120105400c4058008014450104c90a07210204648081c201030854041002551910341d141c06c0e01c6d050390481c80d03059001c6420701c0062181401c041c802c00f05011642480059002c0c00e64032907402071803032040c003594010b896000b036101e07201c4104400f45592500900009400c200e4100103410070402800c00c03055801c2d40c1341072050590300c0c40612a5044801ca00010f00342d415940041d0050070a502402c2c0c40d2400e01c81040040030b004009803003182d02820a44184071040f4403501d84442441c012a980003085002140c08100340b0001c0c07800d07502c000750480c7c220201003102101480d201e07074015440c5400070a0529180e0a401c190240100b03100d0524224500b0b0400128549030f0301400b403841c03210004070b40141c80c0d82e8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 736559541 1250 736558291 736558349
    0x7020a08030c071506080d0e180105012601031a0c090907030c020106120b01081e1009030e030f2b020a0623040809152118100213060f0207 61
    0x410403080141c9640c0e41c1720107172203442c00140140808d035840c0000b00755060246c40850503201007407075417107507a0030400152401400202ca10f00d03054103105446200e400d0320352883d40a54051034405004900484901107148801400d40d0340c00d510500580346180c880f10f480c180c1181d40c0382808204400d01510072801045641e000c2c0d43c84210300b145c0d100512a540f2212816a80f002050b10840e240c0c10b100a074414401c88041d20199008112141c034000305a0301480080f0300c44d2501c440b03501c6a800010f850034080c94400581038000c00565000000c4552480050145055503080e000030360480107510344680c0480a4178440d1140d55802c18000703410f40c81c8800041e8030018440b03508182c10300d0052904401001e038003401c0c1c1442c2240007c012030041e14201c011110601c204420404003041045501509100351140c040c4902d4034144000e006071700f031001c2c14000040e120807103c0c44450241107603500000910102008900b21a64003040c0401600c0c29010204c40760003c2c0107404001003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 736560791 1250 736559541 736559573
    0x618030d0c110c0906060f0904060b04081b0114091302090d080703080a090206090f040f290a030201170c0910080604051b04050f0303220e07020a08030c07 68
    0x7498080c0e507655031a007003000c5001c1c9103554000c403002001c1c1e07402070121040042d1015544144140002042001d031403008018a00002d00f02182c0d01e9541c1e0121003050f0416003000070590081055400a4010307070b85680c030010000d180803118018a180c00480501c11054076900501e40004400b82441c5550101c4100d20809020061110f501e4200401140c0000c6070450009036010007040031040c05025840600307070000c00c0c60385044076a100300140d4030420810030b500262100c42d0070140060f2485007146410901d001c00d01c0e100b00c482684996000250341d180c0c8594641d07802807000d80d038004012000e4641d10310429042d0b4a42c45001c10190186100240c0c0c04115a0740820f030056009002c03d0241300240c40600168461020b01c0c004c50b03516601d00c40200f401400308005070b103403403441014120707030140a9924211011506212000250301c101083c20000c8208006d114449e840b800e500518601c09171001707810b0342d603416580380f2000d0b01c0c0c2c008a600110304082800040301e503013409a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 736562041 1250 736560791 736560817
    0xe07031514120a2d022e0e011e0c0b0403032f0306060703171e070804111504120b01150810050d14101b02030a020601030b0705040e28020c061803 64
    0x48030480c072022801b6204010725420100c0c43c02c00e100e0414003406c031800c2802c005171200c1003000942028060340ba155841840c04001020944101145c48450442e000b58040c4e5004290107403000080c007903400c00828201948a41403a0f100d1440c5602c8003540d41090b002c4511560381c52080c2002c4645484402800d403140f501003081c00588080c00c07525034000484e105074107105544000050b2264082104c002d081d91990040303101d0141740c0140008001c0c080cbd0b08841d030800d9101c0c10f4510464201c08400c5920480100062000380c414007461001600e9614104110f40303400203d00c107000006110f42800b03000c224006004002d030703416104100e80768000881d0100245200741c1405444a1003407006540364140490582900c04021217010301002d0b0000d2000b03074a0b40c0c0c0c480c41d80d220010044000c010007800041051490b0880d024021905001c0e0585d40721650350746e1000411040641d40340980c0b040140396000503000c9000360340600b030904031741541c1c0003e051450170761180140840130 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 736563291 1250 736562041 736562059
    0x240607150e120a27031101030509071802091309080403060b0301020d02030c13150507030e03010f0606050403121b11010c02030105010f08060f010803040e07031514120a2d02 76
    0xf8940c400b1208405480305190030b8001c01c04003522140900340c1c1d010240614081c144a00100c0d4003d410a541219111080300c800039a6034000e15044080e000c1d070051801d4001550030030500e482c0344105038403080c0110810a003052070360fa004035032155100c01085182c68541c040c680b9502035041c0ea1610050440640d030724540700c1d4160141e54800d25104241c05030f10789020510380d4030111b15801c401c1c16500da0034680a0551403d6522040302165583e166490361481001010359005078070090880c3e40301d590b00c460070f600d041c940400d003240000007080b16180c40f02c3e44d03040d8005e854024254100c1e40c00101c50ba040c400480780722009041c06074056007010000540d00c26107007060403c44e8811401d0b6078180e25214200000c1100031b200d01e02d0340d0740c0280030034012340001700b500e250484107504002501c20f000c00c0c0d06813480ad00641c0100500c8640d02c8401405050140c407191800c0000e8010f405048400d41d24817050401c40d11500498101d50709d100003441d1a40d44100720400e80081035945 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 736564541 1250 736563291 736563307
    0x30c010f020702040e011a040f0b060703021c21020702040b091609080a0507060807050c070b03060f011b060515130207031116060e18240607150e12 65
    0x20798410b100482c043d51420040e051605c80601c40c44003880502686032124078003684c20400a080b21b03090154440369035004880c21913650030010800f9070301c02c1d0040c4c61046081c240c102d51204410390302c0d005100210034642d8074014250940307005181c0c0860010b0711814640007290007000785040042c0c00010100500400f9104204e802006400030369a0521590b1035240f016282c4441c035070300130700f02c2d880205c0512802d801110100d44c080340c079140440c20514400d1825141c005ca680c000c8600b202c00109119084c100307503042c0140360340c0c01c3c2010076840803407a0303001c02c3c10a0441c002400e10355071074011500800d0240420070309800c00424000c03004450103001c4009500c0441c0440104141d04041292054007244800d600c2890218858440e8606142074540c509154421640106030810614800f030445041c01d0050700c200545280b8100d032903541100c1d10004e0240e407446075109000b280001401d8148544034050b44440102e90202600061071400f20701c5040031800d0440842c01035 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 736565791 1250 736564541 736564571
    0x3030903230a030201240506091c0f03031b0f020604060f0e010204060509130b090109050408160b06030d0504270b1c2d0618051606080903120414030c01 67
    0x60801000b40034a403000203901b03a80d15440016600c06d00780c00040c240000b500c1c034074140348050145a0082c0c0c17900e039440245c0d035a139540703840d9484040307001c281e54031088020f000c05c210221500b641182050b02601107001ca010356a00c9008000400c0c40340c550b19150700c00007081e000f1854001e100ba000355210394540c540545641c1080d860580215000300c4034403192142c2d4064401711440161843c001c036424400100c01a240041041d200c032002004421040e00540c54041308590240740d645142d0b080290405040420291151007008814001404601c0c40084940e00d0022a00302000d810b000101d09040904418294254003c1d81c11020000d41203010104a01c098401c10741d061811550003000d641d540a8644020700e43c1c80110454000a03242c0d030320024502c04078041c1c044d50010740c7da6600346881d007004400d003140f03050380e141000400d802080164010b103606000d181800342001039200c5000008101605d081084600c1440d4094240100d41031100103000034007c4807004200c0ea = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 736567041 1250 736565791 736565801
    0x90f0d0201021b0118020114071704051206040312090f0609060c0f0f0e0f06130b04140105090d03180306020a020703021002010b01020a020f0312030108060a0b010903030903230a030201 81
    0x1d403002e0f100b542c803102608061050704100c0c80c03980c6012032000303040e0f001140d4060003850401d104010400180700031560740b001881c100d807856030200307030340f1414170050000080c08000701a0050740060140000070390044004080302180340c0c000900040070341048203c440205e02c3c0035190300e2420006200b804000c0d004a0441c03041c548031548100c406941c1120600d004c0810400020b4400d011001e01d854041c6c004072041c43e00030406410000180e094203150140c60780f0000741c4410000307041003002901c2c100480003030000d080a608010340c1001042ca1090705200003070070051442c1d00d0301c5e0400c151001800185812900031512404540806940da460074041a44108808a00c20060350b02c14012041000810b90103019901d0440d4280a019602e04134980d0f80741c0030b40000311210705a080e010714020700080e0010001c0707041c01d00318041220556081d881c100302c95480c080c00880c0e00410103404a07544141928021240071400340140d5080380c0d4000d0007409506882401c3c10b505402c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 736568291 1250 736567041 736567057
    0x60e1006030c080403021b01050c100926120903070f03030c080a0c0512040501061d010302120120130f0b0903060703020310060c050c03063417090f0d020102 69
    0x400c0012451080040c2c0f0748040859004005900500d031f10921400004102c0d482e0507418144103003800700d10300c2d10320b0808050303030207007044507a4400d0b000c010b1002c1d1112000718980c3d01d00124100d0035100e41c1c0c003845c07480b0b225040141140040042020800200121400302d40c000c000111880c802d823400901410019001000203a1003e000c120109641d225884403423401e5201c90385801c403000c0d20030102c1d620040041c1c445560303030700000030b4030707003800c020400200b04c21070f00d200c003e41c1940304001c046009100840816890700881c0b002100c00620100c4824802441040e1079204d040e140e8103074404d9540200c0740072a286803001504c1026140a050f140c1011426100143d80300d9000b14201d00088610b101c2240504404000550264205150743d502030419105d0030480c5001003440c01d103050f645907646104917035403000c0c0151900d80b031a8943e001220303202d003440ca1028004100000c40005841c00c07440c0c14000c03e075500c0003040600e184118440555640f1851280003034001c1d00300e099 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 736569541 1250 736568291 736568297
    0x90902130908070b06010e061801020703061505040f060b0702210d030516020c010e0f04090c0b0702010908060903030a2a051b0604080316090e1f050907140d060e1006 73
    0x3c007082d080e40c000d01f400c0e449417a01400207401e140540011468240c0c1400045065000700a4003202080b905e00801d150b06142c44001440343c0e29000c2404120f400300d000f04e01c00e061400105101607040b0000300c51030240c0481d101c0c010668011001440140d00d080707200800d1058400641c046074040e0001485086000550624040c0700401030341c03a00c02d568403040c0000d02590010f10341c5e2412000d17072580b00c034010f4800909220541c2c1d03180b80c40705260300001448000494200115030b44404a03401904261000c1c103105d00307000c2e031405d80e03901001e440142c1968582200301e8420417010756102c080c0780241e41c0343c030080d2400b0901070156440400e40104410103c2240805402c0010307020340220b038403424842c91540c804200030442c0100300c6191081140c140000500d0721080c04605010f01199007035a03000d1214921103031804c1e102d90b8403c034001d088200410030305035080318814204c95800c4c000341d699155a40305180040505410410b1251060014400c54600c00700064090382c880351 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 736570791 1250 736569541 736569563
    0x604080312150d0b07030c2601290412030e13090b06061c0c050c1b0306070e010206150a2607080703050a060c09120f051501050a09090213090807 64
    0x207020b126810034000f001614140c0e180020a02c070a100f54800e5040d52a28903001c071040740e003001b0102c107501030440300580300d000303c2c801800080c4002c4411111400800c00b80c0e941810b4002078945070340118491381280345281c240f210305043c01021628040000104450000004003050500404102200b0b5580c1e0040d000021628140701040b900c02515055450703e8074020814154003074100000140d0800000307205024480404201000b046000b5100304124140e8002c181880c00c1c42c018400b030100a00745601100c0d0340d80105426401486209032246410301541c00329845031001d03448003440000740106440580e11203441c010a000b1f041044d00c50f099694440c09644640703d00001d000d03078200011580c0041c003581c0c48510168050704020404990b50480d00c5108030440405031132011628282408010040c4840d00c80340d50300c0070f10303400c031941030101144079807070ba41c01028001a511448003065584001003008561080c0300309101510b0545401905034018080c01c480b412609 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 736572041 1250 736570791 736570831
    0x90627030706021b040204080616021903171308030a0b010219080f16120e03010b12061b0c2407050f030406110702104a0604080312 58
    0x20440008440795507004050b8100c0d030f00c19404441601e201300c1030713100d5820000016150028000d051044040002c0c1840a6030500d40103800d08411032a03062240161031540000640c100303600100454500f11508100d41c0d540e001d08802185408018121260100401c1090302c1c180d084442c124200fa400e48011112048681071030f1200300d20700519260060185040032500d0324007034108004032001d8403001c00d44035290044010303e00301d02100010f00000d540c0003142024000c403451440c0583e440d00040c203803200c038035440d83c402034015021894480f8251840c082c554041e0390455101e20150340b03442000d8000e24040400884201d0006400d000c001034107240104142e0718408050a95245036a4480c0c3d44c240007016850303000b40007490180f210b80050380b6002071078043d103015900c44145120115142c03001032400f004a00801c00351001d000c510b95900200e401f0310340f42098420403049948480000e0550241d504041c0d00da12001c07601c40144207034000458080d03940300203007040441b0a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 736573291 1250 736572041 736572043
    0x9022a06180111030112080415030f050c0306031e03072411031311010c05010507030e1608030d0b0111030c030409110304031b08090a141f08070806030309062703 71
    0xc1e100ca00f0110034050004011498860100c80c240b948a0300c0107502d030544460098404001e10050304000a54942c07140005443e01d01c40e1607000203900d8510b90940c6480710009503180b5540007541540700c010390001d20312410410649802076804103403084141c1c416500b01d0700c041f5903450755400d00c070705100c029117006038150112800741448464000700c0800f140c40740045c10314141003840c100031038100280b000c12028032407140154407070750300440d407035001603452441d0002e140c5c0540e1401524000400c903a0304000304803500c1c100003000215002c0031540050341e10403100c041200320390100281d120484100480227206903001c018013040b101d0061090682140400c8800a011460b0b404c1d041121541c08200e5010080c4112201ca01c0d08402c403000caa0030100c550b01940d00b1811000710b000726440d248600341044444807103165840c0e4480d2200500d034400190002040c40405c002160b8103440610840e202c000000e05001d0703603801d290740303000040f11542c4400c44209884500c0c141031450 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 736574541 1250 736573291 736573301
    0xa030f11120a03080615030705190f020c0f030a020d290f010501050304060b04060909030905180c0a0e041d010b0f0303030a0f061805090d0c0c09022a061801 69
    0x9285001061000c2c42507900f80c4a080001e4035044d40500401e002c0207808805c04019403040705c06564075134503030280700c80801c9400381203045c2c4002e20201a020054940c3d0010718200221400c8507041e403a10070002c042401e01c510300380065004003516070481d060104100c1c03200740e0b2000d801500a0641c4184206454181094940050f46260440104100e61203840510b40050052400040f40c41c8100f000804841340c0c0d43c0f0880c0d001c0c0c3c40c1c86850060542059200d00280800c0c2d4950740400f9000da9048804040100740c50702c00c1c0c801090182034980b02d1140300c00381e01006041000341180968065400c0d0480c80b142072880e43c20410940312500b451b2490002201c0040c00941c21502c44484600103010f0071a0351266407a0f9444000510b05040c50b803101d40b44000c404000b0300b47c1802d00a003414060341c0d21980f010310101281c0140066004034880049503e00c21005807100d0070700b1880305c0040b40501007007181200d05c450204103088081045c0c0d0154070011118103e120360380c9251400c0c1c0d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 736575791 1250 736574541 736574569
    0x40302060f030a0b120610060e06030103020402070813123023030c0304140303010305071809081902010e0c0918030903060a0f050105120303040f0602090a030f11 71
    0x101801040c1c90a05040c000c1c503001480344101207441c442c0c64021654000c1004252500365010300c050010301d00d049030120300a00064a801c10f400b80751540403e10070301c41072100034000e41d40080c0f0602071010700c02c213840038502d50031185094103613142d00d541003ca0100109840350802c201d0322001412060322007a0000c0000c1403d9420301d000e03550141d680e880f9081098084801c0700541c1204092003000030751042d110011011341702d05190510010b44200030304e0b00d00c15540200010700202e4000070300b1000300c450005403090140c140c1c0c5603d0700a00743c812802032007050081500304070108031108540560002e58020883c0e0a40c00f1340242e80c800404c01d001d0b805c4404a00420304000b442c0802e0112520b128086900e0320421a010a00d01401212040031b00350b6a584550503441e500d005190042008940501c2c252025010b40303030b1a888007400040c114000d00d011581080380c1030301510b160100003406041e809540303003000342017920f01000407110540ca4062407002c1d40f6182c0d050200030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 736577041 1250 736575791 736575799
    0x807050a050d15150e1005090403050f0c12030c07021806210114090f071a0a1206030c0801020d05010e1012080d0213030302100e060a110405040c050a090b040302 71
    0x4603a40c0d294108610b840c00d5500340d4413034468101e0400c440d603c0d0021801090b01100e160301c9440c00e04180d007411074054000f00d12501c0750b4030510000c69408000c0d15800151448a665105001103003a460049079107105004941c001c020001d201021034040c0c041940261107130783d2264150005020115012294103500c503c0c540d0b07058007910030906441ca9003020047c00003031540880d80c86640c240034103c0724103001d580101080c0315621418001c820040c00790034800c41d0322005502e503080d2680078081070f0008115074240c2404601609030450b6000310740159565602c60b488800c441d000c0d510a040b4400052b0130709000140b0b0f24003a0003968880d00c65101420601307820001d04a00d41c20500c0782c1603511903800d1242203e03c00b80c42c8001c100e000d9140b0108103501c0d14514000e801e268494a861050610340044c0e04054503012400e15408400042c0c0001c80440e44202407400740582d4014642151130504076081c00d0750810018106141c2c991590766406030b82d4000300102d8415808001c0d04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 736578291 1250 736577041 736577059
    0x31103100b10030c020c0a12170405010c03080a18080c1506031002091305013b0403031e0e07050301110705070501051b0a050a200a030b06030304031505010807050a05 73
    0x80d0500c81da10a0b41420280e10541d04070060b14130000c2c0e99000c45402848c01e0004520a10007005203141c0300c0c8412100c0503284c03a044ca0314000010b095000714000180034490110000b400e105d01c150301c0306018008240082c3c1c8206d1082c01c1101e602e0b04500e0025456100b1440078002010f170940b6003c2c4200001001081c0c54110b0314034000103034010886d505e401c06841e61000001494500420303001e00410300548410103c0030b03801e40213400503181110300012982c4031085181c81140050f903407050709814045800101075500560810074001c40c6a42203103410200d6080710b0000c00d054040f0f52040780240702d08100151441c0b040d2060100c014050b0780819010441540541e026040107000020403100060481c05118104132580d03000f1112a04001100e504210700400f0030440120900c1c902e90349807100c203010030781c80065400003406150580c40050110b680c01c10868011756809280d0204c00501d00414130003030502805134510070b020f4802c0120b001d0a29101010803102e0003403104013 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 736579541 1250 736578291 736578319
    0x30e031006080c060705011503080a08011406030609090c03100203010f080304080307121806030207030807090b0d05040203010f020c0a0b07021b01030b0102010615050703110d020d050c01020403020901031103100b 93
    0x3071341d94802d0404880b15500d4403c21005100710469900085005006190743c480400d40014001c540503080005c041e10040c070a10b07029203c81701030f02d900120540e521616500e070900201d2900c0d0080780116814843c441440c03200c48803640145040300d41c96495004002d840e268415102e000c0d50103441c007154414003a400100f080040440c003034001c01d0900490085000341071841d060500c1d0000340200f60001ba58004050303011340c031694014a10f10f0304a22550422020741c0b01c0e403160010302181c0d16100da01140a5603429071003803031541d0461400715950412805040d0b200c00100f0820f85400058400061701c260000c55404042d54004401030f11515020b00150010101784002d18115941c0d01d9001c114100300b411102481041d40d107403192150801d10f0000c2142240d0301c005452038000d607008840040c4c0020710503000c00480c0c28200d85604601c0c2c02140240580d50020f903100c00360100010501c8010081021446002d41c00e4480c403124040e110000d031841070255a401c052483c000707807 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 736580791 1250 736579541 736579549
    0xc0703050a08040c180903020f0703030f0521091f0506010206010302100512040b161b020906060705030d0506040c05091e0a030b09030a11070e0402041107050a030e031006080c 77
    0x1540075100d13540000149803203042035000640340c3d0308400b00e030340d99911845040c503404004403280c000c0c0840042a4240c11580c004041030310200c081410700c40e0204882c0b0742d9803400c0c803803021000c155002031500c0b8035224800540d42c1c40c10050070350101800070b90304c28603c020b90090320710038141a0001c203410f910715801c1c45880003079502d000003007103020f20032415840401e0540a00580c0144404880e40c20328420716880000550419070a2041d00785010824001c1c02166468a0360101e91091007a510b00010445510403140000e00d5404002a8150140503552203180142003c0c0d80801a512120701c050310700e44601614250301c5082c10303000b017043c18180e8030b91243e90b40b000303044a070a15540c1d42d1004102c28084d0b40c110031540011950700d40f11940940c0702c08103120007038003c02c0020714151086010f4100544064020303920361312b0f28580280038034122120503034000704030307100b00b82e01e4103006010181000c0094868000c100541050201500030300702a0381d1410054030001207108100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 736582041 1250 736580791 736580807
    0x108010e0112020609132c071e030f0b01140a0b0d09061805061605041a09010c0b15091b09090604150303050c151902070c050307090f050c0703050a 65
    0x100e03804541044041010b4030b6129601170319406521011400350f541240072000101ca50442000660455520747e143c3d2000048810403500c6c112040600100411451146861103400240c5407001b11402c0004101401e241035040380d19102d1500e050352450300810522a41c28821450074200902052803190460352007181180e00c144800946021a1008804c07010701c0c10400303450680001c42000094070200e8040450902c3c5442d046290904001c01080d5141c0c207460040401d0001041e0020035074010141150041e03004590303401c4c42d03d8407010244210485010550007504800c02040000c51340d0704200300540300c101c8515061000e11b00500c0a070090050035643d02544484400d9000001c0a80c18400703140690b844a81d100b8010100500d0030003414902003c022001c010010102c44a041e00c0a00d24500311000d0f0392030010b410516403420080c0c200d1980350265180c00a101e072032a911444403203042c1c540c1804036a4034561070440074010604050040742042102e400c5203403081c42ca03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 736583291 1250 736582041 736582043
    0x90f090f0902040f0c0908010c021e150f150406080d0f03020403021309031715012124091a010c0206040b030c0d06140d060c09051903110108010e0112 66
    0x10709506150005001d03511000c0a03140da00f6035034401000003543c0308040d1405000c1103402400344c0c141c6907a0080d80c41c40410650100303090030401200c043c80c2e06006102c6182440721540c2440e040401d4010b20000c020b4810030825103081c0c229405a0034140a01340c101c85040f0050030b500d181c515000d50b02000181006003c0603802c20000c001607071072174029440403600081c0003810051600d0027a00d214070f10343c032112100f4040030410100886010038009440320a1904800700c01e00820f4400741c0341d00c142e000151041c00d0686d00311401180c28803400d10102d01c202400030701d6a07610b451408031031400130040d00555040141161fa54042c82c0300e9410244054040c1d072603c1e40d10030088403607410030f541000c41648001080c8080c0e01843c01410b02a05030140e203040d040d01c280340000c25032205082c00500050701d034040c02c5640c50150140500900000d000c802011104102c642c81e400610300040f180c00c07001c04c0d50342c00c06502c07a1700d240341071710031440403110b19034201007401d400d030014031030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 736584541 1250 736583291 736583321
    0x60405091903320301090b12060121020d050a020108010603021c021b0307081201050a0501050307030b01180303050d050a3c02120f0f15010e0301270b07090f09 70
    0x2ca21000c40c11009045450f20719500740c0142c0701e5041c80400000d444c81207120912a40400f290000300050204507e41190209070046401011580e0160311580300d1000207540107005d00800c0091200104016021034800da980820342c0c2e032100348c194100d02803e50941241c09007402c40d800c0c218800c0d0b00400fa40400512001c0e91032560500461841e8403404003104d046001160615194013070701c400c1030140400700c84000070701d41064002060340c0001041d643c1016200e07900584141d01601d0600b40b80403d81c0001c3c003480d600c07400c016025600c5804071842c59884c2000148804072207106a40b98009160f82c58040d00410712040003038030281d01e400c1d2071032401c2540c154a039602588018081071030b400c40d00c0441c501d030100e28806804001884030801c09010001c0052002c05103040385042402420000d200c101c024011a00400c840c1d00603007281044203601020f07203840315460455261042c05841c182d0b6507081021a12001280325516034880005024800d010651300240d0311014201 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 736585791 1250 736584541 736584587
    0x3030b0631030503040303050a02070602010b1309021f0e0f0618060d060b041701140103080405060c0f0703060b100e010c060507031424060301180230060405091903 72
    0x140f12a0300303551140d8011404110b0008020700d2668050224000429580c0000c0025403003910110b204002405041c0d80346076503441b00c050031551190001020400200c0318001551541c4901926032152901c0147c412a07101c522140f8910340b000c22140900d0314080d00b21240d500e02401d010300760304015042007080c0e440e0304022500c0c50340c0001601c0201205854802d010411034440c60840b0394417000c2c2d803844050100180080b40d100811542191001e98030941e54107000c1d034525040c04000301c4030040d00d0180301400818419141c0003040006412500130b01030440c03582060303865244c500c03141400700700319100b034002213800c079489143c0c8001070381030210702258042c455144054044071038844900d04d03915031182c018401441070b2001c0c80c082c1c1d151440c5504011a124420111324204d200040d00000c0041c0f0030101000344002d82c00d22201800841102080c6901841d102118514025468100040c0e15840e0015052026000724540001e0000e080d4400701d49402000c0c06191200300b00d6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 736587041 1250 736585791 736585793
    0x504080702100c0b15010e0102060405060f0613060801020306011b1e03052101080607020106121b030203120414040605010c302001110414030c150703030b063103 71
    0x1810007148501d20419003c42078144450000d0128001d4071f040c42c0c11503100c1c800b0000007540028259410001c9101300f00126031310fa1000039054000c50341100340c1c0da810080c0c0094285015000355014030801d03202d942c4030391001683c007800c900645d000035084503d030102107000c03d60000400c15150f07010385441890051003069030014000400300034244145d0300401000052270038000f09420541030710091200914064441c80030004134100902030344141041c0c0c241007009401720000460b80941903c00541c0c0803242089150468407501c01e0403840c5004020040c90a8407616055903016194005662160b0300c81d80142003211840115402580090b10615000d0004120480c1002e6407445030481c46050b4400d40004580c030070015580c1081040c4800062681c00d031402d0350440c01c22400000321042c0043d16140b00d034420319801524400107880f5107544c030700c002c3ca4124000d0f04d0500c80c00042e0030500680b44a44846588000b00c03000ca00b481c2a40d404070000d2080300d03110141c074061616 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 736588291 1250 736587041 736587053
    0x102090604060507021c11030d0203040609030201180f08031e04030c0605072301022701050307110102040f0f030516030b010504021303080a0c0b10150f030e070303030b01030f0504080702100c 84
    0x69242d069801c890810021291031801704103200030270410f88041c6050624240c000342c1210340e1400001d05112304020b0303c062056202e507400b801403c0c100c40082d145641c812415842e41d01c00900c0c2040000108051031a51003410100d03401c0700da021000c4d403640b0349090012500398200310340031907440080801c0c00c14500104e61b28848991590030005a40318401b002c403891160111b564029100e0105c2c0540b0301d10b03a0040d054a034410070740d0920003c2080c0c4066040e00a04c03550f000101c0c1482d0804001c10b03407511191203401600d20078400c03901e0041044880350350180461000074021800980140100d05180d009014206d07071540c002c2042039101d5840360142e81003628030800058880524000b070100f0a92500c0d000100c0d0703880030b29440e0034088520608100c080c0c100d000c0c004c80c004180c0c4104d110b603206408010b002000c0e90030b400d48030720303004001e40f0620303200e1781c0000d08240e0302001014991051500881c0e2101016281030810341c2808001300f00f2203440d40a10103507208110102d62 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 736589541 1250 736588291 736588339
    0x31015030e010e0d0e040506060703030216060e0d3011040f170c010815060a1419020c030c0303070b1b070605091524030f0f0f0708010209060406050702 67
    0x3403d0030203071a040070444d80040c494420890100d125505010030b0060544811040b180001d41628000d680c40d08014020310f0401401440100801d00e02000c4080c401c2c00410391550541700d943c1c501340704a1041012410f6050100118a403800b07030208220040085640803c281044198407107040c13680d44c0302c0a01d5802040e0344115a1000140c240066025040c0f20100b0120001d00b0004480d05060b0900380710b4510041000c0c0c082d840019000d40540e014040400420000c1c810513955070881c40d01c1684410102440d51002d0321031981000b1861801003a841c0740c4001c09401035080500301c0e2958400030b0405422181481e2502c90b14078050b940b41ea0041c0003d50140c040850039080284e9018078101801c0c1c200740240404801348411021102d19440b85c03960380c20300d00d24440320050002410000700b400010640e21401810002e07002d4040f80d84441507409406994080d540c44801600b81c1c842d0080130741e0b12820400c000d00c0a1400b80c4e0203404600c2c000f52410030b07108041004090785c03071 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 736590791 1250 736589541 736589561
    0x115060201020301410a0302090405010e0106050901061704060209030d09170a08041e080303160e090609071d043b0619020f030f0714031015030e01 65
    0x1c1d4001005016135046098100c1303081107017004031400e544000e641842d400c80e084103091546405a40d40f0f003a60f0361046581000f55800520345603844c205498264000c16584114140d9075003000d00015851800e400b074103040340c0c04c0741c440003010b140e00c508200011b00c0c020401c0340d100e6030030302011450f44c5040001015142507621181403607820140e90785210110b10724956010782c0030040104c0040c0c031003001c0d507045440e800200d21000f503483c290045480078940020f0054030001c020840c6440c003000055101401da911901d50f075100d28420301008640c100d4091381c102c241c40c0003007124688185401030000280c0c0640070000e81002001401743c03501c041c20f0000052205010103d8840070b24805642c201c1d410700e100d00040500810380ea1180c070001d10341000400a566440c4003911150100c80e030402d0501d1420784e50f89071217003603c08194800d9500c03500182d032149902100204001c2100c0c003510181005d03080c858a4041152103890b1035001c2e003010142c5030810410228001d01070708041c4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 736592041 1250 736590791 736590793
    0xd05100908130f0b04050d062d0b01080c1207020a0c080a030e0f030709020f04030602071202010b060f03041221140a060e0115050c0a06020c06060103060e150301150602 74
    0xa6040c0310b001490340d040b103400c10211940c0f00751003001008205001c0764201c480c151621704603c042400c0070002400c0c18508100f5070804c03010380441c4004091461241d001c02a1000c20543d42010700442d4011005c640824a84004001030a204104500d0550b84005140704580041c06075955a07014a042603001c8110b607486a950402050340004500039a420300740c80c201000030b00000025940d00c5140300f007008150b40090544400c40b48034049501541d00850195a03c52051820100107051040d00e1801546442e50314080c0b854600c0850f442d015001030000c1c10764445446820420561038802c1d41807008824003a00c00541400c040601d0607404900062a14003202d902d00400d0340080801003180c3c07908000b848000421101306064074020290b000313411515500554103403080d031081410070700c07075104c3c002e04002075a001020502410030503034940d521840015000c0d10018010000310492401c00070b40074030354032a0528420f840050011862425a1034011800c403059000b40f001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 736593291 1250 736592041 736592047
    0x615060c050d0c03050d0504140a030908060901090209190204030f11030f07060c1403071a01060324140f04020a0306260c220507030c08240d05100908 66
    0x2840424880c0841c10086424100002d410560f4000e00901c184046c600405c3e0b03952020805000c041d0301c84006041c00201107507200616402c0c05081400d403171040407001e2081c1000110f0300e01d03060181d00e00c100e50152840c2c15941310701d10310107030004441d65018000ca50034880000401c042080d03420400b4003905061140c07081a5041c58105000d01a000304240d100c84000c1000991214690301003a800521a408c0e0304c1c8040ca2040c11481001c001400c1411507214407600345c840400b00c68101d03070403134a00f00700340003680311040190b00c4991221441140f500104014202c803a4400340e51a0700002c0c642c5184190b1080000c00721b8010880c1c0c01c0001e541c0d030b04d040c0501c08c0b003c46a49011505003414000d14010059180d50350341d002d4220b203004444c2980d808070042c8a29028042d010f414280a0082e031030482d0000700117103881e590b010001030840c1d0110b2650404503c07003140a02a5a401044c0e480c0c44106020f41d0300f85444086070036203e806580f14800c0705d20710410690900c9a903125503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 736594541 1250 736593291 736593293
    0xa0c1202030d0305160c031e020609070609030302070b0d0b0a080607030f0920180109050a18051c05070501020408061501050307080412032901031a06030109090615060c 74
    0x1262114180049040c113103003005000280c030f0049500a00d9400520384420355488174681220110381c0e048080c100748404000c9654056000f207000b40c40750400301d007101c0c4582c0e070b00c981c2103941c6203140c80060051380100c001440014280b60050104148083c408103100f400500813910040c03d546c0072454542210007440b4040da81400f0b2501080c02c080d03414400000c0c01e890301e802d00258990955854030005d2560400342d12942d0340d51075180100e45503109950303900e10810300a05011200200c03031518040b10401c011001403070810200340c1040082401e000740740e050081c891700d5614070205012080c07154000003082400100040c1008501030a02420a0f01d090740c011290300e844141485401d00030811182e0340104484d0740960440551419420201001d400519088034180703160040d92041c0c40181001e440c0002040303138282da0800200103808440080e100028004543c0301c034007003004000036903554000d1f00d00d080c000e03003000400d00621402c5080c1405580c0c80f00c00032640c000e503400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 736595791 1250 736594541 736594543
    0x306070c0516180c020a0b0c070209010f150e030c0301060b21010e0f06010c0b0a0b1519081f06081005030a020f10090e180708010b010f0f020a0c120203 67
    0x40072504201411809a03801c0030020465100b514101c25040c50351000440b0006200b04201145540c104d030380113015042c0021108c403698003890082c0d010310560f0000082d20f40a1581071000c50b0341103c5070030b0040700c1d2140100c4082d200030031a65810f10802c00300b20345a41c1d083c82000e0041c002a1a0141d81e056000441000c0190b21509813401200324001007020002c0d220f102603000c004610365062540d02c03200107a8424455031402f03009402d21a0402451070242d40c00030414400480e16280d0700d400c48420b002c5603204000300110400c3c43d40000c0440315008801c0d0740e8011030f401c21814000e12010600c003495400b40c0d031000e400103186009210381e00d05010301200290030217401034600010700b600461804410103140f24050100d20760085601da02c01d0044030080c1c58002c1c8801c0080c1059091186d0551130320305000800e00031118001501141403242021028060311140302030360600d042aa2440702c00a0300d40190301a900788c0e00000380c48801600c0140641c038006151400c1c2d280181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 736597041 1250 736595791 736595803
    0x140c011e0c0f050703020709050c0c0c0f03030409150914061905060f0d1d030a030b0405060319020d0c0608040303060602030903060c0306060d060e060103050714040b07030e0306070c05 81
    0x50085249041d4418500039800079600d8041c01140c10705580d14807003031408901d41000741e40054600391808041c00351404040d8000e2500031601c10032602607110220400101a01c01c468007a40350384200b000304107200554001000301b20b11401d002050980da0030031041500d49107603510904804d000e080004c3c43c5800c2000903001d80020360840e018034100000308000e4425020701210084002c1007803407060b00140c1242d106503562a58004c400c03021443d03501c2d40c0707400950401c00400e05002c084180c908062041c244034403401402401c15041098048890101d4890103a800910002044010036003030300300c2c00000d00c40c83d40d41302d11900e010300380142210410303080788003107410030407045040d540c0009910303400180c41450b16035a83c481c000001c4591080804d10104141401e40001e194034840c0c04803445a6420307241800a6039400310102c51540892464160410040c00140300c0d400340040604821446400c0041000c0c1850340080e06c2c100c3d00b00da00200240d002920001003100502c10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 736598291 1250 736597041 736597091
    0x11103101d04030212090f04090b0a05130f02060714240c0708191b0609060e0c01020604060c090528060503151210060f09050c070b040210140c01 64
    0x2101031420b156030000d4840c813189460080641011030105000c0c0d032050fa1034400c01c14018010000740402c0c1c640b00d01107080450350044101d2400b0b002070503800324000c0e644400c5038050b070144e04581981d030800c401030300b0840d41610140200b041d13804140c07808002403061074890248807503101c1c5000c1c151211a40004060f40ba00c05410700140d0009150304007500e100c0040098403100d1032180318001c817400201c440d070394807a40a802c410141405050707845410064000d402c10b0024420100301c880e5140c00741020389005a00500002d400b181791580078251040040c50410030080c0d0f658006040c12101c18800044510071081c0e0103588202e1541e11402000345040030303411440c100b0513420703096458181041c0544070b07505905054000501103180001c0070b40a00b0084551503041c2d46082c0136140c024041c15900e0140450200400301007665a281d9000301030fa200da40d281e0b800d01036008200c112640c103005959001c85003513214140501070802c2494000a40c50019100c00c8207800440a0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 736599541 1250 736598291 736598339
    0x9380603030703050406030b0f0915010306080c09060913050d0906080901050709060c0305070516180504080717070209011503230a020c070b07060f061508041401110310 74
    0x4400000f07a0040e094608694042c140040d00441807800314089294424141d40d01c50400c0c42004254647c0d2010341511980c03e980c10030901d0f8964600590320071014202e50342c07001c40c410028a5910f0f10b108520f40c400c11088070503440b10565528186403000030700d404008105140010f0005607805842503501c5140c150080c019030800c40c02c054800c0115020711003c1020075403140c402d05010b14100c5480d19071240484200d0488400d41d001015003078040c1991380121040c03070309110540303402224040c82d0004181b615000d19a56000e102c1441c002000c1d544030000d2150f400136075501c0170303818000c04500c020301105441c0c194004040310385104400e81e605604000000d001c02c2c0c0c034107074280e0240300d1401c01a680c0302625000f0749844816070284400f139000180001c204241034100240070210604288001602c0e9500f020070902d01b80c0c0740300000f450360700024002c1802e0f4021003000f04042d078000101405e80c4c01c01024076910450311600580700740c80b41042403518100c012003840c18105 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 736600791 1250 736599541 736599547
    0x101508010212042904110102030c0304031b0803040608280e0106030c05040212040b040c080a030908070f05030303131401091a06060a14030601030617010e2e0938060303 74
    0x524840c0707813601070000352407220f0a4504074010390080089811241c3d035031007103a8845503603182c00d41d910000c02c4091021141c0e0b0074400904010000262026121345803070300c011995414029005044000440031111600043c102d0701c02c00603840703808940035140b40041401400c1d410542c0f000c5409a202c2170240e441009030b844043c17410400107030803075400581c0202548403420401d119140a4001c0b41c040c2c0903d020007070400d504040b024045900410548914542c5c4005900c4582c11174421560903070420800140c031580803031400114203104441e01d01c5100380351002d0705d0868400c0f1208542c0004a8441141e05d07114040201c1c0e4050310850f9040d1812424943c01000800d040310f403440302d4440440800c081e68025004840030745a11b405040d01c82000080ca00c2c06060715007003411050045483d484000128000300000f81c0d2003170520115000c174801d0300140208a180000c0c0d030084800380c1c0036401c0c5d0300030742c03007080c3c05240c41c80301c140b05160341e64021214040003a080c0740c401c1e4010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 736602041 1250 736600791 736600853
    0x2012a0606080f0d110c150706060b04140901060819090501020c0a0507050a060e0d050106030206030a05071b080f13150c0308090c1f031e0c11060910150801021204 72
    0x48280035008161907d098080c4803820040311f5001e20030300140380d14104407010846030b00300e2028000300c1d004550b141040b045010140302800000303014110010703405800068015460146005007404a10701c00104400140c07281c07422600a9802c000098102c098034400380070040005c10003504c0300320b5980c1c4403149030000141c41c0900000082d0b010703c11554942050040a40c80b0000442d00070b0301299072813074401a4507008200c200d0304030b4080703008200c1d55805540c0190503000e00c0c5a0052196282070703500a4400401e400001c9600724181c0308800103d00080500e401148000454440041c0110a4940a40a5a4024080307081640040c551000c0365441605200c070011800c51010141c640c840c0c0c080f80035041021804440706040e0040b46419500ca03030090204d0466640d5221824120030310700741d2916410b80701c00016502500c0392501140d040e51050042c00c5c8400342507501603503100781581c260703004072080c200d060079030a040201740855443c0c048107900400803407603500844 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 736603291 1250 736602041 736602043
    0x40503130618051e04050714041e17151f0b030417030907180e1504050106080106060c02100c14031801030603030203073804021c02012a0606080f0d11 66
    0x11301341d00c6104646480c0402c0c1d030381d401070302501714008030141420703919a20b500386085c070200080d442d02081c20000d41c00041e10208072101b000f0451201d07000e086590b40c1504110440c18000d0320605644820000d01d00d0032000250241004004614415449183c181424001d00070740d041c00d240724500800410241407008580d19065488141c88021411510704080005042c1a03018032007512407022002ca1a400070030031030740b10740e03c03420003407140d240c50340a8242030303d82610590700454a80340c408001841d240c1000d510f065090301d0100c5c03102d01c9588807400001061480c004240d0400034102ca000d2903800304112804100b800d0500209145540003561ba00c114100030b80544241d0300e000349421b40d00000e1884601b140501100c0804000204140c4000d066a040384101400f2020001d08030140d410881074980584500390724140c80c0e800030140600c079040f0180400c12031400380300001d142d032003a02c010b828150020a1840c26501009180100d0380c42a5014884040301920301c02d04 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 736604541 1250 736603291 736603339
    0xf060513090b0c1309060602100c030b03031204260304031818020a0e03030c0114060f1c0c080118022806120204051c03090e0f0c0304050313061805 65
    0x55550700e410396510139001200780c5000150014945c1c03505004002400310360014144c00350f0a83ea02c020050101c560340b0580c2120880f003d216015007080c400000b196801e213411540c010b000300e14860640701c0489508040904101c48612488004000d10003810383c17240b803240700f00303907000b0401c2e4a203401c0036550001c0c80e03211201001d0050f00040e600403c140316409050002130007404594440e00c0700c0881318082d0000620780307807840036000001a19441c10307542401d6100000740881c011246030384681d240130918031005403036640d94181d001544030024030034205203181c0211900310726425071041040307058103800c0f400c514040c503000d103007800e220500300c2404035810f5040010080d204140248040c0c00759600ca26400b903050404112144c4101c41d5640c00707213100366102d0a40039140c034494540c02405a880c4c0700f4038020040041c842200c2d000085400c54050b004584c10082e008880e1145c4040c2d0750000e80005088404240703410b01b80e4806c10b00a03100403282e01c514808500400d0010130 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 736605791 1250 736604541 736604551
    0xc070506060d050a120207080d0302040f030201030c170406090218070e1017010803040e0c030415020d060b13180b0d1118011410030605030a0609020111010f060513090b 74
    0x100000c0002e104004080003c0204954442e41c5100414a00f0401079205c8074148210420b5000d10403920217298400e00c2203e00b50f81038410030350359040c02e58004400500c2d503580305070284401c080c41d5407100240888243e101d03520a003004680c444151041c40240150340414803520030245082c062805e401203045004420161021015013101140071101c202d0306d440080d1400341c5500000c9080781c0c001c00104142c0d10851401d104989031035a402240344800c442c0a40b20a02c8480c90f0038861819070000e0411000640d80070a580e0f407603603141d1100d6400601c0f01031483d06103110400c9102d5031241c1035508000000410008116245c0110344c9111000800600303003620b0100d2401140d83ea0030003c0c6030400100c2003a28a0f607158250b240d0031000e00b0340b10b11300c03c2c2801c81d0602d0000384240100000d0350300180140405000d9a43c3d000064505001d041303050043c0301903111142d80091241c0c008a2400d0040468454a0030081c4502c00251610840089045c1030324200401c540c11003140e000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 736607041 1250 736605791 736605799
    0x8100504050118030206090705090c0403030f051218010501290f0d090c0f080a17030a0905030a0c0c2c07021006030308010302031c0e0f13230c07050606 67
    0x26580d500d841401411a1075500b080c41010f401e071038082c5030b030000d00300d4854a103120480b00096180e000b0440243c000700d46034103054404000c140300092003040c900e469440c035400c00b981061042c840c544102c5c8400c4960fa90980c09501c2d50749420ba0090081d10b004080508507c4003143c14000d00c01d006610500344501d83c1040002c0d1090107010700012140200d071054010000343c011403801c14681015031045540400780d10f0008940b0210200340440030303684c0f016900384441409082d02d84240c1000b0702c0300500e5940c0d103c080e4080354051005044000701b41e50b82142e64541361070036104030b00454010347d45500d001d214180030308020180405025096000c0780c8100c2d41e618a089160410010b0200f08a41c1800000420035070000380039810b17a442141035608856204003a0301d5251407003540c0c880040d0300004007911604003c0855030780154040e02d080c0902c84c1401d0480c0a507242c0000402201042d00c01e20344040304841002500911540364045c40c0c082d46440d0705039030b03200140247d889 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 736608291 1250 736607041 736607051
    0x60702012102091e03030a0c03031d070f0803190e240306090606090f01180308210108032d0712020106030303050c0405031c050c0f0309040606090810 66
    0x15607014034014051400d01100c090031610310400c100010b9080780c00301d1400351004043c603840c003058146185484040240055082668000040b1044825120240c060650b110385030f87c3c3d80804c984c5102c1441c035902000302030140c07500f803040d00d0400682d445440300d90000d001d543e400d0459a401c00e101d588541c0751058025200380f00090311240140c0a40d01d400d500c07125000900c4a500b00518421081262141d000e82e03104010700030f072271144c0d5941c1580440300c0c0483c03646560103400b03446031680da010b00c540750068881e620002030303501010403050112520100700000000c24100706000d0040d840155003007580303400310032100c8200380c002460314031100d8130f485000c50005800e8420f1140c0002c40402c0e901c80b1114040e0003041e0f40d0000b1750019003031800060504503410102da0866101800507d08002e51160b44403010032150700c140204071040207140c407212000c100441c080601000a9942d03100000c2c00c10084504031f900c914140280950100010000440c0705130246147c5840450 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 736609541 1250 736608291 736608293
    0xb210a060e0c09070e090a021602150f0c03070203010b01020d021506040207080a110c120a0803151816080c03010b0703020703020603070203040e1305071214120306130e0c0607 77
    0x300741102e01011030340103da50001c11642c02d502040c50f5a041c0d4050780c00780d8142d15100d501c03034240e200e101d4505c14940002094a80181066000180303080b5204c40c400342031101c90001000390758406444c0b50b04660010802ea41946004e205541c202c090074002441c400c46103860194403040c08942000e0001ca000c0c0003e05252519011984001e41c0b00a000d5555005a04040c10038000080003050f03500c1016039242e403c0c104a01e0700d100d2060110028083d0000c99600c00c00b860b40020310050f81070b041150a414039886001c2d802500603003810000209242c1022000058408001000c04205010007400442c894820803213054031241c0794001d50700d03c91410145e24184440e480203411140000820200761b50103c040e000b51080d9402c0c08001d40c40b00c01c0342004031a1400d20140c21900810300030070103281500c1050041303520400c14040002182500c00e410121880707116002c0710303000401c124080c601030301d00c200528002c0c030702000840e0003040c1060742c030ba00700340155000b0b40c00000c01c0b83c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 736610791 1250 736609541 736609543
    0x30606060315090c2d180307050d050606101d091e041407081c18150818241305030324060412030c06061203030b210a060e 54
    0x5400d020080c14022003410304c0c0007090b540742e00050f080110b51501850191103900c0b0303080588100d85413a80d405050055040780345446e035a03a0400e080d032606c1245c030001500d0b11614044030b001c9008402074403961a00d00c00740b09003405040312440c20010500c5009421010b0f0b41800441da44090340d208030b06680c0c0e001d4000345000d0318055510300074094010041000300f0321400c468601401c4007035400107030b51030642c0c1c0c1c0c0c3c5d039441d601046100000c4015030240e01d4410104225401128140c030151a552a0382100c0280ba51b44c89940001e54180c003000783ca101c1c001d8003508009280b9004029a04112407141e04d9245d01c0e0903101108058000400c000f04200c0b410750403c00d402c17a058980d2800c1214a4102481c8640d0810000c1154400129200c0c80c101d004d83e011a8010304003402500001d40d0200c0d42420b00f640b08640c44c682c1c031000803407000300241c92002641d10a8400081041844081200c010700860601c0e86814440000d182e040c680401e507003441c16481754000c038284007080102 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 736612041 1250 736610791 736610821
    0x230a05013b0a030c050418240915240303020615041b05070203070b0f031305010b03010e070e0601020102030c0d05130c14010314010f030f060905010c0c0b0f070c0f1403030a060807090203060306060603 88
    0xd000305000300c80d054003804041d0711070740c0700c10105080c0c0c1908000c040c20607420b8520520cc0640560002000282e9001d04110045d202c030000810001d6001c1f9540084001c2002c065000000924041401c1e001c5050420030b00028040140c03219051208a44002449120007880d074090807021072180000c01c4001d4205e9442071600400901c8600110034005641c2c00717451040440d0440c0ca140411029401842201d0044080810403480c0000c07072800400030701400b520540b034007188689001c0100380c000c2130301000340c00000c2c0811903215108000405a640e03007100b440d00e0340800b20040020545c4280c4910840c1d502240445001c0940c3c00c1c01401440d5610010f04203500300043d00c15096031100904600500c502601030007511420841c041e2000b003214100041004443c0b0280030035503ca20303640400c1e00c1648a403803000920542c0380d0840d041074607a6641c0b641c0315170040c050303c10180030400c0604607068086080d80f1b084070000b0350315240502480d00504001001c40c50340341140c595 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 736613291 1250 736612041 736612043
    0x30f0c081c051803030402120c0d080c2401060c0f02061201030506090106030506010e091609060f0e0402030303040813230a05013b0a030c0504182409 66
    0x20644581503200c07040c0101a031a20034594051030706000803500080b4003400c40d80b0701a100c00450640d40c9550034402c5c0c405542d0b401950782d2042020540050fa90036004500c0c141c4103d0440b0b03101c0f8860b6042d641b402c00d5a81d44d1a601411140555030709210341d80c0141c2c110390f614076144402030f011307003001d12380e0303601c9103001079044800040d250190440026415040324812811100719941d01c4400c039080302d029003c01000f682101004100c25100c01650b0368004602405540b02c290b00780a103101d00300d506070b00c00d40d02240c440c0d1042020104524031000209607050250700c041c50651300094407444010720060600e1804164245510f00030031031003024100085c0e010b4030030310034004c46071000e21160725100c1c850b801ca040d012889500c1110000e680d2002c040e40c0b10030b0300300205030600c11b20100000745c2c8805c204000c4191443d07a101d086010096004001c0110b0881c1001c0900058660307003006052032603244000c2e1000620703440c0d08500e03400c4820000200c00c40503c18110040e280141c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 736614541 1250 736613291 736613303
    0x180a020f0705010b03061003080412083601030c140c0705030a0f0b061c020d0302030c0d0809010c0806030a0303020a03021e031006020f0d12110c030a020601050a12030f0c 75
    0x109401040700540c001d14141000700c0482d40b4613600c4107265a482c2c041fa0000400105044c0810820020301441c0074000d244682d507042c1c14200c45094000400d26115a049881181101c400340051040c0d10110940d203801c0c88c0502002c1c2049201030002c503040c91084c51164400540c030181501c041c041c1d0b40c068040103059900a0303500b8185040f030b418103014103580450110b0042292860003000b10590110810004150030055400304003080d42e01c00000d03800e43c001042806900b600900c5a002c4806503512543c5a81c200b00d4041421034403c4034000062040c0402408203d5400082d50080d40da0f0510300540e03103031a80d0340110041d0146074920200160b000c90304c500c0840b5050080c6103e45601902c2180440e915441241c0e90900c070301c800b48840e00030001601c640e41c894101b4140181d1034190202d086100119140138542c80f001050b1115000441c40c4140981e040c401607004100c1140c547c49240d040160201480d248140f005050083c3e1148107045207004005000d46150062 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 736615791 1250 736614541 736614547
    0x6110c09041a271c0c020109030501020307050a14030915040c08100218090606031803091206160809030a03022101030c050a080721080c06100303030c020c180a020f 72
    0x40b00c0490a280d0240004480b1074480a4032815030030300003648010450010039100e1130310046841658031450105003a410040c80c6d207804400b0410900003940110400d44c1c0d00759484120000c001c001b01c2003522640f030030031810418070100180019a00035425000484881c4680311490a03071400d040f50341c054500c9000d8241400d60401140d400303088250860381201c070045290301d08011104100310b518560014082c0b001c41d00800c011095541c60460920449103000e280c07000080008894802044099001d03030b017048a242d030948000a022120340c10b10308200c1c1401c1f0042912800b41481180805a010552505180038103068820b41c05032844091800e5850341881c4481c001640a418085c00c400200000d145100003404d80884284880e0102c0c00d4460707908008900c0c0c0484403c0d1440c010a104002640b1014040035015035015149242e50034691701c1c02400b1740711741c0c08400080d90400900070140351540000c1f540c020b4018242d030340040c0c2e10548030f1802401806018503e8100c04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 736617041 1250 736615791 736615801
    0x5090a05150612060f0a020a0207090213090b030d090b090a150807080903090a12020303120a0609180206030f101d01080f0a03020a060b0d0605090c04050106110c09041a 74
    0x441c1c1041c0110829103156101c81c140181c0d00d65a804243e50307880d20581848006041840d090780640900c00782841941d9046c1d90752a050416030700b1074041a81403568618040010342d00c01d02c142566814240c0103000b00051220b80608020380310b02c01e00350341282c006406c480c3d9039110900c41c1c0190500340103005038000d404c4001084408200c5401010030006008039203484800001d8800040c4010a03500c1d510341002c080d003042001c0384400b243c0501c8280324046400d40302c0c05000f485514520800240240f410801c0c03400da03000800001c0b0400300005140c0050f0f22a6801c8a80c405c807510301080f42a00d894031000352441581c3d226030104a68901e0705140400700701c4449040310800f6003200d00440c1120400754503a441c5200040250380802108000902c3d81e411082c00308030014040755110a00c4e49541003591404c07550000d1507003000090301520328240c4600740c0500401d01e00100002c114820350b5980d180c0c0c100c03880c2d10540c8008006000c209035000d01881c800b0b00e81c201d4106500b04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 736618291 1250 736617041 736617073
    0x603020a1701050f0105031f060305010e0a1203060e01060c0f0519031107051c060e030403152405191e061b12050a1107080d03110c1005090a05 63
    0x4105814800b94240004520300001e00785595060304c00007006400800d15002e40040007071001007120201c0341d20703110f00002241d070a1140c0d411114500025041c0b22140380b030880c0640041d40e48040a243c9050414003001500380d4020b03055515500308100502100d041000840c41092001000c42c07050030441d00c2035800d07280c5480ca0741c52103500c80400034810254100d441e48010f00403d90030000301c501081000441e0700a900fa8a0700910700014019240920681141d0154209a500d04c42003900e052450000c2e01c1240c11210f1031050240f036100c0c241c070181ea0004030503c0360b503103d00140a011500554004484001005507080341a00c031894120802004000b80c030500c0302050414542038034007040300568141c030a0340030b0307498070341c2c240711800984054201c03d00803010000c0380003158049800c200542030140c0074000041045044141005050345e02d0100110f103034400c244031101c003400c000a014070024a50f03d170017143c281c2d40d10203458034020080c800541940300ba00d50b00091004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 736619541 1250 736618291 736618319
    0x612030705100b0f1e190305013908070f12090609020a2702030a0b0d0c0f060e030c0907031118010f14070b0402031002040308030609010f06050f0a030603020a 70
    0xc0c1600c1141040240104020030719030f203112000c40c0521010b010b100a4a032019860740301e045184061b0385c0c0d9580781d848072401c4903500f1241b5030700e6a079500241d2002801c0c00c004105403a2085080004840820000410303459002d080c440038440310f1007240c248a40692050703d501c02c0c020b201041004034604002000c4c05940034245e006000c2214041084d20850707800e010b0000c1c015482d59000342241041500940c4020320190000b9030762b2000d4521303039860305461410f8501848507122500e00b0110035071000352095004405002c3c007800d42081d41e8a02007043d4800d403100311444500c44e5141031301540946030014981c10041000141381001003c180540f000c03821003a600e005120030900300c283c4450079001c2003000e04480c1130140c00c00140ca001407140d44184050182c1d42940c1000140805036003054004650745e0134080104076603030628032803046c018502c400003c51030381d207000c80280584c40340308100c800b00071000440012050090300170300c0c02181e001e44139066840c0e0320191444190 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 736620791 1250 736619541 736619561
    0x210204050a0509040201080f0405161206050a0b10030e120c0f06010501180b1b0d090303021203040c1806050a0f030501050703090b010510030906060806040506130803061203070510 79
    0xc0c107040c0100d000c1c180804a544541d6041c1c5400c003036078072070410714940c442c4001e204603658402e4150031503280f0160802e10006116250139000c64030020314000c0c0035600024641032070180f030a030844880f0340d116200d801003a40d480c1400600300c5c19442c2d9181c20150210b087c40c440e02130018844072044000284035403106030400075916982d8980c4011115192041e450180c0007142000510081030000014401c2c035030f644401000030000f42c100d03070303042117411003201000c030f51808410407e140e01802001d000c016041e10180ca1407400d9a51800503515900400040070740f0300510003c507110700d03845100600ba006001c0700d03800b5502c1c0e03002405450540030131607e550800780401c0d40799020380502d0030000d50106218500b81c0c06c1606001d40101840360b00401c140d03c0d408840c02241d06803040002801c2c0a0018000c03501d414145a4503000300a4500145003450b12140b03c0486c24400540e40c000704200d60720700a60005290f01c034514000d40501418500403244c2d001d000c61165400310b0052 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 736622041 1250 736620791 736620799
    0x90115080c040608040303020f0d0c0801081225052503030909050603070b0c150903040f1d150111030a080108100c0203190507150b210a0f020121020405 67
    0xa603900000007505000e90b1080401041c540000b29000900039000350402d103226003802c0e401d01e200000c20b001500c005200c12001b051034200188900d1134103000c0304600c807c400040c1c91501401031186009a91440160486013410182c11810040140003090500078844503e032502c100807048450030402d01e07c400c9000ca1820240000c0c2110701e0700a8a00c2500018050401c0515010300800c1607880381d5001c0c42d41e8012400003000c04144030390300d940500000c200540c0c580b0308102412032185016008454070b4441c0c5406118913028464959a102259681142140355180e00507200340c01d00d03a02501e014000441c100211300e90114605040b0f4050800300d6a01c50003d08040742244c06221103100160000c00841601951a8991105440f07091030f0030b82c54000c01e922040750034200c2d00650000f050702c421400083e03207028140c0320300c0c444443c2240c40001020f40c0c405507451401c590014600c000f00c41c820403e580c050f840b4100f0b0070300d20341e07648078501070405141002940305006542c89 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 736623291 1250 736622041 736622057
    0x2031f030818040e0a06050703020c010c0e0f0a0b221502010509071406040605031518090601050f1c0f1202070617010e0c031003021c021c021f030902090115 69
    0x24624060040f031521540c018017509801080d0344486015080082050080c1502005401ca07089024800e03004201e00e87e6880d010b554107001c0400503e007007002c2865205034010300c0180b0002c19100202d8044000c0e41c2d54480c1001c942004e154031421065100d03071300b01a0a4088a440140c064000324840d00c1d008040d1552581c41720101410032820903c1980c00500611080c8a028040c03001150860640c03210032000f042c4180002e14040d91500651907403280d101e05003c1c031000b080080c540500344c201d59101410101d10041800b10030f1a076034002d14084004004010301c0307401c001411031a500909158000c10700654080d58580092180100003080d440401c02c04401354101c0714181c0741540c8000c4560340300d0005600c0c00750006000701c5202000108000300503610512250010040b100c5045d082e0240c3e4010031410040a120225021703403540044030050743c403a107112040b03200c050344002d43c1da1220360040b002046403100094000071408000f05101c07442d407480d070f0000e034400e50355080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 736624541 1250 736623291 736623337
    0xf0403060b040c1d120f010c08090a170306041508030405121603020f01021e06010e0a1506050a050714100b0102030a0e06070f1509141603020402031f0308 68
    0x1181d40003403d00d800142e6520001840b04109110740c40507002c000c1035071426100440d2014180350068190461580d91102d41001c44e03074011541603440b0581d00b0192400d100d094403290000c0640a5400d0700480c000000100544da03154400c801e0400c00310554100301c0d460b180c04a980b54001c0c0200ea1080014619102c48198001054502c1d0400101040f1140e85503900340046070244549141c1503000303a5aa00395100c90f490402c070415180c42009103031551504408100d40103000d00100d80311428a0317a18074100c90035901000441760285040360303480f144c3d500129203901605000404040300c840b0142c80040c0c00141200080c0d9001d1000c110b458082c40041ea981c3c07003076041000124a4403182c1101500d450005880410302428080e8940350050b41c0e00e15001c4c0c002c40c585103510b995080c3c0ca000780000c01504c1210382c407094008050302d40c1281d1142045d42c69501c030091049030000300140030302c4401c00e074045120703003009000c0000c0c1e0345900d40080c0c0740c3c00c0140180300d40e0190f0350102c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 736625791 1250 736624541 736624549
    0x302011505011707110f012a1d011119060f0207050a15020f070302160801020f0f0304080d06081005101203080a0b0a0f0f0e07020613170f0403060b 65
    0x10445005071180c3d08011108481c0315090308000703004006000205140c810160018411a4070f5107a40400028044a400444260402440350705100b4915214084400590810b00020b0a1042c170040082c8080e203080048136025650350000301d95002d0f4085400c0b450300e5901c0d40b214103e200d50b40a102001030b1035100d900724042d680340500198000301c0300740042000c3e55144c44506440c0e80000d45011002c40d004007043c0e02c007510880059120440c00b07112440c0f0806460050400300009501c3d00210044038400307402200c1c046d007000c03074001000c1402c00c1108400c5580607049114144942681c03204940d8440107d00540314225080400091045138102504410745400700c90820401c00725031404c60744ca050092038030403040e68884e4008601d41e580c207505002061581c112651a0b4140aaa000403e2060740003280562005041c0b11850390003040003540444142279041e03414541d030605101451026600564040c000580d5030103038440080284240c2c0d000c1c2a0500078640400240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 736627041 1250 736625791 736625831
    0x90c030509010b0643140a0507170c0a0803040f1502151302150a02010c1106181f05100602030c1216060518011d100f0f0e0a030201 58
    0x15a030090b410041c810390f808884000d2201900350300c170700703404c4140d020f441c04002038910703801c0011207201501114100314124500090b040f40d400d01920030444a0350310540d480c1905d00680b15511481c9042c04034074502000800d94800c8010601c014142d80c641440b601e0354040e0040105020742120042940c2241c10003181c41d00017503600900807100c44104904a00300d015001540c400403103072401000d44c0c0c1d841000b800401400440a50300d0340e100c0006800c40701105070450601c0559000d02c4a41c00707001c0380c86c1d640301004110502c1d4185500c0d03000b5042c0bc0030f880605502c007030004500c5811040b1980914403440000107075a880b1130301c580069a40b0700900402c110b0641c04039024202c02440d47c0050326050034501140c81c10356049a07100c40969008403000420944000300d0382200070402d0003101824000b9841c08a51803002e07502040d11150b9001c01c211040d030310b80601950b408a07a038054814620807560401540400c1c88610361268009101035006600b840c0c4801000c0b1286640 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 736628291 1250 736627041 736627061
    0x1050114070b040b061201020a0f0f0c11040b010e0303040801151d07030b1c080304020f06120a0b130e0307022e18031e150506060d0b0301090c090c03050901 69
    0x2003082d050766265682141d000005040d507410404020443c100c24209002920502c8404c0e2280510304490300307002044c0e408040388400412809907403c9020601c5222540f00c0040c05440110b005502070b0016290b440458440c02d416200008000544100643c051403440f810450b880d450f05a0701e60586104a50a0502445510040010400742c6010b0b40c0310b02100d00018004540201c1d05a00c51403511800500560701038000200f040114070b4061f400010029080396000e0800a01501c52041040028036144d55250b0310b068003011030f60b80284103c404000c5032030600580e815070f040c5944a82084800303d0040505806010441401c813400700002d0240e0321014800034907005044903040c6850500003101f15004a020000c600144001041c00c24080c0450352014500d2030024900c00c3c0c1321403101c00c43c61506042c84a00e03a6500d0458008c220010408038492020304006030052042404c010200c00c407580d00028410b4864100e007404a059840400081d0b45503900b0350b0a80308240c130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 736629541 1250 736628291 736628303
    0x30b01291603091e0602070b071707060f05010b04050415061d0409140115060804050a0609111e010e09010b0406140f2a03121611060f0105011407 64
    0x2201841d10070a103030003558028509501d082e65541c80104c02e2490004600508808002c4284016901040b102d070041804003a040d1074110140c4800c2e040e18400e1000c0705071090002406414071855810400e510580c1c01303810002541c2d103154030110741d400b9119050103503042001014101520f5103105084440a8960a650f0f507909050701148070007500c2d9541d0300590b601159400700c0d61044c8d100507a01442c0e400060204541c0ca400d451a003083d50240c41002240c0d8100f0000a00210380c00059940c480b4022410025a140c02550f50f0808444260010f204841e0f040d4002c180f4042170700c5011081e280d800690a4400c18044403110034000c0c0b0845c21801c000800010340300c3d80501201e0041031a490341000c00d0b40903808903d038003c245c1140222088040100c1c14171140d8994842040c0350001107103002c12946040d07003102002008080320030391910640318414044c610b034030300078440c00081da121031603c1d80c1406481a002c1c099980010142d0240f050780031070010442c0c109941100f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 736630791 1250 736629541 736629547
    0xf0d0b0403030b1504090606110f030f0a0909050406141b03010b03070318080415031a0112061820040303200a0803040303020a0206060a06090e061801030b0129 70
    0xe1030030307005400050f081c40e070000300d00070604c2d5600c88142e0141001e04032268012074180e02c0c060008102a941c1d0411041e1038200400d610032046001040341d050b40c24a00649031107150014054610308055800301d56010b04000401003008080c2d400700309290308202e80492562a60305038400ba80545440300300c480d020410047c0a1505498003640c2c2c030a03481e14010800003200028035118000c1014120b45445010405000080703440f1102c402c120305625040107006403100e217968401c0118a901c90501100c5c09109003104240d400c9400500000b1080c50b0507080380b090341400500c828500c080021720780c0c990b14600071807128211000c40381c1681d40c01591030350b004144001418203007140e04032849101e0f803c000003250f2502a5121f14060780f001038a6840d8040c0c0682403410040655101d80d48421050180e20340115a02c4c0990303102c48000c0c100b40e690304000c40d40c17a07910501c8680040c1080000001040504558941031b9810000c17004d80c06001c00880c0340a5030351103110550601414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 736632041 1250 736630791 736630793
    0x9100b0a14090d0c08010c0c020901060f020a060516030f0507211e0504050610030507270f0204170303010302061215220c0c0c090203070216140f0d0b04 67
    0x203509018201c03080c4038411032408851800059000d41d00940440f042d1220b07100030480c0c0320b070a2064040c0c03903a960604244281175030380001d03050681406403400b0b01c00b0008000a106100700a1200d00320751040c4200218141150401c01001c1104040000607041c0301b034010200c001801b071280a42e8440e200c20010207001039601480442c4240060702d1259100704030b0701c0103006440d00c526004110f201c00a00b40c00d140c1009418844002d20216000490010420005800154400445c4c49034091302d400309050741760390615004800c4184280c0c0d824004608101c001e180d00520445001880c2505501054982076860b80030912020750f00179000d005802c280307103030f4020703055000c01c4519105004178840f000041001010180140c7c20300703040e00c00b04038420040d124040d01c0c00e01c641400e01501031580c0d00e4013400242801819080744d004004503054900800c8010b44002e5201003118810b82c8803441d00038040f014401c000d04c2204038014000103400e1035061401c5417a04111128040e54075 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 736633291 1250 736632041 736632047
    0x615130b0901110a0b010609171002030907170607090e01231503040c0905010602010e25031509170702010203091e060f070501050a050f0a051e04050c09100b0a 70
    0x1220514180000070f801071900c80802d0118043c1c0b98070500d04441154100072000300b2081c0e068210103c01c440728076203018808400502c07605101099000580c0d83e550f004081400c03c1615403000c203204c413149030001044000030815911802c40d40d6600f0141c2e0383e41b5a404110000203104801d00e010ba401c00940d1001c40c440c000219981c000f4000c980350900d002000b426a0b4000c5030b0a445400f41c010b010701c9524a9030240900411040c40240303c1e030110040e900b5150030a50350441c070540c0341c4035681c1d40c09480720305200000b580c00c259212810383c041401d640c060920000100d4202c500104d40342d82000305001620310480d0103030b00950505481e5010310100c15160142e0800c1c800184c8030321486960b40800400150360b034003a5540d1100481c0c136140d825164050840c076116810801006009444c00001c183e0106009002088644981c0e000c2d4004402c0c1d5442d0045080c044402c10051260002e20004662404d603140711040e9650bc86c200840c5a05014805070201c042040d445804d00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 736634541 1250 736633291 736633297
    0x160b0601080112080c0a0c060c17030702030a05090418081306030c0c082101090605090a11190c0605070c050c01090302031b1c03030b210303010611190b0615130b 71
    0x740c40d0206c550314070a0f9141c10708807810940c8520b00043c0d00d00c4590040142c00c3d00780b070a030002960806811170405440107500d9000341e04040d010000c1c041a0703510950707506d4010303041424884921101d00e88682c14868402e50004540302001e10061308001a000d2103480780c640d50f407100d50380381d40c0c0b00c800503a2049a168000c000c0c07402002c8000750b0401c9030880c100b52441c003c2141240c001880f61078441803103501e2800500c0402c216140c044c0c0440441c80580031128820710b21100e4101910212400f41e60100d501503003d090207161404000302c040e0030009001c9528042c4044414012480780110f07042c4406010003134154102c3d201680464024548002c40a00020007203186604081d00010304021580c200307034002611020215114200000c40b00e56441c2c2d044400304031110101a0710b80d4070301c01841381304100202c501c00c0765414441840310f00206d0100c40075400034011b4905002078845801d41d00306100703810400d183e640d104004412503c02c0701041041031042480e0501c0f01d210740e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 736635791 1250 736634541 736634557
    0x30d0b0f150c070803030105060a05131e170a020d1b0b07150615020309130f0516030c0f020a060c020f0f010606080c040e16090b160b060108011208 65
    0x1062021111540e0769445124054946200020b41c8075400d0700d56035032030884071383e0007810217410400c01800a6200c00048503040c0d03040c0d050031686c4402c0402c1c444940b606550002610305514441820408a664407000840d103003590803c100400d0080d200d902c07561160030007580418908094000220220303500b1809080000440001076503500d0440001c0c5d100100446802d6108903106681d00c0d0140f084d400a000e00f000c01c0d0404110703d00021b5070b0303440340c0101e0600c81c00f44074401540d21802c5402c0020300855040051042d82030a5580300804400b0420080229083c82c418544191007040c51480000c02c680c000c01501040380c480c0c1c001000c90340c61103000c60090940240082408200041c100ca45510000500e076141240040c40a8400750400030740a00800c001c0108007200080c282e00318004101900c00c9020484c82a14601c501c0d502c514241c1c040814050103d000d1800d625180341d0042c2501000c550760600110751106090142211103c03490700000c003c2888200502802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 736637041 1250 736635791 736635799
    0xd080f0420060c0102031027090602040f120201020c0118090504050703050d0503090106080604021003020d0e0f010b040f2f090603131415070c0f0f0c0608010b0408030d0b 75
    0x107001400049102c07640004909038507a900002407154400781040408020081c030040075a90310f500398200320301c414000d61a00001901c4105080920120340d044800800000814a0045c0e54a002c5105c8070301c210070060707000d4040c0700c86034115075000391404085242c0031110181c041d400d1511260003444060401c3e1014840c60402100207034081010040143e083e84669891303207803111016003900d0303060300288010b402000900c401038031454210955032589090258030b428546480300c0043c80c070154111410720071800d00410128041d03200784e091840c15030307080c4060041090200301742c4440760840e900c00c00c101c094004103d070b144060010207005440c2c2c4513103021003280000f407058200780c0d03820075a5292800d00d00304000d6a48076650303c1c03a0038138002e01038030240c140c2c48c4659540010700503030600032654550401c104440c1c514141c2250300c00040c0000c0d2410303003080342409900e03000746000319010704004643d5010a10648040308d0750ba40055180600c180c0d400d101601e4614010740d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 736638291 1250 736637041 736637093
    0x1b03021009080705070f063504120f0201020c0a0b130c0b030106031b0c1b03050105010803130f0b04180608030714060604022701140c030a020d080f04 66
    0x40d5a40d0044400c51030046014070384541d41c83c00c1190a040b030076032103c1c0300c503000700f4420051300790844025860316262510215031160f8201034012400c1c0c0b899110404051550100400c1000f0541c1254104909684d006512280f111082e4200e11600040f07202c0b0794810740d86100020310119020b64020f03410300d00f42c040407050360f45094100b40c00d03401c10300240b40e0200041c0615a4548503048124080110801e0101030400380502801e6070710030058428944010001c03809143c0209d640000c60b8001c00800040da550441f0940329004069500d0040c0c64458001861401e180e41c802c05848800351386500c0d061501c45400c141140c020b006504490303c4050008030241c0a1001d007124600030001466050507a114990804100a2a42d0304c2103205200031050802d8000c94520034140c10399500565102450058800f04010700304c17003001c0080015500c3c00c2340301c00b00140c90040b0380b503000c40358003668845064800480c1121400c42c00d007545c1d000600450221010741c11081c400c10b0683e04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 736639541 1250 736638291 736638313
    0x1090b041a041205010b090a1811041b020c09010e0c04061211040909063c0b06031314032503031104080309090108060609060d08461b0302 61
    0x30078035038601c1065555940d5030042e20220b08140700807940c041e102d01c40401039811441c1e000d0341c0c91070810001800012041070043ca02d500c5a40c0072180300c440c563300b10203501907100d130001c5d604c480d41524240160141800015400b1480c00f0081c024030f811411030b0304050518400311180b0121403603d1400035222120400504004801003028200046010501014a080410a0700ca01240c00c010b81e40040c41041d00e40744a407a18180d00010640c030241d03013035003001e0000010703000038841940c1c021000024055140408100c2d100558030990f034591b04140c2a5809070b499008000342400c1203000414168a00c25608004150711442410700103112842c460744009541c01541003c1c070313290310000340b0719803518041002e2030060800b100104410300e070001c040b8020503005010280510769002641d400c00000c00181c0b2800f0141c0300c0b48101c1070710300a100329804a0700c0c00c140195042c02c3c5541c01518070a00502d644030301542c0e211505c000d114185890f190303041c0d0281c150210301030104624 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 736640791 1250 736639541 736639559
    0xc031403010f0905070206060619020a0213050603100509030405040b180a02031b0c0d03320a0e010216030e0105070501140a0b0303180d0606210c0501090b041a04 71
    0x54042e0104028024086061080ca1400c8032000740c12001954003400400c800c03595501c003101c3c0304038024008102c0e201d030040416031400340039190096020940b1209003408000750750043d841164118200c880001001444104a0b5010380d8910002d030410401840a0704168000c0800c0c0c00014110300352010722000790f118400380540d07560010300d4000dc03e010040b2603142c0d0141d000c44060803c0761822140494071031380e6445080045040c5030f150b1064501810a05942c10810048008008001c0700000004014400122215050b241c6803051003c0c0d00c085c14801e551603111507880310005850951010b40c0d11142c41c681c01c6041090801070303440019001e020300c00c254500f1204200e4a410010030000686100403a110b0080d4010f10008038800e6002c0c4010b05242426140c600840c1528100240070b441c0030b8028110810030014000f071003540500082c004140107003d03008000b5111801110740400328840c1407070205051006003e29a11600502d10301c80d441ca00451409544003514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 736642041 1250 736640791 736640797
    0xc11011209060b01140f0316050412050322140906060d0f0504141c0e0d12051215010f0516141e0607050403080a1107090b03100606020d0c0314 63
    0x40b25429242c01483c805075801000351242d030108440c03100e0038095010946522804001c21380b01449000382c1c038600c1001d000740119006010703054501e120700e40403410b020340e8a5015407007014a4100102c1c0003005030021081d940262032130040940c0020780c0c0041040f41110000d072403240e010740c042000854110340e13486000607000c01148041124682802c01140c4d65514405044071a0003058400b02040605050740c1011411420101070084881002c1121010a21801030810035010a144800d940150140444034440c60000d803442e41d4080515004426514085002c26100181300340914050000b41c03d040780884500c203890304c4c1d1500d80702d00010f040f00c00302c49140c11204403111107464003409584058003032802084142000d09004040e881503200103407814502040d000400351242c00354212260445044840d110f44415469004245581420f807080c4124401c401c0149018040c0d00200e8410381c0150540c003007400001d40711111036100407000c204142240c880302c4a448000707 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 736643291 1250 736642041 736642043
    0x1050a30060315020304020d0f1106130504050a060e0a0c031104120510230402210c010207061119020a0e0109021801110c240301090b04140103030c11011209 69
    0x8a1410318608002072000000e843c0d44a02c14010400c0002584944030342c070001940c46602500c0040003420418400c81d0666142075200100050408144141c00f40180540b801207070b08111640303c2c00d81142c11203419110b92404024250001210f120031580004691907450078086600c248100c490f40895026401040031300e03407803200950900200704a2096402074203001000300c40e034101c1802680048040741600f8071040030000408540318224190b03a1845482100170200103149401c03516058000c10441c010700c9100710001d11944a0802d410448402d180a80b140174808900c1201c9200300340300a80e000701c1d41a90000e140050030072114000d080705180140c840b140c03002884c00c1c01030480c0c030050400880300044800f15a01141550749000111540003400d80c00c1d2413603004001c5401160749104102000004080c486030300040d00750a1308407410050046070b11a1100e031844280000380c00140301c1044540010545500f814401307105043c080803c140b0140c800050b144035202c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 736644541 1250 736643291 736643387
    0x14030f1e16180513050a02150903010e061b07083108150c040308030f0a0b0409050604050d140a050c0109060c1106060402030112020913020603011d070302040501050a 73
    0xb8007000742d00158441c0c5508400d015524108080c55034503090f641e8101c184000c3c2c03203a600140c0d4000715010072011254420800350090022405440851f5180d010032689101c480d07203466188528010f51004545410b60700c50790341420401100ca010401cac021004080d1318179500c1124403000070300100c0048000300034280c020100c141d80d01618140d07411002c1d020045689080c0300600006074280d05882e070080903200442e20564601c1c1d072003005000455019a0058980074034602401000300d11207208601400495a8803008400b017140e203503202c3c10482d039081c441400103180ca00e1007031004002850381c0d180040341c450b4160711380100700e80c04114244003150707c880c02c855074500d090007010b500a03811102181150324106100318103000010000307205407403040c006400c1c072400701101c048890b00030703090503204d684509903040c3c00b61804500076000070400303000509240c0310f03008546c151001a90780c14244106000c1c00e55014002190400ea08209500900b83e6020720320f92442c0c030880da81c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 736645791 1250 736644541 736644569
    0x31517030d0212090c03031905161203060305010b06130b13031a070f030c02030d090c030b0c07210e041e0e0c0103060b2a100c03050114030f1e16 64
    0x8841174904408044201e0003070f0410b11500c1c445c89203510682411020b541840ca40c0d8412904d4505030f421b1074103a005204082e503d81100001c0d505503c184140d9111f1002002070344c00000800506008054460031440c01340f140074005000014060101070a02206c9528126142c0c1c0d2440f10b00680b05c100480082400700400542c907a01500c4550715000c14141003001d000000700094603440f07440d414209058680d0484003c011052040c180155042000038489062100000280780d02c01041610800c034140b0311a07251282c2611100d80202082d229000031112800c24803000e0030801e018841640d182c510401000b040c80c2c000c5580014800002d40b440041d280005000c032707030254010f407024070b4050012441c03004102040d40d00c110f440303000c0c101c6520b114401c182c0c034080040210700d1a2074101030191022a070903412850503941a8082155004400001c1c141d030f800040490740e64aa01014806000761030814844141c0030f41c0005613001c40314400784050004a0302e03842910a040b500d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 736647041 1250 736645791 736645801
    0x6010801140f0709170a1b2603040302041802100c06052404020d062105070b0f0a110c060c0f07050405040c06030e0309042307031517030d0212 63
    0x4402907a42c0724444001220003820400e4000300311040038000c4905d10507040c480c400301c013101044103103401c5521042d0b40f0700303a00b451000c02001203000d1140014070403011310701d40864840c42501d007030b4200c80b034070055042c24a075800f084040d0403061882d00b06c45e48085034502c0980c0b14050703205807054141e00c8440c003241107441c04c5421240028181030042c034840340b444020440c98109203040070000c440240e1281220006140282180e6200b40b280daa00400021800301070541040e022601660a540846a540c0c107503c0da6840b074002c01c6d8100301c00030007442102a0098403000f41d03880304002160014102c0c00c01081595101403803141c016030010f050403801c41c404001c7c4101a100c2920280403604060307440702070302c0826000780000d16484502c0d0b402c41e280f00700282c8508a500070401d11180b0b2242290b40d0305000c1c50682103195202840024041d0346c020701500e01c089507807400b940c54591900780d040c49070345040080c5407583d000821000c04e09042c180040d01e010355904a22031824244 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 736648291 1250 736647041 736647071
    0x20604030809190b0406020f0a020709061422060905150901080111030606180306040609020108090c061602011103030f01171c080c0c0a050c01030b04020306090402010e0102030c06010801 82
    0x30060030100a94020380f224101c0c41d00034072442190a0740516000140d44551030903001038007131402e2485500c0d40c08140c100e140b40d80020080c084900b2001708001250321600d415180d22540446c1e10b03086035074008412030480101740b0f6502440c5118074001806900c03005510b041e00c00c140d4031130300780090300700001c0d0aa1400c1001e260043c0410b038001c101c186003015880d082400000c021611400380490000d01240b0307411640c09120000a0964059207454900742c0020300f040071060f80020ba060340050f414880015400d02c1080d001802a070414010706503000c5440c9188800301c0c10414940c00340103115400300080e60041c1d0340c640d8030440c40e604207a001080d08140302a05e00c02d60b0700c03112980c010080d849201c5001c4042514200807142c2d034000d1031003070902c84e041e80d140b541e10036070b404138051040101d05800c050809a030180708000007282040180d0005448607940400044045801580520401d0410344018010340c0c2c02c1610441800e410305000b607210780026515000c1c05030403071030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 736649541 1250 736648291 736648307
    0xc33012c16120203060a0509040302070e040c03030801060e0f0f0301020c03070c080f0a080f03060f18090c04150504021602090a020301030320030d090503090a060207080f0d050703030c090b040602060403 89
    0x4000c110305500c2c160001a914051b03501c5003600442d00c0340040350505209110103005000080c28814450134245005401c2903030a100a0340000d90b000008640c00e84241a0402e101400800e05507203101000200500e4031340f550a515071641d07081007000503804080c0007074480503001d042a65859450842035a00b040121042407001d900715400340e000143c02041551098044c030044103461342e48000110307000b14104c0d04110743c4001d280c940390f0300c082d02e042001c6108030915820307503c8500089080c0001c0c0c41d840008240c01c040340300b90a01c401c0c1059130142448503020310420050001d10303000304a0060013035800100e5181c00000600c18550083e07203400c03144980000e49140420200450b80c0c483c0246961680d034181c0382e410301d005001c020420f50b01144002004003e5240d035940d00a503841981d44140f801602801e001c0c8088024003051040310105c0940755207161008585d0210014070384000000280301c022a00890f1480e580750151020301140d4006250504042c103003d07055113 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 736650791 1250 736649541 736649567
    0x6080606120319020309134b0b040e010606020c0423090a0b0105090f06130b150d180c0b0a110304031a0a0605060a0c0311030c33012c16 60
    0x5070400e00341451a06241c00d10401c2301200d0b007204103102040613050303a001c050401441c944008042445c0380c41580b01e6000b540c01c203404981c2080500c01c150880d9098440354400d600240c0c0210b2410704071401d154000960340e0405011a52040d80304a01c0f40030000b10aa51395111a481030240c80100401b40d0b103c40c0c05404101c419912514244100d04130035000113055501601c0da40c2081c40161b00079800000c2044001468000c6090290300002426040500e03c4100e00c1e05210410285045d40603e0801083e001020500c4560800c0300c038020b6a440280400c08010186180501d00b80d42403010b00003440c420a00007944a0001c1100c0c0010207000c0c0084140900c2c2c090200000e81d115001c031507083d1010b042041000c28142000e0300c007145981751490707260000095070541c2440205902a500c800220101d50081d00c03c0c94180a1942c011031000c181e01205005011503003800078420009072004000c0f0071010706019004944400603520f0424410b000c42c48003240c4e03608444507105017 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 736652041 1250 736650791 736650829
    0x901020f0c06070809120703060e0c01030608191a040312050c0307090302011b02040914070608090a020f0d140d11030c0316080f0414040b0406080606120319020309 72
    0x1401d001c2000416610642e0300040500000040942803a110315102c40850203499042da45615548d00744080a48522075000d02240604071380840503601903c0f40b8419981420300814031225000300c6106c40056181e41a02e00c41c0180c030045a214010214403441140710f0f40d0740d9070314000d0000120003983e0703019122070b01c440000e10400842d141e01850000c00c0301e409290240c0b000070034005450b80240d00c1c61001c0d400c00c1c201111a0188029010701c0410000e80408480c5120f580303110450781c000c4245d0b000c0c00703540c0001341c000c0003501d00142140c1202100a02095001019640e512440b2400022030040c6401c04072080740103a0300402d02e034440054035030185182555080302d01e81c5a1288000f02c101001a44084d10144900d80f000d41c2c1ca00445108003035500c0d51252910136a0004400c801446541004030200c054102806a6800c031504900100729644980c81001440a6002800c4019200030701005614005041601081100039006144d5840b442d805200d6100b1600084e103002d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 736653291 1250 736652041 736652053
    0x19020d03050601080a090303290306010902070c030f06060b07060b01030b0616060e0c0a030c030512040e04030e0f04180302061b09060a020c0a23030607020304051c020d080901020f 79
    0x4280d8001501517448000c40b400000c406085150a0780241405140011030300030041c010380c0c8e94402078003400d2030b2034000c508844140c2c0e640e50031242a4070a02100610300c01103000300b080081c4151800c04e100c0c0780320302008a0140d071110502941b0f034205403010b50301c0d240c4500c0d0002065801d40f003007070000141076512518200d00c107101d819006011340802007070a5925061840c41d800107102141c0444001001c0d00182c6e6034a090402500c1807901055919000c0c808142c3e580003250003c0307a040343d4008510592596403038800307440790441440c09941098903915000010b9559215071000401400c81c41c0d001c0310b0b11814000c2c540340e0001d20440c80b42103001c070090440c103940d10640c0c02d0a07100701c80b459500d90741d222089090400603501c46400c840209000f1450f080d410080040176201c001ea4101c4407040d54041680d281c43c04c1d5600d00168000304018040c1d0305216242640d1039802000584100c001503010840311140c03442c0a41d4190000308201c00d103036074140f0004041040520090003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 736654541 1250 736653291 736653301
    0x90e0a08031303090e010b0a0908061e0403170c180906030a061d010f06090c0f08150a1809170c0613060f1505190602030f0d1119020d0305 61
    0x14581c4000340c81040044110280301c01014420114500a05810a5039540e1541d48290b108002c4c1c0144040c1070225141c01c2e000f14070000d001807264805c0c9212610030b03e060011204440c1c203014040d001f50f0800c81c2c2201c03447c22041c08510060300032030311045913907651507142c004500340540006403244a400c120050001c141da000400d540c6031904840002038041d145083e114550b00c205058500c1755090900c040d01e0249580d000d04116402a181800b81c1c4014290448450b80300c2500e01010900c160701280030421aa43c2010314a007001d01072101c0d045d02c03403018050180690328801c440e076440e2105c0008002c0c2c41c0c0364a8002585214400f82480380c0c034400c49841d03072001041038503130540f01c0c0c0c03112040c40f09076001042c56500c03824040050303840700000711602a02d1809030a02410b4440e000703031039802488a4240484965501860808420144003a41648080b01094070300e91168812450442d07240e0080c65101e40b04203a02000002801004c0d0900078102d001100b450306d4042040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 736655791 1250 736654541 736654553
    0x40b0a030b060f040603021c0302061312030f0e01020c032101051305041e030c021908211902060a05010e01050f010503070201060e0c0d0e060105060405150f0a0504090e0a 75
    0x41d00403600301c805010f0403c1d0303900401c000380300540c0082c0d0311036030210b84030f0413103001a02d40c807e0380341c041e81c29a2001d6035404090b030303560180328100a041070111960540c01a2203540412040400450081406040f0081d1142641c0007041d5980b4180c00010b04007207032203c003280c0311811010201100381c04d907140000059940c002548654501350310b400004d410040180d9071981c40041031018404038000906000b030900400b900124007480039800c40201c5d90110350840001c540c80c0b00c00810f2440c2010720149148440301c406003a0244061055100141c003240099021007010b600800991411844401c151001a40450001e085d07100050040740c41d013204038000c8050a0900b6a40c07900c60fa5000c1b0700410440d0701072545c0c1e5200c0024070001501c081c005110010080c0f000f0320503000406421510ba0500380b16181e8001d000700010012411316200d6074102c800c094042c0c609100010b0006449a4005802c010009900060501035411103100b20185d2445050043c01c92040641d100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 736657041 1250 736655791 736655813
    0x3070215092b050702060d0605030613020901051c0c03080a140406300c020303071d0d030c03050d050f0109060b0a090b03150310091208040b043c02040b0a03 69
    0xa8078854640c002c880c854180142e003203c41207940902243d95035002d00840c44020a45401001d100c0e0103400085004241e051842e901e0050700144884c500340d1030700702006810060102c444529801045d00c0a003c1124041008011070145a54569408a18100502c1d546c0703004808840703000203000510501d070b40040300c4410862002132506010300c3c0c840a00c01102d407010642c10649091981510b010307503001c409980111465200d40000784086031800c940b031306c01601034035001080c01c46800b000c81c0c40f4038041d100c014005e08002d403400001c10a05020395504407800061b0982c0d840c01008595514883c660003010360324a060f0400c124107800400c0c2c3e54082c13040c0d190400d0080042410500c21103242d520440c002003ca54040e010341c440348014090b540360a03100400183d58101107240903100c0c2d80d100d1a8400a6810f40c0d54441c0d640094400700d44040e5080014030011118040b81d484023403012003451018407034a4203e03588100320948840d240d480d03004500705881080022103039400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 736658291 1250 736657041 736657093
    0x906090906010e100b0a0306090f0e10051f060801050f060a08371d07180c020c0405091e0f0a140f0312040b150d02040504050109080307021509 63
    0x3d00c0031252690952190f840000d03070014043c0d2070000480400a640551049048800e1108140034001848075124201ca600101c404841e40103118086d0f01d6241951249038049640200504688000b1441141c0c000154000c500490940c900600881c64202100e507a51f0320100c900030b1030324401e00c03401040d0400103810410340004402a00741d070407a40c1c20f0400007228907600261107050040105030013410411181010b145000ca9500c2e40106011940c9403da50503200c0b009102d03c0d002582c50b000b0032170083c2840c00c5000d000307214502652a8010280101d42d0a002840c0692034807840c511060100300da58242076000082c511000400403506811039030708040540c1828400e05403450421100c001000c40900001a010300144040305c84140120b0040403052220307a10881c1e00b82001c48444442e41c0e10151200b0144010f14203500300580c014460000030840e50003540d5018101e07041680c1c100d000d81c20050350f03e0801e044a11880f80d01c004528003c01031481503100d50300c0072440aa103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 736659541 1250 736658291 736658309
    0x4230f011e120c0806070201021c021204150b04020d0c0201150602071a0706020d150e1003080c03070b090606031005060904060203070504150314092a0a0b030c09090609090601 77
    0xd480d0140000ca2040070020701c0c3c0f100940d445e030b00e45510000e000758007024034041c0b03501c103400c48008859150720039600e0112101003d00402d480d01e8075002d002c00c0351020b03451017a0748c0781c01c00c4c414a0303100c90006d0440b0805840c0007248806079014046c0c00c0d601d52079900d011030000007800b041000e500040b404200c030401c003424200340070184202d4000c0c1c41502d0025044a00019030b0a0b11001d4030707844100340c110100b203001c150a85502d0501d00b440c006032200c100d489412441840401c0c2c1840c010401c0d42e40d650112450402e45035982c4904070070031141e60b00c0b00d4110030308203d00d40c1410700c80d240c90f58450980402c420310b44a0002500e440001c0c00c080d000f5640800040c408074003d808880240c814907038008a64254031703100802902c6001c25428000d0f204201041925400140b00c0904030003129464812502c0115031080911503003007001da022204e0200092182040300c000d5014440c1d00e802c00341d0f42d10b94030b03051104914001d0002c6001e9425581080940c07800420440d054905000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 736660791 1250 736659541 736659569
    0x20603060f03030310031a071205070e10020706031b08131412040305010c0503220305160f06050907031205090f060c010510090b061804230f011e 64
    0x1601040c0e00000d1160070a4041c4000003d00058403803200807002180c0c441c007410b0320340c615544000250507000340c60f050007140890303e170400c1c020103a4000507807102162400e2502e290070040000e056203414003141016070028001440001d9050251081100d88604540e502c0031420000401205004041c26240045c0040c0d400401000d20304a8600c1c00d4008101d0340e500c40c0725000040b099100e8071044804d986410054821a400741041c1d0b880f0303460445664100c00c01462580c0000340400d802102040700400201d155201207130f42900520b400707808040e003509100d19082c0308948001d8002c0c52180d03c40c400410000d19401d84244900055140a548070541070011822140070300001507400ce00104e84407a10b49815480688204120850f2000040c2e0728490001110f1201d03840d541c104004201462502130301c403520488109015000040400690ba0b181e084070740d650b0800c200c4d9080c100107200d8100306418115003d4182c1440303c0140025143d080041d8000c54440c401c0c0307107018a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 736662041 1250 736660791 736660801
    0x12210a0b0907110c0a030209041101031506030905070e0103020f120102040909151515030e0709110909240d05100c0210150f0905370b0f0d020603 64
    0x15811642410314068241600ca0801c84070180003800c55061000c0c103882241202205868004610412250040c0c0018100d4455856840110f40107100d0a41410303114104000501800c04114009010b16900050b0141c1c00d4030b41181030250507808070900d010140010300150341c404440800300c520850300020410082c185050282c090340d40b040007428500311a81051206d0391102c0d034003580c1c000c0c5007000300c0340b603c2a020340700c0081b80c0101e1340030300a142c03820120a40a23502507841191400101d802140e541c1c4002000d071403900c0742404c51404c0100f581c424070f00f0030a100a40120b90501d841c00c84070304069644146841c0030a05900c60003d2840801c1802810f01c00000b8031050441c090201c83d13401e04020b0364401811400ca13141380e02d032440d14000400300850301000d0304d004c5035401451602e000421030160001419049010a10a4030241c028404841400c0460001c008503070801c0c1c4041710000c100c0e14200b03850b40c05000d100701c0c07102180e580e601855480c070394119485520f80d290 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 736663291 1250 736662041 736662061
    0xd09050901181d0a24020a0801140607020406080705100206150105070602041221030204050906060c160e04210c020d05070b040f030501060b0c030a08280203091221 72
    0x15900f6450881c003415001c0001c1c80520040305490b0616501da202610b610703100d4070341c1280302e00c01000780018840301c01030050200091903102156001001c01e802c000307450300020100d070220380c0981c1d0560321410040280b41009100410070303041c940058012441d1145040071100e21a050060402c0000510442007000e140d043e1009450f40460f40c141035621451702201143c0e071640000415a01d00311011043d0348207008460946d103003d00300d2510750302e4103010700402c0d421003041310b045405000c10350440300b4040341510f40200208810030403d402d040c28115440d16022855800c080c20002d000440d59030001d179040410fa50644e0384000034070003803d0142c20110150450302d4400700002e000a0107269a07000c0c2d1050f2070243c40204070030707652810144080c0c40758140c1c07641680c000b40300030b0240a014850740d0754009038603070006005550103011811590582c90b40e03840d556601006010395524100012450420003641051401c07201704c409a0050b6100c1d910711071000001d10000307500300d43e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 736664541 1250 736663291 736663331
    0x3030813080f18011107050d060e12030c070b0714041214060702010b0a2916020301150602010c090602031b100608010207021e0a06050a0e090403020d0905090118 71
    0x102c0720300803036180c002e45419040c604214203d1540041c028505188203104007003541011a600200b034910300f44500e644903405402c1460054000e8040c4214400111558600951162444005590f511a00c900e06201d00c4170000e04044104446080354001c000c100d8421602919044200c000c02e40400d0300d060344072010841e511070654041e4130180300c540c1d5015000082110740880d1000b00e23058864800281542d280414800c4496508000344940c2088400070f1010034591a01100301d14103a030046800d4600c030300445916002080000c00100b542840303044800011450a419080d1400d00000d42d04e0044400c466213100c80440825404001045108010710701441d0034040d240e520007a0764000d41180000364001c051070b001100c011010b4606801ca20380c2c00401d0070849900700b12044505d07800225000080c4800c00e0340b0b420856548c0b8a0451055100f80d004040722110602c00034220440c80d440305019608200c018440c210704030b1405414400c141000040003507482000e440c00e28 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 736665791 1250 736664541 736664557
    0x9031506061b150606181d2217091813080a0327030e010503091513140f01180503070209040302030403021306050f010903120e04060f0e1b040303081308 67
    0x5407600100084030798003c2c0a440b510414000d000000c1d65580164070b00400340e01d1f1149035075642d01800202c03084101d440c05808107101940f41ca441c00d816680741032554524442c488407002000c00d240b00e191520000c5140700d14503030b5410003a141414480c078480e150f851700d002402c0c640702041005505100c0c0d807025400382211517410200301e81407907000005e00702105060b000145000c520946950083c8200ca0040c7e895000a1262030001c0302000b440500c05029002c01c07285000c040004100042024040460700f100540318200003000042d00711000c0d46685129407080d07035844004640b0101c02d994146030144c40600c260b45c2c0c1c3d07240c224118826900f0095015250401c51a83c040c4280c0c440415034032b080d110701402800e84001520300c0059031100074908161041d0704040d040c80382c6140007074850043d01c00f040098440c3c40d01250720b200742c0c000340200c440c454200b1035030f41d0040d40c103d220710903c1408030b0314041c1580c40040a8007001400340b40029403e00c410000c00055504980300382c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 736667041 1250 736665791 736665833
    0x9020f042903061303030504050c10020c0306060405010b0409021c0c020d030e0a02131a1f09050a0e0103031110050f0411041a0f04060504020a09031506061b 69
    0x2012541d03280d03030a0001044003181c0c00c04107140700c1c8103190a000400710b01424100410110707080c0159004c4001e000000e000315103d0090904591083e2a00780f4800706c03000c925009484982d4454041c036140c4a4010040d900c240d0074100100300504400d402c89050b41d00c1d501016984103000b48030b101040100c1c24010b65040d150101008400e43d022590194054490f0340502c031500800758510b40e104141280030754802c0a0300300309800c1c030103141e21214140d25450b91319000403003440002440308506205e400218040d4a8003109515405117020000d010202e0b090a810350405414102c0c4850500005050000300b10003c0c1ca8002c00700300c0030804492a038420300c200c0c50071074110b05143c2d00a650441d03182003050014034451419004a20b100c10510303803241003624104040105801c5d4040341150015036034480400c4640b141d000400160b1115100c1c190381c07900e589406521200741c0107031035032a01d140210510000d40c3c0688041698100e4400c10700b06100035040044680907091518051 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 736668291 1250 736667041 736667051
    0x49020418090b13051c0e1201150909050a03081f090902010807020d1d010c02131401122a0e150909010b151308070f050307060e010f0309020f04 63
    0x40400c15003205030000d2085510000341d4869000f5107660310840000240f858000e041801003464012800c01e01c10b401d549008500c60000b100460041111a4040107259440341402010312201908000050200120801000780b040e1103550f2118242c00d001010421b603000803404662140c0c00c5020100304811200d41e0701c0c0d9540342524020100ca44049001c6004000011b00441c00407802c1d0035026003a45401c00c001d007864411098651001d60040e0511603400021000340c0c071075000140c1c101c910380ca070019460203011014011418140d0294400324040b903c4500000c0c030054103441c0303080b00002080348651241060421000341500900320131051383d0100140c0d41c2d9051034411120400342c61514068417916021800d941c0450340d01a00865101c3c0e104030300c60281c8004080208441d5595000ca945442002d41054000d0703100c4609500014024440d6280074099107005000c50f041c01820042540f0000c0c01610101c510b14051507600c4420790190b40780c1c003044040102c3d00900400c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 736669541 1250 736668291 736668329
    0x203090613092012040c0b0c01050f010b0406020706080603241501080603071a0d0905061005061e0a0e09010b120a0209012a06060308490204 62
    0x41d00e00c03501d116541120b4107020700341c1ca44510820030100c4514110b08164030f00320041c007080c03d080e000944106c2c1c0301c2c4d2400b600001c41946000c06092100c0030f1000105081c20580c2c0380e050045010303040800813007420442041102e8000441900311035050600040c43e46d1414002400c02c2298085001500705811100c1a0484900100e03441806604410701c5140a400011520f13040308690f07443e0150720021044c0701c91954140031556400b0b81140141c90b1101c260801e90075101840000c60303050344040288441424400300550140c5030507680320382010710090700c50062995034004104980000035003003807501d02c44d42c205894030340054004c0c0110b580d20480e120b02ca034840d4011040c0c13810350401007402541da50080f00c203000c0c4169240d01e103540d169821444100d00380b00180000d003901410000000702e45000303500056004441d0552a614400c0c108102e200d034460a6108140e0390005810401d20a2041694480c54030f1a00713080302001c18107098000c1c42113401a0445a0702864505 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 736670791 1250 736669541 736669567
    0xb0913020405031f0e071d090c0a0501031107140106030c1508150619080601030c020106030c03080306120106030809040c02030a1d0604091e110c07030201140403060207060c08070e030705090702030906 88
    0x6012803204220904096507681c903025109d0392a0004950b200c021141c0c00c00242d071181e0040e1755141349021841d4900b14855840b030310b076039211b1070040d141d5035100d607410010310140803d40d80051064010f980040c80442e60001d001600c02400401c00044e42d804500250710b40c981074882010340b5414020383c8a8070001d0250400c081219640c0c000780c00d1400d590701c0140306018103011284e001101c0000c0508580c1d4030030b042d40004006a4100c07900b1110007041900c2402864002d41c040c41e1129a100f0b6103005100a0f1007140381ca40b801e65104000c0c00250725803080e8140500d034551031603041020010400030300c031841546e015107125810900b0804840300c1203030907400f075070ba0844c00400203450000050042c40c000c0e0b00076240150000e01e010005540680011003450b50312152042c980780d00c1b6a1380d0001c0360403044060707a030b040e51a104805070a402c4030140ba081801400c0c03100c440c047c000006039886000d40641401034140d20049014039008000f680c1400000600203521401c011038a0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 736672041 1250 736670791 736670819
    0x18011a09010b040302060714030705031207080109090203030a030506012c030f1c0f051201061701050f0a0308090a0e040515012103030915060b0913020405031f0e07 72
    0x2051050400d03100000320b0507082c1c0121030440f9809090b00382000131070f80f90b24681202992400032140020800900001c0040c002000944860741e840451030a01d86002480224140c1002e29541e14000c0401c2c003596001043e10b03540a00342c40c0208080e03840000480d5802070943e5038012c44e6003007495003c8003005070002d880b85100217804844245000c40003523550303903002c43c40c01d1a15148004080303040c02e115508061400300d4504240f49821520310103810740c04ac090b4411400641510038240b244e0251148a80c0146000c650400000275004000b0702030810324400202624400a0342142648a40380e019005204240b58000e161615003000e986641283c0c200008614070240040703191501040080c101c1c4600c450291045182c80d07070140d00401e8407035010345200404004810400603a801a400688500e2104989440406051004a10140000e10b10207401480280b01c16200090003e0880700d52185e03518602021103e03443c001c00e0790840100e1071b0701462001003445549a501 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 736673291 1250 736672041 736672091
    0x1a0403021305070807081803070b010503010b15040902090a03080a111005070906050702040e010c05131406030c091201020c0a03090504050402010806040c091214070b0f0d02031801 79
    0x8880401c207081d44001d01180e1046a920300400d44540206070301c03600c614031a60748940c2c4c0341d0240c0086601010520f2841d0010001250920003010040c80b95040078003aa48140b40c0c03c0e00d6101044140070030080c1d0038003690146422040d03000c5544400342c7d070380c040c00e81d0040d0b401c2040d040d40c8050603800201944c03504a260030540c8a40d080c108031070741d01c0307114441c0300c0ca056a980748031082c101f40e401c0303509500c208002e9030300c01d841310414807000703070280f02c0d8642120310b64582549d2188117407002d0b03017800c41e207604c180c04480f00b40304041c00d10307111801100da0108803495031682c2c803d070b00c0001800000103840403140075032022922010078500090780d074240b40c1c060344814003060369503c2040107a500440c0c0c02400204803078040350312410160440500504141000c4007680d448105081202c0b00c0e8034400d45402100c15000c1c0004039007030203004c3c040c1146180040c940103400c1340006841c403840c140c126805600100003986400741c510880d07840f04404c0300a104900d40d11440200f02000480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 736674541 1250 736673291 736673299
    0xc03031b0606150801060c0f03030f021b06091228031b030605091005061c0f1802100f050a05070519062301210606050d0b01030302011505060d151a040302 68
    0x2002091841c02044181d1110364031142c048c504040715a001c9000c0e0550000c0091065000e020401401003408405032040642400814040c0390101c01149480c4080c0c0d4900710f40e1000300103215082441000750405801c00c00455021801050800c5006081c10440c001c1d400050702c4c0314031181c0707615802c0320f0101c03803040b24002010b80b0340811082c2c4200cc684070303483d4404030800010844405080034a501215008030000c0c20040d00c034100010f580a000008102e2001e080c401000c41c50803070b8404510081e0740c582200c4038080c010000e0301500c103048002d4103009003c1071800400100f080742e5032100358400d48540480229240110140c82c8040d0341001d030035170a080140c109280d400c9541d0480320b00c850740e0303003c02000c02840b009006e95602e0a55200e80caa41000c034050300d5491018119510030a0054510342c9103050003400c40c0c41020070f003081114040000c202c030b6500e40081e80c001d000d800100080f424225404900b03050b880d54008100a01a60180302180716030801070b2045900a031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 736675791 1250 736674541 736674557
    0xf09090e1603080d0e010b01120906060f1511061003081b1218120c130207060e0d09080105090601091d010c0f0f0203090a090203040f08030f01050f0105070c03031b060615 75
    0xa905c07a8241e95036040c001d40010a040c03000401640160010304405024580c00100b154a4900e98045522150408034000c0604417540041560000102944000d20320151910b0305181803005021826803002410000c0041070081d0384a00d4940d0040c1c00071202d034110b031401000c0d108405019006000781d40010b50342c1c280c0f200403a007030441e0902203040e100409004041c40c1c817020061030800c0316002c4111280d0034800c00c000600c00d44951750510031901d000b0003880494100043c4260182e400460050f4140b41c240a180c100000380c02e41503415200010038200515808660200514510b80e00079608144e206c0368860782001100303921515a03551815042d825400aa0780c034131484803041e0700079840c070f40200182e180c3c0354050354009115541010505026444464070364105541d5000c0c558040d4004000500c6d0403100120410300a082107400c1001235141e10f100c071001031001900788455012540b1180303074118904942280d01400030840562605c40c8440d42c5d4410307188503008a8960 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 736677041 1250 736675791 736675811
    0x270a11010c15020c010906110310170c0d030c0b040c030b0114030307080c1915050a09020d0221191203022817180d0f09090e1603080d 59
    0x50002688402d030060380c1c64609280100c0120004e6010f4113a14400d9540c4a4000c40051201d00801e074440740e10140c0580c0300e003016203040d406d0100d16071000301d1059106140c080c1e0144041010728940320104e80740e403ca01d0a0381410b403420407810100511861211080104010750201000103031380c0500f88003101aa21551000c2000b03026540300d0760300d580103010500002d1010001403000720090004c1e01c0742446c00c80c01000300c1c1518002e0480c0e03644520000d4200e2080300d4802d1550190301e860060054182070f8010582082c881c0d40d0190149220394940e0000b0b10504403111707500840442114602024101ca54909a0400070200c6144421540e03203a02c0900c07070b0081d40c0220040484600c086886078000e4031204e04110b40c000e0030b02c0b090030342d0344d0540c140e140c9900744183c0c05c40c0da0769030084a4101c3c1c0203003003400e0104408140b0107095215804180d000c06034030107440301884001489041c0500262604407807003d404441c95000030b01204000b0380c83e0107401188148201400748a5407 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 736678291 1250 736677041 736677047
    0x80717070c061103130b180706050403050c0613170106050901080f0c0307030302060c28050d0e15150a030609050c030d14070308190c110d090f0e270a1101 68
    0x1179407441d5804003915070b42000f054442c080580c00c42d00c000171008004d042500b4050074000540d1080300400d80200342042400410700c860a200e6808650017841c019102d12110385c41c2000d1700a0000300e00804041610901d000d5020002800000b3b200103041d40c0c8d100034280e1fa404221010383da15000d5040006064140081c5640c19640e168001d130203581d07545004624290800c0301e02e0242012042216035101c070108519444501c102e60300e040c0e44007080c0700740d036083d5100d4644c200c5559000645c01440d061a0300c015603007100300035581650410403540001c0c5441240d40010704914034281c920002c202001a120394922400d90641c0c500480740c43d819204440c0d500da0b00e804840b070420010380003a10603402079500c10606100414455071101d14402252022207030080400c14001c400c0c0d222103010480d542c0e0070603107071800030b95560814441d448800298424201c12a4081021500600109210080c0141251500858810210841a55550510720503038910100c0c45407420103500c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 736679541 1250 736678291 736678297
    0x61d070f060f0207030606080309010f02030307020a0312090b130b07020d0503040213110a080a0e0d1e030618020306040c0c0807031103130b04050915010807080717070c0611 76
    0x38088840c1000e10300780050791110b0084540d00110301034454080700054582c420300003e004110000d58844460400240211103c001003206560040c010084040d90004141442e65898500090000400d9108002a00c0100e0700100418894010020042aa000a00c0091b4040c91041010340c80d0f440050f81c8625290b40075100103a0100001405410701c4505200c96961240c400254140d4007960080c0307903000f09400c0130004920505103c3c60710214058002484120400b07408149540c0b0b50151071101e1865046407400c1c081e644021869000e0303801400108000c0c45419901030349000c00c10000c0d8000c591040c4507500d802c042c0030391240f003000071a02c0c2c2e940c8140640c1c60310107280c4003500d581d1806040d0008d03a1004018092030800103102c0d05004150304003400b915641058100f240c0800b005003881160a290010107401c1da921000c41500a0310600780310085880780780c0300319030020082110300b01c00088141806201da50010b100c45c45180542400c2161070b03916494180148 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 736680791 1250 736679541 736679549
    0xd2901080402010206010b1c0518011a0a0303110f030301030302160f0302011d0a1e051c0f1b0504020403031e08011a0a0e1c0506090d02100c030b030109061d07 70
    0x42d000f03a00512403550203c008040e140740f5400910908c80c1c05010394030954100311804107840006007010f4200300c1090040004000c450680c44072070340140c01c00b00d20848020710014003003180c91051444412000d00880c4054985070040d01d40c0c0c0e42e140e04000e0b60341c43c1074110140d92680150030008070114078903400c4082d00c2d4140d490700446a2000383d41c0e804204500c03045030b84a412040006030750130346070244400f000e405c2d54002c2c08251805003000707a0030300c640c10403c0d00200002d03058800922004000030303000394801c110a1411602c008503034074400c141d800854020b48009404400e05400030082d030845a00741c01c00e04e4011010020441c0c1d00b11003841484040601003980c1004121548081d0141c0c0460340b810417000b00030500061000288070011141c2903255210520611409110455014103d4002807a008102c890020341d503008001224142c190b6803440340140d5440390700031001644000300240214562230914400904820131150030020300f04408040c2d042021420360304036 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 736682041 1250 736680791 736680793
    0x1180303170a0c0f0f030b030a030908280212070806010e010e070c03170a150e0115020f07140d06020a0f0207140109050607031e020a02010833060d29010804020102 72
    0x12007525041071790010408402641856110340040c0140d0b24100f1020448601070358603a1170841c54080c1c03680c20039906a03244840b05042d01810032900d04203d02e035400d207030382c103544014841c03404446640c1805401c0d0401417680c01032100001340c034210303441c2060507520206c4202e19503444240d42a00c1c203030303d0900001c002c21030103403c8650b01e840d0081160790142d403100003c20364010094005030b10801035040b18050380801d40051000d900d0010701362841d840e02d40001d084a1120b126007075038a00c15840780c0001010f0425a1900e9512a00c21460f899540140259114002100081c0c041583c100304840148641240041c2507800303503001005060049c1c4804917914202824800070b5400440c0547c184145000b001c18282e0060b140d158244290340d001d82480c810b00d1000402b4005c0180041c211200c05c401e52240110301050b200281028404000e51701c0b5078210080749040c010881605020380c41d003804901c0c0042e00e03000032a0f645154038510310002503110015035001e4020b907006401 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 736683291 1250 736682041 736682057
    0x80f010e0402220c030614030309010503183a0e012a05030708030103120e13020a0e31050408090907020106090213050120120901180303170a0c 63
    0x9800e02d40c03907114101244090b00210441c3c10107511007990280b24413040003d646050400060303c246401a61001d4114080c0d8a003513103480000344240409082d0184400030303000305018010007045044040140141612000e1100228940300390300400c12030038020900030080d9202600c6121404002e46058503881281c00c101c00490fa8281301c04940b840019803032640a2011640800180c004148076400d4030707640e581141b902e034540341200001c1605000d0140c80300001035032440480896084600070040c1c41d80b0740508116035107049030307000b5078010104d03860b41034078280d00c8002d004420419a80d2811038001420b1080200c8030b040f00d025160004c01d210700080c0b8500891141d40203a401d100200d000340d21607030070b44203e0340240c035492316034041444104000d50300641c0c071308070381000040159051400a0910750b01c6100700820014400000168184e881c1e00a6042441c007285c42010f8600c2c07144c503881d000d845501e040001e009881041400a6201070350790182c040c038400e2540ea40c082d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 736684541 1250 736683291 736683293
    0xf060c1b07050d26030c090f1c0602030a0e0a1a1e0907050907180905060402120901410403260601030c0504030b1518040f03080f010e04 60
    0x200359190340c8028034600a10340000340581e2084901e0003000c0c01500013000e1261603540504070380c00c00c5404050b416205004100c0e140840000755092040103070f500596000b0401c001850040802100742d001c81001140ca8083c003000354040c52160056100c04c000a10210400c3c0350b0b64a400f0070001c00030311081c0c1c0b212401899042016410001e0440c41c11105982c0705a9004808012034220070598800c4500b000603103015425140c0104a6060000d8501040d8035043c1286426010b03010301070342c5030000310300d0b95140d0f64100c5400342c00a0540ca1840d003403022226001e810004926202c43e090913845848400058000124405c4003080c2d000d00b0306102100c02c40303501c00c005c10940070300c404481252074100d4840e103011040c00b1382c0da45010942c0303400d100150449a8003d540c90421000340f20030f00004440b20301c06504090005d0742010045030840000b0050102407032005801e60a40e014081044050900814042e100f501c1c2c64003d592208a8201100e1007446119004840100030070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 736685791 1250 736684541 736684567
    0x18040207021503040f0605060a320d0605060f01050f03151c031e090b09130e070305070306050105181503010e0d051b0105010e010510020f011d0f060c 66
    0x80c0440c4003914031154491056410389950b042203c040d9480e02c00e07160390800b0041e19104441c0e0015044800722031281c28021044000351889441d00c003000390001100c01c0201040d203000060150041400900400500e001d1001e0401a111240101300210301407107075600034400d50303c401c4240c40c40c2504664901c3c200d010041414804541c00107840030308a0b82e01c3c0c44030070340504d000d4003940f2101d0310840c04803440c907908506d4072101000c210812809122a81c3c101003202d00c0c40004942d0701c0d2890b10803003503410080c800d20814040354481c82800100f080400f00340c18013201d000f80070801c81c90381c0e00c03010b005152004404810b408840500007800e0107440f051a07091310003001d000003542c401141d00351440d00000e001c029011440203c0c0d40400c5241030f02e000c03444294500000d100652501840c0d0544802c18041c0b903116801c413102ea4603250307208002d0504000001c1e0001d00242802c489100c13550907090840348000c1c0a5441d11109451000480501410380708a0207071804909240c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 736687041 1250 736685791 736685797
    0x90f0f0705030d0f0c0209130b0601030c090524120711010b0a18090221390607150f0c020f06070e06120f150d0309090507090e1501020d0203180402 65
    0x1100511500e100e0040258460707411f0b040c0b054142840c4100182481d050000804030010590750405090031040b0300459840b0503030800300c80e8165842034043d040c188203051240c1429000300441c010104a100c0c80001460b222350003500c1580712680b420105510702801d940040710340301e800c4003400008000b08400700546210700404440000340c4104ea03540043e0702c0c00d845151012601050180582245c0c1003440348210b003050420440c14083c2000f92421008000d4000f4080b0310100200700c0c1d48151902c1040311111580050700490f00f6034010907030b0006103051400001117915002503141030b0b03400040d4950300d82d4a04e01c001e102a554003001107d07100c610010140d0441000d2000c408080d000011580c011160b0b0240c0300014501840c81c103c041d0040c40c1c100e48100040f000c1c0f80007080c0c0100b4a1720544085c2c200c0030074540d40e84682641d29280359480045488005003c001c1004079011035042801c909a00742c86a410103030101f00ea0b640501c913051498004003896803e114a899401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 736688291 1250 736687041 736687067
    0xb10061e051c0617010935090f0a06020109050d030501030506130203211803120409020c01021608031006020616050706110307051801050a051b070e090f0f0705030d 72
    0x1011a03920b4459690548804e400c4580951580d11200c54404204400c0c0d84521543c500c4002000034204002000e00d40c039544101469030040001010304d042c0d100d444c24411804c0c8003910a2010503541c520080c020050323920103407040d0180311480c41020388a409124120381c3c1107801400c96807507419903981014030203a02241c0c0742c420311200d2140301100882884150a00d400c40035116000307491701080780005140f43d10301c039030410200701010030500820340f02581d044000c01a00c410580300c08078028428050b007241c00f50898088001046510350040d48104c880c01810f61102c3e5558a080e0f03a1901c0950781109005010b00b01084c40600c61005845080e026000101c1c040e400b03090859040ea10541e03c110010b07400066a040b00f48041c0c142140501007883c0c5035190400501e402042c034054501b10341021822b11400c80d405920411021010b45070a0444001c82c0c1410041f2a5448408085440f402d00030912003c22444c40403d400c0c00701c1c2d001801800102d40c1400f4111011031100c20707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 736689541 1250 736688291 736688347
    0x2041503050c072f19080708010204080d081302061801031410060c031404170d23031924080613030507031713020a141f020a0b10061e05 60
    0x280c40c28680c0c41d0b6000d082d01c00c5d080c0041900d00b90a00c4101414141b95400503125a0b00400040160040000c0da035040700f1038130b26141c0050b4441c003014421170b0320303800d00c0a5404200400d201d120350500d403449505544003624100000c07075042441c0700c27801100300ca03450301e0001c01c0002040300034001c40d800300b4002c2c8681752618001c6c207080680311303841e00107070011004418445104100030004003c0103494240900389030451707594045036101901d400b2600303082c60120100220b5035610b000340407080060804002440640c0c54000218500d140c51903007851081902a0001035421340800d215004090045808500582d151003e8070b0590040707008500300f000b407041320480b44511381c101c940601400c001c6d1405100450040152494050300300400000110910344a00e6070785448039084203103120003078080b80203170680503400e0100d1210090701c24440c890070040702200510a003801e80d021501c8450000e046c04403a040038864107000a40491400c01401311400b41c0d603c80d00b210000700708 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 736690647 1106 736689541 736689623
    0x6080f060c03011e080f060601091d040209100320030724120f06030803010e0c030106050a110a1401052406270402041503050c07 57
    0x2c49036141c02d2002d002014105040460404000c05c0d60505664110f10600401500c0340c00844c0c100340000c65100b030101c0e610305400301c010341142801589040e640c0e02c1d03500303001c40080050607504000c10720346400000a00841d017580001c44501c4034640740740c0c40000c00d05160900070341103001c0f80394840d84124102d10421000d06000c0c8698645171288400303c82440c0f000f40101d0880e51101e9042c080e01105004c2e030035004504171200d60b002d05610f561030600f1804180008e00960000803801c0140c0c1c02810f100e8625201a41450800d0f18000d000036550748440600c0b04081c2075090b51100308004482e00000560030369021125181c525001d2280300095651080e00c003040703072219010a0042021030b00166014450b440600115034464480da40003c0100030003000700b00082c1404c0018080f0600348003034500380c69001e041400030950b44035030380002041d43c41d2220000d411170 = true := by decide +kernel

theorem cover : BRFrame.Cov 736510791 736690647 := by
  have h0 := BRFrame.cov_init 736510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 736510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 736510791 ≤ n) (h2 : n < 736690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
