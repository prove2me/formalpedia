-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0129
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:00:41.910395+00:00
-- url     : https://prove2.me/submissions/a35035a8-68ff-4005-a1c5-fc05c1ac5e06

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 23021588 ≤ n < 23201444 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 23022838 1250 23021588 23021639
    0x909030e060304031e020105010905010b032e0503030406030509160819030309060c02010e160609090504060b040c1d0306130201080403020f06090307150606090b070303060807060804120207 83
    0x60f039524040f54400e240000196030700050415012480b90b055001d103068031001c2004000990b2103480c64240d034001110401042a440650030384100c4c80510202c00882a02e40541c100315140c100207810350700b20780c10410000b80da1b0401c02052090800048189015180d803642c1d50a044c016015241c044840700c441d0b0f03050140040c0801c15120b68400f50303042d60800307010820b0340e4101d070000780600349610710643c4a105078540c00007074505484c1a4012124192240c18a5034074206d80c0102a180082c82038070b60f540e980848401c0c50312540035585541c2813640c1d070075040e00d003d1101008541500e0315018000e600600c10482e00c0c42608030a001801e40901b07050f003095403180b40482c505050980f1017501400740311b080c8500106d000024000e518403908200e03001440c120040c1d401c40d84144200c0307001400b80c41003080004450001032400e28040d01d00440c02e561202e80d50740c9003d8259000c4000281d402007040140941c80c0640300900c0018070280c0b07207551030501c00b01c1055844004070030020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 23024088 1250 23022838 23022841
    0x5010905150702060d06082b110a02040609020a0801060906050306041a030a051c0305060306040b040c0308130f0b090a0902090607141c020d0203030403050a12180c0909030e0603 78
    0x4401c080507222402c0d4010550b6689075840c54418002d4185440313004190303c2602030392002072110101c1c41d20100314a002c1036500c0581c220040b15000c0e04070750a400395010714010360025840d2401880d014291407980507030b603405d4601c8010803e40341640014108840000705024450307000c4100c0760421000c48010a9a9040416240004050400e150340c14452207518030100140440c11298400c600c01400200030a868401c1e42500c2040701c20980c1500302100080000d086408940e40042c0070b001d10707001d840c0d180d58032003100d03601c0000394401c0101d5581040041d9030f820205000945600b050003804c01d18884c000ca10800e8460046078a030701d80100d0800510380b504d006507964650441c0900a8011101000503250f01160040825100c05140003002e101d000150a0304034407013907801540703103075115141111603400c092070f050100300d21a54003115140150054078210f4000301c0c0016407011a07032400641a540c070b50305c444006410083c1503c04a0b411041100c2044000c0c2d45c00380d5207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 23025338 1250 23024088 23024119
    0xf0b090c0c070303050f0904140a0609060302030a0b0c0909040302070302150f0a030f150609051509030706030507090e04050607020105011a04050d02030304080703081201060903120c0204060509070c050105010e0105010905 97
    0x240200c20800d07401600d827600c11140400b525040c0d070b0052410180822200ba06c42e0a00e10684201e804043c0d01607225421100c000b8010342d44080c0d200000000c00c6082c0003480c40000c03031044092f1001d500582c07200710700340250b26020100d01d02100e282c0304090701d0810f1100038034400f405a0b40144050542e651811603488030140c11410b2071801451903a0005d03500e92134050880200c50242c9401440c900003c0480d44130f10404483c030002c070040041514034078111040307020701380092034441002080000000c18a81000d090b070b020f54842c0003d04902c0c030313018000a08554050b4401e03003110942c0710300c0710701001c4034104880a6403020f03292a407130030041d030001c00c1c40c0d80700d9a0b021140e5480340360000070621600f98042d2450704000c50241d00c4076682c400e0300300c0701c0040360700018089a860307500b80103030315000302c8441480f42c6c40070b0004200a0f94400c005400a4000c0302c1460110f24108404410841c0a10840d405000e00d904114055418030700000c004420501449015110b4031161031034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 23026588 1250 23025338 23025367
    0xf062205100905010f0801110c0316060e01020a0f0201150f0b0a020a171b01060509010b1809070e03010b0108040c09020708040f030305090901060509010806090a0608010f0b090c0c07030305 83
    0x2402e4400c0041c0a15603503010060001c080d0361160f96503079481e005a0b5213a0310711200494018052810003542420301c021000040c5800605040343c10f10f03520445500715207428005003a00f44810744800c0e6008110100180c25610300b040708500c1c4000820040c440620010032400c1518440b0b0451030719045121020391915185110103042c0507250380380c03110540e10510040c00c0707485811981004401000042c02d007620300c503001d180c0c1d0150b8880014420140e200d405405110070f0751840022070b1000030081441400c0079180e40c80085c0000c060805036003424062400ca4450a01e4490880e1507e9101c80a240645008040d000781d0000740d03440038020600182c501820100c00c1540341d003a0381e850054541e6000d8510140070b44407100000803441d0144050b640080c0f410303118005540c2d2814104485104010035081c3c600303584030004190304109105500d0b800c0c800c0080090800711000c20001c028000809641a140080010022429004c0341c9681200d40c142041c2e03440c1d807002180100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 23027838 1250 23026588 23026621
    0x1903090c0b030a1514120601060e01030902060904020a0305060901050a060507080703020115180522020409020307090c08010311030109031710030b1e061c02130204030803040503030f062205 83
    0x1c0004c819030002c1848003200c071401c41d080714111200d4450002c4500320b5612864248200400301d000c24203040080c6d40680c00081039217100500c03a92038444800b00107402c81e00b1821212001903a580d04201c402e042c9520001d000d040e013110042007103403071324000410520880b00000e104140c0480d6079000c0600035040040c441da1480503103a22140c54040318200c01040c0411114500e0a180104210030707010b5941d01c2c25100c4078622005080c8094090201034a80c50304100c1c0c1511481400081c1d0354283d216070f04090400343c1c0d94803080d5145052180805d5103481415100c1d9240c084468000384c1c001d4031500300100044c20206030340d910080c0c505d0a64401d68030141c40da801d000100140c0d1922140e00841d4030985000d103402e01c1c2c80d00c8082c02545020420f030700041c40b000441d08405031a06090f80b01d004003018501505c0c0c0b41d01c0780d40d4071003150015135044445500100601103081301064069511503025100c154064006020304c1c4c14410625010450306035075074000c80d020040001424 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 23029088 1250 23027838 23027861
    0xa17040b030103150b060909010605280203070302121303020d0f081206040507020715110f030f0c1011030a020307050909090d030605030c09070e010c0c0b1903090c0b030a 75
    0x10380c41e507940e8101070500c80c2c000f0000c90840c9103001240c0000e80307001025980703907541c0a051122903030b082041c00d81c1c0e9036205d90888210300802c507100c114002540c0c546400c107a45694040c42d1111200d25002e490031402c0b4141420284082c007160070f5010700071a1050032aa01103a000d03058403024108200540b043d101d0140502c440043c4294000288001c214001c00040d542089580d86410301283c5500850184108030304900c4500e407800e51052071404400c0d04c82d0016210014511600d60349542e001005814aa150225000325514000e000785501491421802e104804003100a5a01071100620b000c81e019800320200c2d503110301c41c1098444030080a4401d080034204101e84640e600c0710501214002410540040360300d090101d114800080050007580e40c039141ca01c03040e00c901c3c078468003880c1001306504003030b000b044074683c0c41d5004102c04100d02d6600c010f2607216910007103100c4000000d26044c000004002001b146c8081c040303842c6200e01c90b4894070b038040128060b09640104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 23030338 1250 23029088 23029109
    0x60a02090105160c06080f060d080d0212010e010914090606010315030209040c2301020a020f040e0d050309070b0405060702090a0b04110306030d02010902011b03050d020f03160207080a1704 83
    0x600d0070441504c89100a9a10030388503404030303a8a00300360510818007210a650030083c540200c0d00001c90342c0014020132440780c400981020744c80c0c1d040078220003090740800a034602c03800c0100400390f8180308443d030804010484d10243d01d0070160144d40e80344050070060405950329140c0d85c0d200d51100c00342026540c01031006466050274200036203982c0039402604114600000404a8090b0300c918a000700101a00a04607000041e000c0058484100d8240c1d03800503206c9511416044c0180046484402035454607503e9051040c3c0244c07900101c1e8005103d0400b0070041800b0a0f80c0d100141ca8019038101c503001d050f5506d01a03000c000d02100d2110b60b8006060001e04103041c80c01d5800b662040400782d040341c0600d0406d000807030988030460f038064042600a1000110b04101c004c0c42e804140c02402c001d8034120714000031038101e070320072610003008010200c140101c0041004810310900128401008580c1c2042d15058540d14100780052811030b00019940030110700300103a500404d03401c0407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 23031588 1250 23030338 23030377
    0x2070605010e04020f060901020a02041a0303070813050306040b0406020a1e0203120906040b1f120305031f030804140a03050d020105010819050705010509030c0a03030905010f050408060a02090105 86
    0x401e40d10344180d0f0103c0c851201038040c1c01c0c0c00d05040055407403c540590092126110b16004e100003441719030304c40b004a100c0c681c28486661800c000030445503220303021803a605d45404154080701c2c583c0d504078030b01c207400420a100c0454142c00c4a40c0e00a40c00110050703032604145030035104408a101e6141c02c0c803441c4000c0030042074011000d0007122481012610705542e8040c0d609071111002c07200103115070508008182054030350750ba82c001512261f21407081280d294503032000100640312044000031000010440c00e2101c00c0c11003103001c0007081c21b2088007411030355007158034040c6029101803c002d0713441d0202e0310380d07514156000a41d0008203490050506013802400f0703190900a59407036200e182c40700304031001801030380c0e002d054209024003680350030a401159a540300104807541132260f071900601d00d40e54018440002d40c42501c403045d6403840d00001414010200100d201441401d000c10419420082400340c0d11840210300140d83e04000d60041c0c1d11805000d440c102c01d40441036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 23032838 1250 23031588 23031599
    0x120b0a0305030406030f05090a0f24020d060801020a0806010f03061701090506010b0a020d08060604030b0a0b090105030102120402040c21150504020406020307060902120a0507052b03080a0207060501 87
    0xc0100144c4149660500c000b01e00107802c042500c40036107007908079902c4130ba444ca000ca000030000105040c883e030158030bc80407001d082d2812904d65001d01068843d4006282170b0821494440c640007040008000e500780140114050400c4000174200c0e41071280e00b03884001d260740f0951040010300301450007188442012443c6a000b0141000101d4052041c08004180510203e0649081818a50040c0080d40500b841142e07480c10241c959a003102d0244408400126040901c51044605000004006400400b00412110183d01043c0264070401c183d01c0c0740f05460303010300d900a030180c4000c01d0415a40c00101c81008280e00240700c842e0103c000c000100086812480c520316500041d00c02050f00c40d82080708070301c02c0f88211009030380200311840004019801034580341d40005d020006110b00e84808a00741034001c40212050b030070941d0140607034548100d61011080b2031310086c00b0003010750504401d52100b80b02015003440038081c00601200000d40403031751130541c0040d05101550b541c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 23034088 1250 23032838 23032843
    0x30a06051b041413060b0a03020c1c05070c0509010b04050d0f060203090601142215090204080705040f0203100302130b042d050705040b090609030307110112020f0a120b0a0305 77
    0x10b003030141c41488404113889418405004440c00c2d079621515191030480b2034030040d8000d500000104105002c0c140c103807507055407020b10008074a000b81d101c09940c1c1c5100d240800d0b000c1003940140788039840040c01441141800815681a610300755032030440c07041d5504214452181c0e0300d400074403650000040110794080031541c07034102d450111a103400b40481604100c641743e04e2040c0941c6031b1803200d4106081020540000d210714141c2c6410284844c5c031101203509aa0154205001d1030b48006400c002c64101442400344001c05004210b065060248030b803c0314100714400a44504984026051006956446180040f80041c408c000681d41a841560b501c0500f42c40840c03910342d401803940e1010241d001d29841943c071030362802d140c1402d1070415100c80d0801c0d2202900500c0900101c141910301b0402008654080c50005075845800000141860440900c0500090040c414502e483d6103040981d1460360030307810451804007070791075110024810108519070100c3e9941e000024401d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 23035338 1250 23034088 23034119
    0x2040f1205060a0e030306130e0d031a0102011b030b01140c070302040c050304032a0506010801060e061903120c0501140105040506030a0308010b0309070305060a020d1a030a06051b04 80
    0x41c405503811a515071603480c00f1191281c80d242040d41041000070010715200780a802d000078a03000010304152255255840e0000b00986800405e54030015002c441030010f5840450382000d1009001800380400e40003d0846540f4840b4107041d00c6808021545c3c3c012407005082c2411440041d8546240c01c201079074920062200b40c0c0560300d80001d2016951082e0201c1b44600d4141e00d482c221026404103040181c600c400041e54101040f08601c0005001403000e07034001c100c41c40010410500b04004030300c1008000c5d0840f440f03004003000c000304500800900b84102ea4200112a9042d8060081521101594880201036520b0300c031200613082d11482d1428140e80d8250380c1003109545480900d42c0e291400c07280600481c200c600100440c0700c601000b950f02151880076184115030f60340c0c1d0365240410035285a12a02d80106030303844154550b02c907140b0f90750b1030744200b0307103281850001080e1601c0d00d030840601001d4035400001c00c0c841d41661400072000c944139545903542d96514030902107191 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 23036588 1250 23035338 23035343
    0xc030703090b03011412120f07021009030201020d08060307120503070303270818030706020607020c0301050103230a1b0303110606030706120b04090309031202060c0d0c0302040f12 79
    0x281c81000c50089500010780e81a00c041314004038400260104104400702418000030151003170700c5030900c1d1700c60001d02901181d092604000d071034000e98410861140303145d0100302c0411100540c10000340c0c1c1e00060a403440c3d500b900b085040c42c0c03528804281440e041c0d81000c1030425000c40f03000d041220010041050f2802907604002c2c080c0280790349000200c03176a0008520712170300b0080001043e0700070000c12405100c10b032040003090703850300400c3c200083c0da0f000c0e5000d608002c040100094045c042c494000200700c008001c00c2d810b5654075000c0384440708010001c0c3c0105480500c410004100c00b585140c0c00c0468080d03031550f00721804d280c11070203000c1140010040d00f5880408840098140d004010080113840014240001102d5150307200481ca400a500c1360705995a544403846500000342c080d13540c010b01e050a50078000340503403864100c2800c550101c1c00300000ca458030816280b00c01c0d43d084000c90741404a0341c0460113400790384c2000109200c500d134000f61175044088001006032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 23037838 1250 23036588 23036597
    0x40f1209030b060405060303040504020c03070f08041a0702210307212006010302150f070b010306050f040201020604230f070504241e09020318010e0a02010504031b05060c030703 78
    0x15a004113110035120f0548034a90194401d0000780014030b4a5000760461002e08002c42e41400516103d8030400411404c081e140703001c00042c02d02090f00c9a80966104000703088c1c0d011b1601c901540801c100416840141c488000e0000700c445d00d030b000038000c643da0190480c40d410502d440410750461924680c820724000300c0c1e9082d400d84404150b1905040003818aa00501101d07031a40d000c3c01000c011303046007a07034031030f03400c2100e05c1000b42c00b0005060100d00075511b0000640c103514045c811501701402c40311038a41d95104000050381d0014130558015401403202141c9100d40e10144070004215044c40c109018000100d07452100000e0031408442d01200d00707111408032203615050b40712109241c0314196803900010301c991803a194030540d03a000d4400c4000c04003541d40001380100d8106032604040e0b000350780502d602c0e8500900448400c8100e2901400390307280d4590028103a0702c140c1c80010410150071440c40701c0d400d5840b210000030640906079a03501c0c0b4090040644a6010080450128 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 23039088 1250 23037838 23037841
    0x3070e01020f0c03060c03100b0c0a051009080a0c030302091804020907090f060806031e100b030304080706030b0f030604050631020f0f030102040f03020a080303070c0209040f1209030b 81
    0x24400560f0804015000c0d0151615454074002110b069000030701d80e0640c511107120009585464400070071340c60310408040c0034111207904d8094100300b0003a0181d4015401c2a10380343c04625008110b6000c000b05003401f541070503491500303402038040c002c0b09036400340d480030340d601038202d1080c104c6114500c202c4606240f50b49505090320080201d000d250443c181041d0107120b03550040c000c00390828001421204041112000d19408244884000c2800c3d0041004098145101d0181d002c15007012009503040c503003003a00e0300d590780c0d010384500c2c01090786412080700c03e521050400c1038507100140c01d80709a0300d0141403290f65a10240c51614041c0170a454900489840344525130322210341c8503110f0003c1007150200203401d61403c0c2e01a0344000c200200e5811035600344024401030907485140100549140100f040300c50050707000d8052900104200000654002d07801100254122404012502d45040c0600513041c40d00006102c1c540d10a10a01400c0e00042c10b841107078850100c620b0076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 23040338 1250 23039088 23039113
    0x4020c1b1801050d08090901151d0907030c0c0f08030103050607020105040b13240c14090a09200f030a0b01030c090302090a0e03030a0c03140c041202010309050303070e0102 76
    0x21016008100d140349a07151005104030b1601c0d00b1034040e0107002d01d007014101410740c4001010f60713000f1381c8081c4070440700e080200002d40d044442513001a0020003046081c2904802240c418034004080c07408059460910400c071074040d2681e924403076000105501c0c0c02c1e2161030300388000da00c02c0c0410345040c8180000581c0703251050041c24403450b408810380e8042d481d00e400d2291011194407088800500303040d41d1103034651094000c1c83c0b04050f00030010032485403106002c2e000b24600304c2d54000c0c85d0002c02401c0555225454030b030007101c01071100000d007140c0650150300e07601808003402c40340c0d0b030f400100001c60300c2c0d181004d14015002544104200c03104040194211000072030300d0000b00701d041404101601d001c106156004100103030120702d5008000e2560708640c401c842500d81d5542e29505100032a60500c2016843c0000d02038140082c145004004014017441c071460000703403d500400e800f1644a50024010298041d080300c0d1a03052911000d05010801440c8600510400d113042e1003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 23041588 1250 23040338 23040349
    0x405060c040308070807020d140105010501110102070c14040204050604060c0b01050f1f050412050601031514011401031104030f121b0f020d0507030503030f0702061605090307030204020c1b 83
    0x1103960110f00d45280020650b9041ca00d0341100300141d80c440801a82c00f800318180e404a01007244042d800001c1542c14140050466848a0030300d18040c0e20500a801c00500c20701a820103840210090304000c20f4140b000070043e106c3ca0f00a540c00c01004280000c44c2900401000d40b0144650790110a03a070700ca60600810136010614643d1244c550042d01c1205543d0718412028800c0500d4406d1625032240c00746610344110807012150360b805840100184040d0051003100b600d10018140301303205101c07140350f00c00710307048c01801da119450007004e11a683c001c0d880f03444541044090f854482e42d403418005200c0d090050199142d000f04014103401d1032240e03d0009140c483c0e10401c050091241e1070740b00d610800c3e240100d030040c07191810700d804104104138650055100301c000b980c0d0b074900150350610542028003040700350343c49241482400b1708a107049110702500f61a0054840c3c9403000000d00d4840c40e680041d401030300c00039822541c500045941030641742e00074081310b00a4507040a000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 23042838 1250 23041588 23041597
    0xf03010905061912150501080708010e0c0a0303080a290103180305030711010b04050103060e070608040f02090a020904050103060e0c06090904020405091e010204030308011409070e010212070b0405060c 88
    0x143ca0184403071007840101c1000301d52202c080d009a5000280390000340c0e400040300c000380c2040009030700c40403003005200001d001c1c03050143c1d103800140c4411580d103c04500c1d02c90b040d000090502c8500c02c0000e041c040f6551001051404100c1e010b114030580d822038260708420000c10600190401440d0695064032980c0240c8040e80f40c2e0700c842c40c50752441000c07103124419241e0700000e035485050542440c0e440d402818041c6008020008210065110061420304280d00850a00124108100104010600c07072503c1a80540c1c0340240c964507482c0000c001c2c450003002d107600600c0e0800104c103010f401d42c426615501d185c1e04440c85075001070200300e503500442c026940d0042260000400508141c0c101035040107808044559564107580c4504501000801c1c030402d50394089420814158071181041c011302d03003c0d8080407201c1ca40c0c0c000c20142d55008107074806100400d44050910391080103019601000503081980350101454059401c00c0162000d450905c90840890040c4800d0421035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 23044088 1250 23042838 23042869
    0x80303070e0603090a0503190e100504030f0f0506070e10020f0304120305070c1202100305011202010f02070b0408071a040b0706090804030206030117010c0809030a0c050309060f0301090506 83
    0x5881c01e26004200200307640018a01412401101e0300c0c600010001c0001d49500340c9122205202c0d5000c503035008080748000450746103d810318041d0001590780040c00c440940350024010078040c501d60074000140700b240b1000800e40d00c28081000b4000b9405602c5030300c070701000c139900026142e881000b2650303028800104ea544c0d4100b00410010100d140c400003070f030b0324442c0c14014102241038031601c0d07025102da0f00c4900c444000c0305400c011441d03c1d6048015050030390a04000d25410812030750110b9501490003414004029005003402c5d0007001202c0040040c1c1c40107a548030b84404c80507441e05201d22801d4000400a45030b100354034200c90503901500c0d00700c9100d130306254058440c80d001e089180c0301928607540c10400440036844050055029180c1014a00e0b070b07115120007201d08480616144900300050801844030000002c411152001010319002041c1d240341e00702a4214422000c00660040002030000c1040729040003841c103d80341d0b00010040d554030341c4140814541c4d00c41c4031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 23045338 1250 23044088 23044097
    0x32609060d021c0b2b0501060608010602010605010305010b0328050a02070b150d020607060f020a0504080c01020a020a15050d0507030b10140a0305070513090e010b040209210a0506071808030307 85
    0x8100e46501c5c6440581c44040554203142001c1a141c0310b4900f181c2d000d0704440c0019a8540051100710f4090044000920080c0383c00c20080d85080101d460500000e03141d1005402c2d0340131b080442202c0007141c1c03400406040410009424411305a0f0025405454202c0d00d180350704e400940440320484022032000c6014199244400d03040e8204500307903100010407030303001da0394045e140c00c045071a1000c0c0480121a4442c2ea98a40c01c00040c649060420f01c0b1f92411980004020070050326002c01050458a54044001d02ea010403101034480c0e0164881d041c00e00c41c03410080203491130b819048a640b05e88240d80f08040c003501c001c0d08031550b101007081c56081310000c0014000c0e0743c1c0300380e210690140301480c14a00301441008032032401c90582e809194515218160040d00303500a218400c01c07148100c600310b2604041c80081001850f1100000b1060003a030402c440218600b48074844000e13038410152a03080c5055038028181049003035840c03910842c0c8036004203140800000702c81c09544984c45 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 23046588 1250 23045338 23045359
    0x2030c04060f02071706011805130204020a03020c25050a0806160905090403120c05270406051f08060906010c0f0201110703080405030105060109032609060d021c0b 72
    0x1c0d9191608000e070b81d01140328200c1c00007180c0d19201c101c071421071100c00140c02c0c503503d01582a5001c0845001403012286002d05010b1075a092200b100c440d0b55042c2d902603203981f000710069000380503101102d0814010303120950b08150380c00350709548140c00c0c1c4100e070490940ba941440300068440c01041c549a10040118504900700d80c04000060218a09882201e440b130f0b01141030b0401c103a8080b00071614081102c00105250301410510454901d411803c00809910b0040d03801c074840d03100344410703080c03055604140d190340d00080080c0c000a868000860000314603040c1191800e94000009001a001302c0c0b05450160501402030f003050f500c11031201c1080d00c6d40021503260344000c074140b15625500300b0022406200b03550081d8010401640c84d45c0c84e20043c0340c01d480c0002d22050402283c6441400020b80741c83c440c0804529244180080690500071034045220b54081d080e40034a020031a00d12224190f002041c24001c0040c00241143c401070600c0180c800020040c0c1c0d00c040e0080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 23047838 1250 23046588 23046599
    0x161b03030207030308150a0305010c17070507032f100501080606010c081b0f010b010e06030103051507030e0115090c0e06030a0c020c040203010f0509010b030f15010c0204060602011e02030c04 84
    0x305c9007500300c0e40c07031a00c1ca9034007901032001400c60161135108072840d07512842914045a01310000040300c00066844089134500f2180c024400d2061840040c10300c000c0c1c0f002c152600084203a003040c0c003030418540d0001e9030019240280e84040c41006640700a04010020548580108a440c0941010384410380325049503075a5501982204804444000342c0c01c0c40b01526400c100801111150700c6400040e00034512000140003000d440c00c082c5c01400200f0040000801c0020a10850001c00c01c45103102d4550b008101e020f00035130900d290f00d541c2040e010402424245800c0000c1f6134041c60208460421403c2c1940e529012460311948400d003400080d262500300d410002d142da44520545134000e020100080c126002070f003241600a907248000d200c0350a2030700c405405002c4400c0f171203041d031904114048903080c0040c69100458628190080d8a90040f140d0700003165000340180401d03519074000a0003050303024080c009140c41031600f0100300150f131080340d024102c90b1800721b1038141800d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 23049088 1250 23047838 23047847
    0x30406080a020a020a02041e18080a0507050f03040605130501031e11071a0105010329010c021309050607030c0302070305030a02030601050c0a08070201020d0305061c050f03161b030302070303 84
    0x9030a03d0040d07005000071100142d84611401d001d03009402c200b40c01a0211a0405080301c0d00c540099020070380070b1040001142d44003090300c24071000c0d8600196104400d280031401c148010310070310103921020a020450741e421030040c0c46136a600c2c1000c15440c503642c0c80110151000c401c10441103000780120360000780070079008a12030321040e4041c60301d004500e0341c2c0d500c0c1c410641861440c20010303410042c0640e40e13050049014500010209103182c00d4055101c2a42094907810700741071100c04460f1f1400c54666042414100c01c030340d0420084c200749418000c0d00c13540300301c9121000a1070139681c00e015901130b209640a441c1c141d42c0d060704654800c40e07590000d510292800b410710609002c4507118400401100c1d804034401d085440d2940c10302d10001e441c14558080c1041490f04000400a10380c4a000c5002210803040d81050340320465410018204690b0b107030041c500307000005480d000303004c01c40da2114065101b2080d080d4070040000466194001600000f401608040c41c10404684030303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 23050338 1250 23049088 23049097
    0x10813030509030717070503060601170426030402040c02030c030a030506040e0a030f03050a050c0708030406090506010f0602150405120c010605030d1d0301050106021f0f05040f0203070602030406080a02 89
    0x80c10300701e2038030100c0000285041d40c1d0340d1011458050744911000b0b91202440260000c0400760000d101030b0910000181000c04245c000c20f602040000c001414852807441030400f020540c00d003185807803011008080705a100700d5060740514180304040a5451000044400080c0c3c2440958201141b0503401c82c00303044041c0c2080d0b402911841030514010013407003010110743c400d403100a0207404a5001505032000181218840c5191004001410643c201140d03402030740502e1481e0b517230307440b490312000424240001074207130b00c501c00000c211003400c41242c209070b401c1e540840704031a1499100075000c1c41c084400510f1030b040f1a1107d90f0f010b100c03101500c24102d103a8000300c1c0440e21040031030304c1d081c150109240011818003070b10342081010031038104071103000c3e4001d109660500303c01039640d400c480c04820030300c50003140310503020000703500c000e681c0c1c0e40da45020311407800c140c200314801d042c0d035403000d9100340180c040005a041c0004100c03022a04940ca84005a58404422000a402c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 23051588 1250 23050338 23050343
    0x60105010219260301031b03030c0b0408070c0f05030708060402030304030f33050601030b030a080d09020904060e0c0a06080c0d0608010c110706030b0f04050603070b030108060f0f0105010813 84
    0x452030f2980800d1482c507800030580c0d0803400c50941c0c072985142040920603802c135190003e0300c83c11141c10b00c00b02c2e60000d800d18006410002c030000580342c07403800c04d0141c480c0c01005000703150004404901ca0090722240b9040341c604a0031610b585440e2001070707444500549000b94550f004101c2080041c281884100c011801000f0648180301e612513000444880c210300ea150350300f040c0031583c54468152050903004031081c81d080040c0b401c0500800d60311240310402800f0707180c0102d021b09069580e5042003056071740c060082d9410b400c1c1491f100000d03242441c200000790003000c0c00740030107090240c86581202c009583d0510162142c1440002561180c10449005504d800d80480c03488800d000c1c068508166030b50b60740b00694942c03400790520358240c01403800c06041055502c42540c5134400460301c050100c4d40011282c503181d0020b458489103030702c036414011020000080c1e0603c085403161080b58804074010311983d654403c2c0c08000c00c24000d1501240021303000c20a042c501c515020402032 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 23052838 1250 23051588 23051603
    0x1503060806040c090501120f03080a020c010c020304030506280209030307020a230103060b090609030a02090403120e030405090103030c0204090b010b0a110c06070311030d09030e0909060105010219 86
    0xe48031000c46041c41da0480d01603500c0e03021100c003013081301242d101e071600400f01880b5400b01103285603161441c40c03a000c0d03800f904100229012840b031000302c1d0704440c0d00c4100ca0780208407027400d040c8080e40341e412620090f1024054400002d04c012041d09603150306844041c17805c6101c00706c4030001e2009401c030300302c45901803105011200050300c41981340c80203058102d54084000010b2015240f01c0e540600c0154100b60400c1010408250301c441518811038007110318544908011b0046480d01c1c41505010f50321021103010701092540207484900d024500700424842c004810701c40540d40d1150b0300c10740350460284001000840d10071400c10f501d0b18401007012a0360703402c90302c0d00c154400c0b0a0300014107820000a2420301d841c1c0042109001d01016400b5041714850345001480e1805501409010300845418403070f00b1400a004035080140f2500c8200498622810020004504038023050301407251040860f1810000203000c6e030481d28160300074840040e005040488003415004100c6140 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 23054088 1250 23052838 23052851
    0x100b12150a0902030103060f1a0f010c0b07230a0503040b0a020c0a0b070f02011802060304230c010e03010b1e0303040b0d0b0a0e1308030403090b070c05010e0a0b041503 74
    0x1e076203111015008000d1850007585075410750074410203c0d031101003142038040c6400c3c41044e80c8012802002e4501104807000c4860482c40c9005a036030300300c3c865006004401c800d04001805030041703468561000b4440401e1000e1001003051810752080900c1c0d2030101e2424400500051000d180c282e5118060140140c24201800c0c9500c0c58105802c070200c64030060706c420403144a52007284800d807011148028018000301c0001d0f111f58404040000e80100c0c030004c00102030140904200d927514a802803d02c40c520035a040e000c0d20b03a400d520016000602440340f08115190501034181201802002003502c0b10711101140d04a149407200541c1502040c08001850710202015160524040b48003040c06184e880401410b40c001d50003448040d5405000d0121045181da110a040f030f607c0092295291190305060341e1030b140d182c0c044445600002840d00c10020701e03c1c0c01004a401c2070700e070784441c504a04200100000c541c003420305848001d02040003103101c03400001c0d28400d46410002101e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 23055338 1250 23054088 23054131
    0x3051005180d020706020c010c0215070503090603010e090601060c051f0b0a03030203090406120b070804050703060c020c030d0503070e040b0402040503070608150301060b0a2d0903030206100b12 85
    0x400c030507450002d0168005040400c10640c06100d0300c89400800d03e04940849505d900091000c5041724101031044000700d230310300421108104840310304030018155901e96940b04100c60881c802152490201e00601000083c500c0c00364607464041b80e0f214001c0e055840e58070b10360124140310303200240f501b00e0b101c0c100546a5221b600109001d540641d0165503241740190a0009a88550303000c084a000780c1b504000100701da0410040d0009402d01d09440d141d2500d04205152200310340000e06254586411100d60030b40004020913001030503001d40b03051146214003901c090100301d4aa801044100040c5150303490507074000c4c0d0203550300600050030141c54101080c03410f00c0070b41105004c1a240c805003c1580c460200f03c080d40380d812002448518140b4444000038015901100107120480241142c0c0300f0510001512100b188046c4800a000301b04008180f403602c0d1000340e0160052101090300440d01d504d0500c15102244003580c648441c1401400c80300c1c1e80142071042008000420306074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 23056588 1250 23055338 23055343
    0x9060406180315020c060c0702030c090c130e071b020919021201080102070512031e090a0f03020d121b080910050109060312020d080609060402070206070b0106090506040305100518 79
    0x1001511110041c4c442c0d03000c4170f03a03610b4118007902032000c0c10801d00c10607005a40026110000b194140c4d4a8030054803140d6480000d402200e107401a0407205080208000b0401c401c400c1c483c0c01e0302c0e82c1d00801491034041d1600c8108e1003103006504141a600014002c1160015400200d094090018602000441001c110500c00e800112030f6940000300e04051020401003800003030100070340180741d0309225600c044a2416143d0825541c0f50039000900703403410901c00074010030742049038070460540710300d0002d456944203501c0c0c00c040781114543c50000c0c1c03158442c00c242d0f10340b0404140355403038640c0010340c0c04080082c484032441c030808000121152060003200c3c028500008082032007070651410f208a001d071000d01e00119031001d821080f0741540085016004102998440e1440e10f5031804034010344039511000e5000100042e031101080710000c4001c0c122516585e030000860340300c1c400c2002d01d205034030002d489644078842e42c3c00c4500107584000d8100f0314268901c40a241e40705001e0b0f0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 23057838 1250 23056588 23056613
    0xf070332011a04080c0108040303060e040c0302040e0a0f110607020a08070609060302031501110304050616060509030c03030a0c020a02090109090c05030c060406030207020307170a03030f02090604061803 89
    0x50452000e800400020542d10249190000701e804081d040c9410644013540d24030000e0803860402c510b00380442d00f80760003644008050b20209070010312919040c1800c05220700c2c0c40c4000c90242d49411007880341444041a03248505034880f500100000442c3ca502140e01c5a0001607030340114100071000c01603480f00c00100041209001030001e83d40b03050703406042d0320341c240d005105050041080160351200c2c416140c0380c121707090800103445503048910500d18080c680103940c00c404002070b01c1140c004c0030a000411140304001c280015518100341c541c072030044800207641503106001140c840c0d101a0408401e103e0180b0455548001c00d80003d81e800c0c60070780c4560381603556032010300b040c00400070b02c41e0050401980240841615080400d52074030880c130070b2204155000c100744046690a02182c00104000130600d4400807003200c00c0c41d1647c00c0c3e031408a0110786048944107000b1006d000707541c100f18008144a050074504101a100c50b9041400300c140354480d440c0110000c0c4c40c100138030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 23059088 1250 23057838 23057921
    0x5040803120a14010f06020c031504080c01090803010b071e03080424061403010f0b0a18020c010f1b0c030503040209040213050702060915060307090c0504080a0303020d140f0703 78
    0x194171510b081406824109940045406504400c103041299540768507280d810581c850403207076581e5850345410f401049a01030040400701c0001c000559100000013130414070b07000700c1012014458100244107001d285250040c04680c0d581c001601003510070088142e411030000792440001142c0411308103c64450f000250312a1a05441540c203013024443c0040365045c0d00e0040080009120001d24003d120344103a0020341000a403181d9075a0b46034050b107089841c2d0070000d100c0c5541440c0b9a0018006900406e100c1036182c0b814041d400b8400e000f0800201e40607240d03545581c5464090112100000300103980007021481c4c0f103a44410248143d5102c0e2030241e02401040c14081d0007a410100b070b00403c42278101061082c0002907501042031001c44441c02d000003012950301800380d0700d6000b5a4011411800741460003802e143e015001420151080304007006400c0c0c1140039180c8084040e25002c206240400004099600952002540010b903440342c840c043e650111081c1e5110121005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 23060338 1250 23059088 23059109
    0x1030609110d02031216050a11030115060905011409060310030c0803070b060f03010b060705010606022109220608010603022e0309030504150206090d05040803120a1401 74
    0xc14003408a00351681010121020350b240c81e45600085e5840c0d000100303c90940701e00081c02c0022448052035094031a86c484280c80010410341031004080c4a030400880c001c0d401c0201080e4034910720f2141c0803e4800b0b42c2c44001261781031000466020400d050700c00c2c11083d013002040502e0f91440f028620480e07041c64008035040c2185044142003001c0c0e480305000d940180910700c00a42d885092660064040d6600d01000300c14800203409440c0001c1010b410080c002805018498103403c4a420b8404039003c03581c1140941c040920601181c6034840036100382845503d00314079000c209858030b03046010101036a0f41d40711016504450007075205800b942e5566004004508050a0b018082c821000840b244002c590201c80000c803030703c40340c541c10182d0780c501030002c050040c0c060b41cbc041d006003694107032010551640a5600c0c20103454103122842140440302071350f403082045070150740c40d14004d90b003041200180b140b007144003d042d0564585c0c680d0340e0024911a0421803900908400303d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 23061588 1250 23060338 23060351
    0x3060b180a05030309030709020304050715180f060e04020c0f01060b090f04050c031303050f0d090b06030a0201120c02010b041401031707020a05150d0f060f17060a020a0203040806010306 82
    0x80001c00031980d480035000c0c0e081800403010a640c0403406800b2212000c50240e566911482d009085c001c06800c1b14041003402c1d2020090598015034041d0a02200454512556242c4000b00f00d404042e00c14400001c0d0348134400801400e00790090f1640392102001c0b60b45000604203020309640d003d41103611940b00c08a407510407450500b12031280700c401520200b0a5050160080c8030520000700030040102030a2024401c05100d0303c1251038119580914540355220b030110b02000e000042000c0e00c03024000c4011481c28500400d8032130940d0340c161a6801c601d480701c0f4201c0080d03c804c5020900395581c5d03900b1a81180c403107000300240307180d44402c88417141d81903251140401080580c00c540081f4180800d030b005817144000d880540e5401c0740c00302d401142481c103c0190340306080c400302c2500d0804000740304207011a080700080d500217080100c24581c44040100300490064850a0554801c90108070f07810600c2d8003e00a0284610640c0d14082d11513000c0780c9042420b80c02112815030314103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 23062838 1250 23061588 23061637
    0x1080c01030f06120311070306060e060a05030102160b100806160206130c0506070611070507150e0f04090f020904080301181a091503010f050a0f0608070b07020103060b 74
    0x104400880d0314800e001c0083c0741c10080c1c50342c404203843c07200406000c201c44e961521440200a600003c2da840395081c46600d0b1104002404a4410303201c6a0150314120340102d10341c501802511201982510f10b140042c01c0703038941403d0500086d00b0480100d202550103c0c129900f481071a1044899100c40079112503a940c00901d40840101004a5003d05402a40c0000c20640000301110070407902c064843c09039083c000300811030181407507049000001c50310104000811500c04441e00c1000c40142c203201c843d01a100e000d00d01c155583d02402c003030101249441c156100180860091114140c80101940440c0342c00b80282c5065a24080100042011070060b000a6010f070300441c0040c48002c020301c120038028540c180d01c15210f1660640001d800007001311280141c080c000b0002e01c001c611407502c0c58001c00b02500c08000482c201001c000103800b036400381204640c0500000d0800515200030079000340c02480301241056200c4800040c901518000380c03d882c0105004941d1250102c2d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 23064088 1250 23062838 23062841
    0x131d0307021f0507080708090607110310020a050409020c0a06020a2a021f12020d0906050f04110105251a060301060f0909030302070203100501061808061501050d0501080c0103 77
    0x9030242c070001c030103015500c0003640101a80c00722540012902e40b02d0455281507001406080d00240c3c0102c0042100b43c1403203285100200510010b509543c4645511032426041e885030340710f1036012842c10031041024805130b40c0206040d00024055840c4012699142d00c160383c0100030800004032568080b84030405118045403042d09905110500342070b160b8041240b10380c405c0345c54580c440e5070b100c8400003a80103c1c555446a042c1400c00c56480d403680c0d814100030609440107641d4207142400150f84450004040c50282c0e400c1081740d907540c100791004547c1980241c10524805c040d0300b00080728800030260060359503106003c002c1c40b941e80b841ca170841e1000003c0c00b0300d119a0400070204000c0100d0303030800b0180c5401080200c2c40241e02e040c00c0d0040d1180b01741c002d415100d9040c48035000700c800d510080c140c44240da140d41c542e81810450448241e02d80c0250341c0c0c540c02c000c000c02c0d100030346222403046047c010304019040c103003170342d05080031030700260701c254003039041000010302a60340b6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 23065338 1250 23064088 23064109
    0x20070305010c1e08070e0f0d0c030602040f05010503090322030f080d05090303070c020f0f090108060105090601020d0906050702120105090f0105090a030207030f03030204081905210306131d030702 86
    0x510b8001c1132854006801400542d0456419029583c0000a00050307141c840b103103800c581d0804480000d556036480c1010007507105100b809010789400c000410b00e584030f001168028002013005608181d00308172071000003504094036400281e0103140001c000741e0810410500907000d6035804c0d46901541030043c1c16544002c15010964000b001040541078000b00301805203038040c2c401c104880240404a030b02140c07003d0403140d126010344000180a00f00144540c1a208265200146512988010faa4550584c2d40e4580890008641070000601c0394001c0c200c0300740014002d016040c140707582c941c2191003c0d2806041307034100c2c1000050040c1c090080d1508582c13003130000c00c0782500548009440342120b001c004c0c2a804103590803814103202c0d4040d240501648000c0e5a0703000080b030400020000c91103c03c54007405405040001020861804c1e0307400f03403100c500185140d0b01c100c1045103e1710844462410641d42c0c02c84010b405502912503c00321100b84015aa40c0f0a5801081001441d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 23066588 1250 23065338 23065397
    0x1503050f10020f191110050405010b030a020d11060904020417060601050f070308060301090501020406080414011b0f0903051002070209010e09120a02070915170d20070305010c 77
    0x104407102c038168000080b901d03034003d000c0414a80003070f0340d50304807400b50442e01401046d10501d00030031402011940600e005500c00c000810040400701c0916454403144032005c3e40c045009c07069080440c00c2e181072201d400100812540c40c1c04141c00000d000c0760016003010043c00704084414034111401c02900750402e400f424400c1c2008070035001c658441c41003d01c010104450302021818a03202504045801c0398440001c1d5100e41e00c0d0500145044800c88090f1030107460348030406a40300c4107210f41da000611000aa00400d0014501602c03c40c5c40405100c04200c105080000422402d01c010324072850390031005a5141c0d200d00401580310710681116200340d60b80c0d0305000c44603000248161541c65070788502900e4802e10369080e03041644503400140c1c0c450401200071061040e00300041c064441c42400248184480c912840d510003c1590420100c3c0203036081030561070010341e0401e070303d154a0040300e80c42526130b43c0e120f0a5442e4413072a500401c0040721241c2c4584000001c80c3c5140f00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 23067838 1250 23066588 23066591
    0xf04030e04050103200a0f0803070b1501080103030311070507080c0a060203090a0e0408040f030c0302010311090a03082a010203251209020409020907020607030b0a030b0c0a031503050f10 82
    0x141145c4a100302a031800e840d448616400a1105680340c856210440050807031076111440c1c0c40e5103050542d00c5ea80500001c07034402055400040040104220021410304103a69640d0140c1c00d40d82e00760000c00712580c0c2c828039100c041c02101d0000e081080030b03102810204018207140c90100c42809213541154210109641040c0a04842500d800750a18101c9041036400c070803646440c2821156807060340c00001c3d004e02c0410011051248101d0741034101c0e407003030780c1c10005400c500c0c400391150700074854056805000c0d28010404515080040d203001d4205140c0396009101111f1001c03285c0b640104c122180341d40100410078000500303200c1100e000c841030004851840d1080000746106003c650844404c0e41d0b41100e8820b41d21a5805450500da01a041d14028146204041d554140880d40100003a04012401401d42064a503c1044a42c080d10142060700d800f0f42d014095000a8100d10816a03100c0c44032154480b41c1c440d000003140180068040151556050b40c1462401d440340514503 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 23069088 1250 23067838 23067841
    0x7120219020d0908062202060d05040506061206060f011103070501050114010c031e0909020a051314010203120405010906060e0403080106090e0106051309050106030e0c090402010507030f0e090f04030e0405 90
    0x503000c140594002a4002000d0400d400b4100203516806da206019420a03800708100480c1c0e9050fa1105006a000e101141c3c000c0d0303035440070000c41040e002500380c0290442c0300843c0103070511206221071500141440741800c4454503d107891030f0410f0b0f809507502c0c0c4d151401001000d10f180c009682042d420329185800b502d042d2009041e52204a40c40c5030000f281e1000d04000512803620400500fa01c15001e550300c6441d054024001e410100c1c045000340600c05000072001344540047c0c2c12000b040c0c0181d410810f0a003135140100e40000c00599965407034400c030b8000142d580c802c5401901901e14441014105401e0060807100160080790070f0101000c0c05114000c441c42c1040c3c11101c0c01d1070140e589004d01022206040003d0f8000d8103440c0c180310001c9600d40d00340c1c210608200c0c000c00ac40b01c1c2049103074204030040c0c2c0c2c02e8030040c0c0400c9042000d400800c1c800d5880b03a0303403400d0380c0c2040308011071100c01080f0b1030501103134003504100c2c8400c10310080541c4460200d6540901700c50038060b0707 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 23070338 1250 23069088 23069099
    0x207020105070b070e040c0302041e031e150504050102031f0503060613090605090d0e0a0e18030403080703080f061212030702010b04060906081207150507120219020d09 74
    0x1203201e02c40c2d01601c1c080d40040028029485052100500000075200f80300070300c486080900039401c00d029100004110080c80c04d400ca01c0c41a114040b6604010040c42ea4091340d0b03030007680d0300704035801607840c1800da01e80c006041c043e600515000e940b02c1c1000580c0c80c98942100312401c250302c034030610b00d27004214080145030340000b58581c1080f0100c40b901040710120141400034410440010710751803d00b810000c3d10000410580108541a00c6145c40741021a003040644180750003604036522202d004503c14481d1512803000c07203007000c011a4078003a1030341c890000c035801c030f02c07070450008501100f00070014500c09201608140700340c0d4002d040d000221480d5803200d10420015810000100008000310300c01d402c0390502c180058810010f640d10b44000a014201c58002c1000f540720300303911000304c00c200320110b5001a400503a03900b0f03050b844502000207007030064000d07002c0001d03043d81c00c48010002e20040c00414201c0001201e40d00c16503901030306128080c18108280035811608102 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 23071588 1250 23070338 23070347
    0x6040308030402040f0902041506090801020705100507030608060103050d03060f051008040203012309150702210405041e060602030423031e031305030601030309032009090d080a02070201 82
    0x42083d412980440c0c100441d01540000b0403030344070040d40c42070605964040c1101c26800c45400c1d00d0f120398a51000070740320100e0a081c0c1c4101c1800800302d40c00351050092280040d4041074200c00b40345000705001e59920320080c075108013a0000c5d1031a40001001c0d5400c5601441040300904150219610740c1c0d18003000200d40d80c0300d4803800424042c4600015007155070a50000303025548180102010351640c90714498a210b040325407260340c0c0305542c112401d000207202d84511840300c1c0c1d4001c02c074003c00103980f0319414a4600c0103072003025081c40045045d50b0b80340149009640301425001840000d10002403d8443d2644441c05540041109015068155006908644036111000003480c51030002c80d190502001c2001260800c1d030b5140001d040300807001304103010810000740d07036190300e8104168907040b081c480103000c202014020800078511180321000d150512074081e60340c08100e4013040c0e1032607040b00c81540c40d0f0440e02c2d601036000e0304561142d4125078044400c41c10666580d00280 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 23072838 1250 23071588 23071591
    0x1b0f05090105040209010909020307030204081005061f0309060507030207120f0e060702180c03090706030b01020d080403020312070f020d03061202091003050f010b1e01020d050f040504020f04030c050604030803 92
    0x103003c0ea40015150038280d004051001c000c02c43c0ca90115030705d18050341d000b80290080c4c010b0031050b0042004000051029004190181c04010144bd54000c100c1544080700c400c000010411325884258250100d0842e00c2214800c3c152920056512a035603e01890520703044001c0c0800d0001e05510700b5200b540c0250441c0007082d00707895403540c0d285507000048015540b0008008200c1e110010451075040b80c402442c003e44590040310701c2c80d0340b241c0d0180c0a07900d400c104103006074044407490b0b0103242710b030080940280c040d00649103042e107801000f402c0400d0448090020510200c220040c0d140e040007036004a9400e071904001007410803161410a541502010f8400d03668040030078140300c1003803414002160301a04a5940e0010b0212507400303005900e402600c5101d041a400502d0f4a003294202c0526105901424050072004000c1d907164210101c0c901d00c402080c040441c4503269032000345040b51210410503240c5107580303000307030b0701a01c030380c12081c0121014002080050100e41c1074a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 23074088 1250 23072838 23072849
    0xc0309100203072703060e060f040303020304020d1a0402100302040b0304110307080628090506060d110a0303030501140102190303020a140f0307080708070903030804020307050406031b0f050901 85
    0x942c0e20f032503202d012140c5010000310719881c800d4a2105101e100e54203010b0380e00f103922030001803040f031110104050b141d400443e070b842c0d402c080340c80000d80001e10a9000310351280c0b00510341044100f441c2c6842c1a840098040758003504400803d010a605d0202420100c43c54545825482c0c181002c02c0681e141c0070240c002060442025148580340e41c0030b100d4440a840310004030f0b062442c01d140c1c01880c0e00090304404030540760760b100c0002900405d00400d5891608800205401d8aa000610800e11040441540d10402c000c90745849a601d40e90104011406070f64080350550506c54a2020105280025030544d44068880788464800c0888010a01e4060400584070703a007000048e03400c480310260110501f1800200102d00f2030540d40078500400f240ea40382e0800d0b0750307103103002c0e580084141e81060104022040805c0024815810305038001c0c4050160703804950b4403001b1034103850f40d0343c00c00c5038008000c035500039080c0490100007004120754800c54042618002c0402c9a1a6041c020b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 23075338 1250 23074088 23074091
    0xa030b03032a0a081303110105090f090405011b030e010605030123070905090106090e09060f1506041503050103020907020c0a03060209030f1507020d0509031002030403110f060f0c030910 82
    0xd000020240401002c00c2d4020b004540c1e61100c4002d070b41074440396070100b22880900700103c101f00394410400d6801c11580074051100040c800300400162010060049800d50b48a038225070070f020501c0b0b4840e08a418645001c0348840c1524206400c1d00c5450f0055806a0f141100e000d030321034003a00c000203c00304114160325540d1030301101103036441d40a80000f5000040c050001940e903500204410031078000c1c100300310302d64a0707070550581c880c4403c4d40c2003001502400301041c08415000100c2154510041c610b5203000c3d61064411030b50ba0601d000c180100f5582d07801042075051000300070750700481724809410f0b07450b00392001540298080c00054061540800c600c0c8081d01c04006a181e21b4000034111401c0a044000b0001c0201d0708032800e1005008030f031400c2c54428000e0094511030f40c00100900f4031000071160907002500000e1083d42044050a54a9101d0400340000e0206030f410401070901c03450030488000741c80300040c1c52000416410010085554004151201081040b400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 23076588 1250 23075338 23075407
    0x2090601090f08031c0203090604060c0309050a0c08120f12060a120b1b04030206250206030c03010609050d02060a03050c040503010e1005090703030807080618010801020a030b0303 79
    0x48039200000d8000c106036002c10b00380030030b44501c000080e012408070b0410586036480141c10850030780c0801e070780010321580071102160004249400c140074490031340c50005003481345611204c3c82c114a400381a81d0711040d40070240308154040c071500c102c21440004d59403804200044241e12841404070b800010b144200104003207581d4509800c00814009080c240c01030118244442d0408083c1e40710714030310590501222603c1c402105480890380c0003003040707003000d202c1c030021480c02c3d01d5412180c045012032070082c0c00682c1d5090144ac002c10350010400d44960400002500854058109620440343d82c1004401680c4000448a4541c030500d0042103d40354052410514000c40c1c0165a2550030924096000880010100f00340542c00b0804d0010345c84110b480b646400c46400042c0014039001c00080c90203019240c41a040310b00600f45220b1a002c041020500c1c40f401e030489030300c07a500080d14810103549802000300c40c520443c007840c42e0001c14004920901f40c00041188110b81465 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 23077838 1250 23076588 23076601
    0x3020a02150402042003060f010f09050103090519030c0506060402040b030c0901030b03010e0c031c080708150a0303030609140903040603090f0b0a06030b0a06060f030b03100c0207061710030209 85
    0x420040461074800f000c10281100781d5000005d6030030131204a401440340c2c0052039202c0d07105500403003080501c0c0d102c0c43c45150900004501916082d10151514410300e02e00d4901d50740046030320804680295a4006c44041e01c0c0f400d42d0800c100500560300c0346005010a10082081d041125004800c2052481e901d428410041c5e010b8520700391502d5040d482c00e50380000104e40851040c441010032000d49500c148070107402c40f91400540510700000f40d0010000b2a0140200d81d4513410080c907a1120620fa108400011601455900704400107900d0307a00400c410003450003000000b080c032010b0440070345080302c1200e990b8080c43c4509810107844203456000e00162407440c00340f00303801c2b810f07a0401d407408900c24000703004548421601041c0c02e0002581da44900d21038030054035007a0703655495000e0135000842c00380612500140d854000c2004c40c0f0769121481c410b41e04003000c1900600f40503441e152014002100810f2404010311004040204485c1c0d004c1c1814107030399045400311519150035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 23079088 1250 23077838 23077841
    0x7020618120d0e01110306040b010c050309040e07030b0c04030b010e160f050f070b0405060108122b020c0c03060601050a08040b0408090a03030306031707020d0f1401020409060503010c03020a0215040204 89
    0x40003440c6540b800f441d007401c5e04070000045d8894042658140400202e0900440d43c03c1e40500000c1c0c0241c0040c000c10195103000c4e000803600400c9001141c48071038590b11050801c0d2401d03100c43c07208060004082007000010b0880b6401011038185001c1585040c02c90b40303540300003403011841040340b01d0003001e07109805072003958450b141881000d42c07178130034510303011a10b41d506032025103052107a84000155003100041c1c0e0520b160b40804103900340ac4030410389400c1c9000c010481d580c045000c4041d00b00e0140e19201504144500c2c4000342050444d8205150500c00f01508050400c4801c20400031881d40103070419030400c1e8401d501007500e9441c4d046c4082580104403e2907404048010f001061692580001003038031b005602d600c01c00c0b01c00651155407885a1304009422010f070803522400700708050038201c1c450340030f001038102c40403103e614103089900640250b1a540d03034811042c05241401d10404185150702e090461420303500c09400b0b55510450340c1000c40303201007400081c0441d02c45 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 23080338 1250 23079088 23079101
    0x5191e0807110f0102040e0a061802090a150c060606180314010207050f071a0304021c0203010905030a020f06010f14090c0f03010b0901110109080301090f060e040b07020618120d 78
    0x9900680740720b83e191162a5000c1e60040c40390124102080c4d011441d407134180d104040448114003405240c0505e0b0003070160182d0042400584d0250301008000744400c0502c9220303020660540e40c81002c50500d25180c41101c92541044c070801144207004c172003240200f000ba0301030300d400c00b11502d030f1084419001806403061000082aa006540703640446490010740c9500751403411009a0242c001900075409501040714081e50110701079850007600129035030803c840c90f00280002c42c1a030041d4940a1660348002d03004001684a581d040020000a00400340585001035502e0030309840c2918043c401c00ca0528240e100700702c0d03200454603e0121f40c04171103e034101c0110640d12503030345644189868110ba10400c3c003040310701c46c1442d40c0c2581032040300c99069000c41001d05590a2102c868004c0c044210200038255480300d01040301002c407111144201e10814103421145400e1000905200303000d00f00407045101490b51a000c01401308101011521151031180c852400b2000080908523 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 23081588 1250 23080338 23080367
    0xa0c0c1a0301030b010e1e04030e150d06060503040203060114030f12030f0108160303050906070c09020a0e030f0c010e0109210201020d0c02030a080304020a031205191e0807 76
    0xc4100050422150000756049078000d6101c00c641d6a0b807501018004001207520031034070380160130408040c01090a13915006070003498041101004200401c0304038411180c90102440e0102d18030700c4040b298081d8501800041c50228254282940481d07512501070140803202218444492903d460070020387c0b511049050031120300880c142580c0c40203034000d80719502040d04200001c01c50527400a00c1207030194001c1c20851a40e131864508440c0c50708003030b00062f8441c0040044002050000d040c2001403e0102c0f001681c40300400c00260028013200f202c1802a0460320f99052604800303d940d014502c0700b03080c00c01c03403005000012507040095801c2a2a03100c0704002800806910080a106040c400e03022110150301e41041070303400002d0b8110080d8150700900092001481d40b8000d1600310b440a400e81024686998400c4515071000036044002500819110040c40850640c000300140d00d060040d4401800f0f10b2642004004200320418030850b60040741010780b040c48151113812 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 23082838 1250 23081588 23081609
    0x930120d05092509140403050a0f030204050316090506010903080406030b1302040608090c030111160609050a05030d051b03060105070317070f03140112030c06060e040b06040c03090203030a0c0c 85
    0x801c480e0103481c49000e42d00039408110b18001552175103401d44001540030300c1d05600c1da03500b00103030540700710713050300d0890320043c00c05400b4800003925031420480701c142003034400c0050440b103041c8038030301040311002040c050400440300010000f25580da0216070581e50140760101340800c4080225010340e107103004041e5024400540010b002d50710140c058020020b410554420449007401c0600342c44540580c5c80001c0300812000b41d07034040c904264800c19120350004515041795894050a08c108000283c8440c4c10015050398092024460f0a074031188115400513144202c13895002c1c20f0000510f030a041c00000a240b400f4940141c00c08036010405d140f50202d80e242201c0010000d40b040501132012074108a1221002915081c00605031807200d80990000000c83d00c085030450011041a22291360f41c0402081c4039030100d0142d4420707030040b868907000703080600920049452908040080510304840400182e0303001c001c8620031101c0e031928010403060b500b081030041c6100c0d8090306021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 23084088 1250 23082838 23082883
    0x60212040605090f150604230103110108090706020309011d0a170d261e01080d09060507030e06031005090103050a060e06010e04060c03020930120d0509 67
    0x460030350402d0348240000d01c191980d600029110594440c0e01c0004400443c2c5400c0014229081035400b1402003841c1c00780010540350140e086444000081e0000d4407004240c04016846503000480f00f070300220568010710307400d407a080d00252640500c5400604200c407031942842000104064200c081c10000e003880d101640d9101400c100c004001c80403d003602a007580b04141c0d6020b10f40a0010000b40b03103211030b8044104080d44c554500007001d511219403d50035800c4907442210030300e07000e0400d4600a1504c09440c1d03401034075440041d4030160820400b0041100041d0b400160030110080650f481505c0344c440200218450344e19030000d9810495000002007803040000303107600060302980f030400100c200c0c1b4a0194854000740160904418034901050024525500800324200c191800509151a4000180c00070010807035901c4040420070387c0503204000710340824080e03807243c001801c040a5900307400043c0d0240d1801c40c0d0203159124005030702c1c131200348017240349181c403800c1c15a40b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 23085338 1250 23084088 23084093
    0x9020f0702130507020c0612040204020702011e0c05070509010303021e030408250b1204032109050f0f0102031b090d02040207080403060513030503040210092114030a14030406021204 80
    0x420f001c94501c0014440c00d00c40b000c6c1400c20808599004001c01e282c0e40035aa1a502844003079803101d08100e04129203140308100c420003104c010020903506036075a50320180d46040461400500b0341109110781d40c1d40004000003900003d0054841d10b00700f40e112980034415a501d400d5024680c4402c8640c000c420a4048160b42180c030104e0342c0c001d0b804495465500d41d004070741c207401000c844034291541003004c103000ca8000c61031042212404400170b18402e030039600766401e480c144c2d02e044031784c0d500415400303960040c1800102101c41d8088c00850641c40c1c40d209080f0b8540700002d00314008a0300154075005509ca000785040b4a41d0050810355842c0da4910703080384903502620058840b649042d02060712161038561208005425544660454036207408201c456960759807200c0501c8030510000407980308000c2080410450348843c6c1a00c160381b03080a18480041d801c11980b10b810401c0364404841d0000c0828045041d51450151a640e41d0f1a007880203209002002c51548580c0080104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 23086588 1250 23085338 23085341
    0x117070201020417070f0509100801021204120f02120d0207060212100f0b040501030218090c03100e160c051504061b0c0b010504020d0623030c060307020709020f070213 74
    0x3c48400c01d00d4080d00ca0003c0603080e48940c506e005508030015501410004d6117441c003c13082d002940081c1010f0080c2d030b60040b1030b0881c1d00c4036500440745440b103010402800444d250b2310303034045464205402070100001c4004d45402010f41000c100d03020106500601c80030a506440324280d0015046640c0c00002c003e01c528201c00300e0f50405413889041001c82c3c1100200495400c42d90140d01850602d810840154080d4020150f00ba0038020216214202c81c1d450300551402008503a604a41da81031481428038103009a4114600c00d210400900c0030018485c07502c10b000319190720b8908030030039481c6061800c10040c0240346210074101000e0101340090b550040e80a9501c1c542e000011025044041c1c2746011b40034406410680440010005170410350014000034002000c00140035407110851698001007068050950508203a980050b040c2044444420981200e60030306519144000940d104039334000d10a0581d00414207040412400094905983e802400444d10b008000d80400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 23087838 1250 23086588 23086597
    0x20c040e071e08030a0e0d060207030e010305010b0702030304090e150103081c0c020a151b05030406060501090b0706020c210a020106090b010215060f04020f03070201050106030c080411011707020102 87
    0x42503100c8003950001ca074500c4904408442e109000b44d0300b0081c0c031640030b81b01c4001e42c2c21440c1c0c01c181c11a11040021301d180c80100a0680300c0c1c0c441c000b084151000040031a00142c0001070310701820014140580d4002003581c0445421120201b000304550340c595090980c25440c2c03600312071200001104001900b00070340700020a100ca5002000903518a041c140c0350303400c42010140c4c00040381c0130301003011011040c00d000013a410118120f809903400e91004451200c160340012000320074001040700728080e100c0101000d28003001d019003440850800e0b8403400000801056000804402e400c03000d0110b20b0a490390354034081170311404036240342c0d007640c059400e440040d46000030218001040d03124081034208103a000b0245140300720403020381814048c0495502c02131012820300c055442c0d000500c1418860b52401e0744034104440040c3c01c1d00e006030042010715091000392045c282d806a61550b21a070808809000c4801d9030006035080c24001c3c600325120f604440410140540540082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 23089088 1250 23087838 23087849
    0x70605060102030307090b160506070306050a080c03030301050d11040603080901080a05150d06020f030103030201150803070b0f0601030b12011d070b0307030c050c0109061b18050907020c040e07 85
    0x1440565140c00049807a071000320f560f82c3c04500c510030140001c840c0741001e8031340306101000284030b11040703803505840d0041c1211502c0009450348800d100a0074006604c900070003080c0000c0141d80e01c00740000f5164001405018064440e801c0c40300180200715401c4601c00c107020b003040151075200d04021000b1350001d0380a03404181c828002c285548001c0c4622032048030012441008950704204110300081d500400744c0c1c5c0c680d024003481840d4800074000b18025807003134000140103100c80c1d4030fa40b00390440b0352000419800a20242c0041401060050351008211044070000d648480040e0020080c1304035050304800c01c2c8060b50f002c2c0c42c05510074069180d80050000000141c0800142c1e103030700c40e01950b82c0d010380074400321b00141d00075000000a54403134140f8500b0100040c1c07850382110408076007542c5150b19110405400044820701d09050300440c038127411241e020400801c9004007900c6594001c03800400002c0459200707000d217610f9480000c00900c207032410500032580d0b0b0040c41c05030303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 23090338 1250 23089088 23089091
    0xa0f0c0c0602060f0610080a150504110301240e060a03020c030a0801050406050609010e130b1309060f0608032b0e060a0e03070201020a1103030f0703021623040218030706050706 78
    0x105c2c82915018202040e40d28641da1007241c01d90751100c03000e001c7d090500030307150041c200000205666a031402401c016810082007030791250300d8a505042c049000342c1003c400114411032901c4020b9101c5203040504100792000fa550b05a000c004034003d00c55900002054000440c0084074a40d100204504a4904580c14070915484004101c014070030100c45902003082003440040c0f40c02c0828201200c05110980085e04035000c80100742402d8401d141e0101280c0d4840000d41000598824002d5900c003003032007000307031504048003560750b44a4030a540c1003080c03c6240504107916030714480c5802d450158000e0065001c103a50440d5a044c003591a0107500d0306220403800b00c62400425600c0c0aa0160700820180400362140c0c0c0c1112480303140f10303070135020402c5600c1d404e100000092460354441d6006016803400f0f0315000d003500c400341c1c100d01d04e0702900c818006ca18805a0048490f8000200d50060382c60101445060811469100a5805000304100003070960b401002912020740107a80 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 23091588 1250 23090338 23090341
    0x2040602160603051014031005131203090b0117011b05040303030f02070c030b090304090c170f06060a0e010507140102030f0c04120f08070c030b061003110a0f0c0c0602060f 76
    0x405906980e421101c003034a001d82e040317040043e20f00414041c001e0840c05030998026894407401d4100f070300c20441c1c401140e40228621013040081082c00d00c01c111201e85410000562a682c0740d0381c0d00801031060f040190f8604d0041802030310203500c01d140d9920020503055055400c0f0602401c140c00c244001d44c042850090655200003c40c000c0320790b8a94005080c411741800c5a40b02914148050104c03a0103202c2848042296035592042d004404410b44442441e2802168604103001c001441902c150030100c00307200b101d450b0901521302a80040c02e14aa0020201c0b004990901540c2005004030300c110001c502d018606600450160680f400190350b40c2d501c00c4004c0722035104601c01c00700b150444029a001080c007802c110381d0300c1c49c46800c02c0f03032900916494111000311160402d030b940e00c0840040c011149000b21404441c00c3c079506060118468214501c9164002c00c040300c400c0c400301d01000760000c0d121704504094298031520150010380c869030025500d910448011916403420f00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 23092838 1250 23091588 23091599
    0x30c2709060b09030303160909050a0209040b010509011707140304060c0201050c0c0d0302030c0f1b190515071707020d080606070b04030c02040e030a21020304022107090204060216 79
    0x882e0643d070390140081d817454541d50881c40d009085c40002c0c6003002a804404602c04180303000300d038000c2039148400740c0c0301d040c80c00422003111b0300040b649040c01001c03c00700000780d804c42102c95511620101040003661800700c1521010301d4811140b01d112800030401c82005040d80c085c40100c40d8a0b0700806c41540c8848500840c0e1088502d110055405401121a41032280d0021980320b90544a032608002c200d5010603030980001034810320b914500e5281d400c00c9030042103c0150701030011a04903c14000c1c1c1c4549468050795103004420080d0040043c20090146100401d0000e440c54031381c2c0c0c14600010000d403203007200c0480d403000980d44000f284030362608100713036800700e030300001048030307030780b00d039034060341d42001600f4201d0b0055100c5a401ba901e400c00d0028003103090141c0c8605980c031280078502c0e00c0a00601c140035021a00c1401880003680f02d0300312520700e800808242400d40030680003014034054081d4004071070700d8000035011032140d40c081030040a5000c41540203c2154446 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 23094088 1250 23092838 23092859
    0x41d070609030302070b0a020c040f09060b03071208032508040501060f0e010918080c0705010305060a08120a05070f1a13120e010c080406030507200a03030c270906 72
    0x902c0003034010303401403c0c24040303580304400a003c049183d00480304240300800100d4213503101e42ea265540c00ea5103000c03a4050043e00d019140180e00f044000e06003190030704103144420140a00050045000400081d600813922800a004102c00000e0054615400c1f42d0051600c80c0840c0c0881e201d508001e00040c48500e082d9144003036030702041c4c1e5040260300702032401c00282240310080c1481181c1000d18408186000018855070500101910409080c64005000d8510140c115401080c021000b0041800041020b1000040000a1039545e00c0015411206801002006840d800803078a10901300030060304c145030402c84101c000002c07681c400c0407000701c00e85040340c0075008851102d0041c21452003404034a40800c07050621150b940d942e622022102c0d00941c00810211750303914184890513030800000c02001d10400500e03003a118080d1810340e02e485002d8002010306484140741a50345001e4003600c05c13100d0886151040441c08240b02c0b01101d40c0303901c00c800005140440100e91520389 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 23095338 1250 23094088 23094107
    0x11091302040e06040507210c02190f020402030402032802010305061c02090603070915050f030a03020a030f030204081005041b030302150c04030b010806011511100911041d0706 77
    0x5000000220b03501c400622000e405e00038003210070405401000c1150755240c1c1ca94810303003000700380000b41242da1201c01914046590b61041100f00600310618002b5000e05c6020001039819100581c4944903840445d1900b00d14200050442d400c0548610b8803003a00703d0400d01c0103000b41c0e0103101c00d4030b54a041c00001520542d5910301040d419000502500f8038008003a045003015003221252681c2c0c00801003141d501101034a03000040c2d4500b00511710b4041c6001200c0041103004d090720055030341c6c000c0c0d134929025000a060150a081c150b44041c081d905640003020484c09840399070b00307103c0e01e00004050456045880180d8681d91960400005600b0070a40342c0c15001400d07294442d8031800300042006103541901e00c401c220103c0040c4180d403609000b06910702c000c02203035050181850401901601060400149020702401c0580029000d0310f03400c80308030b00250b000c115040290710041161001c64201e42061251818800130155150b41182c6140c00c0d0f070031058890b08c045500052 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 23096588 1250 23095338 23095349
    0x506010c08120606160c0503070608060d03030b040f0906020a03050703020f040e1f1d01080318010503060109030503190e03030708040e2a070308090601050306070c0302010905011109130204 83
    0x80500c014582200b40d006402e8103d8030013030006041c180c801503800c0c145814154200c944412000e0104600d00b810071943c0c0141040c0d05000c2214500b00010032100fa006460240416807101c8019001d030321203034045075450040c0b00d001d010801603420248080e601c4a0443c000192a0100083e900d600c0781c0700743d9421000e60000249080e14084010b0460030000d0203107a41c05400c0c0c4514120f80c1e4865902c400282040e80180510050b8404007a40c0030038164015000ea810400120003000e40141003c0700344c0c4000d081c1030b5180c0c1c070345000407600d40006c0d800082161000180307040e20083c45500c1c40782c0b030010700d542d9500004044000c2c180c50707004550f002455103009100a0082c0070a001000f035100c480351303903030384180d4018001214290102620030140c0701e00000b101c8003803640c04003031a075004141750001d2045524020109544050040c0018200070b8154216410940300303400c010740a9070418000d002580540400050356070091190341e1084403001091150304605009640c01c503070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 23097838 1250 23096588 23096603
    0x10060f050607020102100911010206010b12060d3905030f0606040903050c0304060504050f0402120705030a0e061008010b01020d0807080606070209040f0209060a030f0f0503040b03090a060506010c 86
    0x51a29007441015084490100d0560040c00e2a400c0d29502902c42e048850307018520340410580c81c40006400d00d18180c00003ea0060100a40f82d40401801c0c001c81d080502660006141041410200341500d2400d0590000a500c00101103079101d03c41c6503252010441145420b050fa40c6904056413002d07204902003007600088001000351070701c4e40c0301400080c080e061103442c0c4211200207034196801500203d0200c3c40200d4107120f2810405817410009805803411172600040d00441c98103c2c50040c103a03c100f01d80040090b0703001032580c11107041316495030200c80380f40c20080710b030601843d494003540680e980303008110349040d84001803c4400e2801a200c4040036118008102c441c035034014225a00540d0070041e10380140c8800d030381540300e14000c1201a810202600c1040642d0501a04507845400c083c2400c1c0003240742d8a498941113940400046d142c1d0500e454098114001c503408a030b0a0301000c0300300802c041c000b0501548281c0b203103404019903522480103481ca204000782c090f1116 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 23099088 1250 23097838 23097869
    0x6020609150a0506011e08010305061005090a05070210020409060302090903030f01151806030504060510060203180301060302040e060108010c090e040305280504030b010807060f0818030310081006 86
    0x101055020304c0d0404010715010410000e800b8441421072880c9008000050b1120010030034003d0138007409801c801d40c2260316403070b0340c030300b2001a0f44410007502c0103004603502c2010a0f1502d00810180a4006140c0c2d003e54845550301145c50080c819844141e02030748210002a040c40030100491344203102e112200c05d040c2c0d00b44a51220482c18a0303002c1030521052000c840184401c3c20340c0180100269600402c962600d813400e03005907103000d411804103040c0c1c8081805016004015600441c40c81494510340d103040600107400352449034006504146800f1062920400100d2900d068680b030390028811400c0f000e00454000d0024420310801d080c4802c00704000030321540c0100720b04440325207c00304075903004c404680c1610044803044040360340010100704110a4004c001d00601c8002d000c0e08010340313400b40141c04041440c00704030401144500084005002c903c0f03040801048c4000c0325100c0c50980da0055002d4407902601203107210307468002e4110441c0b0f0203040151401c412044011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 23100338 1250 23099088 23099101
    0x8030a02030304140c0402120a0b0415140406030b0a0507081003020a14010203071b05010906080606220e0103030c02010e03010504020a05100e09040f060c0903170f09100201060602060915 82
    0x1101100240d031541c01800c172a0449070380c1e107001400400307114880502d401e00b400b110105c12900c6024402c2c0c016818060503000c0d041d1002c04d240c0032544100c044564060320000000c0c0104210340004203032903102c0c014400e040c002035108600c54425601d0f03c1110b600c44c0a00400c2080381480000c0d4000e42405007840710b1080032003860203801060044908014032980c5a02e95003850201190120403990010003c561380a85050000c105030f00705860300c0d050210104007144030307200e4080002c2184003004143d0f020074500d1500108003882040741c4075612440c004140107607011017070380040c00c80c1c080c60540785410702c61507000d00e50013040c10300410301d081c09102485404120f8881032201d110126910703a00c680084902c11841441c2c52181002c00345000000c852a8200035001c1000b0a64180001121900c1030f05e443d000c4000340300d4407500c680c80003003564403a0300c40041e0840c0c424200514100c2d0150060802c0e01d0403502654020b41d03401c41c9080e660710326485192548010800480c04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 23101588 1250 23100338 23100353
    0x40207030302070b15090606041a070f05100b1e01021b01030b030a0f05070e0f0109020702060d1e11190507060b15031b0a050703080a140903090a08030a02030304 71
    0x424a100c0e080160403c0d074580c80307031940c1e64400c4400703256400060165a043d4a0070003825035000b40c0807280b060506060420116040c890260941d469110004419003800410010070015551000440d0254a0700740020406010000d8903603003c0c05901d005207442001c0a142002c000b941030b4000c2c038015030004110082c5003000c0c14603c0c10b069880b074420001e034509109417200c20b0300036030100b080b041aa240c01860f0ec0e0781684041c603019103c4082c49400c03800124402e0440b0220305c409a00c1d0840c6000007072651041f45040c031442c41c9010036004500850030303021014150715240402049041c10351044051240c4842c0f542c10385503d03881d03030203485d000d84c01808400c0d0050800103109007c5a002c201000f208440b070f8901810003004000c82401c203520f50001101c000e03503099041110520008c0c0c2035000e00131000341400b465200040a80320340c0d501c80d501342c01410800d41580e04103101e801e500c9610844460307003d80007100d004a240b46000003140d600c0b0f03070540d00541c034568071a00c4020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 23102838 1250 23101588 23101597
    0x2706030106140910050a090608060f01030507030b0403051309050103020f0a03111201020409020403060525050409020304240608010c021605040b2101020310080d0207030311010905010213060e0901030c03020402 92
    0x24244c681c500b40814103403a01c10103e03029140c001c10000e009400d00804500d8500700034400c5030881c0b280c6006100051000c188070080380d901004003d0943c03a01d24040d07c4070b0080d44a084240318095070001038070710203508624100d9009442d01141d004100b41407280004050201501030545509107210303609210004001407030b540030005007003903204d5404005a0384658030070760352503848500b8041c1269820442d01d590401c10861110102d07445540035025015921500035850340c0400081e00340000100842101c94980030b0045103005d460090100401141c01000125840d0420307404500e400003900f008141100510500c80a03c0d04003000081c04561001a4000c0034002c4210026003144155109048860002503141e02e8540303d962800c3c0081d074025441e0744e00014648074030640120707640007500c0e0145854403031001000d1055015101070312000f8420f40c4005600c2a02c034144070a81c10507200b4a40e00e04442c034404070100409090280000342508400c41c03000c000601d065401803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 23104088 1250 23102838 23102851
    0xf0f0516020301060b070201080906041707030e03160e09030a050301180603050d030b0306130b06100e03070612060501050306010f0c0f020904050105070906050309030406080c0927060301061409 85
    0x3600142803940c0400d00355500c607031102c0401d400110f1120119030300048060b501000f50b000902940c5401c2d21680301c00b0368501102c0394220000981a803e141c13180e444030300b0702d41020b0112034440300800403883c6600410300c40d070892100d902000c1000410702004842410b056a6074050a6900340106010f02550300400140d9090b41e480c0e000000070401d12015695803c01d45002407815030000515050400c0241450501c0040e11440d20000386041145600f1200035603070140c22003410031098070480b8100d500c1c2e03541441900320010382203510005c403800c604802c003000c0c4001c65444006413500d010070f91301540440e180400c0704011038482c501002850b4001d052084070300c0b880d0f801142017180d003a0740594280e51100200300b21550812034501c010300c89847d01524500d081c0210b2501d034000c80c003411b000c01990401060910050400365000c20f200200000035034526011100c00c2c034040c0001035443d401e000702c00190280782c10f00c5648115a40b207041440d0a0b603840c401c001c0c0019004000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 23105338 1250 23104088 23104117
    0x6090e0604150b0a09120f0b1503030f0c07090b0306041202120a050d29060a02070801050c070302120f070809040207050a060608070e100605070512070c060f0f0f05 72
    0x310000b01003110302c070082c002000b2141e03940755442c03c000c03c03007070190300041300224414899000040125440082d03650f0032003500c400c42d8540c0003e0300b030061400c2d44459418030001c907a80c4c0341080c651700204002d190140c1103441095a5400e06401c0d906074014040d070641041000070082504072000c441c0814591050302c9040360340c81c400003480d400c001003038000200080b0300408481d0262044481c01e0307003410042040072200040c10418400040c040a00601f40494042001402042400b0251005000130300c542e1406a031558441d4008000540040c403841c90f1480040d083c0001702d45403100b48210017840c12509403a103514682c00001421b8104c0e43c20010b440104a00744801c080051282a020440350300d00440c4600e000015045003c540b01d044091002c100321954000301203aa0a00380700383c90344042c1c00c03d113041c1b8007003a0543d14541400030741700f010480a00315500c107868068442c0c00383c00050410407584c6442d10b91400021980745040840e034507004d20003070200c40c0100c100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 23106588 1250 23105338 23105351
    0x9040c03081c050c030609072c0102030904052a0304030c03030902011707020703031d0109170109020613030203070608090d03050423061501030b0109030308040c0306020c0d030e01020406090e0604 86
    0x920b00482d42e0441d10304180102c0801030107194544045007a4000f840d40c54420390603440703031381542c856010303a02003940c07038514141420030180d00034000d8803c5c0000c001e104000a06d42030b04450892051000c84001c0349540d00024540541c030101907a02641d01541c40302159081580c1c20745c02810120010790501803410b51003039880103148822441000154007070b14005180d440c0c064401c901c8000c04414090000c42c01e244140d0b4400c1d40c26003250340c003d00700d1050344080b4009600414040c030000c0d4002d5400a1300c0502940c902408200701e13031085d81183c40142d6611421a01003105554071026900403600341c00e89030b8800e40009030054024005440387c2881e012062050800d03c400314040b07500104100041c0411070b000301c0b1303007503482800c05000444600000901070b620900004091203140300100f018401203004603030281d640130b041196280700c2e50b00c0850b0307200006500e41c40002e041102c3c29660a00600a46003155829154000d0090400c031150204200c001e005035001903a03001c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 23107838 1250 23106588 23106637
    0x6080a02160c0b07020109050f0609060d0204080601240302040605030a0b0102010e0d020a060b030304081507030b1003060905181216061a120609030a050306010e220b09040c0308 78
    0x14071036402000354036070051381d031a4075100250018150ba817109120b45100d03c3d4119494a482d011a13410000031a001c4d983d850002250100034026034100c07400b0340c41440004129400000c010448010030f58028a4411040e01004c5050b40f00300d0041c0030005105001145681104c2d8100400c0e01c10f0500003c40d110a00309101450400700052220059100305c822000380201481a20340c442c8081c0c003c1c51031700c1e0914132910303554080d8041041408203a00c5c0041c100e02d1281e80042000140207003081c0082d503243c0750080290105020b45c1400f2031401d404180140c0041d000302c02038840c1d400140a5070391895034500001d8000c01e030303400e850710100d145030b4002031500d01c5a131003c103604000e11000b040703000d000d0000346501c0b2078450842c1d510050034000c141c00c000003600d0303d01141d481c1855896a81c84012580c00886200054010503c18602c07002d840c4d400c041c0d0080c00d120b2000411860f103152007007000410741580c015001ea0558442030003c1072101c0c005029a074034010313400300d8040c10f51 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 23109088 1250 23107838 23107853
    0xb030114040c050406051807110f0601030b0106110606030a03030c0201110705010203011d2509030503070b0702010e01020a08010b0304140303010905070f050a02060609100f06020a05010c030606080a0216 89
    0x310380484030102c0c00c0c0030603c0645441c3c410340014240507900d00e01d4000041c0354081400d00c0c05000fa50a00c0034007405508a0041007000c520061140001e0f03490559680c5880c12400d9420f02540020400240b580940a400001d1446c0702e4a00180208032040760f0380c4040d8000e08280c1000d00865484d20800e451401d601c90041c600644a4000103a03258035141c0603603e200700455980800300c1000044c0300c0d403e000c0b40d010143c110000c000c6103c0d0b40103018016a40d003d095403008082c0e0101207030340400d0003c000b400b80c0c410031130780d0000d1145c000c42d85801d07801c0f4803403816908042915240103220070003080e0003641d4024032585502801c0030b1074002c05442c6820903400065119120001c00c05210360001d03001c0c0c100c034462f0821600340900044060b48405005101e280681c0c034800c00550300741d001590b040000c1c51188030999040e61103210003511100c050109640039070800b600c02050364803074450311045851690307413882962103408081c80a5400042003201c2c058000f0001d2001c100030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 23110338 1250 23109088 23109091
    0x5100905091509040b0c040905040b0a060b030c18040e0f0a050d05120711010b19050306060603160f02010e151e01030302030f0c0f010e030307020f0303090c040b030114 74
    0x546415401510380410401c907072000500003035001400e80a200c20585809210942007944040c0d40c1790070b59506001c0c4011409560301121006081c0f4040c00140007041e02101e000f0030348a501403081c00c1e02c03000c080d45c0c4c42c070094961031140101003018808501400c003941184850042010130410100c12150f890601072500d540004d0704429610400c0000403c82c089440c2d0706828214141606042009001d480080140d000d0105000ba4006440400c1d80701c80f4007400001c2035600c03820000100b600750b00350350f80a024000d1040700081202032604100740c0c0c2c801e2103804410300303840720b032803d0403608003844100324002d640d22b0f8101d07600140420b01c00000080000c801000031481c000da1001c4550b280c0d00100700c3d0b44d81c207140c01070012983c044200c601d0040114807180e03880b0001140b15141841902006546518001c80703c02072030008002107002c1e8400b42d0803511a03940364010f00e5100e110941c1c00e410385a1001804544900b081d0b08004400c2d600140005518040351900c505189030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 23111588 1250 23110338 23110369
    0x1605030d0c0908010b010e01030c03020904050405100b03010b03030d0c090b0403110f0607050601141201021207030c080708040219170606030d020102070804050d060605030307080c06061c0b070905 86
    0x4591150441d860b078032800d00740050482d034000b032140c0824080040c02d85036403401098109525291001c05080c040d4040301c030004009802081b5070324150402036180d24001800c100d11030f05051100c1440d16050141412070040100075514054160b10030038001e140e02e543d6201804a03035040081d844030b14102500c019405121101e210761064400c22511142e4035200700c1c4290424403510b00452400254241984c140240c0d1010764640c95000910881d1000c201c84065030000038055000c43c0ca99107210702a000319101823210b8800543d055520150489407840018038100c0020302501d0f01c0341c0c0d410340c1400100700710821192650110301050b0008852010301d60b00c02814868a0705041141a80784141c500c003c6081048903641e800300740c4a10b2084a10070903030401ca88050010f20b030301910050400130110b03070b511403a520701034441d5045428030000b00c0c02944000f42d154240311702240030408403903424441450780741d5614511080083c0c4000108050044041010707120300004244810 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 23112838 1250 23111588 23111591
    0x1110a05010209091b0711060f0a030209030705040905030a080a02120f0601020f0f0d0e06040f0f09060b0a0813050a0b010b0c010e0c06030403050a0e04050106030e0d020604020906061605030d 84
    0x2c3d1000107004c01403c01600b4035030504002c51110703c0110050003982d008552200b80d442c004000032001407654092480e100d181c0b5940050f00d421030542590007000c8110303060f01550b051542e03403000c12045440400c0050615001000305601c1c01e4801c8111660068036000c005061a0304404002d10581e0f0844520400780487c4c03051112668041006083d084481c800030144c0d070700d03101c01c01c0391203041c446000c105000250b00345000c140d80305801c0c0c0d40030380300400544104a65820f1061803902c0180b2422041c1c92500310003090941d01042164050105a180d001d1147c84c5c0c02070390508040c04c3e500581d104d01501d00c9800008007030a1103240201103d010107a11010078103c3c2ea030031109542d003a1440c6510649043e103003911550203a95000d80c1508056803980300781d40d01556500750380b10358158400d00c0c02c0d00104416405a001c502140341c20011546000c2c0c52440685c1e403005d0944004c0c6d4015800d0000403d6484c00a0040c08581c650401c01c640c859a95513806207580c0289004040c480d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 23114088 1250 23112838 23112847
    0xa051507080d18200a06110703080703031b021204060c02042004050f120706080603070806010e1b0a02070506160c03050c040b09040c05060d0b100309030905010201060303090b0901110a050102 84
    0x91000104a0464104c152040000401d07000030b031a0480a104480c144401044d410907403d81c244040f00055411443c00d55640c4550320b4018003d0902000c2030108805440c4c03540440d52002442d9020750714094036040ca020705080041d102070010040c00c83e0320948961034401d4000c40c144212101940c4810203a07115410301e402c01054107100070071240074224400200245040000b6807000702c07031043c140040c564923100d01084c01c151071504a040180714550000a00c10803050400e4490824554088a051010000b00081d44203c10a000060b440540d05000d1490050b0080c0041034840d0351003000c4410030b070b03100003a444141e8400d0340d8a03003200e5440c0f41241010300608440c150111000c070039510b442e60f036912414429010b454004d2002041c40c0f54140010f6109001c100c0d0000c09164880404400081c0a8528100b0803000224a5203000505500501941081ea90b258440c0800e490a10641d08055041030091504000c0740e0040c00001d4542800351f4020f8030300500000d40d99 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 23115338 1250 23114088 23114093
    0xb040b0618040206030703090804030b010501020c061c150503240901050405060f13140c01090801200c0c0a0b071403160b07020f030307030606020c0a051507080d18 72
    0x4198010002070107622262001903181407010381d102d0340541d040700c203103071652100003040380140320f8840c00902201d000500401804100d4115170704a510907400c44601484500c00c1c41230034001c1c40d0240754459800a08019080966001401320008140c10141c030341c0d5844001038a06168120324681d01c003404040041241400b101040d0b01983e036000034481801c0a5480340d5982900130b15070661300d044080410040c0302c40c0c0b0b101070f448580100c078000440001000c410b4a07030f14422130343c9000c140525400501c415040c0201d0303650840400310600b848034a5040101184e109080c200e08a00410720380e4101a51181c00b4480503000855019888041c00c0c5801203036071681190780c0740190b00600aa01c1e16030101c0f0810304059600036164404d98070f84200503417401c0041c0841592a020100070840c0e0140e141e4000d10440301d0355402c807906902043c040c4420a007a0303000321600040a00c0319001c0900307550f402000600d22503190185080503481c007107400c42e91342500401c03550960800d428103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 23116588 1250 23115338 23115353
    0x20405030f0d020304050105030c040302090c0415020703110d02061b01020403230d110a0605040b1504050606040303050c100204060c0b0a0507090504050907080109110a0f03031715030a0b04 83
    0x4280075038001000300d42c0c440e002c040c2d502e000d14400c030b9041000000010301d243e602d07034050b10011540509000d08600b0810041d50040d001401249003031000c4a44802000c1d1000030148110b0b42c0025440342e43c840000103001c000c840910050f030f0031000c100040a4101c0d0448003400c6591000c1d80016211810340c50031592400403c1820000302c20342c030b685c0b018a80b030003150101c0700140b03500388148030b00032540f0b11504040e0303030709400f40811381340008004c01e000110210501c1b5240b0201440d488100b000c0401040760400d8503401d4110350180014000a03002c0e10082500112001c1101d0100c40c030105c0400c182da01a82240c0c0c00140910205000c0004403020141c018905d00805d021a151101c402804092984501481507449002040789844117103d40005400150000d0003905903505208000c0c040007909075001702c443d4000091031195034500750003540d61550703c080300341d10114840b00b007c0c100600008440c00240056500c41e0740c08001001140d4481c4503444000d14041c00c0018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 23117838 1250 23116588 23116603
    0x3071112030408100522030e01030609060e040b040206071209050103050708061e0111030d020306090105060306130f06180905010627021602040203010e0f0a0b0a090e120a0302040503 80
    0x40c800e910900003070241c510046900e440d0030041d0080096180d0356560710070034180d00b0400008059142036004c40c1419070001268003a1442a241401281e0361154001700b2510140b00e0302600041280215002070403241071180c0041c001416203040240c143c40700400a00442800c0340410b482c00c40401c0b0030758042c01400e501c82228140240d0307600c0e00394042035051940c00340041c62100e04681008850f070254104526600503003003102c1d00c44a4100c44440254401e44e4114450180038000045a103408011079206110107000219240225015035010301083c044901007651901c00216a41c511201400f2000420103c0800ca1003201e0400d030f0b00315030703280d00168074802c2201c404100c1141102005030f0380280104005a4490242c103681d040f05110f250003d40c06800003000080102d0440340041c007480501c014181d032900e0345800b407812101c0416040746c1210001004112004113a030098960020420030307124501901d6660800c82e80c888200360000c81d034046030034005806d0401542 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 23119088 1250 23117838 23117869
    0x80d0206040b01120f08030901020901170136020706020a030b010305090607050705070515091201021c020d2406110a080403240f050103061109090105040e0c03030711 73
    0x20046410039440e00c1030080350501134803480580d024503c004100d0041c5115060b103800c00d0041d6282e040400c2058080d50011007414002203024000f141e20604201d5414121145040030281b40307c0280700140c03200c80d620b444001221014080030700140040d0004203c0c0714410b01005a9900700312401500f102d0b000d5a90320b0402d89028100201c1d03030000100d00e41c000c040ca0030006c0c2c5401c500d141046c94920103130071075034203e041802c001030b40030002e502601012608968600c007225912100600700e0003019520f183d0a10179092503100000c184d03004001ca00c011407000306054000c1e40b0034034800d441d50564100080d0000204105103a84080d5480b88071135000040c3c8a04805074480840d02d006500000e40444032000000481d0b2414240d0481c3d1007403100c109021142490f40f0b800c1c0201000d1006459840c00c100100c02c000048808440c1222002080a206a402d260501000b00050410340c1d03d0743c403030131340c00255991b000c00160003c03500c18031501000b20009420300c1152480441107 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 23120338 1250 23119088 23119093
    0xb04031103070209010302191d010302044203021c0501050705040605090402090307150804050705120d03050603030d0f060f05031606031e020705010f0b060906040e130b0f01080d02 79
    0x40b000140e490680003070450390100c641070600021f644800000704103179400302280840800034140200b1a511001d412a8000c8800300aa4500a980b40864003500700c200e0b082e4080e040c58480c20000c40c001c00f48404c00440c82010140e40d00da0780420300305114240f541942c4440200a4400c02c502401290ba002c2c2d52842d00300d05051a083e4050801e00800c840944100c2e008600c0c000d50362020040034000f4020110001d585d01d05c207140c040c20b02c5a0644080e28170380a00b0300301040c40c5c2050380007070703070035800d4900100114841c1e80d000b10f00034007014050581c540400c10420722038809134056508040c0050f07a000403454030b03100042c0500e6660307510080c000d410010078224002030301c24409040740e100703040104010120110a041d42c00039402c0c13090030103201007000030a2000560150210502509080180b03234901c42c10401c45000e440e200580c4070744108814401c4924910385150850500e9072001c0c1c02001c07540da8410001e07011542091503064140040000e200f0410803a1003801c0036002 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 23121588 1250 23120338 23120347
    0x6170303090d050c0d12020d0504080a020105010806010e01050405180111130801051b0c010e0a03080a0b0f030607030c05070804060e01020714060d020c100501080601051503191d0601030b04031103 86
    0x4c00c0d240d500006006042c171a4492031514901d5094048411114011034104418a0507203042c010319040031503040300541c0780400101d82404000780080c1a94004414603c039607181c0f8007000043c10000f00840c006c11441c8a4907400322109004803c0403203c002d003044d8582c000507042601c0b05e15142d1018900c0ea050109102030201c01c6ca15048103503440c104083d40d6a02081c0c84079014101d8005002c80500c512800001403590103409e807401044070315010b02001022104004907160031141c82d80d403640107900480c124078001c1e4008410440740d400c10381d042c0358503900c0d0182d243d0800d901c204041180c507035079002d00b580d06015107070241c2219600320740e4241c4403401154560003100a07d6000b03a0340059101e001d208100104014403640720b406219544e15000350544500c000c3c411103000380d00c0f0301c0603940690b181704140e1740700e8042001d01c5842d0b01d9041d003e0601401006c80c203c080c2c4000301c03400c02c1c0002c1040c8101800b85024a0002513507040515000b0800301303004160201c907800a20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 23122838 1250 23121588 23121607
    0xc08061003050c09191203093201050306010c08040b0721090306020306040b040906091202010b010221040305030403030801060906050a1209060b030106080606040f020a0c0f0606170303090d05 84
    0x10503a41442003d89000604040902c0ca07014568180e0708402403624408840c1c1003010340c420707040e0094441145001608071aa141a81d00116401188160390349c180742903c5515413041c4041c2d03500001c149042082c000164072a0002a030041e04000012003001403032006101d081103045821082e200b00845550100c2d4030000c004011600004001030340000102d103150759540c00c555403010000308100521641403521100820644900310345071f0b0303c824800741071240107104502380c0880c184c000d0b100132491283c803401c0c1c0d8082c4450103159804140008400309038100b01800155210303495a03020741d41031040242c0100070315403001c020008200a0082c0050b440311171034906400c2e5480c040382e840c00d1460104058000c80f0b18454041d860020300184041001504d81d01078481910100a081c0d6101074520a0b44130300c0002801040a4411402c000b545000001c542c1d03500803000040c1c1c0c25200e9514124110700440614041c3d44084184848400d060003140410090341c20034919159102 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 23124088 1250 23122838 23122861
    0x6030703050d1409100f09090c091205030705010e0303040b0105060f0a2f150c0306092206090b040b130b0604150305030408240c09130f0c0806100305 66
    0x1c01c0b400300710151060f020310415550035603100c900c004090700c9040c0103010008100385118011007001498460000425a06c244034076034003050181d66580e142400c010321000c1c071081e11542195244010000a80818420b114043d169450700d400345030361f0b00381814016004003042e00107900c80e0f0403c000850002110604403201c0d90414102040d00c103059940ca1030000021017112610550f24904445090030042080101801070600d070141c903490f4904610300a00003100c1c80d641101400020410103c41d41a071049655041c11120a4142d0255a0503054540e083e00440e02884520103001c10055454140380c0d22080b1404091034900f401e4030b600140f1440900114007a03562102c049040005060500e0069a001001c40e0f648580c0d0307250a960764000c4401e004098002120406104000c10b09054018009000d0050610601004100720485c1e006d485840040d80d440030007081e20071501540000030380399142d00d80185408402e2018040d5104a8a001c141c40c2c6030821003086e159 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 23125338 1250 23124088 23124103
    0x3030708040f02040b031002040f06020106140114040b0d0b01090504050f0a051003060e03041403070b0a0e041404031d01020c0904110a2d060e0d110f15030405060603070305 76
    0x40342e41544402030001c0340080c0003084155400d409009022030807203100c0c0e00100100d840c410601500740c0e544804c1242214524001c55208094141180c0a9580304180504d80074040080041c40c0c15560103100349954401006074101c84d865060740c01407980c01c01c0000e00201001d4405100c980307082d946460018400400360398565545101007030310030070003000e40700c00340d540140e04000d0754881240d1107a8a400500c84c0303c030744081002407441d6a04000c180c0d082202c0c13441c01483c1c14032031090400c0c2c8120742c6035029a50800c1c0c2ea8a4414141d00d00c0040a40c040c3d80070b42c5401d43c80c1000401d2110351154580e88150565011340c280d42c1d115100c0c411900c0c1e1041d040a82031020010f000001020600660f0042c00340602c0081c0c2c4c05e920039156034112540d10030981014a1040d03440b9425510140b00150031540000104150300100d0720541203c0c03411580200803160034290b000000b406517240da440420fa015004c8100320030898100500341d0014000c83c000c00d007080c80c61b034034142c0c2c4011 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 23126588 1250 23125338 23125343
    0x6080d0c03230d09030903020907050c0703080306030c0604060e01030c09120b06030a0501021923030109020a0903020303030703060f0503030414010c1511030f07030b1c05160b13080303070804 84
    0x164804420211140384180e0342c840f5078000b802d00c41d540346414000c01c1400d250100346e06c6051003a0100742064003402c211816404403074054450645551502800c2e500000c00c8a5014021295104016551000100007802140c0c540200c007000388030006084405011a00090100303081040c0308074886103a1548500e0760000e00703082e8580d81d0201003800c0c4801508002c01030744c0040317618810111800d40a501e111074640d5240c884142440c420210214103640b1203020040400041c00502a550000d007107241d031030308040d000aa92503001c2451a40115074001c0043c0d542e0805020354242c0d0408113004110440055081c6030900f1118152035104149550500a006550380100300e250191104202c00d0a0303c204540e40c414501c42c0b590768802c45072414409440f20009070801c0c028403c00340c056601401c5d0f03000301c4218000000c2c08087e4058103640c18442c034402000705070314001009024200c01c20305507480e0158124001c4104c03134107802880194000b80100402117600803a0a070780700c0e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 23127838 1250 23126588 23126627
    0x6090b07060204050a03050d0816080103030c1a04080409060816051018120312020c0c010809070e180f030711010806040204090507020a03110106030b06040c03021201030606080d0c03 80
    0x103059250000091280d98030090700700ea0400310001c1440404200121040e1141d11b5405548d507500b078480070788202a0000102040604005002192207603080e0304005101761804c0030079004002e0084031043e03044030300315911080014180090300b00b070b016820051000100528044070071185011744c4042c43e008080c0a05c8100d40f07000b8809100b281880b504071081d044a40b05961140312428005201c504150085001204210071509030707442215100491a0042c041d12110b444c01103825074030180442c1040c1c41600804541060b034a25000c1c0030b001c1403085089040301092445040c41c030b002400c031155410520801010134003084407003c0340142440c050355241e542d1030000d07000740615040740c05140e251504002401d5000502015100d00945901c3c0c4601101d2800c2e900740e500a010091840d112000840c0240c01e10340c10410780b462840c18050f041003080c0e61441c02c14a4241d0058a100f600e8900401130348030140702c1549007150364940420385100300d45010304902009100304030b124 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 23129088 1250 23127838 23127847
    0x4180c030207020a090c080f16030e030903030c0a1e0816030516081206060f040504050c070f030903120504061b06060816050f030a0b06130902090423010606090b 71
    0x85229904941d44554010f11884845490b604201e0080800c07140031404a0300c280049808001c2c80c1c902540b207802070404030344031186528400c030090010303400e15580900c024883c0074842da40a00103040c0c0490190001c010340000ca0808001c05141c00d0a4070f440307050f4011828021a04080c216070310444c1e0800340d4942c1203a0b40c03400f21510312a400d00074180c0300200100c5010020010004c8c0f1940b02c04000b45d40003030b180d800800003184211040e90300b81300c00400c0300300b10a0a083d0000d40e80b046c6a200c03694140111512020300b4080400000c0700021410b5809200b00003000d40440580d0040d8540a0304041c1400c0000c1d00c0c802005026504800282075000c04010a03908010064882c07802512400b1501881c2078100310818054079210344400000b065980c00e0000d1a004c0b80c54200f040170107140c1361102030000d845c00100c100034109883d03421041c00768440c400002d000f248103003140004501003012214034001c0005c10402c2136410b00f1002c10155030b010a8070010340c0c2c20300144907502c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 23130338 1250 23129088 23129111
    0x405010f0c12111e0304051003090c060201021e0705060402010c050f0106060305060109080c060412140105040506060907030b0307090507090911040602010c0903080301180906091104060b0418 84
    0x62225240014a0800d2142e414204030340d0064034103042582c0d210490f8240d84110404001858529030340414030742c1300740300c10040c40c904100650381c1e40c041d41c2030008811000f030b103038513500f01c64541001015070f4000a40700024080800c07244140c6261140340350030310303e01d0f6031555182d6201602c003038104240034006ca000c0c04802d111505902010200800c121590341e60090042e00d800c95040e030204656400c0064901c03c0170030700a01010f402421985400d040040c0d41e407114060322070948160591254840c840364091007050300460040e40240001d26014041052112008040800b050b08092500c0065280054410140c80f00b2600200f0150f6130b000084400640ca5841402108c2c00d084954484000c0c2e0300003401550741703983c0284441200b514003a1080421b922000701900c80410040154109000501e00d81d010b2030480400e2940f801c7c1c8503c030680300035a0003030340e040b080c2180003142440c282c030500b030007414009810350502e49040c0308070310ac90307001c8039261040b10f8541a02010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 23131588 1250 23130338 23130347
    0x105090f0a0902040e0d0c03020f030406020c1201020909091614090a09062304020405010b0f0d0207020d0614060405010f0602030703030b0f1206070e030a2310060801090203010614060405010f 84
    0x1d00410300800c442040d1081b0f0001020385004020a4016000d0b05031403024400000c0101e4040c2c1c1c166030002c2070b04014040500c114070b002c00e031203800e03695400d0000329030365a515211540900f00714002060340400146c08034010b074605038004852061103646440607500c3e0340d0400d0f80c0c840d000704030024464210382005400f80c807074a041c4c201c441001e80c4454030381444080c2d00f03a004500a4404111aa80321901703c0403d200710341400d0041c0c0f0003403280d084a009580c00810318144060608807400d21181d071441e080d00c034011400c050103c07002c020007040e810075225490040802490300f0900614040001e500c078815428060b04054444404c4540c03900c45002208400c10050304c100380701c41c8086525919403006403201c40000300818060f000f14078001944464646e000301000100d00d0241e0100c101b02002030311200c91600802201d48030500240c0305903402443c01400100b101c21a80c0304060031141a40c00441c1040c06c4044140f6280d1100c0041d241615004c0c03c02d013007640c44071401580e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 23132838 1250 23131588 23131601
    0x20703080121050601080a05010f050601020a02120f1006030303140402060a0c020d08121e010308030106030504050c030f010c0e03071d060319030e04110a0804080d090203030409050f0105090f0a090204 88
    0x810f5480b0b080000281d0103c0080c1c1c1e041c1d0b107402000200407a01c5924002e00030398106540c07282c01a40500401000b6140c00d10f038a0041360b0700401192402802c1480b182e081c000c1e9540018411680d610040040c160540030b50320740e510703585e0b12800003880c190380040c2c07003409024950420094440c0d16541192030342410306c40226080071855441d19420195400136510407070766a890010f0881103e4080b0f10014000c5050700c0d80810094116802d200b4101c000b000c004100341c41d1441041000030035a20b0502c0b2031501d80c0340c000e0001c9215906a030014090a6010615600a520847d81040106860310a4030720030300c041c40c0340540e503440d9000064505101d11510300c22046404409108042d0012450061a64141e13800c2c0003c1d411100c85803801c5c00f5080c0070b138020a03889800100006c01040c0100501c0205120001c0c081d91682c0103e80345410680044540d10798030024044000022500e0350b00400c0c04441e004054580003074640d20b06600904551740290b1502000e004564072900f191 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 23134088 1250 23132838 23132843
    0x50d020702060705010f0615020d051312050729040506070c0503030a030204090b060403211e0504081501120b07020a2001030c08060f27101701020703080121 69
    0x120f484108604144d40240035107054515154034050001030a2081100c1b12a400c0c003003034001c1c10b506100c2082c25505a8001c03d5034181c450121003010070a02d042440c0d54000700c0c0102d008240c2a0300700800d07241e0035400e10b9640594207150700740c66040c6403180b400721019035006481540e2110780718540800d000c0c08542103140e050001150080e415540340d03014000311040400d0034880c03d6100010300085102e50300019112805a80c9020454007050300020001c1c3c00500d094a09490000c450030340111031810508002040054201329882080001450864842c104800554502002c0d4550401e40f40e1006008491020010b010f040c000e1281856854000e0700b06101c203c140101024184000a40d0354042031600c0907201e40107101c3d031f40e043e104007000340c07401803043d02c03c1042020354282001c800c0c940d0388503034840b140700c20301034030130f850241ea007d62041c3c110506210030b219500c44000e80c141d0090303105114100209501c80385c00750455417007000d65001c200d504203185001d1804010007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 23135338 1250 23134088 23134099
    0x5031b0301020f04121a1b03130209010b18040e0304030b09070504060906080d02060402090a02090402090d030302030f0c0703140c010905011a03010b0901150809030c0703050601030210080f0106050d020702 90
    0x1807141e500c04219180d40d8031031b44251402031801c603103441c910b5605642c002c41101d4401b03545145180680e00840d08208800a0b0700d0404055a0010314680c0098200d42c208000205005c0036220b94101c6a0036903c1044605010041d0204136541d23482c000c034440a08088291004602c0902c000d001040191402500c05c1c400643c44848403405044944120607151203200307008000f113071010a880e4051a07000340424810b880e0414100040d400c980c001c2c2c2c0d8803a600304400c0b611303580c0e20520100482d10075140540c4a280c40600148840301c001c0038403902840803c8801c001a61103100c040450031850801d5888280400405004041c0c41000808c190301e08200516291804440d030f00700b9503812002880302d8200d06007441009207080c4202c52501c01030b08990b8001d58000d07801c007540200080d0459081100c81c1d80f8140c508025075209031030320f801407401401941028403040d400c5100d24100300d0301608104613080094101481400200500400c0c0a0101c103c00c1c3c0465403020f400800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 23136588 1250 23135338 23135347
    0x2312010603050a0210021507050d0605060301120b0106020303011a0d0908030901050f0c040f051c170703031a0108060904030207080109030201020c06010501031803050913020703050d0b01020705031b0301020f 91
    0x1856a91540c5409040e803017080c000110810862002420342c0840c0c00c6500c1d0010795499080003030700d03590451034089000e951941004111900e07000c003c0c500070200c000140a07040414140900550410780202046400406c0140417400100401ca2800c40d05c2c800017590f00c1180050903401080780900c0100382c1100001401107072041500a2802840ca00c49551800d844400c1e0a0600e84980d01c5454030350b120031402088240307080d03244481c0a10866102a070550304544d274004241c4481d0203500e40800e0007085000c0bd03d0380c90b1044084022a18800c0f40c0d80724180c10019140c034000800041c4103403c11400a02098401d20440703002f41b00f21002031001807058500a07000c6d410419214030f2600c1010000a02584240075030b003002c00f00406d1605035414652000c035001d500411180d900401c0c0316618555110481c40204045d81c040d54406407200641860081500c1c0200c010701e04550100e0401d009a80c0e0203d00412144102c200d040800005800880d000e0b02482d4107840400d41d000c0f4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 23137838 1250 23136588 23136593
    0x60801020304021306050310051e0403020706020601060f0504090c0309061802120a03050f0d11040603050f060405100909060b040f0c02060a09030206070f020c03010515010e0a2312010603 82
    0x401541c0294402ca070040e151808125a504c1155503c3c810300c0e506900000100454017104d600241e00700404881699100b0b00d0043d0008903000b00355002c130016840600108855641840b0380c50250529182c180744580c100c44d0010400d000b02c3c019440b10341c3d074451124000381d0080e0f1103a84000c0d4001014015085803180303000c1094000513080c2e01459010165445904000c030305010007540c5074988908000030788840e00ea490300039000700d00c0e801d80d940c40159140001c0c0c20207072008024690f40032602e4680041c218849410192100380924200f0307007400764510155440009885240d800014499420f0400c50064201c058140d50001c2c41d00703007510410b9255402c1000801103603000c43d4201d498458242c000c03a00300800150050b0072640c04501c04500c610a404007e5001c0e20403903004078030910001c1e0031513000342e846034500c510800303643e081560000324160011000302d41d03007207049140841c49140388044800e80d60708404007080808891307403402c02d0054080810002045060b8480c07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 23139088 1250 23137838 23137841
    0xd0f05070209012601020f0a030b01140409050709080a020d020105030603070b0301030809120d0f08040201090504141501050a2a0804031214250501020d0c0503010306060f03080f030903040504060801 87
    0x10a2800180c1c50102c04c8800d00050003140c0202d48000c0009140c12036186044004294041c3d44030704100b9030750000e455907a114405080501030741c00740003440d030411820152002800d0742c00000300380c100c9101100980d4a6814041e038290302805e010341d80356603000020f400e01d2116040061844d80200002c01404010800341c45816803e861540d81480c007001800d41c1d56028070302c502300148079035107020512840b8100c0907800070700c11306002e4001615030001905540310030300d2000d40c1c07418100c2001691280c01c0c0040d85404000e081c40c500e088000d85005091034000050b004080508034090740b00312840b0f00c2214034841e0082016900e40780c403440c1c5444075041c18a84032000070300072456100b101c05001d044070711910031070142d150000d11421568949404450042d20507540c00e000c01609415580100658843d030b903038070a136036503043d0318018044642580004541c004402024800610203034126070f5051503658070942c03650b60305a20342d45144555000300c0c2e0800e0401d580090501c205 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 23140338 1250 23139088 23139119
    0xf220309050a0b131202130c090b0714070b04060f11030403050d080702070e010b07020d020409020402030a0c08090601060906051602031c03051305030306010e04021e0a0807050306030d0f0507020901 87
    0x6990480c131146030780d0b0408054980052002940c0501600700b02c01400e2002c0e840103980c20700c0360400651341a0f40b50a00e440503004844107607a0ba0030000010111224180f00702d6024051450380d8504003818240028401c00720900c141d4148040c802d90300f0800c2e0000c00580300150703444022500308240d415001400154162903050140c410400046031000c801007000b816182c038039100505202c92a020400001d840c039800b41e030019900c0e81d007040942c075140003c520034482c4000200d241da12880c80107204520040c000e001d83d40201d00103116060780700450300c08036400c0749041500c1e2402207041c0780c8281300105c0c00035450b00c82c0c040141c020014800100d0000360294a0801003a610174491358084a040c0341c0050081d041000020034640c051a060f081140024000608104441c224144500483c02001c14001d4006c00c3e004820340c1e001c00c51035070040c441d1500601358200b042c0400d0b07480c0c8021200c80180034001c20107c1d00184030301c080e580041d80040144403996924045c0290038142c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 23141588 1250 23140338 23140357
    0xd120c03090e07120207031205010e060f04020c060406270308010612090309060503070507081b0d09080604030c0f05151504020405030a0818060409140f220309050a0b 73
    0x1030340100181d010b001201940c0300d0006511014148514114074500070f60041d0310840c244080c001c10310b08110683d1080300d01801d131070041d4981a041000401c41c030175400f4031016201d240104207000d0064800309a840c1c01036881100407030030380300c580161959070b40441010314007500c1038103010040c0f40e8400e2281341281d045803190f154040030071a0700e10a503081c5540103804941030708410006144600011540501c00340303012403d041103551944c0e110390100c003a8a80d80010800104110a81800786140d061038505210006900d811030300c1c1d845201c020710260038020700c607030305805200f400b900761015580d000e02602c66103101d444102050b0401070b5524540f00102c00c0240304241424400c80c0c00341e0301d000f0020005184a6503e80c81c40790300041d07450b412030b80581ca02c48210b44642000d403000e4609440f0114030840b0041c1d142c00e0200009018404203000b1320b00380100202040000c5a040c2d00c40d541c41d0304050a6410140c503002c280e42d10103500103d100c880001c40806507000307000002c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 23142838 1250 23141588 23141597
    0x2010603020a0e04020d03080907090204030302150601080f01030b0606090603070215010e0c0d050901090206130e0901020403020105192d031a0a15020a0602030106030b120111180d120c03 82
    0xd40b0f070b0b11481c001810071036000390860081440f40010a006076038950f8002103182c101c0310415207a5400105a80044c0c1c404c070056840b840540081144a003070042e803207202864004002e16100042070362135441844041c02c1c19500e00042882070b1101c2080301d002d508040d01c01503807070a18440080d17070784070740c1c0181130310f0650403400108050f03003c060410f02541d007080d40242400126006100101300190060030150368400f000e10042e01d03601d01814002c00d84441c4844214640010703507110440040c90206a030340304200c1840180e8206041c0c2d00c4190074100b505034140d45600c0c0580d1500241c038081030018815003017540e201e100555140d0480303c880d903000d002c051500360003c0c10402100c81d22590140c4040414840803440404001030007a10344115a00d409450b1955801c0740d200f17801880000392901602e034072505207100c030f030700d07842d220103000700520192900303294860700450418a580075155010414640d0312040c966203030715040380d1955103a00300c40030060014008408101c2c00b24 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 23144088 1250 23142838 23142859
    0xd0f02030c0d05130b01060e0d05010507030e070803090a0306050406140c0405010f1e05130f080a030e0f030d08060607050609010203070305011e090f1407030606080a0908090f030705100201060302 86
    0x200400c0960040c13140c0e0004500d00c1c0340c1d00f0140185c8142041c80b68207134000300d0018030180890424080c240c02110306445c001100800700c010282410710b1500141c0305c59104010b0305805031184000282201d8200c02c0000e866101c5150000c0940794040100c503071421807009004074000c0c0c030001030084800c00d0702c0301c90240704046419241480c03414100b4042c0e1080d00c407100b807000e020360014030241e15102050b143c100e80f035151807803001d0250740001403c0d61140241004040e0420a901c40c8500225181c40d5000000000a41d440901a1194080240c14800301d5110344645044c1c412040d03002d800e98030343d8640101503034002d40089a00e43c3c0002e090000004203050a8403404d0003603803079a100054114100441c0801500c082c15440044940e500340101403904140c0440d40034500d41d581c04a00c070323407038040010012800a81610106860100c05c4000102d803c4200e406101003a1810038540d110103001078180b00e0150f0040303401c110500328000109906504c4501540c1c400c440b0140750 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 23145338 1250 23144088 23144101
    0x105030106050d0c0306051f030c06180315091104090609150501030201020303041103071505090102060a1a010e0a090c200a02010f030b0a051005040e130f03050d0f02030c0d05 77
    0x5003c18a024000340f01500e010320118203650015079100c1e032541084000401001110b0070b01c04080e60003601c00404a101c24407100f640500c0088108851040415103503040d80c40e217240703111820411594171962071010340100500100c02804405005204000c1001f44c4c0c00d01c1d501418905504482c1003c0300080d24a100c0914071a45045e240c041e4001c605642e00d070750f28070014a42d0302110580c544504403000a05045049e148400300c49551b481544882c03000c4006032030800d001d00780150440c24246040030303404c840f4100c0103014009180c0b00e1000c030f100a0100b803442249402107251141028543c0344102c0c4c00c032000748031512500404801403000900030944406841000038001035000d010907041500c00c0d0002e24504000520314042140d56400255020021245d07450210307001040070080324444a48085d17020351501c51910044c0341a07a2400c1900f02c50340c400070203109011500d82c006038078662041d80c0d440c22100085540b418041e8414603a90480d820b404a114145030000d4070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 23146588 1250 23145338 23145349
    0x18040207030906140c01090606170a0215090409050d09030314130b0304050313150906110303040807051c03020d270206031b030a09030201060b030103031409060c0d08010503010605 79
    0x10386030503944680d00982481030450b0259804002445143c0e01030103903100a1100380b10380d083e0603210350700008825240142014441340b00b4124492550480c48008002d40c940701d4400c040016052801c69540c503c0a0014005100504010708288100040b000700f8940000c02c5e0b00681e800b03a00c950007000c0c410481c135031192186441400c9895062001000404c240318051364016200301c090700c1c10701c072030454140141a403680c46519070b00c60380100f812a242d013000d004000307051580303040d0030300d1007603800c030f940d42c03884081c0c00200100030000d000810b201c418131819401c22840300715226500d0310601c0090294005400d0542c0e05868034a408104000c1141c1c2e0310b14091203c3d070342580ca03031940d030200500d0b5007000b0a042100b031000c18011000c55a5080254800c1001800000c0c01c143c0c2812f0003400c540d00c607044142246000c00050000c0381e00000c80300c00385032884818039510b9407808045240f50003180c6019440c0c1c070807401804c02346038112520b9416a44142c000b0017005603120100702 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 23147838 1250 23146588 23146597
    0x1115040b04060c030903020402070c05090901060605030c030901090f050c01080703020301080a0609140102040906140301050c1b070b030f0a0525030e0102300109110a0c020a05060f180402 82
    0x400c51002000700700800da02903229010924000c0c1806180700f96290085002c1e40c0c8034101c2102c02e10f5640d1000c1c8030780d240c00884160041d1500000f0410507092807c042c060b488050005000c150000c000100e80e40c0c402d41240c000c0f19070000000c5106030f0103213043e036910045030741d80c64086a2080d000600403032083c07080d613049803440c8008044c5031400340c035400c0c0200000d07807041c0d4440350000d041c140041024001030004000003c400074207145041e0801034406006081940f099040134188420240c01c1c0d030a540c1170240291a1240f02030451290300d01d0050254459213180102000b00709105520b6200640300e002c80410074030180c0d9480c0b24902c0c8461784c108505070748280c01c040e0101d51034466802400718541785400185071540c034841e032580070002036801c2c01c02151a40000428518112801d03401428210410b100401c1d40c00e180800d94001d00782d4000411603400d01c00c0c0155035030048010300410014180f90781c1c4000c2c40c1100503240c1e000d00205503400c003032031011301d60500307103882102d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 23149088 1250 23147838 23147849
    0x20f150f061011120406020f0303040206040618030203150601030e3009120304030515060a090f090f0b01090c09030209010b030c0d0f0207021309020307150c0f111504 73
    0x200d41e03600d1000304074498181110110401410388003400e1010010000b28002c07030003200c0300d540c80f645004802450500340000d00500c0c3c3d0014814403006072144026203081c5e9050f800c08031821200c1c1d5505200050851b440654236100750441714a800400030034050080c9820780c0d0600013152405e2581d9030307414404031402d4052181e001c0e104c905503103104080c01c030208bd0303100302c1d843c209103080007940c41000c0c080303211415000003c0c100101f2004020080440d00c1c6a0040d444070f00d0000c00058001c61184a40300300303561221181c5c0c451144035413111401d1940212607401c03030b058030308008070310356000d0241e0b600080c50f0001a501c024001d0b8010422a80d0040810407917a01342030100689400140081d000804140060340703c41d101406400c1d55042006401030722100d90f03004010907207054100030518149000020b0f00942c8010032114107554036003220b98041045520100d91104000342c002d0803452598a2507810025001c50408820f0000c80710540e95151401001c01d86201d1449403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 23150338 1250 23149088 23149111
    0x51e0103020d0b121005090607020304051905040c0306140105070203060610020f030304060e0c01080108030a0305040525030203010c0f02030d091b140102160609030602030a0f0c020f15 81
    0x40640c0300380c0082c4402e0a0b0044082584000c11000c1150201d480900074078540140d11000301c3c40341c151241680c0a0803640040c0107509003600c0c00703902e038899400b610b8096180c20a240c0650302003010400000c0102800400c00003154030b00081c024480b41c00740e560742c6405940380038a190b01c50419a61038a80080280507240c890004018160200401103015400741c0c1803446280c0c1c02c144041e40c07195020702c80100300b545400444070b0502050007901c5051155100040c040c41d0000425160b00c0821800c000526449a040080c9424040480c518076801003180f40102c03141640501c1c81128400d60007880f03405031f4010300b0b803205011064880c0c0181e20500c040842c110240d005200a45e00406240341101c90307001b8610000e10198001000c001000e0400c582556410010101019064050007d0050904e40d00030240081840050145600803000c00c404c21460f600c03040c40803581d51000c12580300005c80281d00d800c80c4400c109010b01594003210f1225024000c824401c9914485 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 23151588 1250 23150338 23150389
    0x100206011a03060a03060204060c120305010b0d0504050c04060602030a080115082406070b07081003021f031104090504020a060305040206030a0504110a030309140303040e060f01140f0301090605 85
    0x305007103075000200000e520410f6000004081182c0d44010300250020b41c0c0c07002b03104843e07401c06240c01b60b281c100e1601054500340c010020400ca4409640304160844070204107916641070081c505811004d040343d02c285814070025200c0d400000400c0b0010070750710b8840c007036aaa05041544034039050660350105100d00c00203010540c040390791202c080c5c0d00300070b50140007501d84040740301e5400241c03049654005150138040701c5a040349040c2e80c27146101682090450440c2c2c0440d0101165205a0285203400803da07400f89004c0e40050b0003881820300210340f0f0b940d8452610019060a4a0981c0602e52000c40812500d2003402110300c6560081c0c50b0f03515584072501d4460050a00520668807262a00507242c85503840701c12510045000b80d84407081c003820001004040f07507164841c5446584208003c000e00685812029030040f000c03228003200072034140041e500e400700640c0300070403c0707000908020003100d0034020f14180c9072002d0040050030f48a40602c0f10540302c0b0b107264082c5068854 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 23152838 1250 23151588 23151629
    0x3110706020f0d0f06170a0210032c0a1703040c060e0409021c02030105010603020c0a0209090a020a0b0406021e15040c09060b0c0d02010207020901030308090a080a020c10020601 78
    0x1c0041c5504400325030401c0ca40402200c4010031101c034050040304807902c6907020880c00ea44242c00b1015106c0c20805000d60b400144e0015940030956109070741816100d4010792403a014018010803100d10301c0342c8080d14003003040201a2519001481103603895041081d103020030724220305982c0310b00c0c1c3c04003000d0b00341c5080c400300f40e400034200c42407030740d01ca81c91703c4060005803101c41070740848600380307910b075244c0030300610406003560816042281090300c14003801a40c00c00c0040c003040301a8044d80c039840b2a860b4182e8160820045210181d08003040d194001603880e107003401041151600e90039204503c84580d070041500c6150602c450b40341e84014640901003010100e820b4010b40310300c514840c42a40c1d07480240540b14143c1c0036144800f030200d103052001c002031210110440c01c5100861821009500240c000d04060102908101c0e032100098069901001080203298100c207245e501c0e86400756009683c4e031500c0c0f0700c81f07001d400411003600829000140d0076060340c55001440da804610b65 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 23154088 1250 23152838 23152841
    0x9020306040f0606090609020d140c07060e0a0203030f030109060609050a03060e1f0603030806040b0907081803031501020f010c02300403050601050a14010e010309052401090c03110706 81
    0x220199500c0c4d6503800300180ca00e51a201d51001850460f501585800c101e9040c01c0868030020640c03840ca03410303402004001c20304401190310301035021100003581403118002c103181c58070300301000f90544030000b140080190703c2006541210420745051060540310702d02111a19228403405070042c80484080c0001202c079003001d51380b03205910848690490400f0811482004030310340070b2030942d5640b4180b01745a4006503203907103c2401d40d400d01014142001051407900300402d80c1d000c10405001040001103101091854950700381c08490320383c140004210034139409140c48038050321840d2441907e100c018041d0b40c4523054140c002c2e10701c5040ca8603596103c01d034407003511585006c1840d0030914403282c140142001c1c5002d20000e00c580d60402c418810146290703003281e9001d91040c0e420088036030340044d800d601e0700420310340840d0b402e6141c6021071034a16030101c140300d140351341002c0c03550308941490941d040b00e92542c010702500d88ca440e010b40843d10802c1c0101a40d20042060703401003000c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 23155338 1250 23154088 23154113
    0x3030504032d030f0201090c06030c0f020a0206070303020a021e01060f05090f01030b090a02040608010b2103030415060504090f030305060a0f030210140a0c060c0302030603031b030d0614090a0902030604 89
    0xc4c3d00001c9105486907407000d25450440d040140403076680e114072070703600354000e00421f10b840f064002844800d0164000440c18021140010201a0001a804001c0d40700744040c0b6406001455480128108000c25074042c080502601400881e440360004062515001c0b0702e0050030300288002960342103071244640030b14000c0c40b4507254860340500c2401612103105500041448500005409030460100032090b030400a40c11404240f540700c15005520110440341c02030fa001704a940d0b501030b221308000281c81e80b6407000d5802031034a030008090001c1c1000340a0481c1c440d690400c100d64800c403c0003241d00c480e000340f003202e141d242d4085c4014104041d11a0b074401c4181040c5000340503a200d0040c25500074160080000c16483c42e00b010455203011f0350b40e048515080660462800d10007281e900d010f019a0820074410020301d03003000d01c0741031080700c60852000d1401d0084585510074040d024840d8444a80200270705000503c0d10300f50b81c404c111116500401500d5141c441da12000c050350350 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 23156588 1250 23155338 23155367
    0x1404050f04020409062c011a10230d0e160f0501030b03100608071a0f09010302031f08030909060303040303140307110601030309080d1403060402160206030103030504032d03 76
    0x6590006c45000403188000110f0301008884202c04450880b80b1682900e946020001e28005501060919a500c05507481101d00e01441d01d1070400403a6006030100100401249510308000103000c000b45030140c010100c01130700181141e503030b041c411008560f400518031030403035010f0743e64500707000e250f100c0d400c11a000800101203c80d030920b070000d03400440d8480ea21900782c952200008100c8250502103181d01c64050034801420b004251501c8001c41c07041040003410035500100240c080d04a015149d48a01150100c903452a0345504400f542c07944107805403881800c40b00c000440324a0300204940680c0e5140c0d850805255152150361150b40020b802101400258100038404107810001039008500a03074600c00c03c1031501e03000703d0810441e117003014100240c45001481c0618100c0031030b034008100b0340e001a900d00c00006800e105030081c110080d07010340000700000a044c0d01101500a0ba801644640303074074504076118164500d10014146d0327100307000c5041040800d00511241d50b0903003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 23157838 1250 23156588 23156591
    0x20711032d010204090612020a0b030903031302030a0629060403050304060c02010909020c06010303080901090308010509090f030c0105010609080304080714040f0504030c0b0603011503060c02030c030c071404050f0402040906 98
    0x40e145c20940c42620300c150801106040081244000d40c81d0071085400100707512030900c1d19605040944640307a10005040075502c1401d01c001c5011910100300b581210b9401003810040403000001e05c5265001903d02c0a000b8204800b0142151521408540c11a503004006614051402c8410380e000c0d040184140e0600865031030004041d83c41d03000074220810004080c080c02c0d0304518001e408284080c05201081c3e1529443c180080d803c0814503042d01d034100e4124050340d84114100f4680448039025002d603000124000888a0054020f00d0680702d030703900d2300159640c688080300e541c1d0246100d2082503600442040200c0d020101045240c0200138001185480c40904000c0070342e002907400300d000541c401041014008104201a00003a0485c0240011014070f84440001c0c1030b07074003000c0d160030307640d01d8a107980c10f00800880d8100c0c0429015651507407140201036072105030500c11081d084085042c0750b403d03840c042c07103802d12802e001000d101c00d03074865409200c0189079402040360b03080e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 23159088 1250 23157838 23157847
    0x30a0e031603020102070201090b04050d2307120c060c0302030313020103020d0c05090906040509030403030e0a0305160807090510140102070305010203180c0d02010e061809010603020711032d0102 86
    0x401c00c0d540c5510141c000e0f0005642c440b014800144490f110382c0c000c1c09500d00500090010390703108030780610f00a0b0400e140844d071103014035070307181220707040c5000c2c1c40e09202d0558001200d030300d42040a002e0038000c0c0e500d5880c55654200076140c182c04005c00400580040000401c00c01200307020181580c01031500500380403000240030115100b5490001c08101c020403469241d1505841c0301e98042d1007a90240414180f8003400d036900c2c061400024180b115448481000e6100c0c81801d00046421100f1101c0c10303184101c03039004000c6035004444460003070800c003040050150283c0d030b0044004c0a15030100628099003442c511440040c154114026041c002022400c2400a1400f491001d0301d003062042001401d030740b905400c082c013940074071429010303103000d40c1c0c0000c0c0d41006100180c403100da913004161012840101c0d0701c00903030b5112030b8160011550540c5507002d42001841034800200703011049081655641025081c0648400e0600300c0340310440c2500741d4252048200300000d0b060 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 23160338 1250 23159088 23159107
    0x909050609271b03010e010903020d030906020c030f0702010f0e0109120203030c0106060f02070501020a0b0402040b060f040902070201090e2802090a03050109060507090f0306050408070506070e041a0303030a0e03 93
    0x501c07400c0040c3c601d5036080041c002003245420f10a02e0000000a0300811031100c150344e010b0f4507414070824030003e040d40c82c018035090102c182c04880c040310300c80c026682d550000c01c49070080c0d900b181000380e0000c2d40c07070064100c8690150000c00451b9074142c54000006141941d0f29034000c40c41d03101240c0600042c020007403070003001d006402c054442a01d070b5040000075a04024034000035a8496411540140078460200b04001d1003141c1140e0103840c042103a00304480451410b104404106101d10703800180040c00300f0781c2c2e030b0140c0b0400b0b10036039500004940d42c01800b01c1040040c1e4222408807580c1d484442e441c8201d001040c5445203d00c40541000d00040005001c2c85955101b500d15944490025003046214490301d90b0102050030403d12103030508540c00a0715005000c0180280c6d5202c0218080c003094105591031158010b045611524040c90b009100c103035152000c500450812880032a040c20003500710006030006001141540d40b044140e1019003608006d41d42d1038003041101c0c109 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 23161588 1250 23160338 23160343
    0xf02040c0801060216180203070504030503030103050c0103061202060904151e0513060e04060b060f041205010e07061704020f060c0714031b04020a030f0f0b01090905060927 76
    0x291a8500e403910107003585080c1c0c000e0b04041109000550010030003506100890088002d6000d43ea10000d00603181d564868056915100390780010341240305c0480000100807001a110940d40e0007030f6070902c0501d654225018240c0310b0620001d61161044c4400159801c0580c000c11140800820205030565290750621805107070f05000e00060318110780520660400c2010b82c00710060310101003045134600030382d4003600403001c3c1c00200103e40b41c010490303607941d641c2e0565140c5c100c2c040e452692039940380981e050120004d03001b01c80c90750034400440c0035030601161410441c1c1003505d80703022403d07015080802800000f8400caa1080f00c124186e46142c0b151070160910012600c000c0482c00d042c0b050910440c0009501c0d18442c0d4041d404444410040c46001c04c070304501510056111300c0e0415041d0003801001c0000803600d0700e0310b1000083e0005503040051886005c0e01d42001c000c1e01e5000b101d007521707011aa031542100000c004207040c182911a0443d501d003000250410700d002c1c1c000200e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 23162838 1250 23161588 23161601
    0x2130606020109030206090703030c0201050705100f090203010b01170106110f01020d0921020304030605070201021b0729070b0c0706020304150c0512070806040605030a05010e010c08090c040203040f0204 89
    0x80140e542c3c00d40b440815404020040c2c0221803a401458210302e15500141341809820000b41042004038011080050400c00f4011481c50745205210107400108d80d407006045e000c42c20303803007582042140380041d4000d649641000500b0407030004281c0c03c12034161042050422500042d21415402a503015020b00c0a41440800c0ca40046400a22410304440014400307415402b07221400c03004099a41c4c00108071000c60350b110300301203425555410144c1c0240100380e00ca50050b0041100340641c0e010209415042e901b41c0d4440b28041322032111903c0340154280d00c41804c8940c1040040041031541402c964480c00281800e868402f00b0798540d401c2c0c0e00140c60454828070080d030b0000c01c0311424001d01c0c3c10f05040d07107401428800f98000c00f0200c1e2001811180c01c1c0715544010030f03000d0301d035600240007400c809000c0311024106403410b50300074103030090f01c4032455280a040c0c03a074681c031480c01e05000d00b1124008140e5508038008200081d48050800c0f0340b4080b030503000000688446c003405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 23164088 1250 23162838 23162849
    0x601020309060f0a11070e01150c02090f07091505090d0501061503060509010501080402010c020f03010b03030c16050604030c0e0a140f1008030f0d1116050609240402060304021306 79
    0xd803500b40345a80901584805c1c02e0402e503540103804244265040f5a8080781164454102880c21841e06002640d4034032200c0c0c030107500301c030242040050440c14070300c1071801203130b40e80d0b5480300701039850410602142802c1442c80000e5010050200c003072601100c264141c1d0b0040c0000100c081e51526030102e802c0030700c61400082600c07800104400c0c038003900c440340141000e0038854054501540002d1507a060311400a200c1c200b10140c00780603071801d5200b0110700001070102ca55804580854580d22420007110800c4a0b14465000ca210b06050003510200c9a02011700c411003400d10440f50400c280082040c140150b860750500c01c0500c0100c201070040d0b41c0c554130540b850400c001d150003041780a4220f202c89034402c001d24003030030403004102c0d0501e1004180005464103030017986509481103590550034090707410700010a0200200303c040c003600803001115004005000c044e1039612034507a01901658088000078054101003000319405417006281c00810100c00c104070080300c240741c005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 23165338 1250 23164088 23164117
    0x8040203100203090607030c0305040201080406020304060608030f091207030c0612020c06160305161b05070806040501020901080906040308070f180b0408070b030630030703080708010902031509060102030906 91
    0x1b070000031500361041c48400c0c012807030140543d1801e03030006466500007510050205500000003410301c011540203d0140c0014001c2e41c0d500c11000301800719030742040003094400d40b00d003140246d500c10001221f2048a80c444030280c6003915009060300d111142111f0081196020807462402c2030040c00a80d20540c81c24044d40c130a10703850301d03004040f00c00003081a6091980840a2040d49810a000c1e81d85006001c141c07070172a50262916a00304a45a880311400d440b42005000030450103401514541d002a42d0b0440c0554a40009540c0e80c5020799002c5e02280d03440000c104150703c1481e80c000811814105603940e40e01040034640c0081c6581c0c4204050b80c0085428444048107000b98001000324244290440c14441d00103a801d5a80070300d6032a112403003086c0401c1c62219407072a8464943c040c010b480e01c44c142420060032202049500c42d00140040c2c00104032011648240c900402c403098840c0318400031038047c4018490082c204138190f1006101146d1540e031010024a0f44040ba10030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 23166588 1250 23165338 23165341
    0x80403120206070906020613080a05070204050a0e0c03030a0f030209040902060304050d02060601050403021305100308040306020403030206010614070b0402120111040812040803030708040606030212030307080f130201080402031002030906 104
    0x804c00341964200d281150000c40c00c2c800040c40d220811500c540d040f4180716038903865170310151014401c84100a40060900041040d504143e90008030f40c0350485059074240c044190800d43c6034460980c411003c100d810b0403081d40a48a80e0240c0500000680b00140d45e8109800203601e83c0c004840403140750740090402454a81d0501c192a080203003820100d082c14256030001e03d0f00751644035118000340e9184000341449050f100103030300464118480da5a644e4036810b04001030b500c140001d401521500b000040c03801e1040c40c050703a40c2c19014071614100012552118044a00a0401d0381d0046c02e114541c501c0071000c0c404c01060451820751241d80300d2400036240d0408009030f03e04001c00300103002c100324550000c0308899004280e443c00310059a51864204000e00b2540c04c0a504408000003118021034000003c600807110b54540c414035903a4400b200041c00011151940c00c520121900320040d401440010b4100f071009095840c030620200610701260401c07074081c07009038803080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 23167838 1250 23166588 23166601
    0xf0902030d0206100504050c09041b080f06060301210212010b01030b060a020307170c030d0f0f050103020a090903020f0609012c06070804150501080105071b02090601050304080403120206 82
    0x20403520881c00d02d001400d490300c0c0c103404e1011821007600c41c0700e0185880d20002449008010110741c29420b00400400c00400142010002c101090075a58049003a00011a00543d070760140a44038143c0280340a10390303070038100c030350700d08140046c0c040301003d49503c01d080040c0e96035643d0301c0312071160400000c1d0502c0003400040950791015922070041e00d04104402c0480e602204644c06103400c00074202c1282d4150308400c3c0284074000c4181e09070f00000c1803c1c01e0030002038020250002d141001030240d88460213041d8112030080c03100035070000d50f490702001502d060360072101515000f80140c0d83c0903c9040c11040c1001720071540c03101244d65510000901320780b281c0c080c801e00c00c04400184040d20003001401d5854501400d00c9080c005580005010070070b480340300c4a4000c888082c1403013035595885805001e084252604800f0420112030f144c00541d0140c9120200e540040c0021501c0c4c41c1c001c0103441560001c1d2094403000820000403010581c2401c0201d40040039a00814103842c101 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 23169088 1250 23167838 23167843
    0x903010908210915060d1502030406050106030203091b0d0f080409060e04030f0320070c15030c1b020402040506040b0405100801080a12030e01151502010204050901061805040f090203 80
    0x42c0944607281d00010203101c64207400042e0721103484da04c54515000c1d43c90b080d0010b02840c081c1c8000414040c2d022aa6504120454001c0c5014607c5603c1c14040d40c1d0f01d4041c02d805074001114800d102c0c2d4000402c00e145a802082c100840300d10260451350300b41140d44500503060b005040544400c40005010004122248150001802d1850404002d41000c4e80c009084800344401c541c00c042d140d100382c104100c0c03980070b041c55645403820b81a50b150010700d400cec00416194400c03100190a100900501c050090280445144096440b010640c2c6034102441268460342c5080c0c0c0c00c80d80c2440003003000e03102d500c018005081c42c414203a40726851b0900308100010038010708010031811000410603840000350712109545d00c41d2071a00083c00980045004000e0078049031000d40c203100b10716225003071110f40314050341c5c5001134070107841b0002035040c0d0070703031282e40314003604801c40d2001000000c0c81611120b0702202085900c80360140ea032400201954400400d0000f516520580f0100710701c0c08 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 23170338 1250 23169088 23169127
    0xd03021b0a03030c080d1803020d031506020304031709030a0302030408010c0905090403080604111303150c080f090106030506040305041805010311120a050a0b01050910050607060c02030903010908 86
    0x8580c0d59440700d05640e40200660089803004201c900082070301c0301002546e80007094100150004030760030000f98200295142510f1000101017031a00c00b0441e08800c00111a05c16035105800940c035062030b40c0d0329406030b11581200002000380a00c10034503203990a0250900c0d0f0307030180d030055490f182804c0701076086803680c035000d80500c101441c0070003058807104885540260141429040c541e106008640500340018074400e41540016070222141c041d00350350b01c11f4034000c000751003009200c010200d044030300181005021601150002e111620006501e81e0711251800000c2038031617407996110724284043c0c5003180030542c084cc042c0302d000700e4900a840014802c0d9014080e551568031350300032102c2c0b8916081d002d030b040e00204201d00541000681c1820f41d001044a60a00d135a0074210009002805554030426190340440e421060340340b05542521001010240b904519980340d1000301307003150208056000a02003400d4a9a00b0700c54181c1c03090151508658802d2600d00c4600007011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 23171588 1250 23170338 23170393
    0x20d0206040c060c0501020d050907080c0301090b01141f020304090c020d08240307090605010f1d0603060114030f041202010e1b0406050a0603020c060112030206040b150d0302 77
    0x2000c0d0400000c29140404041160361900300707610103158504045002e031240004503681c02c1e05110a12031000d0000070b40004179500c01e816141040041c1c004c05099501800380642034030344400040c01401887d22084003810340040c071030015500450244030304c030b5810703044480250b000031804022400203401071000100041c4040d0031800340401001e4450107000d0010412001083d00310504105180c85100303075407030000c04640303800380d42d170b02e1403000340560303000d007900203108420391401c200d0240398550010980d400c06212881040310034458141c000811250400c2403074005c190b040071502c6d00440c05403034401d030f14079201d141900307040c50707828004058602160b14092118402020104001d400d8980101c200c036141440c480001d0040d1000d50403055000203a100c0000b030042c0c15500420304c200d00074065442d940e0740c50460010b036250700e11020740903810200014002075100039040350300200f21005c40312940410300105070300c0311918000b100941d01018042d811150a20714080681d01c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 23172838 1250 23171588 23171593
    0xd060f06050105040e181002040905010906090905060c0702010e09011d01061805040203060f090712060807030c06030c020a0c0b040504051005060910020a0f06050402040510060f271203020d02 84
    0x140341c01d008080d400710040007002d205201556003d0706c0001072100340e1010890380c406540311515055030000a020a100f00c60305c652030580d000944042c68001c501030b9540240180850750f8550700d101541c0c1d07200c448101e0401140300c61800150b5228200e10f030207803040ca9040f0840311898042e1140b61001030700320f442440000006100118184401e0f0801d98506440260b165104c44010411149400700c0c107a0703110700391008010784264004c510a2100d0300024040c070515a54052503511803c941c040500000803804081c802c1d240250000303080000e0f5881281e4080c206038484050b4034840350003051503510000760070441445e1500030660400c42140310690541d19243c001107503403051805240c0120300c50707403004000b00d0081c091001c00a80009070020300c09110b03d40f000040c44200c2d0304071300c030381c1c44c00d00810401c0420600f40010380d1200d4980e40d001c900092070070303100c559484005200c4088114402c0b0100c0c0582182c00c40100303d083d1082c5518a41442c000c3d08000d601c0407240c0455 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 23174088 1250 23172838 23172847
    0x2090a030c0905250e060705010507020f16030c030618050a03030e0c030105100e060a030501151d0f0606030903041205030315100503190e03130806060109050d080a020c0d060f06050105 81
    0xb03480c078402408950350a2200c2c02d00c0e10000401e041c7e0180a03000390a952a24007000f0000e038010805400344503407441035581c440841c0085115070840343c0000340031416500b01c00d00010b1025805000817401603c0c0200307446140c4c0e5901071601d4180c0004400180d252904409644000c000380301c01d422046001740003502c0d01c038140c2c4401d40303824869204801e1490300410242d4447c0d06050021716000720091001000c52410500c20f06035500c04e651207000d02091038840c0d107610714034041c0590001220540c40c0c3d1213040412201d46c00c003500030b0902340820040000e0420080c144940c0052041e0065500da01c1c100031050400c10305000124081c41425015408683d4481d08480e8051103083c942c1050100003034041d0000c0849074848141c501c03002808181052001000008454103501250301650710b142c01165801031500c02c46810007503520f5003800050414000c0d102000e10b500c1103030094807034000080d0442d1311070340054690707a5031412809040c90090080038040c01e07003801c000707103070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 23175338 1250 23174088 23174131
    0xf030305151c020103150602010510050a0e16050903030a080604050105030604050304030615030c0b09090108120a0302070f0b010e041203050f07050a0e210708060705090603090102090a030c0905 85
    0x40060b8000409040d280c000b00d02800c6a009500c0500094100c14040600545459001c4d009090179224146125004107001070180b5190f040030050315114540d00b201782d21041a02d428100d01d24681d4000d06c1070610807004180c0382000603203803600d000e035241d40e50780c00c001d0305200c11140e0613000580290018400c00010070400000c0780c040b01c0d8004000140e01e1540000d440048140350001803144088010000d00c210840c1c01070046403800701c0d00c0c0e114070f90703036901d54039a11403498510700c0c00001d00b80b2103601014000d50180030410b00030504840d0b001c0681d5509041942c0c00d8201440b01903c0340c0a001c203001c0c1d85030900203012520b040410603400d00560009207603074003d0110082080c005070a0380200e200781e0b11a030a00310058021140c0c0c000d158030381c11480c80c0480317050315144514840020002c0001400c540101e0440c3c03141490940a501480312990004111100b150b408025280040d10780b1f0044070b00030340c0218142ea020a040101e140b080c0c0d04082c00d401c080c1c600c0418009038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 23176588 1250 23175338 23175349
    0x6050904080711040c1d040c1e050c100e1203010b090f040b0405010801020319060317071a04030507120206040308180f060c0a0e010503040f0602090a03050a0f03030515 74
    0x304640c00000d0701d40c40d210305143c5500194036040c145500141482e51294555402c105001006840807000d041d0252000c000d10007158102188500010302900c4880005250940c001c0035031382c03851400e03e10340019003d0b99840c081c00c031441c044485545180700310322210140160659103840111191440d45024400c0207140140002c16100d0f80c3d10303e40841041e61550301140300da0201500520656070350304c0806000350811510340c61522032a025070b150f039510602c214010349500003110760030141c01445090880e0810041125541d0070740340e50381400114030240511a82c441e40c6d039140d640c1524039012401d06c9400c6135110955100205010010340c00c0341e002c0344d0005062190145070440b0b4601c0602e010784e11074214a050241704140004400d000c002418032080c0794458440341c0e40c500c0f004580324401150064003207140b00620318002040d980050583d598020704800300c503500d03516010b003014020642105c1044000304440101178060080325402100342e01a0071808819801240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 23177838 1250 23176588 23176591
    0xc150901030213080d032a0903080306180c03010f1d060d021c0f020a05030d0503040609050a0210030c080a0204083f07032d11120c010c0909060509 65
    0x9051507004250040f142e00510100d400602c0d0080896105c00f1000201030b000301481c2000340610346091030040c0d2510400d03500039080290715555a8102d81c44d6444210807900042c00c070b99402200d1420020310203445c50741460003201c0c21490280da95140460160210489034000508400340021317400c00c9825010b4019403002d400e4400b40203445c1e86200007200381c024915203000150150150b501886004660058668400c1d20810340700341d240c2d02019641c0200380309220010b4010000500000d80541201d03044a1055007100d00c5841994001a0078650643d540d10001c0e83d90038400e00b0b03081d84503c072143c00c4800e81c1421032429040030000d03629100c80f080c0144a4404089880015040307140918040ca0141003014258500c042d05051403a80206e4099000a50b4031200e094030ac00f001c2e03004400224114003d50303148281c6c040c25980e0740b0080c20741c000c00d030094203206031620301c51500914044859400010b0701141d502400341441e00150417128155160120500981d1901e0440701e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 23179088 1250 23177838 23177857
    0x108070e15090f0a15090c0e090105060f0c0a06060905040b070f0203030a0c1e03020a020607050f03010509090a0204090302010f0e060c0403030311130612051305120a1403010e01080c15 81
    0x141169a03000400c00140108000408040b00d50010021b02010147d01506803100729030799507421642038004124004c8070a0240b0341d4400030070442504525050b0000323000705d004440584003854040c0d01c0e14400c6501340da101c8482151900108000c00440b01400c1d903020040d401c00c104c41d8098000001d41e0303400000c01c5c245001c0d41d601c1c5e5840e02103002c0c074200440b84014500e00e0a89414456000700a500608000c20244c800c4001040215000d00c0035a1604a1004000d501b540c0c03a100401030300c0d16002e001d8440d10b009818841000d40c070745000b1039107402c1c002d0b000840c40541030240c12084454103946042c50b500714a040c44042030a40045904076901460003080314044466600c41a200e602808003076410441c0b80064076035005903c415072601012000c000c80c0d9502200b11001055400c401041900100903000381a13140d030300a440703d200c035881c1003c010004128044165402a00841800e04e0700c000108040c00040010036110501076540c80b080311040078060389035000d051841d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 23180338 1250 23179088 23179111
    0x20d030506011206030807030206090706020a03030209060408010914060721020a0306080a29010506070308040303060b070614010504020a0801140607080f0a020d09080d030504080c0102030108070e1509 88
    0x881d400d680f1030b40c00010054800b04040001c20750b42d10701a1590780c00102c0440141c01540001412141c0203d041c40407618150060410008195004c03002980041e441c1e40e1b114209000c0860800b0092103000346242c0f06da80e08a103008131180b40c041c5410710040c4440200941b0710842d100c903005401040d02d410140d0440542c03103459141d000c0d0090b200da5045a550780c8100c10350071040c042607802002a911000030780c80801c0f000d410102c15205005d0041e030f0780101c8108891340c00039115824141e8414083d150000d0015143c3c000e80290368040c02040d43c2003515244604140c40c1d200b15104c0c01040f04840440c1b400c91812000b420000c0140b080302d032a100c8404a00c24152522400c07640785640c0240e400d999640c1011218080350010b4400b80c0043c03140701103c101a0b0701070b10354001903030301840003000c00c3c2e1041c44089000c4c200042007200c282c0c40610025068800034005503000c0d1250601810599040c042a0242d4080040181c0c2c04607110341080c4e08103460300d510b1944c00140300d651 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 23181588 1250 23180338 23180341
    0x16020f0f0405040807060f050105100c03120501060e0a080601030c0e040302010e01140a180201081504060f030b040210090e0c030403020313031112031903090c1d0402040b03030a020d0305 82
    0x51854000529003a8001c2c0c01d1004000411903518010300c0703458884e850800c1106003a00d0a032040342d0003401240c0c0c001c9160507a05a140b03016000518031980710380f414404118034003485100303942d0700782d20581c04070741d0b0211100c03803519102004401402c0001c1c028100c0758950f8072030342c05421803071045000c00e82c25807004c1818103200390007100400c4951002440400259001040701300e20071101005020320f41001041c140807044589900e1540580d110707807032130701c0d01000001c50981403c8a01c2d03219030740309070000341b02c00004030b07050086000c0c0f155200c03140307402d00500c11010089800703082001560102800401c017883d81e0325410041c0804030640300e42c0c031864180e1540c4105c02c62254072001c0701e40e0010800c030000e130b00f005c48041c05640709003a0b50f40c010207150b0799026500c00c03d8044641d071040740e2005840380d444100f4880c00740c0d0394041c040395141c03030010700040303050743c00b60340c55070b80c0d03010402903007028040e40c50500c10680081d468030528401c000e44134050484240c042540340c20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 23182838 1250 23181588 23181619
    0x609070806160c0512180a0905070c020f0d0f0506040b070c051903051b010509010e0102090612090307121112090609010e0a0504060909060b01022b050417011a061602 73
    0x5c0b0304030741a10210100c0382d075007028401e001c10320041504150300c18078001e000840c00c0d09050140d54041c840d56150f001c0142020b070300b000280d44044a030b198103e040c041011021a045d200b0420302c1c039000e0b80c09403c1c0c0782041c1c10201c4940d0745c000c0c069030901c000c0c07900520010704d0008100303c41d0402c000e2058124541881c048419100d02c82e055050f44d90085914090003030194803d038042d20290000300001d107035081e421420303409000c101c6580580c00380400f00c0c0210005181c0c0c3e51110300442035078680405542ca4807560070010301c9200029a2001810100c80310404c04440070516460010303082003146c000098940c81814481c82c100031204410b54030544034280d04002410001304148090707500e81c2591402486c1015050b100ca40c10300c01d00c02030740c0d400450000c00c00c00c2415044018003402c04000070075a0340182c03141040103410000002c00402030300c154009030690700c0010846131100d100b11000541d00e410f4042c801e410401010f642c05840720502010b850f416504000d103440b800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 23184088 1250 23182838 23182843
    0x705061b100501030501151a090609040e0f0d080f0118020c010603020a060507050615030c1509060301091e050108030405120a060501030803040201090905010609051c0210020609070806160c05 84
    0x94072a220a424440084200501904983c403d00001110304204680d03440e006607294003461148500c0003c01c00940b01c2a007001c2000b00f0007070801600200300c1d025010449032600d0301c1c40d034903e0019000b0350800302402c0e80c004040d40d00301030743c08182003055040100350300100344c940c0c0e2000c084503030005988032050381c20f410020045130001d10000c2c601e541c03408080e0240d070000358100d560307003d5000064440c5085448107820124090000c1c0f051141d030100b409084015005e01040d00d1070184001300250b40e50000440c080c240104021031034a100c40072041d01074502c641d40b0300049007020010302480000005803030860b68115000d4030120702c80440c4d1824080c0c20600981410b04000001c81408850001103024600c02c2ea507840c840381d603443d00b6400300c0340c0a0142500080061500700101d00e444141202030580c42c203180300c40da41e09540040c29005248941001503080b107010000503203003c1c00110700a249400180144c2d103045c006186e28418410307200c8040c003071100780100920204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 23185338 1250 23184088 23184103
    0x30108061303020a0b1911070f020f0a030c030c1404020c150c040905010b09010906020708060a05041103010f241a0f0c030d051603020703080a1d0109030816020705061b 74
    0x345510302400d024219840e03000305ca0a01d507001c0c1f41008035243c010300141c4100c07a8042c1e00060741908100301c3d5030800ca20f1180110542c0e5114030145400301c0401c3d8601d06000046200380c0107054118035068442d068940d10f002d50a101e90f01c14000f6421916001c140c910301c6040f02013064009542c0e0f5070010340305000b03a40041807070301d24100001c200c08403010010404250242c8034070700201d9035254220380c3c2d4000d500650b40c0d99080740c00404c220340e12580240f44c000d4480c40201040070406800f05e801c40c0d040b070b00d861903040d840c0c100c4000364180d100102d92564244030401916070b07042151801d020045c3d9a002c0c00e24100029480681182a45c20f8606000d00401a01d0f5943c02c1c68820001401e000c0d02c182d148042c0020003403000368082d1084809066040c3c840107070300d0b95200ca415005181d00a00c900c15400b409510002c2940207210300000284039071a28411030410902c41000100c070000c540003550f1040d00c0c18041a540c28054506070403840c148401c5800080401c0d5081624 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 23186588 1250 23185338 23185343
    0x40204020d0c0201050108071208040e090a06090503090405070e100e0f1207060e0402190e13020c0102220302010207030f050109050d09081605091602010b03060c0c12030108061303020a 81
    0x40c1110003080150306401c00c50403145240210f03148d282c3c80d084107018149095130020141c040400c01000140e041641c49644010342d0419555140c2843d00c0f08820340b04801d50031101d541001589001074a003c6c4075964108045162040d2034500e20404901503402d1100001e00780f0141600d0218a541c64046400c1d2820001e040a0380200e00c80d040c20303903249218003d16003c41e1070a289421f280c103042c42620224040305400281c2d804040c0010380d10214850004c036000703a000c075480000c60b6100d000812283c0d00c0b00000581e83d0f04106010b0200c003c1c01032500010014031030b03007040943e030300203418025a41c000c501081c1007c01403801a0041091441c020528018070f00900b03106900a42c01c4c44c11508041c0903100c420340d4180310602103c5850140544c44a40e03503021a65051203558411500c040700d0000056402d04880068a000000c0750001020100085c01200e40001481002c0450386102c00460940d4104810380362174000040c030702e2840d080c80c0e00c001c0742818402c20441c44090b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 23187838 1250 23186588 23186591
    0x32e2304110306090a0207030909051f030b070906050c03090f060c01050703020403020907020609300c0304050406050604080706030510170c010f021615020106080d02030c1006060512040204020d 85
    0x28031079014406401c2110220300c100458000a10401c0303031402202c0080fa819640c0441d2107042c00c1c8402c0080034081c1c040340d890010940301c110180010f02c0d256000c0c501400020b4072910b02450f00400c03108140d0000ca003004014014a2034510b07000090f2050100121a40c90080140b800411124098080090965804c003014491069015401001628020b403400780c0c06a440e0320080e40d6400d810740710340700d05504c03c03500c6000010044407400d2001ea403820703900200c207001101d401c202e500000440500340d00000750130000c034905485104000c0c00161807032424181343c00c1040b52921454485e4009264803140080c526861141840e0060511555082407800701c0f60359240c0e86401500ea014003140c80c00020b007070450b000040c040d04520f01c07000c0000082e401c0404084603541c0070f9074400155134070303228082003140d8103100c2ca21b1076140d164001c50300d0380e440603265450580c945100c14010752618a00748150780d0700c103040ba400000c6200d401c490a485a20200e0000e10030084a020b099 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 23189088 1250 23187838 23187851
    0x60f18120d050705030603061308090a060e0f01030903080f04020a0e070c0209060906030a03050d272901091805010f0204050405010801020a0e010818070b032e2304 72
    0x8958a00141c800c01010000401c0182c0e1008025a00d0788001c0d030706035600d80c4c80040080c002c0742c00d282c03205030b015100766a01c508005110340800d03a00c0351141c1204012030406000c03c210f9040003100a40221424602403284492944000c3c00360400500300d03c90700c1c03600e00001000d42d08d541034900020301529800500710b140038140100720a1900394228442d20300500401c255190202d1524001c61000b4003400c885005681c040e50745030310090001000584803042020780303c40009944c0380400c0000b441c80b500c2042c526011100da1403680c2042c1d150031900241101c4106c02142d03450644220b60301c00156010b03441104040010f404a00400c15070810362698a035046a4015000300c440658003400700c3d980341c0309014280d0042016520001d01c81d2202d0b0981da41c0b160500350340050580755000f2000804080560401c0d0b00781d00000c030100400414040e1130804124003540c0700001000c00400010b10100690000341e00303204545002070100c0240d101c58001005081c60144c0041c0200300e203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 23190338 1250 23189088 23189113
    0x3090f03060506041a03031909090606090305150106020d2f030c0d080103051002130b030a0b010f020f060406202206080f04020d06021b070e090a05060f18 68
    0x180c41e040343d00350700480c1411801c08405002d22110028104000c0c081c0d030421080c190514010030540c0341c0c00c01009600017001030744821078800d240284c0380f00d80d92810081e00b13604009180c10b4820020000c4c0c144000c004200072540410b100311440c20610b45014141d852540710b540c40c548d01e400440e40c81845000030408140c1c0080100711240d50081582c2c4140a10442511000c0007407001401581000700c081f01e64801e40d5000300a6800d0300309601106a4a9046d10300c3c59800480b10904c0007683c1c0d014001c0c0560b0422180d40f420a020b10041142451180d00c1070b17150180941300500254489034688601c0b03042501e050810f1021000940e20b4905511b200041c007948441d525642c4045020040748403072184800354802c1511055450761602c46a003404400303190b102090f64400d03424004170782100081803062450074100c5008010282c1043c0220200b0b10001e002041554011811100001d401180315035010311440c01448040d038501c01951162151840000d00e18007903001403041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 23191588 1250 23190338 23190341
    0x10e1008060307060309050316050a12020109110906030a1106091018090b03070b0d060e01030305030f0106081b030414070605070c0f0303050711030109020603010f18020a05070f03090f0306 83
    0x4921070840440d15010790301e20302501242c40340c0e10003030070700e80003088030b031540742c1c034031220744184921600446803805a5500e920064641980380100140d440c1c04000c070074000404041d8892480c11a0b8000480c10200002542c984c00f28100070840b501c841c000445a40e111310581c2e180140c05030100d0112408d8080060055081c079220036001c40c0320200102e188000e900c01c50f058404080c009113007960400c00c07010003a4111130514007290707071214408900d0503490240c071070081d8420303101c450312420011051003804105030000020482540f08011440c490b20700010040c2c03400c0e4a080c0c0d620380f00c5081c0081d4103100340c842a0407920401c40000b0b000f80d404001400e110703000c0c801300e09150b80c8032144080740540a220107000604180031140104401494001c2c0060b0020f000180300d084235400f003840e64100364440c50361110440010440c100319030071190011503000204600d032030018400503119026480020701001d0591820f941014040e54185000d4811040c0d0040829900d260540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 23192838 1250 23191588 23191591
    0xa0b0f13051e0c04032d14030c0d090513050906010603020903010e0607020a02100318020618030706051309060b1801050d02190e03031908070203070f06020307090e010b0702010806010e1008 83
    0x750030075aa106491000c22100304440c9030003e4070300001591300306d00d07265844031001c90701800e4028003042001c20302020040000c505044402c1d1580c8283e01d140c80104980e003407940c3e003070600750350500d400c1008100b000300d0201d06448040c01c0040e2205071143c0820700511002074052045c3c0314180070700c41140d40024007119000d100315207c07240a11044000c0b030a0390001c401000344ac00d1000354010042c60400d0181840104070005604202c06200c0002c1c0703040c616030700c100b0114100240070310002074011011740207803249900600085192030700d090824407503051098403807240d1111040540c2c1c8103400311a03a2500e003030425925001c00b00c0340d040440910760140e0740401c1216010f10750300d0a01200341c0d2a481d0291640c20700e0f0b4a1000381c15610070100400311740440c0810404280007480114412142c680199001030301c0345050000601011416000303803000f03107051001040f81c4c600c1a400c440e03100b0350a1902c108140ca41d0310068810091508407543d0202c0404046a01c2940c00288203 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 23194088 1250 23192838 23192843
    0x90d0506011707031a060103091a040311070b03060411040f0308030a1a01080a0509010b030a14060f0c0a0c0c0b07050a02100e03030403021e0301060e0a0b0f13051e0c0403 75
    0x314029200210030b0b03996003a00d1100528114101ea00011120031203041d041c0d003e20107040c04516990b0751790314042c51003040c0918240c82c1c000c03407042c041410f90140e5100004070100004010460030b06000c03081600004010a1113203032100e51030f0441d040d0600035600205201004c41d0a081c0e02c80c40c107021aa00203c48540348035140030020a2100b00110100c140b0740810b864003009901c4083e118806000024400707041592110076084041c1c40c20810352191601038900200f2141004510500300b0350042c21200d0070190350000c1c0040031540c1c604585204809080c0b41c204041e288c0392144007114540e200b42c0304210082240018804080b500c407200030f10031998210442d50905040e5500344200300031940683c4140014801420240e0031040c401454603000030b25416094006030070745040d5000b0b21a0302901405005546085000b55040d8260403100304030040d050002160b41e144000b041003605c40d4441d40801c8884003001410240c0d0f8825980300021031610502c040aa980544002c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 23195338 1250 23194088 23194109
    0xb06190f1a0703050301060c050c10020d030605090f070c03091e03030806010c0b010b0c0109060c020304031b0501080c0d150e100603060b0901140d020c0114010909170a020102090d050601 82
    0x405007104000200c0344166032640f90181181d0070200c0c2115000301c1d282c403c4629205000c5058115503c0c600d01803542c8900e036000b4284805040b02c01000e44103a944180c1c0076013420024000b0810301c3d0080f0780d40c8901c007440c00e4201a501420120740c0344150f54010b80c001c0d03041080c4404035441c60103e01096034080e80b90078446499a03001164207501050f0041d01c8200100700602c80943c6a0b0002d1440101c1d00001040d074001d507440c2c0e00d040f41c90900c4900051f0b032001408000700001300c0d00d08410712084811140104d481d00e000a0401c0f80002d1185207224800540380121801c1030340140d03c2060031104210301c02e900c5100c0c003d1000b07010307221102c1e045501d042c0090724078828080c40303041c0c1e0b1456292905208c403002c01942e07120807000c1011000c005c10b01c21400152082d1019144110058001207012003903540f41c100519010303001080075900f040c24400100301d090711504502e81401502a58441c1c01840480c024000d854120703501c920400c0311704080c000c0004900e4142c4141c2007a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 23196588 1250 23195338 23195369
    0xe0f010806060918030d050f040506061806041d030703020a0510021c090204090b0406091104020f090114090406030305090a090615080c1209011406010e0d0b06190f 72
    0xc10607614403085600c5507012050030005403440d9180054000c003145120110707420100700b000c201c03041d9a0308581d00180304404174100420b000d000c101d0550024415250081c1c24100f00f0400d0040a81c0100410701940c2c4542000b290712028640010b540180c51050780e86940262a000b511002d5034001600d5a11070a03118604038240b074070072102140c1a105240659541b0803907040090281ca0300142d034002d54420414002c50702810074148114455400060030111500d041030f01c3d00a5050f1550080b8418403c001ea103901400882c0d5100009091501c040c00c011401014688035980003141c01030f0904100004140d0030002900700d2810403213460540d140c0718070307107402102c110f4072411240da01e1050402c41c001d80a02c0e210754001071101035181ca08a0043c1d86548031040544c2d54940582d501e604c0d114203908291400f5030464024030746102e001c0804400110f0300c003010800980420708240c00324029584800002801a1031070081c0044a03696400040582c1014030842d61107210140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 23197838 1250 23196588 23196599
    0xf1608031006090503030915041a0c0f0303010501091202030c100c0303050c09060304120903060c120b01030b030606040c02010219020d110102040e0c0901020a05070e0601030b0f130207080d060e0f01 87
    0x251039100313070380c405001507040000b81010001c07a8070800340010f040350001c01c0041010180209800341c080c1003102c1071a946e0502e0400680f40c5a0f0a40400313095030814001404aa03a0150b01d0b413080319004121090140006c0c00089d0800580102442c0d001c40d03001c21490040b9045580340781020b01a8404001c1c5903144032040600d8419114510b5000e80c08100003000644d6076204420451508d00d000c42d5405d4032607072110304882481707000402007400000b21540701180c5018441003103100386024403540005801080e515580602146d2090b500c44460b003200c04e100750306441c003211210140160106a521019403036007030402d603e10001da030f00f14030b02020603c14022641120b14008103500256a55005000107400c070b148150b04600030303418400017060b41006124081d0541542c11040750402c04009001c98400c99002d902400320b00c58617452999403003424004448a91358050f0303445001c1d1504200c1e911a165181110510b0503101061142c1042c10581c414013680c409140c1598985 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 23199088 1250 23197838 23197847
    0x1c03150503030301140108040320061005030109110405090a0204020f03010e130302030313021807020d0305060d051b180a050105031603050c0112021c091505010503070b0f1608031006 80
    0x24051061200040c201c5c1c0e0b900b55225032200307030380503007c2d2410f010880703110240c042c001c20688142258a900100c10b204005120030014002444110020070080d01d95a0700e4010f80c000604406120b242d807000001d006000c107009801c00664000c004540d590140c80c08488260420b008460030500d20302d0000c0e4072135056180a80e14141c26800860550b9180400c0c2510302803064012600408000c0d40140c080e2174800c1e1543c02881142c029103032079014088000c003283c10081036070b440790b01310101d000c020900115600b199a0040e065600e084540d620100c2c000700d2440348200c410103440c0d000c00c00d00b040d640d400346041e01c4003103060354220000800c66603050083c501000d840c541180b05811000d44c0a8504088203044030034000d0306041c503c24066101c1283c55030700c118400d4440c41081c0800105000d11811440c2d641400c00c4994140f9010981d14400340c020f441e219000020882030740c0308008103640940d4203c00c252400c86a0a00c0d04c1005034005462075030490a8064012030001d018 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 23200338 1250 23199088 23199091
    0x21207050906032a0c03031f06050a111213030c050a03080d02030403020c1c0201021005100620061006110105060f060d0b04061502120405010203040303030c021c031505030303 77
    0x200700c01e0030b42c4c58411030929000c00031402e42d4164008015822514a10000613007840044000511340740c1c03030482030010001c2c081c0713401850018400310701170090a400200741c03240b064040c85c00300c1035202441505458002c007500c200b095440e002c505200701d1801c15282100f82c0c0d125030040358425982d4000d00010090078040202080403e1003240b01c0a4841d030b002c2c1d50f009000c1d02c102d880030402e400106a0080c001c03a0005000c1c142c0700354482c02c6d0b580400182520714000c0b241046246008541080580441e010f40b804100400400c07102040444098140040700c1c00d05507440c50400f52000d00002080d480342d00b000c60f40c030303802c84403440d4010b1040520840c0040c11074680b030080002002003582c048180d41c03c0c2e46940710102a4107071030703521400003e850080d075510b0000f140014040c2c03402d0702100d064030030700c1010002805180da000c1301b41e42c00c9951508004c0360341441c84a050341007002004120a010105a43e0390105990580001d0703c00340c550402d0300c4e1340360785400c103040d00c0307200 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 23201444 1106 23200338 23200357
    0x504051605060309030901030506060d0c02061b0c0703080901090801090b06040e03040807030b0a020c0105070804030e04020a02121602030706050c07090b03060415020904090602120705 81
    0x300903030000150104481c0c5a0440c600361900701ea0700d1050300324050400d03443d00003040d400c6d15101c0544070b550031400c500f4446070720101402551400c0840c0c40c3e4040721106c2c0c04c48280210032004940b41250031802401660342036071158665944008080341c1041150b010001c0c06040a01c0f0b547c0d0801e1051600d10b9242c200a0200001d0300c1520790541400d8204100070031a041d4001606011071303500141e4840c0c00c0d074589800c90020302401950030305650902041108841d88004014466272007911000081100c01d0b0500040340980080c2c3d10159000410710b83c0083c1c111000f81000341e50308683e1500742446640441d0030214540e12010100300b0108440302d881001341710507805041051810880c10301032030b0020383e071208043c20280520f40096000e6003110f1164040300c0380640090001d214921131858517000a60104600e412030101080c042010248140200c481d07241 = true := by decide +kernel

theorem cover : BRFrame.Cov 23021588 23201444 := by
  have h0 := BRFrame.cov_init 23021588
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 23021588 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 23021588 ≤ n) (h2 : n < 23201444) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
