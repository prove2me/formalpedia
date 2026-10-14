-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3200
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:57:30.091503+00:00
-- url     : https://prove2.me/submissions/2a73f390-f7f5-432a-a273-e075038cc5bb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 575359712 ≤ n < 575539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 575360962 1250 575359712 575359717
    0x1902040b04050c0715020310120203030c070f230906010f170103030c030306050d030c0b0a2a0f0c2105221406040303090b0f0408070303110d051207141e 67
    0x503240170308542c09031100524141300304c03445080c40c08807050f540742c02d100350000502c1a41f0012030f090301c020401e031100000c04010700c000074201d81104059150411400100265064a01141d5050903500300050341d40c950707100c140e00074020700c0c000d0394141952074116815580d074424a1120906400007000b81940002e5040545010340c405101850792074041c00240e400b0720f031000e000140b003c1e0f2101d0000b1030b40201150400c412031004261070750716003450314240070322000030808014100204200c454011903070050b862001d0a0a140101560b00c0c0c01070704034040f140060034040441e44221210340142c0c2951034007541a90044130f00c03880e1007002107426004d03004100c010070340904411114034056085074241e1740e06642c1c1e482800e113410b0507401f494110507400e0665010900010400b15010048000150301170340e50384400303c2c21003200300d0030840a1300440c81009002c00c26024240794003850075800c4070262034403004188041000c0e072164043c01c0600101c841c8624020308128103444003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 575362212 1250 575360962 575360977
    0x6050604030524010305060a0914030a0903170406050d0f0906020c030a1d010f03150504111206010504050f10030906021614060727090920030606031902040b04050c 72
    0x98102c0c00d02d04010701100500d0f0034800100303168081d0b400505104c2582d004160900c0c81000c0201180d41e00258050039500b042191a0014441d003108000344888001011952442c5c41c01d01071070b05003402801011842201e05c0c2501d015158000c07402c11001660189030496000b820841d1510881c00342a0380380c0d4004004480003611414461f011034141050b08007440700161120983d06c01c01160960181280300d00040c44003800580c00609034465001e4900480704a080b01c55840c40c008004241c1c03448041c1015040110920041c030468503014440306004508440790924100c03007600860190844000041403030340042541e00d038548140ca10403040900c141221964000180c4c14540d494000701e5450b000282490408900c000c0c0c08400244444d05030106489450303120f045110546803981001c40d40c4040780c040ea000c0c0940700341c0d000c2d50800b400320090b154038140040002d80c2c9490308010b41c2d0a0981d1030f1001d43c1190780b10b0340801c002c814003600600c05440c2c04120603040ba000300a = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 575363462 1250 575362212 575362243
    0x2040f0b040506010908100b030a0203070e01030b180709020d1503110111191101050f190807030902030a0312060e09030301030b1030081b0712030c02060c01060506040305 75
    0x4011446139800b800000d003d50711280000c09144c0b51907007040c03000d4100141225058000d00b0f44100150701d05014032800381c41c25007840801035140d4600381180140c0188040c21400d086864480c0a29010403110201c54500d00d0245e19075050b00c01c443c0040a07441852030120f00c5228000041000c0684e6080620000340c0b07841100010b03806149403038041d100c0500c51103200721400c00002032401850a600884180741041c01e142e070400c40340304640d000032440796a603504030b03218490b0194011a801c0d032140300c42c90140503000c2c959021a5582c1c0c1003400007010b02040301c060404101c0c540d840350004000d07a290100960501c011641d803664000e010950705112000001000c3d90940c2d0b0080003101c1401840c4820f46241d1071644155120741303241968943d8192070080085115000902150301d0301084a0003043d42c0100500e113031454940c4940105129007000b2004070760030030004040030b9016134200b03544120700c044060051410303820256000c44041408000e11030009110f1000c42e1124 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 575364712 1250 575363462 575363471
    0x33c05010b0702060403140309030604060209030d05090315180a0605090601170607081902040311090a230405030c06040302030307090509010509010506180909150c090901031e02040f0b04 82
    0x4a01400c41807240502c06074021004100c1000010101107405014000780000d80381810610030000f4103001040e94255543c58010880d00014501805900040004c0d810102d203424809004280ca0b010700c1011542d4810b074550000d4040f4010502c2d42c0140003a071800d4440030b03042460320400414003a0313107403841407142c0000403d500211041d000a0f00550030020080ca6503014000c64074a90010840007410740240d041112034142400500095403103051440741205104040c0700455000900901074681400d504070104003480e00340400c5400c029555040513520b50030054a1071081e4000342005204a804110070b050b07001c00554090800c90396030683c0d41d1303620350400105010030300807a54414105001040103192681c01401b90000c0b0601144803081000001442c074413044035050880c0e0010459440006c0340404400da2003140c011145007032840000c0460300101050000500020a680642c40e09907900c812010030355500800034840c1c0c06215020340c02610001c034421b4043da003031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 575365962 1250 575364712 575364719
    0xb1221031003021e060d0203150f063f091002120f0a09060e0c010f080f04140723010f0e1509060c120c1c050703033c0501 54
    0xa0011203008032420400c1c5141c4500316001c0088900c0c1d00e568100c3c1404402c51030b40d0031511070b00003505180c2941140144c07645041100184000a0740f540548201d6141002112981c3c030700c0d090340c829040303c0c51100c455488007045003e40d016416140d8a400341540400e02d0340c60301c000c0042e80324094010a4414610351211058164011a1101e051104602000071100612000815481440708030041050a000d403100c1003111200044915250070007081c00017070b960080c121501001640c6000286d0303180200c0c021030b02050282004104d48440c210350100e0b590100700d0300025000c1651040c0c40350800b12080b0340c00d918070480d003502003070480040214081c001c41c000360028502070024070134203a180702c03041010f81c000925950311102c1030020f80c0310000100000c400e80080341d20542d40e10f0000c41450351070041d81140442080801078000c01d049584001620641981820041546900d030886100710078001480880c0c0d4202100c3c0d0141c002d000800910004807040300e01f00120703601e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 575367212 1250 575365962 575366023
    0xb090a0902180403090b031506070f1b0b0d0e0f1b01170c0d0902190906030c0909030507170d0c0804120801080c150f040627050120010b12 61
    0x3001c0f140074000c20b003240e07020841181c81400656005406843d9140000b00040000351036400040c41a01d51007118240708040108903600040c0001154603030503582d0380f81071000000c0348294a003140d0b041d61905a0081c50075001c0041d4010003801006039844260407041584040911220690004400c01581c048000503007495a004800c0f46004915082c1007070340c10005840290400c130380055110380c0c8858034012034800d40d005410005804100303140365013440310900e28940c05c450035042c649104c42d400260040100c45800d0b6100c0704103407840340120309440e914094284c0032075040f41095904144540c0c048072040c4618491915000070160b9414100e50310902409500d030640e100130080b80386440c2c0703041c900c4140002088542e03c0c0102c074807410302058000e9071086020816010301098204184408030400c070508e1030300084040d1400c40002e041d418010020b03222001d003541c0703213003500300203400283c1c2943c800f50144004c00c1a02c0c244581d43d0007100c0e400c0b002581c2c043c240b42c08400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 575368462 1250 575367212 575367259
    0x150306050f09040201030c0e12030c0105010b09030304060c1502070809010f020d08130501090c141018030f02030c04050711190203030f13090e01020d06060c0c030b0a0b090a0902 78
    0x10000b504800c6107035500c2d401035009081d0100c0e040240112107501400603600ca80b0419940d10405020f151640d1402400c2425140184c000442d429020320100c0c1044c2c90000598007164200d01c1d229200900c68100303103290000200d441091203000141550a1010780070081840a5082c0c2e68a0103140046208130703101c4010240c000d0000d030700000030569003c00d41040d0845140200300000f010886607940c20510ba0b45c9601080c00c0081e80d06044049281c0200ca6038509001400d05080030741d070040500070182c4113400000c0001c040004c0301c00c15920b0030400040c0f050701c054010449030800790790250080c10010b03481c0c08203100d104400b9004500c05040c0480481d4040c0c02507080c012030100c8210302e6000440b41c44a00400400c000940b1002d40c01503491500d0118001030780c40002c21f1000050340e619030051800e02c0850b0180b840002c02d50050f0741c1c12170383c004034000419100c10456102404141400c550321160650600030400c8042c2d200550007442100d901030740e00165000c1c0303a083e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 575369712 1250 575368462 575368489
    0x71413051306020c100f0b09010b040305060f04150c1706031603060207261909050906040908040b0a1205060f031207020a0b0408030a0909020c0a1401060506030115030605 75
    0x18100c007600100040c0303940c000c3e00040703a1013829501c20015480c052403c8482c0c0d4400348595907107620030b1100c0e40c07c0c40c018160140885401d0780d85414210f031140707a41c0f0b1070040c280e4644502030b1400038040c01010380f12042c2d010540402840881d141c0d0100600c12411a0b0101c01101d4100780825058680001c224135500302d0740100c2c0310380c113266864100080d0880c44003a2141f000900141d1103031000302491415041c900c440c0b8684a046103d00380c0d04020200c40f444040c400d541909200f665508180b00e54401c800319408a0040c00a107840e983c14001c0380c4c0803015101c0d01084c0d103158903410043c02c044a0381d0258040189aa07500c04004410300062542a0140c000c21140c03001c20803440d000b072020340d0000e003100c00c0140c0e0781c4140e807400354095070102107290000b18101b032499030b2150108004001862003507080c200b070301013480c1d201c601c19200180030178503404485410410a40119005100c004c2a19480c1d6a546800e024840d60040110340064585807020441d03140c51600c5682d0f0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 575370962 1250 575369712 575369731
    0x1020c070f0f060e040207081c0e0d1704020a150302041a0a08010506131802120603010c09090e01060b030717070201061211030a052b0905150f04030507141305 70
    0x90b507103071101c180c864007a071001c001e402c0340c0c00b04a604041040d9500901034030a0103125405145490742c0c0031011501d144044041d2a00130800c46101030b030b44000307071605003114078420100c19121840004c4190719203600200807480404240403145030540d001e00700715a140345980c0c051601c04150300205205030450070340445c4100b001489142804000703444440e20b00341c2418038440e01d46000c081e5084003100318a1000da00080e05100c924900d0011030307003141003507000388802805068090444401401080c1c0c003a56207071010500c0d44401d4000d58010f02d140740c0802e50300d0400b05001400d846107124a0682c8000200200300c03e41c2c13051041c1c0080f038105440815514140da9555420f04481100059252041c00e0090300881e8050080600c0d00241c8600090715122140350742000c826152042001e000e1100b00420042d1581c03069851480c10700e10504d6a60304420078149490301a41d0000340140c42a24400f05003131481820440c128074080b518800301d4544a0000010788004545c41843c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 575372212 1250 575370962 575370989
    0xb030103080f1e040b03012409090e0109020904050309040c0203040f060f030209042a020d081906170a0b18030702090a0f020708040e1312270801020c070f 68
    0x3000d200310b5000d4082094a920243c42046010428400d00d40040e041503031141c400000400c0080700c04d80e01d140c08440c5034a50390700c501403880409031100700d485c0b142000c0161202e00d408102c030400c0d88561a9564010441d060509041c04c05c1c41d070340c1d000795480601443c40c100030144401d000200382d5044405419055110600b40305e4111200140c104188051580910264441d940c032401000000720004016034003054103451005109051208020b055400c20090084969400341455501c0850004d2030383c1400030024046000b025294007103070051904500c2400400008520400170b1402241401d0440e203e05080810100b06500000b0380e9a1013000f071000181040b52000ea480450034600040202e8040240d00070f981c00224212020240050300380600c440001c800c03030304080041c0c81d1141d01d154960b5444040c4449020386000d01007122190704549000011070122070750584407503035012b41e03100354481c040d410003001440c003070080d0800031032550b9080428a00b140e1001a03c580c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 575373462 1250 575372212 575372227
    0x31a010318080c07030b0c0c070b03151203070c030b190c0f08100806071205010e060904081c09140c1002100e0709060609080d080c0711060c06040507050a0b03010308 73
    0xb51990303ca580d56400e18064040000046401005036600c2100021121951500a02d41203421710b43c2c0c0381c02c4914021410b02c01d0110704442101440c03401101580c2c024000804000c01ea0320310b01400c07600074101d1181c078001200700038490804a000e0040f42c07007035403500001000c00d1015603c0880c26900010031042480c50b04920460560750031800d4031119420507070700d0340c064508040b003c0300e208000c11024903100c004a060b9100d80360040150315030741149801d04100203210070001038400340c2040c03408107100005009131040d0000580c1015020040c11005191880d617010054010010a019030315a020300c600f04503015801c407036203640c0a004404c0810300b40382c00510341207540050388e1144c0d072000320b648884d0b803240d03101a10064840041551800001c149402030b07400054042104180500c070800002905441d40b00f9030219920140009041c0854158040d8184035910380c400c140920061100100e81d590940d80181d40545400f92581032614a5200078030008010b840c0401079074 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 575374712 1250 575373462 575373473
    0x60506070213020909090f070b04081e0f01020409050a060509062d0d05010e0f1212070521040302010e1518070b03090d09060906080411040f0903031a010318 69
    0x882c121903000c60041c04c0601c400b001c00c5032a0403c807081d80443e484501a103010500421421004143c0c01d040c081c60a030401a4107078450b0440940c4070701c0b0810141d51003406000a000c01044850100021512141c1e202c0703a0700003420341038a211109a207801c5000c03440b42091000c540c0f00d1603000e400b01c40c00641d42d00c0f06c0c880051701080180d90211a9580d03804280e501d083c11200514003800021031100009182d09007840c2d0f8014940c00c83c1c0d13002c15507031022403241ca03043d030b86664814030701c11600d03594030348058034a4819010b130040c01b084040c0c07840c0c60f1a091245036a000d5030081d4000c2048401100d00240c0cdd0300e22181c2c040101c414014005030040200c5019000d424940c0e50070390b107501c0d45c1c4444400c500d400c15034801e89950058850902c203698401548170040a841c41d001f96100c0c80c0c00c801030f0801c04090005001d182100c000d100040c1c90300c0d0410003241c00e00c0c890402005c4040c2c10300070020703d400a0050742014180101282d03542c868062884040001030120844a5507a9580e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 575375962 1250 575374712 575374729
    0xa0606030b1c0204020903120702040b09070c03050d021e0714070b16020d0501020310090e16090e280201090f0510050a0212040608010323100c09090203010f17010605060702 76
    0x12644640c0800050381b2a4405001030b090051f41d00021a45951140c8100b10503141410200c81c000d0342100c003004000c6501810707400c4211f0701803d18035660014215030030060f21840032008000f01048400d4403c0c0a035800003000e0140c0a42c0f84454802941c0c1440354030f42c403440c410a04000010320280002d08003001c0e1f0110100d100800035101001a699180d09a0300215106175801c000500208100c000901078843e05002c140003400c010300c9046100c4a19403290301a00911380da071401313143c1020000300007100b0b001c50030710218010f42c040501d50795150712042608a00052100b14000b4060103401d008000f603900080c2428640c0b07078103c104840503000b0080e0304045100e107000f002c40403aa0000100060400c0c1d0703a580c22a90305506020744000c11001154003102e141ca03202005005000c1080c0c0c00030000007074041410000c407001103c41c2070300e0b0340180d403005100100015154006c044403600702c1c0c07004410b0003442100130a00d50b00701e03103a5100c2c868010344100702d00c00051510451 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 575377212 1250 575375962 575376019
    0x6050109050f011211120a09020913050109020a171501031e020312041517040c050f181e010b13090906090605040302060712230c040317030a0606030b 66
    0x4010748422036480c0500191400c3e283e408800b00030000d0f81e0007804a001107030642c1f01e2504141070100304070035404034074500340082400107403018050112042180a4010101c07003500100300d050142e881d80700c1851410050410000c1c6803080340d03818a0000c85c7e428205040700d07040b11601c085404201d08aa040307041a481c12a071502800e5078104c0b40310481e1003d803002d020704000e81102520704801c09011000b507801d1a14196030200d0230880000c4c01d40e401c50342514801d4410103a000c50709004aa544106002c03070401901105080020000140052000c508c4000003000401e984c0c6402c8100248151ba20580c854aa036200903c44000c107074006c1c4841601c00e00e0300045840042d02e030784045400031f5900303e0050b0031003028041d0b115800a0290b141c001954010003c100801d0000015a0001d82e0035500d00003014002488048403601034800440e004072008484041044491505505c03c82c0c01c21080b5250450200d0458420300c034154002d0000782545800c1a450034842000940000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 575378462 1250 575377212 575377217
    0x5160905270106180b0f07150b030a060f0b0f0109060f120c02010c020c0f10141b0706140a2c041b03050f0405070308071b031103060a06050109050f01 66
    0x3480c15004007021004078000d000c140e807100d016690545200c004a003c9500608250509100141038100c5600c11200031075400030500da50b0707801d0500481c01918543e035203198140115007c60781800b100340c02100120070120010003d0414103007c00001c689040034503800600701c441c06010603401008003610004172410a03440c101c820020b20020794100c07051510040c3d442d2015102215010840da0001c3e100c200e542454009069001c00c401a40f841d009100704010002c48408155030701c012201103a11044c40004100f02c0c020610395200070354811030380041c220048450801d9000d80940b043c40c1d00d244d44440385480711460402002d6404110308010342d54140c450201d50303030350380328540d040347e489103000310203850310b4002600701c4100501034a115181e01c0100300002d00c002c80c3d80c1c01034907401401c0e540c83e042c40c2d081c0703070842c41c2064101501c20f550031540407090003250f004031902007800300c00b183c00c2075a896154605650350303486100c2c041a40020107100b02c1c40e090039900d0740b50341b040c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 575379712 1250 575378462 575378509
    0x1806070311030a1d0f030c0103090c0905040503090a080607020606010e0619120c0302040f0509040c03051b040b191404020c010203100503010c140a08060604030b04050105060405160905 81
    0x401c901800c1d64000304858000c01e0410340030110a5007403504003c2c2c0100c0c112409445810010b022940315144e21407954101035803074800f0010030480d0119840174094017601042186030901d41140d031b0f6031108000310b118070908580040d40900000c2c0075442003006a02038603075034441d0001500e4400ca080840e95000e80107001c0204043d04800c203008480c00c00e5034650030440f02c0e0b54840803c032491001c0c44400c05004101c00c1c04030b40403580101c000c941041e1408652550b41d401c0c8480000e03001c1d04000d003135000b2521601c1452034240b07049048460202c0e401c03c11800d40300c04024210707a100804210360584040100429a180c10090b010354070081c00143c600810b01d5007460072a8403c9600301b003800d000c841c06000e1800c0900c03801c03850b800d4030300300510a444414510541805858121010010a4800075540b6103444040c4e8004540c4840c1030085410649001400384c4401c41d02d050180d490000014000c205d00b2441710700ca0f480355100c51500700c1c28030081c0a107a0000101042e41503419 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 575380962 1250 575379712 575379737
    0x120301140402090d0f0c0905010f051f0504120503070203100e0a030c0203010e0106080f0618100b1c03030c080a1104030b0402040605030601030f2603240418110618060703 75
    0x2101d00000c0550710400492204604007987c4c0003c54406800c038101301d103074072002800700c1e440300c06035200002084e00c42a60003840350401120340e485543c1144445180620120b0308100000024004580c030860940b20110030703180620342164900130b00101070381c1c8032481481c0400e00a24592000380c1c00030f800483c524ae60450020b080d44c07940d034411815580704880b0110f112800b442410b4001c8900f2000c180000f6100c2a000da55105d6403c0c01c0c0c00a41c0d48d604048503a1751a0000f60110004841100442100d1420f024004000f0703176008a0120301658002144610144a0350220003a2920050700382402d503201c0301da1021000b8130483c2c1050b900d0102040603541088010b0003184180f6907442d242e071140c41c201100c0c540c20701e02d00d02d104200c440146003100c10398040d030341e0189811008803012048000e6400700d4100544075603030024075141c0320903c90003403d0b41d0709060f81d0282804c80001d90000050140511523541b04050105101e0350703c01c11032418000030141ca50081c588800007440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 575382212 1250 575380962 575380973
    0x80c07030305060a051905041b090608071b0b1503070302030304121401020d240806162c041103150609190b0702210606060a0210060b040503120301140402090d 70
    0x841c0d0035582c206039481c8010800c03071400e03000741d4400f05880702403032140c4c3d800c03e00e002d800700c003050182f4018440e00100040040b031150108600c800703000300c400102c0c5031036406e1807d91f00d00141c0340c0003213440350480756451f10f040001d41d6000f00d0303034003a0042d0b203051f152942d4070403036510f13038001201c442c15080c8250b081d10401340007402c5110990a000180b000c5030001d440201e06006900c2e40382031050050070441c200010034216031200280c83c0b0351008130450482201c070000b40303d14000d2901914000110303042d0761108400074040f402c0e10100030f820254181101580011074041102e10b130b80c0701c02070260707080c00e0020300704801020341300011a0a9070700365000c003548640c200c804020000304100d0154030b00441054030790f0883e00000092031031042829503c3c1c5600401c0b05010341c40010751400614070810022000c418605010000749450320310703100c0c081e4090b1007014800c1c880c0381d4007800c000d8801e8040341e04a40d0054034804000010400b40700194001c141c5c95a413000915064002055 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 575383462 1250 575382212 575382229
    0x1e02150f1b040801060f060908060a0504080c0609250b0f070303020403080d0203101a03070f0504090606080412090b1902070909080904151d090a120207030501050601080c07030305060a05 82
    0x282d807100104d0143c1c00e022031440200351b1a4859410080c500200704081e0002142945d000396409138045081e50b29400d05c00b90341d12405911503441d03c9a001001b820004c0840c011014400f55180c4480214000c0030081c1206154092564440c0041081000301e050302d0004058040c824103025050942c0c0752115500c80c0c00c8803444103d05900082000070281c074801140307025202204040f40600d55401c4c900c0c40500004103042d00744990f04410140290141040c0d400a04980c8401d0020a40f6030740002c046071016281240c403e5040726600c0b03141c40c0210700c030760107843c1d6030b5504508041005c600400b0164910404e2404c0d80a07510011030b4004880c050500c20500410500d03aa41440c0c0c020302007100c0f24039401030f4044009910910558242d102880c00e81290451083c0440d200c55001904109003d10000c15000d41000240784882d0041783c5581142d0050340200001e030355200054829078421030fa4407004140810803400082d00a600c06c80d00440c0240c6000b00003521400815441c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 575384712 1250 575383462 575383469
    0x72a06090c06020606030102130302010c21030c020c04020a0c150e0d050301080d0311030a0e0f060405010e160806010b070503271504030b0c0c0a0b04031e02150f1b04 73
    0x50703002250901c002070301000b0b46034101d001a4002c5180c410380c0035111039040c2e680c0c00001d04200314100e1003014031060300d05400080b9041c0580890310002c0010241c0180700c0c00e80c040c4054050b403503640d5003602e0580300351200c2940549411b101c5403171903503405402c1c10070884000c01040d030f0f8680c1d20003150720820104440b00d11a032503d030740c1c0b9410320403550f1030903041c8840e00d030403d400c000c0341445a002c05020b40e9080840c040b4041818030314450250304010b1072204019040c400c60003040180001500070501c403449150646520648a040700c04000c0c0c0b483c0a0072107a50300020040100c9203403078000349074450040013928202442c9144164000c02d403056694600c10403810f044141d03182c072480f60500003120441e4640741600d15620290f07580001800803400c968041034201c070100f230610042000c1c1e640100500e5061030b00f4603018011203070446a130348420410203800c404103800001c0c04016406120401c642c259a54074001e034403182c00401619000b00451007000300d42c0082806417029 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 575385962 1250 575384712 575384723
    0xf051606061d160e010c02030a0b040606170703030f0c1b030201030c09050307031211071706061806090604150b0d150f0306090201020a02131e05072a0609 68
    0x301d480c0040104641c14000e003041600c02c41801030046600407062110710b200c4a5003426246506580c005075601c00e01c91201135090b010b40501141040304a201c10380c0b0030f43c40f61108206e159201c442c10784a16070340a1840c0440d078480241803010902800c104042c0c2c031164542401e003820780d543c90380c02034400143d5501d01080c0ca10010300456030035000301d450f030801c10b250422005142100103682c42c0c005210140149030000d00380400c00344500c61900c5d80000c00d000300c8040e84e036102d00d01e18841d41da605440b02c46000d0365011034500e1614001c2c144100c0080d8900c40c00c152102410000802d0004e000c442e03005070345e400c40000c220354140540d8024090104c04a8031038119a0800041d1070300c10300f902242d544084018840d440605845009498106900144941c007610042c0d22741516400042e611032150954074621790103540126288004104564440ea1a46440c000c181d80040d507800c03010803807007180d00c07840c059100100c020300c0321b0901b00c100c00d600e400e40f6070000b115401c8800742c82 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 575387212 1250 575385962 575385971
    0x6090807060b100c0215120f0703061e05040f090203010c120f2304051f06090e0106030804050d0602040302060c15070c0c03240e010516110d0f051606 66
    0x280000d82c880c140c500103080d40c14405003610800d008005100040000b84a0281c142c00c5d80c10b04003d85050701c4103040c03122004401801c21240030131080ca4120343d40c3d80042c0c00c4ca00c0100b5210b1800c2c60b81c9410484d03410031480d42900341001c0001414040c115040c42658901c1e201c00507a409002d1a2600354494032400c030070228029500b0b01360341c100000408076034249040b205150002d50580c401c1c100c0000c084034000e845914101c1e04144000b076130b445041c030070380d200601800c030f071640201304403a40d2a40800101c0001138405003690340c2ca20000c2c2c6060003d00007080076003000d400c504207540c4991070043c41d09880c2c0e4000340d0540c00242d0040b60591010070088980c0c07101c2c01c0000d8000569040030001440e03d030b036030014440124000244840c03614480500740461060710310540d00100a401d1100c5404110043d0081208940480018150b0904900b010b80a2843e0b001101c0490019001d8003024010030303680c40451605401c10000101301307000d044060301c54000e0060388035000c00728 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 575388462 1250 575387212 575387227
    0x105010e011b060506120609030405060a0504090e0705181515090a140a0b0c1015030f050a0b150f060702010c1407030b061804020420040305150a020403050721060908 73
    0x3c41c00c12251034081c01ba611038030600901201c004281c2c2c1c1201d50441350300b80d03034400c41035080720580225030008000700d00b010098051804040b60ad030090307540c1a01c9040c1000d407801d01c16080e005080d41c0740340341690401c280c50034500300020002009680c55083c98907110900d00803442c10405a4002c90307242046852844a41c940551200003c0c00c0c400c00031800d1841c0c0031103903903d0700391050490040780c2c5d68400e4140b4884010304080020350700301e9007840740240c450410030784440c1a9803040310044007590024407140e105800310500d0010113001400910300543c02d100040d40800c0c000d0f0305000311200460b0001e074101c8802c105130086880580038440c03039813502c5524081d01070b00700c2e4455044403040c1c04903a42c42c11143c07503203e82c04a40224001c0004804d40040881034078070000c211100040c00320a104000450503011521000b140f12207035556604081203000318000100b15400060b001c1100010f0410100610b005418800c42d0440c801c1d038401040b548159011100c9480c08183c50f03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 575389712 1250 575388462 575388469
    0x15020a060b030105190e07030b1501020c01081e0a140412020705030d050d0203060a09290603042f0a0905040b07080415091401050403020f0f01140105010e011b060506 73
    0x15041c4901c01d80c002d10a03404c00c0304200307001d02c0311201c000c0503c1e81d58031165003212008102c544001c541003107800402d420b1400b00740c07a8100c6030303000b07040c05482003800005e16548a400520f1040044503030201c685484c40f60310000c5000c01500b400b80c080c0e04c0b98101283d1900604819019038424401605a865840400780c2403082d2540b100303100303420145403000c071581c1242c2100c03e482c24580c00180e032580d816000410741245504032030300451030031030140d0f00c00c01402580c150340c0100300210400803001c0c6003001118881114010840e620702c00e000b2100c032000030200f90305d1581207051507408402803804181c1c560100d80c005880c6a490304107020602911015a0350815664a801a064901922151100b03454000d90300384032a91802d209082c4224401900000d0407004d0080c0b00a080c04d00b802550380c00c0550548426001742025414949014403503551550344040d08085240c1c6031070b0047d601c2c5810b00d0402414490008207150f82c040e00d803601c4200c10340c46208002407d09048092 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 575390962 1250 575389712 575389721
    0xd1d0f120405090103030f031e1d071a032706070e03030307021e120f0310050d151e02070c230109030602210106030c080606030f0f060301020415020a06 67
    0x100c810a01003007105100b1600c40c00707219030641c6d405041900380744517201012402843d00f00c007200301002260107402c0054040e0b8000714030150400c1c9a40307000c0d0705090758860301d40d210751044a0b10030500f88120810b80a0b400050750f8441d0b5003002010340f56030b12401204402460742f0b00c450594010604010809802c01c0d41c0410404007a002541140782029002c0d41d104c46030f0b90950003c034116070b2907030000c1d0340800c0b0014014082c1e51056440307510300102d07041035400a40b0b0b000000003800102241b40d0804624521045030001d00303000f146240070150344c1c0108040c1c0d18038520301040007500319038039116000a18010380b151540d00245441c040d8001c0712488144013070341e640c03081954a4000c40e80c0c0640c03004140d9402500042c0d455940a54074030840a40916102101c021040001202034144d4800078001700b4940b2005459940c904c01c2260b6440200c4003503002031520800300d440c405841e1502030340040701400043c600b80d2100b907440400d180c503400000041e40714150310010421507014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 575392212 1250 575390962 575390983
    0x1e09050705030406050a020f0c0a0507151b112106150607030318021522050a091e02031311090106050a0f03020702040f05010323060c0d1d0f 62
    0x504106a0802820050881c071010f40080c11045c2c079140841c82c0291a541102c0058204181030b680d150350010300903031580110380e0260b03000c4c000c1c0c603000030b1080900d007090910340e001c030354542154070342440d1042041689120182c882c1e41c040007900f540b50302c8a10f0300c0110000c02034403801200c0d041c1e00e1264a0014014009000190842c402d4030003a1654816a466258503041c0407a2102000e0524401940500c401962100d01c6214036404095032100900745410050111aa0400c0b10700003810410143d1150300d40040002004200162048d80400f40300842d1403a841c09415030740c500300041e600180d840700315098504200c0d10030401d10110b507030f14500083d140c02c0340c0d41d132420b007002d4164028101c0315000e005819840341c0304180300740d040340c2e8072a03801001048140040b1407031000501c0309000403510840514405e200f503030b01034010000da001045009005680e68140303004100e401041c0e94290366510b0741d003104100c010511b03c01c1d03011a8400000d188034000c00040c039250042041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 575393462 1250 575392212 575392229
    0x30303072a03200111130807141c06021b011a09061008060d0f03030b01030b040207020d082209050402030c0603250504090f060302030d0e0a120215041e 67
    0x81d00000007500702c82040c5010301c0c000703601c0f0001c0c0d41044441d805003c2c02c203c21020440001000c6a00424214004050751202d600307d480c072648034501d000e80200303058041c5501428401c4052a140324a0308071220b01446100b000d0f040402c4c850240c076180d01d15401c02c0c1c065035103999900400051078407481004c1b0004841b040201d04003400820000004118002c0c200046500055440d8030303214100c0010580c062000c0da900700b40703801d0040040c0307980e0765900e000a0134070107010581c0c82c0038021307114421b800505202c0c2d103088a80d44c0c03c103036510003404019a10075000c81d2120070b00c882413011000300080031012a481c5418410075007008901041c03c3e209000500030b2150b100c1c482444071a01004039581034100d1100d158040d1480c3c013859005000d0079050a030304203141480b40d0010000c5900c250100c4984030200c10040e5408480860100e400c11581c3c030040220f22403502024050780e00180511003046003010044420390300071b401141441c0f03411000e821011210555100c028900035 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 575394712 1250 575393462 575393537
    0xe0d030c080a02030907030206030901020a1808030a11010e15061305010b1c1104120213050106020c01051c0509060103030e1f030207110306100302010306080609030301120302070503030307 83
    0x10440507140400c06000041e00e5940030002425407241000144055500100304d1501c0f45003080815002c1c0d40070808460004a07603900041c0060240c0c1d05100c241e51001000d1030030911801011180700a403403c0b580707150340d00d942524061403010302c14000140c011208401c0c49280000a0004a0342c00b41100c10280c1c2c50000100000f019860640b0781104c0c400242d66030003818240140c2c09490207545088040c5400100014948415070191030f00034400d8900600015030103c011040303d0007485401c02580000003800c00c198400c2c07000303040d0180c4c08071440c0c105020000050341102c070b04840260040d8820b0005109054010b00d40140030401218400c5003640c0711011007803942c2c0c1a00002c0103154000c035001007080300080441d2110385019003200e40c0c5290548032520041d166100503800301e403401038081881640411801d100390340000c021855a46400c14200c2c2c544107a1006030b0450041e101701081c280d406000960054045a403180c0c0d10300b4104d19040b65200220016070000b0415 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 575395962 1250 575394712 575394731
    0x11205011109100c05010209090f0402042406030c021c0203130b040b04090b060922180507060e0303120a050403110114180a080d0e070f030b0103081e0d0e0d03 70
    0x2c006000c0003e400c0c515101c2554211864250b01a01881a5070b59011100b20200310341480e44114003442540200e1303050010007a0789120540450303490000f92805104d038001403041034001d4001c80b5041ea01403044521031380c1e0820983c0710341c0359000e40000040e00006422100610610780c880003900e600c21080d850240341c20542c6e440ca125a10440074a6903ca4502790341560b501030540e500e40b00046c0000300b07803042d136000070304a0048610119040526000c0641c007035415140c2240305099001000f01a11800c1c8882918000400a45036074588070400c48000070f01010224540121240203000c10181000d10303000d0705040040420b40c0d126072403c2d40214156240c0c1494a810020300541205102d03e8030000c1810301c000c103076001e01040070000341c5d9244290540d0101c150481c0a4090310325442c0c2b5005d41111540d02032102601c807104c42c9006001254460f40100b40d0340040c0b40c07034541195a8491441015041a4500d02060341e5405000d030301c00d00240301e44800102245030400c0700110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 575397212 1250 575395962 575395969
    0x40c02030c1c0c240614030606090408090d03030902030c0916180911040e060a0501021002090109170d140a0504180b04050c07120c0f020d0317011205011109 69
    0x1116204016000b40210046414a008001540c801038221343c015a440704d890f44c00e19604500b90b20106502403030407100196110840b412103100d540d000f005000b854456800f0132807400341c041d0040c0d03024030003004040d04075503a0600c22107619109480200716080349004040c03d01c0d50080c5824080c481150400107884200100c00106079241d0070060400d00b24042036000c0602645c000c01e01035443d140c1c440d45089508005002144c0b103107d111b51f4695622024068014035910883c0d015910610107804481a540c0103000140c606140015106a481d60010300080340c080706010541c003c10a8094080c1d4070085400584801480700381c50f049000100620b070b8802d0380306080091a0544840703201c032a80b0380007400c0c5440010824092420000902c40c5940d00c49041192000343c10303601c0e10102d600500d1071068668015858080344103c54080c0702d0700e020081801c50400a01c6040400108420020030b4080c0c030070140b0441c0112030602c1c010742107941e00c0c023011180000078013401d092540e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 575398462 1250 575397212 575397223
    0x1917040b0301030c06111b1e041509050109060302180c0c16210c05060c0a0c06051b0706020a060f0e010c0e040e070b0301060f09095007050d021305040c02030c 70
    0xc2c04e452200e404170000d10321290b180c0e60748c034281c0d034030504040c0500206080c0c0d5034030745c1c1a42e4060034104030300c0e680e40744628119209480000e40280813800f48098540340c0c428400d900030000040c4a00e0311000340511420010403440340007000c01440c00610080000b140c0c00c0044004101c8461400c4a41e034442540006a5200d0701303129100000c2c0c6003002210901001e2034860303004108904031034450b44094010342010440560074481061101c900d94000108581168040c0d0003030511040b00792120409408904490f0510300d85404541c1c54040007449024103815199032021415a0307000c0402098a000f14134030320740c031f80c4103800a0049540c0d20f811241110518141860000d071f1401c010350381100310b5030003080d0147c82e107030842c441459514901d01c0d0242101e5411030702d40440003010f880558103118049415110b49100c0700e00d403102892419040079079401d10605161170030754004242d84c0404041c00095550680400490909000b10b454a203001c0c005503081c01c03000141c107039941 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 575399712 1250 575398462 575398513
    0xf0515010305131205090604030b0106020c01021f050402040222030312020a0e0d14070b0409050109020a021c050c0706030209130908070b0604060b040e070f021917040b0301030c0611 80
    0x70031800300c4c80c50664001c0c0203c809800d40501b2841d280c80c1d50b420b295910100c01d10519015003e0a00345446c03640c808502190f5502090030210300004803030034014000c1c500284200e801c10703400c000181c4a03111001d0001d2103240d182541c800c2e010b0031450300a0800c0c0384042d0403065240140440007105400030340c0084881da0a40e12810031010905010b52149002000700c1c0d80c5000704040801d4247c418401841941c9400e00e080c042641d94980c2c0108030711aa122a0005812803800c030052007103100c80c016840d0401c1d182203070030660759045541c1000b29a51085000c40da001481d80300c2c60030710040d807015103500b80e03404100b001c04a8980c110503100f42c5900810070049880020510f5540e45c0c403044c080c05000741d680c0e0710b580d159060b07240701d83e80540c2c00c4d6001c41c030814501a06144000390303180c0c0c030810300d204002800002d55980704030a0540c02000c602c403e410720010400d802ea0b41e0180d402940210b01421359545400009816210081c03003610700e40d042a409440c01100184403010710 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 575400962 1250 575399712 575399723
    0xb19110d0e04050c0d051006080f0f1f030c06050414060712110f0a03050304020f030c1f0504121101110c0a030b090129120a121803060f051501030513 66
    0xf0b9a50159080314a00c1880880242145000148480c0030240c2c02c191081d100c80c1e803101540c50b282c1281c1880303119001c03180c2e80d99205190f4009642c405842c5200c0c0321900d0700e01d00e0304520581b01e075140c5041c1d483c00c1e0003500c000740e030109040182c06212045100d43e8241511181e1601d00c8903142c80e208025094100703800e010841c00f50b050710340410040c8402041400f03081d9200c0d42043d2074020b1a0358030650342a880307401003c03001c0500c0d1030045400110711500030306814110700e010b0481c004006c0410f008200340072083c0400a079590010300010710035071094503a0b0603000d61041c00508002d5118404008980c01803150400d26200c1c0c00d20001620b0b00700150032105e544802130280500468a81c40419401100d55040210707010b10310302c02407501c00c44112082d5140780f280980e0300c0342003000242c518144400d113200020302500e454020411001581d5a106499440d54403c4d22643d060940c159541c6100f001402d28000b00d071141440320900e820703c042d0801d0082668219440c030006840f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 575402212 1250 575400962 575400971
    0x1205030f0f19020c0f03060708040b0a0f11030f010f080d2001150512010b0d08030403090e090a0309060c020303090f210601050406052b08040b19110d0e04 68
    0x10200d0040c00355070740074418041401c114803402c0e07030007926480515411802540c1060462846280c041552481642c40d0760301c0c900c03a6640d540366003042c0d0f0320151007505020303990304c2e00c10f20741e0b12117000344903c00c102400802c1d600d0070060500080840c050313000e5181030710783d010140b00380d000c042580216102c5519014440c50b10341894051b080350170b00384a07001517180c10b078549102d65005802c441150400c0725940c5c1030102e4154518280c40820a4550b4031204008507940000c020340003441d045806480c1024032b02d034a450300090940d05c25210007880da4810440e000130513a00c058200c000c1e000c0f40c90540450440b5a01087d564040d001c1d07024881c2035140380010450300d41101071100048800411040086085800c82e1504400e000b5140150b041c07400200c0c542c1031041200b00070240c02c400d610840c0102001c21883c030302c005007007103803000000c100c0040c0a01c2141c0281c80c002d01400ca080c28507000d07da20140070302e42c43c080b454600c1c0c0c0000c0f000c2503c95810506000208200b600e003c04d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 575403462 1250 575402212 575402227
    0xc0207030f210e040605010503061c1b3c06030c030b09180105010e0c030f040602041d070e152b060b0901200604020d15051f1205030f 59
    0x600103003122220301110391011502c0c0303610540c00741940b0b15a10007a60200850782e00d4600446691104482c101c2e00144d140c80046410306c8854240c036500b900030785900e20005407145890b101030341c0d254850910101c50411009000c608182414140e05264a001c842e140c44141b401455588511403801031550b5000c1071208140603070483d0500110042041d0060f113400003040b41488040d20700000f01d5844d040020840000a420301c03030140f81800c00d4142117548540700c101684d640100211911303034090200054136001b41f000e0108501c15800c0300076051900100041c00030400d0b50045201e506020f003000c800c0d0b00a40100e611881c40c1c556080c2003a8561251120018021140d0400c074501d40100002e4060340c00000d0842e90030709076100c00b000d002801450364255058402c4200c00c0d0020703004500189001d00305010040d2151002000501100c8414422100100c03618010b00b0700c0c00e010603103007845a146801c007030b000a220a407010b261716100c441d80d0b40030f980341c60440b1a20000703585 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 575404712 1250 575403462 575403473
    0xc090605130c1707270e280203040b010302040c030515040b01181d07090b16060609140402030606010c080412050c0d05030c01050c120a150b07060b10030c0207030f 72
    0x2105800782941e51960f25040105008200d04040010408801d14003a254040c0c1c50440000c50100c801c4601214025202c50702e1194501c7c81c06da00103c50b120721916402850000d60020314861402082160710941c03442c010301060760554009441007528180400c00c404a01401110360340e0f40559000601125200041ea031180c2604010b0021005600000450328884107041c0301d0703541c010b605081242c54019054841428034001c0e441a0f26060100e45500d4003c20207031001a80200e01c00302d00303195500590021100d00440142c400c5115008000540c1020424117800060a2804041d407030302c5a00d5a2045000d14040e0840c286021b140c54814048108801c50168600800c072000400c501c1c0390160b0380b43e1009055a4195003490002500ea080d040b05895910503d5410038071a69500e100300b400070300c40562004445148010f010524009407000f405080b44250800928091140100f0101e0000402100c0070142045084174131035501041c82022a50b01c607034220007108103032600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 575405962 1250 575404712 575404727
    0xf2203020613230a0507061b060c0215090a12021605040e01060305030a1701050907050711040912020312010e0606071211030d0c080928060905031201030c090605130c 73
    0x80f40d14041101007044204000300d080d8810900c120100c40c4410758545042d14512503021003644071881808040c030101c0e6040d084079104105510644d001c112418204007110348055039260f40310780c480d450705403c0084100541c2c03042e01180c00140a0040d80700449041e02c0c2860040d94042c94880740020b45011003508120069640201900d48490502000624004420248000304403c09000184501700700c080140a00f0060b6a0a45014001d450f0403501c0c000c2e0120f480c0d0016a0351180001050503e000780210b00d00503806150350b0b2036a6403103a100c4078170603040040c0b9118000240070040d035030a0105d814141e4000e91200b820290001c00341e42031044802d0414990100181950003c4a50352100c1040075032034a8007005515182082c0703954961035910b1400c051180c10000c0414150900e100c2401f511440010a010b0782a03a5040c2c00c50304001c1c4486040d485490051003085418841403000c0c3c8441c840402c8481d1a1000052880c0d0603400080310311a500c003a0842064851002e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 575407212 1250 575405962 575405993
    0x2010e060f0a0b15071a01060e0609060c0a0507270e030a0e0105391f0e12040305060f0912070818030f06040b0a1814150f2203020613 59
    0x90107172900403e04220104120041010404281042c00482c115004900800c08004050005800c0c9065036043c002c0079441084000c856100d901844c41c0007480c01c200c4000500004482c10b0300c0d80754401c01540118041510a0b500c907400c03e0340107a5908400026540254030b240b0b080004401c102005841a20405005400e48010f6860710402d4165140440d195100c8440b030009040207034070800354580c0341c0c50003e213400d26400c0800808007200d5800c0700035841b82c400309403540e4501d92070780081c0a9000d640304680e40c0d0004410050007078051702d14594440c000304003811260b221030848024a1065000c0140080004a0b50b03148200e5004c03030403400280c001d001c841017006901d16990b1340300408c4a0840b2080501800184e040e903080c000c0c00212002910320f4081407005599588030200b01c3c14107810b061156100c98004031404040c0c450082c401d40c030340c014043c100b03184d80c140c1c841510600c40d46c4241046d01060006a0300080d502d500542d00346407201c4202d150700d400800c2040482 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 575408462 1250 575407212 575407249
    0x310200d0b1518010311030a11040b0c070806010b04050603040308071808010203190608190609020406150e04020304030519030624120b0a06050d0b09150102010e060f0a0b 75
    0x440d240c00c101e460002c00e910f41030081e485600901030801142a500d00d41007520f840034003030001c14a00e61480c3c0141c04115602d203285810b041c0c4841e40c0800301d410140c4a9041e0340c1c84181d0400a4000074030009014040a0070317014501424240130440724440a80000d08000426002910583c89182c1d1a600000740310011241d20b03940b500390354003075001690415806640c034004c100f141d042c0d5100380d108451614025203122001502014995500c1c004180c8070182c441d070455005a40e00d114880c0034000308030f2100300000c41d09100811280820034114003a070304c100309000119030094250b40031004207203c030200903010790100f100078140d02c0c1d04c801c801009c0041010385020f481035003030f0f1002400d80d980c0305002082400d1072054500c0c0c2e4403a50340140711050280151440f0740c1c01011303210b80c400c501080b81424080424444001210700018519900001403172541e428003441c020041003600402c02401c0c8040d0030030304100040d0a81011940d621601c14458a62801b010340800c04003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 575409712 1250 575408462 575408479
    0x32d0a0b070507060b01110d030f0f020d0504050d050702031b030a1704060228060902010c12051207050903250807090e011d03030106081305030c0c0310200d0b 70
    0x300701408580241c0012a44c150078000302c41c040c1c1d4844d0070710040000702440100b1190203e000c040d002015101032071701e401da460310f000701303819078060008046c0c083d41c5841c00034181c0b506081490500e51001c04c0c0204002c410081d100241e03500246d402402c0b80802c1044401d060601e00291400d2800305000b003076564801100d04241c50040040c20854000c1d03000c2d20b0821002c00c6012903a6144a41000c0c401d141054101022484642c400c0c800700b407040c104001d446a80342c07900c0c143c00072000b440d400000d40005031881c10200610005402040a0800343d080240e4440002c5d10340c2c02000820050034400c0700e40e0800c0300c5c00075624074010401d40c410350b02c3c20344c0c41e01c0110005e07299500c0703000069801c010304002c0800500401441014140018600f5642008401c480c803443c0075006805100d4482d5a4030007086050000f085107010120040c00e00021140c01e0500f4440800d0000c0540361410600401030319907441450b00c02051021400d40d04c00e40b0b004500c004001d84240140c110001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 575410962 1250 575409712 575409721
    0x20d0302010606140f0714010b030f060105010e180a0e0309060d0608150c040b090105131811030601020a0305031f0f03050105091207080c0106032f032d0a0b 69
    0x198440000d4031100d03502c3c5042c0782c128a100403154454000c41200b171010811054000c00e456001000800100d0400030403008004c4d80040c0c541500031103c1042a0400d80c010021980c21a008000b0104151941d00e251502c07200401003a080080c51f00c40c5840e1551500c0355000c01c14000c5440003d402001c00d0340b241d0140b41e2400041905000e0708116204140b80c208840d00500c41040c49103040c0d500c6940b50a0410030701411030b801c6104483c0c1448428007400154aa1b10710316100944110b028000c000307811400010203481041c00340c1c00200000f0024000e035641d0218200d524250181446682d9842d80d000c0324018500660a1147c01d485d4010081101d081d03418150080701e01a0000344400d444900d085902c82840580d0507081d850100240c0c2c0000b03007c0030280047c400c07950f00028040d075503500c425580031411240d080090f082c60140000f4001080788540d039508042e001000011420036212507680540c0592a510b10005054242240c5080010350000faa100e001c0681c103040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 575412212 1250 575410962 575410967
    0x61305090c070c09020f0313030504090f0209030c0103140705070f02030703050a0516061e180e100e090c041d191a07020616050d050408040603050c040e0408030c07020d03 75
    0x25140450f84105400000214040240251031403424000541e41c82c44e2607041000e075140500341c5080f800d01c50144400100045684100c1298440d030f020056500c04002d402c0600b00b01b40341d4980790500d0f20b0001d061401d00b50b02162290b01040c1814502d96030203187c203050000a8003010b0080d4184290320b408005c0000208038410280d101d0f4045405000e05d9502c1140c0c000c0203800352034001000b0a01d000281c40b401800c043c1808010306001080c000903040290409400d0340052106403042c0082c0324042e41d40010280090890440c013074407500b40b009136503840e0511714040a1090342c51319400c088a2440c00d0310700c0224071154044804402049030568030700301c0342d05000d55030349480e8800c104003802c01c0b11115201d440d165000d030929a0b00c0e880c1036030880e03030f00c00ca08004216092080009064091040c00c2c0907078002c0940030f80f40c6d072600400505480c4000c040c90b06002c02408200179031940e195916410a5003c14826101d42e600240c1c1e10f03e500414001a5000720303c7e8038690107158 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 575413462 1250 575412212 575412217
    0x5070c0f050709050c070f060216050105071106360118030906121a01030f020c01140402091602120a120203010e041110050a051e04060f09091a061305090c 68
    0x10f54400f02030000e96541040040396000e01440502180c1c0b02d400d980340000c0342c41e4000d16401740c242005103290846c9844040c211101251400c000c280d62000c3c40c51450b40130011158404180b4052a4040340e8149060954070010780601082409101140e0402c0c10290022142208440c2e01071507010120300b0020b1104080b03110b02c20204e400038002110060b01b40c043e03003a580001c85414a60509007800440060540720056601144d09114036501076900780101000a004009440210b0170540104507a400c40580803040000c28104440303003458001c02ca0218190310035110940362240700209403041c80603451801c90141c4008004183c074000e03a800c2600460280b021044030030041c10901c031940d940329000001080f81400b160118511880007007032015407040c8284603a01d11a10481010b8100d0740012010600300c070302403607200764410707644002004d00b0340c800e10a0072144061512100554151203000354000101032407600e000b10007100003001c01905490003460841c5044440780c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 575414712 1250 575413462 575413469
    0x50c0a030c0c1205030621030a030f05070c0807030216171e0c0f0301020706090b0405060a1a06180307030813050a030c0b1e03040602070c1d01060305070c0f0507 71
    0x80c90700d00c1d080c07403681c400e80c000d48441c0c0d845004a1400c414107401912075070402800140c0c80303402800c201d84041d46403400000b40d900481e0007546c8400343da00015041e00c3c0c00700001c40c5417528003c200800d2035803080d081013a142e000300e43c9942c3e81000d410f00300e0601c0880106000801c1c1045000681c00d04d035205038003220b040e8001601e0781c2c03141c4021482081c103002c1003030400540c4200d00035a140e141c40722a9841c0c07060001d00040ca070804540d192402c0d00c0091b8003d685c02c00b922400c20040c0301d41444a0341e44003d011904101100490940c2c82c604020b0040250103880007191541e03a01c003600b009113040c5803005003214841d90390381c9040c41d201e41c00540342c580d1066041d10700107014201b4600700c1054a5105180240013400c042c400c0300c044d0051681c400c02d031090030110502083c405030003103004074043c0384003503a038004174201141d142d1115400741c42003580001034a1012600080f0f4207054981c140b034003040545814400b103511140d1a803001d0254180b6801c0c8500308140001c2c0300044 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 575415962 1250 575414712 575414717
    0x1a0402032406100c05060f190905060414060415020706061e0303140f0d020c0c09040c0306050c0901050336011b1107030303020a051315080105090c04091a0301050c0a 73
    0x440079404000c131200c00064100070100e51004000c215a4a8180910b5034481064449503852400007072040040d520480710586c0d9540104082c032040c0302100780d9510034a181e000050a017802d280c5c3e10034003803001f000200c001d5164045a4481004a9500260300501d54100701900b5000100d10640043c03410744404c40200702d070411450320b402912400d81d04807880420030981416050010381d006944151064440c078001c1941c0000f0942c0d5081a850196006045000c2810f007185007902c00c541d006004074102660500c1070044a81c0d00504880d400b40040940f5a58206c00c188000601c0c5c990780c0c030007004e0014041e14544c112005603c01c80b107002511180203490070020703400342c1e01c90701c02480701600b58201240a00100740250010000403030180307002840d0a405001c01d40e81b9048a40200500300c0092407107411300b5070f01003900c5001d0002100c5840c000e080410940d03646100d01d11078007032001d89500c031010322140d401595402602001c1c00030b2040c0e241c109241100342e884011802c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 575417212 1250 575415962 575415979
    0xf06030b1905060d020d050111120106030c0503010f0501030e070936172101030c05030f0c09181905070303080f0412050d0b04060603020913091a0402032406 69
    0x2004069026441c00b03070764040d102d031040c0307813054007130207116041840191915900ea8039000c1015040700d0081c003414108a074480c0c025410800001c040d150a40c52103020010240018000950407a500400302c0b00f003400c00060280818011a05041c0c40c0c2e0b0266207844c0c6081c191000340c210070701c079810608411601180b8002c1035442c1d0b0480c065102c44000c2c010004500b400344c080d2050340010481c5031081cac100452101080c40b60200600409d8004589920381500e0400440c2001c000d01d841c04c03070025016018095255021400c0810020010300c4501c0340380300000160300d018400341020340002c01e4480c070000345608110340d64030303190320048000980913400a480c40a1624a00e8000c0b50b204514806480001d14111101d810422100d10202d564101080071559140f250038000d1035a5200076855558520400c800e03029030f030030180610790410050600080b11203d54038460400009454000d885074004289490a546150300b202120212101d854140324220302c2e00c83e00c0c04448100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 575418462 1250 575417212 575417251
    0x160e1005060408030909060a0801090c090501060509240f0d0605090c0a050d020d0e060708090c0d03020a02040e0712110a060521040228140d0201210f06030b 69
    0x90500c1140318800c2190018081300e51249000301b070494111100401c0183e1260b180c0b1441c0d8215400c40108403481c1c080305100300310348034a034000d0500500042c20158140b013459004a154141c0320b800c2034079008003880503000f0140e403800689005003004440d1a07256544104080014282d03030140c0c41c070403800e034000160a800a00c0445111031080e03620141844038001440e006900a02244c1d8581c5484d0b00800340e0b0220100400d5204091036074904600e424680c080350b09010390442c203103016240000e081c50209070002022034400d5815030303000401542d22001c642c14180c0503000001d42d0440c1c44064000c0c001c40640303c0403611004c4814464035aa20313002960f840c4034034144000d034808080e500500244d21044102d50290004e0424507801c003040a100c0b98080d00300c4070049040c0088901408440c401c1008141d00c084191041070030a50079400190609030401030071044c05102001407032010a054200c0f43e19041c94880c24403c4d5078030391070070f00780070401102c4c9421810200304900c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 575419712 1250 575418462 575418469
    0x30b010e040209130b07121b0c061a1c052109130501060215100e0414070e01060c0b04020d0501050a0606030605091b1315050903011a0f0d0302030c03041d01090e03090111160e1005 79
    0x280e40c188bc010715000d44417101c52025140c88088080503901c40c0100202d03550310b80b02071083e40050080302210542d88203199000c00482401d00940c4881240c9010010300c005500020701c01d250000000022413540d1711b01d410040080d140d500101c01d900303000d8060108020303175005c4072444581900166045540c40784801405104240700b40800500c840700c2c0d001c0460b03411509140c1007400a0030440110f980b5031202400d40c0e00075955581c0303c65542104214155043c403d413800340004903011440760400984e82d0880d5200054240c100720170000e200401e0751400f9000100920010113800640361040170003801d41d40159503098025424095100e80111010518629440c001000c4d0942c840d00d00d81403100118000d4021819880204413510640c001040500300820a60860728090354146040560401040e0b2085642c9810303c2c905035109040801500c0c3e4580d000e02c0c4c158400d507600c2c000c10b0300e03103003290019009801000e000460102c8110761403030300c80e001d9481030510542d521003d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 575420962 1250 575419712 575419751
    0x801060f33030207020102030d0507050d0b0f10200f06040c0b0a120e030409290616020118051206062b020910030b010e040209130b07121b0c06 63
    0xc070000940d07011079010540254080d003400d0340103104403405c0614401007801240c0c0c00b918400042407010a0043c981d041038018840e40c003005640703050868100601203055030031b08040060510036040000120360f080c12283c8100e8403132030b104955a000c0c0b1000c2c51502d4072070698003618411514040418885103007411240082415540d00d21107240000c4002e0040881e254040320310701003084000b0701090107010710040100c040348050015500c105800010039072074041140501030a1128010b02c0d14010280d00d80d6580a00301021032115000203d42040d03200d4010540c00240843c901e003118000150140c0b040300d0940e00741d5201c140440b841c2c070140c4681c036102040c2c10400007401700107052940d0425041110f459104100c26120b5a4060840ca000d80007072801b42041c004200551800116040c0c1041c1510301001e600d0b0200e44502c0c940700d0000702014148407006801c40b4039006142d100e0640707982406254585064056001008880c281500341d0710942072030045410965007141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 575422212 1250 575420962 575421029
    0x204020717070647040f0609050f010308030a0e1e060405010c0912060e0c12030c070f0b0f0702030a120c0b061008010e0a09060501060507020910030804090b0a0801060f 74
    0x3c820003060f01602c2022995000c500a813501d8081c2c00c40c40b103119101c40c020101c60101c80c65021502a041500101c01c07603c00034044151024500010000b0a01031002c580d08117510040114160384094641454064032010200d0030038050b0306c0004020001081c07050140b0300c500000d102c0c5009100341242c00554500682e03401e0349a0403180b40006405d603104505a00c8204103445c07c0c08444000a1005400b9540210031f42d003000610302c071401c6091203114068081d019248402c541003100800050081c040814681c030800101c00041d5030301000100d80319035001703030b40e40180320300c0c024000e10700502400102c66020280e404101c2c0c0d441e02074100503140d41107070b0341c4d224141c0c6806004c09221001a004d1004903588840c502c01040351030160074082c210a032a01d42e80d9001d40d01c144090340900510b0165418003070541803001a295604507400c545001002241d580000000200c800c0256030007122103600e060400141544011140f40468050511044441890820034451011400b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 575423462 1250 575422212 575422271
    0x5061803030c090a0323120a0e01030c02030d050a020a030c02030304052d070608060108090c090609060f03031303061b020607050d0609150302040b04020408120702040207170706 78
    0x400144802c008a024200883d0010000c0002e03035070ba500d80440c416160030703c0f007401c11140682101504020442d50b203500d5401451245844411080140a00e0183c0000ca041646800e400e40c0c040707108005550520010140400250800b070b04410001d51100c11520042414202290925400030003078070302c2035400401402440750480002900e007455100580e96070081c400924002c4002000403102a0016031030725545401e22070005004010001c20300306a82e0700008111620307458580c2d031030b50488800e441c0c0706030300e450b1000060201c02400c00c00640600c40451b20602030a0859070080840307000b900c0c00c021740150441022403001c100d641c0040581c0c40308000c60840b42c41080142810810340b60700003180e40d1905440d20580c1d01c265403035507055860a005105600d018171030b1030030049084604510b01072031b106030707541c541d0b5600e01c0002d40c00c200440c031041036445540407201500d50103100340017050007450361000a40c001e50340a640d00740c81c19188104040c41104090690023580c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 575424712 1250 575423462 575423467
    0x60610050d0e12030a020301030b0c0415140c0a0b010e013813030302011e052403070e10060e040605010e04150321081006050f0a02011b0c05061803 65
    0x804003a0141c002e0300b507400030603c54001c1d40700118407510051406104140c002581e0307949942802000508003420880e007162040008004514200315005040c1e00340d030800d010038080c0482d81c5402800383d00345404190080ba2041c0c400c124080c07800e14140e032912040741030340d40d0722a50421411601c880c00f80d610b2074040203141e00415207041241208401690f40f052400d6013846d12580201050341c400c0b00943c0d19106441c9423240e04402500422521840030051498070038692901000741f201004580c1c3d00703588044210751020320450015000c0c61621030701d207092524090010300031b00d101c0c1000045001c090021070f494580540001c590059441090020b81501040010305510750707100800d4042c50070000024a0007001d8501141e03020900040b1011500d07000340107031500800f0b6201c3d46803420014002d85030805d00b0f644a246005400039211428440240e005046500400c2058492001c07201003d40d0b00504020360340f4455000d48a042e1a0f11310441a680c00105054030160000d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 575425962 1250 575424712 575424727
    0x9030b0c071e08040506040b12150a120201090308040b1b01020a0e09060f04090309081e06150102030c1b0406140310020c01020412051005061e010f030e06070c0506061005 75
    0xa00b494011980c09001c000b483c20b6a0303040021003541c4183d000030f89050002c10303140080d11015111550240014070103011540100c0002000802e2034041c044040700042c50b003505591051198001640e8002100b55903a900c0d03001414040c0c000d2041604104c100211089660380c060080e0341c0d940a42d07495110318004030700d0400007090001001103402240200e4032100c0c607a120b01650400134013079141d454403d13041540040c1040680b0000450705039072480383d86409000000c0f556881050002000115880c2c0c0300103e0070340c410b203107025860f0f20a2900000e0020080324907454501404c590410085a95200c1140c1c100281100c80740c1c10781010f5459a1681490380041040c01c90f03802c001840d0903110310705441480040c90064600b50312082d244030a000c1c5070722446400c48821113500700600390035045848503a00c0503060f82d0410802420300c4841d50300030780003000b00c0c2600c201a1901031400d103000510700c40c0070010545042c424075000c90130900b8245060085c0300d0060b40c0d0f15140801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 575427212 1250 575425962 575426003
    0xa06180c060504080a03120227010e180112030318030801050306010e04050606090a02091504050a080705100c02010c120210110a0c0813090207080d0f0506060a0807110303010609030b0c07 82
    0x56881f00c0e083d039a8082041d1184a1400800101c00344100542281d00b0b10b090b40005045403c04000a03010b4603082c0c0221005200003400c4030f044801c0c0c01d50800050589150440192084c003158083d8994980b03601010150001c4000c0c0c10303104113900f158240da903658400096070605440c060a04c0d00a0004902c6d0f0341821400141c1c8400b11550240ca0161448082008060b01c1d00310100101c801140602071450079819680040101c00b0041803130740d00b03040010303100616141501e428040100b81c0c00046900a60004c41250b030490500c40032500c0c0440081d459092000910075094980440311a00108071002e5416502d000c0c0d4400f4400314141d6242001540704c044080c80c1d5001e020000101010280011311050f0320032400c2540362045410344000351032200a43d100c2c0181040208541e0362a60400c0d94806480c038074004c0050b84500c2001c1c1c0302270301c000146041c14080000041140740e0400000402c89100b064120255034443c0c071201041c2c040c24000170048070100351290745211 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 575428462 1250 575427212 575427227
    0x417010e0a0f020d142a060702030715032d180b0606070602070605280c0807030207260c0c1f031113090605090a15170a06180c060504080a03 62
    0x18441c2e201122109043c100b11031516291480710342140e4015440e5611206d10044a401e04650a442e21800c200791540000d0b11043d041c080e008100c4000d414500c02c19210790004814034420250444080c2c40c000c0148850008c1c15030303031040050501c1245c401804001881d103152130b801c42454101d41d01c0303041c00c01400b503100070400c2c1c0c1c8850b0244400b90105440e84502401b4031610000541050f0b038050309011041c1a01560800252901c07580c40c40740d40d000000142c0c4008039240040c0d40e040c1a19102400c00a00240002c2509000400d281c900d02034100904407801d000d401c480c900d948075000c002c0b500000401d0b80070016a60103200501c00d0103034209404405400d90721341c1c1400302c21190600c00e21440d42c0142c280949030382d410809030a041800c035402c00d11800007031066030b44141050245481501c6034a500940030002c2802c2c1100c1404207c0d0225400701c070a01440d2400384090310b40d211a08030035100688001d00c00905140560b003140c0403500003001400603581252020b07190320 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 575429712 1250 575428462 575428489
    0x3061810031202100c320d050112110307230a1d010e010b0901020a1407030506160f0302280210020703080907092c070e0c070501110301080a0807020a0b0417010e0a0f02 74
    0x49001f40805c00b0004458080c60f0701804079925524541c2180e4141300c907d1031404a403e030f029070020303403091007601043c2101103841d8600300b80008180180d5404902e561505034801c0c41d040c0c020121504106210003a02c90480303c0d481517405a998a40120450510a50340141e0260384215504400030f40740e1180002880324100036100401e64030303126613013022412280802130004600c401a069a0030211024444002d8501141417804c002d10110700a1908800d801208403003250078403041e407003040030b00000607074044150349916092401400d0303031100f40e5960303410740250768007c504003040d8800c072401401b03100096407801c0001c400d80b640f11032030880360000340d0150040c04190040a24032441c019010744601a9480d9420f080180c02c4945c41d1440c0c82d80603508100420105400158241c3c01c1c81d0456045a5550921310000e0b4400015500c00c2d00162804100001c15140200c0c0d854100002031000340a00e03904050300b04d841d5023030508024a0090700408800140c00d020340484c801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 575430962 1250 575429712 575429807
    0xc0705010c1b03150509070509010b09120304080109021806060f0c070f03030c1208150112021b1e06070c1103010b040e0c03010c0503061810031202100c 67
    0x1410019030003080941d402e9082550a00c50400007910a040944191580030030910060107425013040005401064107100c0c059503040c000c100c0b08025074545072910482c400d1401200d684a554400e110b010b0007048400b83d2250380e1151202c03121f8001d1503510751107040c009005510304071000b40180129080302c502120710380300301100031480040010490700030b14001d4035072402c802254070303007041e0050518a041c420030241c0b0013030043c0c4100c1400741e255440702c2400c5c12080e61040e42c00ba10001c2c000d041c5000080719030249243c000c4903000c5204000001c0e201010350b40303021450411030380c4030401c2e070388003000814000200300400e200400300c00700100020008178a40190070005410360300b03421810419608010680a0249003d1084041300a007606080b8190f26003030000480302584203030885039076040400050280500143c81034040c2d980640e40e80607030071040500a58800340c4802c40106a440d2440c03540829000f80b0340c40d50b02000c1707007294140c54801d540000070100c4004900c1d841 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 575432212 1250 575430962 575430983
    0x1002210310120c03051906051602060105041a03190c0614040909060f0c081005030d142101121703061c0c2105100e0a0308040f020406180f020c0705010c 67
    0x15400344400c08421038040c03403908240fa01807d2402c211a40034091031540b0010701c0c0c86420a640100d8160304480781224000f86091311003d4002c082c030307582c591441c3d06016004c1c0d0128942d90b1840d900010a001b04940042d541d125a0190780505c480c0f9480600030300c040c0030400c80903c094102510a9110b0b15000c00e490184454000650703011090140100d0341c034404018668034848035410041c84210000c080c002e48840016249a051100d095180c220005000c00119590015051054000404500150b95540311b54400c03031030307400e412507541c025000307400d1504000c207003500d005074001450541d61103429100410749181d4094101d9074018285400200a48594003030040d5402c0d9a030103d5126003549081800e08000c0300188814901d001c80907030004d5000036149141580c181020301c5c080d00c075400c1c42c8100301886c0500a50160902d8000b01d000c480c4400088102c01b00c84100784042988103001d1802e034080e507500100107500004041145602c58480c902001c0c0c02248141e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 575433462 1250 575432212 575432219
    0x3b1c080a09170604020f0a1805131a10050301140a0203100906080c01031b0e060a030204270b0f01050d151502010b0a09060b0301060507020f1002210310120c 69
    0x203600803690030401c000d82c200c1d004104c15401d01513000c1d4170440003107821862460030141e402c1d00c3c03442d07881042d000680c0da81000983c00125409495032068000084002c0008031042020384103a0440c2c4e90040c10035042000030f0282014010041c0300d0b080e142c5d40161658841114200030741004000342d0b4424030380500024502a07d1041001822041c400391021103840c0001600b035030200f0944002140d00100d0322180903a00038203100a000d4111152a96031a0101c0e00714041c2c0203607001858a17080d142d01c001c4100ba45100c00f43c1d0081c806420174418031102c00200b1000256203900d440c0400c10800642030964440e5100e91030015003180055034460b243c0c4e004003111680c2c507070b255015039910500b02c1058582096900300900451005010460524801062900062264000380003003c1013890031540c9a550a00d0280c50180290b0501c0e209030304020351312481000b10112060341c1345030410440803100104c920850b0b00082c07080f0b503a840c1034403817215690088800c0d03403007810402000c0f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 575434712 1250 575433462 575433479
    0x120b0601030e210901020d02120d0e0a120504090c020102070b040b1e0a0501080c0a1802090f060c100b04110909060612091011090913033b1c080a09 65
    0x80700f038500e010800a40b9500107000180c606203c0c01008402d540c440440c03002c0c13071030681040310580500c01d07201056924046000d5403911002407001040c007020b1139550b20f4a00d40c8040600101d071408481803090343c80b220030036405c070701c50800040c0c031040ca0174000401143c101083d05070003a03800b500c411110b03501100002190181990030f00390f00c0b0b071107600410000c03808024401045c1011614450b40301c2c0b84c10f90300b030341c1280340600a40d02181c012485040541d582425405c0c102c1015180070790b6200f890341d8258881701e0301315100c26100d1520a04074182d061900c62507d44042c400301c1a0300d0402910200b02100000800456025a0401c600d50400e83c40030401801240290004e050a201c90311001094690103066000213030b0f01031000c4043e42d504d070b0500300d41082c2c0342c8076489854001e60a00315a480103014541c3c0080c03440e003041e01418059910903005101e076008411600031150010030000d01a8403030000e003660070708940703c0c0100f901c0a00170040c00032103040038840d0980c0d4203001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 575435962 1250 575434712 575434753
    0x4050a030c050c0d08120a06150c031e0c03090605090612060a03020402070c0e0906190b2803110d05071502010b040c17130305031801060f0f050a120b0601030e 70
    0x446040f6000f003240042102a00210360701f0074644030013808424107100c030b11621901c40c100039004010261007000181030084403800400c00d013104a2150001810402a240300a44c1c4803c9000582c0b0400c001403c92082c42a640000d100070485481c202e101401c1040e8108083c081950200780401d0020040c0d0f100c0c03004141032032044038031380c1c446460180d211000d40e400802841e05500100204051844170010b41805c070607078071a0008103510b6040200b0700d17480d2505840741d8000c590008940c0e59035002d002000441c0d00c100d6100c00b03401c240d03c06102454880800003840e03607001e190103122790500341c0f20145940c1c005100005045080740f001600390740b03605208402040070750403210030030340031501a0350f8460035142c05400460300301d5500509512008100003000c44508014840d43c01c0b00b134126600500460900075182071703c4194843c0e4032031043c414140f2826450708002010b007000844540600c4d000040c0745643c0e5181d01c0150050400c100f506012805000c00190058000526 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 575437212 1250 575435962 575435989
    0xb0f09150414030d0206090309060304111002031909051c17160b090303040f0303151806170d020714041b210213051011030f0d1404050a030c050c 64
    0x36464405102c94241070801010008103000c40d0410020440100400000c440c421a42078411641c0c079034460400018612000791103582c00011940f51090156002000c2d224101d00c1104421100782404415108020a4483c03a5041401503402c050565412034401c80101c2c00750b0203c070070904424241003503d03488980c68920900d0200040014080860384556000c00144000c40c61400c207500c03418010000d07038000408054403406080201c0b00f00b96918030040c407121140ca411250f00803c0c1c84081d016070b010382003084031241c40d00302001348001030b070811841c1c0b5a006809254203060061460707035130040c1c07082d8125403903900c0160f268101092000b25115181c0d038000400c25503401000b40100304911504025005020b4a60130303c0d414481c050480c1c404030bc1010004800140940b450f031001810920f05000100714240c0303421503400101103c1e039283c0c02c100304070380c0c16541a82140c002a00c01408075030207202c031400064016107100c1c6405004d0b0088469100c6100700050410382c6208 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 575438462 1250 575437212 575437229
    0x702190507030c0b031312021906050906060303070c03031803080408060a050615090103020d090c060c12080103110405090a0501020307030207021318081b340b0f091504 74
    0x4004106003d1504103000207020003130026465414583c89113414100c00100103458007110403403080a85000b08814040d102190205044420f0380703040c100002c240c11038014030346008580010f806031802100f101e803100e502041103130450f415034504481e8400c074450229003921000201101044508003c2c3c0014400c02c0010102480d16203901c0060307410151510740101c5004c040520302540580543d41c12400a290060721400e80c004ca00001d4001d040340503094451030580450100e51202240d101c40e0700030602070310017410302001165101000d100c05024004c0c008850700e03a03031405030030aa801140403021a8000f500c2ca84070242280c0c42a070300d050100741c0c0024003004500b44200c111407945083c0d0410448604000301c500010307100c00b20014091100015144001080c03400b00710071414184044030314020030405035002042c0c4a52400320391240d080001320301c42c241c04651105455030f091580342048201c1ca6150455002503520170350104002401003104682070020700014a52607 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 575439712 1250 575438462 575438473
    0x71806150206242e0309020609040b0109030b1f06020c013c021608010b0a030b04170301060e0f06160b0a06181a0a0e040305031e0f071e0804020907021905 68
    0x80c0c1c50304c045a420400c6a809041c100710085015a82d140140c8207040400d03100844d10100034001250000b0342500001c1a443c6000240001c04070002018085102000b203090f11440d03c89005a07603801d10660b0a038001002d1201d10084c4482c02d20046500e0828204002c15180c015440d480038541104103280050f070010000001007007626460304c2c014400b50f402004403a1415000ca41c6a04030340c040a001e0086120220703040000c003074150b51404c1d020941c540e440396100c00008042d112a038031407d101e440440000580c0f840c1100850303081c2d0540540d542c2e41d0621541e5089401840200703030106440e0f4403100041c006d262207402c0001170070440c0000481514038601e0a40304661800110b01810040030300f800000b2103030990580042c2c15061a5480e07644510005043d65400041a40e40d41d00240601000c02c40052030503000d60f526031103006201001c02205030a107107000301c0c800c00140840c1c0110b40503050408040b9004103481c0b0550b0825906107081031419840d94078100c0b200d0f03010 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 575440962 1250 575439712 575439769
    0x450409021f03110717090109080a0b06030706030212040b22060603140d0801230604030f0204141b03131b0f0e0708070e03010603020307180615020624 66
    0x41c0f241d0000340c80301e41e0320f190600050b030b00c40c110303030a04081d01c00c41034440c001784180c8142e00984828000300111001c95000040c240361152807031009851b228024480d880c400720704207029009a507564030141e906480360395036030745646803c01c2c00548280070f0440b038000c0400c454801c0d0005862030501415000c0b50103891407078050403060320502442c0b041e8000710504030b0440c0d404920241180c0340f82d02e802e4014512040d1035041d20114100e41640110000360020801003507a81c90403000340219070170068010f0803001c80240100440300905028461255802080c01d070300051500301100310100c030082212a039401c484180d401ca4000d11008681c08108900c55a10440c2e80c0034005800d1600424108000050302c8145c018054005011041c5407180c0107880940c01000156002401c407140d503030307941c2c90812042e241c5510bc011682c0c200000800c10707034425000502d511031594028442079840c0c0320440041b58951804d8620700d08024a504d07111f41e143c04018044010706214031a10210 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 575442212 1250 575440962 575440967
    0xd0b06030c04080c040207111905100f02060601030c08011208040315060314070510050d020d05150a050a0b1813050708061c0213051e040503450409021f 67
    0x4c0c003840584658010000400007410b840051070740944140c805001500203c0b030040c0e8011000d402040d0810400a00c1006466002004070711b00e480540a549440d101e09004506590354200d9042c08101e4042c01080243c02289159506030300801038513013023a0300c90380c51100003110301c0f107080441900e0301c8040c0b00744802950703c80081044070000b000c04600d0900400c2c0c0205004840070b0a201020440f06a002c00b0380e012102a0700d00107608200b21b18004003040c4541112561072401640d00740001718260410006440c182c07110306821600f401002c070302e1829294070003040340350805d4080d8400803d00ca403a01806006110369140d007280c514045047c002c0700442c002000000e910703135080c00030258903104031440c1c6140480c003022907a640d840190010710b007088080c001650310b03084100024000e0100c082c100320442001640100c000701240a01c1e0610b04040000034503400c1d41d00c0d9840d02550030441ea0140c01d010340041040c508540005680e485a101d8050395030072481c0d20314031402e5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 575443462 1250 575442212 575442223
    0x60f0207120503103c0305060c0408210c07030309050906090606030f040302011b02070e010e09060c0c0c1c0b090601141e06030403050a0905010503070c080d0b06030c0408 75
    0x9024900b003802c5103000d80c14122a15420300c214041803000e0846018144089107a041d9824506141e00745040c0002112a224160f50b1000b0b036a64040d000c003003540c160f0028100e804840ea06001003540b440e061040d89204030f5186040c0061a20411031004c01c0302090000e20010340c080d44402c00158035100034004502c0c0c2c02048107200d50428820002c00b5600c3c05c1c10703690400241210b090710361340c0301d00d02640100580040b401214040d0540400c005070700294a00c00d035813460380d01e044140d03642d240042c130100081c0e840070800e4002c00b000680c0241b2102c050058500080c0c100d0b042a14040d01240e0700d0440903441401c0c441c0e0131000351060140c032650903500b00026000030042980741003018614070000c42c09861080021070008401060300007041701640031f00030042030f5241001d15002c1c025a120306501004540001ca000400c1d42c040d00690384543c0e1142c45000f050b01c41a620f081c500d501c5400030354542c136074850501c0a82c0c0c071654095031240701100f02c031030360f1541070285891811 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 575444712 1250 575443462 575443493
    0x40c12060f0e0103030e0d0b010f05150403170706060b030c030603010c0e0604090902040902100804020a090b010e0907032903010b04200a02101a0405010b09090118020403060f0207 79
    0x1051a1808101610107402d20354116134141c076107903415504140010340c099800c8000500500a030100226003001c060340b05c04101c071800ca440d001c1c3c02c0350740e01d855201c038000d911010b0448080c1c20000d02401c5507000c0204041403080200250058603880f00d600290401d4038806032200d004010404507084c00d1146594146c19814460554140d050000701580310324001d50907119100c40030711045440daa00400542c507401408040700300100e481c02401d4400c1110140c1c41007030201c0380043c1e0a42c2034400d1011007841a03541a246003100403e102c80d5060181050040660305c8a1949070b0107034492042c0180d1400f00c019046210340ca50401d130030342e078002e0103062140d85000410300e0b0314100b81d520103c0c3c40e6450700311030351210044c45060341031a100001000204c3d0415066000f920013041c607035551640114ad04204a07601d0703030b0190402d0b0161200007900841d19100503c035410500b103030304c40e13501e141c40c0c2e01514013916551400280c82c0715400b40411a50041800010442c140c008032884 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 575445962 1250 575444712 575444729
    0x209090a0b01090f0e011e230610110a0f150c0c06151505071a0403020a0308040c0b0a050d0b0f01050d0c020109210210230603070302040c1206 63
    0x40c03221907154015036840621400b034a20b691034811a200c0f019541103c52802002d8000700003400103600741914010020030030220407464004002c1d558007650482d640c0540903007040c90481c2d9201c0c4240000f0828464409041c043c0100c581d003042e0f0010441440054407903035070a0703001545881d00d46504241007010b40c81b0281003200300e030303c001da200018001194101c0c0001c100440380610b03a14012032a40c2106809500241503800e84c960000024680544100c181e60114020f642c07505100385015500180182c03c0f803019440840c1c0700e006841c1d0800d0161402c040b400ba074901980300564484100070f4003007840071900301c031101c281d44100704100740c0a41d02b058040b4114000208944146215801c5d90340e55801c00343e1249100358469442030398001ca0b01e07181c0d4805441076001c0c1c2d0111004d058010701c621840c650340b02c81c05003e00130950302c0d00c50510308900305005014076a0300000f00640c0d0148140c05001001d1380e29801203000c0f003005030711101d070b401c40c03e044010195242c0d038000103030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 575447212 1250 575445962 575445973
    0x322020409060b09390706020c0313090603020a030201030e0c09070f020c0901050f010f021204060302040e06042c150403260f07050a0c1b080717120a02100c030504020909 75
    0x3180300b40c0d514607540817044d00300c00380c9035480141050529004082e0050715440c40460254110007000009084075000004802d14850740c401800d4180c515501000b500070655610400040d40680c0003c0001c003283ca003954042012040801c032182800c45070030b400100c1ea1007031001000e40502ca04039244505982030112981024003007800114026040ba040055260311071b828140b0a00400010440000c03440f50303900d944807402800794009010b040c0c40710803000003241e07040c074061040250a200d0b03841d900d804c061204810520020650429110901a00600d1194281d280600910461294580c100502909458042c40b201c080069228204000d410300418220425096601009619020390348083e180b0b0111040d40c4000c0300102100d1454501c200c0c56244850b00c0001d6410400c01c445105560302d55102d010b403040b12440c030440d003251516041404401000384a14000e5004403585000d11a28207421038100c5540800003a5a0f041400110315080f61030030f8020341c001c001013a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 575448462 1250 575447212 575447251
    0xa05040e072d1d0a0522060308071205090a0b130305061e0c030405030906070201261b090f1e090a050a110a0e0111100e2b02030322020409060b09 64
    0x7504d00240340141442103084c0f000380010300c60504210a0505410142407002d556a4906520160400301080318440a410b01e0020031621031001e80b00b02602c02442c0c0b12107a454028011113650095080514080903184040041030081003454004c550300714112083c071007014450290380401408903402018100b040c070001c50000019506200d004542007603807900144010303a2040ca082c0309828816200840c0304080c01c0c060002c0358840c8108413039642101e4401d4207602494401c0f02c8656a03c00707100a801603180c1400c02400d81d403494800340c075028411404001441c200303c202d850361216503c030b8080140312881801801e0081040b018080c1c14480504070103010847d151119604000c1900c00c010a03118081042c56209130f007440d02008010704c9e0f01e50194031b800404806580705007904440085d050342040d04800000980d501075802c40d160f01d100300118000c8599140c40740c000702d550b00700140e521340c401c00c01c840d80314090000c0c5000b000010b10000c03810003000ea000c00074000c000203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 575449712 1250 575448462 575448469
    0x191503060e0304030c0e090709090b06010e010e01120f0e010e0d1710030803100b160c15020604080c0a0507060305220c06030b13050f06030f01020a05040e072d1d 71
    0xc0c015586900140fa4140d40c9104515103041c8c0e080d88000c1c1c9040c207049040e02401050003015004500c01e80e00e091010004200640e011140d81e14041d00062414810000d0180b0560000503144100c0d40c0200e05100312004907801d440000810307440e103800c500265119030750040b2440f560608640c4140c0398510340302c01403800d00c101e580b101400700d00000000031500e42d11940000094a1754440c09070320f031514003082c2c40202103030010490b0450300c5d0020126003401407242c0c18001450381d500a20301640c45a41e02043c0d500030700d5224041c0e200362060030340050002e000700c07030180556a400240302c2c64842d0344545110000c901c00e01d6500303955030004001c6180c80000c00300781c40b01c604000c68820810400709004011924092403103d280c18184419504094003290061030100e0803229500c20020085081784145407007000420810001004040c0701c040c50180d00482d5800c0500c404c4206000b40307000c4003c0031104001100100343d495102c15044441c80303a8421801960f03420300c03038171880030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 575450962 1250 575449712 575449733
    0xe0601030908070c0f0f060302030402060306010c03020a151e0b0d060e03070b18010605060f03060108070c050102032511100209060c0f0d0818060609191503060e030403 74
    0x1418101a2200c00c44424044000200e0352941d0740882d407034600560b41c9140e006000d80c1400f514040d011041800564144240280ca010340d03001001c0c1072540d00e40740c00543e02da142e100c00880940c026425400c1c04200403841e200240d02c0da0000107d00c400c0c101035154000e044440b0050b000600d0441c110180b130311420410014594442400a07500c40c00051903480c501071401c0c01081750041c041040030161140140c01d200d035078400001e100e00e50b00c07041017200c070303015194101000304002c0c4001620303580b0940b007943c1c11582c9401d00381c40e034400c541c0301e550036a8001c860304080400c41019003940c10b000301754040118451858400300d4894942800d03501c1d42c4030400240c214030b40108031003401ea95854220340c6610344003011154044140000ca944912070610140b020030040c00020700000a141c241420410020005e8449d59079004108100c1c0707880a400d4141c0d1840da1190a000c2101038403401180200190707035503140900e546001ea096402080d08249a90001e0204100059003241c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 575452212 1250 575450962 575450971
    0x1409042903010b0d1a0c0d020d061e030b04150f050c0705071403030406110f01061707060c0c03020105030a27050717060f0a020702030102030103060b04140903030a09031b0302060118060e 82
    0x405d800c817600c45052030451030181ca0900f4140b04c0c4002941048a0103039409002128856141e14582001e24080d14070880300707600c00a001658800001400242503000303507106080d26000c0010700b01111010081220000c444a25070303401d0000d45141402420003160004000356880b000240400c1d40100340c03280198800c103020b0008500105005a1091100310210005000200111507555500c550045868289a0b010703010b0b105010685520501061003203603009015651a14919801100c050b40000c1a81450980d1264046404200803144542d00c00c007420f00c0d09444092401e000b4100152580300c00d20020603120740440700c02c0041b4041d98070941c41c0620104aa0f160100c46000c1d1045840c000e40c5944000000710801405600c40f40a4490903a0200039800000c00001e800c80300c2901c1038205944280b0003d55401e0b42500000400e40c402d1821103940040200c4180003002c00c40ba0440140e0400c43c0107000e86240400003d0148400000a00420346895900080d501004c0c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 575453462 1250 575452212 575452253
    0x40e0c0d0c031a01030c0e01120f0303020d050f0106030c0203180405090f010e0607080105032b0c0804030f03020f060412050a11061501021902011409042903010b0d 72
    0x803946014410075121080046400112104181c00050706030000348100340401c480201543e980417a41d00c0c500341c00c15041e217811088442909401c1e44030060f074001c003400100e040640070010140709244ca4040c00e80219001e652a80741941840006420340789403069030350071507005000e0f403286006062000b4119210942d070002d55925610740480c10000d03400c003c00107075800c045000e00f900b00001615072181038165034600e2180d80b0340081503100d8030384280d568001090700134004050303041078a9400301040d0718104000d54030441e0703940c908550450341c415110a00d54000e10024141c041c030050b0f1400c1d800402404661078161396480502c41e01d068618100700c404104091543d00610ba8940101002001c50304a480d11880c2070064556003e0b15600500568601400451041e2861050658141c54074940c1b011a40503004507034010094aaa01030f4030b649050030140c0c40d208a80d041c203804881c181107a0b00101040c1800c2d40e1041a0440c056110702042c200403400b00140c40300c40d0305204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 575454712 1250 575453462 575453479
    0x2190b13050123010302030d1e0f050d0e0102090f0a031e050a020612090c091006030e1507120b090105090c030601030b0415091b0c0f0302030705100501050f040e0c 72
    0x14101180142940e00c4543c005840d0000c02248468020000c0d6049a20032000c49000542d030705030403900030541e081c041038810099181c89110502a034010308480d1310901d0b02508108400000009442128405c00001e9600240c29060380c00c0154602c00100c00590b810108203180d552060010003d40382c44603800c0c50402240701c1005001d004111496400400d0b1a48914980440160801040e54103040030700c5203401280f05802d08100d143d12689140040501d103900e02001540540381c1840e0144248c040d000703041103584080742115008010b6030745c40214031101c4400010841d240c400034203220303e0320080100309aa540700d002c40d5001d440076200c5030300da40780d000c01a03001c0c1c620007021980c042e041a0003404000f092054032822120690801d20000c01070740794404929805001c540d0026850b0f0054401080e150841c070040c062003841128502010303610390500b4518031a49081c001c40e00e80004000d907251141004045940c05c44080200111007421507550712540703440b20b4000c9404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 575455962 1250 575454712 575454751
    0xf010f05010c050703020a09020a030c030e0627010e0d09062102071b09021c0203040519150213061d0d03200f060a050906010303080105210a0f0302190b 67
    0x84c016135004560103450444240d4a074100407020b5001611031134000f03440e10100300030840c42406500c2c10000c84901038203482d11140b01405074610001e141c1c1c829241d1201001482d07000910031207101309494000f4002040c0074100c018180c0030264026001c003c8440724040795080d6505203044c070340081d0000160746003c07038684045035100b0305412000c4083c61500c0044c4020560700201400d04200c60300c414108a00d010b41d02c200d01040d10060816400000500b4082400003e01b511080c003400b151391080958904017416a4000c00500040f40c1c5102000c014517a04a10b008002c0d081101c240d4404851036008108078034407aa40c0642001025182c0c698410030030141c0058a071035050603141c5080504440355901e0406450f0b682081f4946800150f1040340410854162580f60f901c0e102d40782d00c4c000030040c00640501401650b525012200056502c0c00c0240d202560320800c240216409a4113010342050261420032410503000703400305002610740c504096001c0c0d030190580441230314 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 575457212 1250 575455962 575455973
    0x150a020d0e150a020606150f070f0503090d03030b01080a0606170c04050a090501030c1e0b030c090405010311121612060605210c0301020a0806041a101101050f010f05010c 75
    0x400d480b85490004001900d0040140d0210300320744105400d51701e000d003a240c51a400100e51240d14101350045800b0311044000540310008049180e005604690030300f6070400004032095102c0008070701083d5680075120300c558101609991045c0a450b0030004070703107018805020110350300c42c0000445100c0e40008e14800c0c854003681d028001c040c08104c1d8503610380b22040001d00d400c0c00243d0f030700b00785408001901c903450005072241c0d040c85400580020724020002c0d02036000030f420140d07810018000802141c6561003072034001c2d0700401290707080340750407010302166181151001000303410540068070040c1100d500e2200300e034401c0003001c01e0000c850a0000c02000300c0d407c6185d1206400710208020a41c820507003658658000c01e80d03c0e03440c140403c15080340308510003000410384181c001788041c03900c0c1c0d01560100c4060505031441f0030b03960001501d0407042499030004a05000c3d484800340000344942e41e800b2220014000d2154100100030042c0503462203980c2c100315140701042c04020b0b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 575458462 1250 575457212 575457229
    0x32e060510360906050f15040e130b071205070801150f050705030301150f0203070c06030b030109060e030c070f0503030d05100909050a1a10030813120809150a020d0e 73
    0x280c1c0242061500e0b2540032250191540b0f02c61580718070f80380760700c03000d03949881141121f9038048412a18941803520b41e0000c91454014202c07500034000c403c0c188045038020505d2031107070080d992181c0c1e00c650118020f104552020b0100c1c800c0180d0840103001c030a1561000c82c41c5e0781d4440c14014982401520111154840d4a10003003c0b0f00003c400000c0301d0f80004c181c1001742081d9241c0300031000941328100d03076900410102074440040840c1c2041002d000b6801040003e40103000440c2c045e207a070b240c42c400c2d11b51445181100d0360000500f0601294280b042002410308511400502440c10000a40c0ca0090f0052100290340e0350022441074040003000c407009040c1414207000041c09810a5500c1c0d0280f04020348042c1484c5002000150400d0032292145c00800d8502e4401425910b84004503048801d0442c404084880b01103800d9800760140140039100e41d12150340c414124051101d401800b06480c0b40b03071001407103200c0304990045110b03d5000c040d898402417801018001403801d9 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 575459712 1250 575458462 575458547
    0x20f0c010603050a110306100603181e030801140d02060c15010b070b07030b1c020f040f09170903030d0c09171e0c0609010e032e060510 60
    0x2580703410000010400d01146038400103000c0c81e42100c8985004051645501e812117029401030348203c02808210b01030351190f019100401090324412030550303101c11600901550f0308000c581031849070b1080580c000415409080d449843c0300308000000089100d0b00d03441c04009200d80300c00300e040d00780180c4c2000010014141e0100748004d650f984c0d400120781e540300c10030640d14070520400054019005e400f0701d886442002d0502010340b0b030300e024118850b030003498040b0b070b00040d9410f40d582141d03901d01910b2010101c2d480d00040003409442e0410054810301c00010500300d003480f48510b56a0007000b40c80c42442c00d00d401040c08038864a080700c0c0030380703640c1090110602c0c06480311503202001843c2c00d82807040350ba074509240442c0e41c0e22555100d41808280c0c2c0310b08100450413141d44100c0b4064029107000d001c03900858a01c00040c4101d02e00364a041400b5803c1e81c030520114203140c05000018a41540c0107148041401002000508500c44c0a860b00024078840c0380105042030381030404 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 575460962 1250 575459712 575459737
    0xa050f0904020420040e090102040501080708090a080a0e030f121b030c070b070605100f17030910020a030f0f0806040902060d0e0313140d110105040314060103151e020f 74
    0x941c2a07104513130058110340a110041008000003c0e80100e0501c05c540640714140c6602c40340d0b40e24007400710742540005158801ca030040c4041040003461250161003031403040e4070b844c038002540000381443c0400f4818106002c1d485004000844032910040b6000c0e90138078110f540b01110000e003818954803515240f402a13110708100000c0191115015000c12845003109200c2e5494031921158054018020040c8a246107142042145226507200107141000010750f0300300383c5c0b0240012002110500e0a0025030045c070340c900f08042c3d1014000213041c4090501034440700078180c0041c205440105a03900aa641c0d0b171283d0199980d52040e629207255403c805d03c40004005c00c501d44039044500d0811019a039854041407a1082100b4619403020152a080740b9135500d48665801e503096051080c14848200804808142105641318034041030100801003945149802c1303003c68256140006003515010300c81202c1010800201d0710241c0e0aa40983c0b5466050324120541c450011002d01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 575462212 1250 575460962 575461001
    0x10f02011104051c0f0b180102070203151305161d01180906093f08130201030908030103050307300c0203250306051b0304031103120718050a050f09040204 68
    0x800c42c40030303006c9101d40d021001810030301000700d440d079080c0d02890b80000d5040e00480d00d2840c859a803003c20300e0344030640300e039120b0420341c5d25100c03581004611842c0503044501c0e80d106001028043c1801002c0f4610840c140d00e003503141420040e41d00010041151440b600c80d44940103028040d08102001608401002c80e106080224003e80c03c410500d10441424452290354000c0d0681c02401c03041402e40d11032150640d10079449200c1c02c2c4441408030305051341c80c0c251101145451002c0c502a5201d0b800840e910321082c10b2843c6109200300441038100d200c071040c4680340c00842c0849410751658148015020070a00c00a81019010b0901100381042c10725003032200300304030400d40300700c03402a0404c002a46a492462841035407084101020980402c0400d00092203811001c0901c0203640549080c07040240c003680b0301e0174098580c800003c0f050300030041c0901245905000a1100301d407440d0a6615200121705c9100c02c0c48a440d1003401002c001038155142c9800c103121082c00389403400c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 575463462 1250 575462212 575462243
    0x7020a080f031009020307020a080c07081905100603020d020904061e140a110306060307031e06080f0c03060118090204060b0304120e030a02060c030d0c030b010f02011104051c 77
    0x505500b045580f400340e1070091000148aa102e0300c02c40307000d0f01d640e48c041d01c18074a5a4642e0203859000030005c02881c40b0b01d413030005074941c007800903105400d00e00307070001610703551410300601d046501b01c0c40200f841c3c82c1410030001a40d038481d10916044e41903592a82c5580e0324100903000f4034070200c5800650388081c0b41800020026400402254a8450300d118151a0000100c00729944540082282d240410118010345056409140c1c0720005140c00700e80c9641d5400010f8075012010781c1c0d0746a094a5220030f0210b0b25003400922006410140100364100410b40029504c1a06100c2d681682144080814141e5080d4002c0101030b50090001c2c00026542d507142c0c8525401141c09541d180c06540390340c07481d540300751020b1008003401001080d1242070780d001c10440798020030200d0b074030344800c100f446505040d501034605001016140003a2000701400003400280050a4030011a45822030203c4000d1040c010b9409131041a02d4444841c0ca01c1d04100041112007000a003204a07100c4100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 575464712 1250 575463462 575463487
    0x1e1005040809031513140307050a0c0f050402120a0e0708030c07030b0702061009270c03050106080c011b020609091503010b0109080c3001020705010509030313030807020a08 76
    0x81071454015012a5204e5407241001c04a050081e1a4008a1045c0e00410404255103541d807402140010040d00d01d02001c0b5981c0d54a00031044004507500071300d460041002d424001c88100c018002910103500d0202500304610040c1c60043c510300e039482e034803281c4d807129081c10800d0002812403841107076503903c85002c082e551011107206c00c407501c045c1e610000f0949032002c0350f440d02039281145001086403c10410070080c01c41510148210101c0f040c2e01d41a100c041410711040074000c41d4004030850440c10110f09403109a00101002e60000c03543c92000e0343d000046102c0300c800004010415000307480000c070217200380c044443e444824482440b0070f0403e81500c0c030b0a0714070114020001110144010b540001c501d108141c51601329510200f00e034104401d13000e0820040b40010307400440081c0700c0101415808604d0801a036000c1100010042c0074800d40c0e402c5070702c0400541c15442c5c824041d851031403480c04004c040220b100c01051406000300080352817940d000390117945501504802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 575465962 1250 575464712 575464717
    0xe07051008090f0a051207051c05071101050a090311150a050a020d021507110a0212030a14040e040f061512030e0405010b090409140102040f18020c1e10050408 70
    0xb2030946004894510840c5600010300b2012580d00c90042c2c040507032040d100e81c0c016000b820040d1403030f0088001d030440c0000d820b84004030109098541c16100c090b6418200c0a29030540c002906010003005002c822a8000100c0e10480354021859000404600d020821240314840500b1241d0004202d4840e40341d040409801c00740d049038200c54805070726140880e40d591b001600d002c000301c0b441c1c0124181314820680b10280304181c804541d40250070740d0224001600003e503402c2690004074590980c03d42c4051541400140203500604141c05d100124030801c10152000b030800550260f031900b04241500300d130760746c0e00c0c500184040302c564862009120341d41d2014101d00040404200703e1241c90180325031810780318191559410f04480f2400e1200800c0e503a907041d40c030108250b040c2c0404030001d000a1020300700160100304403038580019569103144a112254845006004051880364002114241180c400000c180d080c220210102e0a0032900e003811580c25040c007007040144aa900d00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 575467212 1250 575465962 575465971
    0x162102040e101d010204050d02040509010b0307060f0906051e130f030809010f1b0212030706060b0408010b03150604020a031805060105130c020a0821070801150e01050d0e07051008 79
    0x1c190b0419000c000c80e2500702c6c8260301070907900c280c2c0c0d511443c01500b003c6e0310803035010051900001d03000521f1800a0714040c1c03076070302c03036400242203803080b694884d800f00030580140002e00b42a800c01c0c0c030750b800d00300180d92148001d0740b076002e010680042c4680314820607001485003000e0501c4540d00c900b060006640701e0001d4601080024000040d074511640c840808054000d0142410406036400c000d21905080a0458144010300c052000f1030890301c103440080541640701513540d46454262400d451803958658401d4100d0035900159421100b5216400f880444c0e00580c0c0d01c1941c42c00b03600170048642040615141032042d0301c10400d0026140d0f0503144125071110703ca41d9095104004c0c1c1c0e02060540006800042c11040005c1c200405810400c803020000e14484500b00c40d401541d42c401c80303075500000d95010040088411032500039890014a01c0c00350905150000060002c0c0715640c08641038640d03544603c1d80f086414407120002c0c08004180d40d02c401c0204000a14903c0b042d613 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 575468462 1250 575467212 575467241
    0x2070c05100314100e06100306090f050a11211f030f020102070b0405061c09080c0a15021e030411270c03061804031b03050c162102040e10 61
    0x4c540b1000b20034500720308079404200d080c2150f0380d80d0340134001001549000341051680b544808502c0080318010f0030082c0001e228002144e181000c03000c0283e0b07810381d4052072000b5041254224400a01540715196040e0f504d8903001d43e218a0b00c07141507188140494000a55060008000c0112460180d900d050003603003104c1169460315848425031085200ea0307640541c040003000244400c1c0101800380c0d02903001c0018645a2689400c2c1107940701d110555442c0d00000e20000c1003000000345460501c10702e62045042c4210342d420060101c0340da40154180c080c0210000d02046043c4c403078401e4280e0082d0460050000000b41c2d44484c1c402c07410300b1100131051800050b92072400710306507486a24010043e0048501c0b00448100b9164060810b070100840340380324100c510b031218400c0003054400d0362030704d50300d01080001074105800700c1102c0007140000c0c00f040084640d4600080e2640000e5002001ca885080c8001307001091500e03040c240030301440424010f0000e0380e07800b0041441c86c25 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 575469712 1250 575468462 575468501
    0xc0e09150906011b020a0f2301020304090c0201060b030906160e2b15151707030f080d02040e150102060402090615040f0f1706010806040611120412030f091502070c051003 75
    0xb01c0a05c9000341d4248c40150050380188002c101100b15078102c400c1104030344c000094000e403a00c0006030b49920498803612541d11440501010180201a00604910925090fa5140780280c001800d4100d0b1910548014103041c4407945540d504a05d0000c6181e4000100e51040f149042100d019001c4814000004c6008800020301d400e03003880c0b80b200007103401c005404440d0460b66240c3c5803081c0c0e403030240c030407070f409100850700c0390001c0c4024400f500d0b070702107040a549000b103641c1134803004e04a85241190004001d02c00140c0b14049420380002d01103c46e010410303421501c3c242c90340a6940310f2000f0654200b40080c00d207400c0c1011005658032400a000901c0400307034407690f500340078486c5030100e1307004000190201e02103a000c50341c0d102e00180b041d45422074100a00c5100c0c0000d0307800783c8000412810302a909505031040070503d08081e1818001c0c032180d1b494030b40c480c441100241c2d40e0b20703800284100812420324205000703810014608820420300c2e010050042980140950408814 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 575470962 1250 575469712 575469749
    0x50c0115050f100206040b180a0503180604210201181d010801110d050408040504060b090f040501060c110319140111040f03020f130c0e09150906011b020a0f 69
    0x3d03005603400000307940061041c1d460700e41d58050051001000c4080c60007031003040000183d030a110f010346a5000740700a584400d4801118038018910300086413040c8810402048138114004038440c0904446107401c4202185000682e161001c1c915121660754660001107038850a6461101e415140e18105840507a258030b4920301303c404402d851031004d02c1c1884170307040d40c0c01203803c041e61162091020b54145941e4038007007030548686400c4505100c0010440c1c240d54207004083c400c00103821a014869540740c24400f40414003205802381803c01554041000340d10b081141c1807a650710040c445580d0146400d005001c071840b11030604080d400c000100c3d5003c503d0b0006d079010303a0000651030f842c0a10316820454080c0c9230b036105542250130011040007080710f51045848418050702ea0110005051003081040c18005200300c041f500c2156182e406d0782c40313040c0c20720b6104001307003060030119421001c0c100c044011104006d501a42a000220b4a01500c0480c102140c60844045403590703003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 575472212 1250 575470962 575470969
    0x2070b03161209030c0219090c030c030510030b070f11030d0203010519030507050d0201030e0715110102040b03011e08060901090c060c030c0b0a110d09030908030406050712050c0115050f 82
    0x80d441c40c05000180240c5036400545000e021094003940c7c41d04030880b0060740da0b0707030b480c1c00d481401e000c82001c00e948091022140f50107024480c1e0104d062a015000c4a086035180300c404103005d0001d10070000000144038020340070340c03060080385003004101c9480d48400601c89002c2d500034000c050103102840d0340010074183c0717170142400f903a03880303005409100e007003406101c02e40c0892402a410076032143c5070044400704c24403c2d900038203a108c00203a00f83c01c0300311000d040301e0301e01c5001a485a20401041044903040002d03039055400f0388105244a080101c01004c1000003030700000c9540c040e000c2030200414055202e640124480c10380b03410540d1b6285c40566482031180c1c8060b000c140400030300400181c0e40c0325207550000250100141c9030003d0050012507410250003c0003080d9158040d40a06070800000c10007072003400b00030340c41d082c102200186035009600c4014030002114080c203e00b42c4c06401900e4120b800780000f00300000306283d03820509103080c41958090b040d130007088212400d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 575473462 1250 575472212 575472221
    0x50f0d061508090303010e06010c02060307021507050f0d050c070506070801061d01021c1b030806030f0c03120a170403030f0c05040518090c09010303090e060d120e0102070b031612 79
    0xf039140694250307840d04002c40304504c001000b090400501a006000607541d1001442c055110f59008141004030403128241802c0c0103071842c02413007001e0000c60f5008a020046840c00e0500850100d05619003040000c25401034900003856401220704100c1c003158085080c6040328460f9441c3c11200300c0b5007181030b010070403a03140c560060b040b11000c0c0100c00d61400e24058605440c4c64120007980b0441100e810040c0d200c0001c0380021060001c0c4031141c60204142900d1610b2100a4448050380000003a5102c0300200660550309010440412583c000d00c4580d00c18200142e04103180e10701440c3c010300a0804004c5c2003181881e00e42e0714000d0750310840996061355409000c2456403021a030507110300c268010880241c92044030314180e40340c0c82e600c16a0740203501c82c2c0ca41c01d102034204003104040300c000905a074040e01e210b4050300082442c030f40c040429000e01d0305100120310a01c0c00102c0c14070105411a140080c0004107001c610303c1804c1c09004600d03101e03071740c0d100d01e015090640307403d49 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 575474712 1250 575473462 575473471
    0x503071209050d080d020711060309030703021c02062206020d1e05040c140d17071a041a0c0c06040302100e011a060c03190512090d140a050f0d061508 66
    0x900d07017403002d241c07000015402800b0081c00ba86000151074010400201e0035402110a13500765080490f46001b0180c042003400f40518201d001b580001040c640002d585800040c5600104030644840c0030b10701d01540e00310b60400c0d03040074003035655440b0f026811024202c1c5130a884407001095003590511645c0e40724460040e54401e2480c0e032414035001030031202222040d1360a40c082c03643d18440c13000034170030007804032144034900e10192119420704103000c140e85582d01403030382018550108400a6510a0780404c600803c02ca0b2500540712040e1022030303401100c1d01001a481084280b0061607000543c22884d103c02d540c05100140200000c0b900740c0e03001441d40c40b00800b000001c80c5a500d080700241142c11450401c40e4244143c107150811403407100078841d00440c00c0000c6552103401e500d000170381d000b0300030401003a034442031500050448000c104041d44225010540d14840c80c4198203c9800418116185032100d0342d4000000042c80d16106e40141e20098854072501d42d4000c400c0d00303201c3c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 575475962 1250 575474712 575474723
    0x610080607141305180f0c0f1c0e1f0507090f1202010e0607081c09020d0605040c05030f0715180e0c130801050a050105031b15070503071209050d 64
    0x58090312524002a401499844402e840243c0010405071502007110206100c500514034103811310511194070741d0b00180040640c684100003040b0441d00c513100315081d070039800c515180c42c600c0c00c000b1030b40184018410403101c0e004451100c10560720301034408e00d021805130310401407900d9000701941d07c5034961240ba104280102c0c000c0041101e212240300e6078074010704040101500050000740607600030541103d8403c0c012480c200c0c4254181c0c1c80620140a01004100840f02c9c1d80000740018105200204410348501c0003800308a40103442400800e0060304a411880c0440328403500c1d0802d5009020071040c503101d90002d800d209107001c3d42486000365500100500b006940844150000c100403585c040070003036031244116242030303e4010403269000107200e0510b440d2001c290340041c0c0c409886a0301454110068444566421040700002c88951021071034184d00316445002c2c154015003e0b00021034a101805142a902442a03607107660740c940c0a82c0345c1081112185900ca07000d4403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 575477212 1250 575475962 575475977
    0xa0f050c13170f010e0601080c0f010905090a061a0d0b0a06081305030c03030a020c010c083312010507021608030304060c0315030303060510080408030a18050f0610080607 75
    0x440c070000b070881d1022140406640305296500040c600350303001d4031849902c65000900410000d0014014180e40f14000c441a034501014280000c103d24580e00406116181d2075000c40c00d030102c41c2d40000300414910428048200c1e00300840c84040e0880490864500d0030105901d01d0f0345000c1070014140c2e0f00b15206c00d980750311a0025000891400c3e5022140b40c40304220202c2c000508101a46c4a41c030780c4100507a44030400c299840c01e50300440070000074082c0c50b82c06d01c5034045c208815640d045440000b0f004940300708403200056007402803903e03504469000f005481d11001034001d207108000603000c60b1101c1c1401c404410075400c82e403040d1171480d0828004180011000d400070481c3c007000340b8000c03424403444070412804140710b82c003c80c0801e07611b100800040c201043e51254403101e5080001e040d25040c1c40e500b200d0310001f00948591980d800310090365032861800183e00c1070b0810100d40d501018a6038259a5400695070340141030200e8100003407111000030740a2107020395945005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 575478462 1250 575477212 575477219
    0x806011706150901020a0609150c03020c0703030e03100f0204140a031505150910080105060d110f0402130803120606030c1e0409090503040504110906030403180b030a0f050c13 77
    0x90580d08103c1840781180102030459010500d070303018044246002d610b1198881c170910142204881a04150105042c0184001d036030340c00011a200003180d0b051f041655a0410b181d00003804c007910062190505450f00f007444882c2c000e164090700c280c6042d84406100120f0315803c00401034040e210050082c21400035402c0030031100d42107190400c05000e910a00d0310400e00005d030901004032060f04c04802000c8040040c254240280c0f90003071340a645204c13500c0e0b400e480303c11401458400850060401c0040d100441e121075048410301e828854000b81980e0b21000020f450758040401405614605008641b1601d40201140c2c02032800340c501501d4020296103500395610f16040d80d003070a03031040c000010914240d0141c9001c1c503111b5000396a8840c00c0c44100001c0f0340050203030140c01c1d14107105420098540b2000c032508580c05043c143c00043c1d071050409244c02080d0488140b14001000b0710000070541d420030390001c211070405103c42d54840c141104907024600c071081c4009205030701003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 575479712 1250 575478462 575478499
    0xf07060c0234091805010c09061b0c0803040305030a12020405012f0d0903030306080d02071a2107030b0906030706030207050a0804031208010801140a050a0b09070806011706 76
    0x942c24041c211084104555a8401101100d83c294241c100c6a4241aa060100b001c2882004190303403150409886580c00c0002c010201209108440b0b445525910b4010034060041c0c2440c008042d24400c0700d03070726900c2c1e14003682c0360f802c0000040e001c5070458160000d191402c3c02a030301035a0040e55a03a9208085ca0741c00310700ca81641c500342c0c000480d41c061a0901900034041c50300320400b40d0b1103040311213145190040455050743e010308030b250003c124818101e94040307221001c58001c1c1001c1d52540446c8403500b0b02c07a110301320454441100303038a072074101d02d0b41e9101c400c1d103c0c600c42e840804ca078004510034403a1010007100d0084d41908140c0080c006140641c1c050406280070300201c807007000182e40c03101c80951140e001500c1e441e80039404810b503558444100d074054070602d0001d02c01048446100d204400008d85000e14468403540000c8101400781d003c01c011142c001c040341d08a060071180035161800a941940c000366038004240c03480803d0a0f442405250f0141c5080c01110010050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 575480962 1250 575479712 575479783
    0x9010f0306180908090a060305150a0302030d26010e070e030c0109230d05010501030501060b1303030f0e03010207121d0f10030908030c0903060a0b1e04110f07060c02 73
    0x1304c03109001400710300740c2d035201d1001500141c1140d031400105410000343c41000e005144680e03c0c4501c0c40b0700340502c016200400c1200c030000540c10814591072400181011160745c2c40d117100e501486a20000421512300034916000700169107032184000b1220003810384440902800c14041007020008004840700c6065480b0080348001031035003005001e400041d00409008029241350391240c0050061007800e1141000416000c40981d240181c55020b0303141e0300310a84805814001c80c404007052550044020058014000b4001c541d0b440d0b00345850b03051814203d890500081028411210740d80700720f9000c03031110780010421410300003520100800300c40c000044204250321083c0d0000017a8001001d9406200201c0070b0300d8840840405151a107003004085070020380c01c2001ca1989511050b080c11600c400702c00c60000042000000f040241c440003461006180c00006e900c10066480c1c40179180c480d00c119009e0020514210080381c0c0c5040c0603171200c805903440c801e045000106440c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 575482212 1250 575480962 575480981
    0x11e080a02040f08010605090a051317071223090a17030c0f030307030b0901140603060d1203060815010f120f05030a0c03080a0c0807260c09010f030618 67
    0x102501c0c00f0b07219004054119038580c0300c02c409030f458140c14491490300004240e80646900420045441c160341648400e090b10503016002084000c84415604042c108460b2455041822270304002c20a200c01008108805e1248031200c2d000c01d01c05451140c2e031b0003200c540340030040c030f40100f450074104110009110991140075520040041e50444070f824402c1502140c0001301440c0c4919218102905441d44000c6441c881c41c00000140701521940c2000b090001003a29580c0e12542e030280420400030307580001500518242c1c4094a0342503043d0441001e45514030180c521811460802c0d981220003030164407030300b41c0340b4541804004014a40d000c0381500405000040080548500f4190b0f40800c02c2c61001454580213802450f40111440c1d41201881c50100032414000b0401071040501500050400c100c01c00d2900c10080c00c58401c2601400a5070546603604011458040644c40500c00a000c5a108240f0034030f018007a211703036000c0b15140500090345d1091120107070002c008091 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 575483462 1250 575482212 575482231
    0x905010e04020a0e0a0e07110607050a03090501091407091d03180112060b0306151206130605060c0105091603110d08120709090e0106290702090a0f0605011e08 70
    0x4d0380307100b0701c1d65101c0303140008054200c00b14440f4200b882d40206400d1152510500301d42c0311105000505031f01508403261240140b90009509030309246c171034013400410b0005031490846608644140d400030540034120380600c00200500c440c1c5141e89a05400c0d00150000a50000c1c442c0100200b81c510000800e02014908900d0343d00206141c5400c941d241d400102c00074402100700000c0f0308102202048440500a04038140f02c40020b000700c1c0240c2c001c24480c0181580340c0d00d03d1601015801c110003406008181e03c0c1ca89241c0208107009000883e183c0109200360501000403990350008001038070380105800d0800c0070780c0c100780690302700d41c1d0a044030000000c1101d10854144030703540300d005154550b1019841403034401c82d50162a22489600803030b900d803403410060230040d205190351618200c0d6403c003400705104110525406000d4020f9044001c0d0381c05c003c035008003607005071913102c0c450008200041d190001101e130540120011000e85a241c0ca0f88000c1d24012030303c05620540c1034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 575484712 1250 575483462 575483477
    0x10219110f09040804051c0f062a0c05190b01031202121b0d0201110d0902040209090108161e0537080f031306110708070b0306040c0905010e04020a 65
    0x410100310002c2003101c080c1d80c41000441d0901c81850010000040d007003109a031400d11180f15111512900248000142926611901403002140710400303404460010403003070a4804204034043c003111180781007100e00d070050307881c8440c4800c01342d003100030b072141c102500c0003c5a0855407181c040030040d02210055118000c00c0e005444030110040c007030090040f8540030890b00030700d6010300e044c0712540180e00396410140318074003241201d001d9804c0229061008200d44800d4000318000b0321500142c40e4015a4480001c04c042030001030311140d00d080080c014040682d0780000364091810050a090301a841000400071498248106000754048101c0034104685c5403070400007040b500074202c8508001c40c01d0412440758188421201e070103611000c1c0d03191004c0380e40c0303412550300c240c0504000e100500c0da41e8405036504103e00000b419192048030111900d4058000c0c0079002229070f18451401c0112a0349642c1c8595454012502c06840e0f290150911000b0040a5009040000e0030000300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 575485962 1250 575484712 575484739
    0x2d0d06182f0403020405041410050919110904060e0d0e01051204060b030a03031d0615090417180a06180e190212040302060f13150f021902010b01021911 67
    0x40f485818042c5101c8d801468841801c070301341a0030034141b29a074540d242d20701410861100da000c40c808880d095800113281c00710351289001c01c80b4004d41103000d0381001d01e407000c200070050103a02000050340031500f00c40880c208070008039140c001468000b400910300b40000301d00c1c03400121186402030321501f004103810307140341d002c20300d03145060754194002034036118403480b07900030310304a41100161400508810b240501400d40d112502080d814000e103190b04c001400d02c119800c50710300310f0402c600c80513601c3c0704034074298540e22440342c01c1c14425104000001083c03070003030f0615494681c41030303c005407140c0f500700c1034080d1510003000088440404006019441081e20003411200300d020360703403281390400c5d050080c546030000b45170781c6511000c1000d010f9100a18001c1040c0c03a03511003007801101c3e000702c1005029041080403142c440e400032450314864503608000480d070140d5540208450400c0d00012070f929000591103060a10b41182264003080700780c031030701f1002040900100ba05250 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 575487212 1250 575485962 575485969
    0xd05070212192a150b01090f051003020705060106020a12090602150a060503150f060307050603040f06020405120c1206430816020706052d0d06182f040302 68
    0x68001003216404d03841c0030010122982440b03000e010010a2800a410905110a840d8a945603000c0d59214922032000760f61a9803117030301100c5c1e101e58000306503490395a403024041d42e12001e245044070700401500c800c032801407003100324070225445940209a1541a0003002003584000b5100400044d01e03045d012900c0d80701004a0007005620b0f007031550192400d20329880d9420000f50499201c1d070440d41c41040b50340d4900c2e082d01c0c0c200e42c01c1a40c8061006a03854034800900c202c0d80f0058000b5203460f03c1111140011412030a00f81e130546001c1c07440c2c2c2e0104a42600c40c0310499440c0c01005949007082c800302e582060030351402c0501070518401e00d0910711541c0280203146a0900020101401c02204080c040e075140d000c555180000e0041030b003008000b5080b070299042c0c0c074680402e40c0c6e441b4001400c3c2c28070300c182182061004903541d4114443c2d081c001c0c2069000d501c01901c02200c44031b860003014425845041100c002c0c6540c003071048900d900c000744920010000740c4200303000210140e035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 575488462 1250 575487212 575487287
    0x10c0203011505090604150b0f0904090b0406050f060307290f040f090603050d0e0d0605010e1f14062109030d0609020a120b01020a0501020d0507021219 67
    0x1100b0a01450a041c501410000e8030f54005114078001d40c2000f040c121000707040c00e01700095541c88000030f500e81c003103160f4680c0140103600340c0e240e125042c10750341c07000c2c00640b0f85014000d50068005201a0303403115415aa115400d585c1144c16921060007040352111040321111210300c0e51030786140b0006510000c1070f454000160300d131001d040002c0c0410400d009226418024007081c0c000f44209407950b00c0e210707151075008029178140462040d050101f940d40300000307194640d208400b080340e035854008a5141560403201002c5400780d92034402802200f4058850032507540010000c04c00407800103002003a0810350b82e201144d400940614074080f16516000c1c030800142e402140c68004c10542102954500d50046010b01d1041058a00c1d096110102203200102c4110108545400e10300407132070520600b10140c0154070211f0701c0121007000fa00b00c240540d1855003113030b440441050320040c5a114082d9076080d08044030107400c5196020b12640030726044400b1031405840300c00806940401c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 575489712 1250 575488462 575488481
    0x605060402120a053705060418050d09051c110d120e04060b0c0604230a0305031824070342080a030e0d02061303031101020a0804060b010c020301 64
    0x40381c844c0704000145050030000505018414108111035140b03c008a1560101040384040c80b904d8900141003070700c0d07076000807400c181d0040842c40540b0142c02c2c5903403a40a0303206000006251300d94000f80600e41002ca4003402001001d040303001e06090785c0d401c014004000902030b0054010740c80c0b280400c11314880d04a00319090703101c200c0760481600c2000101c4001c0c0c0c00c08480498140701d1400100b100084580d4840c0d8803e150500c0d41301c0c5844400607007011031079040e40c544148407240c41090b900c4400b03140900d070000001c0308001400000c1030303101c5c140801c0e1220441100d20603554078131401e915103a0400c08908002a101c040100300b9201411802d442d00e03250b900d0300c08194034411000510f0107010191040031050f942c00c15900c240c03555810038010b0304108221920b45101da0710071210401080d4000e20341603854481a0070f03c010840300e403000b940807078142e00c2d5040403040180203d0352410010b41d6401c000303503560f68690000340000f85500741044543d0300d9207801604c09103e8071045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 575490962 1250 575489712 575489731
    0x91d12030109050703060e04080c07080f0a030311040305030909100b0415020d02061501121b0207030203060c07030e270c0310080c130c12060e1b16060506040212 71
    0x3030707606100005060380c001800180070140740007810840d03082070044450300301e64010081a9100125660949040065040540c1500800510b9000000300003603800b2041c2c400d84040c030042c2c42444041e03000340a6840040c003242c1041001d14428600090b4056005001549102041d0345444501d1003070b4100313420107400203c3c6400100ec003560100210052000e480c40281140c5c40c0c0141d19418659081c242c013410b1064a40d40c4601050b05600105045d803d040311030f804c1952503460007940e406051005a000f03024210200305407260307941c100c038a00e50300b54480120100e8a1024071014010048250702c03644101440406a901040d1480e406044540305007138036401d003100d00c14a00e402c5a848080380e540708000e40d009a4031118001100c16030302e4840041c20070300d01d040503181024902d4149002516141d000300304020a032070540e02070242a8640c070744041038031890101c54400c81c20702c01c0c5015034800760400003c4442c0c004079031195025001505007145100c2040400c0d4065450005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 575492212 1250 575490962 575490967
    0xa090503120108061b1e090d051632010c020a120606031e0312020306030a02100315211b090f02030915040309091a09090c04110a09091d12 61
    0x515540d070418542c0d03c040444030781e0f03190180c0c038503450381410b00c0f071b9840c10766200c4042483c03a032599444d240c5110723045d04102a0f5400c0d0151007100d01c0a2101d60054072000c0d80104018907505e440b111042e00700701c031540040d1070400401801500d141e41050001c0341d01c40684280410802c80704101145107610407070004c9892821458800320942850f40c41c2c0c00302e5040e144c018000721ba40000101e040100c40e600c016501c4e203600000c02d0520040c1c0320040e4010101002d1415401c0c0e26511603440b6614000f5200850758856001e1440700b003d070b1108202c1c1020b2503495001084180b24149165941c0350b035610042030303407035044400359400502c0c4400305650110400ca0791a03000e03c803d55070010907060039461450305540182c2009003500410031055580d01706c0e00010b250340c4010181c4103c00400100a916080b41001e907140c41031842240038500700903405541010361425516a0b80107916214805400d00042c0001440105600c0c4408074441c211701c0000082404a01c25408020301c5456 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 575493462 1250 575492212 575492221
    0xf081323010f09050915100206040b060d11060307111903020105010e01050a0b0a020f0a1101020c010215070509010207050d21090b070609050c0405010f050a0803070b0a09050312010806 81
    0x10248545542014148003071802c0340e003001030b8001e1004059503011204070005440e9080f490034610501c0c0c0c203103070300841040086058540c00254403446141300da040c4440641e10f000c184050610140b0b03004280700314045084515103006006940d0188407850a60046e0340d0340c05025140101001c049441c0c038044804640905a080c014a13001d025440e072000c000d5450403000c120082000d102c1c00c00681703800f0131150100d51003880b08000d407104202c100ca800912a04000e010041d0114065016105121000d0314950004c181c03140140390681401625643d0960300707803015130150408504500a0f141c0c007140b0f6941e0b0f141c11010081c0a8500342203e01300b402451010442130411010601c00004400c1115140c01000c8402e0243d0000c0b02040c0002c6920f8254900620104013940c080e0600d0000b01e26403101e560b002007103401c110354a16046666074220703622445002d00c0504104066000508481d02c2d540020b1404c0707218504481c589581641d0f000c40030142a00210307040c2d0031080500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 575494712 1250 575493462 575493509
    0x20910050a1a090402160b15130b030606010e04060e010306050a11130513020d051306111c0c09030b09100f0608030913020c03070c0314060106020a0f0813 68
    0x4400b0302580a542c0758110140d00d6001d0403401450f540a00c43c0d600020402c0c07030707030000c01d181403c219481092800e071424469500c040c0280302c81c5100b801420745c0c400c401d142c04540d00940030901000f602030501e41c0c0351003004407110898000c6013604a40c03103003030014501d003429910b03900844c02403000041c10b05145207a0070545030344d02d00c0309210307141c140310b14001c0602c0901e0b15003c454003124a024103a0004416001901030081402d080c546043c0c204408040381c0f2000c0408248520020044c0f05104c8401d4007142c050100520400389403000d4000e600b81c40c9601451019415040590741e00369a0345c2e030390341200e02c226583c2095402070300340c07140310a400b40944051600c220070207001190601e400c144e5240101d1007458420148150a52219000c076411204110818802c1d40e542d1540c0c2e04151780b00380d0491004a60841214501c5260020082034050580d42c140e0f020b00f40f5022503484000030301d500c214060f03680030710403c016681444e000c1000801050040d403c1e10b0301c40c4040081 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 575495962 1250 575494712 575494729
    0x3020a0210090501090b0c10050103240c1709011803021b0a0308031f05031e0613080406120b0406060c0203061f09110d0203010b040f120b1603020702091005 69
    0x807505011a460703042c441c907030b08804000195104001000e8a509602c040107182c1082070f03107404500c1d443e02c800030003480103141000304018507009081001c102d207078504004644040210074002401c480d00c1041c50a6028141d03500a00c22100100d5146030442000805811211040700907a01802e68040c240c414805200443341044030990310441c0f171a1140c1c5031500c0300602254152500345c1c0311800d00722940410401811001d800c0780c8038450800300b0801c1182012000622a2103280002400c0300c101411107003d103980083c401d410035203010350540f04102c210413420155500c88500180c2612980308d190001c11032590350380c01b00f040c180103050401c072000c0c1c00e55079800d04540740644003c180e20710315021515040340004900200a54011441c000c14001020301400000002000c00e1110302401c00c1d11000720b0701e040f4180c3e071740d9203a100c411102c03a001400249582c3c00101c000d040078002c02c8100c0071a04015103048542d034002070f4644400c4078100800c072120002400385d410400e0b030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 575497212 1250 575495962 575495989
    0xc11031b090a02031303050c150c04140306061305090a0602120106090e040c05090702100203041406010503030c07060f09030b0f15040e19030314010f03020f0f01051e0c070303020a02 80
    0xa04620b903042212162040905018000d800d001001442948c1001e08002c50240d40b00200d40411481c10546590003042d840340c8151000c9400f01d5802951328a408603a8030301540004107089860003030f030705511014080c01440d0300740600030042288049501c9000038070078040310030015002503040c41c802404905c61030304450080c4510000b00400986001c2c0301c1c00a41e5400c59002003280d403104c904918112584850706441070010040c4010424681007071300b1605004c000340e44040c1c1c3c1798818540c1c0c0f030192000203104c41d80807940c02c00409008111b441d010b00050320741000c02c00d46030b4442e07400c031a4050756140103412441040003039207242d0518800741d05204890611420a03802100f964400b041c00004072214800d504c00e03c1010701035400500394009120249a040d0313036a00c103289140f2410322050340035100c28419440d031403402c0c09543d020038005866071401e110a110210105401c807056078440040c00b003060351a85c01080103c000154407070303801080f929400744144484e215a240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 575498462 1250 575497212 575497231
    0xe27100c1e05030402042d0b09010506030903120a0b04020408100c030b0f010e04090605131506030312020918130c0b1905070816111e030c010c11031b09 67
    0x14410701040d940300d000c40344c01c02e80456020070441804c0e07a0246a40500c40b55079206e000c5140e11003400042e4a400041e4905000c4a00c8440b0b81c0e602c0060240302c3c482122911f030f29400030801c1040b4113640d0034445402020000300050f060131040d0100b4100d07845074020081c40e500104259485c841c00e4082c29603c0f40c0a440c040c8042342410011501c80d0705205825414004002e4150400d61140e034450858a03410090611843c1042d007003114041414140070f64000920098500c0040c169016400440e80e060341c4000400e00c3c8406801c003b50000f805903540403003445110003081c401d190440707006204030020490300122a00d08000d02d5840c1d5441903407244402e0200c04c58404112070110359180c0e5030304165581d80f09500c2d2840480c402c0b60392950011894030074031014082102e0071075a044405481d5035124003110305c0850080e03075014014940c181d200c81c0980c50507500c901000b5507624401c004200c400440000060b0400c6590358200c2407552001791307000c4692600c1003030a50401c0015 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 575499712 1250 575498462 575498507
    0x10603080405060a0e180405061303090e0c1201060305150a0e070311041e090b012d20010207120507050c0d08090907030911010201060e27100c 63
    0x1951a00c91501441c03103034a11841d00070660340b42c4a40036008500c00510002c1848001c08409014a81c00c81d0301503906071242c0c490354001400c107a003040c41100e40780d601a155102d0031442c00c0410b000404009100780c40211040c41860700403d11100c105000e00246e0b01c0210341c91900c1e01c0a0340049001c2c08000f445031540400030003000c1800e41c100f5070088103516000c110400100700b10040d5104583c4030011400c08052042160b1656001c2c0d0800e550a1140074040d40b00315000440e003007002c1c42d5441c800d03030300d44a00c002803005a2001c4a41900c80c241442103034120203402c07540040100801005c21a50004ac9130400c0241000c00300d0710100489c1001400c201c1503031102641c070500d402840f4000c03204a1030303202c01d00611409440c050100245000700501d081c49006002d0100000b0031990003214440b4606950b006001e204180c400345120780b25582c2c1c2e1100601717681d07895490030000b0682d2103103640110101c140600d101a55060031702158110610342e00034981098200880910600c0d0b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 575500962 1250 575499712 575499719
    0x22080a0e0f0604031a0c04170115090608191401060f08060c0a080708071e0c03091403030a030207020a09150611060c0703030f060e15150315090a09021302030405010e0106 75
    0x280365041d22158444485225542d1ba619480e2590b101d25000115814590f0344282d09861054000914500010264070704043d602c03c60503080e144a8056540b454010075420080c103c4400c001d508090b0081aa03180c50024018400d030071100c0c9a041407c1c0c140c007025052180440421800790000f12141c200d034988004d003c0014501d1030b020b0192030410031228045440544940302001500c5182070050400000c000809440403000c20011808030700380b0040080c0c00c02103445180790702d203800f9000d5450303d01045022402503105c440100d9121b007003403101103402a0305118a80b84d074070082c5110006141808005442900046500c1d04a83e1014040050020024080d106029498100072950358641245400a0600c1e504032080c440010020084000b006c40021b2100200984010104c0002040400c400d8403080700d9003051241141c0c4100c80508280940c0b40c2d0011221900003284001940080c8502000c0c3d004100b0154001c000c4c0800d101081c4148500d03001c02d64001c001103440e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 575502212 1250 575500962 575500973
    0x108030f040312050408030409050114030705010f0f03090506040c1a0301080c01050306040e010c02030d14010305030304020105161709130e150a060506191b030822080a0e0f060403 79
    0x41c0e0300008019001480f01ea141c0c00d0f000d0340944005d44400000d5a81f40c5031a1070303a03500140024400c07814030340c00c002c03d03002840c00c0210341c210540c0c07010307500c03914400341003031003907a0a170b03000202ca400b01542d6004a00105500313200750781c001ca11520903111614a0440c0d0202e07890a08010356110302401c00c0100441e0100041f100002003084c00d04589940c0e0320000a801404040715046e036650810310031003c00d41e070220080018804100d420028032110b60164040c1240c00d01008040e0387c0108003280256000300060040c2d0b406404480320410400e5440c910004420007200d840364002180b803517000e1420034903800c3c0340100d2100c20005054460001650f5a4207102c47d050610f06102c0807901007181504070341d0140c90064411546e404030800c04100c10140520980c00180c1d5a405924218421141d9105540e4060340d9983d000d80328800003080d2400b4002540300c003942c2d450510000078140c1005000421803503100c500d444e50307000080c01411600c0800717940c400c841c2000f0600010f40c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 575503462 1250 575502212 575502217
    0xa02010f080f01121103160f0801090309050d05070b0c031e0c15061c0302071d010f0314011b21020c030d180507080604061503200301060b1b060108030f 67
    0x8002001039880403080f0b0418001c3c0c07103144c0c11802c3d018041e140b403038803180700e00741507c001b15480c1054030306200d9a2038190608071034011800400084080034100082c5c5000301000541500403815200ba2035901c4401403110742c8204500300d1907400120f18070016480355070084045614644001e4500f00c00448542d0f29190700300811040e080d44440411000d46402201c140c0b0b84030346a111a0345c0800c035090203076952000c6c0c8228051100c601ca40d000703031000301c00100e9040b140190001c018060866aa40d01d01c2081121401d5096698003035010080800c16086580d441c280e0302c0d10081d40070b08040e40e02c4c541d0407a04860308118010056440c10900000482e4158110300c0000201074401c01c9a08400b14042d5002038400c0c4144100850400804503925004520035042081150040141c0c02030b07a0f402840082c02a01180504503450b003514024020804001400000c50b075480304401d2507141c00c682904250f0004041040c1040ca80801034540035003c400011030170070303074803c010100d40e1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 575504712 1250 575503462 575503469
    0x20220602070e0a181223090306040f030c06380310020d0e060711190804050103110d0c030213120206030c070201050f031905070513140f0d050a02010f080f01 69
    0xe941d48100101610404d111282c456403085060140f100390000003030600040d8140c4a07103189060103418070700d04510088035031003040a805820150b986460340680940492010b40034407050403030b0880068140d10841e4048503c0740046140468020002c270314446a0810182c0d07003400342d01692126036030001d5241b00803554150301607683c1c094110640c0280c1841c00d2708a40910130b41c0144011150844500d00f5844056400c407401390012101e0300c80c00031600d0700003801398032080209010551080d0000e229a00480300f019203040e000141083c122951890300f034001a50108612555424003400300740142000b95851801c02d40c01d0f000616207101c00740568064240008074001164000d40541e16a0324400c040141c0703914000c401c0c04007003580441005d40d114500000921014050015074807502201c44648015030f0410a40303003c1801100c1c0d03101e034400ca2115482c5210766480c044904041d2090000e044006014400500390401502880044c03092081c1041241e100101005044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 575505962 1250 575504712 575504731
    0xd1e02012016061401050f03070b0909060604030b070215070e0102061311060a0305060a05150d050a18050f010f06051e1c0803060108011403030d20220602070e 70
    0x56540a2151140300d4030014801030525003080201440d913019200c0c50360480d2019a031f01a021210402010f0b02d0b20741c2800b03941001d9105000d84100390820383c0070240e110750082d145a01d01030312506d44075403500040311074500680c04001166002000c3d001032a401101c20b08041b030503414080008cc0d15208001d0030024080381c520038002c01e1015820111220140c0901125a90060b210004000d8141240c6080c01128045c1001590b404c18605840700304840126041c10240b240c90a4006000007500c1404940d844a85880c11a0850482c10151901c114001c100311003a00c0902420f4540500f2041d01031803500804000341c3d103c03010007910710a035070780380340f001c0c0022a00042e084542c1c10740703050b540300744e0040080104042c000046005100c240c03680102c0d6a07035401045103000f5500d100310340541061155100895098100503100e0000301c640702c038024120b100b0360840d90080302021009903034600d229007071402840340300f002604442c170243c10b03050700f02240c20788001000707414242d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 575507212 1250 575505962 575505967
    0x50d0e03070303180b030117122a12040626010b040326030c070204140103020a120609051023160518150c011503050604140f0d1e020120 60
    0x13020f00070000c9040c003800944d1500d03512541c607904030540f01e0b000d0a64201c418803c1d03091440000d01104292045500f4807910400740d00d140910081411481811080d8684550b0149514076022000513001420303803540c13500e118040354a0f42400c454030352542c210f4144a040e00600041500100b120166a0070003114039201428540b000608080008501c081e2a030210900c034035441d60b98010b1501c0c50003101c081c0150502c034040c441d0648828070009600c140c41072810064005480c41b1443d100b805031500080e01c0c84245c45041c00c3c00e8038141c100441030758411132140e40210170b890b0180c09800c10f43c140105460b00070001484400560021030034050045031403c2c10684103407068641c54006015000d984012580240c0039030019141c006d2207500700306800c0000d210410203001126089401400c141d11113840f004102c0f9803071105400380c0e005071020f846031040c04200c1a4090112662040c40c01802d407080e600c0c4580340ca01e204c500f1a41850b00801d03243c20b044035441c1031002c05808196 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 575508462 1250 575507212 575507237
    0x30305090a090501290c0703111e0f01030e0c03030f25200f0310051603180f081b031305060a120b01020316031e02150a0504150513050d0e03070303 65
    0x2180ca000b1400d46c403009110303c080c044100139281106880c2c00506130b07020040f03500d60307407070102495114884c5a500a00d212400c1d030350542c4603411403911076103090f0a0f01e5030b0324201c2001c00e042d6441103214059a43d00003818800c560040b03400c52210003519803113648641c280781d0380c4540019000d075540350209440b42c010446030396030f024140c0d0300301002800c80754a801c1000301d003006807004681c0349032035000010303040c02c0c242d01a0148885a982114094201d030302c01f03a84c0c82e0140310743d50324250f510300c60074005000c444566a104500c6882003400039a00c1c0c0046090800108006400141c041e60007400891440c0350041e040c04118036003041b0224605081400403469401402903003081003152210007000e054201036000709003e1410300c50160198884c106990707450030280400010041d8900283c2c00403040e501c0141c0082c0300f106108000e2803440c001005860381540c3c1d28142d62601e40c0c060040100030414200b00400034140040b03440710560003c1d0300d4034058031024050040004628 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 575509712 1250 575508462 575508539
    0x105041e0c060323090a0605160f0503100902041e060f0914030a060c0c0515060d030503071202070b01080c0f03100e01151502060c03270c0a030305090a090501 70
    0x1000c02280d046400703d8a02200910b6440e9146c1d103003560f0300c81c40c28000ca00400c0b03042e43d4415030031843c0d03103520280e60202c2c0800c517802c1d400100401da88901c1280301254444081c0014030040248019503445030300030122003801120345501a5050110f4a401070000030340080b0100201c074601500380c2040c5400d01c001c2410185005c00041c80e00340351805401e52241c0141610700114025401c943c1d094040c4480411451000e0300c0350b947c00100f0424030800680324400440c2e1000c003a103080c500144060b2680750981e042403808a80c4031943c100144140729040003030208071442180c61001e1049440046130f12600410740d4901071545072400e85010520940180c6045001c2114803100e0340d95503182c080c490356010328450b0041c017455000c01e0380031100c1ca06907402081400036001050102c548015071100070f120103000a80150988215a546c41084031001180291121aa501600020010000101e03080100c0c101c3c60100103200015100000461040800300c1a0284200300b041c007 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 575510962 1250 575509712 575509751
    0x370801060e1b070f031805030304180507110d0f030b010c0c0513060f090902040507080933090c0102120703021c030e030c0a02030615010c020f010908030c0105041e0c0603 75
    0x40c0180e0500040403040680c01051501e40e020440d50b90316006d5241e000309a12882a48513000841c907504089100003086d43d40400e4004101c2d04020070a6400d040301c03036041c40c00e506000343c04961040820700f400342d018004c4c00d00c990800d203050412403000c0d50701e22000079a01d0240e14003881504920581c40303011070b0311000c0500001c10008060590700c40e0050050591140e08074015030138040030501350340c040c0c0c4503a07000d2540d04002c0d041c0c00c4034100f21032401da5100741c1884070401011074106c50b0b0f40628074405005030050f0000d880c5120302203001a00c0d204c1141d0616525100c20800e50001c01e44c081101484500c40b00d25009019007030440c11005411059101440c5000000700d192884c41c00003803c03500e45209600f542c3d034554501c00080100300e00005042d02050036911500e00520b45000c1c2d01c0090201410441340441d200c10f4142d00c1d40d005131046042e903a41d69001d0100340711080c0900c0030f00c169500190500a40c01c1c0d580c071040103501d4070599050544800d0180321020381400e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 575512212 1250 575510962 575510977
    0xd0f05070b071407120b0103061a0607050307061104050303221d0108100b1e0103090b151305042112050c25050303070c02370801060e1b 60
    0x2180c0342c440c806801c2800500c0ca6002c1c120700103204040c4d0004071800c103000f405a40c690080d004002d0341c0c5ca941c8a1902515240c6c403074071034110f42202d04000c5030361108090300d0124000d00085880d140c091a00c007048a03158196039001c004140700030852a98000120741c0c4240c00c0300350288aa024401000c004040d098218a401c00703035000148003c01c108819090490f80e05908465100416200800c101e81c0e840d44500c2c3c00c0300c41d0750520400d010030b8400041801e2810700d000541c480d03803501e84500e0b0301c03001c0c0c0702e6102400c03404414840c64508684107078010b2200f000e003003202d07080603903920000b81070742800913421184000307100040b903000d040b100c001da202c080410720082c50140c103290401d0740441d0031040d411003064008101362142605d80601c09500800a45c91602e800d0f5094548000101d0f040b40d00c05d60000c2ca44d13401c0381d202001c0c4e0440394151248085d43d0b00240ca01c2407008000c1e5003003105981e1600d5403c01680410352500b9411000c2d83c0c9040016020039071a41045129404 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 575513462 1250 575512212 575512229
    0x30c09040e07060203071703100905071b0c050f011e03110d05010b030a0507051201030602030604090f11030606030a0b041101110d09150903020901030605060f0307090522020d0f0507 80
    0x4009215134000c801004880c2c8241045100b03030b1b10316000310259010036510658510070030b14040c0300c850f4580e40001d8011805e814042d911004016800c0c6030150010804c032880003c001341005282800d00c000f148004003401c00e000e142908400c1e00b0030700601800700c0401c254540043c048206140302c00c45041c0741f40710105103e1982c4504071444150300650308049002c3c0741800188600e0310034001e40f0600d00d080c41816050781d2950f11640042d41003d02001da02c243e030342001c3e000140c50100c0c0c0c00c400521985000c10f10040a008141c103091008010314041c0d0807526450300051105003a0702e0f84039501600321a43e2061400040304c00081134084503425200b05401590100c1d0480b241e10f0440d0144e4054881c0442c21902c01c980291240c80025006026400180001030b526044580e10080103040e243d000300f402030000303180c0740b0f250381700b80d16050f80e41d01400040990396160b8488410704c8421560301c8482ea030b003c5445c4442c0044090003146481c4a280200f0a09001c0c0310300034001907 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 575514712 1250 575513462 575513473
    0x40b070e060703030212070e091501050d0608010605040609060b0703030c0302090603040b061f091a0f0f0706060f030f0303050a0e060115031b020d110c0a030c08010e070b030c09040e 80
    0x1c3c58007a00a6100c00d1460310020782c0d41c0b00003200140700e812140501c003800f030004116a1240c4a003110b11031002c4003801d06002c0c0c1800b0420041d04140308200041001c1030010802c3c9181c5401c0c0005c1712000d0700030702c3c0d42130700340783c020b000403c102404c035580a0340c9840c0006105103800c20481c024091040b40e140c0c06580081407109000b1541c2600740618000c46504007001043d031589082a0303103174a6694040f41581d0b0042000c00400300050360880d80c0c04255034a40420050b00c90383c582d000d995101d4510101141807000c0c440244102c2002d0450001d00c0c84865045807645039040d4442c0760002c04050716440060307846085908440031002d0f5180803030300300d035860340f103a84221032a2400000010b858002d09140c61031408a2002807240d19801030910b1045d210811a42c0b1080c0c00c1003981c9603c0b4464081e05192103101d140030080d13008840d54503125007021341150950300c401e000d90800d0351000b84e00703101140d400340450b904401c100500c90351310000c40c0c0c040b6018040c1528190003034002e2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 575515962 1250 575514712 575514727
    0x50613030c0e060103050f04110d14010e010c09091a1c060509030c100207020a1a0712080709140f041d0a0f0b0708010303050d1e020a020d0f09050603040b070e06 71
    0x44005443c02a20b090701c0a00039696058204a4044011140980f01d01012000c01007641071510480e1400b034051011419401740043d43c80f425569045054859603554410051003558004003110241103641024040f582030141160900280c03652054807030320041441d01007d0b418074240c606e80701d500250a104500d04005807076120781000c01c65207543e019030406101503020034401c0312425640140546007290030a4a84514400d842003002e00180c010070400c0c01088014442000215481c1c0e00d01280d0310b0222402000c9010682c4800d00b0b010303014481f455542d031144d0b41181d02541c01d6a000604003003034480d06489214050802115000d10302c20402400000e10006441a000c1c0c017144209485400c2c0440e5401801d20000d070002e034052100b02459074180e0081c8800f5040b5482100c0d55441c02c0e40310304102da0200342c40ba03000d070744044881da1209401141801e0407040703905140740e0a03840d00d00030800612000303000070701540d04c0c0000580300a008aa85940300c0c1009407600f07886044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 575517212 1250 575515962 575515979
    0x712020d0b10390b0901020705070806060a0603060305150402011b0c050f06041802070813180f0209210f01020a0503150a06050d0902010201060b0307020a1a060109050613030c 77
    0x44000d1840d1411002100f4000101e0407602c0102d8000c200fa0010340c2407015520f880a00302c001800e000c0907550200040008504100440c10240000301d0113000355080460400441e81542e6100c401403506003d010408260081000c812600e21124484070b50760b170311300c0101c1d030040440122031801c00c20003500005000c6c0010007101510000c5d58010310306602c040810500f801940304511540029440e186200c0500360003402c071062080c9419420840d04481803205180103800c2813280c1110000d4441c0554400c2c0210403009521040440c5444940e40c00725011040c1c13000c11000c00c04101e1400c1c0c200c2c0808205121100c21010001c41d210161000014226481591a50f4a000414209410030314000c03681d40126040354580515103910500c4040191510120036410355584603400145074124400540c454400780d03000e81681d494614001d820986141d21412500349813504004640e40c025441009aa80407103180c0d45803200c45240000c07107141900028400d0407000000280c845 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 575518462 1250 575517212 575517227
    0x1509020a0f0602010c031a09240904030e1003060e060d02280503070902040510030e03070f0501050603100b030703080c160909030306050d020a0b0f0f120109060503060712020d0b10 79
    0x100750b0b60f41400000465540103004860000110743e01c0240d60002c41d503044c0c49207070071046515400c010b550111100b40c0005032b45030011075040e00031a2540c11036040320310386104203032881c5802d8141000820b04082601c8075010008101c50b004100c44000b02080d9660082c5010640c41d0304045841d00301d40d112150079040380a8402e00f40244500c00740466a0302c00c03402a602aa0000b40107600404032180085000d0004190800194081008a0300224000380740c1070844502410003c44c10342090400d01d440d0481040f078500f03200780b902c540490256004100c1d90308894100c0c021680780d0109400c0581410721100a554000b00340000c0000c102c01507400c2404030f0b42c0291404c00c0800d40d20000d014224801c403000a40c041c507440d200b4809128818007910032030202c0c0d0030640c2060001040188164050080000950766020041180b107807540100005440150083c00142c202000003820740740996403c1c3c541590007044180d000120303075000d01400b02004107a90748450305503101034000e8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 575519712 1250 575518462 575518481
    0xc0903011d0d1d040b0109030203010c02010c110c15070606050a17120408031c020d0606110c10050d0e01182001020d1413030b04050d08010504091509020a0f060201 72
    0x601035041980b12a9010b9010295884004943c440c400c0c03001c901000010210200742c1414010380500200140c2c90912514940300026000000d000d0300490000d042c5140f81e11802ca07841c1d20421030100300b074440041c04425000c0d1441510388441851034603601901c00c41d001180c203c01d4820340002d410018401c80c140a60210301031f910b00c40b46011010000c2e2040303025400455200f006500116401400e17480e60030191103000600f845d100100c0c41d030980c3d080754003500008121151410006034103120744255110200e80f00f9070300c0901e05601402c00c3c012280000001c0e42c0d40c07843c6603100311080d00710384414992040c80400c0c80388140ba000c00051060007155441c888941046842c1d54000503c0652000041d2142c08040d805400740214a80c0420030040d45400750b00000000283e5000d44180501d1150015141c0229031560017440004168007491083e0b080c800d5401c007003031032404050b10460b0107140100340504d50740080360ba0a40594072825044c105947c001882e0369040d070054001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 575520962 1250 575519712 575519771
    0x40f1a210114030303010518130c1404060b0301060c02011d030709051906030c090c020309130603031409133b01110702060a18080109030504150813020402030c090301 73
    0x2042d07607418103030780f070000b40100c1d90042c1d40540c1000140000031a0294414160018400d19106079940d0303a40e080942e0b032081860640782d5115010514117400313100081d00306107807281e04540c500000104240c1e54a0806814040c503142072182203100303204901079506018040341c1100381d076146480c00030070007298503034510f03100d02d01c4801c40c4520034050b0404a03904105072241c2c1500b4a8002c40091030b0404100301540b108100045441d29102ca280e4131041c00504002005450760034068000360342c64805020529080100001c1c55070742010040f070390f00d0214800182c40c441448050003848607241c0001141112042403025a0020b19156000103032420080c450b0103c02c031804065030180f800c00039800038040c400090315620491106818800582040c80e14680d9081d4844c219100794400f81d0000f8030004042c4a001c56040b0b82a04000e0320345400c0c1100d14025103000502c52182c00700074491a000008658182d44a5003a101c82ca0741c01002000346074042e041c451140001000e04280 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 575522212 1250 575520962 575520989
    0x30f07050318040912050a05071b030605010602060c041a0d150312050f090d0609080a030606141c0e01020f0c07140108060a03030c170a0e0103050c040f1a2101 70
    0x48a003064004c00000320350081041d2058280c1403c10703a610740140402d0010000180842c034081480d00b015550741020798034811549a0842c2044429100d05030000c505540c05141031140c0c424811045400701c0701c8070021340b4402c0c0c20a001140700c500c20b620480000c141880200d4820581941ca1030040720301c00e03030b0715a01d8541d000409032502d0043d55180c5a05440a03c17000c43d4a06009503d000c4541c1310b00360001395400c1594032541c1c4c0340c100c1c04a05d000241d49d2041400394541200003054201c2c60030b4805814814031000382d42e207114882d006008166101d4080d0144000c0175015100284c165280e103a4580f0003401d00c841e0360701800e00c962000080c034000c8180c000e500a0300107078041c0b44080d002a260ba420742d10309940c08102044215842030058000e000d460001d60081c0c105450b0700d030384800900b61410300040644e40d01038106400c210701040200189140f012090701140c5403200312041c101d05c0340d0340442060244042281400720540300102d4040c0708508014140d0340240b000c0c00d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 575523462 1250 575522212 575522257
    0x10b0d0609050705031501030b060f0319020406050c0d17010b071109010605210403080105121002030c0304030806010f080a18050d080610080c04050402031815090c01021b01030e030f070503 83
    0x40560705201c640a410000c0bc200c00c941c032009082c02154011a070444415405904407030b000b040341e0040d840b00000030b1b03020401c0c0164080902c1540c1540d40e442c80c0c15002c195000841742d28001040c8a00071036444001120800c108c2d400310080c0003148010b0510f40f02d5a920480508160f01c102c5146804800000c00e94401c443d9101d83d030380c001d9070580d4880310540c0c200000d0200783d403085500b4880c18410841d9900703003600d041c00158420440410384076141c0c2418034016010b1400900614140203407030301b1011030035078000c100580c4640c001c4400f00c1d20108400d141c1c0c07207280756140050824042c0c030100d04c040d01c0c1c0010220380904801e885184551140d040103c3d0150000d865401032100100400c2140e441d05070041d5070490042004221154000310720b180c0381c03841030300c240da600342d0013001000001c04080c071100b001140c00380050b09170304c2441142454071441480d800317818150341e20b80c1150580c50170800c0d5801035000044042d0740c1c480d142815541c0e83c00000040c01400806040c22 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 575524712 1250 575523462 575523467
    0xe0f032508151902090109090908070b0f06030d0305061504081e12071b0914040303060501050705030904180f030206090d0905010804150f02040f031502040e010b0d0609050705031501 80
    0x50f8803409401508046500000036404080c3d4483c1081c281003040d4840041619034484c80ba0942140c822a141a6600b605190980c10310000078000c440c0799480342c082203901c2c0c0b004070701e5840d8a00145800240790351441c00242c001c1c00d000c02e54440500d8045008502d010340002d01006002808031019250b901c004a2180c1c1c549480c0b06a02c584031b402d00610001840e038245446c00e0114003850ba8245685403801d5004954483c0c01c3e14501c07040c030105000030b040d05407080e800071305002c0c6042403400006455141d03481c41009046402036580341100c0604001030b40444504617803104030b502c14000310b030800a58072801655111103038010903c40416081c002d000030002c48030180c41e007243c240d4540d1203110807d00018801c29056407107035200c5070039039418801130014000444280c940c40d400c50401640000a00e0581d03c081481040144442220600f01a044940d1089100e0351056402c20480241c1003036400800103d0821082c044001d410001440c271030121303261600c0c211013104004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 575525962 1250 575524712 575524753
    0x3060105030706210b1c02041a0d230303160315050108042301110d060504110301030f1103031b0c041104060c050f030c070f0b0306010e0f032508 64
    0x8040204a1042070074420070f1840e4000e44c000200d4800c0050805110004030b92446410707240c4a1a101c0500c1d2110210714042c81840f0300707000003009001400640c0c1d0046175880a00c501d000d840340c80035100040380c410b8003521000104030610b0550785c490a102d8070950100083c60704a00c08282030043c2250007241c8082e4420403968140c0d100c001a0f100c1e03440b07442c0c00c11001c51542c208188000e21070007901e2001d020300d814004440c6007441d03071030040c1c181c083e003202c4542d0081440349080020350540c201000090fa41543e03040340107400360b19040d2914241d00044000c01c80c0d01b500020440c4980000340c0e0400403c013283d01c00644204420202c10042112035101c515201007006000a00215109490850030107224504461440c41c4081e030b030758030359001002c016840d540002024807400030120800c0c002011420141c2e82107040c0000003805001c00103040c10300841041491a4003650b04000c2c6094058410480c11b12207140c14207040d000740d2a078051181c15204885e03503aa00c4418110300b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 575527212 1250 575525962 575525969
    0x16120b0115080c0c191b09060311150d0e060103120309050a03030c0504050a030c152c0f09070f020c03190b2a040603180302061819080702030601050307 67
    0x40b040c1c140e80d60207440450540012880101d140700f40791034003601000422010900600800c100506030140d94014081141280c018014040c1000d130200300041203015208201e5008075a801540c0e0403061a1244901884009401c481d06140409206080c08030307446041c0c5c1d02900341c180400f5090b60f825070a440c01048001d1403030b4082502040481d109078004945c0c210035140861800340d8400002d8250000e9400c01d0380d1000640008226001d0001d0700c8c000042034038100b004442030101d401c14200c01181103810b010303080f404c910200c00e6503031400603404244018007020b60342c01c0a5900420101480046c0c0002d80300f0001504234902e40080c0c4800030f81400002444070038011364800c44018009003520800000700d85407c512a0364a0040301002115078094a89461034903400038166001400c4140000d1011a013140200c2c5d030200700107074010311030980d480c4662801142c0c68900f5032040940c01c00100240740c01e50030401d0389001801c0f128001c804a9007a66252020152203445620 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 575528462 1250 575527212 575527217
    0xf0403140d0e010518011b08030105091003260405060703030b010806010813080f0702090414070e04080f03130203030c0106031103121b0a06140702060702010605101116120b0115 78
    0x1007001744c070390050307882c3d600001c061608000000749443d581c9121b00c40c8800855100c0c1c4007000510090602400c00340d03011515204203a5080d1860b242c9116254038500241022594401003e2a1040903002c4800030300c030140040d9030702c0c905402c0090040c510390705260b0000720f078035000c1480b9620a5400303502411350500580c030020110340d140c030005e07440021106040c150901a00340582e60b42044c1c0d500c2640201c0103850b403203484541c2c03d414646103810011028050300c080c0004101e4400079500070042001d02190350f904c5000d0070401c0e004040c14002c2d494403000903603008103501908a001104d210381d2001c58151160000c068030b4007c7c0b91003520b10110240b00f030b005401c041e03650305102c0e400714130140c4401c140c90b1b45034a410345580c1c400c080012409001030020f29581007043c0703075020301a440200f00755801c00c00012440040c1d80c1607a010000864522240c03064240000e01e80006a4005514840e41d112180160aa0142015250101c4800001800300c3c000c80040e404c4100c60b5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 575529712 1250 575528462 575528467
    0x61116081903120203010b070c06080403080402010c02010c060614040b031516110609060f07030e0d0e06041d04030201061208040e0a02040801021b061005030a15020f0403140d0e0105 80
    0x320000540914011015010060300714100c003941c1c50f1510095028080d40014556600d0031820710407615586039001c2c1e0b0810a511040101280e840309826400560920b000e403887e004c07600041b1080c1c8213152000d00041e1a02d940024000c1000d4603840c2c1d040030550f001e10a000703800040644400041040071205119400003c1c40f80100c094100700040690034801d01205038000d10519010045455070180e60211007402108900510382980c860503e18040c007511030b082d14069143c40b00c01e03010b0410300c42c81c0f841444040da20a01501e010700010320050000240c1c403844610b0540c2d040e0b40030340155190010126101d0816414640354682210b8124501071400900c1c1e44144401030042045e180c1c2807001041c1d4070800e000410b1a580c2180d17025a450100a1409091400280034501104554101000f40e40c801159032a141a0807007020705441012118020191149404171a44208006804800c12224040854004181c7c200b03da004484405080d40d0000034000c0860200784103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 575530962 1250 575529712 575529733
    0x121204090b19030503030f10030203300a0918111902030409050901150533040509100914100b1c022b0603023706111608 53
    0x40e0000c0300181d030701621a8888584848110110100503041122140c100009200100ea82e10301800c0e0004588240143d41d01d145500207561000315032015200907150056443d217540d030240d401801002134007a5681c1e500d41c628130007811408140201c03c01c0d40e86c040e543c00741710141303486081584031008032064640380044106003819846010000e08501c820807001c0780085040c000c844c01400320030004a543e01414205000000c000d40216009500b9450b01000c140700a4015a0491284a2a01c203031202d10a1000301e080c442da0b00020382003440c000a100b1400c07000c0c60554100d401e03e640800c6802d0300e02096049004094039000300b0480351140a0003140f100c000105850000e15038081070300320109119078142e03001500c170000c1d01907082c0490760000e100d003503480c2020610b11100300301460a5a0005941680c1035685c000c030645c04103120440300d84e46c8011800c014507807040b0700c402c85035a503038000d201112880c6103039644e0041c2201c07405400d400c15a2001035070351b200e01500f00e0501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 575532212 1250 575530962 575530979
    0x1703070c170408070f081009020a06050708250317011203050307021014150a081e0f06010305100b03010c0f030f110f09090105010207180515030f0c121204 68
    0x440c0c807664050307541c04100c0000c1d00700040144000814a04150f1043c040c90b1030801420410100d0b00115003505195185c2c006070380c0c00b155181901e000b420070640f17451003424240a01d0041d4601c132207121101035040700050740054505642c1070f21940d6028140c5030a40c40762040198284074130386020601102d0b0800083c00b49000c0c40e80240e1520491b6480d0703441c214400d09031a9401c3d51610012802800e102d01c0c404030b0042d40d000300205450404201c0d24107444940d0702d00c03a4030812190400c0c2c4045100b900d07174051111300d5410441e0812129256101d003001a101c880543e10341502c2c501d048030502c25802c040c0200d030051a075589601c0082c150540e07054014105418a450301c10b560344039500f100360680d4010704400c1566801403910340a041042c0b1011070360680146056605c01e020810024245d6503115910388503003080444c2a8480b1800884241100da803070b103034180140c5440c030403000c0c0c0000d42040c0348030080390323a200c0b1241d09403010764951001c40f8210720205403c000602c40300b40d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 575533462 1250 575532212 575532233
    0x9020708070b070806190e0105100207030f051b09060102031b071a030f010f05090c130f0b030f0f130f0c2103020d0305240d0605131703070c 62
    0x40c05800030501c1c0001d20b80e41e0042c2c850007102c2c5a40400c0c078907028130200e400d04000e0f4100b5900c4003200715092500f06a002081c2e80c030140f140910410b0520040b447c0d0600c01d003e0100290351140c1c9807240520285021a1200070410010240d0b202590300001c180c43d204401a0080c0340c183c002e145054454007414940502c2c01e06100f6591103212030000f07003080c00986000540290034429501d07400e188000c40a034401c181e01c08050408804018001c3e40c0c0c80c0204c0641080f042503c0780d98901c480854054004911762082c00f034001e100b10005a010054070042d031041c2c24078002e402c0c2c955035844652b410040155085a40030f8000c046410001d5106070750340304a1401180e0020040d5503807806c003000030180005081da03618004824404240e010000301d40982035909086c402c0b890800502c26407050f8003280038110800d01000200c4584403514000d00040c1c01034400d20080c40d042c05000e0390070852000413030320f032010240300400c0c40040c10140da009084d02da58540c02c0d406c00340c65000c0e03103d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 575534712 1250 575533462 575533477
    0xa1206060516110a0602030a0311130b2b1a01030908030711010213060c0b090601060203121e0c040807050405010f050907021e070e0f040b1f26010b01180902 69
    0x3200c00d007030f80703c0b690360b408641e0320051003540d00940d03607840903003001026200180300c100c190300424070441005000d2504160242d400c01803e4039203404240005001e4a501d0441402c107943e03000c80c1e50180c2079201e40003400024008031196042c62001c5004504803030088501611503601480880d02640c410719100d1001048400003504000105040c000c2290840e444680450f2207000c4c00c0c0c0421a0402465a10180d050040c0c6095850800e01079200c1c410400700c1d032000101c05000500400c504d040502c49040c200c81883d0403440c010003024026070050040070000e00c11800002101d00c2c00c1d00559041e60004520b9000551a10051206120015204c4030550083c43c3c054100305003142c0300035001442100040c02580c0c60200f400c901540050509548103509000b007002080384a4072054100c450401e144154146034030041901100c0b607000302e0004e28501d0a908003c0c0f40301c10b440710804c420f0f030008110fa5042c64006680b4005010011404140810810800283c555028140a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 575535962 1250 575534712 575534723
    0xb070b010b0a09170706140301180f0221010315020c0705041d0604081201051e0d03110f0f0f060103050709020f07061d010b030610090e12040602030a1206060516 71
    0xa41c4c8500c1c8a1007246090b06540c2e00c5035004100800002e5400b8403e8149071000440f2246594140000c00c206451980403080d46641c03120802d1103006603a60454081c41403800d4041250300b44020740d010004400c0c40252400290036960801c107003403500c04c8a00e89070121000782840c61170f0006100203000c2c0b01c0c1401c0c02c01c45102460184640090098138422881807050550b136402044400c010501c06800841c090482c061109502c0200c024141003c0714048691500c1c2c2c2c055481d00300c0c0c06154500f407011160042130548840980c0c001410100400c03e0410340d200e1614a000445e0754460901c8064642d6112060400075552168010079034600b024003694a010000d48035502030300e07074094125000344d503502c00500b0501d1003803003020318042046010b05104d0501c0405000104541d014800400c1d035520100780e5907400810500d140320740c0300c0d9109902c0359a5002c010351250003c60804021807030200011242240502c121811b40e070464542c04e0602c81c0c1c209040d0a0382404443c122803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 575537212 1250 575535962 575535977
    0x501080c010806031c270b030a0f09170c011d060105150903030711010813230a1a0f100b070320010e010608010f0603050d0e0303270a0b070b010b0a 65
    0x5100c59041d80c0c030760780c0380180c0c8070b1480f5040e00e403403240f0503c106c464a800e0404c4080c00248035841200302200d41011102d8004a4600c110390004001418240402084800113445801140070180060811581d22200820880c894041c1a4064144d103a400180c01e03041a0014016483c050385501518200c04115031705008452020a1031a4464501501d01c007000710104451503901100142d0f200300301e194a02003168a9035102103019005002500c10340c081c00c02c0101c5040020800d8901841d04181802a80e00444624006145040c0c90901c2802c9a100c0040c02482c1005c401034103d43c840c84074a4900402c0340c5040301c2982d6000e9036a044044010858001c40c082400707440c0440040c00c0000403081c2c03420784007508440c004031090600504202c0d04002013000401c8111050341d250400954500b000030000e402c502c561841822030301e000d00e02e50100c81e00b100065580990080c0c4078101040c0d207449010b4240e01a4090061160085100610540201c08050140d00231070b42070200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 575538462 1250 575537212 575537233
    0x306101a03041a0c0d0e0304090f1404080a180e011e0608312307060c02060c15010e010501080714090d08040f0b12180a0807020a0b0d0509100501080c01080603 70
    0x24180c1e103600f00c6e00c61540d480414180810b8a092054041c610507000d002c020401a41001c5c0900540041001c0c102280102e0100050381c000d108803032801d946039441c000c01a8854146892184c400c2c080c3e020b030744022804078441000c040b801041600d9643c0c94003a030700d5070307a004055440d5913208408610007050200201810387c0b124104101d01384658085402d0140d600d820444040c0e82412000d4560f01c841030030080fa03500101d00360007560301540c8440c1e5030010003d0803031600803065840c1c0041e49611000151010410009070b0590303c00340c4c0c8400030741e200c0080880f401c1043c01962150780808110344101c0313140081d0b0641a072486001c0b01c03820107603190f01c08681202d103a4000c602c0110300050b10b440e01c0d05034450450348043c3c0c0d0108195040c9042444594858081c40c000b0964200040e0305400d554503026004020203912064641da10b8100e810f140180030262024285403145e8411618040c2c3c60f40140c03416a18040000e20f941c0b04403000443d861103000d043c044e014040c404150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 575539568 1106 575538462 575538487
    0x50906090c15070501060e011509050a0e0a020307020f061f080303040f140307050a06020a1715041d030301030b070f0216090f02090306101a03041a0c 66
    0x2107444008520b00540100345d10740100380013990f0340e4000a0000312180c0e400c1c01102d481d41c4d07080ac4440e50341040c8000720145006140f40300c02c103100050301c04181c40d406190300103445c2c411a499419003450003420182d064680d41c0950240f01040441122000843c000620b0500010744c40e510309134580001908444000074085103c41820244401080094500386900b2400340c504040e62854000020340c03081c600b41001c0b44000c0100d0103036030780f003024261141c41ca425507240a510314004200c02003030242c1d401001040e13140d0301c00c4840e1104201650103148609103805450600e400c1c0505400c40c8090090115809107544401d60f500c82580b510460300501004642d1000c0c2d10340b110007a0007440d40d0590188241020031110700c072070300800750032202098606804c280010396566603c2c44116800b501c0a206141540151170f84482010750101000010754200412103022 = true := by decide +kernel

theorem cover : BRFrame.Cov 575359712 575539568 := by
  have h0 := BRFrame.cov_init 575359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 575359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 575359712 ≤ n) (h2 : n < 575539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
