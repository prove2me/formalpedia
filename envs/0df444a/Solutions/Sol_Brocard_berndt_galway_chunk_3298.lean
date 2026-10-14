-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3298
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:14:38.721181+00:00
-- url     : https://prove2.me/submissions/e0c8afe0-acb5-4254-9fa6-9ddfc1d5c1dc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 592985611 ≤ n < 593165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 592986861 1250 592985611 592985641
    0x917030f03160206010503030301030f02090a09140106030b091c0f1e030905190804060c020d0204090501202805120103030f0e12100c020f0a0507030b0702030a02070306020c0c0d0803 80
    0x306c01c50081d0306561441d0b440350079481d24a03030003e004107403600100360890b0858006400e442e500c4440f03104000c8029070a00e000f00304510040d503280c290720000c5140c07850045520024500141c41d00d03211201310340030030b48441842942400803c507a03100c00c461326030300726010301885201c1c642d80816090914281310303207400742100c2248454011040e0030030002c1e082d8004c41c0c046414500384100203481b503000085020150040107900903050800c40e004014041d440400b4441040a4040c28801e00c0400e40425010740741030005502c540c4113001850900c2241050760084881c50082e2500030300c0301404400d0002030781308a001c100b51074504014039401c02c03130a1903440c0c2c0030b0700d900141c581c000340f040b0790780c0b6001820000d829a4441c050001da51003071203403e45601c06541181c0c000b03503082c5811984c821036480291213504403070003c0340c803040c404011142c0b12481940145005825a250751000f58840d003882c90081c801c10072140d190362201c8806407071150040f0f00031601c9107840303000c0c60343e420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 592988111 1250 592986861 592986869
    0x12010603020a02100f0914070e070f121137140306040209040204080f030301051005091008090f011109040c0f05030a1a0d1b0602010c0917030f0316020601 68
    0x54014062800002c3e4002119990724105400102c0c00b1403004052000411a0714009441c0c100e194241c00b901f2500007505104860f90050443c0550b1b584000c125108205000810b0004c5c00074440c001c01000203422490441d0512120b9910301190302140524441b458204800708161541d10050150110003036040c0044080c01e100042101ca940c40740e4041c48010401c62042c1e42c00304010344e450f202c583c140c4015002c0c0c141110780c01c0b102441026501c0d0000d201302d6200d0544c0200c1c044002e44101c0542d000b150024150401c07400d403051094450328002011640e061007595028130001e0803d0143d901407980312034010390388402d40014001611060f541403028441c1c0003c7d44e450250740f00d0100c0e540028215000500348801910b03030891070ba0b8404006910004001424081c80980c40c1c4405c803180111501d41d43c2a56201002d900382c861b6400c2003804101012020000b546440700c124044400740c50580346000c014269000d00750300180c43c01c549003000d400e482d5494580411401d8050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 592989361 1250 592988111 592988117
    0x6071409010e1e01080c0f0d05090a050a08070b01050f1f02120a030e0f070f0b1c020307050414040506010807110a0c08030a2304030221010c050c011404050309040510150302120106 79
    0x707c801078401200d03603c107011103290410355401c000f590083e01440800b022039880025501049000d04140517540c1000308180c036501d800c00c00004131440d00180e140383c024030203007411100e6800c0d200c1a40c003540b41000c40304154000d041c410034140341c0800c010b0841d440341c1d840c001428a44010141c1c6000d030b030586d060480f41c0c040c000c01c0c0510211380c0d101c4c8046030003a00307446590303c6214003665035180d04480b000789120300201c1441081c542110282003039403402c100b521030040c5040100015074109a8405005c9050140800c1582d48179030001140f1080759411544000d005644250021809910503a05504082a08507800f0307840f4040401288610303002000c001c200c090441c915204610009100e0483d03072198144034032050040a49011160000300005840701c14060090b0b409101000c16951a01e9031001d804821144010301a5410034015803d00d51060b00b44030007000050110020921900d00018044d03890801d6000c1d1018960f4015071500000c0000100000c8103800080034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 592990611 1250 592989361 592989367
    0x2a05040905151b0a02030307030c050a0c120c050a050c0f0907021c0306150915050403050601050d110904030228050a150e01060902071406071409010e1e01080c 70
    0x726000080c0140a1414409090059201e040007480e403c15030041d20350100c400443c200c01d585801001031031141030140c03014003a0400c00740d030803035491040109c90741c0419500114140410506814060009642e08151307104400d2901c640c3e281800c0301200300c030345501180280c00301d400d004071086422041905c510942d4100500065190300074907401c0b401e4101204480b200141c401d40006004182d00000c00c1c0204024281c000c0940c03240340140080307602c511030700c200c099208004840881c0c0e000700107845141d00300404c1212904d0130110980b443e01e00c42c0340e0302015a69a0381c0c86401a40700707800030b2410b81d2401a0f500105c08080c0f040d90031a840f02e281103404944041444142c035a031204148030100d03d555400b400506403004100b116610f4141d0100d500c01843e170082c00001d024090f280c903480890000340b552003c080742c00d00c1c001145028001060b110b02000780c0344a190505000c0104441d010100300a03000801d24080000128901c1040f5940c004200d139030800d810420a0345 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 592991861 1250 592990611 592990613
    0x16081b0406080601060c1a160e063a060f0e0a050705041412120913020301151101140c0d0f1a06130e13050f030414090604092a050409 59
    0x5180c0405100fa602406000d07106001040380c009204207c00b600e564810b9010b08210780c00d1441112402d84410104020070b0302400b16217084000e40d111020402d50391a0000311b403401f1503201c0103400f2000b580e01010165040c1c1141210f01482015040c140070340d44ca000e1414943c18400900506400000c2c0e02e00018801841c1e070002c100c9064034855401c0302c600b01a41ea000c6503240b0041d00740320281d805240c030306c049114180c00060400410032150111b62022030140d03c0c04a20080c41460000381c00100b80f503101600510450a407d02d41704000603031031708210541440310800701c561403180e690000b01001041007038403036010000d561110800c1090720420b400c0c1e5240d5452207085108803000b040710201c9142d2140ca080c090f005041c030f849810308200082c01c10241b46c02c81e0496060184030710806500800005440440300c2811000244040703000a00141007005000c054105450324084030124180e51008940d04e40440204250340001c5042c2804da0326041c0c1120344240d0524520070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 592993111 1250 592991861 592991863
    0xb03070f021e06150619030614090f060108070504380c1b060f070b0601080f101503020904051302011e0806150910050c010501060f020a031116081b040608 68
    0x2960014101e90140c4d2122801d800080c2c8074082c07000d1541204500e058080c501c2d07030303154102000b220303d5051003180340300c1024100042403c085416070950207154000402542c03040c102386821078081d05007549811388034051143d00985001c140c0c00b2030901e40080d62011040c18007003454a04e0449420750402d49074128458444084290488401d04040c00450155480008444400402080999071101c89280ca410340d000100d40e054041007410000bd461044198a032620480320b190b1106070050400581150b5107095442036020142d00340a460300b9601d13a8031035140600101c43c200c2c0d0303204003c0d200040040e00020700d250032900c02c641031703044400d03004440d150704000201c58011543e840020581c40500810100c1a807142c00700c0704005059030400014480005100d000b882241c1c0c8410081c3c0d03c03220b0012080005a01000811021a21510504201c032000e401551028140da10f00b48241d49002e400900b0150011044090b03401030903001001e41c507006403014003119107000116 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 592994361 1250 592993111 592993123
    0x804030219031e2309030d030222060c05100614010e030f240c030606030c0703110601270b0a060c0614040c090c03270201090b03070f021e 61
    0x40c01110425610030101400790402c2800c400101d0008a004240f240c002030000142c8200c03560184601d2010081e11240078003194080100a0002c25546005480403002503004000c0f90304500f244070360542c40d220440b201d600003468142d13192441984582401810b0803c0b243d05008000e281c403104000060b01e0010308402140c007401c0200c0e5110000e0302007030620343d00c1d0341d40c0d14840c015100842c41c050800c81030700380329012282001229030f5070240c2180040c44180c803403540c04041800003910752040a802016103500c640781060101e5083c801c1c580ca00070003a00401804690122049495050b45202c4056040f20180a101e42d6000314003084000106000300010032030411070250500000340c00000b01018141900102071a0030b0134040b00008007401813a0109041143c80240e4034843d005040b01a50140c0c8404400c02c0c0340d40112140d100f42c110200d0520507034540c002003000d40b5001440c0b181e142a2150075002c08200c20003400c0ca0040200c1d224860b540c1c51100d20070110025903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 592995611 1250 592994361 592994383
    0x30203090c0108150d08070501050106030518010e07120f0b01080f190c0e0c13060509121f020318030d060305060708090a0b0703020408030d06060201050a1a06030402010c02090405011401050108040302 88
    0x1750407581203981003501144c465544c1c060203175820f080c00000d1f0329501d40e002c41d02c01c2038912010300025818002e0f003400d0b941010080b27082e0742e00140b810b0023108061003803680701502c103021040081034030307076103e2207a818264003101c1e260b00210140a4211802d0180d0304241c6440c040d02c410008a0359140003d0700114083c00d400d58031041c0003c0c60a0f1003820842d146481990000d00c600da50310b00c2d00501c1c95000e001000c0c01900480c03142110188009210310105003491160b075611181040f03800d0003908014030081480702d00300343c1101c1e81070f41803000b85021441010003040711070440c1070075480e140020304003c0400c4840d508101c0100e01c0412541c002951005110361641c1300c6641c1203004c0c0c002d0350050a181d00000581c0d04c4907a010340d1204080721045c0d0001d0103542d460b50f03003240440c2c0c01c1034403081a250000640003110324100c00215801481410016190380494002c6400c601303085608032140d13907680c04a00b8101c00c0740384a80b40181000d00c0c008081d8a0640c0c1c00948610040d64 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 592996861 1250 592995611 592995619
    0x60b0a0803280509090c0918010e0703090206040f0608090f030a05072603181506151c060806010f0806060a030f111201020901030614061603051306030203090c010815 73
    0x304141c10b443c0f05038111407002030004e00ca0162820b00c400c0001c0c40381e210f54503162246030003800c2d250148c440c10340454100d81d1440c000b012160789500301500078024062049900c5181004081500c0008040c0c9201900d21541e507680540f50401d05c1d00e113001003111116426610074044404080da1000417590165404820346e10b007840141d075a0801c4d04085501e080701c1d900302104202d10600c10307943c1c440991602c0700407180c0c2c3c4602007001e2040c1c00303410380c0c07201e0300040120048050141c24100621340b40d90083c6c00170b9044e14514410808454042d0030640b030581016004110141c00751407014003030f1203460043c080900748200042c801a40900c40180360070f41d1025400140b0015083398030340d0384000703045154102d02120009000758480408603022070315000012900c41548e0340070030156100034251914100d9030813810cc030107400c4c440b803c804014040021918040500f014040103180c1900d01580301e040408066083c175842c1c02045040000c1e030000c04c003021a459403681c41d0307183c05075 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 592998111 1250 592996861 592996927
    0x120702120f071215060308030604091a0403051b030406051b010b040e030904140f0c13031401060302040b06030402090403030b0d0b1008060606070c0e070c020d060b0a0803 75
    0x8000141070a022011003585402a0100020703081115004820b030300b4030501c0c3c501081903c2c41045012103003d40406003180c1c2c402d02c00250503041c66481444460302488140344200780c1d42e04560004c031400c44044001070300100e28840e60440c421381c84282c0ca002d00003d10305050034281e0081050207101d00140c24030b0030b000100c01044000f9444140c2108000d0414040102c606180c0f0780d6aa00442809004034945011f0040c409402841d090050760070080d10801521a82c50400f1681c00030800e00014500850000002880c0040e503104200132401c0041042e44c0b941c01001308454441c8101070140e0340400411006036140c0900b42c2d44036a042c10000303000b15446022590041d40041300904c81c960b094180000c040380c2c07107003501c225658081107442c030b03a0307802041c82007a0103418002400030a0a160900000507008180c591142041c42d102d0115030359900001c0002103551401c1d0343d0160f581130f481c8910301b84048418013a06200d80114500b0030a00d0181c185840c103031070f503244501603030b03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 592999361 1250 592998111 592998139
    0x20a0b07022d2229040204030809040e0f0a031d0a030201020a17090d080706050601020307020607121403010e06090a0605011704022701090516210615051b120702 71
    0x400000c1074204490030004c10300345242c9011901104900928402a000c0103108145018000c89007036175803011003641401412400e0002900c3c1407004800c4c1350240b003c134050100001c000e003505880c025511400c1d084680e0380d40032081000044424052008070b401400543d0700014281c101a41c0001c034014231104180100c00580512000c556000704c000c0130100c180090384c0080c010550107020100125121040166580e226000009402203400d0003883c000c9144840c0106200c0c00f00d00b42190310101100d004e895561003600480c0304540c8070002d20001e410060b26440e448142403000b003150500300f4001a102c01d085540071101800c00c4130001d0119196644603014295452240301096121081e4140c0503000034092a50547c1c900300001e46030850040741d81b000b441e625194190500152800c5010307811420842e0142c40352111310026043c00b050944070300d045426640e40e0f440d0009000c2510182404503216a8254440365024032248010b10803240b03010741c12200c8100203050 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 593000611 1250 592999361 592999399
    0x4020a0320100c02030105060406120f170d061511061b0c0a0b0603062d2d0105010e030a05070504090201110a05010203061507210c020a0b07022d 64
    0x941001281c02c40500600500c03125004003469071410310031002400196210b01c2440111591485a2104c03400c1188441001c85c11350481225000e0191032607100940d405042440e043d8804449100c03110755503103040004400850343c0c91000c800c14509541e00c801c10f14030403903890b10003500e101c02e00e950200701c1e0740f4240c10304011140c0c404040e1041c0c48186215062660842d00c04480d554002d00a1800003011503c603045409185d114103010140303001d514031448880c41c0c100405141100800c2d15a04041c040305850311945903c8080c4109c10302d60600c0c0005000e0300c205c00340280290b00001c10400025030100d900c03803c1d24029036001890342c1141c0012114000f00d808110150300074030b2117620074090190001d601c1258103440e02c0000c0c24048000035568824004050582d030b41100c2c001e1025401201e402059000d01e02e08909196401d0700000c070641000d40c000c0d8841a00052150308508051015088100504403455480501541d0815558070392070540c0344100e620a52034595160 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 593001861 1250 593000611 593000663
    0x61309090f2306060105180a0b1b06091f06030204020d050402010e060a09121a150301061a090411040b0a05030a0507020307032a06020d051906050d020d020a05060a1707030504020a03 80
    0x1340240b040a020740c0c1c441609d8107503400180c04000403800c1c100b8600d10b614001400341d00403c1620000c050020310441035520402040d40a8041ca5444d4100040940d07140d001500100965100008841c2000d200252425001c03681603030150702d060202d08005508407a2100031074488003442d5a04115616020300c4081c1240705000102c0c51401c04e0005044904042c511300e030006400070800e8607203450030b80846960480016091301c00c00c1005070140e0030107800c0100d80940c0b4004003414281c44e4841c05816420401407034000541c003108010943e0114000c0d82e4004899002035071906078540c40041c024040850111403042800d501c000f40100d2148070130300d142d9081242151980108101c12014010903a045600303d0300c1c5900c40004011144100c80403144014902d500f21280c1d0f9007440042c04c090b05060ba8802c1c0c6190b0000b609441d03041c010483c0c1c01c8503980c0c07400381c80382100e44241c003184050014030030149000c00704401038a44140703c4041d240c02924041082c80f081d903e04e11050 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 593003111 1250 593001861 593001907
    0xf0609040504050304030c0503070f09020d0e031b01140108060708070c0b0a0501080c010206150d080405100504050112090503030105130e0a031e030b0f061309090f2306060105 77
    0x40c41d0908000901801102410a4910a4a0b804441c950760b800301940d030800c5004192030003400010400c80703c85281c0c01050310b40300c2658041192043c811302503046030019a003040301c0b40d17000340ea4032802503420f00c030300c2120b0240e0008020155052240e0346598a20007040d400030b00080300301041d810b038002d28208d54010b900c200780b10303a5807914003a00e1002d08401e11030500103220f00c00d0302400d50b40c00032804034429001c040c0a040341d1046031080004411541d8019036902c0c40401000c01c0c035842c0c40c00d04610391200340c1c964665603071909000400ba40c0201000346001d03403134084000700088011046a044a030101c40d540e0720340402080c5680140780201e100d403190300c500c1c7e00380c1c8100b60308403450948000141d0308000007010711200507000d450142c0c0d951980300c07a2000c2c0720001803800c800a41110700f100d02004e214591944080000c4545014040d240070400e8500403042040000c5411107084901c800d1041100324150100e45e55680074200d0340c1800380214180b14181100c6958451003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 593004361 1250 593003111 593003119
    0x5120715020c070311010c020d17040302060c0d08071706010509010306083a0801181407080603120703080f060310020a1d01020703030c14031611041a0109050f0609 72
    0x41d801000c0100c0e0b50751418482105c410000e40800c0ea603c5d8012100c07110819000b80c049400c40c0541d55403003001030303c01d4100804000f0188804405611202d000d054510350110040c041344a500f60302400c4904014500c004104d01d00c440c0c81c0b2013880150b5200e411040c00c5c00c1c01a215182c107801038002c1d00e243d81004505104020320b500c001d0440790601c100070f50303005c11006003241051500411841003c40744502003076280303004121500040600328080c81c51102c0000e0505c07008103a82d40c074100166201c00009907407105000d403528007409204c1c406d00080e2100752524410381d07400303840d9240c010512030312400003200140c02610140015481e6000040c411551404180009030614108140050f200c80d0702604621103940002040e10135a40c054a4180098096030348400c150141103507900124003090109a401182404000780841c1c07155400c1315000f56854103000031140e11070030045415071414491110350b41c10403d081c0c185d4a041c0c40c0c0310050b05112020840c10b205614013a504 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 593005611 1250 593004361 593004367
    0x901030b0d030e04150803091c0515010e0a06030c051903060c05130801050403050304020607080d060605030601023705250305150420010e0307030b070306080105040512071502 77
    0x400da80080400034159044a081010016545c07240391400c041d802200e500d64030402c5481c0c00e61810f0003007000c1329180e4141800c070f0000ba1f580c034542800c01400f0b4040c1c00f40c3c0000010300000030000e001c1b5900172080102009240d1848e19140550b581d5032003850302507134002001c2c0c3c0080104071740c04d20145400880500c0f1100c03900c4070082c00343c1e001c5140c04171024095900071034059018002c03036004607055a201810b6496540820015074070400c02218106002c000403000c00c070403030042c4001408191a441d0b02d9141c110006810250280713004440400c0846880021780004e003100d03610307000341d0a00582e407200d80e8a000c0385448800040443c1d000060026524869400000d00381600d20800540e079004c0c018806038080710005079002010f541d0b00c032000300354440d41c064031203102c043c052404146103c00c07000070904090158001b981d00d8803041c4100035440350140540c400520b1034100800107440c0a07280c603501c0d20b1000305403c644080001d03440b401d0005030301084039800d281c1c00d401c643d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 593006861 1250 593005611 593005613
    0x90603091110050a021207020d0b07170a020405040f0b101202040308190e09090d18090f0506040b0f18100509070e0f0609090a0b0a171e160b0901030b0d 67
    0x3c1150080c0542100521850540c81a104114400e80e91001d90240a8083d015816a03030300b6003036071004140034108800d01c0002145200314074141d42c0601c00c824801a600c03820182400242c1c2d4242994081d414240b0042c040291100c084540d800d030110700d40610f007880488030002c0079100d65880507200700e2022034015a0310300324101e20440c0030000d4451603102c01c189020310406490444001a1a03082009481ea2080c01409201c2500c02c60803000c500c07064464541e01c0403555904005040305644508208842c20701e403103041d25650f0112080501d0a03086000141d050076200d150740d0b24500784034042460f0b11268141e00c1e000e002c00410808840c44d1482c00100409550038000b03110301003d0101c1e4660b4240602140c9000c00054a101d4060b95001d00c5203019241130400a60403541d00940010360403401c001190041117418060306a9002d42e000d102e45480d43c2c111059060340110414016604c1c80d41300c130800f212000062030740c84013415401607004200e461180780d0000c0c0c0d02e0b001a0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 593008111 1250 593006861 593006867
    0xf0c060105121204060c080d0e010f05010807050a0519090905030a031518180b1e09010506092a07120206070e03190f0f0b0f0a0c090603091110 63
    0x25060301d205030707504000d014041c101159542c4820b01c1c01907010904200a0048620840d0000d4100b8000c4404501c1c040b030021000c402c6070a042c02103240c69658101d078102d41c0c00390b0b00a65004008840007480400d081400003004500c03103114140c818a20415039980070508803044000400102008204184060400b680c0301e81c0400c0c2d1400019240c00b14600414405031820820f0761a00b0082c001440e410984030381c02481000c10200403200c03162020000100c0c144000c5100e00c00d00410110100052034960f42c06000c05000e541060b41800304000403612000304482c0e00510f5400d100034003020041c000c1414002c07039103007800c036030301c00080207001c1c801c07981010799003a4840e44c222407550f514010110b8041c400f00790041e41c90b401c40d003c08140c80241a640c0c1d02a20301404074424142c00c1c66a4010085502460071144494090100040003040c40301d6254040c4809000340040c69130320000808400c100d000790024103940e0780c16442071014980140c8400b00018296504102c4009009 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 593009361 1250 593008111 593008123
    0xf0d0f1d370c0e0f011203081e1f0b0903060406051807090c090801150b0c120403060f061508011e0e0718140112020a11070303090905010909021804080f0c 68
    0x211101e101c0340041204d2400d40c0b40c001d4100c5802c121402902105a03400701c41c001006481002d205000d00040318050001e152182d0084074540040440d0b682e0318090700711244140e5000c241d101d0000d2000b0482e0ba200801e6075680580d0040e40000d90355540c9800102260610402e01500d2250b0300b03001c503040155a104130308001c0c558880380002a40c0340001402d84005190552000144981c204440400301d4083e000e200c20040076640c0c818144d90803004960055803080e21850307196a04000000c00300d1140c20050300c1000100001d420b091407018040395010321418820800001601c00301c0d1880c0006400545178208444140c0e041010000f00440c1c07801d168808031180c4554006100c002f50b11b04140b15190607142c0034820302c0042c040c81c0094020b000a1020302c8020508100400340a01940000e1846070303c54560150501c00344000f1110160002c070700302464015200701580e00c20050300d030510407041c0c80c90740360390f9145040401e6000d1001404c82859010404403082c40021030300e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 593010611 1250 593009361 593009369
    0x120a0b190e040218010b070318050d030509041409060115020307020411071a151c0203070f03030e0307030c05060924070b06060f040611030f0d0f1d370c 67
    0x18090711359040c40c01c40c0c0f144100c04c0c414102d81e6542004040d0010303004801d00d183c9038052010b1210120740e1240403030b0798094600c03000c80000d0b00015a010191038180f1034080100f0200ca003100c440c0c81c4c4820340d182d48070018014070030041a04107140b007601c0e2007041140d8031580d01a00520451440c0036400c541c0d60010307902142d5081010583c0c8103c090150103c2c0c0c41801d180325103003002296802808401101e24110f4114040007010440241e1020858180201010b4507400049855420001c008031090f0740018466004108200040385015041505681d8215030003580d800d981d0380012046641c2495110705004d5414001c0206110032000d046244e0050309002c0d901c0c0d032a00e04005062042030614484008180401d10090f4810f00e40f005040200c031080f07a01d004a0008554201d42081a130111242d80b0398003102d013600c041c0c1c0502c0c0030921240440241d10820f00c1c410549070380c00c0030721160000b420b03424402060848406081c9440d110b55100100b40095070424030610011801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 593011861 1250 593010611 593010619
    0xf1b05011e210204030209010806041b050603163b0402070b040b0c040e0406060f05011b030f02100e010603020a0f0b03040f14060f100803120a0b190e0402 68
    0x803881012200801c0c0c004003140d11541c03041410030701c00c103002e80c091989007070b80210140c3c280804401a1108812640600410350041490781b60528181728071903c00602002c10005122041000c1d4a44a00b92604028901c90f00b229200290404460020010359413540b001400381448803d4006c03200358080c00e44541c0c3c40340d101c4503880d500348001d91103200e0b002010038084500041c04160031031034158000c000c00c1405440d0581e5259800150b40e000c5d601030720415510441000054040d03c1e07420000c01081c00c040c02c0c901c01108410740300034080000a002c2c03204011440315118400c1c0a0103031140c68a1070b04201048580d440c040c020001404100d02030002c1443c0440c0c42066201c044c6c0413541c8041d591807a641c0c5581e01e0410280c0a002c0407100109400011346554005011140c0704902121441c0c02520308060303159118200c6038000344854004011040c5120010740040354401c07052540411142450408a0039040100e07000002c0800341100c08280c0c1d030702c001091400303240211 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 593013111 1250 593011861 593011877
    0x15060801090b0105180301020c030d0506030d0e0d06050619030303020304060b0a0f060c03020c060304061e02030702030a1d0a080610080313090513150b1203030601020d0c0f1b0501 79
    0x3401002111802a4a540443c00c248141c0c0382c402101c5003000c170741c101c0190016090105035041649142c1001003003443c4191500300300315050808001c81c0707002801c3d500e002403d20502c43e0200d0050800d41c031000d0a5a611440003843c2500c030404043c02c90b50a01000d409400e540303090050003504103840c00c035229030503d0a04121840d1114500c4142d510f660144100e69160580903901100e40b03086c110154019008041c1c000c1d96810042c0d031055000e814042449203005040d030a050081c401c400840c940306000303000d0441d40c0001928080e00700c078100501e80b2524042e01d0410107000c5080c0a522003064100440d0800d00400e0007400b5140b03008800da03103135881d90361107522806912030000d0b80064628040041110710b80110b900703c4140022207050031920784507180300000e004005040b084d100c03807000c1c40900742103200039202c5090380c0141d03041d403c02000007034940d0088621030f0100900000c44909000c2c07a49580c981e41303544022a0031000b044105020b03841c194610940b408221f40c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 593014361 1250 593013111 593013119
    0x30b01090e0c030117010b1020070b1c0b030303130b070e010807050f1b2104030b040807050f0d080435030712360b0604020d090615060801 61
    0x114440501550401d482d59007140c0c02c0424400d010800c24100005542d00d901c0f02d104a0386071440760340100c0c6010b544280c0c02c1c0000740c52201c0301a84021340c0c20031a6000303400c00c0041071503407030542d84003110008070404240d00560b101d001600c010103840303500d80400824081200070015004a0700c0b48600341030062680c8640d02070740d0f07461210780c9442c08a07500c00c00141c406c43c8540001c201c03009030310005d1418182d60920a0013220024401136403550700c1214801c41d4900c0812000c566004400051072401c0c2c1590384214555002500040040c0070205416003001010300c174844c12040510704507244010400ba009140305003d070b4081c0e80800c00304041c0c0e0ba806a9030b0100c8090050102050300400c0780010380f01c80a079000400c9003007003201316050020152402e0091240300d0305c034a03140581d85040c80c0c0070b0135482c032780c496403038030645901207240000a05c52645546d80701604560058440c0229400d12010304410340c6c0050400d86052100c9460b47e45519980040d9141c9a40b8407007582c0c0c803 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 593015611 1250 593014361 593014379
    0xe0a1506050403120804060e060403020d02070503010209031203040f150606030c0c0809010f210212010902090901120c03171e04050f0d0f06020a0f0314060d0609050c10030b0109 78
    0x40d0f408090814100301ca0f4100c0c10750b001d00e0702150010300c15100012288003860240b803d00e01d0542e4110010380107a040f05803055070412140c0c020b080300320021490b02c10b801c0000b03036640106640c500032580001c00040c0601c580e200c1064000b9410041c0e07106d224070f82c03000003001003905001da0408a4686204510090310802030281a40d030b120500d10301c0d02c01410300640c2e00f001c2c200c02d400d0070043c0700002d0584014407050361140f043c07201d49000d81c5030110134801484900c8160042503003180b0610480d14543d4807070a00794112040314140302c2d24080f550400a0481880e604007400b0b075281407207a10841030032a801010b40783c2020510450f102201001307100d00e40b24501c00d455011104506001092030400c0710304050f14440d40345070015010b99034136001642c20041da0b10012580039814040e01301e80500603840800e65405507034800e1b190101c006505141c1a400140803581d80b2008201005400c000021040000415014480d024600010040c140c907c1c901400240502400261001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 593016861 1250 593015611 593015617
    0x1503070b1e07020f0409240b090c1204080307140403030507110405190b040f0c02070305070b030405070b2508040f120b070c0c03061a102c06040e0a150605 68
    0xd0f00030030064489111004210190102e40e1040e80c01d003070300301c03144480c900301c101c084580d0416001010880d0b1240720100140d002c8010010148508104410314281c00c5010810717904c103a1000400d601e946517504125692903d01124607a50340f80010301105068010000d0280c0503c142900ba24004186060006a40d001e40381141e400403c0403030341310740740c170281c00c8120f66030750141c4002240e040140016040c1e80080e03500d00056082200c0c18424008188005800b60607902410341c80c6050030fa03a150340d6511103100d06924500301064540b0020980c1460b070034011078000c4443c80303581c41410201d60541c810700c2170300f06456031342030700154011b1500300c816610707034014003040020354595000303070740207018110101e0340d8040c004c0e03001c400074100d0b10410502401250012040c04140001d000c0d500c0008130091040c0003a120701c40e41002d045100c4000103056082040d241d02c0c0d00100443c80300c0c083e54010f411403d00c00340030012030550f40c1c5d01235510301c1110300e0140207181e51010250b400344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 593018111 1250 593016861 593016863
    0x30a0513080118080c1204140108070203270a0806040b0f011202010e06030c090a08010903030b0109140111010e010e0c130b06070b040807080f0304020109050a0f0e1503070b1e07 78
    0xd4600d001c0030b000c02c000c00054003201003298152240c011070180030304082d61241c0c010150741c009841740d40303072a13591002e08690302440be4001503281001d260400c4020b4a1004402c05200390381003107003c8540c40d1041408010f0030003408490710740c1060301c1d0400e44420102c40384100510303c50000140c000f484039002600f00d406031901e015450307418041c0320440c0d0000b00300d000c100c401000310040a850300309500e0000e014520000450301294a001420f680540c06028100810314606102e084000100e403d1000001d00300004000816085503014140d00f60b41012075519004a0741d000007008649c80203522000ca80c03c0b1040c5001a0b00e0404a44900740941e4214409201100000b50303070000158020f4003689040303080140a40d2103001a0748104400141003070302006210465802015203030146c4000c4901c218000d00300f0309484400d500d14800e110b25094a2130100b240340c0101c2e1514480802c025065031811500d0708101c2040741e00105949a50114550101d013480030307500b040d40c02403 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 593019361 1250 593018111 593018141
    0x609060603012304090807050a062009010f18080703140f0d050705070305191a0c190302040e070c0c060e0d02040e011803081f03050d1808030a05130801 67
    0x5a403c00b00888081c800c20090b40c116640b0f9103490085604507014018652003080181180c00c81450814280d58440e0322070a85400b181c40c400c0e03540511442501c60a840a1800c00c80301200344030110b804500080d240700d03820138020804aa0b03400e0204481c4150ba0080700500c44081108410f140e82e40b0034000b1030301041e04001d4840404034410002032040c030f40103100310f07048107840e9182e5900342901e9044e001054080d94080e90300700103586422142c030041c21405464949004602d070303041d5200e204115071510b518044403110141c020350603580076202042e5652118900300d14007412011180c41e003500e0030131264200054003071151001c1180305c04c3c01380640c54296003550030f01000d40f00c0007400e180c8075521361500300081060f03000d002c0072440c025903480486081641c2c0d425103000c0c820300803050800c11034006001082c00055180b4401e401442c0000c001c1c80116040d0942c1c0d12180c0142d20103002c001207030706003182c1c81000b42c501110000c0520802e00c1e41c0b000524202c4540481510036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 593020611 1250 593019361 593019389
    0x3010e1f0c050415030501061e0905010e13050103060b0312160206030c0415020715180b180924010c020306160e040f020c010609060501080c030702150c03060906060301 74
    0x2122919401c01c0c41031a60504119040544461005004198210140c00069a20f03001002400c0d03100004821088141c2004460344d000310000a050030b07054011241880a1784214240c15180d0300741e0080301103e440810801942c5900d09400940000715031b00384244220200c043e5085000012107070066940000e51b194910709a0074000c0c9a00000d00d441024082403000049a05a2100c01ea1503442c0b12360141187d54280030659440c6a01d4017051000c1103082d0718075510881c01c2c101c10f082940d039104815502c482d80155070129904601c0f40c020b0704507202c40c050003511207100c6171030382c10182d241e00b4000c1c1000804004440841520300060340c1603101301c0c04184800c15164041c1d00c40442d0b4a410741e10904c045d800714050b581c103c0034861690f5400164140340300c0e42880380101a0402041c1802030300c5c60500000d01300790015092420106000010492040c000c124841803011407400050461901100f602110340086507200d024501d4400040c1041c640b03407044038182e601e035400b8034031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 593021861 1250 593020611 593020663
    0x90f1a0f010920040801091b18020904090516030c08011116110907050406090e060f130e0a0b010512070503190201020f030705030a110a0f030806010e0d1103010e 71
    0x400f90074107090000f8000c03541e900d0020504404401803014000d28400804c0e0003802d803500c1170307030181c070520070f8250018450820700014218556454103131304001c0c000b58441210100007070041104101c020070f54450b08901c440354604111441c0104e900813596859200d0f13507844220f09031740c40240c8000d001a0104040d000c001c50000024501c0d5008e050b2403049212180003061440c64146c0e031a07404510041400c222180e4050391801c0545940180c0040c24244400403801c40384c2c03c941c0d40b40c81070545812103002c03000c460780414940c00c0c120048074004a0241840180c81000b07006a82c090500c1d070350381910842e0000b410303034103c030070190052180610b040384840d100e09141d101281103004011400a02060420140c0b40d402d0007a030186942e0013a10b031000d08240c01c05200700100780c225005200115006900c0015601d406050901d02a5200e0004a908851344000350380d202c003000b254503085c841540c0384440d0300001540204140301a0035200c0d9943c1c012103206062080c1d0f0f010303000e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 593023111 1250 593021861 593021879
    0x1009020303072306010602010b100302040311150c06250e0a050103020c030909090f0c01020f0309090411040e1f02040f0b0903010b03060f0901050f0402060706050c0d090f1a0f01 78
    0x5419a180781c4080f800d00c00802c2e604a003460802e078050740050b9181c0074005000d250060300c040340c61101d420110301e05807a66581031610104500c4081c0700d0007441031052065502c80d0300311002d04042c241520b24902c1c1030080b0300c44090502d0312000c2c110500303014104801c1c1c050311505a14010040041d4001c504c4c1000450195000465451290109002c180340c079807241c0035005c0c0107562140160000034011400c0c545003041031600c150441d4010008820b04120100440304461004c1e05d0348080c80c1d8850030224607040b605803203150040d2400786808542100400c94007417600007040e0042400d2101c520760002d80c01140141e00805802070b0041150000100c014000d40002400110f0861165000241800000c40c3d20110f10103180040080f8a0000c1c82110350212107038a40c6001800c1a4002c40d05030b00860b6401000c6690744c0c0041b5110343c0082c01030f0340720b9003e104000d1011880038500412004000c400c112507003490340a50310403640500034440c1c41210f52040c0039000744e207019814 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 593024361 1250 593023111 593023133
    0x91109040308192403293903162f01060308031915060807030513170a09090c05070816060203010b03010503191104090c12030908100902030307 63
    0x1000850b90361402c8a51461403001c110545071001a94942c06455800c003200050004161540e07890100b055190802d42c40030240c5070005c444406d07001f1000c0130402c0d46075140c001919400702c4054000c06088001070004015407040d4916840d0418072151904140c6844140c16041341203071000c4a071080c03032a4580c105980c0c06000881c004181540d0703a4440c004181d01c10b0710148100f00d12002888001103960003850708011600c03080d20716403441e0800c01806403201410040415850b03101141d105800410300e210880c0c1c1240001c6a0100d0500a62074a540480b0350300c000b00e02c1d190300015031603100e1b103d00e010900742500c1d500d10700609070b40d07900100d511110008104011a40358813011444600c0514040c1003440c1c14207030340e54101b001301450005e640421250013070110302c038180060004ca0510755000e900392004284402c403881d004030450200d070040d00c3c041c000c0004900905510101460803150400181c0e00c9600350031200c9020b81d41988030194042c0e00400030301c80010803410f00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 593025611 1250 593024361 593024401
    0xe1303050f030c041508090613050a061b02210409020c0f161d0402010c080307020705040f0f0516090312050405180f010512150903091003091109040308 67
    0x2030381c40c0107201000c404854109580d00c0c6844200414240540b0400503800c0085440d0303410903030018a001001d240c0c0d915002000031600f95904070814041040c20040d441c03520382e0004083c0600700440b132080c400d1080c0c404904005200c3d40200300300510110341121009685980c115240c10b0038080520040d40c0542900e060390f204050300003000f004144500503580c820310041c0c42c145840c080500e0603400049490450b101c000000341700050307030000054100554410041c0791260303203141c016410190150300c40364100742010111070560b1100d61046207400000041004a6118032a0a8070000c02d94058000820302550f02400400c40c1d11105030b028500500d00356282944401c0442c540d4a028402c1500f000b180b00240011910030b0803c280c09007038159034050280040104650780c0e688032482c1000d269030500c000c11402c00050003122205000500400d04c02c0c80140c2d401002440c03202c800340e0704019061162041c0340b420218141c05203400d9076400c2c80a86580b4075042c201c0c409034074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 593026861 1250 593025611 593025617
    0x3080c1b0f0619051611161403010e07081527010c1101020c03040512100608061005101e02070e0a2a0804170403021302180102070e1303 60
    0xd903240038040800ca04900020400c01805003070a010070f00c481154000c2c00340b685003500f494100003029200703612210415640c3e250403031424206201c200c0c01d044884040c40000d031140340d0003007103007078880c4291188428141c00030481490f00604150321141140580c43c1d41d90800503080011100645026402c166404440c00400000a4100800c4914454200c0469445451082003503421001401550103007000135880e2005480e080c030703202d1045001d4140b0802215042088120003001707c0406041030ac03108110003a211000350350f65072012141982d081210341c1c404516408e021201807010103d540b030b05102c0f40c40c1a060380710001c86012644046108140c40090325030101091203000365181c00001642c04503180807030000e840f10700345142100003c9001c00380a01d9000b00040da10903040204200300c241041c00050185c4501d52020754000d19850308140c3d145684d80c0101900c0150000116a40d19100010381e03ca510034071030200c050000100084803640306801c18603200b48645 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 593028111 1250 593026861 593026897
    0x2010f051e040e06041404032c03160312020a1e020d05010507050a030c08010b041a450307031509060615080f0108060130060f0b0d03080c 61
    0x6030601d007042e04107521038000c004a95042c000b10342071910444044016542c600010b07440c00d40c178041d083c400c4480d41f6000710136650114100c0c0601d440540ca8200f40c000701074500c2c188105404c290152074071301040d18005012419040c1d00c500005440f200d85601682039441066210082645900c404106a0304510704043c05000a0b6080c82a24482e040644486031985c00e0309070002c0440d580e00580030b081c480c8490051000804100c155400c80300c1240740502088074514034582140905040a441060b0a850440a04c1c40b00c8c03410350040400802c440c1007030305c901042e844c001003400c1010b43d01a0404e0009002092241003c0451200e60b484041400d030707000da582d00110b400c80d6200030301d0480031030030000425900c00301181d00014554141600d9504054105807640d1041c4030390140b6603404954899868001d0003555011031800325048240e51396802c0100151016001410205140000f442500d1900c10355803540c0540503a0b80018699801205841d544d2000300c52a103009609 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 593029361 1250 593028111 593028157
    0x1d040f050a06030b1303080415060b0f030103030e09012303011503080d050a1401120201142a0f0d0e06071b061103190c0c09020c0703020f06030402010f05 68
    0x6802218041c0041000000321a85982040b054000300509101c2090a810301d411001c29800b008682e0465049243d00040f0004000000000c1110341d21000d180d600100c4e103468000c500c4800b03103040728041c0c0c8031540413000d100d08105048000740600892460000106140700d45641d51000c1c1500003d0f00001d140c020760401c0803284805644211020f0b0b0300056400110380c603030b008441d000742804405118543c6480300c0300d00300e47d0050040e040041d008121500039a8451070244c880d603c912810543d0b914120340070544d114181041184012a20744015201c0a000007611101c000d100c1c40170700120a69040c040b69a0000000016444030b0b090180c00301052001e2940784075884030f414226200ea2804102402c020840c420007991604184142c1ca2072806500b400b040310300305480d25100210316880c0141c12194030707403c84c040452002c54a000034a40001e5401d083d45e0085580f004400210310821031130b884220f400900050040c00c0e442401400342d0068208504100b070604444003032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 593030611 1250 593029361 593029391
    0x308040915050a091a0409021f0e13060503010e0f1b03010b040c03150e010f0b03180114150a0b0901030507050f0c06040b0903160206091c0f0c0b0a1d04 67
    0x4103401c9208440d0780d941a100000c405c0e03103000d04c01005c05031001e01480520740c00284c110f60541c00102522015652000b524a00c50038622003484070060400e400c0000c8010310f84020840341c001c00c0d002e58030740104025142400070b00c1d1803102d5640c0303004046600c4c103030040c0c08540d0b2006160359050b64aa0080407425560ba000fa060180301c99900099070b03409240540710902c00b5503103e02c0d841040344006104540701c00c0350400680f4010440a1768946941031060b0140794102c04007c8503500c1c1c0304140ca45034070742c40700e038600440c0034000c002500c500c04820400005010b100b00d40119804104440141d4001d07000154801c0050030f18905020810030341d02581e500018625807140c2048040100704480c0000094016101c0c1d0000c508102140c10302c9200c0076800e034070180c400c11002c00d9012840e5510510044901d8044490403058401440c3c51900c0d070508079000ca48425502c0c4d000301d142e4a800b42601c140c0d02c03031030303582603078050b0201310740c4001c41105034020740c1080d1101d440fa180d40700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 593031861 1250 593030611 593030629
    0x50106020109170a09081509012a0302090607150504060506180a0c021c05040503160b0703142a060702010b0d0308040602070618020a0915090213152601030804091505 73
    0x10700c5d04005001c0c41c11040140c21104031122b125002d080c2000980725104c02c0603520603805025050050340c82c032040c4d00040c0c441c0942c001c0205800c0030214403c030369420302d41286002c2c1744181c1e81804540c5504041042e0690343c003d044800035100310000740325591541059807010601e006490b80c4070f021f254102c0002e5581000180031900c00641048181400c1154809014002c000c0821680c24001c00043d544103500000c0c0400124410742d00d58200a0021034803008640002000100a02507441004106410b111002406220005071809006004403011001c00900400507845907542c1910100720141003070300c1603a420312101d00003a010348500b6034940c801410007007001c8480c0c0304000e40b104080c0c10030302003035090440d02c04001c1d00c006000e0342076910700200582ca8202c503c5038004809210f9001202c0c2c142660303410321004c0d82141b030f4000503100b41110351104100315203000d81e40500a110091a0310790420042143c1c8540307a105580001082c80c100101e55a40c40c00507030910 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 593033111 1250 593031861 593031883
    0x320071b0b07230304050105030a0b0a271401080706080403020c1905190f12030c0804090c091e09022503020f0f1513030c08120604050106020109170a0908 68
    0x184a0083c0a000405030080003010004000031490a810000001e02600002c1c10130414651074102c0c101d280d40e076181114000e45074a03103030180b486803802440c40580a880c044040e105180c1100b444a40c8002507015041c2d0f451035000b0411286480d40460321404014030603800c41c040e00d5044034a5980d50800ac405040c0c0296480026500f840d0812411058510110341a035041c10420000d08080c2d11144048a041407003440c0075240904098404502d4400300505000c00003801041a030b09533407015902400d599a000b40c56611840d6283d010392810b42519040380480508109041030b0790000d00180024028545015001d429505e08103c4000412405030300004140640b90034200b00480d01a0b00c16401080c940703a4031144502c4400c07018260041d041c1c3c40080d40c00134103010b40841407416a00a4a5540d544028441d00c1d5400c0301c146c0d40148140d00b01800000d00302c0c41401260040c43d00b1034950840d80840460385101a80010340321000d10181010000d01c89030180641c507100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 593034361 1250 593033111 593033123
    0xd021c170a09080d0c0b0916030606080610060c080a050c06090705100c0b150d08040603091e03050d0b0a0909150c020609070e07120203070c030320071b0b07 69
    0x6040e480009014010960403030342e610707032014402544e01d0340d125240c005401d4101002c0d0141e92110104036003800c86034091184812008100002040720035800807044a0131081030b0341050700e0700701585c00c01c140c880c032038000001e901d940040301017240240203007440141414518a0b21709001c3e1003034100f031022550030682d500000c00c1041a4100a0ba2041503081c542c5016207030305070749585c1c20300004400351000340828254200032074a40c5608080b408079a8000705410744440e40c5ea000203002d4a040c800464490184425500301e641c0c0819915100c142c0c180c850b6400c2c5022b104000000300355543e82035500000c424000103040c507245c403e8114440c040c50701c0040560307854189105568001c240701007150300071402c01c580e07030002007001011390b140d150388001c80d034403203c0d07045450f002d8902248003060f200005002c0010303004440304031214404d0703d0500111104800c1303001030414400176107081d140b08000e5400044c582040803000c440000c211041c4e16900c0343c1501c181074000e040200c5036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 593035611 1250 593034361 593034367
    0x70504120b10290c1207050d0905011d010e0409120e090c030103030e12010b041506030e0111041a040806040803061503010302030a080705250f140d021c17 68
    0x940b40ca20031112025024a9409886034030054506003c1d401401880c8488041e0206032000008014000303102c405034041c640d00c0e1035650700d060540d00c412040c4150390210b4001800052954000c05c8c4a089549072143d20f0341c03000840400640e0101c2c210302040c1c0d07003d5a580700400004e45038042041c5001000c0d07440681c540011400c0c000e0520340582943e41030380303090004100003a88210b613018a440266a905091200300345c0d00c901411061808a83c0541007001a08038000700000d082d00300c502a6400384030069003000614202c90402101282800d030400c4107020902e44950342d500d05282100c0d1584c589503907418064180002500c2c1151608400024014589020751180035003160058880d4507551460b8000390f6075440080000301a444041a4242409000e100c240303d4050050080d03501601e420401c1c000c2c5121a0040d10198000400d0115000359480d2410300e08441c085d10201c2d0480e1160200154a480180f600b05c0c002c02a1140350b0016801c4070180c5150b030911041191 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 593036861 1250 593035611 593035621
    0x10110f0d09091e090206040b03010b270a06210f0207050c030d050306010e040b04140f01060215041b050d0503040504050a2d022101080106080321070504120b 69
    0x816400300303034000e0b54203d09002c850102c54400100c00c20b078040d400b0350000340d1a00703244007045040c019a84803000c090800300001503080d00d00001000000e1211600701280444801d000c00741c0401d280c0c3e11500516003a10510800d405000d030f00c80208114046020100140410042a1001e0100140c904c940214041041160400c005806214120086c014400b0f9070700008045000082c481410090070700000e039010313285c941c06600a01d1000d4018000142a10010600dd00c01501d10b0b03081e401c2e1020001510602c0800c115903010b0382024125100c0d00c96480d003401106494220f4070070122211000101030741c1301c01c64008a50700c500003540e07c80303141400308000c550303000b4a0201e8241c286040c001c14841c0340c0000c1e40c030700c1c001d040034204c940302c0010096000740903034502c1084502c0d400c1c26000888003d40711140c12554400020300c000703510742151316124010a0722080c114201003411105e01c10a00045961004043c81c02e141080c0e039600d001d0644d090041030580309580d103a0144a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 593038111 1250 593036861 593036867
    0xc030a08040512041409090d170606040f0303080411040506130e070509010321081009090f0c0f090e01020909040816080304080a080601090b0d02070206041d250203030610110f0d 78
    0x1a0b200d800c40008d0210b021000801426410b032004e1381816002044001544580d51942918040c082004c00c3c0c40c10700740c032464082c02410301520142d8404410610103a20f0b8134285c00346520501c0083c0c9a40070740d030405055400a400711130700071040c3d402454400b04542d25031030300960095024550f183c100580d2141601107201a80d00e114040200010802101141b1850b07050b007101d400e03003000580740c811401d00425515000400401c2d210b06101c000400f0510080284203440000104200c4040700410342401c07445605c000e00d4202d001000000c0100b4140d034050710300c1d59490340740b40070030200030f0fa21318105038402c85040302c01030404101080d010b640000c0c101da201d0400c0c2004580181401d040140782c0c0901881d00600f1034000403c0760864540c10705a4004081c00c0c82c18403903840075407005221141040303941e0140b5902c200841c00d50f00c0c0366105031100100039900074603e161030721030600c2059501d2071001002c1c00704041000100700420001c600050380c1400c064100428803850003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 593039361 1250 593038111 593038129
    0x4030201050612032109030d0f0209030f01090f03030b030f10020307092c0c0c07030f1103070f03080d0b060c0606011b05030f0c0c0a1203080a020c030a080405120414 73
    0x72000f203038010b002c1460440c10602c0d00200303c02e0309a072461590b544044020345144140e507510310f469410100c07410060031042d000b500c2c841c03d04805882e203140800281ca070891700e02071005410f0854501a0002181c060390210b002c222001c1d083d910484c40c2640034600e44034802c1c03400b00b0403079400010018513580c03201c40a806098155001c030b180c08540441a207109010f0b241400b082100c0d003010800c921a90b4044810007070307154081d9080c050380c0e4202400000b6041100340c2c0c482c2200302d4021100e10b8046280700c2501c0c2003c88024009045448000c065007013a884500341c29a1442c08814664030080941400a50b59000304014078100c0c000400c91158000f01401090540c1e070004001070011042d1141100c059807600e4491741098415031400080e4420207401986640010901d4858030504c1501a8041d484005203a01d4000c00d140883c403980d014605c858106100b0048124841c1d01c0c0c44e07070054022400c0350010324826203c00641e6002e580310a80c58844480c107900241090300c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 593040611 1250 593039361 593039389
    0x2303011d09033403020f060c0901120c030209300f0307021e09160305010e0103030905040b032503140318010c0305040909030f02010e0d050f16050303040302010506 72
    0x294401505049034140d0703680c000d805512800b8940d00015040e44002d800b260700b14405265510000d0b9500ea0501941b20310368003c0701c2d601d42c0164000107103180e040e6822562200e006030748207035840e400e10342110020005500352030300f019020080064196a001c401000c00c01c03101c140d040c1c288984200300c02c403094008107420419080440d503030303140ea40007000755800a41c041c0c0300440201000342c1051304120034641c855500c5070031784007030004620402c045424040555201000507076251150b050b01203809200041c00a8044a02030100b41040e42221320800c40160849801d02a04460945007880d4680c00000f620782c111410070501c81c1020b440c0141c145c503080518a011454114501040b03803d001960511807103003441402c143c071910071030340146402c0004100d807225615000703140b400d0b0112507000541c00c100001c0126a000b190500031244e50741c8600b49440320228003110680c01c030054007802c2c1d201d41e058140220310184001d6202d10f2003030340001940c0c50110f003081441951905 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 593041861 1250 593040611 593040659
    0x1060e01030b0303090613030c0303030203100f050f060d02161407061803020d032102130e100306180c031a010b070c0302090627090d022a01230301 65
    0x741890035620f01108650700807030180d80507550b500c03400721181d08003030701a40020100342c0c40000c000245589940030714098200c5580a10510707035102a140300445040c003d1740d9000180407411009898000010050303e9074402d03002d4206044080a081900703034040302680e01c14021641440c003080306200800c0540076608004d100e00b400903000f0000b84130301b400006c1c0500c4c4804442c1d8281801071011010400700540010810315903003d98078040c0d00240d8501c80003020856004c51405840c01200340f01e0034400c01140440c52840e1180c10180c1551500e0a03003806503144000041122250b0040166008103604000d1000326484010310000590006030f030402c00788207560000d003c0502220480790121041c02e010348407032000446681960941c14200399103103040d07000340803c610401d44180300043c103690030302e103000d003082c1c0e200c4100340c8048440383c90b19241c02000d200c00040021240c135040c50701102c9242a640c0009280203c1c0496120b00703000440100040e800131116520980d241b90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 593043111 1250 593041861 593041871
    0x905090f060a0c020601121b09140f090309040906180c08120f040621021c0509390d050f061e070e150a0921030c02060c15010e01060e0103 61
    0x14000039101c5d07034103000344c803401c460010300c00f002c0c81504108080c0010002a4155031107030344041c410002e000031100080c1454007600020000200080c9051103031045e407003d146445c1d501e400300402081910b004440440d40d030218007050402e540c1615076658070500b0301c1c01c002414800034a1a06814000c88141d4880411003459400b5802050750300f220841d0828004924100f90040310420b078074038030854901d101049419603190100d0b81043d4000c8003e004001c2521000203a50f01d0759988502c1304c01410340f81800c100c4140f0140c031015000050b28000c0d0708600440c2c1c000648940c0b05500c00d9860740d1150750007981c1c2103001d11065402481c00c585001107030503910003000d080c0c003009040406000d6406003401c25030b10350020901c0712010900160360764001d030381406803a200c85400307142280315010300d1480d0b80b6030541c015111855095215003240701078a900b0040c0e96030003c4030440d02030094a03a000c00d02041490101d010300101d500303020352981005001002da81d010b1603902c0c100343c209 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 593044361 1250 593043111 593043131
    0xf050d0e120c0a180204050409060209100c03140a03020d05101706040b04060209060904060b0307090f0506160206070b0906040b06041b0e0102010605030a12180b0a0c0c0905090f060a 80
    0x20f000d1400c11101c440c40e01500513404025030100074001caa104640142c10706483c0410080264001d00d01000f049844c02c0d22201e50003821900d0148420000b40419000749055601c00f00220152020383c4143c81d015140c001c5d618651003d4401c155041028948004020f011408210301090402101800140a0751030107450320010a40043e0000c1d0046034009000d010503101c5100b01c41c01400068003c0c0000c6a0302c0b140d48486601c01c507040b80004000d4100440e620f08001e00031021500018801030809990444043c003424000300220b90282c003c1080e01e00182168809074030492680340588903900c0c040c1401144a00000c104a100e28504008580303540c601542420b40785a680c40c1480d1401c580c040140d00400c0190842d0342d06105542c0b8002c1048030b0302c810030318084866174407079804ca2107505482c1013200e414003031481d400c030082c04401807e5114007588000b41d0300a031118150250303110102e00480d5801e44490031550047c6102d5100f0400c200010b07a0042c0060208029006c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 593045611 1250 593044361 593044369
    0x50715020607030207020a080d0815100909020d06030b0a1a01031404110105160803090f0f030d0207031202361c05071505040f060c020604120f050d0e120c 68
    0x1c020070100516a0214001081d916907200d064060401803044031550a4000405400c204c42215844e140c3d4858007003c0c0781c90f00b4084e50f9a000c0c1411926050b040030306040b065800f86d0444c0094020065440e100003002c00c44c00d80e0814001d000e007020010301001d034000d41d443c1c003c0211121905150824080007038025a102155a125401a40900a1b5500d80d03004032141c1c403070f19000b040070031700080802003400311900046006a11110031114401800c80b1801c0d1950034114001d081504140702003c581c00303180e0001c100581c421300c1c0c0039545030005944c21003280c0090b4010070340074800389000c0700c42c012011803e018085d0305a11030300138014010b000807034058404514030a00b070791232100f11041040c20400304d00903141d00c00c00620017684415000340b140d0018455158444460100040e1b114007070324240b80040c0d0003030042440c082c10301c0f844401c0300f46d080c402220601905054100801d0050149145082d143c1c0e40741054141070301c0400240382c5115002e038107503401c00011021140d079 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 593046861 1250 593045611 593045623
    0x10b0306040f42060812040608101d091f05041a040203100b010201090b0a2a050a0e060d0c020105011403070f14010c06060303091a0307080c0f040306060f0305071502 73
    0x20b5080c411801025003d4244003d4030f080d90120501e84509218503d01030316000140c020340e234065581d15030340c4e55901c0c0c01c3c80c1040024031a107448801c1000382801d841060311120342d8002e0844049404401e190600500022451207450003005c1e902d0040c88100410b1030103c8658421010b800c0c5041d0500ea0002600c4442c1c90303034800e00036690f541d820420b69000b03402484a05030894180c841601d801c540703250113400703001018002c00301c07034110003600070800900e040500c0000341e5070a420040c01c640140c881140ea182143c4c1e00c80d101340580d01e18081680912045e501d4aa80003140d81e500d86056010000e00034030105100b41c2243c503041c07000101c0300e640c0f07030200c4401c180da070500c003117440700145c45803501848003803c0300d03042c400044145600a91078800f100c050148401d280200040032010a0005130307290000200107401141410304d0b1000034008032a204110103181c90b560303503a1031007111000e9200741440b41446c02c1c00c205004061089200800c0602640001c1038811040251151 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 593048111 1250 593046861 593046953
    0xa02030d0507300f02030c0703080c0a0c1106090607050709060b070302030316090317071e0b070806122d01110703120204050a08010906050a0c0f11010b0306040f 71
    0x2515442ea1850072800f1600191052400316000b10b55904000c4070706001c1354004241038000c141e4240c007181d9a420404c040707a1080c003203540c401e01f80f075041d40d940410002040c21011b41c8141c041c42103c1d200c0d40d5440013008820f10450051032054a084201001d841d069480806d00d82c2c800d22444000c6074001c0126130740b220500415400c2e000412a0a1300e0b0700000e90405480c414446600300303d140c113264018010b85018003010204180e01c4003586c03001718541080100a10340c2c10000c10192401540c01507001280100f883c640882e1850758035180c0903044c0c080c803004141c3c40015850050181540244141032600240302c0251a010214618402d610300102005000d14038010080881d60541e00640350091040681c1c0b80e07215029030182c1100324040d52481c0c58000421914201ca2103100340d000c0458590500c40c1200300c605540e544640300040910b5521400018401d0360240441403240d442503581d00440105420b01081500182a804100614006401e100f10900c00d200a84171 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 593049361 1250 593048111 593048177
    0x70501092106090f15050c0a0305130b1e06040504080f070503070f120e03010606080114040f15170d080a09020f03060a290906010f020f030a02030d0507 67
    0x1c070304005881c82840429030000782c809854102d481d000c020300c03000204000d900840800720a40c0400754180211001034842c102286420030111038000c0c02034011517403100d40007a034a040c0c2d140a442c0c01050740f2045503c5441d00c0c0111101e00081400000241c4e04040d055a0070040b074600703079030346261034800c80b048040030000124003c0100314007001205e14466110b450440424002d2908010f9010b80450100201c0e02c0c0100418690805104000840d0000e6403454030603483d001c0d00d06d880815030205582c00a443c4d0100780380c0c0204a0242e5081c2d003200001c10245070386003011307174040000d25900320001a00480407840c211035100701000d802c2007850034002607440d540d10000755015151520181c16014480c108401900f01d0390000d00c0b40031540c5c070580134140030070342240d03030102100411541c0402d213440440c0d00c42d403150941c403001c1a071f10300441d0390481000c0705091958010740c00d1200144c1c000556210860202d0290310b03004129800c0c006000401c0c41d241c0080740000601030360302 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 593050611 1250 593049361 593049389
    0xe0a0f02090c07210e180c031509010b07050c2707090e1f0501020c01050f090303043b07020c041104091503060606050a08011502031209010504021207050109 69
    0x2d8140030404a4650550180c00a07404074800a0fa000a100502e1400000718000c540401e20354108019880b5412a6011910900d03031740c7c8041c0004142c1003d0001c00c0d501d883e00b00d00758411303100c207540300c1d010f4101c0811442d280d9440c0c3c98034a00d0410702400709400348040103044040c14445c01d403190401000b402c0460315964555500b281e54000e5139002d08114051a014001d514810100402e90344101500f111703101c40d119001a642d500e0a21401400a04100509444118600050869404014103580c606a500d9a80756401d04101c10440d000040010200000d14409140241d02c0038803044400902c1c035001002070741761b5a4505c02d0381d001300e4a0301d03541d210000c4200102c0d009001c110b03e082004a450701c4d00d07120140036030b01003128400d04e001001300301a405041950380d0061280d42e50386180e170034443d071b50752041044045001544010711144480c0c0c0d25150b0782e01e1042605c5000050145000d004200502d00c85080c508419048100180a9640c2c03258001b000c2d95461a50600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 593051861 1250 593050611 593050621
    0x6030b03030d060e0708012c060d02040504031701080109170a111204060207090605060f0d060504050c071b080624030f01050f3106090c090c030e0a0f0209 68
    0x100350b208501c150040c041c509030002c5030800c1c940d20010302807840c5aa68001c0c07680c031019850105101c84034040e4804406288003092820b50001d6039a0080c0091b20600b120010b660204046c1c2e02c00351000c401103074003400c800d10315101c286415801840844000e21160031903880f01042c0d04030504401c00500700015071b01001e540144482e40c131203000407040f107294401080c00c1803410b40080c054000140148a800240302255001d42400e944004000603d000340d503010514856200003245103030552207001c006800e42da0742c46150b1003031050444030b039594112450080564841c01943c1010182c1444082c04a80720005500c0d52104a02954034000c030020040358102c480d03034040ea07544c9403148240a9460f040117400c41030040858880400d060b484818184902000e400755610b02c105c040c400c00030220300d00d040c00c0c07019907016607030015290100c0d4403042701000b03260708503c40c03264903550f200c0c041c0c607814490241d4110104010b0140c841c02039890310000403a0903000f0b8402c0c4a11400700d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 593053111 1250 593051861 593051863
    0x507031b0812070806010e061312030c05070f05010e040c08010504020c0a0f1211070b16391e051215090a0302070e33030307050c03100b030706030b03 66
    0x20740d07200d00703601ca01102898550360040010804444003400a0031f01003452006080076001c2d10344403080400c0002889080181f2000e61041d0030500b602000810605100442c406202400103001061441001c490500002400841810603c6030086140500b2079041c3c1d5400546281500c500320b03405070383c3d0341c500104285401001d040103011280d14558060030481013558494028a40c0d444600300d403615009e80380d40b265005e12400e05000420400100c00e0014295100c41e0070f486400440c56000c0150b0603039200c0020703007480300101c84103008a640d9105100c5c410400500911761000b0000c60000d4640945440502c14903001d143c01903580304010b1802e20014484109840c0039069920300005a543d0303d1031511425005805112008140c0c0110b00700014400d4055050384100c030f0400010402ca83c0b903800c00e003c0a50300d040380490000d03a4082c00107000483c014002011a01e0383c402c01c043c2828442084050290b01e84090781d1103540700810b943c005c54285e81000a00010f080b0082 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 593054361 1250 593053111 593053117
    0x7020613080d150306060506030c04030b100914100f120602252603060108040b040302070b190e1c150b060409050108101e0e1014060306070507031b08 66
    0x2c5180d60f41410411050b04020b03030343e2181128002e40701070200036540c41c1841114070040c0d802030003000d0100000e1010882c82d0741640d4011400c40d903842072b510384e07868080c1708580c0c274403072000312400c0568140a1085000106500076040f40d8210840309468080704e81d05d0b800c00317001e0040c000c42d0085810340c2c8811144010745402c4040410040701c0e400180361501d50300d16034400c403104120006400040019103003051701c0c071a00040c0c42d130444036251a280ca800a400041c0114118032502401060f0803146a01500c5900800e000007107030079980300005008034110500c01401100b514520410b02e04450b00c0e000020764004900d069003000b10380c02c02001e03002e035000550f0045000034000860060030741c040c6048883c907038140c0d2071864005080405a483c0c030312803008500c0064007a01030440540e400303040c60000c183c00716032440150303a251400743c0d001f54160800c8164400c04100803410184110f5900107a1f51400071300c0c3c42c000d540d02810f42c050840c6500c540d4880803104d00200041c544c11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 593055611 1250 593054361 593054377
    0x120501091a06031203010311010507020d120305061c17030414061603050604051005041d0f01090215030702031911031606060501031806020705010b060d140f0702061308 74
    0xc40070246080c01800c9425400c2a601540a44900d05500014415500540741030301c4d40700700e440411004c0e010045480b07800c20002640d000b51902c080100041c0030740406c1694010303588001c169807911008111800c48803245442c20b420ba2091030070300060300903500d08823070700300c024046840c4c1c3c13100e0500c078102c0081041c498680e8071600081c041d0700018a483d802c0c0c10a0b680d90140b0165403100140b0055450030f0f503548580040050b0140702501d881c0c0c000b1a180c40c1040c1030a5200c82030000e110345805140a610380d01a5516003417403095080c03800510321034071424901e181c41c6007131010009540707201d0003c1c40c0b160002e40065000400d8400ca0322a500e142d44042120344401501001040840b000701c0d0480c0c41ca803038201c0c0000d880d40203000c5d101031640c2000709680001c54035107a100282d8440c0504072003a560303030803402107160751350800b50455094032800001c00003409c40c801035400388007401940032044140d041121081d800240154403100b500d90380d401c0900b0500c1c2072413142c014454 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 593056861 1250 593055611 593055623
    0x1110403080a180b0c060c1903111306030618090f03030203100b070b09010e0f0c060913050112030e041104050d02130f0c091e03081e07061b110712050109 68
    0xf0001640c51070f200040c01c010761101c010f80b5581e48a0840505141c401c1c0d14002d182c0b400b020300c68544140c041e80c0544401c001e4040194900064016980f4081501d50000c1021a6039034505100c0c0c1401c045101004800e540002c006d00b0005860398109100306950080415400000007000e5034490701021009050440545031141e44c0d625020002a10481d0800c102d0361800c07001524000c0001250a500c0c56074030094040e4000742000e0101660042c0d4030150002280f40403242240c011740f04843c02480f40300120007060748a0b10300180540140214180716909040690500e120f840046508850048500e442d4820151020a450342c1c4040006042c60345407000f00703130400070560000314510362596200c1d4416034035010610904081d01c102d070042605109000c0c00050341e0382c0c0061a40c41030807440c500d01d00c00640c0d4000700340e81c803d102c102c60740c50f01c891183e20070100c0b680e0800c00410316420440b400a11000d0000c1e81c5400c14420a2042401d1544a10502900f075014210035601702c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 593058111 1250 593056861 593056907
    0x1424030105240d0c090e1e0a12050304020915040e06040b070212072d060c03020405010306090b090403230304051c05031b03041703070c06050901110403080a 69
    0x745070014480c0000d030035032120310b06501e0780a40c145003039044942030540c08240c9030306050804201d00020050380e40e10f4a0548100e074240c024110342d5014890050081e04001c02e009446031800c0503c000c4251009410b02c0018414440166a10103030158071503000b03940110000c40c8100020050052100462187d001d54001e110500241040e07840c03098500e40c013245d604542c42082600d0700e1103462000b405941c25a800c50007078507403020810b81101092105030500340700300c1d1039090489810100520104c0d5000404014650300340c002c0d032004000044d4204130041d910008543c000c01d00600c02030400107003503030700381a0400c20320050869003001c6600e95180d00e0241380061761545100c440b0740c03100c0c070380c45568045144101c00f100e1081101c503102c0201842c1d440085880d03600701510482d800c1c0c0c40c60004800e002030f010099849080c99603600521f00c811400c146080700c02c0502401c42907414400c6200c981c1e40c113036003100d044a030b10a06c455607481206c1801c45481e1001800e14462110071 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 593059361 1250 593058111 593058121
    0x905040b01090315140907030206070b0916060324080c090403180803030609010e090d1107030807060f0606021216060b0303030903030405010b010201200d111308070503011424030105 80
    0x40d900c1501c0001c0350403070760405c5407952075a45c4d0340d920151100070761110301044540c0005014013892604103e8850031540040540030f000c0c1003404030b2740c000c07034004bd540c1d4800680c0010480781000583c000700c042da2800c20306003200292600482d4a80398000e000b003102143c1018414a003040711203510701c03901483c09446900c40c0381c0300d40c01540d41c43d1045020100209448131008140780c0904040c800030011140800816504000b0021112103140910000000440d0b50f1500a2140d00e10840c0c2c0002d001c0c0400c030701391044440d9608413108542c0900d00c2010f140c1251000c5031044071001041e213141d8101c0d0300d4888058842400d5031a010300011050000f0036030008041c1d80103d100e01d00030f00c046034203040121300703c50034a00001502000c05409902c55122000180041c54040381d011400c01760307044226035142d101852812901c0c840810800060200307201e100e024100481c024007004250340f0701012001005890130090f042900501c05582003d100101d004c10000740080c4898170705 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 593060611 1250 593059361 593059403
    0x1060c05070f1202031606091e0905070c06150302010f030b030111040303051c020f040b0d090c080c010908031c02030709180b1c051b0402090a08160807060905040b010903 75
    0x3e0544100e01034810420703031920b5210081c044200b920307401d58039118000c0c5482281c0c0e003010741104aa101506100c000401c0d8a0000d02896101e03610540710380c281e10b6018901a000c40303600644040c00d15200c80d0003400141e03489440078401e00d0542c580130501c100000000383c0100840c0f0305080151400060000030181c01101038041d07004000c0d0703031040c070b100c81c1000c0b0300a170f2040d40640300c03550104103c00d110036455807002e0010100004270004982e0165582c00700c18010301d82000d200c55121203001d101543e0f06c2102c12015000d00c0000d0760038401c5051803149000b808a115401e080d40200000e8080c600c1503074101d0060002141518904e040c1540e00c200904606002500030b07840c0c0d10213030806c04110b8001d0011507a000004064400301901d43c0681c01ca00202c0a41c2e12603003c011401c11642c5a4480c1e0f4003a0002c9030203000c98004060000091130000e611020341900b04100810505030052054070480704165800708034850b140f40101d45071002608018001010050224080c80c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 593061861 1250 593060611 593060639
    0x311011112130b030426190f12090605040b09030c03090f0d02060f04260a0f0c08030c01052409040b040203120307050d0c030b0303160501060302030a03260f01060c05070f 75
    0xca2191003002c1351ba602107a0380d4600ca43d0b40c0b8881d00080354039070340903030a1040c9221103000c8031600d000c001c1d0041100c4034600f82c41c0011004d4542c01e80b28000c2c80144901c0e1880c2c5074200302130500a500d403000103031125031070307003d5001064440c40d10711428041c588c880c84004644558014069642c4010821412056800038000e88003001000801150300c500c0541c5062a8442008010301825115a6940050a00145003201d60392602a40000c42280410142c904d0b4066080085070620b440d1f40300940744905800c54002c007a086004001c07581d16441d905da074006070400c506422076516800030030324080900c804644084000020820300d1a0f01602a040e800e01000c814000c881d525403088082e036075003500d007036815001001620055206140307013500d00c51241d800451003554a400080c10004418800d03000301d04488034016240072035040090991b8544141d06c521420000b40542855505000e001c040c45545910002400ba00f00324034801042d40d01d41c040d030172031345403c40060041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 593063111 1250 593061861 593061893
    0xf0f1207060f020c0936010218040b0f0d080f0d05090c041517120a17090a051b01020a02310509060633040311011112130b0304 56
    0x103009280b90903180c1d01c082500b414440009040c1116512244007518204078030130258291503010b050481242d08440b1b400f036001414540006854800d901c400140310610920818403940c1b40071b900c200140d54041d0981109041601c01c0c0010400c075180070300c0144503448020602c0b150210301000d80c01070541006228245080a4a1441c50044180819144108000c0e007030074500c91428403c03134017103000c0e5070b141001c008200d464083c0c04011241c1903074000903007100020140103400f00103400e080c0c0040d8000301c02500030010701c009078a81d00d4031144003452004074a845584c09006613807080262100464008141000308184034240b007107070b0707126280390320703140140388203016451a1980b25840c441d42e0110b0107090190740d40400c10503115800c007071042c2c0d944081c1c02200507142e454041c5607501d81d00501354a548030b085003003203111a850a80014100300c103049a081c0c1801e0085658035595801010306a1260302580d108580d440064120300440d25010080009125112250854034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 593064361 1250 593063111 593063117
    0x41a160813031a041203111e04050901060f0f080c0c0f0c0108100e19021309020a031b1704020a090e01021b0d09170304050d110f041a0f0f120706 64
    0x54030401d07160705850003184c0144c40f1070350400d14110f80074040d810144800d500b0340d954070724180f0401c0030b07003400340064100308000103c0802d003408241048010140500074909100800041da00703002003640380507001c403108000d401c00104d0a0032002101743c03241d4241e040150307080c0c8110314172a1503603080142002d40c00580460701040003244000000019a860320b4502c0c0c4199550302d80c0440c1013801c0000320a400c940c02c02580c2d010000b50705904016140031480960340b25403540c0020309070783c4901a602525014024200d080580248610091818901a0b02481e648034000507071070000561103020401d08101c0c00006198040d8010424200c840e40340f44080240707107408541d00d000048141c408503130a4101440000020102111903071507400807280b4290301c0c0c0c000308208500703002c002c440e19101203c0ca00d0644c030301750b96030100e644001d07a400c014040089a000704800c148022650091001070041381c01030729040840c00b84514090000180800300b030300c0d003558600c4c8a1280c0400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 593065611 1250 593064361 593064383
    0x1808070303230c090103020304050f030c070f0e07050901080901061703041d04032024090f2a0307080114060a12020907050307020a0f0606090b0303041a16081303 71
    0xe0b01c6040e0780d4501800302e0030401c504284980380154000c3d44058410b484a03c04c500c03c58010b013200704004c140301e01500000d494681d00c0d1408401d0140306d941c02c8030303e2070505c07041000005a4458182c8580c550240780c00e902d26125502100e004004503040b50600400f140d5404c007518100100400480e0344103d60140c081070440e800ea802c500c01543c0040000e03050110742c1040b078403030360342c0310f000c1c4030b05102910340000c3c00071405203100ca14803944481d031422040c05c225410909114600c00690080040d2004e82d0311070701c007450302120040340c904c09240e01030035500e4103803010401c07500a0290070340200046401c540c09507103421400c83c1d015106030a070500114003a09048aa043c1441c5d014291003116169460b05580341d410050410085218500c108404210440c1186403800e00035080080c07050304009203001a00c1d41040ca0724065802080104011249050343c041400c8007008100d4880340342c0840241032981031080580194400b01383c04a00c00c01010200044038812000244 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 593066861 1250 593065611 593065661
    0x2060c03160507061401170c36070e0906190303050307021509030705070f150806130c0c1506080309090702070e0408091903022d03100b0f09090a061808070303 70
    0xa43e0780b0782214995003040128a04030760390b03600d58210708801c101040c149c0055540147c081807003140100c81802c00694010783c012039504000401d0364001e80241d807000c0301002e507455034a980141610008003004070010014082e0351090020010303006646a40c40c9040c28101d00e050341e603820404040e54140144a80011000750300d2151104403112014003990b1040792180596041d0402070803190410404421101c005a045c841d0010078401a2240404078504c1e0820906400400005454451601005000042e0300109643c450b04040313034003030310039a14000100c3c104940356014800800e059010b00c0200700114010340f207092010398180701c21094450941443d5400c900c0040d410903501c1111000031a169180444100ea07000c0340c1c5541b49250704003092500d4002c90540f03c1c015503910b4144040e00d4040d1070303340e032000103c43c0c01030581004a440d40c0c4900c5030b074000030a49951202120040301e40e40000ca101c944c2c01048858844130b190034050081d0070002040c03a01a085030030303888 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 593068111 1250 593066861 593066863
    0xf2a0102041e080607140f130e0403140c0a1b0e0115020d020304050a050111070510031d1b100e09071d0405160c021c0f0c0602060c0316050706140117 66
    0x2882078009981c1c40d886d0030b02c0c8040031501981700003440150f09a0801802c5040c1c4034840703c020083c25500c041484500d060b04000b07145004502c8030040070300d01000800c0c5100e100160340b4803101c0c0c004001611b0a407018042007024a045d034004407002003031400014a68480d4006108454195020b4a8400060210890b124030440c01072130b42c00240544d052004d03500c1440440c490861042c11508003036240e1000444840c0309249090000e62251004104103070501c0d031076048990958010054002d801c858924144403c031800c900405120f05800d08181c4562030050664101500301a01170078820310041281a800a202500103500c0110166600301841894400c0c0c02c442202c55910382074000c200c030380b03514010059900004500c0780c92500460003484402d020302c11540d2503101d400901e44024089690b50107501550003020420440010713182c216a409000014004c0c4a41c904210035142c50084c07041c044c0680740b410a110342c1200003114080e05850000030a07224440d5400251 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 593069361 1250 593068111 593068123
    0x603050f1e03030f131a16021506090106050705160b090901050f03060c0d0f020d06050a060c030804081b030313140705130b0303090310020711060f2a0102041e08 71
    0x40c12042d00e50500080e00003104411031700c041c600c2605101888141c00c1c591051001090740c00070515600c1e00083c1c030185030100000c508801130111000c1040c0343c07107000980900e02c1440342d0418007000052980c10408240880180c1100b03c0304010955900c5214450003600b01ca401103004115a0001062524000c00c1176058030078020000e2080c0d90740c0c0010154150000686c600030140c4a4516548490403400a01800c00c03000b040041c0f418602030030003041542c0c0b54170080038010400162404254022441a4800e4001c0e280e241c5e101400d211844554091400c0c452107400044140500700d01004103500d189401009259010f0003003444240d03c984441c0305107640003034000c001d8080d03070040390084070401400030141e905084120003c60309001281082d00250355001902e40c0400945410007942c0d02000d940c140d00305007450340f071040d40e48110a0451050300410f0b00c5142c0341da5200850300440003e0000030b6403030b40c0d95000c140d02c03204008952840c403004070350381c0800e10303c0d000100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 593070611 1250 593069361 593069371
    0x71a01120f021e0a0e04050d11060721020a0c020301051602031b0a380403050409051302040f0905010f090803040f050703020301050c040819020a06050d0603050f1e0303 74
    0x6258001006908000030148103080c25021088805200106540c070408203000070001c481500205140c00c1c5003607801d10250350f001c81d042c0056240e1110500270000f0b18680d1100311401c04184840d800703104201c140184640508a00c1d00019000c0c0341c0f55484403281c1d03003051096000340141c0d2107101d00081c900c0e4440340180300690060102d00c00001c141456425801003030802e4a80c0b282c103940b28003084020000011505840d554002000403030520100b880101c080300d411107050800d644c00800f64481c512502204a85a50100e0944140031071740d1010540d004000308085008c00040f5405030100c2c03501034a880d464160050f022141031300038001c010341c1c014506480c6a40e15035030b000418003403440540e66481130920200040c0c43c2445524010890080096215880c1400c2503140650103400042840c6003d1301030f10041c5c44191068041d0340030307401c1c02c1341c45210740d94014004010303662014042d40700b41110480c1000c2e01052010b414070400e0404a24840414031031070780c0b440144c075 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 593071861 1250 593070611 593070623
    0x7050c010f050103261204080a08150612041a01081c05160f0503041208070209070507050703060203090c0307120b070c0c12061107030201141014101103071a0112 71
    0xd4680b440582c10b030710010414101c5c1c3e0180c00c5c900813007111305120303804a0f070031101c03154005008110130b0f41220000b58481003003e41341c1a81c0c1c0c88517010a025005e40404030420130200c001040030008401d1040140020403c2c15070015a564106503603141c0009080007028403050001c2210240300f03800701c614500040a0003510103845945d88008240003a006031540d00091002040c100c070040d4110701f1b50303802a03000548821540c010000d9106028041d42c044c80030420031540081c4000c40c01d90104da4005a00603125038070080140d00f080000d109040d0716000d01d50380403984c4440e0707a805016840c02038141040d140d40d403000a44a04601d21030140c2150718120040081e84d03400004c0b81c1c07a00b40b003104c0205803841500ba1250b01900451402c80160f5124100b2111040b0390041040e03020301e0744075103041c10314a482028009071a200e090140140e103c9611148218010b18610361040803d00c21a961003007942031050b5840590801e03800d0000c000800026402103912210481e41d070061 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 593073111 1250 593071861 593071883
    0x1005190b0d0b12240a063f030503040b0c03040f23030a05030907121e050a0804030809010e0402030705180607020901030c0608091b190801110a0809010e3307050c010f050103 76
    0x42030700c8083d200d47e00b03181c01104501d18050180349040d034003c80580c481d40750182c0741c2c00c103450070403540786009241c03941e102d80c148108000304022141034001140c12a104a000b03513940f400d008070400054a0b01d004030303c00000c0404103640e1060007544030b80850742c00d45283c1903ca0040410484988002600420380441c1c009041c45054080c880030922a8045410010042e82ca10003241c001c0d030700540e11590b010440242c10758204034020307080c1c01e04540452451901d240003511038040c1c03090803002a2009404640303581c072414115043e240e0000c200504540c1d40b031405038007555141c040c01c0001500750020420340e05002070800181c1000e000210204016113081c0048840139600d80baa000d040c4080009064100303218007814142202c121554441140074040c1004901501883c1d26030700d170407040c23041060301007038105008040784440d100e002d0504420070000c01076501403245981c8080e00303200c0c0d4075401100034610508070000a1060a4030340400d00704a500910004d04804582d13 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 593074361 1250 593073111 593073149
    0x1107050d03050307111009061e290105040911040510050a051b03091e1009050d03030209060f0c060f1608010504020307090803031005190b0d0b12240a06 67
    0x2584170034039455854421500c00d004003107800c0003070700e1312076100343d4045984030041d4824071a074030980d1901058445090294590040e600425000107000c002140000d00c0d410079000d80c480d5088034014220640144801003405c030f660302d095407080c07258074400d4240c14000d60b25103000b001607544200140d1a498104075103680042d046506c500740710551400b040100101a035114041d001d043c3d080401c0c100808100e80091200c50105401c0b4001031120310041080240d07500c01040c448103130714bc41c0160311900ca501c042000360150105d080d00480c004110a281c26000054040c412506251140907e4854801d81a40c0c2034842940e0800030b0001d100500039401d15400543c0c00109038a401305032030744d8031f0400a0075600107480804111540c540100624a4150708050300300642c170f0300452501d841c01030440300d0361040c40c940404258980d0820009540c5000b01456040170890584121420a413040c45140c4020324013a00c03044601008070302003c055100c1d035000e0320211003001034228a8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 593075611 1250 593074361 593074367
    0xc040f0f15180c1b150f0207020d080904020906030a0e0d030e0d0809121b01060605090303070314070213050f07080114010c05161806050105160b0a0902101107050d03050307 76
    0x622903c0c1c020301c003200c0031a84402c03102800c0c0a4885000d04104109030480252100c1034402c00094078144900502098000da41c0d100110b944490f40304561956071442c01c008100a400741c00c412a03030028011040090800c815001107a20580ca481911032a101c0108250304491520039044159400030400c1213001d4040e07810705822822074030841e08140014803442c043c0e80d01058a002c41c134001080520115030302401a54040e1180d4140f0904046102c004240d407809100d101400704130141940c0040003120304111105c0a802030f004a18501f13040c09404007030f007010703646903107200080d00028101c0e500c500c9a86059030b811440403041641900c00464240704c100900351194000e002c042180103003001800c200402c1c0039030b05800355a42c07450380740086500700d510050621408000c1c10106000e003990404007640c2c86078114441e5208e4140c110000c1107030500082d04049265000f0202c2504104660408603580c0304031080a9281e505010301c42e0300d2260010b0211301c00780081902280 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 593076861 1250 593075611 593075621
    0xc0809040203070915121b0f0810030501020409050601020618060a110c060a09031101060608060d0302030d05190b04140402010e060c0114040201030f0b10050c0c040f0f1518 76
    0x10703443c110f086180c41d079422420310b006901e0300303801041c0031078841000142d160058400000005001c1501c0403402d2201074104000b0200c007004004271000020354054880854902458201000319110350715028200014202178800e240540304030000240411201022940181900710182c44079031100300e00c000c06006000788080c1303502c0c424024007000d00030400c0014800c941103407003c55181000e0602402480e59402d4001d49030341810000d0290580180c2d00030b0b041716058907042842041410100d046000d82c601740e00d0341c181081d00340700c40e40c03225443c542c0d07c0b0042014100300000708042040101d9101d9074a880000c4003031400a8050749c024030b01a4003e0b80702801403403800760016a81070840e0701c2400455580b091920030b00c0203550703240c8200c0d408005134400c20042d00004500140401c118014080d080000015102d111240e043c0b04106005202820034403005414410075406013140d0b40030410520f141100142c030712102c1e0303403150045901620f921040e83e1080c00310100a0300d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 593078111 1250 593076861 593076871
    0x2903041a060105070f050709111305010f09050301020c010515010513120f0c080d02060f04031b020a0f0f17031905031b0f0a020715020d0c05010f06081c0c0809040203 73
    0x81030244c5004600042001122141300d07201406500e402c080c009400c0300d0083e20081c08004051000800c1080c0708501641940c4007400c08503158104048102c480b8002c1d5007004c0e41550001c6103078840c030601500f0417030142d660445801c000e41510750044800c1c2c01450380030301c0e000404520800c841a1127540c04d200303080c01411030b1442c0c841d5a488900d8040304551086030980c0c8103800b18000a64140501500141d0b0300c04890702d1400c04d610300500f201c04240d0f0409803441020b0f110317411550b8803400c8400038490b00b42400c41059540c2c3c1004182e0708c4034421414064181084c6803c3d042021007190201017408001c1e50801041d01800c58140c0c000400700000e03400e0300155100c40140310340c083c2021980b900405540c900c001040241072401c1580b1195808440400110000350042400081c0c0c3c0c01601d0542240c03085400c2007409082031001804400d40360140106280303a02251600d001490016090020f4404400450b420030102101400100c0d0600000700c00e0325042d002581c0107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 593079361 1250 593078111 593078117
    0x30f1818020403050d2a0b0609090c030d0e01080108030f1617041206140106020d111c0801030b0f0906070c060e060a1a1f0f02162903041a0601 63
    0x140c41c0d5a44c0c51400e2000143c11011414015180301e841103410038140c0c8200d0114505542100684d0352058410009800d0300d12074160309000808030a0100000c001e42c10f4004d086a06000c5e1a21015145002254480b4005001c000010803641c00001c220b07030010b40402111031815510f54810151824903440480d4821a03ea01d83c900b00c12801000e00003400d10560003402c0d02c0c855140c208101c0780190b035021108601d803001041840d8011230303030107218041e5051060524140600c06400c00b01041300249000f012041440342d01036000d0400c9041e80e00c5041c8172000da44514003000320205044800c24030307aa101c94000f4a01a10950704080007500c00c503800300380c41003802c02c51800c102045a0200d00c40750380e002c445440300340c0018030b20038108060703c0b01d4038081807c0c4841501072404080040602034590658210386201b0045102d8208060300300100b040c6d190040020b0404002e0b50101c40c11900c000d0b02090040c100080b603009983c4841171f8890b05251000c1612040b034020001418 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 593080611 1250 593079361 593079367
    0x1030e070b030114041d071505040503011b02060906090c06070c17101d070902070c080a03080403181811090409050f0609070501120e0307140307030f181802 69
    0x703054088010b50b01030030808594214100b00030044c031044540e18400c650050f0301c2c030400c0203d0150040b858409540c0600c100401003e407900054410b8030580e480580c00d03601c0c0c8500c000524050400c2300714441425400e40760152211a40075555034816500ca001d0b607000340e0a5480030740b400c1401046006c0c402e00094102c55030b101c0c8110303400d800146541c101600800503d1222020501c80c1220360050101d4607800b000c1480c52484d42c5117524003484070000c0d0300062007402c2c0403500c2036150007001c0700002c8800c05402e030700d001050003e003500c04801141d900f511003440112304070240000d9556901015103610500c44100000e441d804040092880040040d001182c40324000c0620290127880208a09c121004100d840c0045c0103041c2480c46d0003030101440160707440f407142490210070301c90100e4106551903046065210b820002082e20380c560320403458810000c805040d0f168040d44650001140c0b1480c00e4521010300c1c0130300c0084200b41e00c4207200303d1418841801d0740560f24400182 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 593081861 1250 593080611 593080619
    0x61903050601020c130506030c09011508040f0209090d031103060d02010c0609320106141002071e05090f190905010917190c0515070201090f120207081b01030e07 71
    0x1c030341c8610305e4408403070315150800c00100e401d081020480502c4151141b40703003985400700c00754076803400101e034904018002c1c010805001040015101040d0010b100744244c0c00d05992483d55503d00c1d01035000407a04064024007481041001d41344241006011403200b251a507004640000c1c401c40304a0f03003680c1d604204400304030761180740c00121102820200c0784a00c84158001c4003a028420301c0d140d07030704040741840400d020354644a404942a1034007824820040b00503401d014458000d207103a52038890422050b072404a00500840d0f10a0b07a404010f40c55040c000e907109071040b185040c00c042c03103440100300c0ca01c40354880110715020303c0000a100603141c0d14050340203041d52107500607403000b04400c120000c001c200000f04039210b08040300036003440c0c1d40e03242d2160300c03901c1c800c501c2c6040390b400074405034000c0d044007907501e030f00c0301803211004c6e20b501d80401c1450800320204010f100d21140450351090000e01c80d020f05a4009601f8911420b1300c00440140200c103070740311224000e842c0005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 593083111 1250 593081861 593081869
    0x10c080709060f02481804050d0e03030c0607020303010311010206040b061e06161b0f0603020f120901060807050a05010c061a09040c050907081e0709150507020f061903050601020c 79
    0x410755000c201c3c0a21011074004011001c403245185401b0304041d941400001040040d0341c98844041b0b080513075180306000000307030031030240e203100290a006a50821180c10340c0840150f0503a40305807890700307031a40782c140120b0b0303101c408850092042400001040080c42d0482e2a124070f400010414040750b10500f0204001d03401031200e44a403c81a40c00d030720204a206106a401f5402403400400c41d03514012602d0380c41c6400b80f18080500d0303400030710181c1c5040030200710340c214a500c545007400ca060011650b0b0082101e8440ca0007540a08800071540b4039185c51880704640059458150b400180e440700c400801070711090a4841d90050554411911b031400c28602c40c0303015054909001d8079200a0001c1014010107220410030b40c1020407852008001d400d401801d2040041d90282d81c03403080503a10000180c018850b0005202803418415078400c0042003c03620a803243c699080560b020b000903401856410004401e0080031810110321941c0302c65803141d0148101c0340401004004a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 593084361 1250 593083111 593083213
    0x3022e020d022701020d030c090f140307090203070906031e092d022b020a0b07060612031403040602130b0304120c03051911010c080709060f02 63
    0x34400c464020546501003c580c0d00e060043c035100c0c0d4030a2034a45001c1000039160021003a2180c1859580c08003a44054442c40001000e0038140040c190b209844044100040d0320078122a842885003680c0400c1d03045043c02600c0c0244403548500c0841c0741802c0b03054002c0e00303445000248920b98044203012a040b40e0184a0303d0718080c11592004128074203005c444141441c56004190540c04901d00050301d600c01d4129040282d1100b44042c0c100c85132011205121001010754003000c100004100c1c004044001c04c0080c1c03241c00c0402080f995208010700c0d1007a400c9015003c0740001d403126400c640c4c50380081d0740c401d1003540011300d010700d582400c034401401074204508200010003000100241c03d01a464000903d08283e5151718696800821130301c41c540214600d041c41100307000c00303540110155595100458001e01603203121400c01442c428003200e0140000300201e100140c3d41c1d014024034280c009a650203008e800252410b0032800100701e000040d241c1084e00c03021100300301c240ba01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 593085611 1250 593084361 593084377
    0x100e061305190516090204150212070b040503090a0305061806010513021e0706020d14060a0314030f120f0c0a0909021602040e0708010f0605030c0409061812021903022e02 75
    0x20050b21f1b18180f070b000024200e541c000050555004103560035401d4070104c1a10102a0700c041c0513007807641c40e03140040c150f009400d2969007220303944c2d1020007000000b0805a01c910702d07601e01c0d542d0a4010815066441d8003e10801c5c5d0418041c140190310402c141d0024110100309250585407003a20030070f015056807000c4000d650040d804544100c9000481c055800410f1440200000a0400b007000170100c5500b4800201b612081482c602c0c4e50070303010b10685811072020048591100040221914503003803c441d0141c1c11050003001131190440e0b0f80650b9a0b000550391404e9500342042d0b0316000039406881302d40f003000041b00c42540180c0d5180109414103a40d0405058000d19004000342501e500c080105803640c00c01d4410f0069440c0082c901e4a030071021140810f0007000c2d820810700421110040c01207000320307880032805010f03527052580c141c00101c3d403c45e103084040804c0d80055604080c0d0040068121802d6000804da07481042d01681344401c48481044181c150440b089038440c0d14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 593086861 1250 593085611 593085629
    0x5070e06040c050901210e0304092f070807020109031205070b06090106020a0b1e040f3e0f1e04110906040b0d0e100e061305190516 58
    0x204125a500709402490060782207424924140103440d40082e00c6030050500e80009680e100250b03042c0c1c0350450700490030070103107a41500d1340d441d119210a0040d00250114081a921b010002c10b01c0240b40140e0344182041110a103040c01103d50340d14000d42d11940041c2d040102084012001c5007804020300080e2480d034441540d00c0301c052a00000f00e0b01e00411291050092000401600340c020490104450707220761400d503182d888440c1c02d22645491071aa0181000d184200030421201d45018000917019016050740c103503146034100c0d801341c01c0c290051054200c80099408910701d5005404d006000284075035105444580413443c0500540300d90f030111400d41440700000c2c2020301c142401d0680074460680b0300403060b004900030344140e2080342d500392000601d0b51180440350748407140c2d2010b21026104000d051070219006801c0c1051414114000c4102007501102c484e0481c500c003541c4540030744240c0c90702400c20102a540008203070b4690044404a4000001e8000024041e0510f00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 593088111 1250 593086861 593086889
    0x3080d15060e041b080703021309050c040602070e0c0904020309031b0105161103030f220302100c1706090a0f02070b041101170613020415020c041b0503010905130507 73
    0x141c00c11060744c4d4014800710361005138039009202d40d9400020035030702500d0750402581c0d612031070f2622601d4642c0c80c2d01400510f0f1500c828080c580c10810004c0c0200c0c2c0752642254062905e40400001c150030580e00304c880040d080042c010103041a4028640c840e6000007903d081000c0340007004003522040780c500d0000e942d5102001154000b400140703080340501c2c9092144008500d000b25a00d01c400390052081d04c10350070006171907000005d900707610818882491107524880d452701a648684400903620b802d400c080c14551094401e41041c520303003100c203100ea00345880782004e01c86905000ba2031101c2507602c1d854030040401c1d01c1e0004048951150011011914040c18510000d4100c1c103012030410043c59204981d5941c0700d66880c4e0480001c6070480350803020540c60000a00c81d139403100981802c0c0380103100340590003140d66070001d030003514140403101c640c0c800824442010203290001c03c0d0b081c001804842803550045611400c0c0042908214180d0b0301c50380e2819110303512600e0074004407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 593089361 1250 593088111 593088137
    0xc1b03070b0f072018160f020a0b190e10060501020303040506040605090a12020d0201050c09013009080a0e060a08040f0c090608031803061003080d1506 67
    0x1003115100400c55410801e0410203200c0c2c401c5580e10806001405504c02d0b00b8060450000080d600c1d0110301c40204041c031060b41150851800d14011241006182400801c60040500a0203900300c69800741c2d000d00042000b42d07907a1001481c000c2c0a208058440e80b414040454081c0314902001d0003d400414008480e0000c0700700b07890729508800d0441d0828810310001070b400140c0f054000c0d60004000c6180c5e07544070510f07458410010005032103d14540032007405140c020640c003d400d0500d90091103c1e87e502e4a242c40988200e4400700d000840135402c0341207840715418044115410045550b6051251840c918150b404016041d07440c200005110a0500c0d040f10714413081c92800c3d1100d50510600d6007018040c1c41c40104042c092844e01c021100130041d081109030301801c040d2504000355515007070070640e290080301c1c44015129080a400380185800101ca610442200c0d800c2d003112801c2d5514541c0c2500888911080f0720f440c0d40b01c00c0340030004210310038094856590ba90040e1a80 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 593090611 1250 593089361 593089363
    0x1b0e0a1505030102070b0f091c090303030b01020c060a11030f12010609170c010c14062802040f06140708030a2013051905041119050a02030304030c080c1b03 69
    0x3160301c69072007a8410001d40300001e21008109606c001810001c1d01207503544c900c154105120201480b100c0c00e81c90a5469005030408014800d481c0281c0d000c00803c2e149400599590514405c0c0d554401810300c40c211134607110704140042c10340110180c908002421094501581066403000c950b000c0d180700600244e54440351000040c00c4915813038407280f03000c8515584512084180c0c40c100200006410207215030300a00c28500c00e54501181c04900c1c000004940700e00800d0040000000c16030341440f40f1292078001d4038291078420300050300107132800c0400e41e14082411a0000340050620410340490b140d400030b0351064074002d0010651200044050030540a802c070801049107050080c00308103544426120250f4000340c8420000e08040001400e4404050348801c0d800350402d2440034403024800702510249043c003900904400800c60140d40d28000c101403840140d0003400043c020a220740030354400240503916a40c42d2104400b051420155601c10841c0c00c0d520021100d1a01d0070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 593091861 1250 593090611 593090651
    0xc0303080f13031b02060d09021c150b030703153801080408090d08042402060426030c1306030209100c0203150115030605010e0a031b0e0a 61
    0x58120034000c41454030000d40650b040c801e80b0050204400d615825120b071507840a03040034941c00a01c0c941e111540b080c0800058117845c8802c071b0041120400402d41d480800c04101e800c15840254011035200d954800780040908a41050345827090801c000085244510a8001c00340318101c04a04400249035100301d110808050756540b84442403551910001007030807005030007007482c0401d1a030b01d990034a00c2c00d0b0302441c1d0b100d5074401e0042c1c0340002004449401001192001c0c251078000350300e9007168202e1540000c4010015803c4a4001030000340c1c035060070540e0030386030414405600740e043ca00c2c3c0c00e683c02c00c48144404403400203c010390005c1e421141d00080030145011340c641852040450200b201d80d0304100c06000f030700c070360071803c555090003150020f0815119440d219030391a080074180c4034400c091940440d107022350110307440d4070528243c1500200517000790180340c9950764042000c06801d001e050f201081c1c1e14042900200803c10302c1c0644003a10021840303003030078451a85041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 593093111 1250 593091861 593091871
    0xa0615020a120f05030f060411180f1203070b0a0906060f06020c09090705012109060903080f010608040b072309130501140d020a081002071104020a021002091c0c030308 74
    0x400010003404075135009003282d41c001182c807035101c060b4580001050140030042c2a68981501c0403610340515000000105401c0c0c0e81100c0403144a504481408240c0b01d448412550580040100201180840c80583e8101d4851b400008030b800c07142c0c0b41d903002c8812035084122080343e0810104652a410040014008021207514015040c440e580c0c2ea40d420080c03180320b0522000f50744022a4151800f40000e200100d6a8280140b0a8601d8241d00908400a0480c08602d072100031035060703840e000c030030360503140180c50358812a261034071030320350a40c002080c031400c100e80b01203080c20601220742101e45520b01c0e45078072915002044200103420800242c609070041c0b40030010420708001c40303951840e410301941d03004441b0019001040c03085100c0c1d003002c4030030311801404180ca50500c0e4000c04c1c1d114059944804c10200403001c20080c1c1c800c882010700140d00508058400040d10b40c005c100384a001445d00001804034002c00000805494003030704c444c11742c10b800f0070074903400030845680f00b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 593094361 1250 593093111 593093117
    0x506010314060906180108030406201213090c0914041a06030601050c06090606010e01050406050324031f05090d0206071110020c01090312230a0615020a12 68
    0x212400744000202075000b000548100000c101280c210b4450150700d02c04590360741040403042d82c48010055480d40684210780008408050300e611403800c030044c01054038504400b5101c20550f00d1318050b156084100200c0101244400010380d40419214007031002c84240c942601607454000e1801c0346d0340842ca0824010307801d2040604840105004802d6104411524a03440b40c13580d80048405000311401801148112420700803440c40020b05203119282c26600e00c03200c1001000111400c2c06070b441204040364040c4007080315698001400d00c8060344030f2100c06800024540001c4c0307003141010004560307150442c80d028542a05000312940a01070100400f25089492402035803188010004401c0210184104c0749510301030113025481c0c91409420b545a8504801c020300130190307044100c000c01c0000400340c5101149005654860140318100022100864201401c1900042091000303070350ba0080401c0c0c02001c0440680e8030780f070941c0140207800391894240340c05e070000341d100418 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 593095611 1250 593094361 593094371
    0xf010605012102030c090301062306041d090a2109080d05030106050318070609170d1b0602070c2408010513090f020a170721080702130f0c0305060103 66
    0x20b812041c10311400038541d1034006980781c1d61440145aa4041c00d0aa554594205000043d801e039030074407035003030f5221540408101c0804010400034644251320849182c00c0424203e601280140448154061281410358241030700c07039034034a4240c94400e0880d140101210031180d2059622040e007602402c1464020310310955044400741403404140710700d43c1000000400148409041810900161030603000c03134281b19103800000d011420b6a0240c1c000c100d0540708000c0d0300d141300103207410706e200c2e02b900d40401302000704101525903a41c5480940d10b00707408202a0001420102d0220001d01c0e108106a00104000b420718070002088088401000020381c018031240d0707110a040310fa40d101d075a00004001030945000d011000328042c0283d0b21400d5090700050002d0503074242c484441820081e55031494540c00c2400d003600d5040d050342c102e019110b405000045080004240b1240002c0006001080c0f1a0001d020740d082400040d90580d1205048421260103024980c1c01c88070900701401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 593096861 1250 593095611 593095637
    0x30605040b031b12010204090f230106050901050c1005150d150b0a15031406030f030415090b0a0201090309050603061c03050c10061706040f060209060d0e0f01060501 73
    0x280d03405402c3c4095040c0b07040d04a0504180e55000550040f5071a00b800940d04c90340d44410340030081c0b8900c114070f40141e0902c04184100e0854000315815034041c818041d4059081000444050b0170001a09041c0310b001c010102410204118105078400202c43c00b24103440c140e00031891652100506601076600e9170411000240c0e4004a00c484940c890000213030300c3d41a031f00040c0c107107840b07901610b020300a0890842078207a06405c80300c1800c560504a03a5241c8540050554610403c0d2000c10160018030050100400c51040405540d0710f0b442e0400f1150f8450310600550b5000300310450240c0e542c3e405a408064100d0340c440020002101c000b41949085004181d1034640192201b54000140d81c64104060044095440c00d00005085602e0b07003601e051040001c00c440d00566440b188030381e03810800c01000140c428070036170340141c010001c040b45a582c800a900521083c83c0e1069083c00307a10a208007034802c04070003011101c014030320901d02c00c9d40f450840303205030052030410540300c0200b0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 593098111 1250 593096861 593096863
    0x60618050408180d02060703170105031b1c0203060f01061409060d0f150f21031b03111207200102070b07030201060905090a03020d030c091203110d0807030605040b03 73
    0xf01c6002214200700c0e03c01080200265a840b42010b000b50b1080010a0200030300d9409800e040c158641804078030140d98949040603030b203030311010b61400901010b20580c1c00714146480c2c43e424118120b95020f43e1414154000382c104182190682c540700e152400420055500020b030281507010207640d18076150f0030901140f518851081d43c105542e44542007007000c200c50764490520303207a039003407104903007600d440140301583c1051050708200c850101c0c20120048100b0b40b104481d540c55210012503004a50000c004404005401d80510054511084200b4018040c180c9149080b40000e85e803202185003840c02c4202c00c1c040c1d08900c462400c500089640c000820320190b0707015560a60316005145002c03405480720f07800c81d440142c00c046c01d0041c041d400040714500d0700e1180c1c0a8400c200030100b0110116820038942d01d0000300701000800c58484011111040c3d54002d2518180c04281104103d15001c9101c0151001a0b0381504100d40182d151003a4805844200c50600c401e6a0783c80001e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 593099361 1250 593098111 593098117
    0x2f070c03030c050a060e01060f06050301080c01030504081b030a03181a0a020906040f0906060212070813350703020a1a04080d09090b0f06070f031803060618050408 72
    0xd0900c0016240d5400f80a410002031281a601c200284000e4658010b4140600540e105442c0c0800800c0e001040950040050b00d05a40c0e603080141296102c8000450181002500503109158104241544c5082019080e482c510218005503564031b056540141115490072004000a92803101c000000b9000b00408010030900301d0306c812661a981041d100910811400686c092000540007441c4800c084d0718104407000795108000325991144241e07219510346000300c0c10b58000f00042e0700001c2e03080300a028990440c0c1a00f042c51502e4180000d000c1c6c10b0081d5403031121503100e000602c044402c016001d07400d010b100207000003516660200c0c2c20341006005030541e0415803100800e01c841d00c01c00703507401098070904544103e9641c0308082e18203203a500841e10020b041895a13585424503a80c5494140740117455130b45842c103035840d5101c1c00600c0030340c07c03410004100407404d030444140380540081e5000d0301000501c5442c0c00c10b100c0e686000c2c10310307200da600e04090411001c91114030030b03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 593100611 1250 593099361 593099363
    0x90c120e0a0f080c0d1e11030a0518040504030c1b082a06040f170c0117060d02150a02190c03032001050103060e0f0f06010b07030c02042f070c03 64
    0x5840c860701c0051a046603640583e442030800d40c45001d52141040d94005484c220060381d449820381e5148506d1390455180baa0301c7c0001c0a1035004100c681c041e14403600081c001c0c00e2004400c0700c088443c040016080c0e8100752401d07000156203030190818131038124404420f50488507482d9500c0c034a080403c5440b04500310003a481000c4500b070141080001001014622500401c400e07545c5440d100d030080109414000c2e4800800341d6001804c2000000910303030b0b80440161100c150128408000c205c190710000e0000e40c00811040c8211300584030700c0c24a660084520310f501c0c2d20743c190218001c1c5040c10041010300c07500f0425422340046800c002010040d20340500e45000c2c500c1c01c850043c0c6502107113010015040d844c00000209115066010701c1000e10a5000c1d01c1140c0002600c20380e0fa0440c0e100b0840e4190450001002240090300007000414420b04001c40040920f40003d8100ca45405400507642016005c50120400681c0030741031007030071030f21041e08120f01a00d900d01d0082c51408 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 593101861 1250 593100611 593100623
    0x90b10210b03071502062e0e07110f0d02010b1503130c330f080c0c0106080a0c080d050408190311031602100504140d110604090c120e0a 60
    0x99070300003a4a00344510409420701c1420704420105006000b07590b02400c90b00e4100100380c489000e510b88140142c042c451000440100540900b8840c004c0c181e414042c2010042c842e44031001d80c91580117011030840c2c42d032a18003400f00007040c0000682074603119009148200044400c000c1ca640c18942540d803c0038050410403644d0400380307001c0104c0f010310340215000341e5084000036840c8404100702a01c050001711744400c0c0c03144003101a43c15001d206400400300304880c000800400300c201c040c004042d0351400101c0e845503200445814045405002e8400038008a024002010304100441c0011050b103411841d0520f40004c944d154100354039440c50b01100305810200b03043c403840810403440d0321241500e5688298440300c49400c030030f4403822400741203c8180038007614014000e407011240060205141d0503004002c01c031000d400d02c0740403107044028951000d10b684450000e40050702900c0c0000902c55040207014020003090144030341e96604100c0424804600410002c540076800f070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 593103111 1250 593101861 593101871
    0x60c0d090c0308071104050411010c21020610170a080f04030b0a0e010c0e060a080907030602030702030a1e0c023106140a030f02060a090306020301090b1021 69
    0x20044a000c0e00030080050705001d44544040140110f81c0014504240300e00c90b00c04c040729000017400241d410444028140d4802c40e280c0c10483c0d405101c42c1c115503480740d440041440c0d00500f0104c11503000c05005001a0702110802900b2011b914901020700f280c1c2c03e80214000000f0415540da0b1030110b802020103c1c0450a28171004080d010b07100a5540000744200354540381c3d510328024698035000f04101d40c201a05d40304510701414080d224240702914052411080c81c00990300b801000e403010480e41301c3c800340000820084e00c0918002c1e01c555002d156a01e84402005009001c07034034092034600e00040d41040c401d0740000e40400001d9064801c0d0194103043e040814a400d148400c901903502c50f04500300071b00a80794000d0307040d00c44d003046a1480c00004414000320740c502c1e0000070721011600c8820400f620303250000c3c02030310015281c40160030340c89545c3e980c01d1b41c100303030300100700b50340c560446012a1410461079102c1c1c100a140c204031680301000d450030080030030a00542d440f9030321 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 593104361 1250 593103111 593103127
    0xe01050108061f1a12060406060912050f06090d08150d060c0507050f250b030f0606220609060c03021c0201020403170a0801080303040807021e04152402060c 69
    0x10300c03034400402299000c40110301010f04288007591000709020a070240000c001551447c0a100e0036007503e040f44e642241c050b040c022009240c00e40b01505031441d10030301140302c0700d014080000c1362258003200702400e41e04000c0395001d13210b940060101c04c60280e4064500800d922000c030440d48403900040007158075140c50f58199024030038000054418040c8016415248400242d501081c2c8000d400c1140c1c0a00b40c45034401c1c10b14800e0007100380361a03040002c0780a4030080d048454000d1002451070340380c47c0345e0b0b0748500b020b912030a038a985412594001007103090b4100c41610014445420442c81944c0c41d0355000f5110034130940903008811010548000d80c600c00d5040d034028503844041182002100c003001403260300709074059800910184c0000c6841d01000c0241d90145521100132420004641e00b042203070700100003141001000303c080b40d141030381c1c2c80c0a800700403030180140c2c4440030300303018140894400309282500b00700e0440c07001e414029400035070300b076101030a07550701629001c403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 593105611 1250 593104361 593104411
    0x110a02011b020d0b0906010f2616080609070b0c1c120e01050609010504110f090616030f0e0103020c1504080f1207021006210501060305031c0e0105010806 68
    0x806001075084022120305100308450844c0b1540246010340031505140c0e44d481040c1c1a480260250745542c1c240c04110102019981036808800c00100d020780702c0441046074001c986904a91200e0600c2d4041c00c244451a00c05002010151074a103441e01d15010b10800e02c035a81d40003040000e01071811151110702c15900c100f418011002000ca000e02142d00c0c01500d05020301001c4c0d810501c1066144000119403405104e803980c0d040300316201c14208035051101c4040c0d87c1142d0030854001c4001c0200401044482d0041c8803998840e86035007107901c10110000308410110104903040c18410001103070715940003d81e0401031004c8901d2011b040d41e491070300e0881c1c0c3c0910301446180307203401b1680714042103000c94100e106c0c4425900312098404605d25407015105244a0310010500320b1840d1a50007074510825440d260192001141071541c031303038500380f80da445440c4600e0141840b03c0e104d42600e88a001c0e000b0036811841c000d102550410801546528020300402d0a5030581e182c1e014040c59 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 593106861 1250 593105611 593105657
    0x7020d02030f10091703010303022a1f12050f060f0409060f061701060614210a06090b0a080601062f03030103174003060603020907110a0201 62
    0xc40142660140f400c804500c502600f00840110742542400010811060400c0d094078100c0e5055802407070031403003181560302c00040c113043c1142036884400e4107001707036154292031070362003460204001008040b540004200d4415520390300c0340d1b14240024400c21413080490a50020320440c0c10040092030003000500070101d2041c01080c00d410400d0024002029500a000301d80340705c50940e01500b0505200c2e8201c500e04d0003a240440e1038a00b1050502c52560050f00c0c420f0f00c581d514608540d149842200c00038000ca0381400c590f92508024000109d1a002e0004030b814162a5110380324140f9010548980050160108102d00445041c0d0f800482d646540da21081c025064888007111298107510b90f0300900050315108203100e0b10800202e586401c81c5c038400c2d028080c180356103c05d503002410704044010b540078610415000490030008091080340214450100000d1940c40e51050209000000f40000244810321038100010000800c041040660900c1c0a4100c03812041358044121 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 593108111 1250 593106861 593106883
    0x1005220e010b0a0b030a05130308360d020f070b030a151a040905070c0b071821060c0e010503010b0f1b060402090108011a09090c060f040e010506070807020d0203 71
    0x783c0c0e000c1d00064400c2c44500a502900790038209004a5540745110030107400701ca400100010045000a0b80d82a4103001c0c0600361390a000020814040110071511203200c024101c500075040840482d1040e40c0400070810b010703c098010b449060704c0c0c40050015030000603e48030302262540c09100203000300c0b60b04240582002c02084922a81075440d03169147c00500a9440c0c1310306c0c00000c10f2400d4014200c1c546104c0d88000740740a240d540107411280c20b03240607035000340e030030001e50046030b900c0424482010221010101e160700302c16509140b010b0751900c0b03d2001c02c1c0201d030808114903036480000c8a064800501c542603480e12110800d015501c5800e100308203080c0c588002d081994000f18503140681d00882c1c07030404130f988904000d400c940145400002e80a41d00710f00b01d0040c00d0603211035034048280c0f010341c0d090007104400f26080b940441031004084034000380c2070204c401c4010f038050152005039102030410080d40c0e500704051003a81c44c06482540354400c02c804664040000c003000c0c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 593109361 1250 593108111 593108119
    0x14060a12021905070c050108160c02030a050615090a0c3002041d1b19020703020406080625020a08091c03050414010804080a0c05070803030f1005220e010b 68
    0x901981d902c000c0140c4c01c1030f00102c030050600c0c400001d082d07204c0c2000c10b014560307480c2c810340011407801096131038a04000c4200e826014032440c1401080c82880880c0c0301d83e031012488c500e031441b104204010040024244560189403840048101d5440060805013580c421400c4208183e0005400c40d15150000b80c0c0e20310380d00004020070100b2407045a0a4100d10b0210303081c03c1910381d80380b050307050000082ea1083c0a20140a51012043c21500104412a8600644400c0d0782ca98007c10191889900b02c200c0da5405082400810700001400d056180c803251480020100c00c0c0c04000d46404a807500a0542d4802150545807991088017921400140c8400461040302a01c0d000d031541d0060b1083d4000310b40b80060710211940141c001c203100300c0c0e212130000d1074a00740e448240c44204e9406404c0c2c130310713110f00200800e0411007000190f000c2d041c00c002882080c07920318140e0310001c00c560401c80c0034203042a4644182c026a01c11114804011071003c0b80d08ac002e241c1440c01407038513800c243d0744 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 593110611 1250 593109361 593109397
    0x5042a0504050405010501030e0c130b09011706060a1a07170a080103030e0d0804050d08090d0b0a0b1f0305330f03070302011706040f0c030e0714060a1202 68
    0x211504800144200c46043d202400103a9a0b03900640c12200710211890403904442481030307540c50000388802c02d50405003000508413658001003100144242c0108600038014200640b261100b000f9480e4020b2048030340542260400d4030316100b1045002001c0c400f00c41c085070150030850f0580f9403a03002003071000387c3c0791103802da45c800404034a07081c4002e40c042141116103418034140341d105403006075004105039180915180c1840074440301004203544030842400040c10301c0c1e49024110400710b0191030000928107001201108a07103c0c03c0f500c92007000c1c014071001e240b2241d44007200404600c5c2c01c0c00122560303555040714003074903c051204240002241c0b00743c0300c07094511031000b800000362811054004580c060654480b214040680465449078407519170030000782619900044c040c1010403aa01e0a60221042d0b44241d14a6000721741c54003e8000002d600b005403800414065001c1c070a03103850000465a1441a51400002c000400e8140781484400c1d03012500180403800c00442 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 593111861 1250 593110611 593110691
    0x90c0911070f030e0a0e2a1308030403061107170a18120c1e030212010603060c0c140705060f0d110703051207050c071203020a0f06050601030605041103010504 70
    0x40700004014903442100205e9000c00c070b501042d081a13200b00c01022051f000e89a1150000481d8440000e028450300d104004203100d000b20381c40240c008190141c0255200c500714500325040c1c850826141d4100c3c00140700070000301d02e803983c040c1c400140c4010031703d5a0b100b40744000c995445140220307070268100c12000040c4000108070b40000f081c0140d10880e04281c44010404249050700041c6001c0019654103102500e0301c101c401e207800e20031800000d84030ba43c0760ba943c42952500c06c03410300466910318015041c0315540b8214a40d001b052401ba0412500f000005030301170042040c1d03d18940004940a07010703c0c0c0c20381c031168036541c3c86645c5544a425a140040c8140d0103003a0740300c0481221404281814020002d90380d44600a8000c2c0440a050801c4075410880d0f04009400314800e110075040803400769101200c04500030003001c00e1510301200090155a0240d000394043d0b4270308000c01c07030b542e5942c0301900c2c1034035821a4081030000c007030383d5600001503400c02842620700407850120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 593113111 1250 593111861 593111867
    0x30809130c09060f050705070e340e030606091b0d0603082511040504030528110a02060318340b040602030d0b1c0602040513090c0911070f03 62
    0x4800c9494135910300c1002908094129010f0084000040c41d51340111020b1007420500d049103680300240c02600c018210800180aa13001c2ca0344092641c0d60316041c42040341075a00120603050910141c00800b018101103022512014004080d5503900c10402c00800703200d10004111001641508402d110311500e82c244042d05602103105241c1402c295081d00031583c49221002c03c0164000d06402c1141c1113040c1400041c20000f041141081400c01c41d8402d00050500045403281556510000d00308002102500d4084499a42d2a441e0706c41b00d15030300140d540c5801c681d440f07507030615031400f00780a50b60018902035040ea0043c1c0110200d4444030024100c4a4a02c4500c0761068075a01c5c0307081d90f400000c501803040b80a410010b030002c0202e1640744180780c01c6071138520340142202903010b00303812210081c140d03805001c840084c0c001a0800180c60320500350025010342000800001e01c542e0f0394401040c64a118040e11140c90380e61243d0b220808105841c10b01c0d4104d0046036922050346001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 593114361 1250 593113111 593113127
    0x1005180105130c08070e03071a07060e061303120f02030f041e12050c0c031e0c06041409150406090207031b0c05010e0f040603050303092104030809130c 67
    0x21400b0740800c1d00e0700d0b1000c004038020195031480070f840703403080750302c40001c2181d21040391303a48240c051007151000181d0039611032403800c118039200d01c80740d01c410b810310388002542d480300c001003002e41c41102403180c0aa107040031300040c90740c141480d62600050a01e000301030060340441da01100d20100030800c29000c21030400380f18511402501c4c5162426001d010303102c8008040142a0b94984101a88050f002e040240280000d00f01256050500600000e26222040002d4011100b00c40c210b45e01c20b5004010006411400f2070b4014203090911901c114504941020320b8030901c403c1c2c0201d010020341110881000002420602080d83c0303030800103011b03520800301200029643d01d130cc140426803103480060b5541e030103600b06040900c0c0000454069141003e4194408220700d4142011b80d901c0c4503440080d807254028503101c1c540b00452380d0a100e0302c01a41c44040038040c0a03c91041072203401c540550b5802260903403268601d2020071402c1e0800302c4071880941c0b9100d00407040c43d40001d40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 593115611 1250 593114361 593114369
    0x9031a010f0902070b010b0c030c0a12020f07150807090e090d080105180123060d0c020114070503041e060207061e060e0408070302030702090a0c090b040b0d0510051801 74
    0x9450700650b0382400008911034010043c0c2222404001401031a50100060580c00c80070741c1142d0424110304046c60502d00d10020442c5c030400b51040080c0d8207501882030070f422a071101c0c0900001031401c100030040d004009050700410800000180080b4000c4840401400040c900001180350001280342c0e00d0700441c0310100840c10607000051203107413200d403029081c0c40918009015920b042c20035001c4800300c80181d608106408803090392511004080c003a032202d000c01c04520700d01c02043c003901f1036100d00c002a402182c07035010003041c59084011690440d90045803101d801000f070303c0c52014651160b0b801041a4000200c400074001c00b42c0000300f008100200e07543e04110fa40890501f181c80b50702c911a82c41c41d00c0d00004005c9840310b00030b0b00f001c3d03003e030041d249005001da001901c503607012105185d03042d50f610003510803154041201c101500340c1649071841e01d81005060f89260142e0309558200030703100c00000e8035400c40e00303850500030000070303111403204c0100c1e41b2500c00364402405 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 593116861 1250 593115611 593115629
    0x2806050a020901050d1e021c060501030b090f131a0712050115050310121a010e0c040909020a0512011d0318090a1107030c060507030c021b0109031a01 66
    0x20119a03031640901c00c0750804a016118249003016008003003021340203054078105807a80080480040640d240010031030002d4036607600c110388070705100d26401c0300c190750051810540750803000c00d03241e2601d0740a507400590780c0034101d100c0c1d81c40385540305007400a00801400000f240608031880b81d81440139a01600083e11088541c0003294442402c90b1002d00c6000242c4c08138261140d00d86000c1c1008640140d2240c00e55401c8a072121111643c078100f048045a070198144503c07002261041221f80c05841c2024401c156030800c000c50f40b15a00980c000d40c03001c5960781c6001000c560b0355030307a078000821000c0e04407440e002142c0c3c031b054000c1070124516246040d030500011115007010089808802807464191500190501030003051316009141e000f050b9030702c504c0d4001d00d1007980080c0201603c0381c1c2d51040807406519103030064ac0c0c006002c58041c981054003c1d4403a03034001c2141c40f180255920014100d040c103000494100c00036900c09415228200c000c1e0101190f883e140380d0603294032030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 593118111 1250 593116861 593116871
    0x729072f0f1009060507061103090a0510090201051b010209100908010c18090203090f01060902040614130303050f090402040801200a090b160203030c1b27092806 71
    0x82800540a041e00000b0005103d1000601c10b450203003001e0309056002c2e5800040d007102602c03000420790710a85010030f10f039000c1107001040000c1080030240b0102010b906000740356039640080c0081c01051032091008c243d01d450940c0000d025811340b044040c0040c204809480002005002902c01d070158940d00e500788402e0084a6000300350424203001d807a00803102c440c0c41d08003120025000503140b01c100d8006c0210b40c65a000d401d02540000d0a614440107945518001d0702a0034000801c0807500b804074140220040b00145c130041c401266003509081d9a50b003528400b545061190511040e0b101d80b0114000c11071200c1584807040141c0400d03024400d1a480c1c0343c65401500031040c00500140301c00c80c007480480320f23036409481d814a000700714152440ba958002825034100d014184115031000120170854203409200505224041d1005400324040b402103131008981211005481d03041c400c041903004108001d18200c000c0140d02c0548050300d84120740161287d00c4805035070150503e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 593119361 1250 593118111 593118139
    0x30902040c12051e040f023d08160c060b061804050603030721020313090c0905060f0708070f170a020123070f1205090c030729072f 58
    0x10803981c0301107903075148000007a607860750384200d5481e084000326004100110110505038540d00c0c0007006102d244501d9101c0d4541e0407401110300e03901d00b020801c200c0b8170014003480ac0c180e100381403d07810892038101412080b5040140240a1559a464004c13034001400c089000f40d21071100b151910444051145844860030981c0d6030180000c00344c1307005c45c4100321000b084000070007010103441d940141d03030a14440707440c23419040b00c15602c46607903a40c44901810010750700030301200141904031006801c00056109402440c01040d100600c007050021b0403034103012000ea0014902603001520844c030070042d4001145503001418000050360a000a450414450650380c0068016904104c2c21540e01d81e401101c0905c409807000c0c09103c074000039045000b4407070040c14400d108210007051414282010f1520b80491503100c00c02035001071144030088012800740c10008580b4409090715013805061264000c0109032a20343e00400c242900d890441d0058410785c0d080b601254071018010320 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 593120611 1250 593119361 593119381
    0x6120504030917070801050411030610150509060d021b1002070b06061b010c0e1c0b011e0b04090506180609010303030f14090304080f1204060c03030902040c1205 71
    0x40d500100400d0010a00f440105010003000c1c1c41c2000310700c1110750265840c1d040d80e085840680701a01c0180c11141d01100e941410484a90024440350284403814545400451104070b980c0300c1d80100038000540031103583d10340042d1f481d1a8040a400c40d5a13030b03c0d160a4080410442200101d14000d400d11002000c80600c2a1228107810804140142d52010100705140d40145d1103030340c084501d101011100a000d100d22180c42d26681c8920840b1005441041000142d2070341c1c000c0349001c0614800c00047d18044ce06045415400685000d010111011041c2c00d02c2504a00144a00070030001103039001600014050001505c151001e80ca80000304240001d08071360342c07600180d200004200091290784100c4141032146000182c1c0d4190504100c100d0700203441c54406070303101007424071122070241b0140d82203c911740001d007040941c105181c3c0081c003885c420b20003840307000141d94003894000c1d0001c0007400d0b4020403c2044070600403020700411254026410fa0300d02d018001011000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 593121861 1250 593120611 593120621
    0xa0608010b190618030605040507030311010b030318030f0f062d0601080711070b0316180303080901110a0203030421021f0f0501260607211e02040612 66
    0x2d0000b1040c54007400c000c01a20300019400003089041020300d00080841c040e8031950740110703c950068030b100c502e0760500421003480c200c95000580d01d0200446190341d00001200c1003000040141d6501c16034910010f82050310a0a051000f4041c03004900c8240c5408034031103101d000825001245041c4520015100040308030221905250280204032a58042c1c40000d0b40714aea0352811042c056451880d00342080c0b0a40c0c040380b0302c3e01000c8107211114151564800310500b103407410300c0b55600c070840c2584c1182810300c00941400036503008103600000c00e40082a0303c5200701680c56680e808605d0080d580d40c4102c90654804110a440301010381e010001060312400c0743e17009140000f5902d00310440f0380c0300c28808500d81c5580d80e030342117510715050142a000b00b5501607400d4000d00080080da040c3c0074080c20303c02c00f981102042010141c0c00c0031244a00051540541021641e00000300d80104042c20f10b04802c10547c14500d080c000042d001002915841c4e50352030b040b90000009201512 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 593123111 1250 593121861 593121889
    0xa18050a0e060a090f090c1e05091f060804020f0315071101020403050a03050702010815030a0602090d0b010b130f0b030a0c05190302030a0c111b12060a0608010b 71
    0x320008800c0144080c0c01c40119000200100400700169840c00510121000a11148012519500e0820620207500c1007a00104a000102403030283d01c0409000e02c01c0643c001d00e81304040d0b01011480d01003ea03401808101c0601d900601501e8603a100a480c1e00c2046404a00c945000407030450241404a0030721100d041010035154191500c070816107050302c414504a805650074000003020880411503481c895029172102590b60313007a400010403262004100c0c200c114080304400541c2e48000078582c880c80d40018006803a2031a0000040c1d60070040107002c1d10881032500003041d186c000030001c4c0b142014000d04040303420340c1c4000007040c10340c06204480c40c05030300b44001484d0710001c2c0c01c00c0c04550a1450b02501d8141690070413904070510b000f072000002d9000c0100500b0b1040340c82030036803003005800d10124081c0b02c01401640c070000d43c0501c0c1205030003e0394021304c6488604182404146240a41c2c1c9a0b2511840c07035401440c00c0d00c9400c4883d0308000300c91002c1d040400c0700d186d001c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 593124361 1250 593123111 593123119
    0x22209200909070305191508010e03070809060a0912050105070305180601050d1a0f07121803030e120711100e0913110d0f0507050418020d050a02060f0a1805 69
    0x180e51400000c0c0c000b4000245110700c2802000246c1018a00c01d20500801c0d2544810624403a4100380a15086070a60258004143d00803c03001010543d2041a201000c90494529948035040881150340902c00c0d4003d010400c090f0441da030030814103410041c4142a41e0380d01b0081c960b42c8400f2810701b0140e40744d2030178164000c00c00500c101e091944402840b41d0040307024004000100d060300d0701107802150700103418030120090102c0d465014410000f28010018148100b01d6445081039071100c4900c0010705142c2e5800c14245071042c14846482000d0030070300c905443e02c4542c200103030f0900b07103515100d20030103e4a89000c0b01c18011009050a60030203410580301c5d070307502809004495880e85080d19a10000468840780e540e81c0b07603404040c188618191192809645880c604e40b1145810041c07159060807100a15850700181c60f07601c05404940083c03404a09090450030b00341d40c40c2c000703500480c0c0000c405000b104278200906840000e9922003001280c80700100d212541940109a48 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 593125611 1250 593124361 593124379
    0x60a0c14042306070302060417030f28020c0d09080102031003120215192901030209012715030b0303090d11030d02061503030702130222092009 63
    0x3068000c1a0640054000048241d032452410030010f81c4640101a04400580c0214108010010941c00400c5400001c0007450b040d0300b404203409100340c030002c0c004150400c1480780d0b0341480001004035103225070400408c6507260740c17560380c0c039441e0a201040341c030210300c0c05400080d01f000140700322481464500e01c449042ea00b103a59880c40c0c41c03a08000441107215564140d10006002a041c900850799800362119000701e51404034160b516548014050307482c45004880108280c20f0f0007805078409190069850351484010799000c4128043d41380c0d0321107400e01d601a807095100c40d28007600c541c0091001c0203000c45200700c0640c1c5003079846542541051004004a04100c4058881c26200b051b4040880d103000005c60703c3c0080590006005a004c0801d0041c2645041911019180150041c42c82c10440b07402080592103001594146542d00180c0003200c4420709200d800300048090006007a07030b0b5908050000f07000c40703800080941800140403501036540000303e6424800142054103 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 593126861 1250 593125611 593125619
    0x105090d060c110102030c040e0f0f040213060806131704120f1505090a03120b0f100302040506030403090e01060302070f020906040b0303070507031b060203310602060a0c1404 77
    0xc090000c820782e003001c0c052150380c0710100c800280040d41c40362100c000050344541c500441410200e40141c811960040b851041c007299804240a482d0300c242c056814061810030403c0070401015903510a0419014107030502c21440c51030002c1d001114080c9450010003000c01c818140103104601c110700410b94640c641c403002a81a845515000d40503001108417074039174841c40810740d1011204e43c80950004081d440406070001d034400503d005d004010000e045607070000c100f004826141c190b21078030070850520803051007601103802914000e40b81c107403031381040d280203450b1440a01a1140c04100c003000451911310910903990780d141c00179040140c2250035001d2001e4108003400c0c1c1a0019107500c8882d005403401c0005091481c03150005121040c0340d428024610300181c44500351136072111404100042d800402d803011480544a52180760000003030f2075010006e0220743c0f0300200c180a40c00129550085921446800301d400240001030605500701c450782408420410040010300043c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 593128111 1250 593126861 593126873
    0x30a0506060a080721080d06080102031b0a0e010305061306030f0c0b0a0c0201050715060f030209090c09061e1c0510090210030e0a0606030f050f0606010207171c110c0105090d 77
    0x618064000c0380c1b440e2512071b5002d0000165540d513000414241c2d0004140660800d4860300c600030040384009190411070442002810b030044600d0752410581c5400200b0946c6daa007403450044003c01d9034040100039500c1c580405015041c0c1001e0352080d040210026502240b0811141e051003203607100070500c06207034019211500801000e545902d90904002c00d0b650880c0708040c00750440c144444100d03031951040040e8078000404e820500e802000c0300b135031181c980c201619080303107003114008140d125002d09401000c011280e103541c070540c1d01101124806d1482181034116005406071012005540c1941069440b6600021b4100c4028500884018825071002000c40500707000d0740e11840581d03c606064030740f280c109481621781e43c40c02d141044002c21600302440640d20242c500c919200d00041e44a6081d44101e50942110103600c402443c014407081c60070712050b482001c00c03142080d10091048075503480c030000d288146000d002c41076024505440c0c145100801420703a039085980e6407 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 593129361 1250 593128111 593128169
    0xf0c0f050712050a0203071b090e1c030b120d03050406050a0504151d01050114281a0405060a08010501020c0d260c030a080405070e13060506030c030a0506060a0807 72
    0x13101140418440500050840218080304070010540f6042880c10800304034210b42614842d002c02d540000c0c02c07114102440000d0701c15280c0e09050008801c000080811206030301e0104140c042d029044043d0a85a050390000c0d00507402540e0420003991040b100d60f0455000743c401400700d030042c2c002500003649a8101089120f480d000c01400b1380060068107094035000c3e048a039401c44000c2421100d810000c2500400548110002500181ea548440701400450240156081000c2d00c002c40c1a80c01004480c010f000107010203a40e6a8260350007041ca2400b03004e51401405000400c60591804c0d110700e103001d5400404101901c241c1c80d03a4101903095010a20b240324006110b0314444542c18000781c00140d405480362442c601d0145012030811a2a41003200b800681100f84220039009040c0d40b0f900c280e1142001440341c075200f00003850040c841241d95818402c14010004200c800b03d46603004400a482c1078001e15202d0154540b9503900b1300442c1d0b03000350484540c1052103848810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 593130611 1250 593129361 593129377
    0x60e042304030201230118141b2116030e0c010507020301091e05010c2303070909020d0b1c020f010f11010c0906110c090703020d0204090f0c0f05071205 67
    0x1c07640f0b080324086408540e64042444892505d9004011640c40c4101500c41030310411001c00c600d900425000b00107040180040e50f402003244025440450b01c0c1c01140d825108005100c0703001051140460b002000407075664100e4002038800081450090144800d50b840c1303040a82441038640c001110720f03401101050703038150b48680198004c6900482c80400039450f510780d0178000d0902c0d062040c207407842d54080c042005140303e2040401001c40303e0201c15980380c0d030074042d600d8640e00c000f00c41175002c60300031a0a4a02c005440b02113800a035020140312802910024400c2c0294038103100f10400c070120182d0803044401d030605072503101e00c480d4000890582044402071250010f8282100e201032003c0d40070605100013071010f590003501c80d2510b541a90000d050812078080411100a4090101c03070506401003102c02c034080d41e60701910041d10380c801007004060100030308440a4885900401d000c900c1400350004801d00c02e008480c0e880f0b4000030900d80f2981a0203040780c0c0c0da407100c51 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 593131861 1250 593130611 593130613
    0x5010309020f04060306021908040f03050703020f010501080c0a05060708030c03190c0210180f0b06010c050a05010204060e0d050604020607110d2402041428030507060e0423040302 79
    0xb03080d801075545211300d10145000b1800107854034004100362000e0001a02c03040288200c030020400010003d80000c0f10a80d072515016880c2e02980c031b8268684140c4c50040c0401c0d500f0000089581c00000070014001e40d0102c3c1c007100b0320340c0e4900c1401220b00c9400700183c0005410400516944520001144c101c000c401a000000c0741701c00b0072401b00c1d20807401c090f005800203d00f00b140203074a801003606064201243c00c1e41501665904001210003000c02000000707808006a400e030b008645251280d1340000a0f104101e040c2e24209000398018040c50020410301d1248913168100b02118070803259200009002c3c944417a02001100d822904040f19522050380040d101d030b0f2034149045200c1031140e0001200350a00700c85c1d00741c0c07402c0e6885000740c3d560301c10b020410007641044500d860320f800c20346255540e1502c00c01048d116082d9250400c5504c092004000308000c2c000800360211041d0790b480b0f2515800a50400095946518040e80380c4410b13000d0348940c0910740c01d802500284240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 593133111 1250 593131861 593131879
    0x1303020d03060b0906180d0b060a090506011b02041506210203040c090b0d0f08120705130302010c0512070c1a3117011e150b070c0918020102010c030504020303040501030902 76
    0x2d0008004100c401403c88e1500a0442403260a00f000880721025040840c424009403078000002002c1790811804118100448207030101552903607400030000020316110811820340310000603005040c26100100d51080c13110030f43c00c03482c24510947e0f016035400310002000a24003075881c0080e2000301c240d150300082d4146a000013070310901409113100d11030b031511900c1385c1001200301400240202080c040c048204900c0140d00c41c07071029942a26824240a0511106400c202d0b02e49204512586404580000d500c000c1c03016800440b0106c81440c13102426850b00c080081081e030041802c03090300a40060f541c980380500e6800103d401042c1034402d030510703c1d96181158008004640c96203c45d0355903a04c4060b8083d401041c103403411040010500000318040051409034255105024170310101064001c1081404d4280e0b1005000f4001c00340441a203080d0205603e1403000d01c100d02541c07078800000186c038068000d040c800e94005000c2c0d41000d14050040d0060241c07d007040b64807071488 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 593134361 1250 593133111 593133157
    0xb07020111040609140a06080c070f08030703020309060c07050d080c0d11030115031a010f021006230d110609040608161a0724060e1303020d03060b0906 67
    0x8500544001d081564032200303120724010842d1000051041030034003806c81070b442402180e8011340560303005146614000d5865545040c084003141d04000000c011044c00030a2225566041c2c0145019402440c1564a00d46820302d40140c0c0d4821050014400d030040546d61080d10700810f5540c1d0301c02d014141051801c644054050219000c18074400154040403005102c001c3d4106008c070140c4001e0700b0b082000c003041c4602c40000440702440a810040300403201e14101d84244400e18001d04401410300900d03071651420082e042d1040416078900e15050000542c1d46030111044465907007081c0101e0546040c1401d001060340200041500551250b00001348503904210826403802c0d8201880804c03070800d1794640c040340e801d0128245182080c0615400325034801c1203051502c8540e0800681b10880030405030140000342c1c441c11950501300c04101c112201c14082002161090303003a5003421040305c10603422640d150190143c00b0f0300900904440f4203041c2c0c010841c14152001c84bc6400001c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 593135611 1250 593134361 593134391
    0x20f0a0e04140601050f060d02070201230706050c0304031e050c071d0108010204030201172203020a060c05032a070c0b1803120703030906060b040909111203070b070201 74
    0x1098030200d6000c1c0b08110a182202014480a0701408013210101c08030108400051840e0054001c1180708650026114086a000701074100ca19052100400030800240d44101c005421040c01513402a06007400034101d00f00c49030489100c0c0c1c2d4584c44089071300e8600b002103080d5060014001050240400c0003613103c00f0100600002811201c00c5108101801044d0040c040c00680c02802c150b030045c0020300060ba0400c05022411180040056981d513861301441d20a4405102c15540b40e41e1000d0800c06141c3d02244151601c1d00600c014001c0900540c01101c45101c1100c003c03008405c0c264881441c0005004904126125450720034106030711a1914080803150790300100c2800c00000380c0255002d840b148003081c001e01140070705102c951031289201e5903c1081001004c05076600b0308a400c00050b0b5009001400e05a0340c0a0b444030b494440030401081a80c3c0150346007032450f401c8244515014505e1105c40c0b2a002c055410100d9954502e4100342001d410071040d95201c001e28000000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 593136861 1250 593135611 593135639
    0xb0d0c1202030c0409060b0301120b09010b13060518040b180319091e03151e050702011e0504050304060c0203150c040611030316050a140304151b0c020f0a 68
    0x4458003540c4d55a5180c03000c01821103c440e4010540580d040c80100540c4503d6150501c0e01d64014600048035917410f10a503004088000046038031402c903144a0a0a04c001c2c0d0016040d590141c2e03c01200d070442c0300b0690300e4041e0446005040700701c2c0e240042d10f1081a07118141c02010003d00710b82c20a070008409002051142100f24002074a00b041000212139a0400c100c49440501c682d0b03103014110b485c0e4100030700c2d92800d80380035103803204100e1400034100340854840c40581c0c18100302c2c0d8100010000d005c1c110305041c1c81c0503200d0603140d030008800c242c41540c0c010b56020004602c0d207480c000c0f041c2c0d0014044030059a05000721243c010b0301041e17404803144120020301c003103907466090410103000e600c1810310881181c0c2c001d0041100480440c040b00a913071000d0700340192680c0c02020700302e90b840046960310b42d1601f404820f2200f04501610103103010716861038184025405012001c100d5000c4940c4280098141ca00c3d100c05801d0145401d040c81c14054175034030069840d1109429949 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 593138111 1250 593136861 593136871
    0x30f0b0d0609022115190e1e0c0a0e0c0708030a09061104030b06010c06020d02040915060206040803071d060417010b030f03040522050709080106050405010b0d0c120203 74
    0x50784542d09042145050108012400100c6903e100c80315550504242d0364030744412040c15101c1c0c00004182030f80103995080400c040e06610520500070080c10050711015001c100b07458411509100d4400d0b80030204542e403440c03902a10500700d952422031010038005000d803099181c640e00b04006404100301d9001148075082104022410b9142803400d00c0442e0112240101c4a071010b12040c000114040d00b001d410030340910b4a84e00d5600c41d4140b000c000c0c8600c2c41020049440024009440001c0360824030a100d030720480d031286581d40f0001030340c4a0070300b114000c101850400025440d41e006900c4000715510b60303620411512000340101e01a40d10540000344903820301c0b0604215484240541082c0020135001741942e03101d1040f469550340a14004c16224940340c0074011407440d480c0c035801e100d200303d00b1000e124604001701e029003041d02e10701442509500340740b00800d003418140900b5040b0f0f004036840d94503000c8903403842801481501c00303107030030002d0301c00b94000d03a05000c3c00550b00031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 593139361 1250 593138111 593138123
    0xb0f03060423100b0f07020126070c0201110f030a120b040c0306030b1602101817041d100b0a0302071a06030d261e01060c0b0f090d030f0b0d 62
    0x30700b0700c40f0300c4080818075a4444004000308200150b140344100040d01d80d85036081c2800710110302003050282da0344c60001d0200c0d0301c10901004000780c15900c08260140c05000b0303220b030700c840d050603403140e0f4454a0300811260f070755208000c11021030340300708000d81c0013021100c00080d070100a48001415610b90245140010b074859a0a01c244020001c3c2c40d5000702c010405001c1800d00354401940b1182c41455203c04980e0720050b503d01140341c214203040040d840a5070b801c8450802c0036411154006005601c407070345a001c2c20811001e2501c0d901d40c00b4030507505245001a291003540f0030190f100346a4041055003c1c0b103200300080000c0c120311401d00c3c49100c20607992800c43c040c145000e032945c8008041107416001070400314000305488451214403034941c60603030383c1c06420401c0d644031101d5102c65140f00c1000010b1180d400a40b9681880c821004082203884001c0c00030781b00c410544d080e0350142c10900111010702d0083d0f0040c11000c00128001c03601d100e80d80c000880700e000214040c0c80f2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 593140611 1250 593139361 593139431
    0x6150708040513091a07090308030c0a1403040f0b133e01090909020604080f060f150102251502030705010c0302070b01120203120304050d0212040b0f030604 69
    0x10615150720b20074400800840c040041030083d4440c17544d900802c600c0c18403d1032210b0302103010f0074030071100003000e580c002e80d8240d079a0902c800c1a80c030703031742c006045900098042c18440d903000d4440e10807203018540140d1034549000154990300e010030030280a1001000050244800083d590b8119042940210038060003103035030510701c03407855004c3d00702032551001907084030b01240c0e0300500114181c400c070000015090031148045101441140c20040f440c0c8542100034410690005d8282e100348000a001509501d13001001c1458181d03c00c04c40d80541c0007030184c581d040c0708903504035441000300700610440755516245059480500d41d06000140c00000e806001e0100074001c030414804d26245c11460404103031541c022440e0b060080c111242280b600c0503080d035804024441c800d2101103031480d900d040902c0c01c65914203403548404003502980c034440c1b40b800e90400642e8101c8010001251a0503a0301070f00100a0b03200030041d0b0350107960358500c1d1a21200025a6144070b030101d00310800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 593141861 1250 593140611 593140619
    0x105060a0b0f030c091e090c040b040603110f0313060f02040509010605130329240d080903010f1e0e031b01090506040305031e160e1c12030c050310030b0615070804 72
    0xd070303000000c0c00c423503011408201c2081184000170449044039150702d40055204020742210300c10348038182c10240f90300404030034066101074545001c02c0301031041344100094101345e04400213901a520403940d0105403072004008050291000b05156042c102ca081c2c200341e120b41c2d4064041da02c0d0700c138217110aa0700034000f800c42c48004038402c0d004a4444e004000c5402078440c42842a031104483d140942090350915040169207015039600c1c0600600038003002400c0c0f1002401866041845282401c070503401049502552048508641e03501c2c010b14034021200403694442545090500100d40d43c0d034216802084bc1804144e0065200355505503483c10011039001203801041052120314910344280459120124031030714500482d414502113052185000845c180c0e0824050700040e03a14150780d404125200c0109001e02d441c90300e04009060580c1011111400111410050301c84414820b01c00304940082e038540c8820010104031504190008031a01074015060807a004030380030400b0702c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 593143111 1250 593141861 593141869
    0x7031b02011b0216030f021f020d030609020703020601141302040e0708010806010b04050112060e070315080a0c0e040609081b0606090424022a0105060a0b0f030c091e 73
    0x100b000070480c4000c02001c01c0d8031850340c4080c48940f0004141c100e2000d040f00841d00d0704070320740180001e1410031201020107800301039207501d2000d00740030029182c81004540b5aa880c42034a0032590180c0c02011107a0a10aa1140b00f03040c0300d001d5a131254181441c1140604140010000b074444032810700d54074104200094048078040e00102800d8024a0040c0a205000025030b4122002482d0800c0c1c40400e25a20b02c00030102074100c042002594010000722a4040d0020061071100501d2107900759030383d800341611038054000003070004003506010800c0010310891030360041c0c058540080c0301c00c210b540301076065000c0062440c04072002280724540010902400341c0c480004c0d1480c1c4024640350f82daa030303000b28400c407103072440d9640300810040c0c440d120740c10780e4148000c04900c61081011042c100d00b01d024940394800c00780d0300b018005004d03820880b28100454052080b880e0074a80c030003000f04000c3c3c10013082c017070b13041c4014840c2601543c0c3c0c124850040203020300c4044c203464907034003c0c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 593144361 1250 593143111 593143151
    0x70306021308010e0a060519140613053303031606061202090703050403031d070e1311130f060b0d0c1409120307020306040501021b070e060907031b0201 67
    0x44101d41d140c25420940041e0100d090b498550b40111b0005190f603e081c0b10300400703068070036030080e92442c2054844004480c8080c490041c102205d060140d45200b00941055034011100d00d052590f01000303a10043c40b20704e024950300708481114140400c92074010900d19000390b000b109031228501403800902149204080117411040d140c030240c0c0e40c3d02d4010403123124026214a00b055902c3c2c0c00142814400c1d4042c108001c070300f0101102d600901c2c28015078840c3c0b24041c0414213072400c4045286541d0305810000d620758401c031a40f4484051404210071002c0d40c0e0300c0318240a840c0c0802010b504441e00c1204054013404c0d5005890701c0922148400310b901a0328400709206002c124030b5204100142910381600085035510f50f4a59000140c0342940540030000f90148151800c3c0010058190043d00c41d00c00704840302c10520a107050910307601c0415208060040003c4804107910b818004500c0d50f0100b41400d000c10741002c50a1480030301254000b03a400142d6462103040001102c45180d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 593145611 1250 593144361 593144369
    0x120a140a1a07020316050a0b0a05071107030b04030320030403050423010c0803131415160503040611040b0a090812131203140712200c130e0703060213 66
    0x1090195151501c00039503640f00300342e042a04181d050b600176040203010401583c03a03d41c0101c8901e4541003024021000d024281d0303440b008960803c600203610403000030b0040c1140c1d08400410a1a00c80c0c0d2400c2e0020150140041f41048802320b4442da04812003000f035000c0d40c40382da14641e456180803180700c071b4a0480c6250385c0c1c20b680c90044070001da070303030002c044861390340c00000c0e065503501c403900c80c0e595001e00b03404001d10f803c81d928182c04804001140d600441410501f64031b070f0070f0362110b403040f000f0b410340d00025000c100241302080210710154060020302c1c00302400c5914160325030040f2030752604101883c0000513074940003440044028480020002c1040c040765042250b0040d060182d002c003800385844040c5a5103000050505c40c24048030ba01c450412103e98900e02820300751500d02d0021005408204400886040c5180b07441c2c0244134800320302c002e04006c400f02c80030000c5020301404446901501d500742045204030034030141e00114410354006039982c0224481c51300707c1c0c000e980 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 593146861 1250 593145611 593145653
    0x60a2c0c031611010e0706200601060212070f080712030b04020c0309010806060904060f0807150e040b0f120c0a05060721050d020a05030402040b030a11120a140a 71
    0x705002c00d1449040e4000d02c10119070805040000e007040080b40180352502010030640b1410100084407a00440603610300c5002c2d0710b02041010200c50281c0d40c0340400c1c414000160310000000080b51091380c00351480394407030910440c03503024503240c2c00300941003080700b50354000e2010491902c8640600c5000a400b000355000d500b0044c060034400d80f64001e8031407079410301c45424001400d1b5920300d02200d82c0004024403c000980e04e4100000010740940070b401d0280c0303c2d9640228500c0b00381510150340c110b856460f03000311000340c0c2c10b00c00601035a09603030342c1140142a091009540b400d00011490ba08034009120300c1490904100c44035107158045401250200300304030120b4015507040140c50550394030808401c2d401f1a0480700b5104000764070b44c0e16840421622000c591210066009a000b00c034148101c1c6103807820141c139111044801018826411a9050b05090000903c2018004003007995031203200b81d01c80ca0343d1f620b803e00b840c2c1c100d508200846010420381003200300220031408 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 593148111 1250 593146861 593146867
    0xb1e0901060f09080604050f0d020102070b04020d030e12010b010201061a040b03090a0519031223070e040f0b090108070b03060609060c030a090e09030c070905060a2c0c 74
    0x1004141480018040c07103041103219040c481a0030300800a203001804020110786140c581410038039240c104544030220135010720341c00d0030b00451050080d50a4103420603007000f8592550f900b0807040108182c011000c3c070504440c4504242c4d06e40c10b0134100c01c65140c0020900c40641400242107440076000348852844100d414100c520300b400c241d505440440d20310b582e0f00c1c5c480300101403a101c03090500422500c01c0328003c0c00c1f480380180c480e900b02c0d4825118180900902031112040c0c0b40f141402c00000189240c19490a0489052203500110742c0d05011f400140340201003002d54202c9080314a2203903c8103103000c0b450908117103c500600da86409000401d080100080d418800680ba45206440c0800e500001d030355030504036094142103130122980d03582481d0b40506410401d00c00d0340300303241e110000240b0303c1d00007104480131a54120043d00c6606d04200c1254024000901629000840e001e80030a01e81c0c1002d4080101084950b0b05400d81c117041c02c09496010740040031000094018 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 593149361 1250 593148111 593148169
    0x11431030b0c03040c03050a080a030b010f02152a120604020f030f100b07120e060a0507170c1218030703021f0216140f040204082505060406030b 64
    0x380c1c0c0c1031900b01c640d0720340c803540d80c1e11030f401d0042481080750000b50071400350303190306001c0250b402d0007080c0101e0b190328140b00700d401d42e60054502c0340c1070024400141e00000707070011001c00c04090300c0d5031024103c2c1c4040007104118040000b100c1c02c4e4280c0c0c0f81551030010b441c00c125404514401e520681c1160258500412303c4c8425056000162045002103494008035180e0358940040030054000000c01d1038a03506a418803498005415903540302040540c030b60300071641171403000c84401240d661500703450900c650369501141d440040382e80e171003000c00744810119044180440c001d022242440661501140b029080041480c0d09509109074012101040103031215240106061060a9880c2a041091740d083e070404003024001640440ac00c4408501420202d0404501d21029541c0c10200c000c0300e01404100d11540c00354098035440082620515480c01d40101c0c86941c485072150fa01560b2000401c00d2504070781c1124000c80e80350189039240b81804540f12141c12001100441030040f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 593150611 1250 593149361 593149373
    0x91b0506090909070b030f0f090606031b2e08070e030604031209020904030f0f05070b060d1406010b070605060405041a0901060509010f0501030c02070609060c0201143103 75
    0x4030507140e030050381c140c1d002800c855414401c031340c002c00600c005140d4902d800c44c100d0101020490340c1108a1081501061049070001040c520900000c2c2c000c04031400d4003144810002d0030425a181e20038090004048011280c460842e100c0c51100ba411040a0707040a001c0e04048004040c035003040400d04502016603030005403a07400ca505410300214a050707030141107018165560002e90462800c409020415611012034400e110700795841007129041c20208655074414407402904c2e8044c03039408140c0900d008410104983c1c496180900c007070140c00d042c1c3e42001000d9101c1c850700000455040306010b484d000d4180e2000b012542086103240ca552785080000c0000c0c00611540507081c000707004290254032003809003200825022031584e6411b00c00d83c09841500520b1300003410040d0003056507000040310819951142c44030f900c2c080c100f0404440000c1d200400f83d040007035440d4107125480b5010300414a000012210740c1b80656008074040710002c80c400c14040b18503101b1780800200300d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 593151861 1250 593150611 593150617
    0x1b030f0403050607110a2622230f1207080313061715010306090617010b040203040218040515072c0f12011d0d120501030c05131e091b0506 61
    0x607100c00d96a08142400107031030940104a00f420b0002c0b00000384941001d0a00d010540d0381e81e0358414030707250440d2600100c254009e440b40d03000302005c019a0014605180140510240c1c0001508000030032001f111001d01e41142944080300c50b0300001f44401d44003030f401c0c1c0300070301a10f041c4c101594101c1c0ea030100380f901140010310311411000e844020f4211a07109421a00043c0380c9444103001c2c0c03546a10040d403614021507102d40456180c11101e0301642881d0098a200d9034005000b400d000000b200310401c0500d0050088855000d800707411001e800c51003080d280501510381e250035451090449112805051070607848a4120b5100c1d000100c1c4c0d110240e03801d524a040c0ca2010b4007803140d500c042d0141c50901081014007d6584501d0302c0740000090341300c0b01a003155249800301401030700190486400380409896044070f00c10611139400c041d000380641c80f40040d400200f40001e00d50324000c0b0030800b05000030136500e50911740203100603288071180421080b42d5002c030051074000059007500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 593153111 1250 593151861 593151863
    0x61116031b02031f0b09100303050f0c1b0111071a09030328081003030806010c02061306050406230d0e030d06091415090c1b030f0403050607110a 64
    0x465a25441642419000d080c101c59000d011038090f410700044e48290503100c9504000d41c2c92429080c00240c0c502100e20f01d00500680c4407402c3c4090440d1812905540404a03281550008110300396009108003c81182048640d07002100041c2c40700004110b01a10300640e1030716400840140081c2220f0640140340d0001100e0303540e81c40b4030000200381180a040380002d01c82e041040400020005035040311000c1040d507440f61241d5480c500c0c0141403500038000540014000d800058482d401010000f1a80380002e210a040c40c2d9181c103080c50341c4407150000e000040700410108140383c3c02c07020144031032249107010403808211a01c016410700a02b00d15124030340e00c03042c8503656258240200c6505944641c2c0c1440b40649032840c1d14054084a810703002c900b2540e80002c1c020f880403260300781c1186001007907640c60f501c4041d40002c0a40101c81d4943d0b980030b0f07006031401d4070078040004000019400360010744071491800d00c0c80c2000c10040c08503042c0f05a1411444c1e0040e070214a0780002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 593154361 1250 593153111 593153117
    0x604060929030c150c01060f081005070909020307090503160e0f0c0c0d020309100521370e0111030a02250f12051c05040203011b090306111603 63
    0x16010301c8001a1401c02100d54441d08138070414401e081208a6100800c1da240c40500244815580c0304070014441d400e0f403140110366003242c03225000c9840244c11041d002001c40c036104002689442012080b41e209544403004034601c0c003403c200c031741020722000100650310442400424030b0311400100810004104620b0019008002105201c0704c01c103035600e861841040341c12050f111080603540e640056400740c8501103400740907800d607101c1d40c200c80300401c11555144140250400e00302074800040e26205844252480c43d5500304ca02c6d00303103124143d10400c54511441d00d041746010498507018401c103200e0b41400700240841d20340504594001a249030f006a8400307172042c02000c1004c0208204036581810710842c1c0c144881c1d0a810302c12603004031001700f0880c940390b00554980c400c41d0014200380455184c40d0031069090740c800e50380140090001306541c0180100b815002c4034502c104804110303444024428402180300c0c4003000c001004c5000d18001043d11041c01030041c0400003810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 593155611 1250 593154361 593154431
    0x507020301020705030403050718060f050907121b03180f031b050706080603060f0136091b0905190e010b100915050301031e0c0314010506040609 64
    0x85440035811122001c1e0024181d86c0c1300c603140c0c60003a80fa0030542c820340703180c852829004803805400780301c0d240444030084010540c40e07160070b0920100e0880201280f003800440c5002c0c0c0d14541d410300032120001601014600002d00002014023240e00d400714120301d00403000c0c6000b0003e804103008940741d903014144194550780008030700c0c0d54180c00141c000d0a40c0904c010018500d6041041c6030300500045058408035074684e0703680008030f4000d1140f00300300406907022113480681c240503080b4031a5103100710b10140b0f05035640d0800fa200c641604032218200b150744c5180e0028010002c2c8041d20090209000508169004810300019914803ca20756074841030010a04000d5000045a5602400c204002009081d0241c2030404902c5041c80c0303400d10710b4003084414894030440f4140e035400303521101c0031603000c0c842000042c0d0100741121010980000800030500804078204036160800003c0741c030b807a0500511050364800d500c003910490a000b01c001090f4480728080d0742211040c400100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 593156861 1250 593155611 593155613
    0x110112060b0a05220b25020a0302150d020f2116050315130504050106050415030b040c080604151103060904060908090d030216080a03050304060209210114010905090705010507 77
    0x902030102c03001001e03401e50400d000203540e000801c042c04901e6020490031021b034014001c50584080c41100007540006e0900c000c0c8010311704079140781c20003266824964101501c03800c1800032a40440c41920040e00080b03250544801800c800c4000ca29500303a815600741002001201d2812400c142901840000b00005e04a802c0400d51481456001040ea00c03100150542d00c01c02800251800d40300f80d420001f011450b81001c1c0034144047c0b92034005110503e10350784941b40321281c0504211207910401500240e0500200400c40c001c034060220b0740b802ca2070640c0340400700c0e100c220703408511010510421070640d440d1001c5903030040d000b02c3c02080328005807604a0440c8034002900b0fa0217103040c6446010301d42d000400c00c1c20307031880404803481280c48030340203540ca55285034001d0000308104009800602690040c0003610310240560001000f02c0403801202400b121154071160355034251041d0702080300e1401d07401881014010001810548030a981310700260140d14140040098620 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 593158111 1250 593156861 593156887
    0x1719020103090611070b0105030f1b0409050105010b12010f12030e12010c090e0606030103020306180c0901030609061a061b0a08030a0504030f030203070e1c0609110112060b0a05 78
    0x3010b4282c0c001404c00c0f81451007600918250400c9034107032480c80c0540e0021445040010b19110404031880042c2440110550460a900001c4651a03001a200c07241c01c000100c0c240a040e001e071014618498640640310800711982c1c005031710049603024000801c0100c0300100c0d00d034010550301032901c02c0c07041011801044c04c052500522948642c42c1841060136294072480940c2680c2c08129040c905466070700400150740402e000195154104c040030410315001208540407200410003074908a0560700005900c00070300342e0065841640f10b200800401c030842c4124219900e10f43d4908808220f050003240d03907401500254121544141030503103540c4810011100141d40c00580c15641c0e00d492103820003c0d280a803011008a9603809030003011a0080c025a441120b1940c0c4128564080404220941070403102040702c4004540789080820582d010f4441c810b4011018201c500074088001840300b0042c11000b80814940003003402644114003c68110840301e107411929400040120 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 593159361 1250 593158111 593158121
    0x20702090c03061f08060f190506070c0b07051c0c1a09070b071104060e0705090d0f0506071d0d020603270706120b0603090d0f02100c020a0506011719020103 69
    0x10031300d001c800c1310000b0240740c0d210410070f202d904c0c140c80540300300307869806212400c0411111040d000030845801e001505115000d04030603405132104c1c030861aa2240500d0895206500036156500640c410398a01280303100004c00c00344551030310300040030003526400c0d4591600601d400d800d080420120b03041d02c10410482020303140d00c0f44440c0ea956040e1400d04070031062204006e0007542408400a5000c0015111602c611501d8031200d1820101c0c034100700c443c00c400642103551001c298104404241c0811280d4802d89260f200c4000c2940300320341d000d03114000c6003819803280a00c0901000143c49540542c0e07002503607211225880c40300c0c040310000c80588804110030502c11950002816a440004007006004d594002c105d555803c80a10000d840119000040740e0311994072012081c1c030400c09000403c1c55841907030b05407007013840e4000c00d03103c000303c030f100040c1e0043c80c02c2003d101c0b062054034010114a4040030000310b4000c9429100c4080d00c507590042c1130b800c1102c1017564000c0d040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 593160611 1250 593159361 593159389
    0x507030204080d260106020d0c03021c110c301203070f030f050c0403020d05010b1e0a12030801210b16080702010e03030604091106030c040305060901020702090c0306 73
    0xf568000c1031005001810100d00201d03d41c00c42204042c0030b0040031803009407074141c07081135000c1c0140d980e4600301030342d403c1e110308022001c40c40b80d0700078482ca0541920034281401c0043d651b50b00740c410a280850b20704007002c804103200703000e0801c6600404805407055050354410300b86d1680c0000d091a0000c0c00c000c4441c284400c144c000004120080c1d0740080c6c1445040900d440811924070304032948012034008540f00d04400b0003c00c010b101600d42543d82011242c0714400115078828041c0c042401410790f5450b28072654014900b9403007030310381071002d58041d0030048e819115210705034074000c0c1514418030070720b03030f51b1455189440c1d800c1c1003211034a658181c0201c1200d0640c1080041e0360150000c204544000402100205075942d2040c0640706d1040c861200960542c0c4842041000400a480c0c0c221208420fa036900d15407901c405014602c0348191040c46a03caa01d5800c285051039401007120503e6481000810011f9860f0a0b5640d001203030009015241c1d40ca0700d0204090065001c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 593161861 1250 593160611 593160613
    0x411090114130e01050f25020c0402030a020c010603060b040c080c16030903140303040c08030304050604480f08070b0d0f09051c090b1803031204030c02180f0a050703020408 76
    0x1080946c42d241d035112400703800d5550180c5178441d120311001c2401b500c0c16440c200140c01c109002c410b0703460b0a401450700912a81001894000041112401c4480700e6204842c1c2c1901e95415480e545414828040c5030307501d40c14030324040d1a01480300c00251140581c12101d190340c0440140c00e141c46170442c80003941d0310001e03d511281c3c0d80c243e003a41d80e40003101e04946588034050041800d10b008401d890003248d2010050003503444556842d524659400880d8500c1c00f14000c0d480031007001039000d480d81002e2980c140340000d416004e01d460040e0075800c801c00c80706a0000421000000003100f1003103400703002c21540c440e50101d2900000d480d05182c110422400c1034000400d10401044620341c0c00d031461800c900d0300081c0c540a0711000d00303902c81c94442d90b0050294034441000c0800c2e4406010000707003542e20f07040041c108a5195401600c2c21350000315810561001c605280000002c904c0e2a0702d00a00b4900c0c01080e01c0c05180c41c001d040151340f507240e0000c1880c15020760155005488500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 593163111 1250 593161861 593161871
    0x7020a0b040807090605461805130b04020102160e061e130510050604080f12070c03030c030905040204060f020c0d0233030109050411090114130e01 65
    0x80c2000550003078041c001541c01041d4002501100038401c5800319007001d0007a9910b54007902014500c009118509941d8403241b890401c0110010b8108528800b00a500d00c0421410300f0552071340b0045150030380d08120328150038008080080d90040c084994400710785a0aa6200d10040b400c0c846d42000c982006c600300c02d030101d1200201400c5034411041987c120004040c5540050340354801e68003050740001c6084000e14070021181c00240e4815103071006a80002d40e18800300c0d0716940300c2e6000c90305c50703000300c020300b0400032042c020b1090141030040614100788a9880c3c1e8907034481184401030500c0080c21950041500036030000c802004003c00c11911a41e0b51100584054400c1100f41d0060058401700310446c82d0988042c031506401421010706020361401c0054201040d00d41f0004492840028046884452000354060400302c00085994103003032900c225454900c1c3c8085225465020060040d01051030030034410400c200c52010025140881c0d5000600400e07405404139420b01c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 593164361 1250 593163111 593163119
    0x906070303060611120d0908070b040b01050315070f030e0c0a0b0406171e0402180a150801050f0f0604091a0708090d020615010e040e0c0103051e13060207020a 70
    0x10b50200d82202c5440d01c8451040d140340c00780139203c1300e03007a80c0c00c035001c1000e101c00c0b143c01c0410b511460040780700e41c02e52450000507072200700010804840c121110030802005000d0b80c1401e10610f00700300003400c2e1a0303c0a00b03219001400c0610041210300030180c1d2800365030101001084640d800020103851108015290500c040450f401405440e000c41e20303003428088040710880401b032080b00700007907520141c840b1403602450014040c00a036880344c0c540343c0340a14480e60300c0503030b40503002d001000903242c0b400e1401001002c400d80d004418031307450241001001c450641001d0b50200c00d00c41c080040303507601d000107401042c040074060002080d080041e5089166001624014192603c0b001c0c1240d4517440d4840c0d0790034922402d100103811000104081c401e00c0959690412814100210390301185400b09044414804c01b050305603200c0042188503507014852a500309821401c3c0341d494403400140400e01c810050941d030517041014420005103c015170654880076401002407004540c1e07 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 593165467 1106 593164361 593164367
    0x81c03021b030406020d11030702210703081b0c01020d0c170c060403030b1903031b05030307120c05040e19110f0a030b03010e190809060703 62
    0x240180074038148141841440c80304550000c1d6295850040e00030301c0c00782196401c005201692514806601e0f0100c200d820762174055900303d082181800400548180b0002d40c1c00c000e015044011040040d418010204072180080001190502d0003040b1346a152888105015a1201d0740c000d0801e070068500241090003410f0702d90a40300b41d01307013205496000f108030000640290040108041e014440c0b42d65040c000c0d219150000002d0b0080500c101281c000641405801451001c0c00152200c02e02c100b0f6034000c084c0da4a90600c6880038001c600400b04030311100741070042406002d1303c50b00c03e5130112a20403030b02010fa5100c01d41c403185500041040158056114298034803680381c0d6070000c09405031482102e03030703480082d03c100904603200501d1a41c86030341001241c00c6042000208600081284410315071607210b1440d02c1c1c2c0280c0719950300b9681000002c00c1050500d60 = true := by decide +kernel

theorem cover : BRFrame.Cov 592985611 593165467 := by
  have h0 := BRFrame.cov_init 592985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 592985611 ≤ n) (h2 : n < 593165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
