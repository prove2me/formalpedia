-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3936
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:06:43.083467+00:00
-- url     : https://prove2.me/submissions/9997ab11-660b-49d2-98c0-ebce5e31d85f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 707733812 ≤ n < 707913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 707735062 1250 707733812 707733823
    0x10060906031a06030606040e0a020301080d0801030c03151b030b0a060c1a09070f1401020114090a02131806090507120f06090204020403062f030601210f0e0a05 70
    0x301881d0501401141c03903440c42c9101c0c110485a40541030010020380962030700800c0314020f200c02d0066050710300d06803003581c00940081c007580b1802e000c0d44180b01051441054043e041e42c0d0081c0c4020302d80b510316070fa40f051800c0001c011a03403260310382c03841c40c03500c03000d00c4ad03078200c1c482c482e48003c00d13003400c80c0c800c0001550b180c1d0094400e00003010b8480c400b05010441120700191411b4083c0003070340721081c4640c0303400030f140d1180c000c1c00c400482c04030300307868400b02c200c0413000203070002d01c941010b510f0305c031201c40300403209610154400306481c405403801800910200d4024003001400501200700c403d9403030842001550300c1900d0701005401c1004c200480c0c0004c0c8503e00d0f00e030065201c9a554910501c1c401c001c00350a440d2149445010f55a840d81114029980070700d0400c01c030800710b00303500b04042459948401000103001020b40030808482228400c420582d40c210181440322801c40cac009040f1418003005030f980e00604042480b05208050310000307040020a1950038503e030007844c21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 707736312 1250 707735062 707735069
    0x32211062701031b050702040912051314060a08070917030a0810060804081b190203010f0504081c0902100309170c070339090b04050f040303051905100609 68
    0xd4035140c1e013000304400302c1c42c8900301141da500d0001d68815580c000540689041c1038060820040401d580c28040d4215000348050b5015542d20b694883e1394000300602c010f0340f1481039030082c10811040c3d4955100d030801c1680040705003010708640c0e46408406440140d0000c42e01c1182e4000600540015080802c00c1d81c00780b01d04044026050400c0c900404420300a40000d04001000c0340308202c10746104146040450384004030b5038640000021500300000298007030780039501c0d29280c0101440d0500440b4411604199460300e04180380004101209220029081d03d41d507400039000103945030a1031202c1c0d030000ea6804111309072141844140407070081e03120b1244810812000c0d0b441c07600071406500310394001c07088400780555003141e040303071143d040310340445081000fa68294644284a040080d00d9020300100515405031062204441701038600e10804140c0780d00050004c0e00c81d0300019807026a8114042300c1021741803841c0195881650071400d41c01000724107010550384455a08000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 707737562 1250 707736312 707736317
    0x140106030e06100b0307090314030a11060403020a020616170a0807020d0c081b01020a030e0c030111090d0203071d01090c080408031528051302032211062701 69
    0x580c1800303240c2d040c0312401c5100d409018140840000c406d035010308000001581c0000d507600c0080704c0140202c2d10b0707511044103500441c8000441d41c844c0038002a030305109680c182c00420382d40c00c2913020401150000404002030109440c006c0700042c081145440c14000d034610005d40f1250b181c04041c141001c010700c030f54110360081c40e9108100e54041140089a500860b1941d07507002071006100000355900c090f803000e580000f4805017030070383c164007001c80151071000323440c00d4000500816003a10954524000b04a009100242c8030b0701c0c1c00400d0242d05407000b8120351125507540115841c440d0241110a0010704080040000304158000d0070344d08d810a240c800715034a010754500c4003d01000d4510b8004101001852805072210343c1c80c0e207085850740b200640c10103a02c84079518a10b40e207004036801040c0c0265401403005050003603a0240e1181c034040851310386086d141c0c40b101488000c1c252100e0309031018100d026140c0f80010300b04110118a80c1e400015000b203000700501d040703800c4904 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 707738812 1250 707737562 707737573
    0xa140a05061302030106050a060c021504051e0a030606030311160302010c030815121014010506090907020c1305012904050d0311060a1b14030c1c140106030e 69
    0x54000701d80e440e4040701008450304010070794000b0900404450b0041500005050800f150b8250880507000407a03100b00d07000350104107480c1350203d1078007441c410260000380742100c25090800200c040110040040c0252072516600e80310042600c3c1154400e501040480c990301c0c1c3c4494040c030074003860442040c11450850306d181e000a118011104003c0c1c00c020512000c2104a101000201103c40300246102c81f80c02c80c800c501c80d100c248032914010640d241c1040c038001c004020b007000b41250001448036080c403000c1ca05100120800404510440c02040c00404681d6140040030044c001e052000286942c105140c0c0c00c0c1e4000c0040c000d42c07500300c191001c80303150802c1800b100c2c2034640560b415603121440340750070303680b140406030b049003103009050401c0090704069105420100d0141c20748000c09007091010b564484d207050b041000482c042000a0f503108004000389031011034170111215040c1510b4424003110502041041d42d200050010000190305006060b10404908003400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 707740062 1250 707738812 707738833
    0x21506010507060506040b031e1506090408071536330e011505060a090e1302030a1505060616060c020a02060d0c08070306081e0c0d050a14 61
    0x340140502d44006100944407000500b0944468201c03210400000d41124230080d038004d6039220884c0413010600c0c4d0b61142040183c40c6c1c00d560010726004200241030100d4a450b15142c408140d4072241e025074800000307000c40310320b0b01d4403031190586a420072525a0681031040a00b5000402034101c4001c0c1c02014001203030108502c4400030000580302d5074004003216120006245152411300303e40130051402c218054145019041218500305035000780556544910030490980101d80d00c61000a620042c24020503c3d5500b506400c610b002d2154a2030b5041940001c1c80e1000b01001112460f4001744002115481e42c00780701c3e0080000c40c0c0b01d50508086403403c480700403400c44042d050395200d42038152264001d0040741c4000307801804080d980e808088845028209410040001424020001d607625201c0d1040d1420307581c0c0c21020780020005d03880070062551900314941058003c0d0700c80550503945450780d00345080d202c0d001400e524a0203090204204107403080c40c003000c0d0409417545 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 707741312 1250 707740062 707740067
    0xd0305192c122a01080405191b06050706060b0405061c020f04120c0b07080306040c0e0916031112041704090212010314073c0909020102150601 63
    0x49100000c104050101c801e01d580081c461250034004050580222449800a00740c03d41c011401100030110850042c0403540044420000840c0c020300b213500984e266009141d4031440400003203000312000c50308070403580000600c03070701d50f50b2040c3c011400004ad000100b1540b405404001d1100000b01400c040c030f0724020400510400900d940c445c601000401b8205010b42e041e20684804648039548581d22440c00e01140e0407240410f4800c13090380075000a0a2282404484403540c0c801501e40c2551140f0303051102410010310a1030600140f07080400a5881e202c0c0e50a103c3c0c100020fa030034021100716005030455800215001001030200200700d1302e200c010300c590350460352101040402e9646c000c4900c5c018000d5420440c0302500020b05450310041c00842641601d0046804509074010788a141d95510700274807075012850710300b0302d16003182d9648602c0c856042c890103a581001e410044080980803001d03810800b27010fa40d17924078005550341007140d0305041c115000750341302a04010001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 707742562 1250 707741312 707741357
    0x30506090a060f152007061b0305040e04060f0c050d06060c02031213080a0c0f090e100b040b0909010501031b030c0504090c080a03121b1b050109020d030519 69
    0x41d00c201030140c4c8048590103104104c2414042241c000303814460a0521010792901d40500c113110028010362003216408580c42032441c41f203030307050300e4440c41c00e4502342032140c05100041040c0c0301c09075145910181404d0500070005040ea550380d070903680f010328111401c120340c0590884410419401030540042e20001804a520302e04203002903210426440314980108072038104040d280110b000314810080181c40780410b45035042c401e0301c100d64076442c4c850b0440e50b0142046520798804851113104050507400742043c004003400c0032810203900c0c004181d5803002910241010f070340d104010003e00084001071519021825040d6400c546191036818540241e0f00078144100c1e503624220b010004000307008002480039105075041403001e41000307442c100300789a080c02c1e032500301640600d808920b0702011103905401d4503100c0703c02111110720302141d84050b000f1100c0e5940d0346580c60250307a0782d248540f070b014403965809e0394980490015004014090914509210050b8040301960500444 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 707743812 1250 707742562 707742569
    0x10120203060f041112030403030e01030219030c140c060105040605010e010c1209050a030305091216090515040203010803210f16140409020c0c060a0e12030712030506090a060f 77
    0x201580d107850340d003003a1000018130103e440c1d20803005005003840c484040060f00880c3d000c0d48030072001c0310030000194249e10a182040c1400565110342c6660103000b503004c0340014481c0c0c9001192644010503142a40d4402c0c001c40d583d076800100100600c3ca02400340300003030182232820a1103040341c0000a800550600e400418108503241c600c01c29a100d140b0340381c004d0030b0003092040d005c0c0c1d032803c018025038803840b107142c01841e034903000e10302800000400c80c00c2c0c4d407216800b040300503240c4041180101405004d203c1c5000455040002c80e5a841c0051800382140f500030795034440803e04407001c402c4885040c100c003c0c00703075010003007002c91043c115940140c5107450000c0e002d40e00c0d003048074403044921803003d00c41800320303000c6001b121560181480200460844465024030000c02a80c1d00a06882100041d08440c22902508206a08200140e402c00849081078060750b1190714803e0540b6042d00000c0e6113000b000b80900d03211001c0d50700407400030001c1000b141840401c8450106900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 707745062 1250 707743812 707743831
    0x907030b0406090b09160c0204110c0c10050d0213080706020f07120503031b0c010504120908060408030a021c05010b180d050c1e04180c0b0f04180f02121012020306 72
    0xc6c100784d505014455641d0110b5004104100b194504103c0b172566030040300040f00c0c0c9101d00e10110110b410301024001d0400f40329140c807801d0451840460f0040e601100c4d070039030101c41d8054001501101088500083d124640140c2807180704058a140b4080d9a070780030f00c18100c02c1106400103e40c0200440350401254880c2c0710102c0d02c0280d20020501c100c841481c0950321b800104024000f00d1914040704150320b5840310301a5944007030b1141d940106580c0907203400c0d42040842c2c0101e42e02d07030003080c2202e80301101d4007020354501080c004a40d02603001c00601d1500062107051680f03050505513150008440b81e00c00c0c00242d80796130b42d9540704032002d00e014007040f414401c0024407620044440c07100040042c040000841068001d086003044100c4010740c0602c40032030b8030340350300040d48c0e50031840f1905141024907180f200c911004070001c481303030b415035a0040b0309449019400180b03124803c41c02c040e103480c10300741d407006003001c450f6009031516000c507502400140e4001c6109504910b100c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 707746312 1250 707745062 707745091
    0x308100303090b030406020f07051c050a05040e060a0e07030525050901180b0c0705030d05070f03080a09060501080610080712080f040f0e0a0605040504110607110907030b0406090b09 80
    0x345400d074000d110b814208002003802045280070410002f9402008400c00c000308041100030ba201628103010f120651710100342d0501040c00314075006641d651340040c00614400c01c140d5100d41d103110100060b24940f00103130300d07902008a00303400e00301a46035920a0101c0350b00c0c5481000d10050650062090b13890410400b602014003400b810b041400203003c00c1c030b5503940e50781326100e1007540c0c4a106200f11070107401000070502c415800740b01507440b95904400e401c0203511030360782c2c01c42d8640402030603142d0155949410034081241840b4040c0a040d00100404640c00d15448048844015a00062442d8011201071100000000c00d601c2042d03440070b03100e5115100103031414058081d6412900e105000e4820004e883d2042c1c001d07003401150110410811141c8542c240810b0742c00458015110b20b150141c4030540b03041c588010700e07000380528442c22040001c41700252900c03d0648800002903150740c14000c061070544101700050024032000c1000c00003c001003110b0300401042e6241400d00f0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 707747562 1250 707746312 707746321
    0x3090303032f0d0f0501030b0103080c0f0303070e030c0a42021515030a02100c02090f100801021602060715060b0d05060919360308100303090b03 64
    0x40800348019000b50a0109401845800710342500d40084204542c1c00303003089a401000003440c41454143c1e03030048418031031a82152902503007944418816038403481a10510005410240702075030103030311596280030b42560300c8410940707450707180c080807031244100d01c404000042564114403401840380350003d41c05c40304c410790008000c0e5149444582047c40c0c038070f504010341c3c0c082036188005258a1710a0f00c81c2e12543d00c00301c8000c82100d07a05425602120890000d4a000c800e41c240404940c40c10041c45140b48d400b1609030324040e0f892203c541c3c01c400500220034485200a40070380080c200842c100003a80c50200c2d820700f80200c1c0a4015600062070340c0501014800880042c0b050081c01e10000369906050141f9a110f02110007411307160030042101403500310951070041c020104151090055490440010010b25a903100503801d0f45c02c801c030100aa40c1c2d200c228650110030160702036065418003030042140103041d0f08000c0e030300d80c405000180c0c100c00243c0640d01071020860b200e644 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 707748812 1250 707747562 707747591
    0x103020f01091230021b1203120405300a090b0c0a02010e0111150c04080a08071e02090c0c030906030103350d020903010b04020a111203040309030303 66
    0x5a80c003c00031160540071241c0c00e10444061500f0652950760000380c1e41501c2451031280a286000640b0060300b0406104c107410030700030044481d850004281c21000c1c100e0b8802c0034650360010459801c0071005804000602c90f0500000c0c4410080c0c801440f1084c07890a188001904009007101c000c10021031240000c600c101d09050180c031840c010595101c085045c200d9444d07842031822030010743c0ca5076800085511881404038104044030040c0860074100f0000c10461000030894913000c41c0a0200084c480020041c0c0041d080c01403038001d607145494180b02148420362402090604d8404401500507121100016484011020210f03220000f03051918103501c6610305c102e900900c04000401400704007043d90400002d000d580490304018001020340041d0175005400c8004000d105081515095030010800c1035401400000d03407040c1c840c001012a004101d17a0380c00034511401d11030481e10700700090080806524a1f0300d0852030a980c0060054015001c018101500e4a42c400c1c2c8101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 707750062 1250 707748812 707748827
    0x20c06161e020406060c0510021e1e0a0306181a01050f070b01030309080f070501080c0702040908070614181e1908130509011a16062906120103020f01 66
    0x2580200140404c56850100411191040382c0071741d00350081001280e900c5a040c82100e0070100031441a0740c00d030307498840480d43d6400817510392552004070041d191205010400400310f030603054400043e00c80c00c0c003100e017400241c02ea144a5040e4941304129018540c00300030404004800d20700280d1b18822030009550234058160010300061550001000301a00003500340c042d50788481c202e600408900c0c00f83e60307641580d88130711400f2448040118514901c03560040209900241c00418050311590384ca501542c0f010000750307a001d03a60f1200902141c09043c0c00c94010a03103254400300090224031075600c40748246000d1764483d18803003e480c0e510300184514848120f2407c0c008400c0d420714106080d06a11170481c8040079503600341c0120301c502c3c00c0345c50305042c0d4030300300764510f01802c1941d025046648400f80002102160300f0500002500d01e00070001310145800010281181441c0040003e100c0c4a0000340301e003006014040e071814205041174116601100c403002c0e85155800140c4100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 707751312 1250 707750062 707750123
    0xb2508030c13080601240c02100e0607151a01021209040203060409020919051602030f070c12030c150908070b0c09040f05061e03030d02030a0f0c030c020c0616 70
    0x13400b0305000010103002203040341500f001c1101c43c0e100c400d1082441101e4000141c480250700503642889070040e28070540501544040240240b8604030050322030a080104c01848107454907242d200404042030307000484c0340040d0081c0000e092503050107000030206d00400e00300c0c9000340d60100000e615503643d0780202900603009000f031000c07820001481520f40008040841c1303007900300380100e42d0704901c06244a40e01c02496000d941403080680810310710303a02210003a06c4041c20410045044500010004c4800d4441e4560041944140c5060015030040c8081092a61b280044030b0021500c2d4104444040394004a51300f625501c0681940311030280b01180c0d6006490400454030b00e01066100c07900450080742c280c07000c000301c501855507241c0803d07103007a096002440101c0c1c00c160703103802554001e00107802c00b0900441d0024544104d440c080d04410002c1d07203600d5000c00340750701400116101103050f25100d150401c0d2440e05040c4130721450f0020103000000038802012490010300d845d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 707752562 1250 707751312 707751329
    0x150c04030204020d050f010b09010c080306030f0114010602120f042d0b0912070b22031703011d040c060c11120d080c030403020a02040c0c0c0b2508030c13 68
    0x4c510788035110700014001114840030459004001003038801d1200103581000805070341c0c484800006907641080b07500040c101c660141703e400290507030320704203010302e4903a2003113141d44040b0796140c040020b151103c2c1c91851800406d040054840b074001e440304031002d4498420045411024094662030a1454054091840b080c03088003c2040150240180300901013211420700840e003840c0b02548500661044001c00d0b0b408100ca02007100a1030003c0000384042502d0200c482e0f569112800c10050180c3c05c1c0c10400c00003c0144001c0c10108401a18136451200045091500d03a449201d521250b00540c0c0912505d0303050001089800c00d02c1640b84500035004c1d56581c41e00c0c080b400d9464100c016104081200f81e0b001901c40c03181001921b124903055402801040080c0d001d004c018100000038408001080c1e00d4900803c0c1481c5040000302004034203140da520a10000c20031a406400c550b103000b54810000d2404254020309503a041200c081d030b8295a500804181c540e0301da010b9100598 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 707753812 1250 707752562 707752567
    0x6060212030402121006050a0506030f04061d061f15170a02130b040e01062a032a0302010c0e0105040905130c030b0103021c02031c020111040905060a0501020f150c0403020402 77
    0x41c007290603001b41c1c0880700c007500e18043d96601d03a420040d031030108a800001d02544500000d000ca4000d030488041d4200d9400051358001c440c0e91103504011044902448030f0103034014140b60f4103100441c2d140140004c5080a541174001c9030b00031b000e60000c8010250035003090000c59a207115640c1210719401a06195a19080d950400d812064100384030b28500180001c0001803a507009401002d2500358030b0100c070300c50701c103411410130201d8007044003642009581c6000c0c040c0751241c2081280414082184011908490300d4002e09440c01c4041d00340070001090800c0025036004803d45e07094070f070130360030110302645c80d900c00d00c504c0c0030600406801c0110442c0c000080c080c11041c118180c0f8002c0d01c4103288660010390600c2c903448800703070080d010341c410300c100c50440203401d10308410024180b00104400100c0081081650410b4001c1d910383e039651402d10540385081c1c480305006100a001400c40a03010200340c036200e50880803c071401260003000103030703541c0a00044a020b5640103100710b4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 707755062 1250 707753812 707753833
    0x5060309060604152d060f120905010f0c0810050303160b060d0219140a051f020703020901091a0306070f0c0503130306140916090911060a0e10030606021203040212 72
    0x1885013407032061188405c03002e502180880c8500701d201c00e200c03000d407106000d1502186e2060300416034034105940c103560b0740030583d070044e11500070102024500d0b41c0e00095401e144100a035400c02c0c0b5404240300358000c1100048030109030813842e440c55003040d150a1140e075100085416444c00302002980600e280100c1a84800c0252510054801403032581e00607420388014400d520340c280c098564419540c58250506003403040e808040c4c071842d0310544500540d80e5011a007500020b80000503003a0b22041000700060201c00042010b000890003083c482c1403118000c2c1c4110002a0300324100042e084071101403210410403240500c0801a039200303138564070704101009001944140006010000114038114400030f4448001c9a031003207081449854044000000c01103ca0200d03040f440001d45241c89617281005815200c2d2251952020016030408114020341003203401014149040790904c212076001580d804000a599502075880e1194000106035401c80c100c58a03241c498414480e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 707756312 1250 707755062 707755109
    0x30304050607120e100e0309030604050c040c05091c03051c140f270f0307110a0b1305091b0a0f141206060703030e030f090a0506030906060415 63
    0x161141070070f590340d02d800d078400040003c140c0d02c0f654107190f0340c0e0b84031241c4500c440d202c5a22081c42c0c101c100c811640341600c00c030040ba0030031004076000d44894011000c40020307070400b400740440c00d05841c07030010325114984d40002c0242c0510102c44c04d100120f4005102098001d6040782d110008038001c0314008441d00d1040302c060070340e002c91203607400514804942d070080f0b00030403540034a91040000000740601401d1400001c1e00d030345800500d116158603403507900002e000038808a40520242200321800b10180120840580d200b00c0d2002c904004c0200d2080d40f540c400e030140d401c100c8007160a82c640e2058841031704440c107907507120b1007000240c0d42d2415800841e40b1641e08100d88403201d603032018090401c40c5004000610707403014901000a0850b160040c010135105200b801d0004601090105441c40c680040a80c00346c0b211001a2400c228074119040d40001c0c50b04407401490340c546640003d0302c2c2e900c080c03c0c06d07000d69200c160301c0740c407451619030300c00c0500300b11100c41803419000c0503107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 707757562 1250 707756312 707756323
    0xa0909060e0a080c0c04090809040b040605180907140a0303030903030207021f0816171807170f03070804060e0f04050a091707030801030b1306050a02041509030b0601030e030c03030405 81
    0x13440341c2032107419207220482c00c0078002c84020542002115050108400912000d8511901c1807948142c3d101c101040c107681c3d011080050400f440b4540e030341c1c0d2078000c250314500300041d0030481c4401c001e0000a909075841d90110001c0d07d074180f03004903101c602440c003034003e8040d001d002076100a42c0e440a13043c1520030140a0350310340071a500c40842c3e8903060f154000c512082461540002c00b118910b40300381d804011040d4120000180304220a00d40d03aa5850410489802440388514608040340035030804000c40007035844440c003e9031034180c40c0d50351801075118510582045c4614400019060ba9860001c07030852400508144014038064bd40080200b020038030131100314030210394104000054400b503901c4550305440b0000641d0854a81c01c00220000b05103d607003074401c400e1007000881c4c0380a01401010200400b585031810175103d2440311101035040c6c1c0401c09440400c0010503408492540c1060f428240092a105250b0b1754901350711884801200c00c3c4000010f100402c500081e0703 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 707758812 1250 707757562 707757577
    0x7030e1e0f0d0308060f0102190812010803041511010f06180c03050f06010e060c190309120b07080903160f03030e150c030a0e06070804120e0a0909060e0a08 69
    0x280c40140024031030811120110406003d00050b80a100080150504080440742c5510500466049400c428030030040806003080458071100b0100e00254400700001400d405020703640040d500f01420052004800c0750401d0340c03039007007091581a043c4102d00070b41c00004000d0040500f4002941c451503680805540d01c0c8050051070311301078220070707030310b119106503070203004104d05a00c4643c54003001100d68031110710300e2039444030040021540003036040114105480364071024180d4210181406000541c5076844100a8a000e01c0d078500050200ca00d80350b480030142c2442900c903110105100e14502a02c0c0e078a03052485078080d0300080c0f0040b64a003c440c18401d6405100b82d2a030b10760340980b81c0750000c0c102e4101c00180710225880c07081da00e0141d640a0662031000807030000d00314246152010954503a008110f40300140700034031010801584000c1001d0070a440b00c501c10601061402e040c80c410400b2160b9034425000030440c4d650008150030081c40c04a5800440500308400203034000361 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 707760062 1250 707758812 707758819
    0x521041b050402041409071b11030613020102030d200c010212060a030302060f1306050439030213110307020d0f03180602090d05030406020a050f12090607030e1e 71
    0x340001420714080c02180d040d80c0007003913403800d40341803c014442402c00c09021072041c004900c0001500034000f681e040f01d404c0c050b6003000c00d5003581c40181820003401808503a8940d800041c883c016036000001c480310f20441c5c02c40029462852109082c202807040c49440b030440000680001900c41500940645583c042d284607070347e200d1108008042169203c02005600300b0400a42d82c000c9044515a001074011108041d1420503079468088900894088402c03101c0c803004400640c6006040c1100941e100460003c2034110fa1401030740c03024030b44002132291584c07001440300000103411894a0541008103e5128200b223600a9114000a800c2600003050501c0c08541c2c0c0b031003801002414031186001c8001c6a03610f49910010750b000d00d00340c03500301060040c1000094401c100070001070549902410382d28813035103425824580c0a603c0c0740d5a60f40072119041a1515803800c071188142c0440341e035580c803c2a45800c1d64280c2c00c000045074002040e0780c58520304c03c014840100030340002c4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 707761312 1250 707760062 707760113
    0xd290102011803090e090a051609050a090203191b08010b28051002031608040911032203180605070b070f0f05090a031514071e052104 59
    0x809550310382d0290070740c01400003804040104103195074000c1d078581151010003907847c4280700b43c6071249022000112035440c07451035081000a01c1080c4522034100d44515000d0140b8210394000a60b255036491800c030140103500151000c118000d0401e4181103a1444101ca882c3c1d6207021850007084882010741c068071145209001c0409142c040c0c20100b10704000c0c1c4200c1034141010b02500501406401056100c104080203108031840b000480c0544034030f00342d596450900007171405882c401803a1070011306051060189020104070568440400b407000d016400e1254102101d99510054000c2480f21303200e400801c91581c00740003441400d000d02034400071030311000c004842c0b0003581e082050000e004440c0c410000c0c1d201300000c2c5002c081c000c00040c1d0141d00c075114042e80c06000055030044030341c2d580714400f0030000d10321580c0e480070243c1060548210b0745024402042130b0f003e0504100900001c1d01c48400b40810034006600d0b4040710040810716041c0b40076070f0000c01201040c1e4000510 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 707762562 1250 707761312 707761331
    0x1a03090705062d0d143705060d02090a141005010219020109090c020102040305070b040e010603150e0403020309042f0c070839060f0d29010201 63
    0x2004503103581141c2e00d4024a845061440305140a0301090b482c0c05680d010403100034440c401d17001e482e20717164524a030720304c4504110309040d0080480c1c8120302490091801000c00c060b100b104242054502d404010805549610008070340420004c0e00940c000690070511110302801c1d406080d00e0450850115465114058090306410180c41501d00580c0062507141140341c070218520322030352040c101400c0c1c10307440f1400303038080d03e003e00341940050b0742c00700d401c0003400000c2003801c0042218001d8540b070241400c9112080703240501483c0141030300c420020529001003440c11005200103002d000060510345002510303130f8801107086204074280f00010f0a0044680141d8400d42851030b885210394180b8080700c40c06410900701419140550080080c950605008400d912503100e044151140c080250040c205440304003040f003001001c01a0741d0954071a0720031200154954692151260f60046c0304401410111f000d00800700118481444107107980340f44c810700305400340c00038080c9005 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 707763812 1250 707762562 707762569
    0xe0f01060b190503041e050114070309020901090e0304170a120305191a010c03050702150c160e010902090f0411030108010e011107030503040f080316080603160e0a061a03090705 78
    0x200b500c01411b4110107142590000700c800b0b09410100c0c1c800c40001c18049a10603508003403010032039041000c2511141000214070b0300d896154050295540100b0211421260b0240e480c0030b14000c1070b1200c0c0e201c1c1d000ea10019070070090550a164441c0c404201c035203000d0390040140100b91120f60b01c0149080307107842810035901a81d0110310000100141c002c54220044854088030a405d801b032000c1017080c0000f44e160000d561030320b90a40c0030b4460344d40c500c01c2c880510708103002c255541e0201d2020b50500c0855500d8106904552a282c40940c9a403001000070f15035503101c8980503803240ca402e811a83e410b94260145040703842c0c4900030030044a20484103801e82e40c04002044000c0410040301001078001c0c000f8540090054100d803181c003000d5602c41c0b10a40c0150f51003160511502d4201c102c140e44045216400302003900500200c904018101911114a00515003a5000c0c2000207100301100d038489802008810741d58401c400b0125030003000c0e40d006442c01c56482c05000c2d40820700b0b04 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 707765062 1250 707763812 707763817
    0x9020a08010b1e130308030414060c0a0905010e0a0e0a0b03070506130302151b01051f051804060e0709140610170405030d09060e250303030e0f01060b1905 68
    0x4440d011655455080c3c0030408106500101c40080201000d4902102184032800550b204606c41c05484c00003c540c82d020070714203e030040c11600c064a08002c1c040529074040641021600e0a081003988803c050380001c100b01c3c0c05030012514040303980c0400c66444107940000c1d202d0300042e0140c81c4407131f440d0030611030382d445469500c881c40700a60b0000c0006080c0b594a060302842d504446130308000b170340c90b2450203030481103084502c035a4403a0140049150443c1d141180088440301c060725991402001c0703191a0300550301c0f60010341c100030000b0b00b80803658100e08240340100d425a02c2d101d4907952220300408070403621020004441002603500d00703000000c1c010883c1e498454459540007980159540c40d4014812109070005001800ba08200c07805600c0d1f00328402d43c000726400c51000395107841c1134000070f0020303603031400160b4a4621100c0750300e070441965054580840d070640b40d00c0e00c00d840c000c52503412405e903602c1c00310b001502300340210240c02c500580e119520a00030102c00221200d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 707766312 1250 707765062 707765077
    0x303010f0506030606070c08100b03070302010e0405090109230f030c060c0c0f06040f020f01090608150307030b010f03030906030905070e060d0f12030e0a0f11060408030409020a08010b 81
    0x80000d08414070292501c1030145a000d031008110f103103032801035668141a154175034050001c55120b6a45080a03034828010ba8140840c2a002404040c0c82d40d00020720715011007075841c2c000ca40c0c1e0070104402403001c2d007000c1c0302c298014103440c440760000340c12140c40c07210301103e121880c0034a480b040c0e0124004411a400030441100078040760b1a451401c10982e401108c4c5181141b0912142500d1004280100d510403401609802c404a40a00500c101d5002c0d41d4092810800320030018040e071904108110707049034906007074070b2411702d0b403c0c00710b890035a4540000e41030065810000850b141684003040a80c0d2203681c90f0440c80343d0300c2800f60140c510b141002403143e00807410600c520755680b80281d40c0220028003007640f07007440303450740104100d2400f42a9103000088944103561038040c0038003410605039200a0005d900e9a48501001a10a081c001c003c44501c000b29403095403010280d41c0a8561141607a40e5284c0d1032800c4c000035071003000050b0108085030b00010b02c0c00200030a035100c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 707767562 1250 707766312 707766329
    0x903020d0e0406030f110102030c07090605040c03090c030b15060301180b01180e0c0d0e0d020f0d0c02060c030f0307080a050f0421031503050303060a0909020a210b0f04020909030301 80
    0x113209141e031003013807003601c1203c091f04510062200000021041101c03c1c020300c400f01001404601340024031046d01d20341600c0034241400e251200e00000e1244202c0b20440b504003a981c016922190320b02281d502080304000c0d4098408000411806003a40c2040e5810300703052010001d000001c00107584018044006507081c4143e80020403080b0182c0170419804450043c01ca803034158448c20070b00031258040c0b01d558060748000e8a8150003034040100d207818642c28001810a140d4445008100c16140c41d8000d001c2c12010404941c216000c00503600010303841c00016440b80b40841d00102040c100f00e510b1450581085c0201d2101d02c80d080340d107406260000103120021004084010354032243c1c0ea107080030160760f100d0341d1440d0724140f038141c809180302e40040c5d907580c144003041100c20302d00c42d080a001380349400c20140050b40d89c00039000c04c8880c41c044c44555410280c1c0c110380920320511002d00000c01d100100410a244d009a4901c0380c1d1007224a00d5036030301c03444401c1741d13240401d000702d080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 707768812 1250 707767562 707767583
    0x150d0303090804090608030901031409030711040204053307030507030e030f070f03031206050105092b060b1806240904060b030907080a0308010b09130903020d0e040603 74
    0x10034400d410091056000302526032805640e180a0012030702503074000d203841c1d00f000c9040001d960b45405100348030007003808a20340606103400b0564681c410140300070100c000e5061088a6500c558050f10b005003001400c0424001e1114540b40d491036151a620440d04042210030000d02e040c4400c1d660420b4065a40d5404c4c441c00c2d07a42030f40c20301c400d4400e080d0f06210701c0004001c603090800c47c2c000500f0094103d02e07051440e518014100d0f0b601d041803004040d05101d400d0040d82d0b80003081e26460325044032143c0080040070a161060919401c1001541d800c007081ca03001d014881d00801d41052040c1c40b11680f05807880101980ba45081d41c0d00390b80902000700c140002200388071045014100c0414075481e103900f00303000600311030880d8031228100202004000d41220140315260041031200c0141510740240e69009100301414002c1d540d1944010508280e281ca50108104140c561060204030105560401070755510548400e800007494640c140001c40c14640103510031aa03100c4041030703 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 707770062 1250 707768812 707768839
    0x62006010b0d09020901090b01170606070807170d150e040b1b0417071e0b07061e150906090605090105060a0327030e01080c0a030c050f0d0f0515 64
    0x1400d42d0006010340d240e15150001e500150f0398400c0c6040c001d105000c80002c56102c010000350090b9a84103402050718400c904106054403490708030f588c410b0748a01e60b95070780c0d4103e241052010100b035190001a000114014002c00381c186d2102c1c4011101c194681100e43d42c410a0008450045600070035000107040817a1001d070007200e001c07102c40000c0d40c07024209511015020034030700c0120a02c001c00d50210b00c0410500741c000ba01001092810070030001400d080522007409403141c080c00401040d900c1000d41300717000c0e45a02520381c0d000004c10901034500c7c40d5801c1d0f548c1f03146c240106c00200b45040d800140120640c80386200310b40006d0414070150b0f20b40410803107260460300d855028145ca90320402e5609003100e0b03003520a001d95121115442200303081c01011003045901c513a050003da03000344812440c94006980e03a50005183c045900801c2d00411542c9000e007001e081d000348008100559504455040003a00c940c600004000d140e4a1054064001500f00300e001d4001910b62880c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 707771312 1250 707770062 707770079
    0x3060f120212010e0a06050a0c110616021c020f100627060f0e040314130512070308030c1c0b0a0510031107030e0306060a0608070c03030f060801020406200601 70
    0x240d402c00c641c000001d4980415420506100507480c00301d60003661103080091500ca00c2c850a228504140b9004a07080c068500c000d6413810081c007041c481c20352485001c01540d1007001510581e05a0075400134030769040d240065500c46000300c41e110203000c2d110440e0b4012000303204040c2101c60681d020f1100300e10200396090240d14049825410369180c00012072200b14407a41c540080480e075040d030507649000c3c200201000160042d56621035401c0004e4492800714142d61425100f0031906a03560421140e07103e481c1c0034041e4001020790001008000984408401078901052807007140408480741d01001030846260303420495018040010a010310b003000e51405552100d941000107564020303000c920b400d6080301c2800c40c006801c851640c052400c05000541e0003d0042d1071001d0141d052a4001d060344100608000030010b01e01c03600414988203400c100460301c0050410441c01d80c03140745079400303035116005040124214100040e104552861942d1030b0001c040041d1103540d0800511 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 707772562 1250 707771312 707771329
    0x203070f0510110a173c090304030b0f010e041e1b090c1701090c0c0510050709122015041d060904050c131103090c041109210f0a0b01030303060f1202 66
    0x40c120040342204540c0c1d4072102d07030000d80c02404504001c50f127032865850240825440107140409510b034200040116541c0c00d5a03454001c0d0340100c6022803000320460401d0002c5460401601c0203a11a51031022081d840501200342c03001c40c0c509021010202000340c41c00004450081c1080104000401040780c90380c0c44900c1000c0c8601c0c0c60305401c6015290350b854440d03940307010b4441e141d030b40341030001c0e15030064032120003401846401c2500b003a040d2540766120301032200703069100c400c44c440d040d12982c034003107403156400c0d69aa120b5112500c4e4141104d024007000c0e03150021000e00c4002c0f17031207844e010505500c601d07440002400201003840c180300c440501620740798413130350f220f0028608180710403011b10320074010369000b4080540c094041000f41c1e00000e1b503501c45001c041110040640741c10300044031016100010f038042044001c40b45190406200d0000320314024601c0d01000c00c040058039078101da0080e9014481c2c161502c1050103945581d00c1a02c4810a13401315200050400006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 707773812 1250 707772562 707772631
    0x60902180d031e030f0501120f02010c060f090809030f030720060d0f05060f4216030305151c02031203091e0c010203070f0510110a17 59
    0x8050b80040001c001d0244000f5056801002181c0c803000240c407050141e228050050400c08070b600e002100586441c3d4400d642204042d0401183d004e0500604c8645d80041000c400c3d020f004010035019411b10030b4042e004030304800d11a020344640b91048035030020075240e445820109022a07003052401406100c246000c41542208040c041c060740c510f098851704511203894500440c403450b1030000c0100d4861030f01c0ca120700c107902c2e041c0c00c601400240380100082d007611102c00490b0b5800c850054051004182c143e10703032407400146400016241d1401039030414032a0318184403030744526000300e001d00d000c2c80c1c6003900502d62941024040310010074441000d4005030a40d540304d10b00000e0741113268000c8944840542c050621341d071006016040b82508040518040d0640244400000f074980c81084000703010f00e5050480c450070b1003010300011404040d003800130400100a964000b407035030420100300010603060b1007400091021001c065100b06414840c500c1e01d00b04881e07400e440914840d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 707775062 1250 707773812 707773817
    0x15011403070f03350d0203010501080609010b0a0e010201060f0621020304050d1b05010c0207081608030405060f0f180f0d0c031515030506010f1707030215070b040c030501060902180d03 81
    0x120304901303088205008007031080340780d00096aa9810000054070186002e80418041d801e044010040040550140c4049205501e885410b004202004034003400d81c42d0800c11145443c2c000004070207402c40c8144541c21701e036003103104c00401076900340400c81c0001c03540038040d42c1104007541000740c441c0c400448990341d075170076101c00d0028039180c40b400c4503005024400581e112601c00d001d104410880101c0d00c40c0980400c4c10b980b17041c500b120307869004511460b4000c0c0400b142451307203c084401950045106000c0c0192161500d100d001c81b0a4112070b2070901030a4240044c84144c10580014000d107900b00c03206525140c9140e4550300c410254111844109a803807075081100081c98003010000c500990003032120354101003003400d01d030070b842d030005c81031740a8403004081e038150201e804c1e030841e074040301e54500240c8030500c22011486101001001c071812a000c100401c40c05101c4001582d00440c020002191600455003c038410b031154091200090140c0e20220300d40086c04118807403103031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 707776312 1250 707775062 707775143
    0x30207120c0324051506041202010219060c0801140f010e01090503030d020c060a06060801060c0f0c150e15070209150a18050603010b010c0b0915011403070f03 70
    0xc0e11010040840202c8103c108580c102102d80e510b1824014590001000c1c603042070700030003500001c0e40c1e0b8822881405182980454130700250784c000c0c403002c0301161020b14030001c500d441c1c0c030f0020004d00d5400c410001141c0513100100d05600c500c00340170070180002d0120b41e21100410015500c0c00074503c0740c1e60402003600d0020615071010320217001c0c072044095015031519041201e660418100410350705c05145020030401c042603004500504640d0300d424680c14403900ca040c182c02041a030f40c8003815405200100156082c03503d8140410100c1944e51466040d420804200030f0240701d4086000403102400f94402501e0621221500704042d1044060700207600008280c143c20b081d80600301c00c0c12040d03030f1488100698010f4070341c400310450081121600620002c0e20b04841440c026103038240308000103c601008121100364801542c010071032070740c5d641c41d10950181c0100d0003c1d00a001d1454009182d40075920703c001583c1e400382c0b030030309040e50007130145000581c240d4120001c003408 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 707777562 1250 707776312 707776319
    0xb0a0609020a11060a09050c060a180311030f0a030f0e010306080a0b0414030f12130f081e1c092a030209090604020d12030e120307030612030207120c 66
    0x8034401003804481c607850f100e452401100102c0e041c5180106211515400d10f950080000c0001c100181120000c0b1080c50300c0311610441218000494000000c1140b900031010040c414550700756128090114101c2d6110074801ca000344d01c845e403140c001004115032020004045002d003405000201061400042c201e6844060030701c0e00711110f1043c0c40302040741003400248040f40c9003022000d00754100852600c0c40401003004944a41c0c81294044141040415203020702010202e00b07654001841c80100505401d14a41c01e80c404003450b500740c0d07000144402004050001e44100641038503150a0103901d000961004d081415022100b1300b48a0600005400c3e41280c0d9400070400d13001841c50702d900790f01c103106514001400024481e072048042100582e01e6148100503940d02000c4442c8945c02d00d601035010f003a01200c80c0c1140c0c015040440e80c0500e0400155108550700e690500c651a43c4148030314101c501c985c8040c0040e00694007c0c07051030b00c00307610f00c9900d5115400340d601050f41d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 707778812 1250 707777562 707777579
    0xa030e093d080a031b03050906030907210c051507140607021e0309190f030302240603030f1e030c0c101e180f080403050d0e0a030b0a06 60
    0x1240c5020708101140324200d51240214403200601600c200070007002460300350346002d449058802030503080c00c0442c5810004141c0b184054030480c40e0301815550b180d0810a240d00c0e284c3e40e090107040444c2c10b15010140c400304007003054401d11034009400c55452400c04050240c40307415050940300d000010040840000e10b9407502c0104080c0a034040c000a04101900030b04201c1640c502c160303941180841441c0ca40ca0110494810707840444245d081c06681b5090340b40c008017161721a10b10260001000000d041d004034640b0004407540b8100c190400b039031400d00190050503124550540e0050080c03020030381c406801041104003941e90b4841e03d0201e100d610384964070031a5008400314020651111030b4104120b81000500520418030800d6401c404408902a802407101b0140f42c8907409a4821075101d4440f000154002201c00003039038003800c1a441540c4184400c403040d04c50304800c00e41440c882c1c1c0d090b0120040060641c1d4501d40780d0380b11180440340203000107600d19541d1000048040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 707780062 1250 707778812 707778871
    0x4050f061311040501030b0604090516230402210a020d1b03051b0d0b010c0204020d090c06030b0d0f290a060515093616020a030e09 58
    0xc0d1000e442100400e00d0501e02440782d419040380030b10300748401440007410500d0400d43c1b08034261000134050b10507081103407078908142081d0071003407080d4038041400300b5210f860499845001610502488014050004920906102c08030305207645041105c0c0446103011306400c8108540c0c094144001076620008540324020800038140300d0790366200a00b40c03d800b40541c0015803845151034010540c010010301e00c83c2c0c50061812658801c41c00a550f0300860f402e0f82c080b03070041e20031134031942082c8121000f41200402690802e00001000401034442e01a0810481026028000305111513480300d034080c8503003000721100c520901015610120854508500000d8a02c4400722404d101421500312151600514015a8072419070320302a100c0c0e40854a0b011030581d0320500a4181500107a4040000c045e00b5000303441c0d04071a0b40281d0710720b16445002d5040e038841440503912028043c0d94460182000402041d9400c40d03031409490403040669100702000102d400d40d042c122841c10100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 707781312 1250 707780062 707780071
    0x3061207060512070807020a03052d180d0503180a0510030c03051305070b0d1b11010c1b12030204050d03200c210307081b0d1409060304050f06 63
    0x1a4022509420354a000500f1540180c51800c2c403001a05000600035155608114041c0034004002070482174803602a4001411400300300311001007189088101005900540310310f012200300c5a2902d010780343c4202c909000c0e95000004503d800084000240003c5944d44950f610640800001507a901c5600200b0803200055500050780301c50f00070302400700ea01c050708031001841c2c40070401c0300103540002d940c1c041c0c0c1c40040140b0740301c40e4814102c00180094684050000300c0c80e00041c0000e80d000329014042185001c000d0103a0034601c00c045900c44400500b02c2c0720b0740c8906115030089909210b51580380e40451501510381500c40740403411030000d4450840000b0400c012925614a040002c0d441116000e8007501c502e400c000009060610241d1180142c020b560780804101142002100c400c2c80d803003e803240d2140e00b80f10000810802d4401e40703039891f018010b10207103040c2c41659064104031285030110b05080d0b40e00d040c44880d0700700400890b214130420200128200d42040801c0c4079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 707782562 1250 707781312 707781317
    0x708011205150f100b090607021e0409050a060c0f080601030f0b0303161b03020906060d06030f0c0810060812070f0614061305060901090e0a0c060509010e06040b09060306120706 78
    0x104c0c00c080401c1602c1e41d00c203510020352600c06001c404040d50f00c00040312845901183c14114840040101c1d060014403205480e504c03519211061040080204014920901920080007011822401985c010142c280e44900288140380000e56640c001c0e030210305114006034000807001c4d1150046441e40d40000650b803403031a03880c41000c003003000d040e01009200020303162041d111841e5a020882d8610040e20b81481514041000801080c1582c0311400641d04108114081001070919584050b51030140441901400c00c07038148900150090a08413407014005080242c000300b50030a40390004001190b226403010300001c00300d8003034010443d50b0240ba0f09152454100030040211507585000c01d501c0d80c5043c41c04008075680e40203c02030459400e4207020800b07070350242105051042c40d2034000c0c100e110400c004140c00794880b0103014119000e80f203c000b018004070420000c0c0c01284541ca00040c010019604641841806143c1142d000307071408400341c44a04060f82090000e0304441c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 707783812 1250 707782562 707782591
    0x61407050609060118090b07030513061806050a140103020114130b0d05240d0812040b0601030b06091e040603080406050702090a0b060d110f041e0e070801120515 71
    0x3c941800c0010144100501750104080045599601480c2030000e0500c0709040c2e80780b00064008418501880b1841e40c4420100300c0d41250701d103504080c0e5a80801642e200e4039140c00541920314500c24031803403c800ca10422600c0c1c0c0ba607401100d0703805545501405805040c81031003000c5000c01c6640010744121102c040d01c0c0c080d1031152070110340004028408140209000ca800d05000c0804000b03d1042920254810051070400c00a18403400b981b8003205001c01b4100028004640c400c903006140c2640c05000310189081008828014103c481d5031048105a83c52907280083c5546032050398090b2000c0380181d580d171988600343d08182c1c405004190001110030443c074241c8180b030780c003000a600c01c00a04410b9004512107004059074000010707950604044c0411012080d1a9043d02503103009544544400e00f4000c14140440340f0706686210100108402040441c6903108603483d50f101c00050717180041321240303e503201100b65500c0c00740d074031600780700000030710403038071415130b4101c00b99 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 707785062 1250 707783812 707783819
    0x110f0d12180f08040f1d10121b030f030c051e1225030207092a0c0f0605010b0913020c06130309050303120612010b03062d090109120c0209010614070506090601 70
    0x70806c0070040081c6c944100d03c0c8401c0c08406e801d610280d04032030304501c0d031a03201c01c4c00901c1012002c405c2e0708058268213810503040d042582c04241e802d01d20380305105662121003980c42050283c1106011a00301d0b81050980d0311102540002520b420700c9880c40c0b00801007030b100011440d40c80c0d98402903006070000344043c440c7c5040d90066000038081d00d489a208105d0152852400303074880b00c1d02c030042040714107407001400080f5100c50580e40c2c0014042025507901d140c94469648a206118020f800300301c24890403021501c203440b14000518090000e981d510a0440c0c44d40c00d58060071414884c01402c0840c003510100040c1c00b124203030321607001083c2080c00030002c2002000c03251603082d80c1410800c1010f5100802c40982200c0e0286040104000c0e80c4000f0100300ca46880e016082010300c1c0410030841e905421100f4054020f2908011440070741d41d044600304030b0400069041000d440040018a1081584800c64140710a0080c20a484c41d5202405d2034429980446c0c01e078071140051 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 707786312 1250 707785062 707785109
    0x1140103050f0f0c030709091505101508150f0a0e040303050a0e19080d0905012306150a050a120c0903031b11040c110f0d12180f08040f 60
    0x103620910f07010080c81088501400681e030b403401c40c02400381094a840c441402c102040081b5110030010a0062041e880c00b051500c82c003014602c40c13071049010300a182c1c0d1080307008040e1715000c1d4154070800c03201c0f0180c12050050524440310820f4000342e5404c40000d4003020800800c0c040c3c0c0c403075500400c160810b080c60400365480e088040d0a160000700c1d0b02e40d40042280190740c0c62607400019030384ca51500000140003451600c02c0a80f807542030003d42d03400003051605405012031300d1000c08017030342c5a0a0600c18103d1500d481d4250000d402c0112020140c0107101034240d403c104d1034016001c00080d07100d14151a19090540040b070f03000300c030074000c05800080948404c0b00004009000c40700030b855070740d81c0450000d01c0380e00803aa41d005414040780b0036003000f054800d894044030f480c04542e814140c4d44042c10307072403c0009060f100078001e2480719400707076088a4030303035002d001e95054258442804145e00202c2c00c17070341e10108010014950603000120001000032078913200940707103104401c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 707787562 1250 707786312 707786323
    0x6120c07061104050603060909160305070e010b161502090d060b04110316140c0f1609140726090d030b09040b0c070f15061404110f090301140103050f 66
    0x500b60348030003800184955245c3c0d0003513a40c0f0000807564000300b62284110b580c100703051641c241544085400c07001c0107100e0006041401c4915441d00740030b4503a0703034414034003541c064010061480c0300d0502200000c22038003000120158031541c00140340c10076030000281d000c01d140d0760444d455a1520000b074181c0c0b400d84940b554201c04030b004e503882d603c1c04200010b80902194125400d00c07409014000505a14505444031402220125805045000000e580d624149058000e0100b208003021940c82c0c001d00035400d80256400003850562501d650543c0c0d6032140721032008c101002c0d05514480e080c1102c03840c50046c840400a400242c4040d080201a02e20008642d401094520306100c001100014195030001c07640300307102c0e1104150305d03100d4411071071800702403e4040000140000c00d0019070008088543d04401d8244035400c100030b00090741e8069014201800b000e0003060400c03104240240a0807800800000d0008004c010084038180c003130700161503d500610080c110054200710 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 707788812 1250 707787562 707787581
    0x1605090d150f1517100c030209100e0303030a050601031e0606090f0b04060507050f0102031f1203081504060302090a0b0913080304020f0d141f0e030904090206120c0706 74
    0xb09100007614040b050001200741e205940286044121803218a4010f10205a401c90a035005001004050300010084c2d00090401071060880c20660080180200b03030070004407001074060750660307898141c01001400c0080240381496103900c2861b40070740703101c8110101c8016414001030303941c0c10541e00030400e000540001c00c50102c248420f000c04c41c138001c01d17203049030018544981e54420a15205083c00808450386409600100600034504200c1420240c109009400d50104a035694018500d41501e000c0140c0800d000001141140002550074107800030042c002041c0c0303d5a0741e0100c0d05540c400c80380f0002c516031314051030341c5a01e0030342c00e11904111365401c004901d08054881c458580b1020b40001c0c030902c07105000c0c20090300c80301d001200c4150800b04819100b2680041140c4604d0100580c02c0c1288240342402e44222032881b980c0c5000b26210020342c1024000300510005068001c800c4c0e07801641444001800f0440060079880742c42d5016485880d0413161602400b034401e90300c1d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 707790062 1250 707788812 707788841
    0xc0d0306080316170702060412020f0609010512090c1314060406060504060807032307030e06130f0501021e040609090501050d030e0a0306060605090f0306040b1605090d15 75
    0x2075858688000103d100c0603580020141505911140150115200b8490300035003001c00802c000859410b26004860345600907150384401030b001804125180c4a020031a41c0860401e000c0350303140c2010f03022095072109420f030454582502410010340700c1c900d40e10b07110304082d8541c41040c166481818409810520070398040c4405414158050100d025501580701001056000204104e20076003080d600611014408a04804401e0a500c2c91002c1260312002090a04a060303c161b0300001c3c03024803030841d01c01202850211950b902d030940a5002c010346040d902401070841e102c41114103201c0381d907070f00c000b159610782ca040340c064101d140c1075000000c200c1c54800100141d032901101102c6065062500040505601d40002e100d03244c183c01c05403c0c0b91030f110b4046501504040100b907d49021500211220384480030196a0b02c401c40b0018058400900881e009010115511001815506000717080c04042408180e260700490b00c1a503100410804d03440340c0401900c035401c1e01a0416 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 707791312 1250 707790062 707790067
    0xc03150e010e030901030b09092505130c020c010c11100c02030f070303090906061d01020a140102031509040c14060c1906060b09030c241305040b010819020a11030c0d03060803 77
    0x1003d04ac0c44208041d44001c10803e0883d1b0344040c5400707040788101400c0d0060418540380270100380680203040c1c01e07001c4809442025039403a050360017002d00c0d904499000c05034001d43e07196001032003021a00c10a050040c480d039400b0050040c0d409000e04280907151100801489285040040403020150300408819240100c18441641d0208081c0c000d642c45141e0041c0030400503004070300c0c20020700b0740580000d0307030802180c140340819001140a400f0800b904510545407104004002d001500c4c01060b22550303c00400203494007940c4d548c1c031218000c00f50380c105000166110300741480380c040121042400351480041021038072030348001d044400305060610a59801095a1344025400c040c4074181c0c030000e42d0b02c04540103d243c1100e4a289404649500c074042d006024141c050080c0d82c4102e007044e4a0b012194451030010740b0503501c7d1011010524841c0c21048020b6106400c01c1007000416080c2e0040030204000a21400111000070918581c040700300a00301c1d141c1d81c110000c0380d0003c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 707792562 1250 707791312 707791321
    0x61903050132010e0904030e09070e03210f0301030501090b1e0601080c1b010b12010b0109030f060603020409081207030b0d06050933090105040c03150e010e030901030b09 75
    0x160814050201c078140c82e5200712004090060b07441c001440005944400074004000406501050208481d28203840c4813006c2d8861700016151100c20141c3c1507050360200c00901038a030920b0b43c0f5a802201035210711441d1551a00c0c400f03403a03600981043d54640e44410490003084144418160700c04a115401e050103115896201242c80c40904558104034176100441c1007004610115110184a01041d20b51281d486003843d0290981316505031041080344a03103160004107001e1101d5441e0169111042c560a60b9624628141540b03025030310326035100320100042c1c41381c0c0b1400345070303900510030540c50300340d60091450030480044c0070f0300070141004180a0140c842c098090b038071650000000c01e03a0364070381c449607140001c480c4215a1810651541800301c0318041d41d070421718050905000900e03540c64900380e09a80056500505c0d11200304000c1022400c404c000c3d0440c2c03101900c2c045a40380a900e40036007950a0304103011616040010b08600c10342e0907204094010500b920380020501c0e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 707793812 1250 707792562 707792609
    0x211005180a02030402131d060c0c0601060c212c01020309040c030b0a0f0518100603020a020c030a061d07261903200c1003020f090619030501 62
    0x900091400c1ea00031020a0031541e80920300a41e2509014040008002c269840c403008080c051442d400d6000b481e01080b80864800101e90910102c00700401059182920494000b0f200c00303410f480300311115841140328805252000d6408a95964427841400d818044000e001d0480111110340002a00004101c3c4d0300801900c2c0d450901702c80c0040c07440c1d420030302580078000c0344400c142d00a000384800303d203c0500035400c406880d4203886e803502044207800c08043c0b41200b655141e4201c501b6a00c01c001c01e9200740c0003000d51030300b1841600e081a81d8100403170300d4640c00700340448007aa111036084401d04210001f2021252080f001400c140d0b01d000384503c0c0480014944480741c14030300b1402075000c0d0040103001c8030344202168000d01d9512500b80101765442522016031880d081c40034454030044001948544020b00510a04405030034210030340003544400880c2000210038010110940da482c400f0348901c091301e05811400807100d250040840340160024000c408401038650b0b040074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 707795062 1250 707793812 707793859
    0x111003140705090109050406080102032d0c1c020a02010f0e010207080906180a080307051b030d112a1813110307180e0105060108010803071502211005 66
    0x4541c01c109a03034911083c012959198250456504203060001c0043c00030815030041d071043c518000c03403280381c09030807240c800c01c01c82c40100f0090310018040405d0121040d0001041140c040d4180c0d800c00700001c0551000340d8003c1800400035035915400700d012030615010752580044903400840c50302e5001d90712310800d409030300040f901550000c620745280d84150703464041c1c0301c44018a50218581e4429405941358411002124540108040c88640c2420325840c3c0743c0c820401005446003c482c1c1c0702c11070f212020a141083ca9100301e0720007051410000c44a034010214040403041040d08031024802413074003101303000d500d4600380c20400803488844069107842d02d900041c1003e01c104038a000901e8025940c00201714030101c0c0c0f0400c0003802da02c0c1e100c0c0c0307a4061400000d100a940c2c01c0010745d41000d0905c16540130760010882080081c480049608a0703980511005003020010341c600507141c084e286000c802e07804080180080c06a003072410790000c2c1012603211450310101c0c2110300060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 707796312 1250 707795062 707795071
    0xa0203130b152809022208070929060c2a011e080121080307050403050d03090302030a180308030403030e160506070204053d061701060c050a050a11100314 68
    0x50fa0224a080300700d801d49415420341c4802d4142030a5280d100c04107c3d0700d4100e144188051a40b6040c0b052080c0d41201d8041800c404035500b604910120f0b5006001455020603120706c19802410b0b002c4400b91020152410112516141c000401207070340b002401c0c980402900c0b4012540301005003d025034401503041c1901c030b0064101c2002191011100018500c5860045c80b1040202c00c000c200c0303500030064401c6900900845c0c1c50941c40100c03d41c0ac40c0c0706000c001d00140c00401840b01242d0207003015201080b03200013000e101c0d40c1e8a44031040680c01c107407022800641c80d81107140401204000958054000310507032a4450b28250020380680b2403030740c0003801191154001160200c9041c000c040c4403c141030301444036211141c4c1c04011300d51802650b000300460180c003141d8148180c00c004101d00403542800ca0a03406c102050760f91489480d07040f21103120344216000052400e004840c0c00d00e10800018032505a07007010072100100321888034040600c0c10707910481c4500002c101e01d401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 707797562 1250 707796312 707796329
    0x23130c1106071115220312020c0606040f05060a09110c0f030a03050f0702070e04030306120c030308090a0c1406090310060f1203020d030b12010c1d06070203060a0203130b1528 77
    0x4605c6160588500c00701022060740f00c0d2010824103030078100880d109105030002ca5041103100840200786046550139200e554101140349000d00251109903c50820000c40340c001e14104980071001500d4401900c0c402c0c58190004618900c02c585c05004190704007080c044000d9242c5040d580096440f0724605c511700c0607150210105042c0b42c0a5030044015062038034080700e4050640c00c18285c803000e01d01c406c0b400035a1100001f40030350030200d00901c12a5200c2045140c0c10325006142000c020000003241d4011000c016942c480c0c3e40802101c5244010403501003203651600610a019244a50001c102030302086201da0010360f010501070703102d003000e04000800c040c1d840003141310303411030b1402c0d58010362900341e00e54030954101c80700382d1103d02da45000140c0216510b043c028070740101e19000703400d175200c0c0c030100348860210b4015580c8061074894825580748a40c803801038168003941c0038001c03801c0c0c400354100c1e98185001010b030f40c003400b4610140e145031140301070b1480e90018031400e9003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 707798812 1250 707797562 707797621
    0x919020a0309060903080915010f05010e0406150c0b0109090f08160b01091a030703030f081b03270c01120e0c03030f030123130c1106071115 62
    0x210280694004403030b0541100080014030280d18000e0301c005030030744600d0800d1081644c04458402030301c081074180c9a403024141045440d20005403407910300c0d1b450003540b05440d1100850200101c80c15520700181c960b03540c0d00120350340c1c148042d0403903060700a031036458105004074020400c2c10054009042c0e00c80a031a513600030384d442008107500710792401042d000418000180145403034002070328085400c00399034068600e0004150b80e03040c080c030006000c05c0d9039600303c0c0100c0303000c1d407091540401a000b486240000800d09444c1907072007110710320f04c08810500101091601560080d00c141000001851140c0c95600080c102a5500740e1500f08182c51300089280f0140038401400280c1c40034007100d0325001e0855548046410034014a12205916010201d074050820303c16429140050223041c1b001500410b62005400209801410300070100c0400c00400b10401006105440e1569090041c6c1c424003540f50030801c1000390084042107007024400184842d682059212034050740104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 707800062 1250 707798812 707798827
    0xc0c060706021b030307090f1d0712060807030c0504020a09090e03040e040501091703010b030f0a0912020604150608120a17040b060108010f082a060c031305091902 72
    0x18060f2103407845600c030100300010740560006001029500900701d640368108a07903100c2c0d1814012400510802840450b0305c54000048000320400d15000803c1d0300d0f148010038403440002060b0b03480c580c400c025503405950700300144075050a048000d4001104c0c1580361030081d490003440d16030030340207c2c0c0d40e4940d1407440c007a130300800b04125002440e040c2c00e0b8036034510703241c10405d0090440240a070b0b2180c3c0e42000120201007003070102d90503941c1c0b00f4181e0303046898066034075084010042c20642d4003a07885241e4008603012100e01c8654008503402401c440c0360038988030220000b5403a4954103181808000d000240003c144030fa001d1429244860301e840c00d4010031181609600241411080f180c4103200511030105a01d41c400c800a1700e803a03003140d0b83c5101248020056200e15100da40100481e002c2152804407a0b040303d540c0c5d000000c0c8424034900014606074441046a030a603840041e105202ca021102d03000b0003420201c54204280c549034940c03c0b42070645002c2000c0340c070341c00034850 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 707801312 1250 707800062 707800073
    0xf010b030613240e010e0f0402010f03050615280806030d0804020a0b0f070302070e0f01060315180c110a020d0b041a100e24060d060e0a05010f0b0c0c0607 68
    0x111a03070b00b0f0808a0001c036a50394004040824003070050050880e8580e000407040e00440000c2c5019540c10b0352078844417081c18a04800401001d4203142d8040360000210343c10324004409440c1c031090078a0540031040382400c418030700c066490414802e204543e070420140360340c0462148003140803420800d01c0c6651f40d100080348071105800540c91147c010400801c40c40030360f00078004a034817903002c440104d40c46401e40e22103940b0440782604000e0300e490041c480b103440303500090042e02503000e4aa1b500c0e44c58004030120118a4500b0034030342583e407440d03411425030154030106522642c5000e8000100150045000c580f0880700240102039054045030411440d800006400078041559423114100340740b50440f0710b10988101d141d100300800104c1c504600c4174800101201240c20320f68035107803401040c00180d030002d034109500e0560f6240002105803101080c00c0c495a0140c50000f201c1d8101000b038461400c0c19040709408880c18480341c40043c00004484030041c00c112410350311142c8901d0300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 707802562 1250 707801312 707801351
    0xb07050705070504020706021e07081b010b2115100312020f0f030d0c210c050f12090d02120d1d0a0c24080606030603070f08060f010b030613 62
    0x121341c00c64400503c00703082c415030b036010f40000403c042800d5051a4091003c88030b40c0240344000d810103004001d480304242408401000c1044040c002103801540c01300000c4444c2081321102035040100c0c4518240260144401c0c2c544c55425005c1400314145406c0d03015031141a4040201141d0390700300d102c0e45d5613008124641441400c0c00888071504000f100e031544940220b5a10240682040150300c2e07106e02840c540204003090600740400b081e201300750000030f4625414045c06021041041407518100d800c001c1c09501080f1089070000e08140034031604c0c2c41e140016801c1190864182d20204d000b03844205c809401403860003051060300c6004214188040025028440c49013081d00420001c4891980781200c40648004141c95507601c1028042950b81c610900040c101c0c6001032030501c1c15001564214801600315403c45440d4060740c500704015810a02075503000c0410030000003024140303c0d000d4800f00d808281181010804101d0600c8600200900c99843e00384a801c0304100b884c4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 707803812 1250 707802562 707802569
    0x902030f03070602071101050403020112092a030b0a020a0c030c150e06071202130501050708190203030109052211180c070606080d050901080907091b0f09030b0705070507 75
    0x281c0741d503104076182000c02075012960403601d540201580c14038641c0108240c2c0e003165010307160304a10503440d00c2e03210005e20f49040100c1d42076940d8131181c400d174403000704a003c2c0c80d0150400d150f042030444c00c0070310314020010664100540100102450203070b00000380c1158691504000009080e585010200c18401c0c0741641070451070030400340c02091001503a5070090320951281070300200c07548003400c181e00c81c002c224085500301c40b50400c030552107600200039060203101079500300b1625003030243c6151001201c140059002000600a05c2c155124542e004100111604104024101510600c07202040081d240d0a6800d20184240e04c50345080c1c0d041406450200c001032800018802c400d40010360161100f03842c104000c121030b68001220204070a0f02e46030a0708084a40004413540c0400400050f085d00a02e035002481c2c0c801c070b005449107c10414000301c540c03158494010322030400300700a0410461410010400b2905145d84a41c00c01c0d503514107669180c0b0141442d07858406180d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 707805062 1250 707803812 707803843
    0xe0714120a0b0f240108010b220e040c1e050d2102010c1413050405040c1e0315050709090b0d020306011707080f060c070303060801090b0a0c090315090203 68
    0x500308441001001c0c20b040c400c089140c286152031030030a0220b4500b644c003219481c0030031710800042c05011629030140c401213061132880c2c640c214180075245810100b030350003070b07140f6201081840100020406c0410227801d25007005150303150003000311a01010300344282c901a14902c5100c00900000c10301e044000710260384591080303020040c0090081911094040c0040ca0b00b0300c04200034212a4200d46441808010151031141848104002414042c00441e4100d00d50380c2d0000382d0042040c0300b10550307521482008400780c41d500b41b400c105640199030300c56903440d0508222500e41c0081e029004e580e0039a40014040d88448003046e40041d00380c00103541441040300000c1d0b0780140000a5a110a811054402107075031802c0c1960741c3c1d200f210700201190070982c00100040d840001038407807035000e4174021445940e0750102e5400c41d00b00240175108445840e00b0031540c58007500884008075614a4895002851a1224000e032200c1c10301c82000b090f240c2c411602956401c03c1000f009c5000030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 707806312 1250 707805062 707805083
    0x60a021b060f130509090d0507061815020c01060b190819021305101704030e0a091b0207060e0102070911070c06020303091b0136080705040e0714120a 66
    0x210f070f034042040d4a214032441403103540300145148201250480c0e842c2207903140d080c2001201d03551000900300301200401000c80d0100c140e800706580009101c248480c40a00698032080890900d003901c08541200c8400b09003004100d45424042d04000c822800c28542000f06890301ca034450658204a601e18001c14000300d40c1c4e00c03201840003609000c40b80219810945040c0c540404e807118054150040d03452900790340000c0100e40120300820040d64002d00c141451030301c0340407036400c640303413500c480c0b541c0418001c0036065907030100302c808017808182c10803a200c036045100003540d9240b1070041450090b16030b49109a1010460103070394600707620003109501607446280c0256a50411148050b143c0300311000002e441c400d900600505840696442c0045003030666142040d15805001c40e0707144c80380c140c03200044680c507100f00c0e002e01740135409024000c1c641401c21040e11048120412580c104071020000005c04680c410b4030104180d51400200d5808412031303080c0380c01020045c14072040c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 707807562 1250 707806312 707806327
    0xb1308030a02221e05040e0304030b0403020c09010e061c0b06130b030f01020703080a06050f040b03210301060f02010615140d0f1b03091109150d080301080705060a021b060f 76
    0x24800181e0000106920020146584500308000c1d51f220702800000764108102c24030101304020511940903000c0d0040703034508084480450b01482c2d09a10000d4001040418800b02c0e180c002500d240f00007e11103400b40c0400652559540b400c405006240b044082001d46111000d41350002040c548000b07040e20b103040c070440c0503c1d000c1d5000c61030440c00622180001100514144a00e109a440282800d610040030005000c024144401013650621590040c060346840c1322003d180003000f1252031640302c1d45054805028411004240000d6904000041c400200388031181d80303d00e00285000b054080c6074460100301c6105410807266440d040c4484285e076015141c114640e81a400c0744480003071460400300b14211078016400504580015110340c51621784007541c1a000321004031984003605401c9d000546032050494200d54165003c40100103045040c0103000007400c051380c007281fa00541640c025200d58205814000d94140c915000c2480e807a601700781c48400c4403c0c40740c41d40d00d604 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 707808812 1250 707807562 707807579
    0x3102c0907090b0604030302060c07020a0503010f060306050901090f0230010204060906030501030f02010c05030903031204151407050f190c050601081906180803040b01030b1308030a0222 82
    0x250007411201c1e4104601c229883c04d00c1e2046400b202c0e0558051324007a155007107003490607804810b040c0e900110042c0c002c102e50ba000c0c4108448503200100c0000c0700741c6940b4114050781d100801640841c0d140c1a10400071464107003140e1041941112041943e40e000d264002c4085094050ba13200c5070548040d109018005500801c241c0d4a079444440301ca91703540c8011001d42c0c10901000b807480c1c42045400d8019405401954202e034480c5081c2e80c1001c1c1003001107455a00b000200105900a074002d1105200101c0c000d070808501000c030900c00c014243c400d0519684001e00341074100030001440d131444060240a031303000c500302200100ea14100000c001044038070b9541003a10580603410001030007140000c0c80c843c02200e403694802092205807254002003110035045103400c02844644800212408010340c4254030580c1c82c3d030340300c0d41141805941100018400c00024039075100000104010794180c0303500c01c140200c0540c6da04505010740d10706218801815101810320780c00420381c1c28 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 707810062 1250 707808812 707808823
    0x50405221512051603030906200607030903120b06091002280b1806070f09031a18120910020f0d020609190f060908070803040b041703102c09 62
    0x6009400325507685883c40c2ca07a0244d080d052100030013254180e00d007048582c1c021140418801d807844040e6003c143d1003c031140c10401e045400380000f99907075514208240d0850224034000c00070304c004110282e00e500101e1203510840c24031900c070303006ca904400459403003001100240114902c0c022000304100000803191910503030b044070006007442c00503080041d0301e1201300e840040b0700d0042c00a070304c51500c1585c0080b021000c007010031048140200101f80b0000316040e0403103c8422481c02444d0080e00c00326602036100e03508850780c104c05c0c070031300103032001e20103484414070200c0d5241a040c0b172229060345080c02c08000d6180c80c3c00340000181c4407a8010901c0c521a01014064500700c41c0c010807210b01400d07a988000300180b04408003403021800642c001e0750f069200c0c111062418905442d242e540703410031901103d0364400001048100404510010568480403103101d0442c2810300031500c24100a00800003620042d000703100350701c03003010007030f02110409292003d007908004e040540c0341c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 707811312 1250 707810062 707810099
    0x1611010e040207030807120e06130203010c05030411221a03010c020d080c0304050328121802130605060d090b06060c070303030b03070f0909020f010504052215 70
    0x990300302094411414540216421994190ba5019081e92292010f540d20000035403a5200a0366484640003c040c0801c0020b0140c070f5141c0c0c0105007400a44109070a45440749042010000c081c0305000001d20a24800250000100ea82518a08138030502040d041e0b4032201c0f5448080c00c003100c0c030220740700c07410711041d0019050300207100102c541c0006030781e10031801c00700500040c00d6000158001c003042004d1760300144600203580c9041d00e034918407801080d0a1072460518074040588008540c1c20104c214042180ca20b418001c408000c8680004610206070180c050f5188806051500c00389031301840240074020041525501040840c800600c0760305000c075803441081c4c010640c5442c09405403014102840010809a4119a421000341402c107035825014818010040303140c1e52001035500140100c1e020010b00034465004000c400318117410307031a052000421040c0030645595507220401c10b005140c0280c4007030701400d000020002c40584071210607a940b4040f41e00040b820038146c44 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 707812562 1250 707811312 707811317
    0x23011e0b0d0f1a1f020c01140c0f1507171512010614150c0303070f020109020a060c03030513110d08070b091e0c030a0314070c06030f060f08061506161101 68
    0x7040100030450b0b070011340e041c1414000da0321502014845610034802d690682c80341900c00e60030b190202d001140b030f2482e004ac4258154100494601040d071b40d507100780354880001c0c03800060302c15480f4165901310b00060500e8020302d880740309140003521500500701d22140d200000b045a1540c80f00280d01d043d91100720144248210440107003d440100203607501a8860009186151242c1c00185c50407540c0c0e000070001c2d9500c59102e48096600c0345010f00090507152100c0c09007222601d00101141c0b8010120600d2901e00040c5202007084e51070300c281250015038001c1c4c0807442c0c41c10221364901846000600c0d01c4c0c1030808200500d000031031544080c5000100e40e00d001d80d040c1040e030340c6071910307142c07920303050b82c000f20a03000400e00c500f4408500110f00d200e11440c3c032170b25894031441c40405400100210713891355050a95002c80c5d1054800030f00c440201190f2503400c0c24955520741c500602000c0e07480e004510020b42079a00da20865a90107010203441444401d0707803914000c0d807900d9070a000d01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 707813812 1250 707812562 707812579
    0x1020c010f0e1b0a0b03090a0b130b010302010f092301170f0a0504080702030102070501050907060509031506030705060d0501050a1202100f021023011e0b0d0f1a 71
    0x880c1ea40c078060003000852070005450300e83c0303d40400008503424034040079030050b100c410004a500b003410066009078007800251441c0b00c09420018021000540182061100311000c540454013103421035054960900c0d0400400846000032070752080d1b02e8001d07100000c1d003491481c00300320a15400c44952002a200c10605407080c464035503a107107080341c14182e10709003000020040c11003540322540c0244500c40c400e00b44850386e00801c0c220303040000308403044e87d035803400d006106074200326050003003065140407482c280501c00440c3d1a40d54042503000303c40da000c030100355a03035828807415028010190416480b0a541094003020b0102841880d024210130714012800a4211108003103540c2c025101303e2000c43c0020049614210480f100421409041d0b5a004003020b140a004981d6080c206414001400806800380b0b50348181d0081c01c1d080c50954101c8004001102c110003101c03810500d003030700c0700c00403400c010203040599141c0300035601c4c0c02120400c481d07807001c1f5003420f10001da96084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 707815062 1250 707813812 707813831
    0x201020307200a0b040302071707051203030c0a050c0312010e100504110d0f06030807030f030c080c0f1309050c04090b0f0d031103090910210c050d02010e040207060507140a200f070801020c01 84
    0x41d03c5ced00c01540c00d00d00d03180e0100807440920703014100419070491807900300da00d401146405e40082d004281c1040d0780c8403d1070307020705c4a104003441060001d044220303810000140301c030034000940c3c0309034106028219103c84148620310000d612582c001d6400c0502960b552007e03140041084034130010501c00309140c180104081880394140f80d200e807141848051500786184103010242c0c0090984502d070080801c40452102c40f20702800740602500e000543c0c80b5410005d100094408514456010f4500004151101d5403000600c4407550703054107103070068011000c3c078641140f1032440d40f03c0e00403103e14240045107085c03400d0201103e0450310704c204209564461555210083c1202a101803a8000240f2540c6020070842c0c44041c4141002c1155090513008a0180d81000781c00307131126503403070041180041c0c128096482003060f0417201072a004181c000a80004032841000840700c14524034560520307800c1041d060441e69103c104d0704420703a2103480314082e5008007502e0180f035080c080d403003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 707816312 1250 707815062 707815099
    0x2040603142e110d09080a03060b0909011a1216030c020607140c0a060f0b09060105040b0a0518131d0109030509040b031c0201020307200a0b04030207170705 69
    0x400312050781e08420041c448000b01074401401c402441003803150410089424024900d105000c440e901c2a0310b2581c4909918001904070f41c1c0a034801c21171004100401070860761082d550505403039000180020105070200502600d00801d1054a8403508810030320000e00100c00543e228080d040e9030910074071100c1343c0e00702d0b101d000940c1c0c2c0340089401c00360082c0711144904050321080038050111080c100c00d6480c0d45040d200300c0c3d98000101e960300d404440302d0b810009a2568400402c0c00c04c246424604041000325110b1200f54008004011071880e0620001c0264903d40388001015210030864640c8040000c1c4450050321082180000303480100e072406028191590350591500c500b0f00c3c00e1542404017515031108025418080e20840b4010141840c41c900020540c40d4001a1030b4030306040701402c0d5550702e09030740c01e0729507400105601c07030341001038141c44840c0e00204090203a12940b40692510105403c24103030f924000c030031000b510b00300007201c900b02e903000c5030415100d03074030000d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 707817562 1250 707816312 707816353
    0x6050406050402190e12070b0d0b0405060105070605090a020d2102011b180b0310140103090c140f06161e020306041b0b0a080a0f1a0d06090204060314 66
    0x741c0c2220b10072504e8070f40340d0340200001c015180e40507100001640303225029134280301c201e4100d00002d40010035880d1000c8120321031900c41e51020f680801240c01c00d0340001c2c1c043c2c00340c7c0d1801011541c44234000b82014205103c1c1514160317000c1c0003035101d20224645851510b900365152074403a24200141c4c01402d00c14000c0303101c024081303c0748030500c1c805500200c0d94bd0322040c004880896003480009505140140114841c0f0000b1046030105410400c6d560000c89058490030704050400f10141c0104840d1081c80d000c4481c5840b4203e02900600046042c8134032a00c0a194410000b044044120790309102e8060050310641c042d0741d40b4000420003401c200c1c0090b034060740542c000350000c3c0c005070345e030305048410120900400c00641d0780d0300c446000c40d50200107110001110308c014080c13801154015040707011140703030060000d0038241c207040c2da04040c03568006114039100100c400501850b684005400e42c1c024105201d0b264890610700319100141041007485d114a01e2441141481040b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 707818812 1250 707817562 707817577
    0x11120403111e13090206070f0209090d170a0b0a0e0115030e0304030323040609060809010903021b041d160807030b0f0601053907061b0309150306050406050402 70
    0x8100c102c56500078000d60250f000d594026640c0e030340c00c007400584d03580f0003d0030a140c410300d0303c98100c40b62441804012000036040300b006500142800301d8558001404e201007501500b00b40301c140d81c034401c2407400b41441c040c6854129411071404904440134246c0c40d4181c4085403403e12600450b0742c012401c96495205100843e0028002840001d00c10713150b526680940024819a50780016520801c5034000e0307206001281d03824004028030f0b0342000c02950701c40c0c501c0000304801d035126100a91144441003080081400408081416949662101090f489000b5100300d4203200469041d035100300094840708448070700100041d000030000ba0b21300031b60390700c113901c0001511100c12046030541d01900150511101b03102c0d400344c0580c15481214039095503c00c010319402500c1c01032f02144280d1402c051545c020400900c000703600314083c5080404104a080003241090408403240f8410340c10846413504000c00000c03010740e05420480a0303071004c4030b0404c030096480c0104001c0740302e4a403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 707820062 1250 707818812 707818849
    0xc031107080906030a0b22050c21061f030605030709022b06090504051b013906050c0a090902070201081321030e0c03060f0402101112040311 62
    0x1004041c0d0b0f0038008050354004c91111808101c50600c0c0000810700070303080c00c0e02c601f00320701010a01291055801204d40052844d0205803421600c0c0b00f40412010310040130f0014800e281000c182c80340c5441c07620b811501d4164080d4174030b1819030390008025141c140b00b060f100b0302c1a0340010801005a10032030380781100c04406250b1801164a4011020b403007089204621941d40b01c00042c1507800f401041c0c42a80300758040c1008410a68049100c7c03100d85192604009a602ea0000c0303440d40d00000346007806c10042d400e03001c0b030101c0702c0851801441d400c00816890400040c0490b00305040082c0602c030744240c94038100310381c880086c04102d01030108047e000507407000215030703801d80c0c0030301301d0030002d0064214001d00079842900c0c8000c114800359000010380d440c0031005030040306204051100004070f01400301814104015100044003400c041d00c159202d40c1c0c1034000c03600030074200ba044001342c0150b40c0300c2181080980e04541240c881642e0032030301d8405030203444c5880c2891480c45410381e07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 707821312 1250 707820062 707820067
    0x20313020102010614061c06050307060509011b170f070507090c12020a02060705070203160b091c021f02160b0301060801090c09060f090306110d111602011817010c03110708 76
    0x290301f86807080d10450300c0840d400d0340c0c0b00401720709a02d00b8040c42c40a03001c00c1d16800c0da2404408001003560740050f041c00c0b00c1c0604010540001000c0142d514648106003c0b0241c481d80e442c0e0706492244542d0744010840c1c400e0344400156040981c118200c46c40940c1c40301c1c2b0080c0030741c0e5081c01c140c1c402d110003807005030411030005142c107002d40080d00005001804580307000c0003026a080305c0c003106400c040e001c8800480c080c3c8452a20040302e0840340604401c4060403c55580812143c00310300b0650311100c0701249540130329603c2040210074001040b06c0d51346d07056994002c007525552080c095180001c413400d001040140c8280541003100c2e50b2a95125005072400504451116071004444100060800000003084c3c0d41d00030030f5101c2e002481c0391a91750405190150856003030b407841d185101020b0080040c0312480300e800c07104003a02800d00b00840020710b101700501c3d100c10340000140c40c845600c142c140da441503011032f001c5082074400300031080100034000180c0c02008001080d40303004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 707822562 1250 707821312 707821327
    0x6110d050a14161e052505060d141003020604031713031109070306120f05031908090c15040e0408120f0405010b1c030c060f0c11010c09030c0e04050f0102031302010201061406 77
    0x4a86c0008080485407072001050322240007a1550380720700c9101881d1500c40540e80520b985042c800303a0011140d40d418104d8a16640c04290180034034407000d0840c02c46e24a24403058928602111a5160010b50300100b481d240d02e09120140001005240540000c400154655000e4810541650400c124401200b0016540d11685080c0c04c03a04a900780020b102c460380b00301407400480c0c04e001352500ca1159610b0328944244c03030000b4011445124007064523100e45040d2815003101c0954a02000c0303c00340b41d560f82082c040c40e00c640741d541c0c1601c0107403508025010420703001e9140204e12031000bc4c0030040e00201001170341c458400e100003007008086403540c00240500e4070200614030484000c5009514100e01c002107465030540e0364040f903803802e03422044400a100e1185204900d06140c0030190641c3c0702c40c00201030b00e000e15060841a040030a05214003004029006c1c4018402503549281c0b0a10b80326400385015422070141d0b00305900420b181c80d507440008080c60000d000309090421 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 707823812 1250 707822562 707822593
    0x30b06040909030c0501020406020705030f0105010f0e04050109050303011409090114060d031b11011e02120d021201030c15050405060f13030b010905010e0106110d050a14161e05 78
    0x200020210280a1310b000d1220014200b070006d44002d10701c0d5009060064580814141807407001d01501400c0c1e49040014008014101000c030141e51500b408088140e481d0714009004011180d40035085110200001a5513800d207041c075030f14202c1c00d0300c0700b03c42920344102142c00d0f02c007000045940c00c00f81100040701420003201541c0b01e1402460150f184250705854070f5040640d1480c01d8801c85081003100f44036507002000825480b0000347d0680748030046000094275090488014140310b040003032002004800c903016180480748007481a070042d40d59213030840a0b02c00030700c10ba01c013590500305520201c0740110155002c0301e401a10444c80d01c5204d50201e1280c0c0c2c0320075003040426071080f0000c40420850790009003c1c190020340022030794100845201144d005038011005c00000000c030050025011540440c07901290400716100c6107010010f6a81c6030380c07044c180d8044000481d00090f0348813845903000c0d2081c001c038cc140c00032501400c28610107418038040903100781c1c0441918803040c5e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 707825062 1250 707823812 707823821
    0x2150a27080703080603070f060c03111c091d01031b0f0b2d271e090a090f0803072c0901050a15050f2a0d030b060409 52
    0x2610111810300e4030300c090081085545101206503110080801c4007420160429030032900f0100071030003080007614014180540030f40f54010901004118240e040070103000300d402100603844442a80c203030803500e03440c2c00001c480c00d403030035000220001c000003001900c1c1401d80104420b6600580e210ba07003144c446407600c040e003540c1441e0f03003e640c500c0010903500c8501402c0c050310a028215130349011882607881282140c505008107807940e0426003484405200c1210b440150550010032045d01122500c0c607801040d1040c00e400041c45505149480103c00590401020460300e110190704d940b80744004546070010000c114080c64942000800d11903000f46078004840d192540c848080c4c0d0194003408107040032404032015401c00303516030714908076010502522007a0340070b1041c81e10780381f0010000c404a400c20821f102e000949680c03110b42c00c4c42192540c0980e50900032f50341c00c201e425030380c842002c1065480700e0300602040e41003681c42401151841c400041c04079040c00c1c10b00d44280000d1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 707826312 1250 707825062 707825081
    0x50f070b0f06040614042004080a03080609160f030906150e09030c0604020d050705031204050f040b100e2e120b0607020402090105120408030613020f0403060c0513080303070f02150a 80
    0x380d03158287c4038091001000a85194406002c0000c102c0c036021740700b04406070200e48600c00c140104030f900f4070344000380700e0846914501040400d1030313824103030000d0520b000094141d84c03c000c0d02c01e048810325100d003021620740c80590071440c0c3d01c07204200c0c0c036401040e07132002ea03680001020401503c0e0072140b08810782e0003402070341e40c15580c50001a251603c02a40f9000308800031804006520b484005080c4094090303405101d1010a0b00029001d800b408009400f40a004200425035844400c100b000c444d543e00341c1425001c00c0c00048020f009002c130b05031000100c1c10b0f142d1044956a03809409000180a400e89051522507420003019400142031103040080030b0055031101d00704504d0050140d800340084995a0030060b092000828080c1e00c144081801080f444a0300b00c0a035040300d00b00ea8210000080a062202003210b50b4865044d005200c80c84106012403207120100c015400303003a441d164940e03130345103908007a42c940a048110f415100b08c2d4200107048040c070794101c3d1410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 707827562 1250 707826312 707826341
    0x11010c05070f0801330504200409020d060f0803030c0706141501020d05040b03010905070c140601060201062412020f0c0a0501060e040b16050f070b0f0604061404 71
    0x8030303070b100d080d09070380c0450b107a02c80c0000740e4481d100d80d4100003000d03910f110300c0081c0b5584040e0f141040095403241040f03901c201806150f848051010252035189010f900503101220196a40e5984500f10040c0d0840d006406000d441c0241c0044d0b4488600b614208990701d5201440c00c590b501c4103200e806400225041e01d126849001c1d510240c0b6028012902c40c15020b500300303202c0c203440c0303000904d824800703500c440c28460100030600040340710506880c110780b03400201140e02d41e00c0403c11100c2c941c4425000b4880721101e00c1c400c28074400401d806068400d0340e1700030016541d50381190150391801707001078000d920710324105a100074851500d10355003500550700586014040c00007440540d0144400142d9a00110f15120821100303020b940300401204522441c0f50034562a0502900c0000d825601700c090080c88104440c2d000d10252014080d0303200e4525120302e268200320007840c0302181c0803030a84400c000041c869181034803c850036100102103400b81c0f82d118009000040c054148400407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 707828812 1250 707827562 707827573
    0x30c080409050705070302010e0304260c04050103200d02150a030e0f0304030605010801020c070b07030c0209040f020f0102010c0e041104030c0617070f0c030503060d05070609050f090411010c05 85
    0x81c03030301d280d00480b4000c00e003d9603000d5450a0360f090090840340c15000c1a0751640041100f0041c00320781050b00e00c0030000c21803143d10050300404440e480c0900d500450b941203801c00c2d0000040c030003d8869603030601d0204038028011050b05003003041003c00107400a6101c0f5041078000e0304c030409440600b1180b030310741c1800501e107000301507a140340001031000c000150740005014800c001c034a0040e103004000ba00000c1d400c180380c80801c0303500c403003a80c012404552008551001814482d00d40d600070142c014000303a0107414641031a461103c1d48000c1680500020003105245520501c5000b100d0b0302c2550740c120001c8610401c0202034503112403441042031081c003010002c140310344040001411152610015002c21204611a1110040a190601203100302102d035094011403200b20942e4580340c010741c2ea070380303000000f106003541c0d8601404e00d10443c40b020882d1030700801201d0603030b2000c40301280d10030030000803ca000341c0c0c00c407001080c1c7c181d1000e0340312155000c0c83c02e1400a030311403420b0351f6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 707830062 1250 707828812 707828819
    0x12072303120928020f04020a050f0d0903090803090d060b010e060c0c030105011703030106081008030c0c1306180509030712030501060f05030f0f0601030f09030c0b060319030c0804 79
    0x2101060039241c01d0700c0d0742c100e40b00f05120407074440502c40015007419801c880200098001071000302e031001215010b42c0c2c00081e4443d04501c10320440780d100094208954895050800101c0100072400080307002c100781401c00f040401c4008241d03246003030300902400d64510a9907a22024080c9d100c18541404418015080c003592280c0180202068860003818500c0c811810103007900d006030300c68010302c280310340c041c050f0b4800801104e040d1501c504141c5030b15120700649040814440e80010150b000c003090701d055843d404604490166400c4030740200c0500603070070703c0d4200c1c1c000f4803031183d8940d0400c07980407003111241c20007540028410f055906098040e1202140307925668120340000f584c56005204d11900b200c20f0906083d0702e490500c3c11464108100381d020302000d0322000900d0365220008025030b1203a0456040000111401d10003c0300518001c4d001c1501d1034000c4070b802500c840020007600b070014072107408420a075140c204502d50b685081d01c5440b02d9440070f4440040401022 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 707831312 1250 707830062 707830087
    0x20714130b01020f010f0b0f1c0618120c06110c0309040906063b220c05102d08190e0d05090f031606050c0124050312072303 55
    0x46c01144001c0390003142034082d605c20002c0d0810011001c500c29211030348000d10070440c83d440b55070000ea02410000301c41303170306449805040d144403900800b0150460f10419480f90b000815500c0030f07101d043e06106240f100044107240340561806100250310a2280e45e2042c541500000e12041c0206000288a03840e40c07001c40d03c20000f541740c11103070b0b8592000c3c544000880c00c3c205a0f00e052411b4910400d0401004040452040f1003155085911200c0d01c2d5052003411541c460040c02d000300900702c41150200c000d0301c190450b000070a440c418181d2070750140b58180c4600402509a5501e0144544e9405d100e099803102030000f8041050755421100004202007105113000c0701d01d5210a910b030b15001c42004040041120103a000380c0040034002206101c0c0e0480380c0c190f0301e070341c10015100d0009500d06401031481e140b0030310700101c0c0d90b03004100c102034001450060381d00550a03511009440307050f880c003502c00c07103000520203d0541408a111081004502104800c41050780d01c0c000f0b0324043c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 707832562 1250 707831312 707831321
    0x40b0c25080901021902060403120e030109030f17090a060e0316050102030604050c070213050a020706090609020306060d080301051c200111010603020d060b030724020714130b01020f01 81
    0x1c860aa0000490a0166804120540d41c00d9140c42c54000402a1540881c5807070140d803100030032110040040d50401401345544218602020b402084107958900b0020580c1d020102c400022171102440346803468280401e561050601000810b603140c02546d0b007000503d89800c9290042c001030103040f030428444014480b481d40504005a240e040c84000c05c004c07100041c2c441c000d2410300f00b00e01c00058440003682f1068480c1c402002405079100d10b0b07050082c0c842c2450041081d86401064002c020480d48805a454002d8044408a0355504184031500c40d0411010742898014801080103142c0017030300c000038140c1480c5a03130021203595507461007039100c584180090744000350103942c20b5074401540000940c0076802813190b17070720710f0f000f04019803880e401c040d02094a845401a454904004620003000a170941040314012146c45040d0f505000c1030820046c06030720701c0011a442007284428041034024600c0340842099a40c910040002c410f0190542c040c6070701151072070000303106 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 707833812 1250 707832562 707832637
    0x5120c0909011103161206140d0c050411190c0507140d0c0602030a0e0a21060603020d0503031803130b0a020f0613060e060709120c030c14040b09040b0c 67
    0x5ca055803404038500192240d01552003600300329141010030030a0000041c9541541c42d001e0310340566100c0d43d07050030b1052201a40095801a04003001c005040c101d44000707000231501c0725078481205001c00c1080b0340006481034003034016802818240003002400c0314241c41c541004001c90304680e00c542d10505075010b01da01102c0035800104035803d00030341041007061015001c07201e4032000da0400c0c65001c400d07036814540d2010004001084010003c5907440007001d0b40d0003c201c00301806091515650b00d6000701d0311442907011840501c002050000f0940301c0e0000111101e000ba80e003086030440351500608200e07800c41c414038408100f041c100740101c60040c103210403090b014281c1b5041200a4131450003d01540340c1c8010200881c0550000c400303401e0350a0312012007042003ea081c01058a001900f0244c00a0b66075600090200b6108030700707008813081903034103101e220506010031800442c100c0d030161990490200203038444092400800c1c4e031070100e0398a514a1800040d040094600014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 707835062 1250 707833812 707833831
    0x51008040605060f0307170f01020d0506101425060f0b0a060c1e0302070b030114040513030f08060a0305010629270a030b0f0a0605120c0909011103 65
    0x82840107202142c040d807540000d094500c220700f4480e00010030341e6180f2903c030711001c00c01140e4600c40843c006101c032103600002c1d50000d544a403110100c20008080666425102d9226104d02d60000ca000321101d42105070550300c01d500b406105800f16500420f150301180e100007040c840000041d500c2d00c601e01e214a02410001a6408050b0034054040f000c1d40201061043c51f902540c0003c0030b060340b40200708484a0b4540d6012064901a81382c0300c1c843e005400705000100020034641c801419105998600300c80602658446040405100f4008200a800207070742d120740d141298050710120741c11150262004190560b40c2e21010700710f80c0705400121101103400c014002c01403250080700c0d00300c4005136149241008180f6003039a84121361a80c0300c00c1c5444031a81c241c0c196218003d10300215001045100340b898070071040c564905007103c0350300d5128602440810345003844680c00e24640740031001002420980001c01115250050840c0d05079900d03007040030625403003000030b075000701c0601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 707836312 1250 707835062 707835077
    0x14040b1207090e0c030a020f030a1703090c010507050d030b060d0c0509030c0306070f12090602042d1a09060403022220090d052b0809060c071401060510 67
    0x3800030019611584104105540013546202240e5808075490301003540c100d0380c2042d400c6500000c24180002c208001d0141c09580103032407408074403031004520484e0f02e44207884074040700c0d0005442c0c0e405800f0000e4083c0d0304c007009010700c445c000d0b8410316401400602e11801c0801a04808082ea00542080307400201c1c04212034070f15050401c5417050b800b408401904507840d200200402d800b4010040c40108081041d0b0004034035030560150002c01e411079402d5607180c3e12829011440d180c8414000d064103608445401c00b051518070340c2042d41c4c0c3c5840c03000d00b40080503a0000351600000e00701907004104010010041c2e4500d2500b044516041d00e100c42c0320440c0043d801c0494201e04554120240c01098983e0080e402008880b50307100116071000760090641817141c900220200e40048203500042c015001c0d010620307244442c8042a0f5404a003603aa103440e1944852042e01c091302c04040a0216000158034004440c130f140c49804000145203a0341c00c00201c24588803040c4c000801e070381 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 707837562 1250 707836312 707836319
    0xd0204050301140105060f0714060106080106080603072313090515011401020607031a19150e090a0902030a0b07120e010e0606190b030c18150414040b1207 68
    0xa0141095001c3c10841e103a4440d03142c007001c16984d00c54501d50a02024000800c40c041041c0329401003006090030046481ca90b13107072000070340100828010074011030030f03070000910b01d8500043d0380b8041c0c480f0400341103c1c039640c4070040b011a0001600d4240c0c001815912205034508038030504000358041d400810300070309003810164440c02d040c0c2152803580390001d80c048240c4d0300069240d4100107240b90004503c0c0d41602110035405003500020340c44100300105a07102c0c03d082e0840c0d401d80705805102040035036200415148091440100307904400d92000040710420305511050310b841c00602510251002c0340d9440d8170420080f50329601203206545100503046c4248501044103102a0003001000d800322042583d40500510140c85201d000296100382545951031100402d2000405910b90824030043d001d642c01070a080110000c044800c0005403404544071a02410201900361500e03080c000880301c1c0056580490380c000ba1601c072000c44903100d40d03514141d202404005440c01a04 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 707838812 1250 707837562 707837569
    0x40603050c03100501110c0415051c031409040b040e06060f06070c050907051c020c100c0e19080a0b040b13080a1103131e0602060c1803120c0a050f160306020d0906020d020405 77
    0x3140f401201e14205210342f0700000c5d00210002c0d100c1104110103074407032000400240140c00a4641982c0080c01c000b182c031394540300000e0142c00341008031a8480c0030096134080c020039004088000d000841d03100b03c2005039042020480c0d42018951801d103140c1460760010401e603002042c43c82ca101303a800038800d04121002d005030140303104040c0c018441c80090a0340240b881c9030b003150581c420903211019400c0d00307814200c0c690082c200c10301900e04001490402c50130381a0103c5040d99a54094000110516101c261410714140d2110a4504090688908450010500d107050314a0b2008000401e00080c0c0a00c10f180280300000988041c1056041c00b101e9451035544490300303540c041f8051000360b00e040303401c1d00c50017004c0c11540745036245603000082c948011100001e240003400648070400d004082003400c82c1c0b42c0140112540f8501501100d56200c51961924518560040d814000140701d0b0700140303520000c40002044412154440030200c2c1d12242ca65211075500180c20002d904 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 707840062 1250 707838812 707838829
    0xc030c03030f090f0e151f03050604020a051b03042103110106060203041208120a0b090709080a1e1203050106140f090105030c040b0f040603050c03100501110c041505 73
    0x80780c500901001c0c64400b00b8442160280105c40420014400060118180c800501c181100c01000740e2400040300800c079045039240308600000a041070300040326400d0074000c8500d407100a0352403900c0d261280e00d00c0408400094003024040c082080005048007000a6052500356440d030340901c12011894041c00151401e003000c0a26410220200b040c1030700071003a2401c480303441c841144102e804e46004541486904400040215960140040c0340c0899100010400003511141083e40b00c0c02c000fa942c0c0c0c1201e1081e030320070b80d1103100100000303024404030100300c0720798111000340045955161600c07904803084110020b540c6c0c00c010050141d000640d151551540c1000529154582881803181c0c07042210701c50500c80000041003142145404640c02010a07030101c81d184c0340d01241d4105190f21920843c2c1c002070034880840c10030a8010101d034012952068403002e0180b50500548400c4283c40b6003403014041c2c0352220000b6110f40c003403030303e0703954401850100301c5007480704121411 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 707841312 1250 707840062 707840087
    0x20301081b010e030604080d110f03151f03020f0412030e04060f0b640e040c02010e010e01140106020d09140a120b071d060f030408070c030c0303 64
    0x200800f0100d200d2901c2c04070340c1540050b00001e00715600d1070190b500d00080c044004648007030180c0001d200d01c2c0c040c4504003441c001d951040092100301d84100c2003000c420340d9040004020202e2040201503140607600504112511078009070809607690207120044038640010740c0072a44101c01d131000761800348900307000740511049098045040c0110084517018860405018058202c04e0080ba60340d222001a00d00040d101c0f03200c1900041d17801c0804d2100e04005140e01c1381c1c003000c03041d01c603007d45094150680e07660b40d03150203001d0710301030400014102c0f603244002555680c020b022000c031403e000d0082d100303000c8000030402c51503544480f042910142d000b81d0464002c000e14002071070303002551038210b0341c000480c1d403441c525990000b100d10701c0b01c2e40200c02c44079034041d540b402c003c0544407003440782401d901e031a081c0000d009400490440183c4031307190b2085040000c2000500440084c40d042800b0380f02c440e007050207540d0342000c0c01010741c105680b12101c1d540208101039104003100c102 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 707842562 1250 707841312 707841317
    0x140a02100b040614010e0d0203010c05190503310204060611060a1404080a183203030406030f0b09010b09030d03110a08060d0f0803060a0f080c0d020a0801020301081b01 74
    0x8500c1c103213842a20102c9078401c0b904008460241c101035581c2c00c030024024980040003041802240c840c05809a0b00000810040c1a8048600c220b103034004d4068034410701140115403201c0c176614407101e03243e050303681071a030740e143c0200074040241c0c44900c00c0c02d0142c00c6644600d803094a01186503032400c5001001004072604142a440d00f502c1c0c0d14400340d801c10b9001c81029140c0002110945960ba0302c001000c5409e4002c24000425070208441c0051241a03001117a81c91110f8440204149107072003a015015801000100640b41c482c1e0310105894080d2440010700d0004a8001003001c4420fa000f540c031150302090b0b104042c9024401c000868030a404c0812030140f14401a0341180202c40d2444140700000001480d180c9039180c0d2030700403550100d410b0791b4401403890051001e0b00280c4940d0301840c110880442d07648042045d10003507403982e00040808015640402a00c0d4002440881c1c110280080020f40c641007400138602800c4024041c20300b02c00c15014601c5203040020b4403e04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 707843812 1250 707842562 707842571
    0x906060109050d0f0b31034109060403200907090e07050705030703080a0e0c150a03240509060108220305130f0f050a0303080705030601140a02100b04 66
    0x542c11300b0f0b1040d050b9520110380103031541c0e94841820341d000102c020540c42c80140d2440c15100006100241216100b6103908d06030303580c20003003141d407039940604080781c10103040343d0304898454038034071a401d01d00d5100030300d49410001c8021a0b0075812a07401180d044d007290954040404551039800c1c5030b51030661308902e00b49400500105039040d1841400c04075a80c1e2030100d89414452070844100b6078205044076640c00e0700b803034002c040b900d085407042a2285000401241d480000c203055902c20301c0184030b10a1f998038000b6000c4607600c895900310915560b014a0307041c3c500d07a902904404406201808040c1c0d10f020280040d01c03000400050411040000b00600020a80d500f070390405038001806081c07440b01d01d810346203481070002c43d05201d80d10101c00561980c1c101c00300415180a0001c0200071551001030103a01021804001c0110b603003040042c3d44280b18070081d543c80303041490b0103480300420010340710319544403491400041e0002c00346a01005c03018026001f5044040d2402c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 707845062 1250 707843812 707843839
    0x8010c0503131104060e01060c0c0e191d06130501060f0501050d200408030a0306080d022107020405010b03160e060a12020702031917070b010e0a0f05090606010905 72
    0x4514000c0c0074000f002980d1103a010f05443d1660b90080d000f0341b201070703514a480e503121440a404400c43c100c0843c1d0040c10188045010300110408900a611524241e2546a030012200c009050092204400711030f41c0e03003800d4000c42c030802c02240195411003000307010741307403a0501c0340c251055030300081c40a00b0503600c20802c03a60310104507149165000000949850300304078001c00404840b1080c204142c01060200310480702000803c207101c00d40e1010805240c0e6140c410f611040b40f80b030741001580100d05440c2084403807500585610300c161030748518001ca640d0005007103c80c00e0304007079078000c00441040300d19038181c10442c44c1081da60030130400c583c2c401c0000411034131403200c48a0810155070b0030f8a0400400d9010381d0451a4010300340c8902111410803a01e10202450081d0384c6119440c1000b1f1016004108568010360840c4810040743c1c03c00360f00714082180984003420660b540c0c110301d50010001e100b124001da6492001d40b21500344040018172038991500528414080080b121 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 707846312 1250 707845062 707845081
    0x207020a0f1404020a030f0903121512060b03030409050403020d0e030a050a030e040902120102090102010b01110607050a0c1202011e0c05040e0901020c0a0309030b0112030e0d021908060108010c0503 87
    0x142c1032000440c0d0140c2d44018150703080b0007a20040460004550818035040c0c10150465248110411001e10401503004000e890a20400091040c1d80035090143c0e81880440c0c000d801400103520003400f01c7c0d01d859610007200e0100c1c2d0341120141c0068121418940751294068107106440004900410305044a51909611999840002000d004440380c4040c039503183d640000013542d030000d0644d05428402c030900c0d4043d5000d880380b01c0c01540b07002d100411560103500240300d221221402040a036481e040252a517030720022951050014221000d13001400c50300808501074207660005c00c800440001341c45000f2000045104400e050046100d0321950000c281d908980030b80d0b00b04612526101281c1e0300910036102c0d031001c1c50007000c080c0d03810b25400c91098000c13a84150f01201242e0f98911918044403058100200010712094800f280ae280205405105500013010242c064540c500940384495881c3d20a9010303400c100d004110640c0c080c440e030a100301c12420440d2552a00d40381d603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 707847562 1250 707846312 707846339
    0x7110c0103140601080402030c1c05010605030601081e0a062a052508040e01061e050f0d020919090b131802060f0d140412020d0219170a030207020a0f 66
    0x243d810042c80c20001800d6503001c1080e0508004040c100d401c050440da0515074403404107400a80f01c030744c281a00000e05080000d541c504a8100c04041c000ba00a0b0400302d5900c41c02c2003000160920816201c0c90118600d48191451544084140448840c0c920020754998410521b25001d01200348002d480d05055a2281550b00c80c010303988086640075403404111500690704800c42c18280741002003662070308282c81101c07805017403010381001042244100c945204805c13600e140c01e282440880d41003046a00034084105000300404000e9605104103081c1800070b03481100c13007035200c0c0c1e06000e103810081d40302d03810b651215105018003480010035190402142c1e030000d00034400040c25070f0380803507130b00d05584444240c600d090080542c0c2c5000b00c00d14010a607800d035050f101040307000f0308a60000030800002155038000d03181112840c1e01d0041160304614054a500015440f69150101040024123170f10446490041e12446140148030810035103030030001080c0e104000c14011178050200 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 707848812 1250 707847562 707847571
    0x803090102221d2202180f0108070b04080318030f0a1b23060318100903110f0705060a170921071e06093203090105030a0903031407110c010314 63
    0x1040f0480c0b044ea10104918904001c0755a9140075003909000c8505041d0500da4100c611410071501c1050f1030701410310461249215a07000c582c0100712410a54038a4403218a02c40720040c140c44510301d1514509003007000140c1d0448050025000003042c181c0d040c0031450203004600040820082411000303c2d20b0b00071219024865000400010101c5000b0180000400303254001e941c0703a03a645183d00b00240180d0303081200402c465031071110011030000f0f4620403030303201d01340100460340c50b0005000c2c89601090260080000e5a50101407450013014401d000706010802031062104e1207004030f2900002c650098000743e800c00220001c1800c2c000c01e090104090b0b00c0c1f1400c40b0071649082d038014100d0071401804081150546210841403c0a40d0840865404290090719810381002e0300d0f0f00c280f0f42c5d460b010500c1807020030201c2407290301081c1d2803407090900081d0100c80c0c504204142d802104d442c80080e586000000150b8000d10444e04451004e08090184555905103010001c00060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 707850062 1250 707848812 707848861
    0xf090f05091b0f04210308040605061c0503031906060504091a04110903120c070605030604060308120a110a08060603061504140f0307120803090102221d 67
    0x400b0030805600c99041501154890082c1c076070307842c12030064a001c0d0700325204103d005019010f84201601801c00000303240e039032650710481150b4680da10780f40140005090f554010700550780c0d2035480382480410380c0c03000d0f014000031a220b29151401c80150306140c070f60850001d080c08002c1020680002c141c9055036030188010030f140440124951602e139105c4d5000307030f20500f01400b03030303c602c542c2c10000c1c0b0800d003003030b4140c5200084000680c1e200d823081060f0843d0381e5001e200704100007446480a5038210600420105034945d4903116440c20ba000051040004c810440502c141e05050b0310401d003400354000c480504101c1d1444010b00300361001010745008440000002d07002d5503030000c80d5100e00302c0c144540d03501c9988070301c03103d0b01c40d001e80400325004621350040c2d42000e1900240303c4085450203101901a00c00e00d544089240d00302a055040303640d000c0c00b0b104202c8852484280469100712200e416862030110004181e58400010494424518050100f46c55014030141c64146040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 707851312 1250 707850062 707850079
    0x60b0702061c0b04020a083304090f1208070219150b06090a06050901170603060403030e2815201303060203100e010803030c09101106160f090f05 64
    0xb0a00a0140400e42c81103580144005481c1240c075030812011030086041c2107500c041c5004e0741c00ea224903410004001d005450301142410303402e01e45900000b03101752003244440e0a926840d941c01c4188443c04074040003142030b180c204115190b04000b004103074041004d42200d0f810305a01c611000080304a080c0d07481300d8440b100e01900381c56103801c551894078082c0030b07e65625070b100e2005000350054554980060400c035140284007641803500741c040c180042c050704554445a0b0b040e40203101810802c9064020184100d0350548030412840c051800c0c000d81582c1e882d030500d080f01c20045100e034140c0e60707503103051501e50f0914002d001d0b244428400004896030780400c05a02e9041c41440c3e800109001c3c0000100304c1044c0040038003008451407040002d000b03980303035218030b902c03800304071441e80d600c02045c000000c651030310b070f0640c00c8850864203045d08640c41a00c0004d0400c10220f23600c8422880c101905a0440d9001aa940b07207480146000222242400c2500d03219491a205140c4100706a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 707852562 1250 707851312 707851357
    0x3010617150d0309150801080715090902280203030105040c0306120b1b18040b01090501021504060618020c3d1119090608010501081f0315020d060b070206 68
    0x80c19008021300001010600b80440c5d01000401c0c00609006201550285040008001440c40c0c45e0b954142d1aa489000e4614203000c0280700940001035994008584400c12801b005443c0d407004800d107015901959503581000c2c00c0c4002d44408010f00e4040505e00901080400010741c2d0556045a002c103101a00e07403942c040b00d8030005052440006000c0e03000075524401c0d5a2008012a00001560148001c02e001001036980901034440d007800f6801c404507003140f0300350405c6400e501c54401e0100085880c1c48000700a00e42c08000c000300b01103940040c1c5003840e03900400841d0108460015048480500b4042c0c410302220542c005400c1c1001d496011703041400035401c2460b074440000d98040d15003101241d1040c80c0c0b41c01805060100f00108000b00f021403051007614140d502c10303125810780c0e40345c00041c281b01d01c0141340162428018074001100245014480c80f03e40d102e51540903840d0740c9010301001c1102d00340c0e0300101010b801004030800580380c203003e41d544552101e07003042100e6034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 707853812 1250 707852562 707852567
    0x4032a3804050618120706021e0c27040c0513052401021929100b1c1103090d020106050d030309020d0c030f0c09020702011d0102120d0203010617150d03 67
    0x641180c1c0b40d51051003d089610000d20021b50070040342e5403a0308480b10740c280819030941c040903185034460305400c27003401c480403410428000b0020b039040441d00071601e450180080700040080d40d0071118030070446c00400403444d006803e469210135240c010003140c1069402000702100035405a4160305180390810b105a009200c18540f04545083d280401246490880f0b0b1207201407410344901c6000e0304c0108102000188082e124403d195070401340181800d0102280d50806a01c4240c1081000e444580441d45401140004122031200da80c0f203081596900e405c2082a80c44041160f240110401050b902c80d9010050759805060014042c88140041007a1211a03040503000706c0103001c0c000100000c00d1001c0c080d4030b0140c0702051040380c40d150700030b0076403180f00d10190020340c210340c1001d40344160005031007446070140102c80c06007015008042d256004401031109040c1e0210040107035541080395030200c820070b00703110700d03462130000d41c2210b41c030320480015070158162070f0803101010b0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 707855062 1250 707853812 707853847
    0x80c1311090a030b0a1103040f03140714011a0f010c0b041a040305070201090501090b090915040f0f0b0405010b07060f020405060304050a14030a0504032a38040506 72
    0x254050b01c40e5480e00e403039003000200d0010503502001418504441d500008410b10180c1c0d016941c03042000607810401e4a0898020203407035080041d10408000d01000184041d80e280000302005001042d1000340d290500500480c80040500030040f00e1072548040e81d0110b044003086038001d03047d1086e074840e8144000f91a002100d80c014a0508006000c1499009405004203510076610700454585860044032800207a00c2001c1e12504180250b200701c0c07038090129584800401c1d5440c0c103000368100041c013511601440e41d0700041d07540d00075940c003500c140140551058180c80910580d41b4203440e4a010b80701e0b0b4000074044c0b40e80c814541c0003117407442e0100c03801820000d006a4070703402c15081c19a240c0340c3c101c500701c800020a002c2c4250b1101c0c003109980214505840710345c1030900d5515030b074490b011980b805400806200c070031580b0250803500300001078102c207002001c00c6c05859021500c001800d61442038101250100f203020b01e03002400325800d5460541e00d86880d40c3c101c120621100d03 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 707856312 1250 707855062 707855077
    0x20d020c060103080301170a02010504050913061508070b0901050a05070303142d06012111160c06030b0604050d15060801020a020c12060105091f06080f01080c1311 72
    0x1030241d50000014082084003450503038100d0b03542035401c0c00889406135a610410007000740030a0381800100710314038140300340d00d600070188034900600000640d14542200c01200b14200e40540031a07040c40844410400f032805400c1d00c41790395150028010028205028031070600341000301c00504203040602c41c0d0080740c100c48080f0100d101c00c2c1040601a040d50441d001c00c4e680e010110140100b583c0701011405020300c90684502440c1c0c03011020004840941040c1031030311580310602d0440307d10760440100b0312035110006c031006c00c01d03451501b09400d64041d4004801c150400c0000c50701603031000102d404a400c00c441c8100b4514484c5028a2088203016100d80c0380383c03600500061983c0b040d0010700e88407a0303540c29a5900801d2000700915101b1900e5555161b40c0b1078030040c00582030050007a07412490ba0f400c505440f00703a42d00340180c0e2400c0d582101c1c2c00a014402030006181c15900094007400300c0318080c04040104401084686c0804c03100f15080755155503945230a941810b044030f10a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 707857562 1250 707856312 707856337
    0x503062808100504020103110703090605030a14010b0910020609060105060d0b10030e07090c0909050705040b0a0507020f06040e040b150a03060e1005131104110705012c030a03020d02 80
    0xc401c402c039180004100480e81031b8046801c0036094821084164101c0d03041683c940c0313800e040c036400c041003240c6a400c02000e90340743c40c1e51030718a000842190041c00e4001c0c8503442007942d56802002c140200c0110070b20300d0000795071105052000070500443c41905407101901c8154840001d100103d0140c52480301180c0c02c031030a070031f0140d0700c9980b54100c0c2d15640c0354801100d0311139695a040800b107da030209d400001464100d41400011354541047c0d070070020380d18110781410380b00d041119007540f001008901103480003c1703050841c100b174410207050410845165081514105400300c03008401000100504940070000d40455080262a0141100504145651030300c13445d0040007401c6000b180c0d041403080110440b20461103000d114400d08005100940d549900d0742c80d6074090140c508000da21644030f024400903c207405002d0103645006900124000203080514068441491a0014400f07030380300100381c41000000458404001c107207401070350f9032928501c210081c01003441c0d80b60b5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 707858812 1250 707857562 707857573
    0x6050c0705100e030d08061005070c2d08011a060901091802070c090b03030702090a02041206051504052e0305010c02031b0705090408070201110a0302100c0503062808 73
    0x6031a80081d0070180181c06404451420140c05c100b074a0140c0c0071031302954040404e5502c42c0003540718070040c3c000a40300f8180003c0f140c0e01c502c0c10b41081744134030003180348401e40da0803120031160a00ca1144010000310b1700800042000440041204100740c0d4903a006510026011400764418004280105600c4108584042c81c0d02040d9000e0340c000304054a44c00f400e0740d00498141d42038032519105004c020001d515000e0545e085c0a0790040042c4103840307141d400d000000354801c4a50f02002c40c103200d0780c4001200c1c94501c8080300240c40074501ca0380546e207000c0c01c01c000d4030602540300391380920498400c811001707180710b211806080b0f50001003595080004091711250000090070f500f6070b41c035420800d940c0303c4039412a501c414903c55264000c4108020601084104c801007103030a0061400070007421003a94110310307021420304200c005078000c031049403080307585202c1c10031703e110a0328002e8903506100001481561004640d034411a59811205a424000050b130f1b000030f01d0300d03a013070b5030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 707860062 1250 707858812 707858839
    0x509070507020324090c0102010b06031b25031214011a041220060307020a110d0f0c0f0914160c14061504091a22050c040612080406050c0705 62
    0xf04d182581c02000368840d80d00d00409a41c0103002d08000014050f20f464119550603000c0d0366490089080306414140400c107080015401507000c00100c080692905070010061500604070380083c1d40005030245000c04004614140d0002c042c1120701d0158148081c12841402e0f207124450395001010102c000200031040002d280010f4013101e1a055215a003140000c06000b59440101e41d95130040e084030f15070800140d20241984244100981001c808194a030344191910740ba04000b55568240928200420f80b003014842025080c200828403408401003104224204041c0802e00045c20048411140c24450900e4002c0d440d0480314098101d6040c5101545542040e100500c100306072207203c04440c140350041c1001c240d448a24206071090740402404030303510150050a41d6044001454101c11101000703d820134002e002030150808030344108022a01d1a0b40040c1420310107100b00300c00b00c0c0c00711090320200c85ea541052543c5091250b043c0342000200d81155512500806452 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 707861312 1250 707860062 707860123
    0x50316111b031207021c031e050c0c0415060507080f040e09010c05160605090a051f050610080c0f0405030106030c050405092b0519050304020312030105090705070203 73
    0x90704544030a030b0580d070b454201e40021244a104900d0082d42000784040801a8440503002d8044d5035400707498007007002e0303404d440a44905e08211a59100103100030a6502b600c44090180c14881e88080f1020008000b44e170400400c080710920500c2c0c10b001c03012409a080c030007807500311381031002501d85503139031641c507000c148000a405583c0244130358038000c0d0404015004104030303000624004001c003540352040e610480a0b080040c40303504580074034803071000000c00402030b040c0d0101c503580e00503981455403451441203a4008200038841e443c000b181086a44d08085000c0c5c000c4803900c1d942d40c2e11490410010010b1069a0181d905580703021400010700c4821040c00c01511021a0107011a032503008400d590364000d1401e403041c0001c05658005103640c1c440e03240548000038103090341007203081c0150b2003880c0318041091011440010402c02186070038095210242001e070351030341c01c5506000c04030300903001c01481c60090010001d00001907650411414a0280c0740001000101030840b018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 707862562 1250 707861312 707861353
    0x4110f04030f030906082a091009090b011e030b0a0b0d0506090703090b061c020307080616050a020304090507050c010c09030c08030405060d1d160e010e060105031611 73
    0x10360006800540100d1034500c20511a03005a103120382d10750110b51000d0785001c80030814240d0346c00002c7c0800541181ea210f648501c0041d0026403104154180ba00c02410b00b03592141036078a0400c2404424104040d0312500100f461032141c2c40c3c001040c0d8a008041104140d1603000712096240c08074060002d0f280743c0c1c000c2c61041c101a100c80342e958941c04011380690b400c00c130700203066400307500028503a070900b1440d036003400f0490444884441441e80101c2d007130400ca0740200742103400c5001000b00100f641102c0c8081d89881e4030781240703003940002000351280124011000d9040e240c601040380c140c840c4096031500143d13100200301642c0c8205000d050b854180c8000c071040700d0070340340004403320701006960440300d015220502d0042c580044d41c0042920703403803a101803c0300c00e56500303044004110301c1e0090800004806200d50074107a03035880c00c440503170058010400b51030401c0f0031a64400d003030b00d8101c80303854050801102d05240540d20382030b03031604a480340d100e512840720044028201 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 707863812 1250 707862562 707862593
    0xf0215070c02031c0e0418240608011b020f03030a050613050a1506020f1b04150602060a05060405040c0303112a011b020603010b070501090b070f120605090604110f0403 74
    0x9074200d0f645015014001540d514498401ca26400c68880b000402c0c0e1860310444000c0c4044003a1102031000040d000c11a149602b1600c2941e540b0302c40300141403005001101c002540d80000d120f1801441043c50f030324400100310169150b1511301041e10b40d03ea502c404007141c02004000c4c00a464001e40c08401807001e00840c031049804984005803160011840c1e414044030349010308110b020050605401514081185811545d220700450b44030f06031058120182080fa4042d00d882e0810b1f0740b0740001c2d81e6000e0402803140345000180f0000403010210720048a51505108000d210002d20082c02d100803600440354404039464080040c0400d0803481600c0c0d0b42c245c82d9030340038201c004644411429000f00c025080710007040180074000d4120050400c0c00c0c804c1001140310801641d5500c84100103484100200b0b146060380c13400d1540101d0884840440d80c501013100c0c4c1e18000000740500c00c00380010303004503031b00c03800d04039400d40070001c03150080c007202e400558032a968504042160f42241 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 707865062 1250 707863812 707863817
    0x10b07080708190e010f080a020a090b0711090f060d060c120c03050618090712170c010504060e060906010603020a120e06041b0f030312090f060b030105070f0215070c02031c 76
    0xba141d18646c0a01011407100003559682070346980c8014042c1c0c025400840355000344030682c403001400f02851001090001d100e40000310901c0300380005c2c05500800501a0a01ca035681003c00242d40c69030f0200c03600150f009940400c20000c40202510703040911aa074000a6041080c00c058854060300013a00854003a1420b200f104004924101c04400960324038100707400014080104090240d440c0d003a403030184001800145030500343c1900390384440081c0700c1d165100d10400c400e0001a2044181c8040041c002e4082898500401c03034441405001d502c05269000c00c5160802d4410385030251076041800d400c0082000b505145a6501d0707003185c0c112542d079407100e0040d4001e0002c001c582c040356954000549040e0465401341c891510b0b411980c1441c5984261440200d903040441c480311034024a8001900e10391841072500351000145180103020902c00c0b0020001c0c1e001804004540b0101400d90581d00e40300400c555050300024041d600d03108925580307454a4001050512580e100d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 707866312 1250 707865062 707865077
    0xb040609050601080f03071b0f0f1e0503060a0c1215080d050702151c05150f06030709050105070c05270a15030209180d0203040801050c04030209010b0708070819 71
    0x704d036845d660741088610310031a6042405003400240008641808804810b1881c50889031100c42031204401c0310742c0080800d40900e80c003009140c1c1c00301c054001c0c603003003018019001030600700800e0b40c460f8064500c01042e5522040101c001d07214419482c9003510580050180c41515031011501c09046e01400805010724402c02c60400d004d1030489078641d9018220311089180d0101004040e0400c00010320300c06800102500e0514803841341d02c1c400c1c1d055000e82c9012418241c1030040c00c0107251145070003200100140284241c02c20500f1080b50424070303000d40d444c0c0051170082c40ba0455a40302541007074118506441080801201103d606c401c1d01d00859280d81c0c240c0300c0010f0b102e100500700414204038a0600c054103258504c1030303115a00081e00814698040101440e003824002f0300700c010b801c0820280071801c1c080c06040d07088034000150505146c11600040c01508040c4519009504001240c404016401d03054440300c5400c100360342e80341c14920507041c5086102c54030030700001c2c0c0701 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 707867562 1250 707866312 707866319
    0x10e09040506010506070f0507170616050d0b060f03070c303501050a0801050f15011215050f010c03020a0624090c020106080d0e0904020109030b040609050601 70
    0x805260300c1560004001c01150340b0b001c090017929803102e1800c2d2510b030041503180001c5030080049070004c08260184c850040c80c00ca12190a1040180071034035600c5000c030420084682c0324050350840e40c000744001603843c00781000140b0a10a4681e06408090080100300340541c210b012040030038001e01c00c0c04005001000802c1c8079082c04200b40d5194154501480985403140c00050510340701e5462480031410110048103017811820080c910860740c0c0d10042c0700c54204450308000601c4500024000c81c02c0201c40d00c1c03c01c10000342103120904410f00381e40748682c45230f003112508071240c0108010000d03489424a44000d400e01480c0c0c041d5a12400c1a5482d520039804000304503090381c06070a00403907559903003002d00340301d24000918011019404107002403460b4076100070100c0800020702230100b1072010742540c0c02d0303600c60b41e0710fa0807090301400c0054000707a0746032110384200c541e181c2580c0d40d440183c03600740042d080075042c070303950a0410042101301d6000c2101c842c0039170112030740f0703aa030f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 707868812 1250 707867562 707867569
    0x105060616030302031b0304150b040605151e13050109060f170612030a0c2a030b040503040b0f09150405010905040f0b030f1e0a02090c030a060512010b010e 69
    0x4908a8544031400e0142034000b09119501854004c02c60b8018860103220003c120482e50308141c90a640048450900000d885107178410b815070390b28192400c2c0103181ca400c001a10016022100785c0b0182170002d144001a0b6108a280200c20420001c8a031950b01310b1328041403904081c0509800301e2100c0300e020031500c1c0260380c0d07100184a1695084002754220703c0100c0c4414029240300e40103408110b0080c40c01c0c5041c0301400c62645240c0d50242d0420320750500140f140d010301f03482e50032501c000d2800c1103000ca9003588030301520741001e0091610344030f0f880c14a01e11301c140d41c031821015030041160440400c5000060160410444945401d00308134402c21070240710321320070240401d80d04c01c410010340c24990010110310300c14131070009841d210500030034141a40d040b1503400c0d80e085510400240754280d0906a250035060004145112881e80031070401c2ca0090215145410080000b0307241a00c1600920050000640070082d01c2c51408403c601a14504071a14003242040380004620305 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 707870062 1250 707868812 707868817
    0x708090f0a0c0b0a03060803030a0f050f040201021504110319031d01080105040911032e05090615030a050a0c0f0509090705040e030706060b0d0f020909011a1e0a0201050606 76
    0x2a003140b4402452403900c2c080464550101c1101000e050321101e00140d903620a1000d0b6100d0203520001107000e200c607c690f103046983c01420340171458500d000340700140c0d0f4002941c003280d4828a8024405481e1424501c050059140003c0c1d03252054144424203100d50614003074002c0d20986810440940000c86003201c50f152188041c0003034400d40041101e403074a03800480740729025039403142d0491600b0010900340350030a1a0b81016212050704c4646c0961030204140c0c01c400506030400850901814454407000040c000307550400d50203c4000362a507080c0424158594404115840c541061034482200c0080f0311402210700360320070b00028641000202d140c420511003003e050f4640c10301c0d0402c030007030000078506c03ea039110074000980083c8040c070824018280102480d52141c060021000a4034540103401c540640140700401b2141c40d1280181c0c15504003012034001800c0b107550f444801e01a10040030b00c1044100d106500302c90049004200d00c0c5219402403000360b803120300307015151 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 707871312 1250 707870062 707870083
    0x160c0303031d06070f0e120102041202010e0a032619030504060b121002070c0b27040b0f040c031b050327030414040b040e011a011d01050c010b06030708090f 69
    0x61114082c1040240c414020981007082c001e2142c5107c9021a04982c03c81c0c00542000304514801500e8500350f6030004800b03250301c601124181081400c660316401c020750305841d01c0c240300d030740130100b50501542c2000399940c400c41c03040c40b00e620030ae031003100802619003130f2019500c0c103180c402000f803a41092010030000000c90001041201c103a00b50350b00095100890075605c6009600012500080e03a00c0107020b04042c3c6a04808002c00c40c03d040e1124113840500207100301d00d0003001d0065600c4c0d400302800001e108440008581800140c140d02421444103c0910114a5490f44448940003806075025501c2441603400692241650400800700e81349107640962007480100302c01e00e0703000000c1c0d40b00a4094004241c1c0d024140c042000d54143c103802404a0f5103034840850225420003500080d44000d00e441210410f680c8038001700d4003206100241040030004000280c00025040940b420030054281a603d1600f80300c0104848815038002406025240f8043c103461400039621840 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 707872562 1250 707871312 707871317
    0x213020a11030322060e0a050618010b1302090a0302090a0204091b0804080a090521010b0301270609020a090504030801060c081215041b09081b0105160c0303031d0607 73
    0x40356000c80e861104e2040350300b000c561183e01d0340d0070310890315414095407025510171001010f1724201605014024410300480da40700381c0c90861003d40c281e0381e01030402d031528100c040050740e520b151000704103082000d4101940091282e001d218402045600401c11034840c07000400000d100c1c035402d6250300c42080043c400042d40300c804900030403041e02c020035a07030101e4101902101d94900c04900310510300320301c000c00c42512010b4401c1200c400c0c001d034205500c3c101d00030040d240c00718401c0f070307102c3c040020942811039449040e0420800300e82e0015040d1034000300b00485555844030a10080c0404507400c40010b43d6840000a0090042d11501d0120340c0c080042820290031502c41c0e0035152000b050400c6003010b05000d0316207510755110300403020b00c00300d2100e0080300085d1005052078000703a0005115621050007955101d00e07848000c4c1c10200c00b4640596a14815040300c00b00c1c020245019009070010003001041640507444168451503903104038003040075100c903c42d103415084a28102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 707873812 1250 707872562 707872591
    0x1605030f040809060403060905010b0a1e0e19020c01020a02160e190906020a110106061103030a021b0708160501030e15060310090c14060c030f070f0213020a110303 72
    0x18002e0002c1d11100c20054920307410242e40e9154071054421aa0082e0f4883e50b480440888500f44454031002418034204c82084a100094210200c1d0b0b0080c4140b01e40c005030300c0042145090381d00c2c8504d889500c05a07013035441d40c104028440c001e42c0706200000152141d024134807a90105200200d0480e4030341080140d0aa8409000400480d40e100c500350545668511480c00146144081c10f80841c0741d948144403941e400500500312003a60300004140034001c0224121103000108880d4000c1e051800543c030340301e9a06408003070001b202e84009450262141c04100b07502d00081c036450b001c580c0e00703014414035504c40c019000c4442c0405001c00c5030708000c0c4140505042040150380140c809012200c128041800d000215669200c044507149500c00d02001001017030b060380030641c0c004450795407400c00a6a91580e5a2081c220203204071000400d042050111103030003402e5054001e0540682064114441402903004620b240b000c20015010015101c0c0004217072807041c442c0204408 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 707875062 1250 707873812 707873821
    0x10f0807121b03060218060f0f090301060305071706060a150e01270306050f090303180a0c03080429040b1606020c0c01080a0911091f0e1605030f 64
    0x240c40909400c090380c5445141d1058620001e16803102e100842c050100140c030341c1d51441d04a511620108506441078030103025050080e0402021681e203981c610300e50607039400c4c0d500d0200f0301501940e4000b030b2507405180c030002242070301320390031041c0100c1010a0750401d503221b40421440100d20700815014081e01c08007070200c036005d000415081c4030b0506150303c8414050f1025001c030840000d460650090f03c5008208005040c0103041d000102010020501d00d0424100c5a8900004003400c0f8041e6410425107074000d8184072549040e504004001d0004e42c680c1489030441c5c1c89849451407000c001d0a100039a181d041818404035110645200e207007034a0201011904e4200c1c403500440ca042110342040080c460b480203100b1507000710068030a0f030072000000b400302c83c3d00078103406899081030380e002e00040c42c007400e80d00ccd00300c0c00310760b1a0070540383d86d212072001c602d030f450240045500c1a100070070801584c1c114588680f500000184103c4030110045805000641c2d0101030102d0300c40205 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 707876312 1250 707875062 707875079
    0x50c07080a051c0f06120b0f06010c1401060e07180905060303043b0f16050c06090609060105010f12090f0c091a10020d110f0a03090905010f0807 64
    0x10418001c0d107140c11801c004188003000b0904080c03120320004581e64119090f5000650700900c130007040320301c0c01c00d222941d13951182c2c41340380001080480803000d403d000694030703800b5502646107190003a070341400107140c06400b035000740501c0c094640d21100600008124503c01c01449076840c04100360740c2241807511416402800e005040640d1500080c013000c1202541383d010340b00203e08101c60b04c0d00c2d9034646040c019a0000c0316801e4840f40031400100580400003491880e0841031151403540700c48002c4104903194002d02514180318001c03c01449000140020305c0c0b8020414402542e001c0c2c0da807000155901914454000c2c08146030002c3c2c0c0d00411050390103d602c550040c280c5210105442e80c0310300541d0781a4201c00e0000d580c0d0300490707807000070030fa80301c241d80c0609903400c1e0090250f09101940d0746410000002c07c000001c24024000401801425401302041040312041140d0f890058481074142c003403202032529040000a00b4407166034020215401100038201040c05c10011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 707877562 1250 707876312 707876317
    0x509061c03112b090302061806040e19051807030f020a0f0303080a05060109060e091306050c07060b0d020a0b0a02070803040b1b0d1d12010f0c0f03050c0708 69
    0x40e02480200802000310342e10600c030140c41485041ca031590300961400c05990280c151201003410002c200e4002c2c07005858010499000060750400021056002000540d851149401c0010784071412014003070042c1c860401110300390f144d240c0501850303452040c5030100c800342c80540c00c2e03942d1080e0720420200305596110302c00710340060324802c085521081959003110741c590049000920314400c020418216108441d0404000d1030041c90342440c00e41700804441202070114451041c0c2800700d01e07461005104081c0c95540000b090102d480c24010924254005030303030584138941040b502e1005c030300d00f680c03050b503040c1e074002c00802919080c0342d00d20035141c105068841c01e500c20302c14042580c100c200b020700b004204522900e41c1e03542c00d80019165040d40203d1301c0105034011940c0c00440d41d08184000b040c80034440741c503000c41e1034800000b5001c000e9410418119460501030000f520100d800c514180d86690715101c8900107607190450841d481110380300656003090041400180c0134100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 707878812 1250 707877562 707877619
    0x12092d01061502060105090906070c17090a030804180204030816021302130510050711060a020a1509060b09010608060f0f19030b090c0303040302191d01050a050906 72
    0x20354180caa104894095059040d110b0159010000412441c03410b0030001e83d0109140e005040c0d1070400c1c0e04090842e03004000002d001c41c034082c2070081c2100c0d405050b6040628024170384a60603a503420498003580c0a4040d503003443c040071078540c2d0303070203240d000303d5044070f80c01102c0c1807425070716505031401701000000c200d81c000c4101c040186601d60600140c00c645a140202e950b00525140803c01d001c441414002d082c00b80c207004250100b40786003003034454064184d40da5607a03480d0802049007002e141d040005e2240ca859410303c02c00e2480c903441607c0440c415001008001c02d000e042010300b1000340f10700c030001440702e000a0a03504000050303082210b0060b10341400002e6800018900c02d8442d104216040070540081080c0545c0c0e0030f185030403802c4407000e0003080300350340081b944038030440c0400707030003100d01031400f20514100b4803e0b20700801c00c00100c0d40c0c40c0c00070b141000c0705111081c8100351050702a201d012820380782001c03540d401100002c15410402c205d42c80c4c5400d08106132070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 707880062 1250 707878812 707878903
    0x5071211060708091f0f030c0f0f091a0d0b0414160c02093d0501080c07050d02070306062106050402030109020a3002220b030d03021209 60
    0x4059242a10380062114004c2a440040c01801c03c5105c401040700c0307151103200c170400d410496030300311803034106200484803000c5150908100000440940c2e002c615a4810b501111380c09207804101d2003140064089803080c4441440810089020803041ea0b03883d00c00f284c109104440410300950203034a81c080c51400760306002000c03c0b62500010303102c0c0c4088496400e60003800a800c0d4200013849026a040005d03a2003040d003505070220304003000142030054905004840002c52840e42c9900c0a8030f0009c3d600c00211201d00c244498029107400c5288011182d1a04052700070814031000d002d24600010500302202c00c0d060103860b02405014042c205a805558580941e400b60702c906203001c020b480e44030540088803011203580c4a41c0e100303103250941d06030050300150005940e640b02c01c402e481e03180c0816895410300e50084000401182c0e0031a54140320b003030044a485a015000b904901c0c80240d000030881d07a03841c00c0581c443c03c10f12a0403122040d8010700710502e10000e9034880f01c1c440c0c8071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 707881312 1250 707880062 707880067
    0x170a1e020a06052508071214031801110a2a050d03020904140a020301060908070e310b071e0c060c0905030111030103050f150720031605071211060708 66
    0x744c01801015800200c05d9544040000b40c1e0000d0040c594a4803241044030316000000d000c0c1c030340b4041501e000107060000795440b02244821000c0d8250010f0b88004601c18610307560b041d0809018042000d02c0b401f88480400c401d007004006d0132200161030507903401101928140502c080110003d40c03200440a510541d995040312130190b004080901c2294240c0c00141e595040000142c203128031540f0520455012807000c1c801401081d03140d0382c100819200d40c81707071540140014842c2d003044201908034501806001000d1016811200d40115083e40b98144e403c0d07103103100b5550407030b800c3c403800c80452700300114030000504039405803c51242a2508428440d00d4400007403e643d100807014070820804801401440000d00c42101d4094205c8000c19410500d40d000e01c10301c2d80700609000034803924a441d2003441219209011007001d0307001c107a079501c055800c0c01d0b18804803112001d6805128240012440400d190300901d070154004450382c1c1c0e404820410801148e026400840e0009003e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 707882562 1250 707881312 707881357
    0xd0f0f0504031a01090f020403030215041403030901060504180f0212030f16150b150903010216050a0c051e0d050f07060c05390307170a1e020a0605 65
    0x318102043c0e0055200401242d54900948101a10031803211480e0045c810482040001e40008440356155007800f444001c5176650300f0902c88180d55943ca01120f800008200214548194040710580c1d40031182081074819595580b1800000e003800144041c0502114a000d8904805c4100980c200381084130726041c24545203104070b030442a154451910340d0340d021810840c01758000448008528410403213440d600c00002d005138454517030030381c040c4800108081e190300d080d01115101105407000c1403011b041803806598a005065041c1e0341c030b002d9488040f0b9503203410009100900c2d00c40110381c1e101e9040c4401c212184180304021680e0780314017200300768100002d2240c01d00508180e1036500b01140341d41090b90524181101c0f044c00d00c0c44054403200c080200d00580b4800d407080c000c06c48092400c01e03000c2440c20000382c1010800c44401001c6d0f140508000a100755071510a420a100c07080000380760340741a0020550003540a00301110070310101d446030016240c501d0b4150740f01b00e0f980a1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 707883812 1250 707882562 707882573
    0x102004030c081b060a2106080a02010210020708031b040302030105010b070201180524070b070c1502040806070e13140a140f06040203041b182403080306010302120a060302030f0d0f0f050403 83
    0x3d00b64000c8c1d002e9000b1107154400e5603010b22000f0100184040190b25004103a50b6204284c40010240940c10712003010359940802d20b0b40c15100030710b0340900200a03550b104c454940c9641c018600407400106058041c20808070b14031051000c07124060b00c1031039214080805103410f0954440740d180600700030705c041d10101e0344c0007100c14007845203622000c51007596400c00412041810300c0710803949004000411511000242095128140e40340041180803408001070354040d01d8103040d00c220342880a4000c00310b24295103603000e0340742103404000c030908180340c200000c00110354960240f00b4a0000400505040c1c0080d98054420302140204001c005101a402455a0854a46600c80142ca4402e1040c1c0d407040071004840f03140701c8000c09609a10100c52130303080d40030081c00140041f0100340303680d0003901030340d50000d01c80560411910304060420004c1015200980c403a20540001c0581c051002c80c2c01c40542d00240d480c2055002100d0040e2691075010851104201041200101144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 707885062 1250 707883812 707883821
    0xa0c02041a150c0129010806121b011206030203070e10050306010803030402030c0a03021018050a0b09100f1e0c0b0a050a1b02102004030c081b060a21 66
    0x74011101d9503c803000c000300035007142c030300100112142c0a4010403503601582e107000502c03204404d2911841c540c1e1824041002c1c40c94130100403d143c4140e02c403a500c10492040c045030400000c0c0c0e569108800f60850000a40c0e881c1e00c00650103422031002407010402090082c0e41c0135007444800c8441d60f40c5d400100b403500100340d110141035000032043c4021840c0a100850030840116407509541e42590006450f40107040c2c0c4176030901034502c50b64120411900406030003402c000b840c20160541e0b801e11605282d105844681c4601c400b14041e0103047c0c060741000d4040107450350b030703100d41c7e580c8202c00d1041e005000c058442888405407903e4005070300010360f2072140ca90044080b0741420500700000951700501a83d15070b0443c2c1000d681e883d280c0c00266008031140301403001c9840f002001114080100251805186800016000c410b000c0c040803280c0440d0b4880f801c0b1101404045d07851003403440d912560580c010740410401102c14400c100a04446c81032602078480c010320501c90b4000c0780c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 707886312 1250 707885062 707885089
    0x5071d0a0b0c101802060d05090c04180b0f0c0f0a0504050d1a0f0f0a1808040b031e01120b150409290f160504092d020a0c02041a 57
    0x1d902c400012626000c103805200e0084402000718060000b10745d001a07031501030003d0641540f41d41d0b50004406480c100700c007062424001c0c00400111400d000040c003050848041520b6058290011401c444e059091043c07090240c0900301317043c00400600c0d590146c3c000d400300c0040210610005c1400e548101d03031099900d1081080f1441d40c0d020b0f41240c12180c034018101e00031107400300100842c40c0c04590b20741c0e5008409802c000f422030080705480d01920764603180a82140d1300868081a82c500340c200031b50103050382c0c0e48030f0341805c18585045512150300340503d0001004412460001a02021a60b03800c030011000c980e8510341c000d0b01007001c035035860740e05962003170b28001801c42c1c0396002e00480c6d00c1c001c440721441320b05190405011540310380c06006070a8054280700c94506440c482c000340c5000e0400a0014005141c120714414a0b1540300303020000000d4100d00d01d04055001c3e48200c5e0b05108241d19040d0144809400b0000103281540d0107030610303a48294bc51000e9500d840310800d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 707887562 1250 707886312 707886337
    0xf1908030f07120203090918031b0c0102160602030d05040303110325030204060e100306030b0c04090c050304020d11031c0201020319060b030411010509060a02010e06060405071d0a0b 80
    0x32541c0c0d6090401480125600c00e03c00e41d0010010941c050311048209584200d400084d0051094480c1d880c524601c00c13001c0150740c0c03160800901081400200c3c0104420380264210307942e000c00d01140d252111218401d100240e40100103540c3c0071910382d00300c160700c0342c00303802c000400c143d0f02c01d000b148561040710940a0708040b80c0e00e0306000d030085007501c81128240c0c541103003028101000a4501401aa002882021501c18040d0954440d030041006144e118881d07208508050141040c142c0080c0034032520281444000b5080510074419a4400ca8005055616032000c03511030000c425880840260117020301c40260551100315424903a008046a00042c0c0d64601020800c2d5010a100700154005040c27400401021661000b581c1d0046d401c10310019002d014540162910310582140c02c1e0401d0f8089400740d1200d8040d40710707403591000182507540907580d000410040320340450b066004240203000e6880710710201d840b030031a10302000e00508005902e5246c035204d1030b0881ca04203e00f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 707888812 1250 707887562 707887567
    0x50103080a0810260a0c0f0e0a0b0105070201030e120406180e100303052506062303071205070e0c1c02070c12110a0e090118020f1908030f 61
    0xc4103940030b0142540944615101000e00b410010007041114a000032008030211500802034940814008600500e60040e200403003035944074014106181c1c00d12801480701c0c041700003d09441c20078003c410001d10b0507959645810401d600550090080c0400040d981c8100c2c20b030003081ca4002d10083c0081c06864891101d0029030504584181c21242c00c807500c961842c42c107100140d03141d000d447d8190780d0b02d414003a45400c401003041c500c029160412a030703008078511002c82880300c81da00160a940e4401511940340b03000103600e0240b0b140c010320040d055807044070100429440998a555030900c0b86041e0752a2960b45c0b56200c0d6080e200340c9210006141c00103611003884030226a801e02d03c41601001d60600344e0a84585000d80c4180c8192800d61410001c01d4041204c8544114540d010003071464094a0f1980740600c0e15100480d40300d0019868070010700070030300c0f240d08010785640c0c1c02801e0035115900c3c8020b012240349203240095600000c0700002c64141400d002409040d09803003800c0342c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 707890062 1250 707888812 707888827
    0xf050708041505090d270315200a1413030606030b0618060405101e0602151003110f10020604170c06150105121501020c040903050d0b011e051c23061305010308 70
    0x1c00702c0e0000502e41401015003901c40d0727a182c40ca030301030794034038469824001560300130020b03103500b10b11031407505200241070b40d100403040082d01d600c0038040d68028037440b40103503a020140030200c1c031004406000c40c00c8010019809240641240350b2102c100410380302e9082d80c0d100d0080b00d69a681c1461010744030044014002c80750b0410100e40c00c090350010022850411510803002241c00e800040e0440003041400700072610384500c1c042043c04050030041d80701c1d0428000a44402042c0d800320707864000050509803103040c031002c2d2035804403044041c01654480702544100301080140c1941401424031402c500900c0c0c10341c0662095070402170012241181100081c10020000c00f0580704038074081082011036800740035100501046000081c020401e80300684403482c121401142c00c00c1c0c800c103e80740792a80f020150241d070135113400307900007400d101d180310703058451038408552810503882901440007402664150410070181114016145d0904000c01f0f0b100260000e8482d03880004e105c4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 707891312 1250 707890062 707890103
    0x1504111b010507090e040b04030c02060c1b1021181505070503040803071d060c03090405130503030408070c0f0e0f160801050d03030f050708041505090d2703 69
    0xc43e03002a90341341048010781001c802240c04100504054884c0c0b400c6000a420140100500f102c695001021617445980003606181d40c1c5000c0c04801c461207082140b01c1145080044011001400c04e031140d102ca030b241c100080c50710480c128118001240c4401c1003038030343c4032650600c0c51514015069010403c140c4000724064405c09050002040420020400411a92804d5a0700051245031400c81068480d80700c4601951016800741d00040003c4c00300c448900c00001491908015176003844140c1c0c502d14005c400b40c410038005031080d0030400001c0c2c000b071b19000c01000030a00c10702c0701600d8151200400100c0000741e4100c0c5001c42441024032a10820305403455520460000c0d9010095140c8080103043c604103224040c09401d208a21504040c002e800403540b0b2503d80c0c90402c054548048010311071001600e041e00d10080715131884440e40a28001c81d41f28021240081c00c1009810901300d4482e03290404e802071070b2b4001d190361001d40303401010150045010f04440c8000c41003600d1039 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 707892562 1250 707891312 707891321
    0x190605160302070b07060b091f0302040209010509040e061b120703020f0f0406030501031718060c010e012a0906050a0e04060305010f05151c080a031b09080d03141504111b01 76
    0x50203409c3c0498a03102c40c280b100e42d0b03041c505490707055a001d81c86540e20780042e941401640703980c42d0300605001c2c42260340314001501c540304003014207a69a110201c00014482032040c0e80445480785038420000322020f010f034004043c241e0381d19403601e140c02110b081140b00c580081d0450341c00203455000400501220b02c081740d0800c0602c3e034840745084d440c04103a3361544a04d0b9007041c0a41c00220740764107004020f5024014001d9214000e02100b05440f0f00548401c0214440c01e122848001140304e25510079080541500c1d015100e8526000c0c40d0030060300c0703044c0c506050f03d030b000c3d4035090040300050084c00382e40c0d1a1400068041100d051462281202c03600070348919004d40c034079404612440705000000e81443c0c0c0c00104003580c5044031302c0114041c241111341d11134407140c080040c40d102ca500c01940811203001e0000c0d01e2081c071030620110142c8904000401c409020000070500181e44610880c1000c00018000a0402910b000310f511680107088134006010340c14840c1e8401e08030038081c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 707893812 1250 707892562 707892571
    0xf0b01050f030d030b010909020403060b0a080102030603060f102303010501050f0d0809060d050708011805011410090f06090915060215090f1209190605160302070b07060b09 76
    0x101210722000600c0482c2c0d4518400c544102016120845001c040c1d000d410800043c1a045006566a07031b12424000040e001019403640102c94404d00002c400b02c0c1842668050400240504660740742c00321281003c01000c0c1408651a917600f100242c1c640c01ca2101c03030444e004400300790554490070410582100c3c01684213501600d00c04020f500995605006009480d81c4071441c0c0d900c40c1d00900c08115140699414513400301e1505003480b5840e40c0058000c0c3c1200d05e04e1440900c10070130000300500395602071140303084803c01c942d100c1020745448840ea0055188524081d19183d94807005404015120b500601c0070450f18130080c400ca1005c0d0141c2001802804442d030091b40c07a29030f000f0350b1010b115190b1900e1080c194045918407800b80070284031016400101d812504a00c00c14039815800401c20783d02c11503401d0900c8950b410780c41007110490301d003600d5041c18503100481041c080300741d5040882c11801a000081030340d00144000e0081c09000d5100041d11102040522181086c00360 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 707895062 1250 707893812 707893819
    0x130213122907030e12031801110f070506010f0509130f0507060905120f0316150905030a0908010c21090b0405102702130207061e05100501080a090309030b040f0b0105 73
    0x176204e254501203031040781e410810391440e64601d124068a583d00400140321900803002000800003110401703040940603460281064403800d0340c2e42c1041e0303c86107056104090704008000c0008000b020411201c89503c0d001d01c40c02c003820251030b40c41c130b0b08002c032941001001c142c215400740180e0500c1d040c160f1005081f000180300104145600681d01c0c0640060000302c80082d642810411080300d851000c01d413402442481165000e280082d00c1c2e4200c003456400090700864000340c040d10500072800c4210598407241c0b000502181650004542d820441c000280c865482c60b00090b000c0144522031400348018101c45881d00300824141c51003010868001341858101c0c0845c0350800c00d51520b06a81190354908048580d02c0c2c10f0064082d01d0005000c0c1d41c50120b60070001004250003599565004c681008035076600030100c400d0701914011140010860000601d0070200d951110f500d150203414081d0005980b46e507400661103045500f222881341c0b480e000380401c03610f441d140340545001c0f07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 707896312 1250 707895062 707895073
    0x2c0a031e080621030c010c03050c070b060f062205150403020a0b130f0602010902030f07060c021507120507050f1203040b100801051005130213122907030e 68
    0x200c10062034080081e00c8603200707080790742c0010341070351108450020311412101565107480c00483c45900030800034965601190034840080c00c00c0c40302d01c2c03ca600c0550b01c903038281c500d515800103201ca41e100d0a0074141e04590300700301c01c00d0340c81d03280b451082400054001c1c00b240b2074100410f01c8088a000710400d0300001047c08280010703503440701c401e000d643d0000c02c880c2e26025510540a0102c101e82d101c06681c071103511004c1201981074010204580c026030840e00c0f1810b03080802952081e2a02c00c507400a80c082d2800c60040c41d200e10612030b000c19404485050100644a2184103019601d8003008110001031080c20024280440c040318102c1c1409048210141c1072990020310000704020200c541000000b411b10b0071441028024000c604002c018528000140002d4558a030045a1044400e6007131424110f40900840340240c202c0409405014a4175100702c022080c4108121821101c1c07562410f141501101d1107015011070724001d0010781000407015046404000d943d12994026 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 707897562 1250 707896312 707896367
    0x7081c060816082401030210030b060a0c0201080f04050c0d020102030c060903120a05010506040b071b170f010e0d031512030504050406240807110a06020409050c0a020703062c0a03 79
    0x213103500703141100e4041c0c1d4080c0c003803160719908500030862402021fa0021000c1115040d01d071703200d100078644510030380399034a0360b03100e02c500524400c408440042407640001510011400c0491b08040041d01c1801201d040018040710a41400d1080718948010f90021411750303642e560400581e5004841c51104108070350400001c519a440745020721404094005030709410000c8413a0a20300b8450540c05100500e5290400f6244580070100120581d200d14039004501709810300c294030a42c51003c004090813114060140c0140c80f12480c1c507000070011060000d400082480000d05030351080c2d440c69599030a0604000031039156070005440c00950000d200c001125200c0240394100c0c1908145445544000084501440d40748600d8500d00401c00b01000300011600540180ca600b500240320700d83d9a115150201e0065440c0c00c40103a00000c0100082000c0f03500a202d010b01a1031f90040901c8904c6a40500102081c3e622110354171000c0c180341410340c092601d0400210b808800e102036140b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 707898812 1250 707897562 707897623
    0x30f30220b070f0b072606030f070e0f1f0e160309050a2612061c020a0611010b1c030305070503010605180a0503060f160507081c06081608 61
    0x41260014130701241000800d503801d00030014941d0b820140c1c83c004515a4807030301740d007450003000d81e001ca000f4407901c0d01c0b03103464031008a0601c1c2582d030341c100340d58402d81c0c8603904c00d49401d1014100800c88200944d10203591210510450068040b860040305607050480181d501c05040c0200c40302058a07040042d00040c0c4046441c02819400004030b104403041481c08400800600b5200807040100081c01d01940d20342c2c0c08114030845003112401d6a034151554614010110900003d52040c0c015005104040c001d045900c3e04081c004000208081c001020442d00c0b151030380c20601c10890029124100b40d854042c80340c2c491654508681154034049000c2c2160003401c040e0300c000c55140106c40c1e400d481d0000801e00800008003250701c00d081501d00718615140995042a029005003890039616016004903507041e0344c420002c61134043c8111860740710044003a2150742c015168540080c821000700728464070007035042d40e480166440c00e0803440c5003441405607040c06d0411007809212421 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 707900062 1250 707898812 707898833
    0xc06050a0f050c1203150405091c050d0e01060315050703061401030b190b0c15040b040f05011401032001031e05090a060e0d0e030f30220b07 62
    0xa50501980314654800000d0a0544c120220784081c00d0100410040d00f641d602070000907201610104a181c40c1d14010b02c4d1100202420607000181d0f00020111030740c843c0b030003400e41c0c9010312000100a02540e00c0700342560200d6005844a051255141c200034496204d41a0882441c1c00c04014051070565001e10310004c01c2c1000b8145582d607404042c0070740340d082c000f00e881d002002180014944980724540d00780c00c048485030452181100300c2c00120035505265000f10341128001d07095507115902e030b00c0f80e0055190300b22041d5403190b02403501035400e500318902861054a4503401c0c1e5081c03e0503003401a61a0601307504060400c11600f41c0b03141d40040c50091640d41c003101150380e95451003014903214801000420451034260b03400403001c00410702180104440c1d0f1441c05a410f0041010f503229514044103495070406070716084100d01d1500d00410705040001030f076482071810031039140c10703810917441c0941c40f020749a1110642301c0c044507450081c116030203105013001d01c2505d80c4103984 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 707901312 1250 707900062 707900087
    0x905061206210c0f0108060d02150c070f26151b071101111b12030405130e010c030209061801020f16091404032102090a060309060605040e0c21010501120c06050a 71
    0x139203003001b000c01c100381d585c0c0485802f50310341c3c011030b524696900b42d140210040e0340f2514414a056020242000200084c15105500d10b280102104055038840c000c0c0c0340000b4041d0070404036031070340d06203c01c0c0f042009091388134051992481040c24500000d024401d4000c0c5990303143e00010b2512a450f045080c065030b10a5040e89e11603910a100000c05286205039003105900101c0143c03081c0300c1600d503420172560507803608001c2c4581c681448068059014000e145680f0080500400d11416000d991103158600144110707840c01c22402c154608044c03081011000581340b0450502240c08170703009a14112500f180006070500e41501c0041881080103404011580802c450182140e00f503015a10b1b070003801403018100d10754450003d4010500120101c941900700b44000450380b0f024881d1017074200a11000d400a807211004100c600a51201080c044140344004041d9100c1c00b481450301034200240c480c00303d48420b00f00042141d28650000741004070420814940030342c8041301c507281 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 707902562 1250 707901312 707901319
    0x7090e0d08090708120319090506011e0f060c02010c0204060923090c060d1e0e0c01021b0d06020409020f0c070803030405100e1009080315010905061206210c0f0108060d02 75
    0x3030b034036420011514031f41205c1d90260068188025107040c8000803400c54108e40f00c1189458150701028a003022006103480f0b29502900580e10800200d401002d0624415205152820a1003a04c2d4009000c80b0500d412038038a0399278820208002c0700418001040c44802035201c00c0c801e151034800e05580300b149814441c0219004500306a500d841900b00c0c1902204490780b00c20f80b4019401407000406010b000285580304070103603160b43e540041045400c00100422400687c0100c0e02440002003501e0011202c1765400c100015500009101410448d602141804d40c1c0c1c01c28410f602d0700e010500e4100d01c003550000c00a000c00150b000a032560451203445000c5a1518811100c41c10b081590206040c85410030030755108001044008612815054070290380d03009450004407011030300e50094039080b560130071040400e07016140707900b54426801043c0743d440c03014140500352141801c410409440c0d1114004e9041c91030000c00c1154042c10038030b061401e070b107001400105d885c0d8203031502a00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 707903812 1250 707902562 707902567
    0x901180f0914010e070c0b09151305121312020607080a0207090c020f0604060b0d120302190509060d271b1d0a0e07090e0d0809070812 59
    0x11046016028a001411080c0d0685003030341d5038041c0039000c0c003010740d000c1c410440090008101030040d03954060140d00d140d590408100c0c16079540100886015000060300e100e81110102080b103c4180c41d84070707210600040c21a14a1450716a241c000000c1c601048a0028015100303003464007aa445c08484070302044032460035590000c66102d114566001d002001c00089441a20f40c000548000701c403280039082000c50b01d150030890310f60040b0582084550044808100410107580110620000c02081040d00d41920f558084018159100000200b030300424040307080000740f000c40510518030b00b050761501d03408100240051082a8110802c42d0b602d030031024040805184524001e44d03494660f1030745a805080019801c403400001d00c40003011040003007011220b1540440011b641001d00134055143c0350800c1c009030901d0082c2085500c24035500040e6170085000e22081d01903101c0c054140040258802070072528000c10020166100b200b040141c40d200081102c0100080300d011174 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 707905062 1250 707903812 707903837
    0x270c0907050c19030c06090b0f07080925080d0c0512090109120c0b0c01090606090e0d0c17040306060501030c030b03030a0c06020c070305010e0f011802060d092102010e030c030901 79
    0x190004005c010241c0024580b060090404c0000000c0e1800303008018080181951800303011a030200301241d04101c0c9400002c507040384843c110300c000141e1100301140184940d00c499246107010f0040042d000003c0d00c50028009204040c00014280401a0f00f02450035110b4030001e419500c4910500da00c1c001808604014004100125409098229211b80c0e84420820300c86005e48044481070712102d00d0b01c2c000041e98900d078422085c003140c084020307082e501400c0c2000c1d9250710b40726030152182c50003622815041c440c2d440040028610030000040d02030308080004085032041d0b165a000e1501d400121380e620b03500081600c0070074a82e45480d201c3d0842520300030020b0b0180d90501015441061408010044d042d0803071041c88403884215008840f04100340d070300b6540c98070311452045152040b05409030411500070030f80c0c520b4003007020603064170702d0b07842c541002000d0360481210403102440b0060590b084c0078040c40022403a000b54145103441c1072580d102d11518980c941480500c400c0031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 707906312 1250 707905062 707905067
    0x303020d11010e100b0307050a050f1212071518030804060218041104060f08040b0c030402040b030604030e1f0e0913050a0804030c0506071a270c0907050c1903 70
    0x1801e040f807000541e2000b08000300f080c406041910211403103401440004102800d2a049802c01c07114000c1c102d21a403901403050103440e00001c03e522a1a000b510700d00b06400f00000002c0c800c1902c01c101c030034241086400329030200d070701038010829400c1c4442c00d010046640302d030103d5001500700d00b0040c0c1d15007100d103010030025a894040c03a0000d051064543c240c0400300007800071201c40703880d000b1000728503540841d0b403410704582c01800380240380c0118260075081e01c00b0756805031020700002850601d000020707242284c2102e04400088c5421414255400d1001c0d0403207010820720451440101d06032006012003016030f00a602034508140003a460600700c00312036403841e03000429954801d1a07400d152005502c1400b054800c801c881c000041d080c20a0012508102e1f0414100d13820a49529813041c1105005090720f2000940c40e84421400250485048140c0300004010b2200c24120400e2002d2100001c0510080c40303001c1c400c84410500c046000d043c8141181c0d411501c5020304c0c80c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 707907562 1250 707906312 707906321
    0x50901081f06030518030906040b031905010b070c08061e130807120e0a05090402010c060905070b1209030408070317040306051503011d12092704030809070303020d1101 74
    0xc955129002000018030b071905030b4403c074000c00181c0102044014405125541d0f481000000340d0820030801040260030b1406002d9a0400052401144210004109642074400a07084804411000034000040000000c501c200a12030030016004c035181038480c2d89c071400c0c14000d0002113403685800080e220301d100b10101500030360104000ea15030380c0d242032502080d80914024070220303c2c00c5410036400c0c41e0040c0d0b603400b01e030350041c001003080d941c503401112800c105880032280d0507151800350000440902c040c5e00642001c004542e02e07440c56850f00d40d44080c0280440466400c200402e000303a4502080d12015a0382290768041200718960b0303401118840c030380c0f001d40389620708403d0001824001c2e10503070100340c00328000d02c0503190141441e00300a02c08008030046920102901d40c0203805440500b00d465002804201500302100d034400003041d07114000380032503092508200c2050342040015401c039220100401e4518250755002c2d40e2100d00407074401c14401550f03101c44040009410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 707908812 1250 707907562 707907601
    0x6051003020d0f090c150c0210090e0f0405060a0c021e0129031b18010806010f0603020a0f1b0b0c04050a080f06041e051b01030f0e21120f10060c0305090108 69
    0x3c50303001e001a0380001070a800b074500bc0d83d2040c0e1004c001107107000c400c21813254002c540040242c2916110903d004004091040701001035008821404a0203025007501c0b80500282034004914a621000404000600074000d011070052070001d0300c030191000600b80c2c8000c000881a0211741c80c21500050800c5815111440c0c03400c5110004143c3c000041809030403541e4a40d601054540c4403001507060b40100c002510004501c0b50707610718ad503486039840180c512a82c110300030304011035448203140403004070340c02801d00200180c108094106600340c05c00500c0d00e0b90250071101001d04140d622100e02400180c81180f190b1030710075008180024140d0120b5004040799005068128100c03c02e0907100b40c0c4901281c5041000440d00e4454003034110b4051a12001d000d0020403450314081d030016002005021600500042c1a070884440b00740b40915a2000c001313040d032915035000c03811516550041e00c100318541c0404c01c0007a030800c0568407000d80900b4082900e40d079440740428844032030003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 707910062 1250 707908812 707908819
    0x9040e150901090b18030901030b01260906090d0906080c09040204091a0a060c080714030a02071503060f060e0d060c120f050c070803040606051003020d0f090c150c02 73
    0x8050015240381507000d0300043d4070a4452020741c0c1e6034051030754045e141003840f460150b003007080590540c0d0f20070751140e900e0035414101001c011009004e0169450070408008081d442c9210901076880e400704034050707000300054010048090310f82002011021a841200140305c07903076004c02d0b50a241c40e415120744c1d01000d0411502e4564814030790780a031803c80707221300c4601e610199902d403d09040005109660303058803902220183c0d0380d41e4800541c0030700e03000c3c0c0d4000c000d1100401484028402003d0040444d4014002103090800103110001c040000900781460b01408025406282d21440100c94060a2402d40e540030440401c48150740d441008124514100c05000415040165802001408602001000840d184000c2150429034036800024410322881001440c2640250340c42803045d14040385880d510008654400e01170050720f00860740124503240e14103024400c2020364010b107001400107c038203465041c05103a45000c1c2007149041201204144c40c010030350340404940c0078 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 707911312 1250 707910062 707910103
    0x80606062a010e24060103090209070f0e06032a0406090909080c0d230423060d1109040e0c091602030f130801050705030727030f0501060e0a0204060509040e 69
    0x3000c1d40544c03a0890341202c2864034550b00802e280354464480c02c11100d0b070140c01e4422580b034041003647c8010210800b40704000d01c4032041d4070300d503c400c00554024603000860006610701505072544600100c204540c0c039680500007000015480b620704421914480000200c00780541005401d0f8030880302d2000380381c82003803035000b011903102610503d0300e100c403101c81d040c3c2d800341001403a00d0710880c810302039041801244a10715500c0903590080d80f1000500d1b16103841d43d01c200b41020344402d8064901a0100030400703e484c1e040034002c80d18101158809807940b085a4400119805c2024100c0907c0230858004000594001c2044450030002040065207a00703c0c006800703c82007403400b50041650034070b4046010a40542c041e00c0c00f40300305480e903101c402c0c0001002420706900a0040003581c5041c200000801c903500c05d4444018000e00000c10543d060500ca0001410003600c680061481000200015a4001f041e1552138100300d81c00300e04c42e805068601e15000d44c000b03480c0e8640c0d500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 707912562 1250 707911312 707911333
    0x50c09101223060106030f060501080a1109090103030207050114090319080c0708070510050307080411030111030c0a0207080d1b052d0d05030c03040b04140d0306080606062a010e 78
    0x104a8100c0c0c0180d82c047c80101102000801031b902c1d90b1050502180c4840080342251041e40c2091401d8140c0c00040340c10031121340c0004021200a90060780540c0101e80d09106550b03110b16010b1050300041c05040c508003074a0302003a9603030554202c104500b0400d511000c01c0040041c210390724442c61000b00d84100f40c843c038041d503d54640b440f4085c40742da01404000d10540c000c2003543d1044003a0b4980070321135515901c5a410410f4140342280d4955641d40c0000c2d003800780b000145010f20304415400d40c403800c0e0890080e240c100385400421050303200000321920f0b03950082a5004000d41940c03201811486403400510700890000620000c41c2c20700000b41840e44d01c10100800303860608211201680300e00d04c10348407440143d5507141c10540410000c1d004c04c3d070144155400a2155010f56004150000c041d41090000d01c42c020000e5112002049405410440207400c4481111a1450600840280a41ca8501e500c20003a0315440034002c1300040da00391311600b0510581000d90311510721 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 707913669 1107 707912562 707912633
    0x130b270f060c03090a0c0603060302010e0a05090105010516290f090303043809010b04180f02150a050d05150a0618050402040306020304050c091012 65
    0x4107031701d011400104801246401402d803a80e0016099055100041ca900c86402c4440c2c460840303c101440656203040c3e62a0441e4000d0a040e541c0700c02c40f08141d00c10903c07080b405080050040c0f503140c00011620783e0322145040507904141c0342d58441d00038100e1044103490040daa58020700015000680790070702042ca80101d1112000c2600301c4110300c69400d50b01c213051040c80c1b00b50405010214400b4001c00079071100c110390034000c3c03203a94101e5031209614158003500500f802d90f00c48082d920799041341c501c10304100b41000c1d074400022401628036400145091f92491070070b00051a909500c4201da62184401480004901d140801c22a02c0c00e2008662850316a617817007000a6540c0c0700c1c4020130007580701c0c1d00c0240e00c074505810402d041098800c185801000d01d00100301d00d00070415807400c2502c111103000952041c11b810254a002804031642d90a0000410082603411 = true := by decide +kernel

theorem cover : BRFrame.Cov 707733812 707913669 := by
  have h0 := BRFrame.cov_init 707733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 707733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 707733812 ≤ n) (h2 : n < 707913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
