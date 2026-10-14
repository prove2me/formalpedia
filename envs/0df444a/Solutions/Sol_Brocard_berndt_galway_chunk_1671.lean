-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1671
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:09:22.935404+00:00
-- url     : https://prove2.me/submissions/8247e810-b3b0-4427-a41e-c6bfb7172697

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 300359712 ≤ n < 300539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 300360962 1250 300359712 300359729
    0x708040317010815010e010f030807080417100e0607050712020f010c030c03050114030d1101022a0c030127030306050a120b0a0b01050706050c07020a0e18010e030f0c07 74
    0x41d961107620050b03c4030a41c0d0140b0440c124070707a00100f000b00c0b00b0b2060328100c80e142400c181c2d2043c91681c90ba82c4540180c28191080341c01400001103408000c555214488010409007000000c00c600e100e048039440242c0c203003540d0024080040f038a8100080703400341500584080448441004100d02d0f004c007440b0f040c01607500f03001c516010740c1c6d00b681244081711400c5d18240f08680e00e071560f41e9a044003200800c0c0e4035504c801d0725100454000c0b22064208442c80b00050f10b400404071070030b030800c20b01030340c8659541251341c20903078080424000400189001c40091065483c0202003007103888407108803c9412040844c3d00003014041d030302220003840082d01c0101400d80d2900b40720614601030105861207201c041c001a00307110180704403541d2140507101c03c0d091030000d4944c070000300001070005688400c10400794002da50751426206c01408408515001e9292600344001d05004080304100c1c86d0781000307a00ca25491020003a6900e0715105094079440b40403040702c00e03180a1075640030b03118 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 300362212 1250 300360962 300361007
    0xc0603130f060203070219050304030f020303070b150a051009170f0a0501050117150f070e04090f02041a01021c03150e0403030c09030201020309090a0e150f1b0307080403 75
    0x3007105a4000c0c40c461a859001d03120050a0354100141c1e50102c621f0080c03860704104420b100040a1170b900807589070015017120308210103681c1e000003041e8180c42c8640100c00c0c07422594850302c0c0490101000d0f11040d0b80f044860030382103a024182c1d42440c000c40724a0060041e0150110300d04103e2410f003100928100d0710a070810341441ca00911007801684c03c90380c108680f0b007090005c00a03880060745240d80b508a1030350f940503100d1000c0b200c0034211804204016082d40741ea40d96074042c118200c0e02600d80f1181030f410910410040b503242144199112915448611560380c01040e40041803415409030861000c0c2200f048005000301c0f5503000d01030340c4525000c20b10001424000d40b145119880410117200810000e889000d034510000340164001c12a000080c10f0110016411240e00000807508150102c01d4038200b800d0810010b003004950010000459015145260825585100c160740301903012008000ba00c0014581814050444080b404140c441c0a4401e24031010019848c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 300363462 1250 300362212 300362243
    0x1a0607060b120a11040b030304060512061306030b092503060902030f030c0703050c032b0201110a051e1603140705010617061b03011403030906040e010510050901020c060313 76
    0xc1310744004040314050752a0804807025820000700700c03016030304952030341030404031a10f50104080a000b04030302c0d004050320044421805060107820080c0d440341840e4441d0340380415a1524104082484d80722203500303003035000e00380302c060400081540d42101300070802c001c250012a241045200022200f03100001d8603480792217022481d1403d991203042653f2007807016100300b640d9007103e22040c7d008150214900014615504401d03018850305000110303c0980c031402c007204682003031820101055001600180e03c040380c01900e440b188442c410107007072481803000e0580c00007074032400070305110200e04020403d200c60320944648991002c000d014450311698001d500085420030b1040310320801011419104c44181040d5202c484411040d0550f0710b443c4441081390000713045590540404c1100b0021611510002c00180800099a04440d4904010300913415401d05007442001001c0c061202aa03901041c40c00000f202221600d81380c1e10b504452480c108010f05004080710301001035007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 300364712 1250 300363462 300363473
    0x110102040314030910030c120b030f011a0f0a081c0c12051801020c030a1b03050f06090d0903050a03080604020d020c0a02030f210a0302120106020a02041a0607060b120a 74
    0xc1441c0082507421001c00ca0719454150b068800044c01c7c5008a18900042c140c0f041043c0d014020403c001800c07108010540072040e801c445840c142c0c0e8a1400000d2102c0c20b40f400c01d809548203030b03030b030640340740040b5403402e00a25144c1c1002c0381008040d100c5180c44440151068030f16001040c0c000c180046010940079000c1c12550090942c02440d0745240c000001300e60012444052040014000c1c0044020799a80d800c44040380c03210406250404100200102d00e0812000d03026241300001000241081d40c00a0b152444c50a40c01c41040440881400000c07004544907003555450b0820304040d072030302000640680100350a203038030144081075000f6100350020f54420142c2c0280e06941c5034800420380c95850384c00340606441800e02100c100c00080303c1c2c0e40700603da0101c4500c2c0040c00c0c540625015619a4400c1e4480c40050703200310307000c0d002e40c5000c0c42b41380801e02d50183c0c5c4401600c0d080b0080b034950b01a50070081c045c23a50f079a09491040d19840000082c0b141c01d2010342d11481e45520b0031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 300365962 1250 300364712 300364717
    0x120c0106090510030b070f050d090b04020315042120010506090a05091506040605040608070612060509012303010c05130509151306030210030c020c0103110a11010204031403 76
    0x5184010b420710021500e0039040d10030b184150790304050304ca040c0e80e5805d0010b4807a099104082c0003003041c00c0140d0308034110207219030b0741e0f03582c814000b41c2441c0c10180101490711b41c03000c0c20080c0002c0c0103024007000400004c1e1110400240000c4c015608160040c00c1d42c10012880c00c0c88080a00e40d000340103450340640c4254807409003118540d0b590b840743d801c00f00813070301d0441d400411b69100100840e43d00171424826540508001c04c08030310729803100040381c141c80082c0c0c0306030801d500240c001d01c03200d40c005000c11000d0001c0b12003041800d03d842e0000b0391000061003016000c100c0105000c0d00038448000c0c1c0610b14802038020b01074003008650051255100c6481d050110164810214140c606417200038024423882070800200d40400c41080506941c0701d02198009564100c000b00580703400b0040114440c07141c500140c00240c59002a052089854000d07041500d0a8980c000090703c40040c0d0302030801d0791502000266a60902600a2040d80c1014088500c002c0f4004041c6800000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 300367212 1250 300365962 300365969
    0x1030b220c0905280b0609040c080115020105150d060e0f0c010f0507050c09060303120c090108010510090b0a0e03010905010204060905061201050915040903030605030f0a05120c120c0106 82
    0x400f0030465542e00e060b00c1c800e8084824030761500c8800402e04060414680020320344038002041c0e18600032441e8001000c40302420691004109008010000354100800d03411a0801c9400203210302d20f809030301200d103000c2018900e885507210a03080410b100440d4401072143e03206500704c1741104481c00035550ba4000d0003648a001480d484c090030b40c01c0d40f142069600c010340c040300801400304d228082011003240180b01765003511040c407507214103018141e4524040c2e4040030b60141d8640107000010072240d4160400d5000e1500046102a0181d01810040403a84100d404549803020034000700e03818804190b406915608041049092013010360050084818686a081c485543c41d414030201e800341d840c14031141e444400040040e4203107160615884404412041c41040c401c000160484501e442d040d00040d90350f060500050070300b0003103101c0205569008103134040c42a9a1107039124081c03001403024490114000f920302c9410020202c508210340b058a4aa11410f410140200414131 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 300368462 1250 300367212 300367229
    0x1a0301052404141803070503030f040c05041a01030b06041a0910230d150b030f10081b0307150203030a0606030209060d0218040608010b030c03060c0301030b220c 71
    0xd00403a103442d040c401c20038140704400c0e045216644540c00c0031106540e040c10113501d0700003000780300b0009200f40300071407054014100c521100c4c18107042c2110425025000a030180b45841034820403010441d48190300401e0910300414107151078000700c1d07014000c03030b40220b00e0590b04c00340034410002054080c0039090f405a49903160f501103003008644a01c029100e811030301502030380c0c8481c0904000001c0c250a100c150020521241100011005080c00d50020a4080001c018400d0b11046c2180c0a5000b100200ca10b0141c58140042d1030b85950590300040d04264490710b021000b504c041c000503000301900710790900c0680c243c80002e0f480383d00482d054a03071180b0309140070500c00d0280c030030380c0c3c50010007403d1203040a403402e9805d002544405442d1001c0e080d0154a03885542d42c40c01500041e008680002c204204404241881e010305100954401d03080349081110011509050300e04480d0401e0f04105c030f40d110000d160800c510743e05401c0300c081c0180503c2009102040d000c9008844024 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 300369712 1250 300368462 300368521
    0x13030e0909012a0f1b0c0e041407080309060d060306060305010203070801080d050f07050c041a0406060c0b0619080a03051e0c0a03050903010b0301020403120206060d0b04061a030105 80
    0x15140c0c140c5641c3e0403501040071034242420f00f06080d10611800d1821007040500b0f03c0720860703985070000c14180540c0140420f1912104010802840301501c2c0194030880c7c1c0103044140c101201c090712805002026400742c400401c5c0700c480b03c80eaa03001100256044071040007810b0304d07428180e002c0c0d44202c0703c1030b010541410000070031010024a800d050369a0fa5130b0765051204400e0703d030800741d0084005a80c41e00c00d140c003000c8640c0d0303640306070200250844103e0361840801410301040d01d44d158015001d21101840d880003041110011643c040011140307812803800040c007021422609411801d00c80c41074190180416030800020101994040507100c040c03252410904941e00c034140c031443e07480c1c000040c00c2c03001078016000b80c80f107500c00400100b42c43c604c3e90003107401ca8006510640d5445250b04090914076010320026170070040903951501c0112507a01c51400c1a000900300404207036542d0703d02c0c4162051511074424900b0000c0c002d00850404071200c4520b09200a040c80c0d070844c0c003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 300370962 1250 300369712 300369761
    0x4050307060608030f040303080a060e1312030209010507110d0c060e031c0e04050403140c100606050307090b0a050f030103080a020f030a27030c03080a030b0d03050313030e090901 79
    0x51740c04070050100b00034946802e5903021601154090a01d811080e151840402d941d004000d11074130805014128400a581d9070402520b0140020079480a1503c104210849642d001040f26412500500340f940585415404100c0c240003240003c0d06860301c5550211302c40307520540b40b01183d01c1c210201e0301d0081da1411200202d031b140241030070202e61040c200000b94200b40c2c0100b6801402030030030b0000c00d0420890000150700c92a554640d070f800818030000b10f103519108040280026192140c150725002c403025010040030301031201d07003140c003103200c2180070b00c244100c030343c44030400404540382d50b0340b80781c0700b613440c0c01280d00100980075114640b0320940c400015580c000c805940d0b103070344801c84084035050b10403190010b94440318008501202084606140c00c0042d445802c025985a00f011030090469041c2025144a50000c200e0000429440760035240c110303180707252a071fa85516904e425142609504130090b007084002080162120f410b61041621050005144051107038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 300372212 1250 300370962 300370979
    0x4031101020421150c020309011101051b030903040b1902011b080c1b0115051804020a0b0a120c02010608282402070501051501082403100203040503070606 68
    0x1c80c010350301018096280d2002e14560f0100701c04146000e14403050072104060010b40641e0f100e0380400b40035071f10004101405e544c0c46007450281e01a0400204018200100340410401348a501c20200300360100c0800c490b10000d1044600905036404080c0c1d940012143c041040b000381102c0304055441c184008a10340751007013820014590594880046a031183c646001640054035002c2c0c0c00039a0400c80e800c0c0613024450007520f000d482960000e01841c000401c880001c90f62401401d40400c1c0d4280801078803811750355419191002411500c400c00503008440358503019079142c50140c00d0941c4180616019030298060301d4582c402d40780a00c0d1714401c0c0107a514000d8508030a81d4000084200c0829220001110110303044842149080308040000003030b42c01842c800d0301d950350b40d202481a6200c072041200003004003130a0100309440e02444110300c0c0b43c00408511080b100700c01c2120300d04e5606000b40c88100090150442d143e041c10304101d540d80c0c11548040343c0141c81c0500c0840c2040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 300373462 1250 300372212 300372217
    0x80601080f090705100c020901090218030a05030306011209020d06140105040218190b191205060108180c0402040603060509151e1906170c0c120717120403110102 71
    0x410540c001c04074649804e0034010003540580d500c200300841d511124005036901700e0f4042c001c2911103800358881095010030602c082401808510030f522403681c0c1c074000340d008420b0307a40c040024202010100480c06160700505400c4500079400307855041c81c43c5c1004066801199600c1d01c19008000716031300d0b0001d00040388a042d12000b0403842c100c1d2190a02c0c50024955010060140b242c0620156104e41c107a100b50444030403200ba180ca1140c01142c403039404500c170b401d1841480f1044c002030038044006021514090b01084e007a43c0401e10f402040b5404200e550711081c0c0143c02156610f64032003005004118501409100369403c201081303100b84100c2161901d400b0050800559010a08105070090720070880581c0054045030461a078140c0d295222004140310f40311a83c200e01891000e611034003004254031035100b0144034541000f000047c00320800880205019510f282c2400c10000010380101542d40354900001c202004800c1041d403940902c2c460386642514104041c0310500f43e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 300374712 1250 300373462 300373471
    0xc05010f05010503100509030c0601060504080c3a2a05060a021c1206090e0c220c1419090f080d030902040e01061401090905040b010308070212070303080601080f 71
    0x160f0200002c3d4081788216445240c00c807281c0f4048034030f071070001e00129090030002d07805500405c001040412460805100182581c0022a04541e0011002a0300c003111040d580004005806a00018100d101c140c40f10310032154020544512005502c400481d0340d210314001c038128065000301c0000d080c01c0210558200c2d00d0f460300503103004800c401ca12001000c0c00703444202040010564a4649800c900c40c807406488540780100c1c5003d0405801898548421982030182440f00c040e1409511003c90491050040040110381c40a04020842e007940b00306031110030407200020400720040001454003100082911075460704da0759505182e600001c9840742c420250400843c284600303120b907226030b0a49100810010f02211141060350860b182c81d00700820f86035403200035140968008a04900400403075209100900d442d0356801201001803000812103000032412504541d1030000b4003820341d900d9012500c4003950b9040051080070242c030000c0c041075035000418100d20300392114a21a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 300375962 1250 300374712 300374719
    0x40b0732010f051519170607080705130b03191508070e0412200604030905030f0309030a0609060207140a0303050c0c0d180f08030712030c021005250c05010f050105 72
    0x4007000428010f6030180414400701c1c0c17605c00c14001c603082640b29540b08400791100018426482c00300000741415038042d180002380002030000603480c03444503424034203440d07240e84010b85030b45501c8090b180c0300310a401d2542181d802e00800c911044604000c034402c03a21188100d410b0680e5500c00c031182c070b00301620b0142000319424204142540280002803581440318000408001c904a101741041401d48044000803e611410000d81c80e041000c84014440030b0b014500c0d0401c8200006c3e0350f018030300c00040040d52614240c50038030080d58107079081d09400900b01903081445007811920b03519410000c40109151002103400c0017130890690b1180326065009018904070240203560440e4100341202003051a80c00104031002c4c032131000402011920021a00c500440c40c10154820b440464841010b01e480c2641e00543d900282060803580b502400081648035492040703400410a0a211201d00e65030440358026680316020702d04181c080e01c002c000841695081b201914000e2140750f52 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 300377212 1250 300375962 300375991
    0x60610051b30120709030f0807060c0212070b0c160506040317100311031c0c0309080d02030909070309060528050f010501030e01020c160e070e06040b0732010f05 71
    0x46180810f00d01a0041c240c0d003014920b0b90350700d85e41d004412002c80c10484840d01c0100315a801c101c000c0c003402140014600103804d000e0b0010340004d0143c0606d800c00344c410000350002c07a40c03901041d000c6030f4661f41403801201c03104050782001d0b581e070b05c400d482c2107001a1a203031030503840492004115020305061040007440380d145071240f980300d5210040090303141c0680c45e086000b00103100c024084600c03160300c0e503515144182c20701500c001c0403a40401c8070740d004400c2c801c1c0000e6010088409040c811264250903440d042d90031001400d1060b002041c0610306400c0c40507143c622a44031000c10304002502c4a00104540403000703460701078900401100d4014014025917000340c1280f170a81800f20001410712802c1e04409250100b81c600303101d05000f10901c00d02022005c1d218040d406105801d01e480e986846901080e614407942c8150030304a5000f10700c12080240d8a0407150290b140d00001490700b009100a100141903031400182d02586010314000c0300d210f0901a0034070411076140f4113132 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 300378462 1250 300377212 300377227
    0x40512030403090e061c05010c26070c050307170415050c0604083402030111120c090a09051503010b0103090305071b0b0a03020c01050711060610051b30 67
    0x40884405400c0c1c6511090700c803440c6c801000600a0316111074060710012514104a250150000008040900c000d82d840c09014048290750140386400025504e000d90140b45d0a003812403c4d801848801482000155004c801441d030860240c0159882c1804189480701840015649882402c000101d2034002c0f000003000310798041d0152003544e1511300100f800e40c40c074640310349402071146802001603041c8000001076060910440c503131002041d00c85481c0040c02d0b100380361812002490700142d208001102081511500c200100400090342c0602440c02d00a204088030880c11024030700a618114980c08650b101c2d0103050b00540c0c05890b59803511800b61581014101400521400b6001d03800002917110710f901c1c010030681510340c0c2e0050b11020482d007072609489015044038100040c4082e00d10703401c0400f003240c1d50424000c4030442410010050107807100d004910304240c07204c0101d13030050049240400d458541050340c10840e4055500c05680700c007015440000002080e00c00d0003c0c9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 300379712 1250 300378462 300378479
    0x60f0604081b040213031506060e030a140c0603070201050411100905040b04060b041e0b1201060302070f0c120c0801020f07081e030a0b040c1110020d150e04051203040309 75
    0x150300100c805800545031040110840c244210305c0c0d80229100d07052804036a04d00d00e954400d0074081d144901d821a503191a0100007660f402c000500504035000741c41080412040407c01d0700e0000e100034100c95124078104401038000c9c001100e09071a06159441d613000146043d80c0d9102c402801034607900e8509041c1400d10006091140402d504141c2e1030202003901c00c10040a00020000703002844500001d062081003180d03503551001c1c2001d4414031503400c40c4d24810342101d0548107503240040e207600035030a0800002c070b49420701030300707401c140c01d4007040c03d280024405070344174040d003882d20046560f850060700301d200740011000404010f100b0800042e9100d8010000071405050302004400b001070360b04016070054546101303840d40c55402512604003401010382c5100705080c001101190110407944900d59250a101c3ca160b00061103c5403040036803102410000298030f1a040548a280b0f03100e2940c41541e041d02c1c144602ca5461060303111030303400c9900c181e503d580d0b0f03007c4952800440 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 300380962 1250 300379712 300379753
    0x6090f07120b0102030c0f030310080a020901210c0303020d140c06160c050105190f0e070e0901090c082515030507050d020c070e0907050904020f01031e0203060f060408 74
    0x2d182c114001040030782e10f600780800503541c1d09000d02c0d01469a90070403044400b480f08441e0b02c0508190480010310015075202e820042c1120a9503211940c60010892209800203c08a00a04100665030040b0605600042c201400700b6692194a810340758462100468020036040d0061544080c0005007020080380d0701b030007008614100142d24103150307a1001e003501c10464002c980e41420128504a10200380648500c501c5070030400c0042200743c94001d40c40b840380340a01d9800d048e443c408a00020401d40c030031480e00e030f08122041080303034851042c252100034407220050900321094404015101c6500040104c40440410701d40d6000090306c29006000300800314401d22106000c1c04d0326418a500040c2034104000307001d0000941480d40d030082e8010003a01864195120035028085130302c400c551503810030307011120a41c2c81000107004034050415041c805959842c6d103034195a1341003282e00514000c2d00229007205071004010300744031590155201d8100b441c0d200412034064414143d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 300382212 1250 300380962 300380981
    0xc040906020702060d1a0108071b0302250311030c0d03120f1a040509010b2b051e01060e0606160f08131802090a050108151806090f0712 60
    0x805401c000d810703000554190000d080c0714644680b100c6c17075600c19034020b6014084500003401c083d01c540c280b5480017010700541c03000b00c40301c00184042034814103000b004a01020400401d010024001d0300e04001710a0307040344011a0113210310054200c1c1c61501003510a400c0d10003818100c4070341010307141100c01884032074010000c65520707000c07a461100180a0b007680640041700c0d6421541900b8140000c0f140300401c464284e03450500701d1416651040b100d00011849503000f0310b40b0b1403280282e070824080c1035400801c1ca01c15044072111030251103003564820100b0038000c0228039034401c0108030348503044944a42c450380400002071a400d81100e120b8140e402062103004104842c1d07900b1040303a00c4084a4800e080300300c0780810201c0d5601504449082c0c58010560400e5500c1c00422109180380c0190b41c1800340f8034000504584e007001400020b00c00003011118058041d150f0750b80c40640940b060750040a071440050000b0301d41c2c034451802085550303074600c00c0107050061400180388001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 300383462 1250 300382212 300382223
    0x81207031506030b090703090314090604090203090f0d021b120109060c03020d060501110304090507120216060b0d0201090504110c030c030d0e0d0c063309050a06080c0409 75
    0x2007008119034401004405000162400150710382140b0811014141c010000000c041c02c02d8080030000f5032150040d442102007210a03600e500d041c5001591a006070341160300c400d44017200b00301103c1da0000f44090034140c4101600ca03489050403089841c0c503051101826003070b142d50000c0507182000e800f03d9090001075030001942412030f03510031040d00c200c1d5505c031001030303000b151000d01190b4070b10804005107024201200c1c1c80f28045a03d039180d000302e03c0794120856403180018503250203110811034180640350110b503100301100c5c0448140055007015248180380c884900002e082100340040c00640584402c0c075468940340070080a44403034003051410020600c006504000c080003d840b6031002c0802450b25007015040a004440ca1000d000c070095202a84004609800c1124611195007100b004039448031041c103112500114500e8000d081003c0da1102c1c9542d44c1e00008480559101040078011601c032802c1817002c0e10400d0040b10396903000300c0581c9003c1c0c90301e5407240d00558480c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 300384712 1250 300383462 300383471
    0xd0806061204050709060510020a060b12161d071209030e1504140303031603050709150507050114092a18010305010b01020115150903080309010e160308120703 70
    0x410900c1e803040090380d0850350740e480400240000c0044d4011013000c0c1c041902c410354020744c0d00000030340d20082d800000d07004075928130040340c00352154400b880300340b0407210488500381c2c2d0100c800a000407092040c2d803030300f000e0020001c04400c0352040880c0520000d542e22004011084a034000500000e5012014403440108031a81d5448800c2e02451002c4518080c503191454451103a48100c20609458404e40042041020346092144bc094412040e0700d0001a2561400810340b00c08041e600980c8045140518101c1865403010041402034072943c02804042e0100303003100c124140c00c3e2070b0402035030030200d0b5a0740301a1183c1c0000114240b621055a402540003011460380003c400b01c003400c5003035a200600c10b100013400703540c1d41c000342031000700f100385403403079000060340c0050044841403840340341100030081c0b10320300102c0a1904940600d0303a03800e000304028006d204401c0c0e11040c038007940e0340b07880700e41445036440c9040f6500a0021850500e03462807880081e00d0040204082c56601d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 300385962 1250 300384712 300384727
    0xa0827060115030b030a0201020717120f18010f0203030127020d090b01060503010308040902070201020f0f0c040b030f06010902090102070f120213050411150c100b010e010807020d080606 82
    0xc001a034000c0000306100d02c0c8281d00032030010180c1c0e000341e0069000ea40b01d0420940182d900160190032280b60861108041c00d1004446051081100c18406e0000011407030540030030030b5500030300240c1d4100040618150302c04006450b203120413018100940c0003400100a10356000c503000810600c039180034401d621060804c0c100f03e03002018509203142d80c5000000411221024850244c1001d080c014295813465032070344128403590260700601500401c450b0110790081011500c64188801a1581c1c4c034110320f14140e9411003141030038811420a00d29020508001c20440010303803d81e006030115a01307181e5004069448800b2940c11480360240c001000c0011100c010080c159141030030140c4809801000340300c0c1230300c14010000d5440d001c02d200000d041078071000300003034080c0d80e03040d100c22113500c0c00d08141c054644140160300500c20043c1842a880d40031101a0400f62038030b540a105003001150890421030703d220140e440036211204441c000c091b0344ea8840381c0200034038508100d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 300387212 1250 300385962 300386041
    0x6030c02010f090f0302071d0105010f03112b0b1305060a030b0c0a08070801051f121a090a050c2b0c0f0207060e2b020411120703020a08 60
    0x301050f06a80b00c0b070b40449404100b590500401e8000d000c0700007040b400d810007003003058200c941803083c5418440d4014012096501a4004550144281c03408546615200d2141c03035101c05074034a0031300343c070404544010182e200d511420920004c040c14890780d28442801b154010031018240680c808251b071000400100913401051140980c107803691348a01248102800648000c3c0141080c0003036000103000765100e03840c020107201000030003a01c3c107010302602070303506100880e030322041103081c80d001c00c0048003541401114800b041c0c400021540c1c03040c0b08003040711801c3e100140b845904100320301201e10030700c1c0524010320700c1c4e40c1c05802034085268680200c4007880080404a486c038030620350f1103501400420014031144c01c040f0070050f0b5002c00101540c9a0200b000c40d45a20000d107080e03131140940e01c541d030b4183c3c0584200701d00039620b0701030100c1e0340100c0301c080200a410000680c00500c01c3c02501c881071815101c8601640350800c4031700c280c4119050203000214050641c922245 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 300388462 1250 300387212 300387221
    0xf021306051b010603121d19140a05150705010b03061e060907050a110c0a0303081009060e0c0306030a02100305090c0102031305060906120a05190b090106030c02010f 73
    0x2554494958400b110351450042c0c01c500b501d0200564500041000807a000c21410362003c40729141111034080e4030700e9007180e100004003070550080102c190380d4414030350b0070003c1c0c01610340f1203000907002100b0508005054146000c1c0907000b2400303072514406c00e034032080900040f510540010807403001d1040800c1c0360410807540403181c1100640c213804001e154440c429005601980d0420803407030b00541c050600e00c1182e215000308440070504800e19001032122a0451100030151818255a801c005051901c01c0e5808000c0c4580719000041c1042c0910070300e0f08503116040300e40c1890392800c0b400c001030b400c014040340d0503016401d45d185c0180c1e9005034007030a00103952400260b5003801e40915150441300c580303650540d40308000e00d000000c84510a00101c68040301c2c01030740d980036040803a4040c018500e9940b0041006000d03c0b00824164002d02d110314480b92159a41807420381880c020b0311400d00400382c11143d07040040c4803d52082c1c10407000c103c0d80e40000309120b48080403080465 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 300389712 1250 300388462 300388469
    0x30717100513020a09020702030c0618061201030308100f030816080c010e070b0c0c0405040c180c080a021804092414060103020a02060c030a1d0c1201110406030f0213 73
    0x328076014400b0114642840d00c0703400341000d40000c609015056000c02c3e82c0b0000ca9210b01d2007a01e02242c10300740031007100601c82030300380080c100d1034880700c0b0128900406030083c00201d01080900c00018003400107801400100e071b181000029105145440325400c0b07a21420305a0a078240c01c09040020440c800000c04205a401e400043d01ca01024903442c108001c0d074000307071403121041140c541003503030015000f000004121070000d03945d21603281510041003a5401180046403901421644801c0fa0380511010201c0d515190b030030342d84618021040f0f21035103110f42480c05031a5010b6015080c142e203c894807a02c0f560125402021241c0d108903190454001810310b1170321066140c2200c9551034115401503000c1c242903052244401c0c0181d01c55200800070040d41c00301100054140380b00d504011006000d642e00001c1d4144007200d96601c0e05052000c407800f0390405600b40c416020f0510600e1482400c11600300c0c00d15003400011805003014081c0c1e40d902e00c0c0c091040c80c100e1529604080c004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 300390962 1250 300389712 300389731
    0x6060304080c19241104030b0a140705031501080f1501031104080f070e0112240204300506070c02271012020303040b0f0d050405060108100b0307171005 67
    0x100040030001e110300825400c0341083c02400c090962136201c404078291800e59034012000c5c00155103c042700b4001b08100b00141d1990f2080c0000d00c600b444c0c001e00258080c405d82d00022a510510380f0042da02031030152441d9800075a40c00014030350b40a005d07840403100034140b4020130601001008440250456000341845410180c7c0c190024403042010000400f0207139001c10456140c4070418840c110100d00c06043c2e20b12a40c2405c50710701002e8600b02c0c10249014003151100d454404600764030b48016003802080f41858003206407424000c00c05d86500b640070b0300405d032a60301c60804803a003803a5200100c1c0c020f06951008091300d803030001c0348000da00b0b5080c11100c0c1861720460581c82c0c6e01995101d801072142c88842040561001b0040310182d500725420740350b40d490f02000251303542c81030101005866240000b40020080d0101d0402d048503100e2044500d002c1e12211031104a502010b0000e9255010420400c4075411440030015009a00d2095408040c00c0c004048255007040f0f406060 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 300392212 1250 300390962 300390983
    0x3061305090a0c171b0a17210a0306080109020f15160605070e060a020706050306011e020a0203010506060a200129100306080604171911011406060304080c19 69
    0x1c080310170040c07001d001e003c014200c10348100100124524420b5401350040c103107120f00c080d4401803010800102000700801c915030040e00da10304007a246402017180c500010342800000100108140959003409800410301440c13141684104a6501c03d0400030743c4001d802408580409964100400380c1da40c000c0c2c902184a180c03400005000340c0400c07041d50700c00c090910407103e48070b5000401c481074031001d0904a0362911001d0050b01c0305400c2e00e9090080c0105949103400c4036902050850703d440c8264000c3c013a64072038008009441c083c0905540004030b116400004014842d008034401000c0c0d0000000c516094905114180d6140c1898200140408144c0d0100e42028180b03030740c9031030140c035003004018101940107440da180034101a096944901c0f907001c1280c5004222031584020102e04007050352400d00282c03141400c06201c4165500c0d011001e0740644031441024881c0f04003d100c10300d10780e05d507607c01c030464200d9040c40551303101e882e0761101d03900300d08510040041e0051040b540c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 300393462 1250 300392212 300392249
    0xc0e0411040f150807031107020402070807020109140f04020304140609060f0f010303080703020d1401060c111e1219030c05010c022803020102090603010603060f080303061305090a0c 80
    0x2035101e102c03940880d4040441c002c01000c1e45a12802c901d030046650300e000320388130071103140000311400b6a59001c0c0d4420f20024151040010340e50080c03501318400e0301c40e075200d15a1400300c941c02c009003048482d0005565001c0c800c0a16195000f56440f51040c400c90b9000b003041500e142c0340a40803151103649078022814445020129041d49502001d0081d9400540d07040d5075004007034040151000c0b0516802244000c5000b400341c20044c0036107001c80703d8001c19a035446000b001350403803010944800314100c00c0441c1c01d060600f80100c00c4030080d4203a0f034858200d082801003002c170207445083c1901400d85550403041c02201c0e010300c03250007035840e81d40c07e0b903040c1011800c440c402156007065502a0705d10311001d40520031546803080500c0e10010000700103003001c0c0c0c064810080e400358007120000021500d40d40540c0907d00b55102c14101c05802c0d603c0d000d499640b0703c0140c440c581d010310400126440c02c210b68109580c4418401d00340d5035544c03104e9907201c1ca0a03110341c226540011140d070099 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 300394712 1250 300393462 300393479
    0x4050a0201080c0a090905040206070609050705041104032607080a09170a0c060e0a0b040905011a07050304030b060f0306040303050723031306060807080f01050601050a120c0e041104 80
    0xb10342015803400c0d4286003400420f000b900000861003840c1074644c0700c01c0040c0955030754106650440d80c21907000d0040039202d140c2a511030300740b40a181d100b1407800000c10040c02d84002070b41c040e0381c1c1c803400d46581c0140c040041c3d000000502c0181c0d000c1102048008005045c0b4000788c2428102a00c42c24406420411511001035000750018104d600c11f40e0140042101061010110380d40303402c012005030031010106100c004075401c414010240090001a071001c0da03800309048a028201ea0080e00c0c41000350081c03d0300c500b0502400e40d030b000380818801300d94a1030203103401a00c01000707112001c10101c04a41001821107040c0d0200384d442d0100714403544c100d0b0100d0300368100703400d039101000c080102c513600e580006404000e00c40903c060810411040740c1c08000501071540840745902d83d5500002c0da2568000c1505202d5401c000104030654007900c1030307a41c05080382d11441d404a011600920007010b01d008400200440e04194419986071840741701604d40b1400d917071a55139401c14041c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 300395962 1250 300394712 300394727
    0x90a080d0f0e090708090c0612160809060106081306090303050f0a02030106051206130501031401110405130207060906020310090515010c0803090708070b0408011401180c090e04050a0201 82
    0x10141400400c50107510ba965079032011039801142c0d810095034580300c00b00e1480c601a07261154039000500019200319848201c0c1700d0fa031203410008003034a21031000d60000c840d2480b0580d000052079000e20018040e02d03004e00700d0507603c0b4016850b03440313403003001c0d031290401d403107054005502003a650320030302c400030781d0303142119a02401a8509625651421000a046101c0c40882c041000300d04004a01559907200c243e100d00100b2600900055071241407030f10040c040207401246c01d61030840c0010307100400c075059030101c40005104901580b198210358002e5400040c0480300750342da60f0751541c0054414800b85000f0389040286010160030000c19804841d4050040300e821010640020351680e8400360790b480f95a800100644c0726102c41580f02e240c10380d1500100414007402c40b000c120030090b0b40140c001c0b01ca03400c00038005e00002d81e044540301c450a004410b14501c40050100101b44282c11403c010055454048256039035440401100e4409480c01c4545400000142c015517a20000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 300397212 1250 300395962 300395987
    0xa05011d0d030b0603060418050a05010e0d081b0a03090b010602160807030b130c030b0108011a0904020109092c010c09080d0806040f090203031b0f0f060417090a080d 73
    0xc041051080300c0f030000c0c2d29400000d20f003900c160b0301c42c240907051002100d1441803440e801030444500041c1843c156018020388031a038085c0d8850703440d0300380d040c6c1d11a41032a809406400030300706030048003400504e060b42c0803902c05001d054440100e440003405083c0241d009006a43c050550061400c160009410b4168003800080d400710b2003c1c070118cd4030f000f00a40009141f504a85080d00e14075015450280c558070281c1440500d0000148110040d0004e0150040d5100806c0029a680041020070102650080e0004030200d0082c08146007590000010b4a900c1c802da01c030440821880c04214404007580b5001a5180c0812056080e04040d5010140980401624118006250041a0b240001c000c144a00d8030b0f180b0840083c149035000030320803078000d000d4030368507021030700003410546a448003450a4030850000c00c5071450080f65004800c075401e0041c009940341c54850100022010020800b0b01108100d41c0c0303054bd661152050040110101070b00d1800000000500303900e04485 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 300398462 1250 300397212 300397217
    0x50102070f060e2b0c0501080c031302010e0f2101060b0c0307030516170702130506010507150b06070c03060b01050a0504060f0c02040218030f030703200a05011d0d 72
    0x5003804050b4000b06502c1401c038056481d091008113020002c000c4a01c40b6a010036800d01310282c402c1031100da94103440a8030f0081c0c94030f42c12a01c0d088442129807200300d54100e03030b030001203444000540c071440e007810709800020303c008008544440051080d0351a454156101f19800038518107100c3d082c0521001411000c05e00340c10700400c400c100c1d440344030f4140014100f003c0080e28045140c02c13074400100d807a400035100d1b0704800041c000c407441c035800304038207903c944a013207110300d11482140511482520306945550511809a0711301e15605003500c81e810f03407a522850185125195200a04121070260603041c03c0c140c65030805204a500440050741000010011030313140b0340d040400c44080340d81a10b04508940c40d444030407280c2c40410000294820f00028031445040e210100303003c41c000c03044080e51446010310103007035500c1c8650318004012510031400d5491041e10514410f054070b04000503510000d500c0e0b55010b00311121f101d800040304009002002d00700f04100700c201385496590 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 300399712 1250 300398462 300398489
    0x40902040c05040e0901050f04020645030115140402271c030503130602090d1412041a0903030409050403030f060b0a170601020a170c280201201605010207 68
    0x108ca2040c0c518038002c0c0068060400050710b0b81d440d1110221020b44100e82303036441502001c1c95080e01e90070f13007000c07007101d218102c44c2c54100146141c10301c110641710138588030444d1150714040c660317251209042c0d2000d0b03025600f408007800c3d101d841c00c0344038035221130b04002e041154811010004442c4001c0c80380040e090801e0f40110000350018101c0e90070100601004d4014202441d1403000ba106100c4800d400110f07540e40c590401c022010703ca54404081c2c03058505065000c1c4500403140078500c00e625940e606810f0b85c00054140a0040030800c9018003a64509a1150000025904c0545003200043c2d0b407280b60344034003d00c03445000003800d03400900c54500600301c00300402840c0b613034803001c0074501d403080410f40d140e008014811825511158800104581e913640d98259003145104c60300c940035258106a0540d0400158165406241b105d90310401c0c182e00110f50252462843d03082c1c207044c10001c48040c3c0d80400c5010304165082c800c0d080741038141000242008040d5121201e0701841 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 300400962 1250 300399712 300399721
    0x306051008060f150a09091b0b0c03030408090a0b030408040305010b0105071208090c0a0f0f05030601081504060b0a0806100b160201030b060415050d05070f08070c02040902040c05040e090105 84
    0x806920f65003003100340c0e002c0b8083d03203180c50004103120300503030050f58060b14100701da008001800c0c06240603405502040c448003995040c4c0d040680c07060045c4101d990b0030410000d80040d190030003070912014007030700b803142181d25110042483e5009840584100401103020802c02a00b4081d202c8142000c2c40d04905101403940c4604d10207104410307500c10300040d4800503007007510404c030031a9408001401c0c929081d607a4075000c0400321003400b0b06128000c40c2c1c07c002c9030a050016105048400c1103000307080100c03140ca0f02888400300900121440f81c2c451001c0b03469951000380c100003030801403020348228105222901d82040c0254405043e800c400d01a001426540c01c015088158080c20301040c0c450058000030390b2032143d604894040612190b048890650204c05445000034401c800c004a4503514002c1e0340e026600309040c00000d401500240c506440f0f0b00a1050180c030140c8040366070740d4958000b505950b252003034100007410100d07081000401c00c10320310b500044100b0080249061 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 300402212 1250 300400962 300400981
    0x15021209240f04020d06020d09030e0909190c15050406030b03010603021507050c06070b0603120c07090b060c0d0807020706180608060114040f0509070513061413030605100806 77
    0x1402021440ca0b9058500000c00703546801e04070100d401c0d0302c07490071540d070071079150f040c4006c16440506500244d955202c50340f01d0304100320382c18000c9451000902407040c0c1c60020381d100350702c0307031000b03e03200ea42003800014136840c3c200c1595250b1b40c00e510340a888a04100000f401c807a03081c080c0600c42d0f8100f203020000358503009000c000c0003400c9640303690b03110010f090292402c44001401c039001580080c40d4010f024030402000c0c040e0b24120281c07540760065484010850095212200c1d541d0001182085014032540c00300f04e0b86680035100509103941411003e060801c048240c00c0405c0242040107080ca0381882028050240e0b070a1000d034143d406849042000d0340c5001c1c0d00f050024020205001c0da0080c07041420803581c80c1407542c0d5441c1c80309039045a01e80ca501c103144c000d40c51200880c003881d0041080d150583d16030040e440c0c10b0b074038200b021103880500c01200041647c2c1089611038518080c109031001d14011000443d15082110065490880d150b110180a8200d00280b1540c0b00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 300403462 1250 300402212 300402283
    0x130b0a0c0f031d1b0f03151501030e1606020f0d05160305070b0114031e03030402010e0a122406051e01050f040e1b0309070506030415021209 62
    0x41c081c40c001400d80440450180841c1c0221001c18040c42070b408404240d4020780807002c19000300755030484072900c084040c16650700a4401403621805540000b0341005501c500400034400d052502080c034040980792241001162800c40901c003003030300c20a0010139010440c50351390514940043c01a446049030013019402100510341d10300c442020500300f030500c21760035550381d0343e0006003104207540e650390700b00800044104600e0003400b40044603a60400c4020b08100000380807005145903a8a81e401101c1580300c100b9560f61000550b0300101d03524540c1020503215510038032802c00d41e526254040007000e18800300d1084850b0a126003409075441d0080c3c101108180e520407140424074800040e100741c0180350340000085e8020400040030422080d0040c0a103051030b051809011179080c0c41c8105200403a0101d10030340c8104020040c078208100256401805030000558243d00e40503c00d06030b030301c40c0c405280c200036500c0030b02c011100c0510402000102c0300c030036264680c411050100902 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 300404712 1250 300403462 300403487
    0x5150a0807030308100503010518120301030305030613091509020103150302030a3005040302180c1c0f020c0a030801170c0108070c02040509010c0e18060621130b0a0c 73
    0x444c168022600f8140d0341c1900e034024140050080c4050314144450391407001c0c50342d055010f0361184600c50940f0800c08011241030f250142c4d122481c690301c41060107106101c1a5442c0780039a9031300c02000200380104407072400c40b0b1107410040342c006518000107041d101c0241c5654420420118104010795000a0310080c1580c4090080284031000920a080c0b50b46100d0701045130420355060f2a02c90f60100041058030320844034a03003425503801c0c1c680c0d5417410460780000030140400c003084401c0a42c0200b50101d40d451000813846500e00c01c030000507600003504c01c0c92640d104d08042410150071018030360240511501c90414084929060b80c1d0b21903988882c241480500e02c00704014910480710102800d801810034001410804180b40c0240704110f14180040d2103000003003d0b074980b40c10140d1350740162107615a407540b42c01080125a604c1700004c0449101c0b04007070248160900d280161146a110343c9102403000c00c1d081840e0002e5004140c801d8803450311003203a210340e802800c000ca1a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 300405962 1250 300404712 300404717
    0x6090607030b2e1b0f02040b0604120b0103020a050105030702060106031503051507021b09310507030506070c02090f0a1d300a03020c07031505150a08070303 69
    0x41880d80c9002c100c804050a0b040203507001030488034071140100d0040a50781c00b050f0740e1343c001320b00540120b1603150052204000c1c505408075a0359000761a01d0b070000c000c4980001d00032440c041e40d0700e070401070051282c2e40403945001804010030551030b103103420300300800003030816034907500c0d25480094450030140200d105056030381c00400300c50094100010061540b0000b114840a2944009890810102c91100040c8503030410040144842000030303068110241070880c940e1240d1324148001032807005c6102d9048241d440108040c0030b501c501c190024045c40c098001a8107508016003000c2c0000c201c101804641c05000340180c542c03c1c034103a404039110740d04d2015030301d07481c0f40070307000d091500070400724003922041901c101500450615020114032003880380740c80030380d090085c042144045222480394180101000280030303030001c0c0b07940d180100c00d460440741c40323581c0c6944810000941d11030b01d03642c4030100300004034850310752084480e0448240700c506243c1002e05540e0703c09400300904 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 300407212 1250 300405962 300405971
    0xa0807080705070306020d05100501050c070e0603101107030909020412030c031e0e01020c090702150c0f1920060c0706020408151e070c02120c100806030705030609060703 75
    0x1440b00511104026503400b03401550341c2c01441c3c0400001d003101340e84000c24200d088000244a41c042c3c2d08840395501460003815010349083d01100b50601c004100d240c250140540d13014400c43d03103105290f44002140c8040740c40b5841800d008024440c80e4100c140c0161041205000c448458000c0c1c030003003941890001460407291a04640501d81c52580b003030984809020b00d100180c03c03484130f4140c1c01e000c0c1d0840d00c0c9801b00404210001c0d00c00d03900480580c222503030302644079103104401c0d540140c2d1010107610708102e9920965059001d604c0c0d0765007a541d1103001091950b40b0507015601e0000048500180d4000044400c0d04c038100071701684800c01000a60904104a54040e2802411807900f920b92446043d081c0c41d414460888211465400120245200c8008100c40d00d000315542c1d07861610206144d401e100f80d09002c04d500004a01c036280e503410b0700d42e90f02c0400c0180344a456a0303288140c00c000e400d0510b4400e01d500a10721a0b00604200b09404a0020b1f6159204605240108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 300408462 1250 300407212 300407227
    0x80103030207050d240f0f0209060301051203070c0e060901080a020a06080a200d0b0108130b07030f020316030605010c080906030a02040e04240605030d031505030a05100506030a080708 81
    0x85018a40ca08042904402c0704400c1048217440e512280510703d840320300f4084003030b080e0300c080c0c220b1141800150f841b51080c001031050f4101340c2c2545284a84510440c0d10f81003182c0c840304490041544414140386103402040200d0500c0fa18190041104000400c070604c0700d58005a5a400c40d801004c08100314000059000761094022007803c45000015582035010710200050641c131044140007890f007440c440c544594800c1045a01c10100b8400c41c01715442581d854100390314020b0300350b008043c0c0350070213603409245510003140219800100c0805819608130058152205a4405418400d40c048071074089200c10003103e00f1031808482e883e603a40d403400d00042c000e0086070403580c450200c1c803080004000c2c40c003000321001003940c10f04a2604584150b0342050354424000c0680582228102d01c820600075080707406040070300e140c3c0c40d41168941e00031078581003005070166150340c09107103007a060340c0340ea10805400c42002d0340a0030f1f9040a54599100a101c0c211005003049800240340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 300409712 1250 300408462 300408473
    0x91d100c03020d0c03090210051608030408070b070f14040605040513150b0d060b0a050f03090a12020a140105070c02011b020a0603090209060d0302100222061e080103030207050d 78
    0x100c65400d50f1500c00c201c440c181840080044c000ba110490156203046002c02c861400b139416075406d8a8034001c2c8401c040e404d990380740c002d80c1000d00111400700d01440507100240c035001c400c0f03104655594800c05503c4c80c1400c010a140c04d00f0214041404003000700344201907110040b103099a10a480058881c00c4e8101080e004115070f641c1c0c0c601000300c41c940030a40501200081021660381042401032039100d800240d100e100710035628000c9807003045100a64001c0c2d4020b9503014861000341c9420031000d4a9140d0030446290a25005070040c8810400300007104906851030540c50000f04402d1411101c091b00d0164083c0c0041d05000184007070592103c0307540d6200704101d40c094a005042940c40b070015010f4a003400049214444240016100d420502c42016120f030b010b50045c1114290b4601c0d20000394452000b40b404034644145032000180407000e000002d1800d0764450349090f5901c0c8080114182107401002046a9400100003107940060502e0030790f40101d50300700c0000c0701c503c0c0c507 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 300410962 1250 300409712 300409717
    0xc010c050a0b090102032d150111010c08090d090e010e0405030f0f19031401091a06040308090901080d020a06020a050415030605031b0a1202010c081201091d100c0302 73
    0x103190350401c000700702a0312010340203580200c84900c40b002030016013000c0724010b2407145200380795101f00140024406010f440e0081d11081046c101076080095840c40c860079240300f50344800104802c0814000e84c02001c100500c882c003200d241080083c4e040203980c22540320180314420449107100081002e010062045520781c02a0164030343e0343d001c07000840c1d94250005800c040c541c030610024507041d54041d001d40001c10000d01c07103000b4070342e0a0101c0c22004100080f041002e281e441110640503466640c000c20113540107440c025298034050003003240c01c280580002c0400e40245a44420072078002a40b4008070742e002d400503132242e100c3d8008a60b1401183e01a0010540e19018803504e590198800d00030f44006505076a5145c0002c41c00c0c1e0411748201c1d5486400942c815020403051107118080c4200c0e0344141b5084000c00340c01d844001702900300520940201e40e81c03000402800e151440b44a85260102c0130560b82e12103281080e588821500014141071034540989408840c400e504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 300412212 1250 300410962 300410983
    0xf05010c170c1c083301080a0f0f09020a051f0302090613030b1806070e010507050a060212100501030612110a051309140c03030405010f0201140415140403020c010c05 73
    0xba00f420101601c40c1c0140740d038a041e00c41064992a80516500b8000d420b50300052400b021020f08039190010001140c69031001401c43c410242c0c2e400d10880c05030301d20b001d01d90320914175002c08a40360781e1a004000072156264050f510400c2c5103518600c90702404050032803001c0c8a03040c010f84441580f80400e500d442150407541d603488032004040200a030080c585c600a0702c52075203441140c9a20720110b035681c2c1040d02c04001041c105180c549807580708100504d01c4074031800c1940d0059015a1300c0304140d0700641464403100d401441001102c036804d03030042c0003d002c02d02e41444a0f9192617200c4861140e100d1000c0c254070000d2603194031320340b160860390300100f0001d0f001c2000d4804520760360f0010030901070225441e4400c002c00011600c00016032851156004001c2c6151a1601e001900c0000d861054141136540b00e50075414901501000d803072046003d141c103203000c81c0e208080381c3d0444d1810111024240610f4080c000030940c006280c155500f400c0c02c0c0309035403c50a080c09480c0ca0304000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 300413462 1250 300412212 300412243
    0xd02030a1502091804030f08071e090b0d1d0703110f061209030d060504110a08040311010c0e09092410271d06041e0206070b010f05010c170c 62
    0xc4c4540b4079010140524440c038080c1d070301c5520140d114503007202c690310b064480f86d00041e48034000164500c07019141c148000030900f400c1001c0c40d5901d80502c440c0e084403000e06010b81d5180307030643c1030a0404550f882030008000c00b82c078200341980c0c0c0300000c0c041030344078490298036182c00a42040c0c8416007240d90854000051158915040700c1807503a030380c0144c13000740c4c00e5410084009043e05007402001d00002c1c00c0d0019508080c1d510208840040000304185c0401c201c1724507125226100707207e01c881c03240c4140d50b04501400d82c1c0d403d2109030b28018040440c6944505110305881c001007004e081e1074001050b00c0ca040e6200c0d11801450a4184c2c0c000d440821842c8040d941e120a0550744107045c1c40703154005204007812103030344e45030f08410600041e24580140002400103003c02c0c1d0915901001242d2802d180209500818015040030600302c42c03a400d80001070048199802d40c4c1b0000b4182480e00e246001c0950381c42c0030111504a04004409a02245030310b140309080c0312907070007551501d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 300414712 1250 300413462 300413479
    0xd09050115050103061502061933060f0816030e030a03140901020c1b03150705030f010807081e070b031e0603030310060c111e03010b0d02030a150209 66
    0x3810100d2615490310602c1d022920701140052104050300060580d03124603000343c10307283ea0300c01800460030411091031605030f40ea4602240d003ca0800f00a0344079840740340d03030848131035450418118025513035000f000c148032840030810181e83e44260105c0e80440310007010105415200800e8025040b8a10100c425000220b03140d2281036069102c03030038001c480c1e200481c03a0303201c2640d02803c0b03103c4c0702403640d1907400501d800204a80d18111000103c14046c040f03810300c1e564550088140d0000395084800104000305014441d03090858443c05020700c1340c0030348a00780c03402040c00e503102c40b81c81c8a944550030703010140491901c188480d4000b401c0c1300d204a0761f03a140223010091900c41c1302c002040000f0460f030200e041c2c2e0800100307482c450010f50085000303c90034030105036485100008105c94681004404580e20785030b450800007800b00f102029100d00c02020101400e450001c6403982c000c00490008402595000130740c02c101d981c01c00c01990014200c0c50b0b110300a449011442c0350002880b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 300415962 1250 300414712 300414731
    0x8060402031b1c18020102071212050c0a080d022d04051210021303021507031709011d010c110c060301030305030712180b0f09060c0306130f0506010215010f0b0d090501 74
    0x1340b02d81911014800d80c01e0b81c29003034607002c000c1c0107001c1140e0302502102603e0207490480740580e0090400d002d6140c101d0f212030442d9a40d0300c03101d6000800302c6c4080c540104903215004500c9404c1403502d0341c4840c42d03e103c131011100545141c040c07481524816181001402c0c01604188420300b84504458030a665405803d031040401c5540c41c03000f00d0040c454040610394405555054a10341c980c90340d140420380030581601e0360f03074100c040d2030942030395a590000314484510f8440c80c41c2440741040046031030030328150040c0140c0254048910f05400c051042c000d2665100c080f00d064a5150805503229140d0b91401c58111618580f450140380c68048030010100340086100103030782c451440340040c0d03502e2080300c1050040580e217941803540200c001c101c2c4601a00c01071a4070450141100243c00080901c8005480d0054005894079903200203002807940d042c008036000d039085240140300755260440c0781519180c140301da2480c1c640c001ca484681a222500300d80e0301d40703402c50001c0c030000c40c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 300417212 1250 300415962 300415991
    0x10306030c080c0901080d020606010f030608010507030902030705010f05090409061803170c0427020f040b071e0f1106090d05060a0b0102070b0904050c04030f0804030308060402031b1c 81
    0x200d0700f51007038038060700001d26000001400000c1d11000c0d400380c0440c0c0c0781c2c803005484003480569407409054880501141500c024171646100308031950340800d401180740103060400f911908000d04001a03081410f103901d801030125007469000f40c40c00500d0303040c1c50900720000d0054850284d24140c01204401c00e2550140d002061110310340020102901c1d05c0f84d42c020144180c3c4504c1154080f19408402c16202d00c1c07810b0541000a03080142c81e00b40040c4510f460b40e88950401812505d002c600c180501c02428881c40d8046016161800c4025460311080180074044c0c0004200346001000a941a00c0e04010b0fa41c0010340074214030300085483c5411510343c90121a030901c528030b41124190203610002d46481100d07a044400ba203801d68400c1030002410f00182011140c1904100002c000780ca11224a0301d090702680010380c4482c194500105520b902811191107540144240103044031107540103018404d010b180c06a40300c03030805061002d480d140704a41300c514900003d503002d20b607 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 300418462 1250 300417212 300417223
    0xa081207150b090105220e0f060a0501060816020a020414010302010e01020a080d11040302060c070e10350a03021605040207080405010305180d05040e0c0c060f06010306030c08 77
    0x24030500c40c49603182045030072001100c00403a0060740c410b00550041260b0705082c002c442c280e00c12841e0340c61038800c9607a008819101e2590700001c0039131210402038143d560a100280c0c019640140510243d49000e10040803004087c04c80f80b180b09442080b0350000780200064041d19601400a101e500202c44030390303258401c01d00c016400b240140b0019615984045030307103031920342c0c402c1041c0d060580c443d0412008214101006520910402c00440075984000143c444400c070680208181420448050300043c030250484d081004819024095001c03912524850400800140e111600112189400d01e21411445004034020f2002580034103902140c031400c05151012252a0340e6036420a01089100c4c40b140a04003000c1480107104a41c4a5040300d90011080c1030585240c8280c18441802c0410200d00c0134081000002c00300a145004102c465128015541d5036080c2080d1807880b544401004141060b400c0404000444580c0240d0141001c0d43d000510a403400e0380b510031b1a661030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 300419712 1250 300418462 300418477
    0x40e071a0904050606070f03050c121209010c050c0325060f0504050d020c0901030b0c1201060302130518041b0f060201020417060105010c080a0c0605090109030905040b1503060a0812 80
    0x158103100000c4c3e2030b402c01804a40c2c1c8164080050158103c0c5900d00f1034032500203040300f02c01400f500716551901c0c40c0240c0900b0552040303c224005e2030802850a60031030300c090f19014188002482020fa1241000c81a642d103c001d0420400d206000c191020601c60a02240141120b1800644014034601544044c0c81603114208440019450344003ea82d145c0b034000409501c805540014000210b880b1003654011604104c16818944103a000200c03080d0240c10003c0066404910001d81c80180240d0b00c005007000e0301e06054034921407490011080c0018401f0300b0841c0141060031b00d0310300000640b402410307520000c2459544030a03000b4040d5006105810b01c0c205e44400ca60b84052001c14074504846050b10341c194041707a84c0d502c001481d00b02c1801c0000f0710200002c2400400c0d907a0280c02d100b4500380000155a801e01c0c54040c180c00e885400c20384c065482e01010755043d850b40920046025000400380d81c42743d8a11002844090303040e000703c1c01d140129008d41c0448501e400281810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 300420962 1250 300419712 300419719
    0x60f100e0a0c09090204181109031c080610120e0f010f020903010b04111209101b18030c17120a0e09090a0f0204020a020109020a0b04050102151302040e071a09 70
    0xc655540c0c1381001680154000c1da000010200000e64260300075620045c10302c98090f4010b82003002c1c2000007810b2030394842c1c200c0d0703035040401c4503e44201d43c009002544404212030310480740e01c0140d03004285420310300065010980d21011040e0f680c4080110843d20320008009011822195180c00d01941100b60818000d43c01c01c220b66003a440c1c0390251840800407004801d04140e03140ba0340e07001310b003409045584d142c061990700c01544d40c0d00f80900c2c1c0d100e80301e4510107121011030700e01c02810386c2d45156034a0342c0e040f0020014000580f00b1034a100c1103640102e140401d042c49030320268240100203000c0140a200010f083e201203803c10f80c2c95807400380442d1032002c642d87c1c6522990b2a60061900106000c2048000c0d0700141361030303805810344500520000407110281c1d4041641401e094000c000c0f0400045000c011640e410040c0c0000300b1003014644806007030100643d461000896030091165880301c48400510300704000c40001064100501114148074542010301c96004a019a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 300422212 1250 300420962 300420977
    0xd0b0a03030f090b0c0a0b07090308030a0c0905010c02031515030a0b0105030f030f0304031817010b040c02160b0a1707260402010c0609060608100e0606040e060f100e0a0c 75
    0x40f0300a609094840300501e070f07001b0b844c0140300c07546c800084d003500500540511201303120120208402030061441049400000181a510610084e020004990040b0304028840b094000181c034040fa280b10a0a50110b405010f83c8548500c00d850610303003003c4c16003521814004105118410414074101c03501a4107031a140540443c1d510744030302c5080703003940f0144420000f08000a20035034095811039144148861101c1d182c0c1e0304043e2102c40410501d4250307442c0c0c103000034580303410702c24030481202c54002440d601d148061900b048000e2486060b103100310100340340c804540640c40b20021a01e40807c950107900d080d400141061150621820311107042c84020b207803d00d081c1c15000d0280c1c1e0144c41e07452040d011681c8034006403914040440d41c06440750f100181c404c0d0104001c8951000070342d00810b405030003181c82490880014210380c8a1410001c1110b000440451a0b5801140c904401c440341d40d520810320015a4151f8402c806600c6020308003e4080942d034800b03101960030303684503407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 300423462 1250 300422212 300422219
    0xd030911010f020312060f10030c08250e030a0615030b0c070c0504180b0108030403110405010f060f27090c090602030d020d1b091e030f02060d0b0a03030f09 69
    0x1184008800710302d0015070320812480c012030008806942d40140010940d007a9800b050010802d0484c440b00c002001c661560f0905299070340150b10300794000c454a0313983c44581008900d041c910312429071100d06100d40e205003d00c0c140c401f17100c0300305d801c0e0b0050428403408035501c2122144607490300c803d0f40c003180751001181010048808440446420a034145046402c0c1720030800101000300030311500c0c1c1400d00c0c0d44000900071701703078060003406200301035a103880c41e44c105040c0d001021000d240c0300d03528240c0103101e0340c2d07e0100000141c401526010099400b040c4068844070201c00c0780ba40600030880c000802024001404000d844012505028413683d1950a903800d518500074103000da00180914106020554040c2000c3d001d44400800d4004001c050080740210709508040082c503280c20611800010030ba500010340c001d0320101d0016440c43d1a203046550284100034401c0c000080c0e50205016160005c1802090080001803202d5903494050441c2d596003c4080c0030445d11031001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 300424712 1250 300423462 300423467
    0x100c170405090a15050108060d020916110712030e0616230102090a0501050c01060e010b04050a050d050a03180902180a0f0305191e080c0105060a1212020f0d03091101 73
    0xc1c0203656401c4400c0740c1314280401940c224400405154018200440231070250b40d648440c50300848101d002c9014440d4281c42c002c06140504030f001e003481d81f00c0032003000ba0b5855000d401d41a00d425242200c0d58002c41d000045040c811243d07610000d100d40d040040a025412080074910b6003606110001c0783c070742c8481d09091f030103880050b9030302801d40882001954052030050481d4100300000280d00b0b62905401c81c0d100d6420f070000d0741840c034049401d11140c2801500700c0b025120407181d0004850307030707940c80344d64842d441d910040c20040c114080c02c0d82c50040340b4070b041c00391004020540d21001041040f10200d4032300b846d05442090308140024840703400400380300c180d9800c50090902c200f00c443d484003840030a19412140c00303001c0e200340644001580002d4401503c41c446255943c400d55051900303543e8050200c134882c0824070301c01c00031004c2d007a8034040084da0240360b418204003240350903810201d4581040009020b1040745590fa268917520007140c041c410080d4481498254004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 300425962 1250 300424712 300424721
    0x28030c0905031509122d0403150207030905040c03020711041109010302070f020d030819060b09130e161e08060718081903110615100c170405090a 64
    0x4040c0c064103d5101d226804425110781507020b440e1070100d4051440d550b84905241c1e110101000305032a480c14083c00041158000c1d50302d5009011801741454156142c201c84000b000c0c0c2400b440c584d0019420b010076004045401c02401c1c01001044481c01c052030140c06544003910460f0b000c1d09190312809140f4042c4604202c645450b01020306041680c03005400940c4111b00544120f0900c4243d800145d9a01030807160f920321a5a4403010741c1000080a0003d050207043c400010341004d80034030629031030a054a140c10001c850052411421343e0141d402001c420540c906180601014000c1c40712182c1042070803251402454a601000800520f0800d5903901480d41d1031380056000c505002d01c200d08003004c1e203080d00d61010000790745031022803030104000c201003222525520f0000a2640000801c0c40d10174610300a042c10b45411040d00c1a5002c88200d00351140f058140c40c0c0640e580309a403021084da134840441c61342c4040305010200590811301c51b03503104034800c00004034689080c3c00fa = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 300427212 1250 300425962 300425969
    0x6030b04060e060f010c050115030b0c032505130e1605030903040b0903070e0f060a060f0819180c05190f0e060d0807141603050601090e0328030c09 65
    0x781980d50f8654804000c0040c0c1190091030401c105403c0d00d0011a0b02807092501092050100da60305525614040c0f40d840c00081514002c150240108840d0812805a010020300030092a100d00804060141c4240c01001c3d440c00300c0b28400600843d0100e101e900301c0c0d004200081e00d044641c0c50203032049465100480e035a28103508184420481092240f02600030000d000b0250b41e5800c0e1a03080785102d940c800c465900c00205c0820a209131400c1410200c40500810b03e0702c41030b40303840c03071b8006010804040d1001490818008000c10282041d900c1009805400c4805140394513031410141e44079052405402c0c8645400b80b480700368100340240c0e20040b9071114138035451451400000700c00d9201d0080020b81c028182e408450001084003004101641c810680c0d0107080c0c11f046d04243c0340031907051041425102d03203102840070440000f56a03046401d200700204071400700ca03103c9820b502402c82c1654001d20302c1d1910f0814030030f00500c2c040e403140b6190b82c100007018480c41c1c02c55907046e6511 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 300428462 1250 300427212 300427229
    0xc0818100c03090f03031514091609050307030804171501060e0301020405180f0f0c0d050901090206040b07140a0f0f03030b120a0b0c07030e100c06050f0106030b0406 73
    0x303040420600d250703008007100c003a4034140001c0b4280341e0307240d0000e030710801401200020350311500c078101d180d4100e42c294042e2800030f022980b890255404503010100240c8295960038820840040991044081401400c409026901100e5032858020550342081c051009a603480030b00e903100316880010701050512008407100c070964078242c0141c1c2c03402d921600894055400f000042003949231700c00360480d00841340032401124a458440710004007006400c607128040050140701e1001c403528241e5501c54000700002810b0740b40d0500c44c3e4010600c1c0d81c0020740203140428001154142003003d40f00741d9000c1d040781c0e0096500c0e200c2494442201e020001c01c10300d0f00650341c2c03010640404030030761014030a08001030b80000340800100f00301800000608503a00c511491740410004140450304501c00c040d06074100b401580c0c018200b20401c40106016055425203244281d20403504101c40540144042041c0d003032501450f12995001d00510020a00b00f80b4506042c1c18140b14410440f180d11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 300429712 1250 300428462 300428473
    0xb27090415020f1b0f0d0203030705090d0c15110c0108041211010e010c02070807030213090819050307080106020607080406050702030903030c070510050408060a0908120a0c0818 78
    0xa81c1c85a00452214031442800c1da424001114414240402000010384a502c04090302105001440c504107603081d2001c1c1176040702d900007800319000800e8035085002424599103854500000c1181000743c0701015011032036800000a001d0254040d47d1034048003640c55140380751010300c00b0350b90365140b82e60442c00108d000d0001000b00e000c1104c5941d000900745001d03480700407280d9946003503403c2c10702d02c0f909a03591444001c0210780c04000d03e40040c00804007824600d85103400050816144400000807075071103800b0841040002c00841d041e8400f0301d01046a21948624004c199030802c45041c0b000c0f4040200200700d1600000d940352259000b5510446a17035155965103014081c09060351040d0303c000d0080220700c2c3d07030601c0039100c01142c290003021540c0c500b00c2040000311000085500b80318041106101200303010400c5a4050130700382020401002c2031178855034504c500c0841c001c22070800000c1c8040e15041d50030040c100b51742c0e941c0d80c01207a03c07801440c00314450760074021003072503028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 300430962 1250 300429712 300429721
    0x90303130f02010c0609230c0a0320030d090e180c0d02030f07030308150105030405070e091219081503071a07061d06010603181b0504060b2709 63
    0x101c14000e001d0381c81031404d05a142900d5a0303860944258410132203680010052010908034501d001c41c100c070703140c20002d01080d80640045001180b076804040d04074082e18900d03101c078580421350140404006001c40e0101c00300040000d00341112070081d8001380841d000802c1c0c00e250300141501c07540c0309020217090502ca0600c01c000750351151000c1260035004d82006d80c1c0800009004120055000c1d4139841401d19244550030884403201501506000781402400045000000c409082d204001140398464444da101d0794604801c01d1001202440d00080202880e41414200c404090b103c5e29914003e44404900000c10f0050701c500070b4060b07004000c20809580d03215000c201461881c40968904403154980500303a03855000e15000074566401c0c46c040c158010404c01d030042241e032500300800e01840c404800300f000c01850141c02100048202e070101d610182c05440100001070040003010f640b217074807030120f400000342402150b05070a56a10030590350201c0182109008010300d109654 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 300432212 1250 300430962 300430973
    0x304260301120c270b0306040b06010f0311030a0209040b0114090f0105040321110304080703110616110f0409020a0504020307020a06050103060605090c0c0d03021b010504060507030509030313 84
    0xb96640c0c141c2e0301d0302650500048004980f08200c2d040380c07541010b410080c2d04109041c0560381417a80d580d0103503000204010105084041081c0c1255091806601240d42428120081c1000b902c003113400c07110000c07d02080c0b040703e42c01059142404d40b0207005030384da2440151481c0505401c3d04105004c04c00624030f6501d4a240d40d80170100050521608103a1030f030300d0703074401095008100d00784400410070300318101350400c2c60000702547c0c03540114541414500c0f682c0e01c0700d4030380c8002000e030f0310241c1d0484482d0f0340e85025241c0846c246190403410302c4d05c42c140462035004400445000d10800009042e03d81414003940d03980a401400403500c2e03a241109020007035000a001c1d00c11400f030004008002005801458002c2d03001d41004039245041100b0080b505030050849840341170204032400c02e002c00860032015100c210b040060b111750f1500c43c0c0054400403801c0404c002e510381800c200820120354445c5001e156a543e00300003681d40c68168903075911060b581400200034283c401c0340000c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 300433462 1250 300432212 300432239
    0x1020709180b0f0109051317070303141627120309051e0301062c070516030809070803040612050a060306020a020a05010e03210603010908040b0304260301 68
    0x74040400003151842d44500400322030a903a51200240039070300401c00b851030707401500d4101d210101080c603517041950342d1510200449808812000c0c011680209041c040d5203c1c201048102035802401e160aa20030401214195924800b250b0319403100c490280019100d031880d240c0d1405154031007030800b000c00b03070180c0009008074200030442c0c501160644420f13101d04404415041500c000090361400c040c2501c0840d0484526012250038419800403000450040703e00150740b1090192110701c03007224107105550f00d00141c0000307107052004042d8000030091040b83d01905441d0400d03100c98859440b840fa500c50b00e40086c03401c030180c0d00f01e030740782d03603c1117411020300d01700020001d43ea039031101c05a0704203141007070168000300a90340070f005080c01040c040c0840313200614500317022100d515030392020985203400c4d00b010307440000d01c050b1825402142641d410080701030301c2c0c59888003490a5039200321412101c0f100f00c403400c03410141c0380d8420540c607060020442402c40c0e090080400c03441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 300434712 1250 300433462 300433481
    0xf05010804050c10051206010c1e02120f150c0306181504090804051908060a020703020c030703111302030906130f0b0a0203060406052e02030d05070c1202060601020709 74
    0x3d0161a07001003140d034484801960300b05041c0c44154840112440d4002d102c8070040815040c00b020001000000e9001c60b01d25a14410320740c44003054028500108801203c02020b440c0030340700304e03504200715050001e80298000110b00b10081a0341c1c6440301c4182500041da5815004051078100700e8a0241a211560344a0040003030b03042c0303035008040001c0030390398400c13800c0d600000001014445414000039200000c800c0280b1082040d1428074030660712074008119028450717001c910001014030074804131640d020018112002e2030303240c0c1800d09800010380c914a114460001480009003110700030313244180070a001600e0160313030f50556015a448192002c42e4800e04000200d80015051440c0c2c034001c0d03c07141801a04c034540102800f0440d40300e0303041039115241c0c01d01880e03008401d0151a5801c4c2aa80088070140c1681382030507895401451401240b050410040041c176035030040000181500070148a0200c0e180e03080700f0384e10f64030261140350041e0407008052019084d56082289070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 300435962 1250 300434712 300434723
    0x3020f0105220e0708070c0f11030307081201060e0306040309031e0605070306050f060f0d112502130605010c0f080c2d060601050301060e150301090e010c08010f05010804 75
    0x341510800c0380c214a0545802030502c080c3d62605010302d07294040505a8010110b043c012003058075a11078a07100744032070b0002006405203000c1540b0360385040c41a01e003020307444203109071203280c01034050390310398000d0041d00005511112080030b10b00d1f0004502e07000e02d4241e110581d1ba14190707204d012046942c0b020040c1c40c907400f40400d07030008800c0e114040c410304183d60b0004403030381010104000001c020307003910304c0342000703110800b0140135440440d10a850100c0c0000b07150044143d0b520706034020038201c0e05e03181000d5100c8080c1c107140f81c2d0710355040364402c85041d10344c1d020340b21043e41115421300405001800e009076900c00510142e0b0100d004074003900d0080d0800425020702031a104003042050764010308a810b0070320208003410b1019101082c0c1c00504950f00e01440028408c0c00140326041c00c218071021840c05c1602e030303004a1210307041003440c020385d0307580c450030040c014000084c0034203030544c0707001c3c00c2c6025184280724203810388151801e24420140381100440308a60301401c159038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 300437212 1250 300435962 300435997
    0x22060507080c150406020306030618070b0c0f070e19090c03020616050615011815080a06030510141501120911030703050c120c0108060111011803050d1503020f0105 72
    0x508401ca0101c55116505c25400940d0b00d2904c00700341130603c48090040c9025038045c841030740b0140c0300811002c0c2502c21200000d0345400c4140f950b24504020424481a5801100340100703840e0201c0020034445c60040c03055180000d2812145012210003044c090301c8060007500500c014600030300241482d500f606c4490840c404a0744440d410003000352401040b11400390003d803150350300b00002480c01d441c0110500d0009281903103a4010b06040e0594000308100d440004a00700000e501c188085c5030080b04036512009a405074a0062486aa400c00c1000d9000001415049203c000b249070000c1130b0340b6400011303107100c9104080c0000001c104d50a1300c256412a280791810804280150b000d00c004047d1460040244a03281e005400400310a03000707050702c00e2583e42c0090205801140c2841e11995640454080a00404010025600501c100041c140034594004050240d80142d6802084601d00030f41007052010191f204c001c0d004641d601455500d98001e50141c00f001010608100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 300438462 1250 300437212 300437233
    0x16050c01090b160201110313020d03200102030a0506030309010f14120a0203060111071a030c250516030f110f030706030905060604090809041104150522060507080c 72
    0x1040882c04560300d0300401c40c9220782241459090007014100c40c0700808891950400c2260310f00507070aa000068003840d49041007608062060300020000d020790115007581c0c1102c422a24040d50090303407414801c5040c280810440e24021044030f00e144016129030b47c136003050b00c81c20795000c9070b80c41002d26000424080c2401e011031000405200e032070001d20040c0d89290440000d410b0b6605040300b88a01e5000071010b108503c01030008050002c0490341c810388030381d01d130700309104e4134414201340030940803000b0680c40c004e80700c81241e095024418800d46084e0204002d02c991801840d100203404604103040403008600040015270380410050a14101d151010010924100b150b074030040001c0d03911101d07142405018003480b0740200702154140704010b85610360034060301840c80d01c3d610850b5913581c10a04101c21900700c5005200b4900c92144160312607a0281c00364014458004080d01c0e00e2681402040e0703c00109400c1d51250740b03034142403d441d52074450b01030f045204c2d800005d12408084a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 300439712 1250 300438462 300438473
    0x21e060708070e1504080d050304081e0714060f071e050d020c0106060c03121103070806040b09070207090e120318030903030d1a0306060120070b0c1501060816050c0109 74
    0x40d141041210308117582c0c030724140a1a16000201500804003d0140709001c0041c440104a45a1446c0d148458020303810070580312643e80700f9002c0040001c001c000c03159255020200c0d40d07600c00c0030008440c0c0400d640b0300500380c0c2c0309614416404941e9190180d00120a40103001070002600519801400e120b5100c50301821500070303800190110b410a1500020113920006000812905000038000000744005162082c0070280c038200601c15120001011601c4590101074451001400c551282c10310140294851025018010550341045810899140b0000383c2486602e212010740e803855071a40d0300c02607854600e10318649280402c11a585956400b00090140c405a1410001d6100c0b21384243c01c01c69414400c280780680c20840411109a0700071848c0c14400d08190340144424602100d0141003400307070b0704221030030f00b00031a070456080000141c40c6031134000702c07070b01c2e01469807140419200003a04403181c1800800006800303260601c50000350000c004000f00108007411540d0300c5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 300440962 1250 300439712 300439729
    0xc01090909052a0306010801020a050702010807030e0703060203190b0306010e0402060f040603061526060d02030609030d0c0c0503030601050d06080a14070b04030c0e04031e02030a021e060708070e 86
    0x9452408400003d4081980b80a200c2d5500624010000f14074012140308041c002e8002c0800c0a03060018200014130854041e411100e00c200180f81681d41d0151a8039041000b90020303660b0050a50514803550800074486c468400c01d20401401020700c0e0b03207002c4200718031820085c001c9802003c18451040303031040d507801034809007049890214105040850440a02c080e1582c61010030075000718810500c09103010030f030005100f503200303c0c0f600c1c0d94280108901e012002802901841510100040303010b010014201100c07040c20306005045460303d084030300009141014000e90007c201050705907014034002c1400200111000c23034260303a1000000d017402c400030405e40364803072000d049000030441403280b8400362190203506800e01d82142c0391071654032503501440c0203079900c0002040c14580604400049801c02ca03890310006144544000c2d240d030850315041001d0b125210500c880001c0442101240440410081449590b0035208030b9480e1800b0300540c0901c07045035540308551300d45200c07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 300442212 1250 300440962 300441013
    0x20f19020f16062c0103090303201804020301061409010e040504030804030305370e0a0320010c120506040615020a0b0108010908040e091609060302120c0109090905 72
    0x181c0030340042c9003540144c41000102040481c24540b591a00c280c01032000b0f01c1c00426000f8680015060702c24034083e4004d1049001100c0018400140c8006114005d0010301b000d0340075a008846c0070280740b007488280d01081c0198804190402480d42106000c1c0026211300384052400400001c501da0116046400564040d000245d4040c104810f050300350084540201c400c3e07403010701e40b4441a40d803544100221002051140c8010f03600908002e07903800088040d500c80080e156030215500d0080c0103004c08070b2201d1190031500d0320040c4003a00601c03544006081c0c0e515150703140d40c00304440e80010300004100c40c0d8802e940301c402240e0f0b50100303404444100200d4000345500710040c200001100c40580c80b1440583c14802e407000000c24000640c0c04a41c000c00c010704a03503d583d10540d04012000d41d0841850102000c001250b01d103a41102d07040300d000780c484d2804001c03c1495603450702400018503002c54815201040784119680c4582000c900904c00d0318800003666450a114030940f07078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 300443462 1250 300442212 300442243
    0x7060501090504110f0a05060a0c06021914040501020d0c020d0609060c09080a0f0212032203030e031627090506010f0b03010f0905060409240f020f19020f 68
    0xf00030400040e01681d0014000813500c01c0c046201c40c10004034a40b64a0080a0080c0e00c041101c0b070446001e4540c2184066200c642507480b500747c1c0340540c1d0304903500c1e807410340040c3c03411180e5003040c88a1002c0741c080d508182d0250a50800e04141a290820701c41401c0341c12240c400e4003480408c10510403458ac1d10f105070008101003c6141d001803500c00e00b50002034040d00314500c1c02e030000b03592000c0311001d95030643c0c100d0882501d1401190070f5020b0300d02024015050017141c3c4030030480c0b000040081d01d2194480400c0580b100040c180e640c682d008410f046041c2450f420f00c24640405464407490780248454400c1c9009024008240c41410408850a40c031480040c00f50000c00140300c40030301a8541d0144c2158500700d041a08017904c0c0c070030100d0319036469020440c945c403140c00c503c0c044ca030004030303420322000300d00c2030100311007404000c01d00c1d018600305440c002c60080d40201c038407454800c0a40e17800c180421032040f08040495140c0c00540c414501350703020f5840180002d94032000e111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 300444712 1250 300443462 300443471
    0x6150112020f1204020f0904080904050c0f0904110d09030504050f0904050a120c0c030506090106050a05060f0c070e1801050f131b090203010b0a03060b0f0306090c0706050109 77
    0x1000140c00e554004922014441c010720100c52040c15840542c2d5140c400001c2c9102251180d00110742400560b601d5641c00030f00c017a041105000c20320005140d08401520104030f26a01d1440c100302600807804d9510580d14108070b03100c02450641c214000c901c82c4480400e1a15502130300c00310460f1301c80300049001c5000071604020a2818a0322000300a100359400d400d6485e080c2d980036103030041c6a00040030396030082e28451209100b10107140a065210380840b44264480c03e18541d10383d03040b83da615096081c5100810142091060002200c4014091030300308114900001403940005a1000c5e03240300d101c000107a140c1501101902a1120f150940c0e100410102000d082d0303100209a1103000c4026410320100360580381b15003c80980040740a18800c140701d00d5010800516407191076414004400451041140c07402060315440355201044515a50b048482c5c0c14002c0c0c03240b082202d4030503c0090b00c282030000c1070507800141810128680741241d030318070049880c04c0c1c0140c081d095a4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 300445962 1250 300444712 300444751
    0x1509050315010b03131110030e010e0a020306181f0204060212090a03060507120c02010c0201060f03021305090f030f0a1b11010311071a150108010e2706 67
    0x500c2030311980c1c0c08016150746150f06007941d1520601c0094034a03060820f030040d45506200005e4144140984001d01030710485407140001009050606505400343d407074603d030941c0c0010002851840b065002e0003402c000d81d5410f000138020008070340711084a01410100018104c0c0c54007405a1181200c1801a2101e04140c0e0092801030614000000340f001002004a83d9980755100c4080725400480481c030383c0d07601c9001700c500b80035030000001750b141800d082461443d01074001c0040c21100f81c0c0208002070307444040003149200c5200c040e4100c0b10040f8820b2241f40550000d907030044004080b40e02c02d0410101261555008000044c42000041000d0184541c401c00c00500c05c895013002161a080985030a03040c40a960142c1d414540c1d1581d9041074051007a098031a5160071910000b620115038070b10005800d8115000c0007025441260241175600654074581a604074a42240d100c0c5c0c0ea40312620103040e004da42c10f04081c0f01171554065041002c00c85107208003c64140810386244 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 300447212 1250 300445962 300445969
    0x103050d11030f030c07021206040606080d0c03080c03070917070306061a19092102090a0203040308150a090204081b12030715061a03010e0609040c060810150905 71
    0x115241d034208203030410000ca6102d1083ca0702900c0d00100c01c000a180d030b400e61440003c0304010703000c81010141c002c01d0200000d20a07194403c1003202c0e44c440035100300d080c014034112004018140e0082c045403203240400c00240c15880690f40c0b0100c00d003480b0030a40c4e120607060b480d40000d00d40c003000340e0744030304818810450340d0701480005106289010329180300c0c03440801c00b180180d526480286202a01e45180f081c41640c149000f8010f600810340303103405940b80000c0321007000f24280d0082e244d140100e00f5110307070791003183c0c0300d40e0301540d03441c03c640c035011105c08210800200341a44408440070103c3d01d02c03070070300c0100000d240e940000c01c0d10035260512245a00c2806115500c0790f103110013419901d2030080200da056a901290340210482600b80c1c0e07100411158010700946140c4004030202c00803d1750045045e503c10101c100003075603803641002a001002c660080440c4030032101040850f014000f00d941000d100c10b1415901d685400444604040715401840000c0030342008008505 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 300448462 1250 300447212 300447227
    0x7050106080a030f0f0e09090c01030e150f090a120504062007090b030106090219090f08030f091c06051914180a0c080115080606010c12030e01050103050d 68
    0x40751030003812460041e0744000c4c000f80c03540c225020034015030745003459903a40300301443c005108006101c8a924105048c080790745040e00b2503100d01291a00013420702c001d100240254901c2d4006a14181e42d981c4c0742440c400140000d0002c0c3d141e8440c000300e00c000910a15090611550386503655a106c0349880e00c0181403840040784141c800d810916502c2c010b4a0201c0c40c042510111040801c1034903121001c02d005203426442942402e01c045036806004080130016480300d12180c2d0358041d91512000f8021218a90b482400c500354820000d4056605c1c600c4040d114445e4001d021341c020031801054443c10b84001c06048800e580c6d990704006040f0984205020040b010450420488030f412102d801502c201510035410b908100041807481401000070718038460344105070b60b40d80ca80d505c070720f1030113081c0d002d00c0c2d80301c042000d060100e0408400030300e1511503c016956689182c031291205806400300611040805840d44034611001100f4081c02e03000b0f500c200028880c02004010051282 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 300449712 1250 300448462 300448469
    0xa1208070614060d020f01090e010f0f080607170606070b040b09060a0e031e130306060f090e0c01030504020f0a1838221d01020f04090908070204090807050106 70
    0x516050910200f40c4030010b21400c84c590541d129400d84081c600140c2d55016181c2c4208032040040e00080340c8482d03200450400c59074a400e151100a888000c01a2103c008885481c0040c4040407010640303503100d10081d401030700240c5690703d0032080351203a5074010400c84040c1c807a00c554806000000408104940d401800031404001c441d02d400a207940768401c50410100381c0c0b190204c030308043c040300350071640903886070707140300340c5560303603440c0c21000f81505200788010300c0181c440024440c03000c2d00414808216032805810203d00260040d001418007802c00d03a0801c10641e5076108548401c5a80405000001cac00541c5031400b1204100c262022110402c640d1003480c8641c00c1000520452030700001645a41d03041c1c03502c2c89a021685e886950308a40c0d5503684640c0c400380d084001d80c0d1140318007076425200c4034010009810b00600741d00c81c070700e521800d080c020002088400110340c002c19040b44100355051911009400040c01c1c1c038030040c0203851010b00007400904104003481008008c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 300450962 1250 300449712 300449741
    0x20d11030a09050d02030c040e0610150801180906020d06031709030606010f1101021b0c01022b030b0307090209011107030c050f0d0501240927020a12080706 69
    0x14a0751403140240b498a541c89858011408104101c003155002c0c81009202100680204a19440405840d5840609813000c5040e0359980c4408038682c0796400588808220036100d050b090791070450280b1460300103040701c007651075546180301c4c00181540000d100a0441c41004103c1c01e0841c104550001080d150140c08000100070a4001d0f443c00310340c0301d90101d02401c000040150988050380c042220281250040d440011011000c02030315240710440b04903401115200c1d0104401680ea0783c2c0008192400002000c00717140d11100360992452a41010340380105040c000500460318101460b042104001c0d00030800d14045c1d41d00840014080045000500403145140c84941c2c003441036001d603c2c01181c0361409100c4540ba0b03501c240e002c00e90b000f0004c00c191120705401c03a0b0b07a860900f4500d00c00c4030b0241400580c41c100d41c0900081e120382c000013500802d40716820721400d20792411040340c01070680200047da50120a205140a80c01840007030307951345051030804100c03141581d8244a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 300452212 1250 300450962 300450967
    0x51b030102070f08130b161101032a171608100e060402071a0421020d02250803040803040f0906030320010605040603051f0e0307061e050403020d1103 66
    0x3c6040700a08014258108492a95a905500b00c005c1d00461a410000f503160340021100d203a003d0324049484202e00034540b0801c12209100110103840d034520400d41d4005070160110b08134440100c1030b0101c0c2899040120741e014091110036000c0c0d4013258217171003104c0502c00c1c2c03549213904030300e82c00d1388800c8400214110b20f05200380950a42c0e406403d007400b13254041000b01c20402c0f01506280180b1180c1d0100c43e140c0b400e450f00c0031410b2003c415200407181d4442042d040c050000070540c0d24614181c002c0c16070480c548400c4425420f141e5807074104030700080000102050180001d001510036031010303644e154181190f803107c0031050f138480564949071207020404280d000c80803c1c0042e03080782400b140003c044103040e01408458002c20b0b401464880d00100700140010052140c04400780b00d00140d69210f0502e20031181d01c3d003040e04654204010ad01e001510640c84074610280d0f20940d83c448510b440b9805045980072182100541c2c8554401c0222035007144006034900c0d4140d00561 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 300453462 1250 300452212 300452227
    0x120606022407030b061206191a090415080a0302060106050a0f0302030421030f0e01050408030106080406230f1f050409020a12030302040f0b0306011e020c030a051b030102 75
    0x780c690440318044207214001e0004a40024421303000302c0d800c560020140f036101c2c006840d44d0195203030141c1e6018440c00c01845004890070403250400c2c01c440c4c002d00340044281004c20210090f5005030310013541b10303942e03420300300c2c8000100036a074000d81107900007044c0f411b01c0c5150281c984601030b04a003080c400d05002040303000340c1c80a010300e00500b0625001d616a110ba00c0c04800c01220f1001c118090310100e071102040b694542c1c021640c02c42c5841c4d0501c04826159017030381c02c03103c09840140104004200620540380100d1070550002e10424000640100c504100109800c0310700703034411015408014414101107a20480da00402600d801ca0407440010481503135901152260a029a0b140e15101080d503540381041001000414869402e000491078014025030041c0030f4140085000140812481c1340030081d240b02d42d1f8180c5500d407400c160b15210584c0c11101050030030451140c80810440740c2c0f02401210012071041d4002c2041c0510601c072910511001100203000e0b0384107000d5034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 300454712 1250 300453462 300453493
    0x10060e031b030a050604030e010311070507051c08030f060405090d021c050d1a1c0b01050108040f0f0b0f15060d020c0c060f0901080c0f271012060602 66
    0x100c4000a55106080d41c071911500801d08000c60188040d0581c0205401c10003810381081081d105140d003607804000c1101d10b191002090701a07854040c0c080d42c404039041c091405c0482c1024680040000d4a80d501c403c1a520300301183d00840d0b035240c000499806000c1e581c28140207058200e141540541002c0b03000080c029035603c2c40d88400100d03807401d1510960703a14010801c07601050b40351902400120041800c41c541501d80c0700010b030040c1c204502d0312443d41d01d00244e8990300d03544030b4240c5000c0c0c0d2038031004540382100608107030b50b603400391030018000480c200c03500410944645280003052420800b5001c0103000140200241080700c05991455940c81c0203d403c10006060016220a202d0440e01e291100140300203801040c00582078403124810000b6000820090ba14100d071030713031200e580403158084d4400f0241410818810a03202c0c481084000c0c0601c118001440524100c110015401030743c628160004a40c0f41407003001d44e001c403401a000604000d000a040d1305076640b125 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 300455962 1250 300454712 300454723
    0xa1e051c020108280902091617060120060a0e0106080a0206030c0705071701050703060b0a121b030902040b0a05100f140a0f08071e120b090c0310060e03 67
    0x80c100300000f000140c104d160300d80d220101042c01c05400300208401e0901c040100806281039210f108200001000754620b52041c1c503402401d5a61461900a00301e082c191800d0080d04044c10721074006031801503140311f4517044224003003a0b0000c1080d4103200543c9012520381c4801c0d14180c4e4102041402800070000e03a032041140d0544c0c0c0cc5075a07582c2c4940d103003414000e15600516178000c40030300180598a00804021f440c252600801c59034903100c0c01034048903242e00c10a038940c00180802e640f5a40500c1100b02a108618000b050b03080502c0c80034800d00700380c0c501031000b09a81d8030a0382d040d07050500c550482080203641804205060900203581928240300c203c080001401064450f50b10501c4e880c00074025208105032106071241f005400c16180c140c2c0d600001d4000c00009400074451074032242d0200055545211704264843c046482c130707900d42c40020106403621507140b60b503158000d02d14411f085060031151a402c22440c0c64080c004a58021410880c859040c0703082d541d40807a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 300457212 1250 300455962 300456019
    0x17010c020d050703030e060c0703020d021c12021b1b1905060f16050307020f04050f0109020d1401030507050a1a121506030a050402101407060c0306050a1e05 69
    0x1002e03a158409440c046018051402c0180b581303024103414400400c1c2da00c00038000d603074442d4080d41c282c41081c600072650f540c40b0b402040ca500e5440a2000a154020700d001081c50300030340000362800384804021607401448040480890788190410103815010074418140c0c03031000c444004011410046020f070706101405200d10900002031300404461130b007012500101c1345c3d4441501c1030801d904059481703411003102a0300450507a000000645424411340c0e1040039551445003541c1d0800380124000d400c1080d0301d417000303a911a050110080c0d500300081c003c0d4442c0004220303c6003040300b84001c496451b40304e54104680220f02000c840623aa083e0380c42e507030740100e4480080d51446280402502c0108015801c5a8004103102c2c0c0304041390030042c841c9000781c1d002d241040fa03040007280c01624030848a000c051080c0680400107070b0130b41003550940c0302807501050340c039152400a45101001d030301101110781990050940d0403c1ca005580090a00301da0125203a607100030688500041c00b103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 300458462 1250 300457212 300457217
    0x90503070510080c0a170903130905010b0304060b0102030c07180c09061d010201090c060c050c01020609031611030601080601090f06050f04020715020c070609122105040302040f02030117010c020d 86
    0x594244114401c0001d514620300360106c031401750404121090310390380200c0d0040d010300b10140b00841d03940d0310750203841c6c100e841d050007403071441d40c854588000034904420482c1c114082044040300101d004c10900d00540710b0686040e14014070711050364101c900054246003400720341142002940e030030840400b5403812a401100b0094240c0b40101e0050040c060004d2900403511008940706502c00c1d04000320510075001c07141c65007100401a82c2c0d4100440700500030798420000018114001c212922125100341070201c00da0240d40006414080c02b600418040e80c03000004000c012054020613901c001c0c12082089400d0410010076107501c0d520344407500075900010794408000034490440380b0f601d0000c4e0215111034058a51035103c01705803007500c002440151011403941000305140244552090586c030301401d405074104401c0003411190010322006010002c0581c665015501d00540c40302c00041e0b6030742c10700b84031072100c00780d5000020142c0c0c901040f00d9171030f81e000125400400b800c0e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 300459712 1250 300458462 300458467
    0x120201050a12110c010b0306040c060c0f02030d03290612150a030c1703121501260708090a0507030b06041515030c050c03040905060d080a090503070510080c 69
    0x20010b0341c4100031200c000d030240d4030f8850009680c03030a1801504a01e64100024001b901c40c850416a4421060b20007501c08040407100b00620780c010b1408100443c4200f103158100c4680740c000909040786502c00a000c283c0700d021400180225490700280010740d440070220403035001303002c00c0c41030142101512400c03201c0b2001c120b4941140c00d0501c07500c1401412215656202d21300f141e0428824171071b21801100441d6511616031011054551413004188458056561524012650801d81e84030398103000c0c010901e0040d8070204001121000c102594443c018140810014000440104000d0311070708a17400900c005a008102c10003100c2d0054900511500c1360400034004114400740380d0000f49050900144031084220130b00e22034001c0e6102001240141c46007503405101e501819055078000f00710038010004294003541e00900050035440a03291159140e40b0f15600800f48040401c0c1c00711402c004038501084004050300d401d4a00100c1d04200c01c80140c0401d8010340f200b00d03030f513001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 300460962 1250 300459712 300459727
    0xc0f1602060403020306091501090618180804060504031101030c020316061b0210060509010f062102042301050a0906080c0708030f0a0b030307121209020306070e01020105060a12020105 81
    0x81c01d0698015540007015144107003420b12a141e6031b2622508115144225070000294010b801c0c402c01044854400c003410302111030000040081c02d0244401c503101c05c05521a2000c07039007201c068400390085450f0304d03581d5419414802050705015172194100350900034410040c5901006a4400c0005580703104109511403620b40d02a2030940850f050720011500085011503000500e83e21803030820f001040342d1a100c4c4107000d841c0a09018500d500720b180801040b00710300ca8040e8a0082c2d249080c01d808000b000e0916809981c065030001c402c5403158221049d0202c502103286100714000d0030000c1ca042ca045c0800b4024540502c5907074107101d83c900002d04045004811114456800769242c0c1d0380349080c0001e0b1040c030005a030211316981c50320041c0d030030508000080341c192541054003240c032480c03203107401c446203140c0f0078601200c691100e0700d581c0140c40030084c0a0151540341c0392500e02940743c40c002030840e00c00804c0e10b40f0645416000700103941509000503900c64080ca062550342d400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 300462212 1250 300460962 300460969
    0xa0501200708030a0e0f09060102151b07080403120c021c080c032d09010903080903010f060e0a110f18010c0503030403090303110105100e0a090b040f03080c0f1602 72
    0x90769407000800d400002a401034407980010321140401d03045400900080c010340038400d1020040340c985000d6440041c8840e8440321b078810740341e48190640340d55042c1440c4461301e4101c64100b0b00086800304008203061080010b0074020340204205072a03d0299810700d5000900400c5681c1c448071040c103000743c0c04005110b0303000c048503480307011881107a96500601c4d080d64003015860f4080d0071849218520418a0541282150042001651104d1150303086071034201d072644c00f4882459241d941d601034644280c0d128010349004166070040c1c440740745400d00c8110b081da42c240d40207031448901005076800b05901c1c18140d400c00c13600040892400622240141c0e140c200c401d07030240c070318030000c002c00c230805900940780e60640703100360780c0e03640308103880e280e028241c81d41030301c0114036036200600611191005840103688258900c4000c00c0c00d1609032140d07100b090042e1401d0340c007075004042d543c1c00c1c56041120507811248012003589402d440d800214228090841091164850030076024190355 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 300463462 1250 300462212 300462223
    0x1407050a0504091a0306010b0301060c06051015120c020307030c0f0f020d061a06090906090403020304121103070b0f040b03070e040509010f050a0515011215060f0207050a050120 78
    0x80d4180c040007035030102e000340d841c2c880100a138180b082c890480046000030030441034134101c07030158441c49103548042d40c0358400341c08028021808600344c16000a8103c5060f110340501030441c4c0c5940250f03401052260050301d80b504d40000541d40200400000658440c201c400310076001303007400341074179500d2401800f084820301f00030354070849904900060011300c2d032110142c03162804443c03c0d61168a028031030940250681194008400c0c0300088d00c1e810109005a48503211f4415245080e4444202c2d0306840080d6600b41c401035200c00c6000407a045c1005080003030300005d94094100040e201c45110a03208a000e61001a8408000300350080c1c002c00b48001c2e4554003c10500580c6044841140240320b4035001801c2030b03080101154050005105460081c40c2a07107000c4122040300c401500c045106079001c0590a50b24915500c6403000b004514014201a80e220301520b91468002072801420740c020500c20040403604004903a0419042d201c0101b6806000503c02e410002d11418403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 300464712 1250 300463462 300463469
    0xd1b090c0f030e0c1f020613020d0803090705040f150b16031b02043201150f050c030304060b0a08030309030307080601050d060626010503060a0b0d120905010809011407050a0504 78
    0xc079241700c40c41c4110300c845034401d55181e5401c49080b507070380c2c05c44d01610b90f441440c0a508401c41240500c042095030004550022005044991060341c2d98081400c8500604e2041151035685580216261250481030014440d8504140c10311101d80c03201880c0c1040000014203004180000c0c103001e1161040304214180c0040c0200072651000031013000380c0c002e0011000e10004100340f11844038001012290580e0000202d01245000c1c0d681c040c0e0760034203101c0fa0001030100a001011040c401040111b11030341c454080414440316910610440102c1038000301d049400034001c012a980b000030543c0e0f889610b07840d043c003551f205d550068030184942076424000c2400c014000c80c005800010f40c5c2175036030171855082c99010044804a09200e0280a4284c0c19004000482c1c122101c40c0c010310415078000300b2000724041e0941da4030007444401c100501c0401c418410410442d8ac00c01803c540c0021404028484000419400803040302c0042c4400144040030565200c1e07144640140c030040c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 300465962 1250 300464712 300464719
    0x601030b0312030109142206020c03070c14120a08030417190810090b09150118091b0305070206162001050907060207050a0902090f0d1b090c0f030e0c 66
    0x10f039610b42942d28003610454820401117908a00402c10720011000c1b98140265114603401080c1c00725076507040030390300031140140944024842030012507a010400b00c0100400245108100c08100610000703041100d40702e103003504444c000601084029041742c1d0300c1743c2e0182241000c462040c80755a40e03030148029000303042d40d0312030303001d1109900a00d21a0040740c1d007038010184030b551001c0030b50130b440044000c9034000142e9400b1440041c09080321440c9140f050400038410500030380383c0b401c0341110703900040d0010344409140000070201e24444400301010315061110b481c0c5641c0103035594401400140818580055014155210710316455220303081d10f110003200100c0c0005240070304011b0302c042c0028024044005000340c0002060740031034002502d05013215180102d103500a4126801458210010412200441d5940100800403900c9001d1141400c000c040c54049070301850b800c52805140740c0400b107c00c1980258075201a0810342c030b400b203084c5108240c040d08101500440581 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 300467212 1250 300465962 300465967
    0x1060b070609021806130213080d090608010e041205031e1008070e09060105060d1103040605240a1202010201020c0a0b01030510060b0315061e0d0e150601030b0312 72
    0x40000d02c0c0c00c440b9086000701e03142500c1c0700900100700501101950351a42c8880707104049004500307030360040d01d4090030034040c80d280d4079903400505040c40d0201c0601c000181e00c1000a1002d950042451409491175109a1403203142c15a03540f0b400d20b024400081c06d0000c00702c001400c84a240348448910b401c0c0028a5040b07080c40c3c02e15204030452030003862042d00400e2030100711120500c10703007881500000002d00d09039107004180003081c1e200a401c0505191242d80c07018114540b04019800307544540c0c0005141d2074150800c02c8a015980003a543d41550040c92508550300c190780750302525140d00411100541502c0107034024800d41d0200c08843c003a190403030003408560401a41201c2c004c8041d1081c4a5219465508a514a00171403000034020710104540c4204d08500e240382c880044c08080c5001e0100c001d1072148400b103100304e203000c03000241040b11103986008002e05a602240189403a28003420246601200203001c1410581d4031000907140d0340c0c0802c02c0090340d40b5405003599 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 300468462 1250 300467212 300467227
    0xc151107060e0c03211207050712080f06060a023403060207060c05070c03121416060c14072904060906050f09250b0d0b03070608070504031401060b 65
    0xb80ca0390f4040701c58070701c20300854a49013407030326058600d404113080000c0c030585040340d200c01140c01c1400107032948040240a104c0d00380001d0302c004958a9400040d25404120725211100260758480245014001e45051200300a499000103030340c459885013264000f1021540d00d540b420b206003100c070117204074006000000920481da030060040901880c400d100c0b22001c00000c0e00c09101d042c07001446080303c07100c01c101151a840a60000c5003c031714245c0c420744415088c2140c40d800410801d483e00103a0403544081090324440c1c15141c0c1030300e0078080c00c0a41e045d015401c060181d880701500001d56404100d0460b213172100040c01c0c1d00b002c400b02c101d003420582070010051259080c22501c4603c0c00002c11400a04c1c13242c0c43d44900e08200c010440b010040c0e000442d04203070322441e082c8032000f070351001c0f4155050304081d125280c0c0c40b00c40020164580b6040610f00360b4140c0c40403051002c42e900b41700c0441d500c074040f00d0640790080c00076440c5244c20740500e40180401e0307201c070008110215184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 300469712 1250 300468462 300468491
    0xe03070306060302030c04051306020d021303050609061b180d0813061b020604090f0b1215010b0901080106320d051005280e010b0304120c15110706 65
    0x90b0540380240d04461040c1659414802160f000b900c008030084030748102500010002e40040800d08014003026007400b0f620f102a003410400d542084440360031203030810000f9042000015030208a03c102c1d03221101b00003110110b14412a81d1350f07035024010400340328841d1160b11000c42c3c0c540e841400140d03200301d042400c2003604160b01401c00095030031868450302000c400081805d1603001407016140074540004040100340c100501c0c5290707912903480c0d503002d9071050b40011050382e0210184c285000001c0b540074a50030160090301d0701030801c0c050120241d074050f81d544d041d03c0e11800c121040e940c00380e101c52444030301030124848145409000d5484048290064540d1150b40c02003402143c445006139514505a80a0a40c0288803800030342035030101001c00301d402d43d5110022210254903100d0a19072a00c09030818907014000200b40400c10440c0c40c0701030403250380381c41d0400c00d181c043d030b40380d0b18011301c0740400d55072003615880a0350107071407000e0440d07007000c0d8801c50401401e801c18150 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 300470962 1250 300469712 300469721
    0x804060302190e13020304110d0506090d1b0f020d08030c070c090519050606120906060108090a0b01051e0402070309140604060e0409030201020918040203060c0f0a0e010e03070306 79
    0x390b958003a1031000082000d070282c41054503016008108807001611400064001e402c020000c0d42d0292003404003e40030340721000c1024045005070090201032408803601c61910444a51100c200495080c00c080d00b101d101985034141640100d148507210300031300010300040c1e840280034104d54000001e10075807881e124000c103c01d1b84500c2c550383d0550750350040c00d0120b860884000c0031050884004154060040d030107540c0c080784c028603083c106010380700d000840744011a070a546503801041480855a003140c072451740424080014002240070780e03668010824184900340c098944541c00100084071100c0c18a0703410005401107440308028103008014100070311403200b49200d203030310b00c41c0c10b400c0c690704031000c0d14016103d01945006840a120003413100b560b060f030441d58240401903044c2d58612195001200d140140101130034203004042c180305000c5c1c508400640100b0201e10211180401d0b0b444001c541c0c01d000302c444c05507400599114003411170666040c01280310220030030000380d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 300472212 1250 300470962 300470977
    0x90a21210e0a030b0a240b030604060f1d07030207060e0a0309062a06090206030c04030c060c24060305120c1203040305092205040c05010f020105041e0c030804060302 73
    0x90300c81c801c80400d001e1160307070407880c080a40840007100004a41d440c95810105e00f051403241c801812040c0c40e0b412090000568010141c0c00c00000305000c81440c0900400c80035284204c1495000c0d0715011410b0100e5124141912a15482600260026009034151804140c11000510010311905001501c80040c0e25080300411411000421058414806210440500348407200760014191041409581e80d8804540c10b41e1a08400c2c0010385903240603500403543e14500729119421490300000c000100d13089142040502408140480c85a03c1100702e2810040d90004031803a8060007074000c0e25083c3c01c013501c00d2140400b1002d550000c84010a000c41001c2c0940745d0214400700d0070074051005072801b50005030244001c0c0e51624180c1007102c80d8196030f1803240c01c0400110500350944004807800da52440000030200495604000d541103c5d14851008000e14079060740c401c182440513011a052134503800c41c0351010000c561440303901070341d0008201c1c1e80700c80c1d45001c000c0c003a5120300c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 300473462 1250 300472212 300472217
    0x2070602091f02072d0902030106121b030506030123091b091f09091a070c02090a0f060e0a0204030c0501080702150a06031b0e0c090a2121 61
    0x8a0400d15240d0a0380ba08124000c01e902400c07070355103800000d101300e50795481c6442c2d0441e030301002ca20b07039000e11014120040c40036800c00350301c3e0b626211024114601c410025100c203414000d40410041c4050101c2202403050b003400104c1d602d8041c0402d00400198450450030401041490200c0e5900403500703101e1111300b400c41d01e0262100703038503042d682651060b25410101400c040b5201c1c0502840e56040040381000300110380340d40300c260100303442460b5001d85406c0c155550700410300940024a651003042d6041201d10601160b020510b02c2000403e10500603a91340a0800c0c6003940d90405c17030050020302078240460030550bc03048000d5003c2e02c42202c0104040c28001059405042c0e500e00c121940d03005030030700c170311104030880e40b001c00100909401c0c0e50351200400000c0300c4440341c0d145c86503e502c2c21a40c2d1420284044540301000d03250005200701485015031696a00f49050180c6072000070900004029803c8100d0310f1940c01c100601001003260341d5030424008034003280030313880c666 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 300474712 1250 300473462 300473479
    0x1503020405090c0a171504110d0807020a09020c1b0307120c08010c02060402150711150a110c030a0204110d05040f031710030b070c0602040611060c0424030b040207060209 75
    0x1408200c0d070002000c10610841c1e0000702d00d03010194918004107902a029069082d2515415030000c0d609d21104041141c2426010403141c044d0b04000c02c08401800e505401107140514081145660b404500c1c0c031003400483c1c126a031304c25610144540c0c8003c240001a104030544d00f480e000d206c000142c061174540e5031900c110b5681181c40050002e0050741c0151559800340c59062025800e0782c09150103071100c66003904039a5141d12140284421510244ca44940341c030f02d986001801c00910a075166010307400a10391207000c1e0360214001e5100366041310006402802d0b10303070b8070196001e508244e500ac1c1c6d00d01802c000c240b00c0544d002c2d800440c4a076139445204603060034803000d8000c050303c14a05c420007104060000505c45004240c00285a0620810303080c00c03591600281d07030013500100d00180e040c28030303d007904d1000c0006d09d821550307040741c49041505041701c0f200b0300800c40b002103402681188100054034025131100043c0c21002c0d000307542d140720a050080207940444400c40c00350500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 300475962 1250 300474712 300474719
    0x101a07060603052e1b0503181905010b03010c02191b060e0111010c05040b0304030309050a0516050d21050f16110105031510030b04020301080a0b09031201091503020405090c0a 77
    0x9601c264450111070009200c402030701c000e41121960001040000f1006000d6944112220304020101e000d9411034042689c0086920b030507807c2d900900c50107030103681010155146c0c5c9401113200c101e80d26203c52030088504007410a00066401c40c945003a0480341d0002c08140241e00203401c4d41021004c0e2141081d250b40c041c0d4550032141007003a03540006009100500120713803414020f5801500a103004034800b415521440d0a11030401411035080c0e0015680142c440955001c84009000c100c40502c2d85610300c1d1248480d80c1b8400d10034460350203a0840b087c0119008006854001d06000c0056840c1c4001100c90b1307403820030300e00d004d40d54030455071a0002c0940c411000c42c0c1c07040c02181c501300c0c182c2d0900e0040c003000c086000c0c4000149a11079001c40c000c3d44642c40910300800c02c02c4000e086084c0942031851800c0d8018202c1502c5030004c01900c90041c3c01c541c0d20904546140c0000117158a12280501c0c0000154000a521030700304018850815070008440c00b1110048400c41500c654 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 300477212 1250 300475962 300476053
    0x60d150e0907060509040c0509031005060f060421020307030b071706060304120819020c060610110a032303070e090702070f1404020f0703021005101a0706060305 71
    0xb0700b4410207001074002c000503981740c02c0030341040144000d1030411604058540c00000d00f04400358803507280c038a585108101c1e4500c0c00f102c0080904405840340e038a0241080700350080904500203400381c0d500511600f0b411510100030040c01550031411400081c1808207000f0b100e40c98444003060a0b001c44000314840b85000d0003202e02403a4041c03c0000d001365046019120201c004042e000e24011650045002210500052a07041c110002a00b503d142c074008200000c00207400c1c900c20094064120b411804000484490140d010b040601c0100c11100500c8568142c8c0380100c1044003001c020300c03000c650040d080380740000c0201c40781d403415076503003004031780e030f19954441c801e0f4402c208d0b401040394004400703003840c000304090009841d0203581c40c3d07007101c29400494118010b074490b60100c0c2541010784207168000050005c0002c40794036260303203840581c03514103600070800c600042d008200511071780440f000359440000d5070300f21401c0f951038035040c10141442d8450864030031012840081c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 300478462 1250 300477212 300477223
    0xc050909031908160c0303270302010e03090904081b100b030606010e01080c09010915090e13080304061113060305091519020c030f07060b1c0b0f06060d150e09 70
    0x80c2e114410580060700c001308983c00d200e1808281c0502da62010f00ea5400d18680081c1607000c41d0b1044d40794a481d000f403038004c0c03c482031a031504a460b081402a50310a5a42c0001d59802941114504c1e880352805080900031300100c07280002c2a02c140010b8840b0300c6680c1c0c102a18104084058407074950340c050065032143d050104540c0014000d00000e40b61049080180c40340f0001803501410a50b140e8000700e090b49080700814002c140e02e00410021000001d903043e9000044800481c42208550749601141c003000c1c10080407140c0715040103501819250684d89800d00a081941700a59500700c0500185810b0320381d2000f07400785005034600300204403500da0103141164402d2600c0d41020000388000d41159521400e80e0000b04940c5400d03010170b0018112240c028540058004003402c1000f51a40c010281c521120070624140c60201d030b01c48032a1035100c408800048200d0b40c81c0000500180300c0c0b1240c1ca5003461030113410328801e50748101c1c0142910700c012a003080d039484a24055640c0c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 300479712 1250 300478462 300478471
    0x207140615090a0902210703020a170105091606050915070605060f010e0105090f0d080406110d030c02030313080c01060b03090123070507020d080f07060b0109210c050909031908 78
    0x6c1c1b80300d0000114694a81031121250100d5410740f8030043d100d0303002801614842c0d1059031400c00345c9010300307500d2000381305940c1c0042039000241400740c4a0851288081c0f1203100d00070900001145e05e640d0b41c0c5842030b110361981e40481c1c0b49662039000d847d10b81d00504068420a000b618900c0c081101540242440e418004c0143c40c0c690030000440e0410141c203003804007460704003040c141031800107524040640007a0403d5195040011804041d4030300c2e04281c15450410142401040d0200c2500130007103980158000480c264480c05c2070400e00102c4c070450030080020362030010005082d02c0349001a6000d0b030f070068000e01000380c050105c0104049a0648882004c5c0280081064030b40100005e0031184e1001e040701c414807103203844820745034016015560000c000000c51404010362481403d4580c01d00742032100c009070601800c4003000b10480c01c07030315080d610321007420180142d025041c8010721006100d8500380ca0400c3c2100c1c0c40390800c044240c15a40500f10304403031340b402a08110b01c0b6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 300480962 1250 300479712 300479719
    0x90103080a081014040e0109060509031e0304020a0311030c150a08180304170c030a030f0806010801080d2703030504050111030703020a12200309100206060d060207140615090a0902 79
    0x100c034203244c100303c018a08240402c00941d40c5032110300008065000721840744505c080595152040c0300004601c10341000c2144280603030030003c000060392401180b8080e6504100104800e07078000c4086840c201030004a83c1d40b004e51808040078400102e070060061031340d190b441e0000c580394450030b62842111050702314840d801c10700042c0462070b210890150130300c3d541e00c00c41c1c1d110360140b004203040200d50001039002a00c0b0740d00b503800c129084540ca64000d902881c103481250325002665480e41d588100403020080399207207641000c2500a9645508010040340d0410317990340e441e0161655215100305808144070301c3c0540c003140404015a22002e0705074018182c3d4120994410409a50007510201804508a0b042404203240c1038041d40000030100219903030319149080107001c0a003000b1003401c6600200c02c02005860700402d410740d9039400b81015884002701c0c940a010740300e050301e004c07146112351030400c1a503c800d81200c2d24592001d0300c1142880e01c4003607243c400da90a04070040d42 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 300482212 1250 300480962 300480989
    0x403080403060905100f06140102030c100c0e061c0b030a05070b0313050a03230a020a0f081b0d090504182a09050603060114010f1409090103080a0810 66
    0xc20541d4014110684c410010b6681c03901d411182581200d2004800e50003450b0340301c4083c0b0005031101c280c0f08880d4000d00042d0300b4082c11072882c50b601e102650445500f1502c0e00003e0805a0140c98010250b16009000c0794a800e070403495402c81108004c0354011450074442c05010a09020a00b03010498004018007103c40c2010034440340ca51000c1c15102144c148540008080b81081c000c0288462007a911040c44540061101c00c10358030081c0446036101c000c008101c0b206800041000c40d07181e000240c0c80c0c50305420704185e00d44d8000c0400b072081c40300103880d200d403040001080c0640340c21220b40365a006161240140001c85081550851400298110700e002007a1030400504044881040c0c0105045800c0d41b20f40415586a02401711030b45c54005000091509012150240000c04613001e4580aa400024010400d4010a00522901e404041c846d400100c04440d4054000341288885582d40e151003016903100c40e078898005009540414003102041484c00c0413030b00440341014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 300483462 1250 300482212 300482219
    0x2d0209180403050301030b0c1c020c1216021c0203030a1e0903030e0f03070306020d020d11030709030b040c08070b03040203010e0708070512250806070c0302120903190c14040204030804 81
    0x201f80d440580b03c80c180701001d000641481e003107d0030045500c0c001507805a242d40350600382514251707800500504110301030102103e043c0c401109030481c40e80448402aa0540982e5070724102da10907600a5054000042c926200d90703042a45440000058041010404103a040413512540203000040004008c203a080446281c110780a4043c403034004c00360b03043caa03509c0d42e5a1049903c03958851907255008031340b40754001098424188a60007101800349180340c00d41c1d0007003c1e0703100c034040242107011fa01c01140a0180340080c03080501211400c4a08050b00d50140c42480d4204030742c103e22940c280b5152060ba5140840c488080b11403030401400501c0c02c2c40c080050f9010700d01c000794444d200390320f286041040d10040d00d08110900f0050840c145040400203810310400401c2c000503c0761824024000903800a40280f22003d54104242c6070203041c80028140103400595401c1481c081c9001000c1c004c00c20000800c8600000c8041003584001090000364025407001800f43d0300c0a00041 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 300484712 1250 300483462 300483473
    0x41103190c05090c0903070806060f011e0c080c0105070504180b0f120307080d060303030621030503180a03110d090305060414011e0b0a090b132d020918040305030103 73
    0x20341240d2008030302c1d405c04074418040b0345840300304da00c0351000da8071110034080c55041814040000850a290000503030320003841c0000110903021440c002c004440700d44200703000303070340d01030385c00c6c940d052070083c80141004130005010f600b1a01079104080d02c16440c3c500207a205120700d40807031801070440091a21303244100b165a020100c00d00503035000810020002a1a21b00141030842508000007101403d40c1001021a080c680103c0013542c030724044003400219052000841560501d000c41c0d0781e03965180b0030300c0c21998025855166200d07030214141010340001108000c00441000caa80c09011500126250441488058900d401c40c40115001c40e440308038240c20816024008104e9400303102d4040781010b000c0010806041c0e840030f217030405203440041e05000b0580054107201c10449100010f40d2980244d100d1440c2c50360307035006061208440f014545240d111050000d4103580c0c104ca490019600050f0054801c8010141c0b2045010101c600ca43c09145c00d69240360450f0b0842d81e80c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 300485962 1250 300484712 300484729
    0x604110909130302010b0a030b15060f22030b01150e030c0a120c050d030903120201110a20060703090203060903030108120703090503100903030f290117041103190c05 73
    0x60341155251529511187c0310b1303c4c4414000c44c0b003040c90800b02e2030210001401c1ca6045100107101390b40030084a084001d150b0150b921128020981901e10b941c2c90300071b101500e5075a07000420f014051400010552003d19068007030346015103440d16007081d003904050300c86900781102c5a014820007000d1244081c83c50a101c015031003080d10750314a076100c0c800034005803842402100041c9081105000b0070100c065485080c40172400244580207088550006601030221540108255100c1210322042407401e0b51500510300380071341d5403908080c00c0080280c0704101c401c2e40288a80400308007141c60000c00ca80c1200e81180c040e1414203c034440d41c1d40d40c1d40c41800c083e81008917402001c81d841d5410b000c65814a049003000240350100c0d03150290a64108041c0c50110782d1904c0d4034107460301030440d002c10013200aa030b904a07110303685000594503400d411022510403405001000200855882d154100d010708404482a4813201d88842d00c24807000f20005010440c940d0040080c3d0602c0000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 300487212 1250 300485962 300486001
    0x715030f0513140105090727051f0f1217040308040b0316021b190e091510060909020714011404110105042402030708070b0604110909 59
    0x10085002611449154140c4100780d49000144166070007103000c000000b03e42c0c1c8050056140280000e240c512003203500c0b11440d2280c01c2000d9070407d084040c0e80404002c56582e11018032003000316050214950042c0f25001028808032492a03c000c81c4003c0211070310710450309081803c07180481c2d203130b4540008404245030030323181280070700c4003100103400304024001074020072401030385134580348440007160752010190b00255000186022141c002100f001d44c50510259084640c0000d0300340400041724555100e008040d001d4001d0180388440403a01c0d0000d20600c516002c00750321414065035050a440c40343c1c2e0045a41c40c0d004004140741500549802c602480c09400c480b40e0585416094410b22804c40c2444a401810001001241c0340c0d0410514002c5c83c103d420503003000c0c49a17000c086011442c1581e20303401186007240c00e10070402c61740c1b11030348002915242c1c801e601d0842031110083c0c2d07509219509101c242d0703000036441e4047e6060520001d084445e551550010310511100101 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 300488462 1250 300487212 300487217
    0x7050109150c0909050c0d09022103031008071203120908040b0c07080303060d030e0a03081b070603091a040f06180302010e060412080c04051306180603050715 70
    0x1190080401c081d09200480c0090316003010840e5214144018100c40b8960800c003200340c544018002e41d0080031040d02c2c004d522902000407181000d0000a1114540070707520102c1d454860aa802e43d03150101c0518000d0030702d0900c40a08a80321007440380c032034005010300303e0003a44032404800401e11074030583c0204402408000390010082d1941c0c8019841501f01d40c3d07804070b0000d6290304605040008400820b054009103045007404400106403148003000602000701140c1c071040c982d0f0302e003000d2174000d5602003182583c1c0e8590310a0301d03a0101d110183c01102e4000c540001640701e0013401802c600990100502d100f074001807013444441180034000743c038031128101d04000003c0f41071288030341c4000c00707444803040e0401a20380203080d9a20303541603001320b42003a020710000403a00180400d0001d4076052400d0655100d140c2c0c00720f10300842e80580d508c10380c0d414064055641d80d47c400c60a0721700d60242d80443e03180b006c0c2e4200690382c4034880180b69034070486003001016401d20300c00b1803402c05407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 300489712 1250 300488462 300488471
    0x2010e0f1c03230c100b01020c040b03031b2a0d080d1e240b0d05042a030201030c1106070e03010207062a0801120b0c07080a09030309050114030c070501 67
    0x1039550380c100403104107820000b1030f00010040d00c0740000700306610300810545000d010183c1c00c000002e40342c0c0d0a0301c00445c092070316940c1e56038a40e41d052041d212101c00424648144c040460101541c910040242d4507030a06103140d5a030441c194041c0741040d04c50043c00450030141580d642c01aa07a0004c440030300b006544018040500803100060b402c2c0305030600e000304404074010796406a2200300740301c5140c40b01d02d05a00f080240da6510a8490750810400005a246e4442c20300d43e5002c01444503000319803401c0321000384001032030098201500c0c002c2e6420008540f11400030f845044e0081c40e06119030b4400030018544904c01d1004c02d4201ca0060000b60a110301680d6440c1928103800141d015074814044080d01580303092940e010794103082c506144294981050750410900705680603001041070000111007540d041e045071007455101d0345441d03880c1e0703103000c0041010501d0b00041300000c1070220f00050641c411032a4035800c801c5040c51900d0b42c1c40b46c81b0041013a50101c81d0480b100d5482c0d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 300490962 1250 300489712 300489737
    0x6190204120506010609060906080109270b011d06030a2303070b011e0605120604060b0c0606030715021e0f0109120806031501030623100302010e0f1c03 67
    0x8410148141c240304000928055040c81c3c006030400020340c0110f400c00c00d81c2d14040200c0c80d40100c1860440301c018200144e21007a20880c10760038000300e01c180e040d1400344422001004140c07000f00e41201d11031440c0d80800c00584031000030040080c6d039110340c50780c0038104031008907408416442907100c82d05264500d10000e0f041e9141960014481a02c0110792080100320302e041c60241074441134900804900070360b0500700701501a0081c0f10744100507002c040000740454541c0c6d400180580781d800d01d080c0c1c03204071581130690f44072000c45120340613001d0713410002900510380c4c503880e280d1181a00500a003803c1d40814440c1000c00c560a42c1286c030074542e100341030388028030481e5040b40c0503d244030451400d5102c0581484400b07410a4020303808079840c00841120506118192940001c0101c1c80803821411020284804015008400484014018008940c00303035101100d100781c0355007082d0007443d020009210070f17005601d80c100032400780c54840c585008010004c42131080c200b518002c4203 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 300492212 1250 300490962 300490979
    0x1020405013501080a0b0a0b0108010b0c0c09010f080f010b1e0a0b0a0306050910083a050a1812080c031306080402092404020306010509090907030201030b03030c06190204 75
    0x10030390001c0341316081603076904c0906c5003100c1016800205410180401c00285000134034040052003011040c040100e410307905030600f842294007030a8000d02c1c408441d46c5841142c190400c042c8280c280d1803099072114043c8840600580c001807200070f19450001032944207809100a0f140380c41c82d0300843c0504003003009a9400094000b800455400281440c02c0c181030028034a0060500115031410714401c0241c00000640007541ca2031000c94403580170354405041c000d8403811006008001e980040d5145215400f00251041d016a6a1a1985c0a4840c00e0321140b9900500400000c401e14562035808a0740000c001c0174482d280d070003113034500b02d4694140812900c0681142000500711406d100651611403000380c0c00030381201481d801c0c20000002e52015044448165000316000300014803c1d03030154040d81c1080300003a00c520b1440c6403074450291640b1650004901023032800c0120743d1a070400000b170710094407003403005017090303160907034840f1001e040ca52400c0c1c0e0050302040003003407040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 300493462 1250 300492212 300492317
    0x1e0109140a1d0108070515190311070312201215091609051f030c2001020c011a010504060e1c050a020f0f102601060c060606020102040501 61
    0x14045140030b954100010207007415006da0095214000081d60300200c0041c40381210881514a4aa03820441030860140c0140440240c011000480800d440041c1038000b070441d800451040300801516070000a5002008590440c4241c0650144102a601841c15181a40010110740425403145105000580390344003100c0d0349905020040d040c00c00a5007007038000e00517050484100c6894440c0d4001d16440d1001d01028104140d03ca5414403a0316014014070f10806412030310512a00c000c135803966001c1c0d03001c4100601c2079880d103031754003030b90b05840c0c40645803402059403990f00e424a0301d1000c40300f441c150b1081c03680c00300a0074400c8000f9095a650103040e1445080605040e800e580100300010801204c2d050145080c1b0b114582c0c541c3da00103140e100c416050400b21000c81ca07401d41004002c05148009014100c0c0340008160a80c21640c0480d1451041034188003007915410101d082c1d000d50300c1014003107415100d40d03c2400980c01811803490403a010445007200108a402160b074 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 300494712 1250 300493462 300493499
    0x207090905072111010221160212030703021204060804170c0109030c02010e010804170f090d110312120106140706090303020d1104050303160f050a050303061e0109140a 74
    0x2111144048404c000340c448503103c90319001d0018140000b441e0402c1c036950b00c0c4d040e150007440072000030111446d110490201c54100e80141c01140e80802e00800f0f10350703a602c03815041d0007520850700e80d59140303680b410880301070701c4070f581d1900125100c43d40c4094550710390310300c02c0441c004140b261503100c11007403003035401541c020741d170380420f46800f40005040c65000c1d03a0307281d041180c0782d01000041b40b583c0c0d4000a1002c80c0341003040d5114410000e64100703004454420b68400b0721580c207a402d20040649072100e041003201a01c0b004001007203101020321a59400c0c07508101e041004200c1a0b028101c04083e60440395400b0385814419580c0310100e50300860118042940032a1440401c14984640d138810200c440c0013920301402d10002950307902a44400c01d8400c604a50349404014110081400c020b50040440380c1d030f41103601e05562603800844449004001030303400403034009881e0a41520303a10043c0c650a200504080c51901003c1c03010280c3c94010f5900d500c0018078200420520440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 300495962 1250 300494712 300494759
    0xc0317070215060102161401050f0408010e010606021f091a0a0507090609030816020f060a030f0c0c0201201f0905010b030a03050d0207020a090c030e060601080106020709090507 78
    0x101d540611003840d902c0083c0415045600036003520039501a400c03004001c0d5214240004910f280c0000105d40391b01c5010300040a03090b011030001051541500f2280400300c0600003444102d4032148100d17505c11103160400070110b18201d43e203002c00e0040e40108000303402400c0c0032105044d01c5840015104040c0d4440250305c1e6501d0401268540c04000d41001e0300844c6081c0d88500d03e16120a10325000305040100340c411400300b01011503551440d066140344015069130f0b1101d00000001d0000c0181c502d11001321824400301029180c800d2401c090b045070305864a0281403500660080b0800144100b035203d44903500e00080000c0c0200c40d2131203243d132080004250000a4038001b425504007147c040e02a9124030b240c3c0700026003040c10b0302d42401850f100140c80e4501e6000240c4c802303c450780a02d40742450010403440b1a40e0503042203814000c45011a0b405407181d1004587c0003009104000041c0c101100c20f0180030700580040b215280240221215140c550342008001c10442e0002040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 300497212 1250 300495962 300495973
    0x40c09020c0f071401050706020d060906080703121e0c03030b120c03160b030c030a0207020901030f1b0308030a020d06030b010b1306030225060e060411041404020607030c03170702 79
    0x5688003081a00f0141c9003050860343d8501d03842001a10303500400c5d0b4010714158010856500e05021540302e0001400f40b04e10500030b070340c0c0d01c000e4540c0b07506150000303581800e003400e0607809d400d006440420740481e004031420002011400212202304803010b00701d040540300c8030072420603900c411060f91351005402c058800f03003040004042c40e0007101408140c040400180401100f9101415280c0c0600a075400e20740d20380c0d039001507800034402c0e843c4c000d612941010000c4140300e4404000d01525100b150b6240600ba00c03a1820346075401c044c40003c11288080002442c440440d4016154050b0110300120f42249c403039580080401c401d80051014940c00310300c81c0c144441c10001b2038020015424110b261200b11070910018441000c12140101c0b800c3c04040c0420010340d120180d10840c0600307940e07040c02c0c50301c1c00e00402c004076170700d091083e4200002c64039035075602141740e40502e9006050703519044443d40d041c2d8070000001810b42c24400210a1980000c03d10004075109443c642e000c4c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 300498462 1250 300497212 300497233
    0x513090b014e180803060909071d0601080603032b0f061403120a021216060c18050a060903061a12060f100305061306020c010c030204090e060f010b03040c09020c 71
    0x4110f0f90031000303505440180b9031511012030b48039030849801034019500c420307680d51008512447c110700d40d80407052091141c52042000510381d803405000345402d90b2501c441d034941c00101a92405900c1d800b0313810031446a03004040c00015190400392100350100407424000703c1c0700c40000c490403980285401e1024051680c414a800d002400f891080045468148030074aa0029580c1c85550f49405410b0000520200c0c0d0121031502c0380003065200380c003440113032500000100070f52070b00c036003003030100301c066001080380c0c03400d0340c54401580c41e141d5902c00708510350b0702c604014090080c2c070480209900000300800d0b803104800c00c9610004507006101c58201250340d60080e6800810100c1900c100001c20b1000a602051541d040029481d81401400407130800400074400c030004200301d581380110f8402c2c0b4a400d50050001c54400140401140340e0003c1c4007a12024200c905012a038405001440b02c521400050340c5c1007030142640030943e5031200749000803a0b000c8150381034107034411807010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 300499712 1250 300498462 300498617
    0x609090a0e1e0c101b0308040602280f090b0a0c170423040203060a0302010503070201240e09030a020a140106050306010e04050f0a0203060705071e030513090b01 71
    0x1160085480c02a07004100307a250a4440090114024200071f0403001185c00e10003250182c0b0206010704441c02101d100440707001e140111f501d4040000b144007664400c000b280540ca00b04101e9503501c170300c2450300c551000110f40d00181c00408035a52111001000900540074026101500000b00703403083d9182100320402c0d0807084515154803403801001045429140c2200c000e04495080c03d00d03d44a44507050180d0260803608000c0030000480c040e40c0c1e40030305028148604a804030001000d041c1c031201589610f034031440f614600540e1120080ea400902081180c50421004e907000003007403034585000a007414400c5c2c0c022104010800d0600080c41018010340c4158981c813001429680484c0d4007003a2215401071050003445000716920342031284411100365141e01c000c401c075031382e03081610b80035040c0d4111055420a4001106000c24480700d50b110b6080c000405860b61000513035010300a800000c4a6000d2995507034000c107129200d85004402c04410980b0103600600c6407151140780c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 300500962 1250 300499712 300499729
    0xa0b040b0417030703051207030b0909010209040e0304050f06030402060f0301080a030e01030b0f1908070b0c0d020604110904030e0d05210424030908030f010906050609090a0e1e0c 79
    0x14990241c03c10001400040d400000300d4104040380341c0e072000e1507a03640b0020740080517032403451600140040704000c039080c1c0c103500820007400d00711000c018802840480c07580d01c8c00b560080c0ba82002552000c0400e902d0f008014642c041e1008100d40d1815607036a50344001508283c0c8540d5655004021000800d9001000c90380d00031000e10303041000c03c203030100160b071705010500c0f45801040c1c2d0382c03c128500710a044040f40500f4050089807a22941e8500309581d03540f000803455070601900c1045151184045240e42c011608001180c511404002c20000c413108044c00490501c2141031814005465480380d500d00c490180d00503080301c0758074003145204a1240041102c2d024002c01050000009224115110400c103c1c051880f1480c0800141c0c02007010b00d601410250010040004c0c0700980498a41681d044480900c00d80e90b60300300f0701045002d9201e113550b000030703604001041c0481ca40d000081454111044400c0b805080082103c1d01c2003214480260f0f03000305031580b9450a02c190b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 300502212 1250 300500962 300500999
    0x70219060e0a05060307080a050a0b030f0622030c082101030803160201180807080d05100305100c050d020c01061a0c0c030c0f01050307170c040302180708150a0b040b04 74
    0x21305a1861a0409005200b0080201168411951280803030782d54210780c0d02403c06060040c00716030f00300d240342206981d00e1b1012143d0000c0b036052503046c81d0340d044c810201035404035070540701c0f074001c00490354600020ba0400703403000344448910104400041c0b80c0030503e034001c500826a261307903820b00700303502c044848114040301e05582c141004140741481c03c0184074042c0750400035039030b00c445075840c010300a44954207040c0d1409050000b40007008616003c1003044174420800c840050344a003032003d00303440315486040003040050003032440528807034000301030002c03040000103051500d942100c15405c01c802801841c0903008140c121503948200001e00c0c220300102c0007405c2450350100013034642450189194100000032000c10303010303405200742074021509143c040441d445d052012130f81d01d0300988070030303842801300c8543d0020290018003400e010f02d605540707051f030035036942c4403520409218075029600058a0440000d500c541c0101030000313442c030003c03400d5480f071a25040c20410802c288 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 300503462 1250 300502212 300502219
    0xb060d060801150e0610120c02010213140a0306020f0c0d0e01022509410705070b04061806050406020304120f050414040b04020c01090308010b1e070219060e0a05 71
    0x7070248130900c110081a640031200b100d10380c0420952110445201e41ca02492a03819402c24001c62010b68040d006420342201000c1e082030500c2e034a01b01c60b0503035640e40755810b030040d102e00c20a001042039074000741f14002c52403001d50314150701c54448924054605c09580001140c400701e10304903603814083c83c81002000c40500990320b101030310302c01917428a031142074000d5595901c00e68540a0b008a110075142e000c01c43e4007404002103010004e03020203040032142142c070141c0083c5c0014082c50640b5101e43d0007000d074040507130b180c1d504c88006291010000c3d11034418140c5040019445008061003039102d000056180d007428540440c4036030072880000180101003e1021203036900205590807200000d0b4107490403c0c4410205008012001280d40c000e400064140e610340c1054100c1000284a903840b078090340e9903401c0744d007164002d080c441d40c0380410180030920512400000b5101e8a0700040c6407407440f1038280c8000b2050b2001c0d5010102054854400c4260362400700c1d8100c00400056 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 300504712 1250 300503462 300503501
    0x3030510140a0509150306010f062003090d05070b070f0204050c040b1213021c031103040501050f0c071e090c030506090a0507020c090916050a03020102120d0b060d060801 75
    0x810005801e41098001c0300c4c0500c200100140781c00a58111201805101805454203540c45d4040b0480b01c4d4000c0c050b8001040f400c80c0005140100d80100080c4a201240610300f014522410071504408120040c3c60b83d20440c88082400040c01000309803d40c8648884145980320b841808282c0d8801410103040003424081000a502c1000031101501c42d0105250101d598501080e08207100444ac042e4120108800e0615120101c0d2813001e8814041d072180d460400400d0780c1103aa81c1300d640a5940080c90a10002000c3c041c0d0740003404c1c4441140c800e88040c00d443e00f140070341e40071800508210140c0c00c828108000ea42d170b8440c108034a0640d180611480c9000c10104000d4400603000106850b9908001448584240231464500c20b004045400e10700780841c0b829514070b4907407110183d004540f04002581e1503c1411207003102e9068020303111600700d08505407220340180390a00b28440c0c640703100840d05e03a20f0350024400034890520000d4210b0030304203940d08480003070950b841d0030300d4039 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 300505962 1250 300504712 300504749
    0x708010b061213060906050c03060f0907090b13080a03020106050901090510141f020d030b0d0215220e0a050c07020901090c030e0a0b1f030b060d03051603030510 71
    0xd0310461039021241000000303c954442c64654010035013003001070461440c010a0007007003d2007200850040c54122000410b401d5440f0401412610a550310000319241210810039110480302074154050280c140c80d43e510f640b0030100f4103110950004a0041c0d540302801d0045142810f95640502214002000036241005041220030400e00402041d940c00f11031050140d618800850300c1002c3c03d910a00204150341d50180d0f8900c40e4109090120b41080180403086c00c140d05041400da40003042036019400340c503140400c81d400700d040c500120300b10144400700ea640010800e4003e00c00703401503401031b1801d00f203e0000c031203003e03005c102d10b003030104806d0001d40c0e6004801e44c1510030958001581006804056004241000a1032000c0c084c20180714140114014010b100b50200d000301207030140388900d003508615250200600c50304c401000700c1d40d5420700c0303c00341c1038981c404d00f00546040781e5a5800c28140c46064001c81c0025250030410607410410000c0000a040801c0403030b00c2c4921 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 300507212 1250 300505962 300505987
    0xf0b0f04030201120209031006090e0102210601031d060f010609081b0303270420030f04030e0904200f010509061608040314250312030f0e0708010b06 66
    0x80c0d20010f0704020001c0c580c02414841c40d8100e0b2081a00101100d81840f89440241c0150866210b0324846910b00003050315549018001c56034015441201c13525842e1004000b144001c802500313007410903a45901c50409103101c1140301c4120850307940201140d1030301c0c0b0031710825084141c102a0070402501e808000074040000c030380309440105844071200d108808007080c40c501804000d415800c040d490718000b04002406003004e0003405480c00c5c882c0320060f0614a01d000c03804480182e8400040001416880a0038107068020b4800d190403c1c5100b25080019600b40d0142c8040d540e081d020404a18980301804510b041c00c4000d40d060340031040200c0002c2c01a028030b0b40207900a120000b40d030a990501e524403000c9580d48409040d4072240c5030705044211003560340e04004103200300101260300e11407503002c041e55103110014a4104505554623102e061080840401c05d2644071500464403214501a15095507400c030b00810115103060318032801d482c495110503009030020043c6030203800 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 300508462 1250 300507212 300507217
    0x708130f03081204060b0a1d06060a0806100215070f1b0b012603071202100612020d02040e010f15170c1009030611030402090606160b0603070f0f0f0b0f 67
    0xf1648070031845140e985040a101624803c62141e501818036140031488503c101c0000c07000c1009800d104900303588070004c1c014684203088590002c10b011500140c9a0700e0302d580b82800080c413501c1a1800380c2c90b200000350700d2404c1981c001c1b001c0b070068150f040701107078000100c260000140c4900c80ca00e202a4454025000040c06070300d410f4070818400b40d155441e48501c420201c00d00008507030740c4160b071303007000d91182141c440200018050301c81c1044150721240140001e450301454603a0701108190308018403a140b50100300c1c0c000d81c660030000001e19082c440c901140b0207828000c107104089d207440135580185500a500d1910f12000d4080e01d070540080e0b418005201a80c0c0d9980c0d0341c146090549044402e6071006086a080034a6245200d0002c400b1b103000e6031007990704070703a40e4407008104251406202c42c9000d207403802d07850950210b114038120305d40042014064810464403800d003000c45208641040a1028402408100c0140c0c0312242c10000e190024400d401c01e4103400380c606107803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 300509712 1250 300508462 300508477
    0x302090d1b0e010308040e010503030705070902071a0a0b01020609010227240c100612060b060405041d0615030d080a062114160303140f0708130f0308 66
    0x520380842000007081e08400c2400103841c00b00201420341d03950b45405a00ea07032050096050103c400c5000003102e00b400400e0310607142d84400986002c81c1840c0c405070003500300250640344007007980c410184c0300e1101c828146c013071201100e01140418003070300060b240c5940075000342ca09078410001e0b00d550034040108000750101210400e581d960b0070100261800d4042c0104407190a0081e40000c202d203101e0740140075100f4180165091000803041440844441d403180c2003142d42025101d100048460b4403008806800500142c24941c4400120701205c1c0440d16441c564000400f01c10007084c001c05c04140d0101c0151031641d0480014030101e62a40c10503c03428042c4075100000c10f10348192904028068105d2112200c00a082074000300c0c4c8880310100207450070f2030b501044140046000c1808813464641c10901c80c0d0503482c5a0b070032116080c4031244540040001d1140c010b0400b081c1008000e0140207083c999103806625240910714003040d401152100c0350080204005080401600c1aa = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 300510962 1250 300509712 300509723
    0x10f05160609050a140312011203050403030e010909020f0d0b0a0b04180f05040c050108060a0b0a0c080403080a090509090f0a0f02030c030f070f0e22020a03080a031406010302090d 79
    0xc4110361924501c2c1001c45800100b0300ca18400189455202c000007038000341c10382946607d01c0d645d95400e000c909003050f207400b80004030704010a00100e80918880c407032115041c500210510b642c0c442d464203d0b0005a40c40c1c40c04000001e400440c03820901900da03065004660305000140342c0750751000c0034484e92088070000c0c220030404540c184290f40c0003407038a0041c894144080d1900c0d01d45410031104c18014030340440d45840c01700764207040c80300c080000d80d41d0090b411454180d4110003a078401280110440e41034034108000f01c0011014000390101c10065162094003d0500c1c1c10050852801088213099601441140c0d0b6031070340015100a5203030300302401402c06403650012900b049215911550140305990707c0710180100010a50202d031048a42800c14548074031a04035080c1341520a600c0402001192820301e0000d0890340e007540c2d1000341a5420b103076403a55454403079041a410580800e0352035608590307811428520561050b000d20382145450390308400600e0030300e145c840c040d25 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 300512212 1250 300510962 300510971
    0xf07090b0d140309090f0601020c0103050c0c0f030903121804020901090302042d0c080c090102012a0e0108010806040b1b07061d0d02070b0307090e15010f051606 71
    0xd00c0c0e11810424444160016000d46491040c03890303082e0349610003601e031030050600000060180e41030760801c0b4040c00c0b05034007601030000c80c1c2e0011800b400000d000828640030410425140b01c4c0100008a0b115407004055902e0f039640708105400c01c00b10680d0308280801c02c1284c8410403c070041c486140010807030f070058a49003001c0040303c0171521b941009400901c1c2400030500041400c803c2441224200803500d00442083d101400350f8030020081000308034480d0204074208003603406001080d206100005800740d05104144048400c01c107480c0a003815554161041d43d401001c85501050030300b0820007a51510312020368401e801480a4101c0d88114085072804908001c4c00c81d00d0003e40907825144e4660741408002010509035450b0317080c600c1d5414180601c000b140300e0302c1c201c6aa40140150710f00d0102c5c000c40c150301c0240340341d0400094036030100740405801c07101402810880c0e10300300d9005841c400502a81c4461004000707000090001500488a414003140030b190300403000700c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 300513462 1250 300512212 300512231
    0x9010903150609180c0b0f04030b0606130e040b0916050409030210020c0c0108091506010804050f07061115100b070503040509040b16050c03030c031e10090e0f0709 72
    0x401080700e600f1409040f0f04108249150030f902420002c1c1950045820ba103065507942c1102c541032150000810316981d00b0300003000460041070860b80e00400181c82180f90141140301d003401c455250300001d0050310751005000500100d000c0090380091002c009009422008039100b0101c1d8a5108851003039843d0000341d000c1610910080450f41041a1b042d5144d000d03802c905a2154100e01e9062300140e2003000181c2c00726800141a985900360300c81d2100d1a8a0b00801100e080100501c10b0714148182c10713414501c40c104004000042216980b000c80310000c0c0440541408843e10720308603513007558818030428207208406c2c042180c11080c0c50996a00807840c00c541140181d40c00710782c0c0040c08000b0802401100044940b00744003442d81c41e15003c1000c0750686650280040101d210b92081c00010001c1c4100c2e4001e54100001d100b03066090a818041407022030710031980710344e100c590142c0422016219005004200b0144406040764114244039607a07620300505c51402055160348242 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 300514712 1250 300513462 300513503
    0x18050919060f0611010b06090120060a0507030507030b012109061107111824041d0105090a051504061512150c2f151b09010903 56
    0x54141003100d50303081c0041592510031054095141c410f0001040074503907201c15003030040c45240045440100b9036410400908011551445000400780d240c6804841e4407442c41010009948198202c56001c42c291502901c0281070b01d4000d000c1500345401c2442d0800907a0f0040c0320022102c60090031000040a02900000074092000003c0d140c03620f0403088180f805550070041c980b1a00039010704890049645c1400501c500c0501103d003074415010118901c50340501441d1030303807403070b2501035803030005c1c2200010104c81d50107048061802c0d150460204c1005c0a000d0f15500040e044040c200d680029150142c88010f10300e4a560010307142400101008813076030100c207100c640c1590014110b501d86107540e00e9003c88042c00e49640c50342c0294400c81840c1c6002e0f9040708038a6580d41d150314002e025140d40014079900c245003140fa1505414000031800b00f01030202102e0000d1510780b41e0600c11000200f80b0407003183c1c5a40c01d4010003200c4206c0c0d8000c18200b0403207910550000c04100c24450a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 300515962 1250 300514712 300514741
    0x60a11030f07030c110a030507090b190602061f0503031605150405070305060c0a05040612060803030a060f1517130b01030326010f050d060b09010305031306180509 72
    0x40500000301051850900d40e00000d22100d01d0321405d100f4402c0901c042c104000c080d0a844020803c0c0c1c0f000c1400d000c200ca841d00028618031340501202440d100e10f90841100c0c10702504141c0059100204000e010b81103d50201f1307082d1004a040e13a2000e08280110741c59124407100c54000c0c0ca0241c000e1410440c0401c50801e91a14106a1440704e0500d07280243d00c4851910050300c1621649001ca44245101c00c2201c00381040c0e80c441600e89460501c040d01c180f1000d1080d120801c0da1102e0015000720240020361046403c9071000954900341700050b4034000440d0008000010903c0c01100301642000c0a110350b031060040c0024240c0c5c449010100c03001900400400a0508000010406030061000c0007400c1405686582c640e044e00079808008200b4454000030076450b001c04c1205007082c1c060710301d41c90700840d4003050a80c40c8901043c0d056601303a10407281a800003071810701707080200001e0030160071280b03800e007440d004604502c152206131f070103101d00c10312100d00407400200300c0c20b00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 300517212 1250 300515962 300515977
    0xf0206010614070818010f0315030b0717010902090103110405100806030f0703110901060e1809120f211b160f11040c05041811070f08071e02060a1103 66
    0x200c942c0d503443c4000c10002400c5c65640d0590103c2c0c42820195a203500a008402c0b01c07460341c0b041e80004502d1600c1c2c1800e0030070050565410b104919a0010542d012000c06c1406013034a00300240c1d854003444001411102e14055200041c6400d03c014015a6a44c0c6400da403211094582006540c540380c000038101456448640d005100e8003200100304084a02ca12055010890341c0b17445581c0e90f0788042d140b00202c1c403002e0350b10901c1c10140720a910b0440801e150014111000c41e5190003a14400314040c1c1d0042920b10b124060200b19880d00904401c0c4032607041c2503a400019050800e40b14240c4942038014141c40f401c400852920080000060380800d5030390000a813a1103040d003801e103044494070400c1070500443c2010706140313020780110202d40840308820b040148600b00c9400d200d0040c5078182001c100100100601c034045003541d58040d52140c0910340480d51682c8a20b800709072424207210340140e000c2c40c0059100585c1e906401c0c0c0300e00c2000c50800c0c80e00d50743c0741c0010724190b01c100c54 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 300518462 1250 300517212 300517223
    0x30f022a0a121104060f05061b19241118040f141b04082a0303030f0f090c0109061803060e030c0601050d08160305040f03031205070f020601061407 65
    0x40d4071418001c00c565001480c08042c0d90405c442612101603074501c8803d40995504900d0810041c00b02440b07800348140142c2ca16016214840b620000000401c44280411745006403101d40c0800d103c03505480c0302045c550002c1c0c040000001d584e0164216005484d500714040303580340c1c401050340c0c40d980c01220011400301d000b04568901d00510380e50400060300d040e01c03c4041c4800700c0303481d164010221030540700320000400700c08002003800610302e03081c204171204903280b0300d41620880d2410800346004250362005542c0c01c1c6080c0035002000072004050400303503880000d5440082e600403486000f594800e1a180304819501100c83e8a0b04449070b0000308050719040c03030f4541e4550044060702c4070103503120941d60141d81c2c540400000c1120400d02401c81c050801c2a525480701602244544500c24104141016520104019005541d40c0241c006c00c8103500c880100c0500740c4541948070029007460344d1114282800290f0742c5005020340d00038843c9050001400722800c4007a540d0003580074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 300519712 1250 300518462 300518489
    0x40c090c080a1b05030a090213020a0804030f091409091c0201021c1e0b0a0308120a0b0105070f0b070c060f02040608130f03050702040902120a030f022a0a 68
    0x1500007018101d0440d04124414a80003810816010700028040e001030582d0300c41e42103880e107514600c000c01141408036030040621594141d0395000b030014000c40002030310381c504140350508001d04000c4103003010301e081080c400c000340140c1000b1055003040500a80e10074000c1c0e501c0700d0005180c46a20700260901c00c43c00c010001c95558150004c0c0424030040d10807a00d90b58404807880281c5031000d900141a83d00154001c4100205038441d50403400010003080c00903590b0b8803154403503030061040e00c00340d0006400b0003034a00d02c18094142d141c00c00b86015450b24445403160a2a024a02c02c0104810221400315201d284280150348a454100170200407962003035a000e4002e521611030800452071510026901d030290000c800190f0b90008c60703000b020038503aa0101c415a004c1030040307038807940d0707003540001589031445034141d00301035480140881042030030041c0c454402c0c03402e5041154002600c00074446c03002003011900c041d0400b103840091240c040003400540d04d5410002c41c01d40c45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 300520962 1250 300519712 300519731
    0x4030e04092102030c06011818031106060f0603040b06040b0a0b03150303040609030b0c0409021602310b03030c060c03010e130804180e030a0c0201110102041409040c09 74
    0xc040440c01101501c080e8140c040c00c240b002d980744e01070248454060340100004111070b0809100d002c22001c00800c0000c2e41e8070704072800c0d442503039404005600213451004681d025000030807215401110071581c0074036204620000403000d00c00144010081002c0c0e201180058495402005161500410f0f0780a659180c0d190405560012600c0b100701030210196140c03242408021a400d58200341d441144250854840c945142c03c003820040403140d0400c00010210340520180410304100700c096030312100c3d0303401000464540c0e000c20000e050000317922000385415104154428644020000c10220260f900003415800790092130341503405070070200030885c3c030140c0086058031509020104035071906184101614000788006090140030081481041000c81030050720004111010404106100e1918190b401a240c3c04001c160a5880c1c20115a00000c5107044100c3c85002141090301c0c09404040404400d03e415001e140401d02140900205500110240030250030070b004081c0c0303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 300522212 1250 300520962 300520973
    0x80f070501051008031e04081b040c17011a090603040b0103050d02061603110d1410230f011412070806030303151003060905090a031b050d050304030e0409 68
    0x11204048625510700000201014109603140c420b07070702c41400039401e01c14020780407002140f040b1400401c241c000d0200055881c010804590100110040c0066107030604092200f585c491814110078401c07440e650001d0282054a52411140d41005020544148001c100314034414003041c0e40d003040d800030030031060000b40c1c05001c1c100d80c451001c45800012810049803141d1065070040010304842c15604100c51003500450840a0381030841440e02080c207542104035039414804581c03001c5030f801041603001030100c5403c0180710300c040c2c4041d812079400307807800d00c10f0b04051803511605407050300c86c910780d21075680300e1125190001c41c6e40c1c0d01c4118880345400300724100c0311100010300910002c1e1181c01c0c0442a280145c0703074031441c0300154145030108402d0449032241101050ba03a0903000903070b003040d8040d50740100b0307120307014040c0c2c170181c1c1c10001c00d26504248007284c3c0da04074204803800941c0015030bc0c40d030212985001c54594491f4a81204c0c4032010010b40e643c401d00b0070748040c05000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 300523462 1250 300522212 300522217
    0x8014104090b18030a0e010503060a050d050f010506040614041802090112110d0201020303040303200703051210080303010902070f1505090c04061505070614090304060f08010308070f02030a080f 85
    0xc600c00b0b02a10500b04000e07400e584c1e2040c00501c80000b02d414110281e40e50103403025540007a001410381e01d150340c4800100c0d030b03001200f920a0783d407503004202c00e8203943c2082c410650803000c2503406000c0141824460100d41503d9444103000e50342d590103142000c11424821141c1540c010904015965500b1aa0481d450010070944502c0100c2d98041c0040c68582d84d4051001c0e8183c020790f04541c1e41d80c4084c2e0040c807140c4410120802c64120b83c4460a51007001001054803d88074a51504003a40b241a41290300401d044140018098140030403000002964115004c0f04000350750f90b0b4041c9080f41000c0c1040070001e20400104005289000781504483d00ca440c131602210445130062003080152403e078420030360362013420090960054424802420f0a500642021130114404042c401704828101c800311040e80010505104060380000b44420396100c9241c802c22039411a259004d891141c03500051041c240803c1200440d1014422840580c0d000392200307031a030b00144076280495 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 300524712 1250 300523462 300523471
    0x804050709050c0a0e01050301051e010c05010f06030c0b0408030708030a15150206070c02100c02010302090319140304080c010503090f060405160806041106161b0608014104090b 78
    0x42d000c0c41229045c0d501c44c0e02a2030407180001c1540b02c0c1c1c3c03249041c8944480e88c1084040b41040340d5032001d200802c80074000c50003822850700000440b00d103542051510304280350454001e1841c20001009040d20000c240c0f07090a80010003143d50703403200d0110070001c09500d8151130400031900800038a141c801d121001c2c02c10407640036981c40ba6601c03070003143c908202e864001d600462200d41d40f142c941c442c8580580700340c41814018600401d1000280c94058034280615085140380412701c10071400041c0d40d2210380c0c511340214100341c00c00b0707561921010384090303c80c104000440003404c1c1c0101000902d03841a80441511140c0c00c050918603118841074114070340e0514982c40018803076200050152080341c00c204d414400c84103850400101c2e520005844007115840241d81c40400d8040b03500151a5150034540b404c400d1400700c001e1b140e2401680302c003c065051000b44c48010546540c82ea9102c50720502102c010740103403044d900ca10b08411071072034101e031510039610100000c6e0807240303018 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 300525962 1250 300524712 300524717
    0x1203020706080f07200c0402040e07030e0a032a080705060106030e03040321030608060906040506061008060d06110f091819090609080c0109151505010804050709050c0a 74
    0x2e42e03078000d0300100303000040e101c2a000481c084981c04044420f198040079241c030450035141d000381c02c4800034007070340c0080e004500d042e405071080c0414150103210700546840e1100c00f8161040310307520080d0800f60802d001000da150b44006088604071070380e18011f4050f51003072056440c0c6006080030f680e561400d001b1440880d01d0b0440c88010504c0010685080b00d91100d03101c0206903d58036004103110503070b0b000d45c091546940010030308440a011440c413404102e00245018a486d0070254178111000d01091302422641c07400010342c030f521400682c1e02c030f64191030485a01e405881c10f00001c2541c44040c1c0300610b0f021507821084031444000b00383c1c0810864520028101145000c401840306a444500e0780542e400c005403a0081c607000408000c1c06441c00149036000c0752106a060361000a07810116550307282d00504010901604060b055000b2404000c01c040100f04005000228082c00b41030192060009081280403c002d2000d402c8100d405d00260800055558503500b018490601 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 300527212 1250 300525962 300525977
    0x20f0903151009020d0e190308060103090b060915030d03060618080312040f080f0a1206050a05010e2e08070f12020f070605041b0609032102071203020706 68
    0xc007128400111402014054100b4903202d2600a0602c002e60048011a8101d521071000c0103030004107114902880c940b0202c2481e6021003440c4c014102000180154141440c0140c07000c08203ca01d61380690019090ba00416240c80d074012105000441200c0640c1c14450031400c0004103605070000c400300c8031691941300003500303d04440480c0e548140641c22041c3d109100c2c0782201446402d045400138040e0107081180100764131a0461035100422010a1080004a085500741e001e0058802d0000340741c010001c86040100240d4504030b944111030400c0503010f0085104c3d0380b40c0980746803001c01d402d981035102c0341c07181042c0025004056544007180d058400100302c180503042a4688812a6882c115550020445107009400c00d162080c0002da05000b00c10018100c0e2181c07038019401602c40900d101564146080c519405030081010030881500800029144003410140c4000d00303402080081d031070000481c5030154542c80040c00004d002c0c030050030b15401194000a43c0c081381d13110030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 300528462 1250 300527212 300527233
    0xf0608100504260c0604030201020909070c0c0e15060316030c050c070e04140f07030c0603140c07060b0a0b0a1b0f0201030c03021303060b0a0e01031e06020706020f0903 74
    0x8039a012200a400d0f02101d20705840d80c54480c08402050348028031040f424401c03000c4202c3e1502c0c0d402c9400300c025030b6000032170350303000c0c90000c1517240c0c040213030b24011084904c02d0b9280c0b8100e402c548200007e80c1d080c40089280030008072060499000301624480e16854422035031201801400b6406000c2487c101000790030905c50300854001d0a100c4c00141112883c24003e1f54500100420a59020040d40254840303000d00340103001000b89a14010600c0c80d0031400c006103e010580d02031024185040070810b811400c02c031050340e11075090003240703880d0302103818000042e04a4102c0b559101c41d0101e000324681c840c880c080d00300b60207540d03240c501b003075806070f40070031548003a05002d0304110038650f002e401580310b900440b01c0640c0c40d01d030150801a81e0341041000c89295041100d1103030310b1b0380400d00182407a45a1100408205500120a5245841e000001800882000d01e400341c44180c4c40e043c041e440c1c04403005280d002c8002c56440c0030307400405405402c072402c21803003801101e4420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 300529712 1250 300528462 300528493
    0x709050d200411070f080f07120210020301061407150203070507150c1b030e040507020c040e070e2406040b0309060601090b03060f0a030b0901020a110303011401030b04020d0f0608 79
    0x80c88000d50800380d4a107011607540b603aa070845c010320b03030031130340c040d0100071120000101002a00c20345203e0307003070032081c010f4481c80603013066958000c040074a48140010040e159000140d00c03070a80c0007100b415030707498142c10541e540003c3d542200428074000000e100d40d45600c1001820070f40e000300e0300b0440d014004010034041c0e81d4618441000030340d0030340240d1900f00300f0325180c1d19114828185644a90b03607420100f410b0701d00884000000d0b0704041c000e4032440c105805000700711503188000d000c400b030411046150018010b030407400c428030291241e480d00112280050310000004084a88030341d41c9000c408003e510440b83d07450305001d5a030101e0555405142c44a090b202244030103400c540d201710501c11005c1e804000c444d407000d26a0300000c0401c280040c041d005244034000940d481e803020703c0c041c00d4a10003504101e101d500800040050403141440141041030919001c541c080820700080c2c080e003d003d00440548e454524440d00700d400755407050044806540035568026805840c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 300530962 1250 300529712 300529721
    0x1507021c0c02030601180e061008190209130206071a010617100303030203060a09050c0309010b090106020a0b190513020103060b120c1303050a0606140a120b0709050d2004 75
    0x7500f41e80030780014084801400c000e10700b642141040064044840c1c1c041c6854610300350783d09041580107040c10701034000180940f503400010654284803264041d8049a1800700c01070854914003071480214046544443c112002241c1044044a1440e04080c02d42d44442c8288075050120f00340f40300b1503614020400b0700b248944155010f69a42c146540c6040e00603500040c0055030102600700d0100d0003045030b1141502800e2815082610f034070f82038a02d6421034103820305161161049a0040205daa800540505815448681009152503208034001500600707200e900c1d019081408101026070f41031100d84025000740c0c2c00703204141d900c6c00803007500c1c810480702403607075151a00040c000a07081780c010080052501c18440400ba83d9849490404190020031660142c84400030442d00300064014010384604462030324405180c854400160001450002c00c410a00ca001031000c0303010358000c0d4002c0c10f003d0090180400c1d84c0c604000383c40a1040d48050881c2c0500c0c0030350590401b40706 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 300532212 1250 300530962 300530987
    0x2062116020d0c021906050327030307110a290a0b060a0c050a05061e060102240709030209010f0f12030e090a02040504020d060e06010c12111507021c 66
    0x1410000340e82d0b100856200f640200c069800031200130a0f10520b4481c00d80b00d0005260326a1400d03104d0a1814010404060f0250100004c540c2480c01245242c0080101c0303420034202c0c00c1c00c0600010702c0d8105070510480303080241c001d18100409490350f5034407061072403011542024415503903031803003015011145001401c541080c02030100c540b040d070040390400341c4240110304450340030000d651490f140c41c0c02145d202101500c1101006e0002030340c0520290050b0b4240041d04145104078422001d0314802d2050427050100320740468400c134050228400a5034016041c0c146a40e10781343e25500184651280541c02c03110075000180d400090240e00311400e80c50b0751003c60001c45142000034564028180e403662981c00c00000880d56683e100428045164180c04100c007071400111100d0304100a201506200038400042d00144c20031a102003c48954140035a643c01c0d540c6002e403800d010048d017a0b81710603d0106101d0125000a16545100c0c110300d0841c1c1c03620010742c41260044564007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 300533462 1250 300532212 300532217
    0x60303020613060609020307020304031a06030a08030612010f02130806010807050105130e0a1b030207020f04020d0603140a060c0203070b0a0c0e040c09080d030212040b06040902062116 81
    0x10702058a249503a110000d00c940100404260103845150710001c03a4010f5070b0074070140c2d0000608004111803005040c0f44034550741003004c0f140c500750001c01d8592441c150028034640300000020003954034001110030701c11084000300041e038410b16900c00298080c54042c1082400340344009588007000800c40d0503035040e0700103005032070f1074800150b40c1b5401607000882c500380c02c1c500100349001e035920181c1c801c0fa454400841e0004007100642140c2200d86100c1040500410800c805620344201c04078441c84c05840c010b9803951450610001818907410082640c00d024480c00c1401400103201d21280d03000d00000c101000e0300e00d13400d0fa036901c10000001c1504030a140020100c4040b5408038506141700d081041004003200001011100c041c243e60740811826401400121002c02c900d0340508080d0504520300969030307103003640c00e0100074802092200800300103982a2515041900e030250b02401d400d844110080781c60740440d071180c45040c038400c42500001c0034448140340c2d106042230183c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 300534712 1250 300533462 300533473
    0x305040b060a060e15160f02011409033d090b01050d0f320307151802060702270a0b040510121a070306080106080f2808130501021006030302 62
    0x10000e12120f01c005c14000c0740b07012000c0c401c91003d180b00f800401100b504c15a13030400380350814400945103845204102809000600914806880000c1c104c03640100500f102800607403411100128580d0b2120615240c04404080404a0625410048580d231040100301c01c5aa01e40e000d00a00c07084c4094041d0031214000203860100c7c1481c200004450f10000a10144803640c0441052031000032a0001480d8400030319402032110182c50580704108480090100541e0104c05840700029400041d201e801d0000f02c070000c540d114030b01659904015108600d401510b0600740004e004201c3e001001c560921419161501c0c1501c03a0a02c03034148004400000c504103803500c4001440d1803411102c02d9100109034a02d44d91040c43c0e1403182015980200d4802c2c1403030071150035100c03030368000c400c207501c2001c0210382204040707404041034040300350040078524141c019a0200111040280040703100041481502d00403c101c007050f61070070380880c0c0118450070140c03800c4a03001d202c0580146c100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 300535962 1250 300534712 300534737
    0x210e040f0504050d05070c2301030b0a050f0103020a02030d05010801060602060115080a0b040221060a060c050618160801020403020f060c1b1203030a06051f0207050609130504030305040b060a06 85
    0x4201402080b0f00812004034441d40f03d80c0010b123050b2040607d054628203403130340d1070440d41e0306000e47c03a0380c800d003914030075107651070240482d40d00d14901669506250300402e181c15514400c0082c0d44501c0e21829080c0087d594445480e4020169409400014028000041208030050f00b058012000d40c0c0d840c40b80f5039594282e40b0005200e400b17062548a902040b220300744130180c440050081c41e10709021610384c10f00800300601956994060414003000411160115102003452750b40891100403074848070040c2c0f840c4604000c0300c03200c1c04450100010000c81c45107015030140054910a581d0765903800405020400030b4002c2d00306920099001100b40c2c0c000310007488441c0b101c0e030320182111020410b81000c9c242580c10880300d04070042e0795000c040019182418881082000d0807000d1101d00d81c0c4000001c1d12940b090003124080e1a00050300c99803a22070382401201138401100803c100c0c103080c98010082c000948058079488044004282c684c40d00c0381840c41221000e44844007401038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 300537212 1250 300535962 300535967
    0xd0510171b272806030215030405160905090d0507050309010c06061d0613020a080f040312020703210b06070b04020d02040c05041701091a04210e040f0504050d 70
    0x550070805054030184036425072200514080d0385020380b02c2e1143c21100d050b040601000200c03000d2900380ca2043c20600c04102688070800301203921880c0c1c1075900e07070780da883e1302300645030265000c154a0078081e5504005801d030916840300e030141150704c041c0e8018580202c0c040f207042c000c844020700190010013500400750300a804120032030313128460110301039968448501d68420b4002d210380703403a6480000c1012030b00d0b2103080700c80090440c81045003041c1c1200002031002e00020920070100c640040450141401990b01c0d80e00c0c3d0400180035581c0e5000c615006100c92035181c81059508074504500d812144a80129125450302030301c903d041010a407220348050f4001b610590300403203071040640c050303140c0380200002404a51116a943c501e008850280e101c800042860765900d00344074440003600c012648109903070710441d0321246d40c03210b0070441c819040741c0c14980c1504e58051140b254a581000c1c0310b0261800440c2c04016540000214800f13440d01210020075030340089244050050 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 300538462 1250 300537212 300537229
    0x1021519060803030a020405031009030e060a0504080a08180a050123090d030302090a0b090a0605030a15030303051b0316050307120e030319090f0303110d0510171b 72
    0x80044001c503855564142c41425603005807000342d0b0a0f03400040c14070107420100221441554684010802070741d0355100206501c0c0f912068501c0381c0c00015800e144240700e1818ac0d4080d11010042d0b800b82a41071806910076405035629003c144903000c1030a41c1c81c41c0c010a030400312001a101c203000c0b00151a50300412610594810710381d401e050081d01001d40740c002034210910700c2600c0c010b0382d41040da010441c503070016500c45040e018003002482c03180d0315034020741800c130741150603c2501c90310364001c4e15001d401091900820b0b010700f440c00006044d85a04200d0051342000d5112a0040203228660114841102c0820f010b90160060285203031040d001035030b0203001403428032004100084240107880d40e99240020560000c410f0108a02d480c0c4003000003c25030140400c40c40f902980c5842007220a84800b40902d603407a4a400d451813000c4049500c64140540200b00a1808040c19003040c1c0300360241450030245050801081d4200080b045c4540c52a0600c482c1c0d0004048100030910 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 300539568 1106 300538462 300538501
    0x53a0804080f1516050a0306030b040c060801060327020102070308040f15030b0f040b010905030316050c010203090915010201020f0c030d11031006180e0412020705010215 75
    0x10000311344003000c503122604144d40c5131149000190018031080c0d002800409180080000308030300030480d031007943c0340c41d11481590790320703804114103c0da80507030038003285504280070081200c800180e02c0c1ca41c1b841441114445c40c1c40f66100c40c00c03504594400c05030b81d58a401c09102d105003142c15040c034015a8a4200b141548110010310180320100c61a8082d82d59110100307601d910560b0114080e000c05030440303540d41007200b102d0f94000290740054a40740180c81c40c94250358400f10881d820301381e00510750159a12078208038010350009004190656508001d69414041a03001070849208444042d40c0c46019010012054a0481c00c50400801080041090741e00d6081000802e8a0340d43c688041c141e04001d03102c00c1817282179040802c0141c4420104010000019248581e14a02c1c2d400e441c3e45984c0c3c1c000699445046a2003c0203c520f0400052640352150920f01c005 = true := by decide +kernel

theorem cover : BRFrame.Cov 300359712 300539568 := by
  have h0 := BRFrame.cov_init 300359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 300359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 300359712 ≤ n) (h2 : n < 300539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
