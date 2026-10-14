-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0859
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:13:06.225632+00:00
-- url     : https://prove2.me/submissions/d4fe572f-7492-4f7a-a735-a5d978f57a8e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 154316546 ≤ n < 154496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 154317796 1250 154316546 154316563
    0x301170c0621040201020703120306182310270f1b21060b03180c010906050c01150806100e01260f10090c060e011409010504170c0307120302 62
    0x2d00d4101d07000440c0a59000b4020100551f030441401542e0000e00900580a403000e44200d0701d03401003808100020300c840c0d1013404402680100101c0c94904a00300603c0c61000141040b0b520082c130100006031704070044850024100065030b038103214015480b14604039130004454030605400c100d4441c403075404c2246494251403190600100c1c10100c54440041404c560700f007043c0c9145064004248080c2c900007442c49401e203400d42e200085c48180c601038842c0c02418456020890a0070107001e0540910b0280c424100709100028503d04000c00418048100760301a4065070080d00074489040c0000407100b000e0300c800000d580c942d5142079022404000d03d10900e01c1c0c2030f410710152544801c418004400c3c00c516032800c8846030011241058018800110100d5040312176000006656004000f040c0c00f0300f5050310360001c9420102c006203041e50042e881141048010480400d000c2a00d51826482248040040c003580c0f04032020b03d032178440690428644041140c1141c00040c1e40020300c803c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 154319046 1250 154317796 154317847
    0x3020306101b02030a050f0606030a08090f130213030c05030102130918020a03120801091803030c030209150301031421090301110313030e0f2b06020301170c06 70
    0x282d08400008540c03400c0c00030000950601030b0068040501800040e801008100f81040e50300c01d031110020141c2e0380300d40d072500806092042c00604001c0ca0070002503940758401030b041d0300b501c9007840b14001c1242e000006d182420420072005006001c00360001002410b010740086240000c0b030750210b50004480d1003040a03841d10744201510b42641013075601e84150780941002d0410340c80e480c2844800b1410342841c0d001039048800000c1c1808a40101c850f8034582401c08003240b1920f0b00c0403000b405145e140030040c036800b0010f0060315107500212001c4402d021003965120350641c900042d50713815100b01e040c0d1907403042c20140b10120001000004020280801503031350111000424007402c180c414444540c100401080700080000b50721401c2280300755109901d09041000b00400d8108181c0300d00c0d0000e00ca6201c0181e031240e03012480303c0c4046149001d1000d8001c596803041139a00036003104554802d800301c814400e0300c0410285000d5101242d00d2402d103003200701114600440079000300d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 154320296 1250 154319046 154319057
    0x50d060f0f050f060d06031406130b0c090d0b130c0f050114071103010c0c02120d0f0c030e0405010303020304060908060708041709030a0c0f0b04081b310c0302030610 73
    0x102c415551300040310382d4250382c03500c107000990766400d081c0c11045607086409080d0040c0000181207040005040d445950f10010508542d240c00c0401c040b07075003103581c038640c00802400c03445002c1a21366241a11406001f01c01171719201e007600d403000e0700503401d52042e0b11071861011b0901050782c000e004070000c0b6284201d500d480f4207a40c14880c110a101c074072603680551030b184101f88441c0e84040090152402074800690600d108107d61369039017007a4140d280020811000c80078080c0c412a040428a8000e01d8941c0d0110506c9000030110358003a070089000d64800502004583d4010007810010460b00c00941850320f05460050801d001c010402005012400c1c040c10181c0e003c2801d81e040400702600312403200c0c01078682007040c001c0900511000504610002400902c0b1000b2074055440c20320180407840c54052204002030004403000e50b1020456000e209803403090424600000303d020b909502c00711101d000320b011114007011001c10103004104000103621000501c001e03203038182c9002c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 154321546 1250 154320296 154320319
    0x705040b0310020d0605041b0c060c020a05070806100e01152d2f03070204091a04050a1b05030318010216030f11010f120e030409020703050d060f0f05 66
    0x707410b085419942400440c030108541d00006803903481201074520a440401515401c00c0c00c00c00b0a06180361120f0004049070b03442e10014940b41c10500d5000e01c0c6004071400c03095551345540c201490341e08100d0031544190100030f50b4010b03040e030f800c00806905210f03a40550401081c034910a080810345d409015100372071a098031360031460103281d00a840295000c1010001c0020041400d000c1c408440f440d0259661001d0395111100c0310880003036034011840c26440f5421b1001030050b000d800d41d45000c20340f40940e00a030a000605215900c03500282c00b480380c0b1450f00381001200d03c04d40d0151258048000d11141d180001160510410003001090740782151004074980710b461403c042e9902d00d60b105c0003040011440c1040c3d00b980c4108440c80e40c0c158040e00448403000ca84d003a150009444080407d1014040c0d0700c60484c00c1c51107000d80e4601901d5040040990303000503400c0340020070004000c100414240305240c00383c10b11750b080303500c0c02c5d00d44458481003c000e03020f02441600903021 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 154322796 1250 154321546 154321549
    0x10e0915060d020412050106081911061b060f1b030406020705010b1003020901020705040528061d01080606010c030203030c0a03061806050112060312080603030912010621050705040b 80
    0x40c0c46808007200003e554407510b910403500d440d21801000c0314150b080c41d401251610340031a46401042c0c0801810f00b10300e000ea196601a07000c09090180c100e40d0400002450b9052800d8904480b20088014850342c24220501100240000d0032022011600300c8000c42062120702180d80145e003005003d602d0b04881e0805600603c1d2804c41ca40c0d100400311089001a50583c02030301d0044000d07000d132000c0d035a4507414002035490803200d0120102000d41d0b055016803014015000310f0701d0504000481c1f5494031548014107610906041d0042440001002000420042554010001c0ca0210540062640c002c4e40d079002c0a44201c00510020503a8001a88644d00080c024240030030711903116500c0900e100020851030003042d0004906121441c0c00607070f5030080c48103e0340e00c414203040c070b01050181202ea01801501003a4540401c200404c942d40d203c5006000c0303018018000a072461900d0b0700c2c07d80c22484150501c0c120b810206085000c04d0b0081042c1044a00589020451031110780 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 154324046 1250 154322796 154322809
    0xc030c0812040b270d0f110303040c0e0108031e0d0e0604060504030306120c090507140304050609010e0c0306180f120d060b1206130b03010f050411010e0915 69
    0x4424000881d04502080140810105002c1c0034680d248810302c2210a03001c80041c054400540400c040d42c0702c180d03007002551045104880c640103e14045008404003451541190301c19074080d100d0081c100801d110050f003400c400740c0141681c50055144c0034105071640c42e100340d400212920720b9030104041e501c1d050503030003091840b4402c005541d1180b9061402d10020401a079050740001d180c040040b8452400c1259070400ea6000703449a030f001481c005582001d0701d0020420002c222051a070b2000302d00c21800610f006500c01c2c0098843da20b0030003d040d00b1240d0f00990200c6550041c0020311854502042007504504409105050203507111400b5180401e8815825805d1141a401414490f18a0041c0428920700c980502185035141c140b0519030152030056040444210045651840d040c1049124110000e4000c50a007107948002821038103181c0300c120019440d08200420842c5010340220700c24824200782c8440100d03000411161000207100d071071032000428035092140d80c0c02 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 154325296 1250 154324046 154324057
    0x180621080c010e030c060106020d17041b0605070302100b01120e0f0a151b2a050106060507110904050a141f0c11070317090105040803040905061c030c030c08 69
    0xe00203208807142e00f001030303544c0c0c0d004000c524014052800086600c2e84046200d002000282d916410602c510940c2040d1901020b801142c083c4031115100c071f060b862003031048000b0035003030303c0d56503d07100c00b410040e040178119280006418a4042d006c2c3c0345a07013045035103d83d04140080000c121190301c0c0914580070340251280094801c0721450401c122035540035119020b00a42c0610010901c0c0d50f11350f082e01b030440d8048001c101e01510714807460650103d50110320030031004040300c1080e6a01e0b00f500b100c14039080b10700000d8001a03040140040c4029100c2400c0007518002564039254a906442e04102c4c44020b002400007a006941204108042152640104143c80c1c0f2081c281148800900034030b003128000c0341e80110900d0320b623000480c2c2a41200e0700103101c4a4484011090780003d47c1c000310b43c0740d041c04028003001c28446e1b0f0410107000030f8503101800007aa0f0030504c0400c5441b42442c0d03503482405094a860b0380000354442904108641e141c1890300a80c0c480b45000342d02030096 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 154326546 1250 154325296 154325317
    0x20d140d0504080301030c0b0403020d1e020a090c0f1409040506010c060f0906060608090d030b0a0f33020a030f030e1b0907020a031706010302070804060918062108 72
    0x81106020600810344004e504881c031442d410120541e0340c94070055540514071000e0b5000102814400108842000710b6072600d001c1030220340010220382c005070b001407003074200110103030703480c40080c0515030001c0385d0790441402400d0000f50b00c1c0090380c200301c15129107020140140d4446011a000d81d02580c01031001d1948a00c00344500800c080741400101280007050781e400e400c1500004070940100034050013034a4017009850f501a01c000d040d4054099084015004900914002001c00a0f07240b40f901510100e02080c01207040b0700c4402d5101c225500c2d0f424800041d0302c03848014a50005141d101c0d1940c141001d800342e9040d100103400030304494000035100c0c00b031883d80042120041071051414501141c1e400300c61b1710750050480e6580050800203001c1082e61180503080401c1c0038905130b100d58145005407400b0b085030340380d0a0075005a40301101086120f942804854214040401e801c1d8860a041010500c0c0c00c9020402c240c4211414402441c0d45a001003840304241c00c0707801d100c81 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 154327796 1250 154326546 154326551
    0x5033f041706070806060d0902010e060a0e15030705120606040f0e061009150516020d050609240c0703140a020a0201180506040605030903040503071502060702010606020d140d 77
    0x180e0310007049440341c0840c04041240200d20008102d103000303a81c401d008040c094040c908041ca100c11041c028040c4460903810b0180c1101c2e02d401540d00c010050440390b000b0341d82c070301140d03281d0014010044421003440001d40c0060041010807a80402a0313804086c8101c11051280ca928010502034441d40d0025a880104000041281d440d0340c081c0354000d100641d640c1809460740b441c11034850b5030a008442030f2815800003642114421000341c4604141603444080ca0061a40061441190b098080301d06030001020099241030603c1010600c540100d24a24403581c01c0800e10348042d030080c11101220000310b02d44041c544694014841140102c0500f0b544182d2040040d5a07418000c100b00d00207811103102c0c010b890402e6503a0012184040c1c821400c0074107081e0b003030320140c1000700003a48910051100103a284c2c2c3c100100e100804040c0381c41d07070005492540084c18404001c118000b9603060520800980d6400194180034200d82e24144207294071040000150b44500d1b02d98602490 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 154329046 1250 154327796 154327799
    0x6060e0f01061106010602030a0c0203010b060d0e12030907030f1506060e0a0b070c090506010c080a03020409050f0708011a130b0405031903090b13030f06090201030605033f04 77
    0x5152001a81a203600e502c0310542000f14842d21a60344000b4046d45005070070910201b140d840c05048a50095840140049103d858010105440ea00070f0b644510304a5101d41c02503a400106214082c200403001030b60f0740c40d40c41d00074515951483d45110060421120311f514030f051040c01085140c0000188400340203080c2d903107a0042c140711559492034840e5000c030034000b8010303604d00100c4516507441010040500e00d400d20550041200400381d50501144034100400981c1c02d42c001c103010b60f01501c0040c0c6440c01d04105a00303e0b1001045503c0e0042494288000550030100d8181110224000105148540d00d110941d07406030440000c010400420301140c20103e040290058030b409404640c1c1411138500e41c0020704034880d10140c00303c0d00c10942404810740a02c000e21400c00c40303030001d0310b203a9070300e940780e54032408000d100b035408965465407007007150390501074900140030890040c40c1c0c01b00100d075501d000003040750140312182091580707002201b0b14062000400810038014640340c0703 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 154330296 1250 154329046 154329061
    0x306040b0106080106052d071505010e0708060904020f13020a020f0f0a080a08090111030901091703060a1806050d0c03140105010e04030c0632060d110d06060e 70
    0x103080c011040030075015000800c03610f104900b600c0400c143c286003406848080d501c1e006005114884000c1c59910420888000c200f62203d061402c000513a80010710398908078408a50003c090808002c100344501404403554800425507002601216070a40c1c0d500040e0008880d0020500d0690509001040c0014040d03000302d5042c007128449015200040d21480300140c031641c0d545030090055009124005003030748a068440c3e0701c451840000540110314400c50302d0203400c00c588140b5543e442d50046010024010b8071508034944960f0402d045061076000200c441090303008201035540f0741041d070240400d80c0e401800c01428064841240d5080904003441c052540f4041911a0510001c062008400c1481518101c1b4111b84080d82aa00c1e540c2d0110b07090101e040050312002d441e00e00ba40e03018000e50b0040300c90520f1185821303e80084e090042c84541c0e42c020504e510400350703100301c400030600203a05145c08440484154041d00032501e810b10081c501074000306883c1e00303800d0811a91 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 154331546 1250 154330296 154330313
    0x126010f09050a0908030708090708030f1c0c140d061a07021e010906050a030207210f0201050402090402010503060a0b04080a0201030f050405070e07140309010f0c0c08040e100302030604 82
    0x60310300300d0740c0900065494121000030f031488190002c0c1000010400188218030943e03080703130440203003815503545030b0b924151a4a1030300300110040081c08002000640c0c800d0401c0c03041409208282c040c081c1d5641d0490207818541041d030100003460000481e04551541a8442c0001e000a0b061040c01042c80c501000e40541000d20124090a01d007002c1c2c0280648880c4080c070240f5059485074142401c01c0e8040702c098010b240300343c0034035400307020710300005070100139042c5403c0b400d48903c0c038080702d10340740142403806501c10b42065900d00001c0c0405602da200045a1240d0207003081a40c0e43c40b000045010b151265111841e11030011501207281c010100d040006a0b00136642404411548007841701255800c1d1401032041c3d1041c0003c0002303071020406030340d00124030704200d128281001e145c486540d004a6400140781d5443c1c0440300381c1c9c003c03449400000c01d080e1402909001036981c600700c1c90320440c010805d1640b131503400154050045010380d4003450740981500c1407414107103003401a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 154332796 1250 154331546 154331549
    0x3110c0105060102010612120c0312020a0e130e030904090302031e0409060f08060f0c0c070e010512120304061a1020030309191119060e01020a0206090126010f 70
    0x55013080000200340128020200c901900708c2c04406000702220b1003030b114121101001c0b820f05c07002503000d1001005501c041c200129941d181c02c4440f1380ca05080048803842210311266030303454135942035414070000080d10380c010ba0a0f10009840105410103a00d1805174158001c0c034480b10190030540052038030701500c00c0b12700500f41841055122010300e03402ca030180c024290140d00200000c0c1003800f000e080a6040504c000b1054501100880043c0c24211290050000e41103008010031190501e6003240c0703540c801501c05840044c1c143c03070000c5814800035001400894551900885005500d440f11007c03030300040034880460718012001c3c0c95100c0b042504242c5010250521490140100440f40300d0901540504032200140b03032300c10b000900da824113540f00004828049425110b0015090003a5005410781c0c1225103018401490b13501011010390440d00456042c07030058642e01c00740c9890101c02d00304110001c1840300c0c5850785c2c81c200d0700001c80d86d0591b50000941d60016490301c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 154334046 1250 154332796 154332799
    0xc03080f0a11010c0f0302071104060b0405090a020c120c10050a06031104050702030406030e010b1017090706020604031d090703020c07120803010504020f04031b05041d0604110103110c010506 84
    0x4001002010b070a500700c0751140c0138400807482200310f40400500c80c2d40142042817040b251140c0354240c000105003200e100382c0204400002c00602842149407607024264007083d41d032825440e081d0141880c0340c5400681035054006003021440e03d14496061002e21445499044204000d00d400c00d18407001d8031241c401664280b8a48094503158182402464412040c40c0c00079480d20f0b01c1c0400403001070031010300c08010ba5590b0907082d0840d50300e400f00e610b50020103a842e180b0702c8040e646401040d40d806049000705910924040005640100e00d1aa0240e018140101080c040c0940d04240d0380c0000d4007542e0188009042211481e0140c2c0644071862601c4110740802c1d0320b945444090904002c0b018007a1a41400100300d50315294000b0104a641f40350f0700383c2055926a036103000111074450807810802106024856814a446251400e82e038030700d034055400318020504c03516808040c201800d481201070581041e42d01075042516403100c1e4040f500c1d6a615208201d600801c2d058541a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 154335296 1250 154334046 154334057
    0x403021f0504020909010218011206030b0906060a050307120305250f1b060804060216020901060302070204050708011508090c0d05030d0c02010603080a08151206100503060903070204090c03080f0a 86
    0x485e070000510071307261204140010030204202200040d26141daa0061003044251180008000524900c100b01c1c01a80ca050040c40036040c90020480140c850350000b6029610040f001c10040c541e10a1005501c1c1e010306000c1da45403045201d200c2d030400081d0300d00316000d05842d885810083c1c808400e40d1094001c01468a100c4072036004a41c4401c4a8442c54000683d4400810081a031070741c01000021861007510100840940c041000c0b03041c2640101c000c00d07404210902941824020709500c40e150b490600076640c10710740001c00000700c2c6420381c402c10072140c2c00038400b96410020310815180c01407900c042c081c02ea207015581da501888680b034489090601c4a14018014080d910030399510042076418808201c508440e41f01d0020684900c801d810b802c1c1d10007646880024800d400100c50240206c2d10b011302499801c2e902d158410750103584608100409138802005807003459504540200e80300280d0b04011400c100c41e40c1019080c1e110008a40600030790790701c02010300ca00d1540382c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 154336546 1250 154335296 154335301
    0x110307110d0305070903140102071b210b0c07020f040513060e0105040206040611070b04060324030b06040f020c1617030304020915121b011403010b070b0403021f05040209 75
    0x700c2c180d641c240c80d1400403421001c0140000343c400c1c40c11880144000b0001401c02e0426140d11107140702548460700000003a40085c07110350009064020590701700c0c540c49650b621940d807414191540101050318203c00402d11004543e14000d24800c0d01100a00601c205c1c00c02c0c201951701c40e584054103c50051502e40c22060200060080b18800c0e500109000d003030601e07040041e51001c01282c06d8015074000c2c01c07000b05400166202030409032006913030004260300007001111083c3c446a903000440b1824800030000a200039030711680c061819507000c0390844420305220045d0043d9603004096025040d500700341450600c10344400c503208030f074119201101001000d618ad21081e81c010b50032000d50300004089100100280d01d0000014003196000040d0604450424810301404c10103025244e1080400d50b0740f02141400c07483c6a00c2e0401d28651601d00c920310b080c89220001080d043d0b510002500f410b0080c0001000c2c1403807401000074099004030140c00030802200c0032031003164100003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 154337796 1250 154336546 154336573
    0x20918011a0304020a0807030320011a130209061b0d0908030f09010c0212012a090510020307080309070810020a0c1407120506091b0315070311030711 66
    0x50040c100d407200140c15141075a00000d8003999403000340280e030444000703607000841000c10029400158000c0c0e541c42072170300c05126840044c142c07807412070f1083e0781050445c21005108140044214804551000340101150303c8000a40582502940d1100000c0380446807481c400d040d46108981c00c0c0103860804200800170345903090340d030090051039481402800c600743e028800415182c2d0050505e0031409000b6400540c0602e15401e80a03020b9454440980d601460110240f1580608102643d1882010400100108100d105552040703084040510035140240110303004990032021550b0707246400b0500aa5507191403140381e03503d1060b040c0702045002c151090321071624a0740d950214030340076516601810840040100260b025141000402d4401c0c440c0901041d441071024140d24a02107001504200703040d48085810220040222201d80e004101408040208400d040541c2c903007440407402840300403006603800ba00003040c01040c68002245901d414500001c56041010100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 154339046 1250 154337796 154337839
    0xa02091807110106090e2e0902130c02031c06060509060304080d09030507050606040c05090f01450f150302070f0309050f0f0f04110d05010905010e24010509010c0f0302010209 77
    0xa07030108034003e48420f0842032851a230880f12805000400905a50b100f80462030201e982e45180c860140e0f2000888200c401c1c0d00b50a210b21494910004000d894640306025100d44102c1010900c1071900000080400400d0819104403035401603040105003407a00c0e0203491588602c00980d80703031041000003021441c00e40140348041030a0b98a0038103084d020004d100a01d5902006541804150405545003810640c405540302c0d6041b10540340304e8241d00c510041c0d00c906100b2440d0307603601d80346050142c40a080b40e10030403501c1c2c400100c0e07400c00c103a240c210000d0042c0300b801044084244600c1e41403550004108007a600100d99a0040b02144002c100015050300c050540045a030400c80c25580341903400021140b0042040c1450000047c1d80d010495009070001c4544a81d554010321048008880582d4000c074205980007409540842c0d500205c014003207460704015001601b072582d64456440c0340a0346d0380c000340b6901c00e00d201e450040e010350401810070b4002d942207040e03a4045850a07 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 154340296 1250 154339046 154339093
    0x301181a040b0d0f060b040f050105090414150a140f190e0718050405010c110a020d020a09150509070c110d030c02090c0a080a02091807110106090e 65
    0x8800350251000e00c0007070600075000300d9000e50035441440106a1030b92070b220b9898860200000c60750b80d074000f00412622540f9165166500e014010322164854095403034009811800035151a504031002c289040300350f03071286490b0201d440510030316280f50341280340307045071000c203c400c2d95507114215614403108071940303d4907405518844030b0355450350340f0881d02da050b10000c2d6608140c84801c041c0c03420030f40380030b826031580d950400c00050040a10411520002e2480e1071113840700e18003030090783c2c0c4500700406031107110004454002c640ea84000c9c040200081030061000400003400010110524845c05000e50000707000100b40510920403981c4d4260312114a03131250400c101402002d45803260300b101400700171031144001d0b07500c59280920a40084101e1a80e0703200400c0c0042404401030030310701030070307006000001060b0b5a03500105242400c032510210f103681c86500440303c1d9617408020100d1541b801901080034482900035014160f4180100ea0200c141400c4004088452 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 154341546 1250 154340296 154340321
    0x6020903032217151b070f020f04060b03010e060a030605090105070e010f09063e01060506040e07050a0c0b10030201141206130e0304180f050603061602030d0e03030118 74
    0x345a103a101841341c55555005000a50259507150320b500c0700c0d90160384601010b4440058283c050003c602c2d0043c00d200200c0401d0720b080c004a40b4120b040655070006001e00141741110070000f4030151541c4081e00c0003540c20000030300c902e04140c0b041c035000785410f0f036a0301c0000d989641e268406501480c45000f40300b2040e0b5580b0000351074481d08076210b41c900700d0060036650a294500784103150b00c0c140610310b14144085a048020010042421914030b0b6008501518050100308507017011155460703403040890515640d180d81848003101c2c46024003000410641642081c480200801a04a0140da200ba290180b1400d032045a020090280200c820000020400020902d042c6980d420480030282d140106070010580801410340c0c1058001c1518103402c1c866070b01040030317503000e014240391245004129505010700401c0e11000c00500c0d400c220320000d19509000c51003042151401490440d040000740c8070b4181e001c2d1a50b200b80301d0381543c51400c699880700c813146031191904c1800c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 154342796 1250 154341546 154341553
    0x10e0a0c0e01050706060503030403120f020105010308120718030501290607060e070b0703030b0913020a060806061c020a02060f1302010c020a03060f0e0106060f0507020d06020903032217 82
    0x25070200441c0c5650004404407006a102e1100040685041024102641c45480c03806182c45a00c01d00402c4d2803813000b0b00c10110784c101401040443c102c6800c030340b4411424101d0400503a9030751402d03103280c40f64a184402608807440000140941940a640d0b03019091079854000c22803801d400f80541c40014005601c0350f000c000010000e4500e40c0002640f904100c183c1c2c02050b42d401301e140d17160304804010703030110352248081030b5980380103a076041e070103581400d0000d032214164000c5480c0880300d003d0b002c00d03c405400450a65a50002039075136041c03d03000c040d01c0f02c0d514401020003a41000740e4030701c05445a800800d2000305070303d0115108a0307108001d10030240c40d540044400c803280c0d507826038100b4400d40f00400404d4060103020000c3c00e41840100344d100701100500c0c21510f45500000402c044a05003a1120b9400070403100c0c00c2d5011240a1199441c90801d40c0c0240b195040700c9505200c0002c56040f0740b001c1d8001c0c5148c40d01c509952040507030340c2e03100312100108032252a0b0702940 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 154344046 1250 154342796 154342817
    0x12063209072103090b030403030903170103050615060c03040914061c0605130b0f06090705192006010f030b0903090a0501032f120c0a140c0f01020f03010e0a0c 70
    0x2900a2442c1c21102c0c002c1c0303400507506a403500c2040c9135500680f401e50000751141e0500742815000440c00c08107090621742401c0319807540c4c440549809001d0800548000311001c11445a901c00c1c02340e0b440303030000c181503035686c650701c4074064014040f0b044502c00b81100200000c40a1a00d15174035140d00e0014a80a560880d0680c0c40314000c00c402003c0e060070443c480380b1800454488842d00d4415401c0d15502442c40c1882c0041040c0007600402039000c01008005c41801d0642c0b81d845d0400f5a100e908240c50a807407141188841c403c400241241d5071b21451000040e0140076007400c0044a000f044400c0840c0c0f10590482e890340f080300f0304150440c5191404000b254070a40c820383c828489465460000d180c10780b5940740701c409041240b182c0d1603000c02d1803081c100c000350200d50080340b10703008036140c4542d03d0302c003800403030210031003000c0c2c02d00114180400351401c2c010103500c1c401c0c8000855450429600c020140e0b00207010780c0b00c4c3c241c0c1d0580021044000c6128412405860307031140b03000784 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 154345296 1250 154344046 154344089
    0xb0904020604050130050a1a0109050d17070b10061107031e06050906160804021c0302030f12040606050d2021010f0e070e011206320907 60
    0x8004038642c00340c0401d00080b9005040328415130400ca503031030904001c91b55081500401090700d880c2c00c50b00514080b01c44d0203003984da130030901a00403204182c455a00504a505115440c0407032140e111000d0b02000411000b040348403000c1610960b0b000780c0344031800d030b2221030883e010301e03a4008640382580008004c4c0003041c241c0030490742076207900803140c030350160665440c01552000c1c0c03050070307260f1701c010309102c600a540600c8000c0ea5110b450b1814085c41d090f000102c45010560000c8800344415052030b040c14800c3c001c6401e40b0841c902c019581d6103a181000d40005004c80d010796000340307006030101e0380f882c0442c982d00c807150f0000500780100c2200150500107204117010b2641c40326055424400c08917800c02000e40c4016058000140201e801c07070440c013551120a0825406e4200714001d11461003956040390648000e020510000700441c0303000701c01040b50011005d00e100c550504100705d0b04a180114151034401e90301d41e00302d500c4601d004c0c0d035142018060b0072415113136075800e244107 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 154346546 1250 154345296 154345307
    0x20a080730050d0801030b0109150b0703030b0a0303090501141207031a03010f0203010e06040b09070507060204170309040c03020c120d060e01060c0c060f0c0206090f09011205010b09040206040501 86
    0x710a40e4145440011041d0359254a8004400603400205000320010018426200c0303001d070050481341d41c06d21004a407200c9150180c003a034001d102d00e0310404120341c41458440c0d0f105d100300f060301804622035075450703080141602d9070502c43c150008241d40d003e0442240c008080c0c8203502d0700302d60412081c1d00c2d00c850540180140740d0f0500035510100300c0902d0700366000d005052058202c180010781d2075051800581c41d8010091402e40980e041118240c166220003602d40c0d0300510700d00d0040c1e1035a1280ca841000b91080354010044500552802003940b03070044000c0c44182800c83c0c0410800101003425800da0180c16070b06e481e80e030091100064145d8950f4010140725401c2032000514545500380c5000c2c1ca2001e80103840021802c4040204022200714124058803050401d19155124034600801e0300c40b4501c1c00034080d0201192442c0c40380c40f0203c80035038060004241240540c0c444c0202260701100b2082a40c00d50300b8040c0f90521410300071803e50203550050b003010700d41410040195107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 154347796 1250 154346546 154346609
    0xa050901110f07091512030206060913120f200606190915060207061701060e0d0b09011e090c03020402070302030d150f0b03060109140301140a0603020a0807 69
    0x14030700500032402c04025080c000030014220805000414410020107010f2214058202c0401e2007403140c00f2801003500010070540c013220441d20703c400c075950541c001150404591000700228035210000708132980107401904211406e944058480810300c400c8158401c0602081200e500060b01040341410011001441003109111070511281d8901d056400c4603101c140c0555540d8891400b40640d95040c01114009c004525051408000000385461030308818402c1d00117000c40400c1c260016114141c40030b042540110300c501c018504144043e010f402070386214a40240c404014070408501c52140e251026040020041054190350900c0002d50110364203030250b11041c0241240300e0454010a4000f14800c0c0510039124500220503c072003c0d5600929500f9000b40308120003070740c0c454580800c490881d102c00ca0086207030408680108070b07245c4000e248011079401c000c03a9456542140301164420b0710368140c4541d5442c0319030f49558403400742c0500045000b0000e0740e400c0d43c0c070440e0b40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 154349046 1250 154347796 154347827
    0xf0f061f17010e090c060408070909060e1606090b1204020f030a050a030215010902030f190608030403080c0c090702190515071808010501150804050709060f03060f020a050901 77
    0x12100e884601c01540d00036407015035046044001c00000583c1444202580803064038070500301414201d409480e02060f0081714030b500d41d103078050300c04c1c498580c00c01481009890103417103042e10140004200b41c2d15a01075400480d04200340000c00420010443c1c0034001c5000034060036860f00e900700100307a00490030040c2e1500c900ca600002284080c0916044903100b034004041807600d01c45035000c7c1080c140c3c031550ba603510610410010f10305099107258490100700c610b60031400d900580740001c02180e000700704030b0311001c1004420084050700428100c002101144e180400700d108009004d50111034144c016002128041850403501c3c075118401407040056450194000355106040c0c0310445030319000841041d148a04814503400c1800684840c0000740041d606112040203c0c0800300070f01030410000c00001001d00200f440713607030040c4c640220207008142c2e95140120700b01c030540c0001e41710300703241100040d8110224800c807520b90b0f000d034941500340010750005440c2c814540c080c40 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 154350296 1250 154349046 154349057
    0x1204030e0f1c0f0c0b0c030316020a021e1201020406030b011106070c0b0a060506120703050a0e0d0c1a15030d02071404180f05060106030b061c0c05210f0f061f 70
    0x10461384c5d12600030700317041400c11000f1501d0b464a810007000c070360020345011081d50401c071454009a00c0b00103840c15004084007240d5503030401000440d0141001d81c01ca04625440481c1c0466219031540001e15800c500342e86034800c85030000c4142e034036160243c51000200b483c00402d800080d00700b00c160740d0300001e102c00004075141d03a030010444592110b24500c0c00c2030441000c101d600d540500c500b035003000d401c8508101030702d9402e10082d0f480c101121040140110028140e003000085038010511f14840440325807541440200021032504500b03090703220340070b0030101c40e6003103100040810445018041104500c480481808001d024114404458030001d141080215024503561480544100e004100c40c0d85800401000c445160304200c3c41610100244940888540c030003440001d500f00f8000b440b0802c400050f18940b24503454554175450b8510480b050f500c1125400780f15841e140100b070360030f076200c030040303c0c0d0003608a48003544107841007411007081084e020800001308690904 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 154351546 1250 154350296 154350299
    0x126070f120903111014070806210607080903070c051201061a0307031b021c030f140a0b060f030402040e0106150903051506010215090304120606090e06060112050402061204030e0f1c0f0c 82
    0x4074022b15040d034083c10340e0b80d8810001e0010440d80f207501103601c40d00c58405181413100d5640c480710032020754440c1d140f0038001300c0c814000300d40c000c0d44440700a00400b02401c06d5034a49c80c82540243e00f007124000d0201e440d110408942c0c0c0d5018940e44010704450b400f074818030341c40d032035404402c3d41c00d814080100b56940c414034007030040c0c0b0301c90181c41d400b685078041c5081c031304400d9241c1a59850b007d164000c134014056083e004001e842903c0e00700e68112030100d03034a0349080300710b4010001d641c814600810103948035040b00750800700910507a400703141607511160308202212040780c010f6829900503804810030900b140c2070130300100d401909600680c4e2509545200000f0f070b1510b44142503c4860751203004100102152290042038904078024040c189011000a402d403d400c076040b2034429200c0000804550b40c504c101c49180740003e400c0206030816080080c10340c3c01c40ba500c03d000e0100c82d468042d440c41e0405403803280c500c401030f041c46c141d9402c0d55095510000c004044400c0085400c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 154352796 1250 154351546 154351579
    0xc120a020102090f040608120702030102070501090b09061e01050907230c07080a0f0803040507121401180507140a03020312090126070f120903111014070806 69
    0x51aa00a00368005601d522003402006501d285104800d8405c03403505104100c48140415481e041c51481d41c402d544401c02070011034068402c01c41d004280303510b045149000c001d41000b905d80260040000c899090b0346407481c0c0d44a8242c612203102c0c0010601004000920f40403041d1030348502c0600d003480800840e003120700381c81420044041498031010841800d410000c21183c40200710764130082012400c1915621050f08192001402c0c02100100150601034100152001400c8840d0031000391146420f001c10894110140000756500349850032070094541901240c50580180280034031030301d8420b649400400103086960031040b81900040940d8040c00003a0000c903803246001d948220100004244c54044d858903801039052040040f608100f07110929800925800d1541001d24107440c04c0c1c03583c0405080369801d03036091422031010564040080e40040c0d60101c1250b4078400107a54130015610802c0d40e11213207041010010700701c1c510440c5860b4101c10064804149078103c4107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 154354046 1250 154352796 154352833
    0x6040f0516020d0e0607030c081c020403020a0b0c0d0503090118060e06010f0303050a030c0903152c0a0209061801061d0d050604062c0601090c03020a0804080c 70
    0x1e50300e0000d2665921120081030b0148503d20066409240c04070b40404103100046580c01a06800760400044100700c80801414100300d5a5041c40c6034035460b01c41d50740c0e610f0600a903103d800203c2c02a480b0038000a20b4441007030981c0c014800110142c662540c034030b4000c581907040102000019134856a032030351502d91848403028024010f407800b140071018020300ba0710701001130f8407480401104030800c10202e540328064900104581c600030520103040141200c01488035040030f085a2500703008010102c02942c0456101401c91001603d43d118406034140301e0b0880d080b5800f0382e42c10803d0311a0040c50704000e0540c0c8502c0c02001c40842c060507a8070031203000000d03008140410941c1404190034101d0550b81030360050216941c0d406503501d0381d10b0544a0301c000d8002400030345c5411b180003000340d412200000c1205242500b1180b440800212561107100703114081c3e0b524030b46544100034a06c24022611005d615413900b044545031682e50303042e2a8030018290400d070040c241c09150500141 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 154355296 1250 154354046 154354051
    0x20409060308074101060911090406150504030609020a0b030c0a02060c07020d03031a03010e01150504020f0a0f0507020307140108100f090e030f03040302240c040b0306040f05 77
    0x31070280d515054985410380200508407500d580700b900e416501191050350384c101002001140c000c005030310745002e070030340c1c050191500304241c0ba03800c026007100d10050720f001a186c084d40854080c4045a40d41110384c0c844a81d1091040000d5010001400403400540040c03c1007880030748851071095a41036003680c181c005035444945010000f520029007681045803540103204010010f18002c116800682c0a842c00400241455280d8904454850962500f0b4038612000303002030007901d0100024500803c403204a002c03148144030b0020916040901c25590103100343c40000d40703402c05101098801e00d001500e44410410200940303801a207090000000801c000c0301d40344594558000050300035240105201c0447d0030f107140421401100700e073f6490442d103142c0310000301078000c2d035604d504500c181080707892021000010b01c810140d00240c822055411080d801208881150343c203c1c014200341d40000ca031800c28001440310b480303054000e541144004000060149243e103514040c1c5404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 154356546 1250 154355296 154355303
    0x703050f010504090f12050c070b0414210703081c06050a03030503040206070807150f05060a0915120506061c0803040305300603060601261003140d39060204090603 72
    0x8c40c0c4200c0d200c0080050801a1000d1107401d82014100355084070203c05001d081031003403c10300c110400216813660f034211541804415110016103d080c80600c540c441d84081c40c420402000415076041c0c14803075081a135000070409400c407442c5450480d6140c00150050340d0040c420400480052080c100401c0d003d48038030401d041b10883c602c0c18404440c1a11585049541010108071a80e9262400c140c2607a41d0305c0300000707562500c11044070b082c1026401219090050031014000e000c400281c46114000c12109036030008403020704840d0740c15184500401881e001c0c00403500080c0508040d10889146040b18010380404186402c8030705000c036441008035640d1010b11046090038003c0c281e0000081c00c01c0242c4140364a4590208125151000454810f5001051803110144502d8000b1a00011400140040e4140b0036884d040e4610070300011070208003a4101404004440400b244900d02c00103042e400c001d00c619040851101c4225500b5a00708000702d6148070500c81c1c20301030b600 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 154357796 1250 154356546 154356557
    0x41401020f0a03060306050105100c02090702030919030b0603030702030703081c06060c05060f131410050103032703031e02070305070f050a050a0b040303050a260403080703050f010504090f12 84
    0x1171414800121032043c0c0040340035a001d1070440d11015017028103220215810b0300c01070b54a42d90b00034220b0641c001c2030b0a0660040c800c0c403081b01040040c80310482941c0c0951a58061902d906081564921440b4030094141c2c10010b420000300320341d540a01090141451441100c80c09000030b070088a409811000104146000340d0060150802516034001d1541c1c13641d03045424600c40000003c0c0740c007071000344000d4818060003510002442128040741c100c0d0014403085d42c4030714004d040c49922000c01d00c0203417401103070f0031801c41004500e00110782c0c01d5210f8101d00340e0350803084450614002903040541c801c0010003c005001000148000d20003d03403400f0340107080c902000020765090340101d02c1030080c5107083c04241c60300d004540840368181049075aaa511000540380c3c0f01c160f400a0501d081407a20b840030f5002442201c500c41c1d8801c1d80c69071069965203078150115242031300c03080041804030005201d00c1c03c20f58805c0161078000d4091814658103a03507510070403140803100f600040e0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 154359046 1250 154357796 154357799
    0x5090a0203071d01140c01092001020f03090d0201140913020901030c050f0301271107170c062a0318010c210f090506090f10060509041401020f0a0306 66
    0x15401520f00d501400c056812045560794240004d005000030101d5201a4400281140c280003095100c8082030303501218044801d04070302107800c1c0f0810001c03c8503016001e040c058948000c0007200701da0b08003500511305001074266400450b4400c00100304e91030001410844028203079980c110f92088010303502ea0140e80c59003000c0005050710040910003082c0701c002c3c0326099005803400280c80c15203000c203a004142c503180d070000303095404000c6d030002c1c40c15240030704800000034900014640d09010700c12040585640d0b03201c003c10f0f807041000c2c281440d00725002041e0802131050404500004d03002c0b100348070418841010840b0303802030311408403488000807410107182d002e002d403100001440c00c1c0032076600091703403e404010304541c58a1102d95500c2ea42d05804028a5000540054010044074030f01d11380348600135030707441020310b1808403486000500409194240203d205446015040c9503845e243c1c1d6861401415289842c26615502402041540c4095501078101120281d8002c14000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 154360296 1250 154359046 154359061
    0x200604170105251202030907050a0308040501080c27031f060f0e010e0a0c090b0706140a05060d0602130510080a0c0203040509010b070203070801021602030601090207050c1905090a0203 81
    0x740039180f680c03c501c21048400480c00c581003c0441c4002034a9100176a80ba0b550340c50340383c1001c04982099501007940c002c00700a0165040103802561800e8841c0c00c11600d0b81d041c0b42e000340c001c902151a408203080c2e40321440c0caa2100081018503405002c03140311201181920744890368203031400410990742c050810081c02c28581910003002607106102081d41040724503c2c1590b0010501c20105443d55900c2c000c281c428074580c4000d1074410310040d101c035030510b81a809000201c1c12401c0d1185a4000303d1007401c0c43e4820b4600a002c010301038018400140c2c1d404000e500005190b00310307001c1c10600021141c80d144919044141241e031151441d1802000c8202155038600460085610034001401039480d07c880701c6065450903030140b921011144002071404946402a080381d5001042610342c10b10031240059005208800307030340142c3e88802880c2d04034001c1610280959002c841c4401007802c20780c0080c28a90348514070303203919548400109614034000d8542d0f40001d84c1c00010800007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 154361546 1250 154360296 154360321
    0x90203060a020901230c030d05192901050c03030c0a0f0503090a0f1506090203070906020c09150d050d0f0306090c080a0c0504091503050c030307200604170105 70
    0xa520300004504241c020f0700001d10795a200642d55000c20020b4014004600c0c0c0c000603512910741e40c0007165558409400b520014240640d00d074411100f0140e030102064102d40102c800191038948140c54620000c1c0c03540310401d107681280c605002c010842d071445d059061008501c64041e400c0569030710074601c00c00810160300744104408202d418401d01800044c040358902c1151b412441130240c0c5409820044402c16040d07414882d0145810000038041c5000e40156105640a0b158680704980e901000c0c2d84074140b641007994031074000000a4120000b60040c0c0d5003056010308000c0385502242d85191a04140c50a8003000c6000d0840c1418040e5060190101500c01d40105111001d410903014107100c1000d42031103561b0b5100c40301d00143c1481841075500404400f803050156580d111202101000a0b000c03d85441c010000183d0843c20000115614254003d9803080070b400c4e19440c0107445100540e003d90712080400c030014442c104032054410000801000003924205010007861 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 154362796 1250 154361546 154361551
    0x4020d0e0c0105160b04170d0e0c03070e0609040501090203030304240c020a020904064109030301060302090301060f18060906080c0f04060b030c030103034e050a09020306 75
    0x4100d020040c150070000ca03510000d09041d44170068a083d92100e2a0025804580701c02000102e50041015092943c582d0403081850a00005075074000240d0014192600c0550042d5070a40c580000802d0751410801c2e0300c0c1c3c3e8014022000040c550301c143c6c5c00242150702c255400e0b58007222109816004809048650080648200040080f13180700d18002c0d44803051040c019105402520020f400e0002580180312030301003856902c514103249101c85c01da02d4100030304600c1d194200030403a69058010303c0b6410b0154201e80000e41c00c580c6001401c801952000c030100d6050354030740e2400102c0d580956044e030003030005448264610102c10b014a01141d55640c4601c10310740c200345040040c2040801c1d00d110000c02039a03104500c1c1591408240078000c0c41c0d0204034480c400004000340c1107002c10246050300e11a940d440c640420036460382c40340001e0030402032680403a4501106440000c1c003010642d84160561840e050f650514140080b10012541e9035111030300c0305101021460140001079 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 154364046 1250 154362796 154362799
    0x3060a14031903050c0c030a0c15090f090e0f06040201090b0c01060e0a02030402040b01031104090225060506030d090303080a020a02010b120102180103021e07030507060c030c0305090312070503070c0204020d0e0c 93
    0xa500390003500d42049a1489212b096035940300303400b01c07000c904e208100c104e000e030030812600d05806035a441d40300c004204110310004580100744840720132000100d40300c2c1c004c82c0c050f942d840019091a0390b03d00d80394070175100350b000356603105400210360703840b1000c851040030b00000041e2240303041d00611082d9240124803504152030030050032204001001078505840800b64010f84451340122a017030040075000c1c40c0710007411001440c2d410020a600b2185c42200e0270b40039102902c000c0c40c1d051b20a62072601008011070340000c0010315204059001d801c036981ca030301c004503071381d001c0c4004035907202030020740074810385d4000504803500103003041e04000011013841e00714507080c2065a07064446849442c400c503042c2000840308141f51240041d201d501c0e030801810800c580b201c59014005000600b0003001080c240310010b185024044142c803019100100202c825070384036002180c81c1e07400280300d2402d2000c103032082005603d0b83d10140400b64161000058411a0114030030b1401c015514490f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 154365296 1250 154364046 154364053
    0x10501030b070305160e03030c030c0304060e09100e0a09020d1407140a120201020708160e01050603060d030806150f0c010510180b060d020c010203070e030303060a14031903050c0c03 80
    0x30203044031202260141020390701d030203400418091b002900314465210103002e1403101041850460f00048024821916140c4508004860500600140600c1201d01d540c0301c1c42601010070014506451090f4061806540019a440c107940003076068400c1e9141543c80c0d44864080c518800d0080202c2406400055259103a4140b41750000b03105400c1c60090404000351040384004590003001104003510180e029207040c0c0c601d5001e20004040c00348125415a0581000018581464030032030b07010301000b4180300005480d5440613a0090005450590040741036646e1002040411018010f01c3c0c2e4209106680c0c0c081d84602c541c01c0d41d4000d0000b00402e4407983c0200002c0c85246440c050b00300d9040c23008104091590f0000d07106010b00e500000c07003d4000648507000b0744040d8011841b405054817a10142d9404c032092507504d001c00c903013035504140d140340305108104000704000d0702d010008044910b40c03a1044a6400d0454028034201c0110300d02003031450340110103202c03032010442e0542c0107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 154366546 1250 154365296 154365301
    0xa05011202120a1208070f080705040302040203130b0a0903030f2a020c061c141909021507050a1208070903110d05010c050d06171b12060702010501030b070305 70
    0x46108101094009100c0e44440d002405100c03010b00c140c00e41d41c0d410429413202c6000d00e00300644a400116081000614280445c925440c05400540d0040156581d0303039086c05e01390f909100007940043c21908400d146038034a00002401c01d950720744101c000040100f031040d66840c020f42a21070070f002c1d20360303c2818840600e0000703000403e00030000110705540c4030805e80c012002d07820508410349154002c5000115003860015070581103540280e441010485424841e0704503903814005d0300c202803a203e41135008400f00300d5980205141600050000c90b0700280c3d40841c4815601034141241da6810002664040c844070888a41e000790309410607000b186808800288292641e00009204403403540141c40c1c0e0b521140d02040c40158400c000300044010344501400300d030402050404040d0030614040303203061041ca0750040c8101604020003035045200750096003480b0707158003241c02994039140050310b00b0040203d140210825000043c095046080400000c03e00611820505081406 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 154367796 1250 154366546 154366559
    0xc03020d1107110f13060b031008010c090605091c0c0e07020613020405100b120f0a060303050409020c03070f080c15160305100f0305070e06010e060d0b04060506030405010b01080a0501 81
    0x192410f0f0000455a0030414000a000100c0d801e07040d0111600072894100301251804c45140103502500098404c401c001c0d0b5150070584c01c0e107010640d8400020021390042150038002c001900000400a00c0d051116018509405801440001c1521041c0f42c1d0001040303511840303240c1c5d58000409201410762450404101c0c8603001c0801c10090080c1d41d1800015041c00c00f46003007801078200901c442d40d030307200000407601c0342d04401d80b24249032074514804507120711011311510040b00d0349503e41900b0f0174134202c3c80700001d410803400d183c82e81c042004480006100600c410000920580980d40c03200300c403006461070801112000910f44101d441409801d60314442c00d201c10107064540030030584e4030a244806a607415034801044440c00d200040204034010400340309945149041202956450004650000c1d8010b501d5402c540108810b00342d5007901c0d00800c401c4000944040b491a03591310102d0040c5e44212010b440c82d0355540c080e06895030b0702c800e44275000a220407050015504156 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 154369046 1250 154367796 154367813
    0x3070f120c030807030513060912020603180303090a0308010621050402010c050d0f080c031e100305030a030f0b2202090103140f04020a060f08010b0714010c03020d1107 74
    0x34003020092650004820003051850000146a01003019511a032403480c0192031900b140300ca500e00c1054a54021030018411142c800480e0a00444901c260000360240310003640054a1141400c40c01081c40342e0b2228104010b60242101078020b2680d144207080c001e00f009010f810440800034014a24000240c218000d01c040e10b60941c000181d5840c2c0b8030041c0c0c0ca400955900401c680a00c401c1018034940190b880000d500c529103070804d01d651100c075021083d1200310b84d012406401e03980c0100d4802400c0300c000b42c1c0103402445024040d501c2c0c0e01c07650700d5504080d0324080020b8559204c00e49000c40ea00070040340000546800e2482d042d1000400d4400f0228480c2c1800c1e544c4c08079024659a1182e0003502c13010310b500301c20443e43c0c203040b02234815280d002c9a003039001300003c107800548a4403035400324140d98000d5440740f92a900700000700740709503c0190241c031010718508255569000c2803183c0712140c40c060b1001644e41100700c1c0541c0c15100d5015049880000030701200021410a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 154370296 1250 154369046 154369049
    0x1503060a05060a02031c0f0c02060f130507030503030906070e0d03021f020715050402040b01050c071a0904020a1701050609011e0c0b0103110913110f0301110a020a060b03070f 77
    0xc480c0d403922a007100800300c0c17540c0074060406800d46924200c0782e165003400e511800103906600b6080c45016440c02c41680d941a054070160400f960039000181d0750415402c071a0344080c4100160f41600740d03292181c525503003007580c6203c442d070801c40c10311260640105240a200c807045d541c03149ca103903168401944442d0101e041c8071040314004140b148404555040b60103045d40021207107091200341c1c00c510002c4c1022074040f4055403824084d41c45942c05031080c1e503080803c10000340b80207030811525180f15100c4100c142c950034003d01141209907030312700151808800c540c0e160000c1c81d01c800412110910706030f0000e800b0302c000b000411111790b840396035860100040500071142b03c2c802d101c1115010145e07031000d0314100d203550003c07082080001d00c41d0702080c005c4075001d07860703240c14a04500d541e480750802031101c4d486000e940441c2c140900640030021000b4000250081802691145c40d0b000720300007001600b11442150410910380310740d4015010a8008103001810540c0004440480e03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 154371546 1250 154370296 154370299
    0x7060e030f09030606121f0b03030a0c02040e0303041707022704051615031d01061205010c03050c0909091006120302060112121202070807030c0b06040b0a09230103111503060a05 78
    0x2007d420401c040c541c0c1e00704074030308080234048940c0d032480318000a000701f002d51001c03485a030501c55a80012080001036a00440c0c0200009039000d28007440ba0510750300c240c100b282c00030551291442400b1000d1840c1002e000380c0e042e507001e50320705480e1160070449207200c10200307403621003414000307000c012440c10b0031031106043c000b45113150f00a400b091119033400000c1c0540c20202d01040b80312003170000441a0b84210028040d40d84038810582c20354008035441c2c4140003013407046010625040a19a0304081e5030f1081c1c41451030030070b00d1502a1045074100d08036045500281c1000c040d03042008500404054098959161301ea40e20303590003941d83c011810410030a5800507040d44e0150341140c800780d60120520740d07154070b20f107405001e412401400344c403212071050020b00d8908190042000141d002045030440724102103036600107044540700f042e26140d8421901225111000021740614018100c44070700c101c6182c01c1100c0b11400c2e0f2406e100c90740c41401030186170340354040c620003581d00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 154372796 1250 154371546 154371583
    0x30b0c1903050c0a05160203030c0102070c15020c0103090821010f0e04020a12080409020705010f0e030c060a1104050a0e040203060c0a0903080a051909030501060b0901050f07060e030f0903060612 86
    0x6040308111783c3c14803219000c0e40c18000019070910141054cc000c004840c410395201c820705030790b0865101c00b032420503054009600400307000302e40d03907200341d00044c8a944283d1001e4144604499400c3c41c801e02064804099400080103004040500c812840141210b40100c030340d42c50a03502281c3c80c0611807041029400d490800402040703c0300064070003070185078070b00715294042d40c201580607107101c82d4028010742c680364100d001c090000c01101d4189150200030045520b480c0e0f541d00062422820b4041c024000703020201d19682d40c0c0943e01d00074010084152040d040c28010181000c0c03000d1310b8822480e104022484480f80c01a401c0821290415055501c0f440c0d0341c8815a8a40304080000c10f440b0141c00d21802c85607000b4610b80b05a81c00341300204940d03600c0b550050001e2040080c0c29001c40c800f8000301d41c145003004000c00c0b0f40c51040201044880c2c010550078a181c012128001c6010380c04590f150083c00d04120707040d40100c00301c4940300406101100c460300d801c1e80b846590041b00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 154374046 1250 154372796 154372807
    0x604090c03140c032b1403070e0a090903020304050a0905040b010b0a02010b04060303110d02030406020c09060402040b070309060e0405010b1c090b1602150601140c07030b0c1903050c0a05 82
    0x1031080c05180f000e0300000e0140e80d501c2c8007022540214151071548003000d00d00050035103055034401c2d1400390114440003040b515584903290250344003000003464560200f40e4010219017241d403405400000f62280e0000e50312141014100321444209801110f02640381c0003c11001c501554441030445408035110781c1c1c3c84001040c102e02500040000c0c41e007040c1084800800c040d40b000154400074950801c3e038100c40240b40049031244514810a0f0041c0c0c00500d09005915110100a0300f14800a10040c5800d5407402e010b64550000b80096021804035070b030402183e41c10081c083c0c1e20440c125010400396040030500c114a00500030030b078560981003400034907261116800048041d41085940c2c12074501603a900030b02d04111400c0d4030050240c0805582d0048900c1c03d06409488142c40301704158222107030800c920340004510450600c110900000170a9140551900441c0d4001c0001d65034100902141211051509140105440d003800c1052080d2040300f0f0f81c0b9502440e1a0035542d44 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 154375296 1250 154374046 154374083
    0xa09030308041104180210020d0801091a09010b0c0f0703020d061805071514040806060906031509030901030c050c070611030d0509060f060a060e060d1407030b090604090c03 76
    0x20000c84110f940091600c969070801d00d01600782054840c0c82118500c5000c00c4035002203884000064440000c1101075005000e03808094000c4c2d00151044422000d000c40720340f0004045000aa00401d402d03880024981c0140c0b1050100c0001c0c00750100040100030300c0e5501040390000380b900c02500080c0d4072502070700340054103c50140b8003900174044034070305a210804c034000e0080304914103000c1168a02c4101c089042e00065a00300da00040140070196107203800d0105115005102c0c1d40e25003e80da10061008400754100c40c01681d1503001191604615000034007194400c8403518140003042c4620106081c0000302402512a40d241c96410b98210100880c0b82d07000f000000380c50181080b08021603810300160003882201100310050058941c0400e11841c0051401000c0000d8400300301404a800c1c42c1c0c1c018403400900f000002114007125811441d04001503440c0e800080d1284521005880c0c030400d8030323802c02c10845080050003429901c0c14501c4d000b510004001e19059520708281 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 154376546 1250 154375296 154375313
    0x60d17090a080a0b06040501060c0b010302040b04021b01060612060305100e0f0d080a0f060f0b070807060905030c0f16060c0606081621020904020d020d0c09140c0a0903030804 77
    0x51000d1012966032403032919249000c1802220380c170b801149080b00000d03085100c0c40b145005c0c10f41000c001840c0c1c0e400d54091101504044000d240c016800300b04281320081801d5038482c0301840f0900004000741440c0340203107400240f8040d40c004d03909000050001c60b03c0803885a1240341d02d4040002c4c3d1003460711481d41800e00440a1140320b001c0e24070140c800c50b8001c1034441c801c014901c001c004c2d44681d00800c104a900302e005000340342031040f00034001e0203110303c01004541c4c0110441070602c20740d0740e650000d0343d6500008542139080450301a0107441c0c1045010408038244001e0642c59010400c0c104107803105104507805c1101d035240c014103001c0d8a41c001006003068109940e2840d9120001aa020001d4814011907030292182480443c49940703900040e03903401403005506423203d070200600c1041800050344d100001e04100000200d568110342c004141c08000441c17011292010903a010f0001030581000300c0f8100640b00c0740c2a48003900c1030940f079041c00e12104944031070418562 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 154377796 1250 154376546 154376549
    0x90906010207091125030f08040c0b0a120513030f121103070801050117070c020d05010e010516090f0305070504021b06282d090602030c070209060d17090a 68
    0x10050700d1300c01c100d420300c0b0ba4500205150b1110452450000c040740710003042e0600e0301100500006c4103c90301015082c03042c11500d4000d401204e4121f901a102c03502da1410354444141d11010504c00c0030700301d071800c0040c0581c1e54040c14041c44400d4a052549024000c041d01d0b110304402c11101c213500004484007070b07102c00400c2443c10b81403501c80c900003002801440302801b499020a4000500d258402c20056803184184082c0c1d895030816405a401e102000f074840d030302100c1d69526814411440c8800340704182c4542d41507180da40e901c030040c1d400640300103031540042d12a01c02680062001c03902c0000c0d003030100c441c00d40300140d5403a000303d5541e50500201d2001d030030f5805410f0502c031314901c81c0c8443d08a19003e0074840100d1b81d1b001d0f880c92044402d016542c82031640240d00080c030521311880b102c2080d0703604000100343c140303640d80c07150100d1303104851550040f1408070b9032006508081c20015030082d02034424004010464551120780c1e10014094800c1640000740d0390110707202d03000000f0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 154379046 1250 154377796 154377809
    0xa1509050c04021b0a0609020a050604061403040c05030a0f1103150103021302090d03020c031203010e04030c0303020f12010f08150c03070905090103030c03020609010b0d0602030c1e12060411090906010207 90
    0x281c14950515145c0060301440409034850781c000c41d000702b82c6107000300480b403c9440356110054000103201000e0740540004209a40d040c1ca110000a00f0703440a1002c02c00041c41980d08004000300352500c4468206401324450099200b0407403a904050b030084054150f90301103c80810340001c1503808270180c810960240c0d0844228680d02c1c00301a00007880d441480400c406075140803d60300c40c03071130090000b40708140d0341d1180003011801090083c60046036140c0a45000761401081140120b072303079405140b80c00010142c1400402504100365240c4c8007030881038000d0840e020903031022500803440508880d40c1400c2c00404034005900514800c2c2c0200005461407145607941d0074003902030640b070030040e0003600915000418001c01881024084e090040c1340c01d0300d114094031820300035080142504074110040000248503440494030321001d035400c1c41c0880d560030b0078481c2c40e07201c203001401725070240341040300082800501000707840e0903040c281ca8000d415520600104e20b0031714141d00c440c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 154380296 1250 154379046 154379053
    0x70804030203030a0801090c020d0c0b060d08030c1308010605012007080601060527010f12060902130515070b041502310e06030703060b01200a1509050c04021b 70
    0x441145d40001c540ca040322010a410090007540450a0341c444100c1013914000504c140300020019132940005504070402421a031140081907407420043d81c01a2605844a40c001c2003a810150300d42c130464000e020240028403130300303240000180408403111b0041d0b03240d00f604441d462144104000000050aa010440e2200d580d030b01006805070780102c1489800415154010007041e010501e4a188100b0603520703462240d010034400c071100046a1050074a0b0354030b0703200008070550740c0d0000c0c10072044003c2d0716000d52440c190410070301034040914800b0500c0180040d0300440d1002601d81d90141c1c01c400c00300d0740c0d500301e8a502c0001388500c003106c07103007400d41c4550600100b40e0401d02440851040c09405291915160031141d0070500f00c960543c5540b003100144001005500072000d91401030404035000050034550205024000258a22641c00450600140070f035403003204900504070f81042050710070f0394403100d4070b64184881c614000c1d42c00040b00c1d5001d000310390f01120355003c89001e8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 154381546 1250 154380296 154380307
    0x501030303020310080c031b030f01050f011d0108030d0c1205100e06010c02130c02010608030403030809010c031814120f0726071707080406020c031c1407080403020303 74
    0x2600039001503c2c40036131507981800110b4490400180855045030050013823141c0d203501a031000100341511941ca070907014044515a5a00003402018003d4a0111902280790b0415005450405403640202484d00024004010050002c011100318481d044c00218010481d81070503180011040440a00b141ca4001004060b20400c1131460070754904048580d1503881d04001182c0413480c6810107548605070204802c014101903001c200303c2d50090001080455860039803608603045544160082908407003009280c100a105400c000d030054141088000c29102103c03090030300c0d140000700b00c041030541600f03807000d007044a107440565196106603581c90762a10070000c3c0d00300741c00c211000003105032503181215560b241c20741d0007190004c1a0381422042d858008502003d507058000140c000c0142c00c009c114000002c20140909400505550b134000080c54170b8100c060340d10b801e0490280000c00001540145151115138075002565100c0085041c100f410784143d42c4001d41c14403000ac3c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 154382796 1250 154381546 154381553
    0x90a12061d06040201020c0301020f0406030b040906021902010e01060b12180f010209040e060f0f0c1c0507020f151801020d02040603091b03080906031e0a0b10030603050c06030910050103 82
    0xd10741e01c01c5101ba030030b49031592003003414503082c1e0140704903c0e008280c0a02c01400b2062083d4000d4404c40720003440855018056103c210403a800801c8080105413261403050145409005001236010030b000200201071030504503100e02e015103002c6041700f1656801003000402ea03981d0490a650000d0207a0b03801054070141c25000354009801c0394000c41c2840e2090854250100d00140302c4c00c9001d0440415a90b0440383d91014800102000c50312402130003c000040b02440361080d080d00c0080c0001541d08042601038580b891740200e5101c150701801030000d012080300f221940098140145490b400e00c008030440c00780c0503041d10070503290b102241c005001549a000341704424052560300c61000181180c1c0b90a02c0d03801d02002e40400810040382c00c850a22000075070380301030b40740d507025085c90202060654080080d150384a0258684003190858944404090117911b0141000c00116107156103690700d0380e901c2541940b04200100c00a41182401d02c80100c00843e00f4408004942c1c4924 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 154384046 1250 154382796 154382803
    0xb030604060b030c03011203021005071706060313062304060204030c0b03090d05130905090105010f060f0e040b0f0d08190302040b12060a08010c021c0203090a12061d 73
    0x151014451070420301c0c0000c0103101c4004803801039642107501440c50f801c00d851400310b1806d00e8011030440c40341c198101c03c8440c044c810b45000b10f1003641c0b21203841995824080c1c030264094a5148900020414006c2c0d40110300b400c000c03415071000c4045042140000c4401507400700c4129a112a03003084208420440c20354001c005a074881c044540c0c101d52610101c554a01088803a4a004d6022112212005024001614101c178545d403c208090b51110341c2c503015034406494495031a91940e0051080aa1000c00f11700030b4402460920715600c0011401025524079010003409079503240d406804544950043c01000440600844080c0a00b46031241080d409040032060005403002e005a0303c621900848044407152103803282480c84042035000034820140055034005203103000018441300a020b0005480d0464000d0240380c020b882d680e20225400d04184421034208004880c015514020b441d403d88101000c4140709290614001004140d0070b200e01d28146a8400e4581c0c1c2e801001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 154385296 1250 154384046 154384051
    0xe0316120b0901050103080a0815040606050a082d1801090b150118060e0a05100e0a1d040f030309320106060912150e01050f090a0f0204240b03 63
    0x924445841d0755642c10003d00b201c1c800c1c0001170001c10b04000c40121680304683c00c6811502002113005585030540020b012100140d0003800480e0021440e440183d401541c0c0c40d0340520106850000c659010162502d007034001e1091034080e01800b80814448600c1c5101c01d42841c003020020411102c49080000061208581c000c0a150807e091003859502c81c80b964464410700702541c542c15801c0400c1601c0409850090b03e4000900200c005040c2d0f4a8494075081d803034103a1194082149240d0600c000c3c02210341101c052401028000000c004a014142d0380c007030f030062000308101c041031504174007404080002030f0803520580e424094206030000e000c1201a0150015512045542c40007030a0300d00c03d101d02c01c08034400c40000c222a40100d40041c541e58410583c1e508802a110380302400c864a07000311903078982d951010071410800e03a800f00e40e08241c010b4001c7c011303003e90340c1ea011400d00720200c0c000d020310749404041017004131503110882c40103031000c03091107840d440d1408540c80e42c008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 154386546 1250 154385296 154385303
    0x50106030609120f05070b06030a150606090b03060a0e040503040b04180501090b10030b06040902030c0c071d040f020d0209040506040b0c04030b060d0201050c030c2103070e010e031612 81
    0x1440300c41807240313004000200741d002c00c3e525503500303140c07880e1900c00d80102c000f07060035050300800b54228002811a00030424003e0303408400a89a42000b10041140c401c60b000b00c0c00544040052240aa50701755540d001ca40da40054081d42c0e9480d0b284c80307411400b4591020100d0840480e0200d10140810400c2c1c0007118400810040746c1e0740d444080080e181c000030b081ea0001040304003030003d0f83c4039801038000c41c003004e00143c1c42c060762048004c0032030707000700e94a4440d58000b065294a80b9800d01503d0024841215490b01880c0340450030742d1f401402402c014440c080380403281d011900c8500c844404142c00a00709000d40c5450b00b17000d5245c45d01210100d039400100c0001501d01a442c00c15601074a40004000c0004e6031604180540e425094200764140b0006000d040c1696204000618085080c0009000d00c000180c4170a509840c01307925140e2010001c1c01040865503001c000c011040c00c00340f91110003040035201080c1000500c0e81c42c3c006030801840d01240c180251054100c0c0c0c01d01c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 154387796 1250 154386546 154386563
    0x60f0305060a0e0604090206091e030c031501091a1e0a060305160503040f020418030e03070b030a0903031b2106051c03121b0237050703050106030609 66
    0x1600402c2000c00c442c240104403916a04101090301401e0907800000c0d902d2010303244a141c00302110009003440c104a029042064041000c43c505003810f0184c0703480740c1c2e030650013049580042c0c19a00358041c414010710800030350700c80704511702005640f07104220100240c082c80080c00048115520084c3d0030701018000c08dc01440011702c6e61084c401c0070b2240e142004d02004445500c0411901644050019649000c45c142000d001d40e85a00c40e5036600850300c4010015a00140b4001d800c2d56003018003c0d201cee4121345810010901880c040729070100c95000c0000303200c40ba43c41c0980041000003140d080d864400c0c0705140b4080d82203030502200300c1d0b0540040c107641c2c16030751074441070301d015015503038000907489040c1d520200309001605855200f82415032610310344200f90004c40b01c00182242007440b21110515200e901808501e5480544c070740d0391080c1070a00000c00e1050000109a5184245006005800d00c42c051001102865000000703109181d56402c102c0f001d400d140509035030340b80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 154389046 1250 154387796 154387801
    0x201090c0e010816030503221a04051f0c0605131401020306030111070203070311010c08030f04140a030806131d060105030111070c060c02060f03160315030507032901060f0305 77
    0x4420100c41101d030b1000c000c41c6407410507251a04e0230105440705900b540c0c8440700204901008800c8410900f03c6070b8001368a540c90981003043c482840e09840e01610703021090f40f4401640032a480b00166041100410151900110005c11100316034001c1d0403115102d513005a0f510f0190003d40c0900800c50081c0304986410204004a00c43c45c1c00003036040d4800c10040001844506400c880e500050411a075011903540b50b03003200354812500c094461001108010812580041107103030440c1e150018640308c202c5039805011414041c013198450300340c0d00c1181124114a40081c1c1c8003410b98030001c44aa100c665810395114800e00038144203500b441c050454500001041d02c030b845030861005101949402002d031040480d21400742d80140d01048000003111080000318058841c0d01c00c00da00c001c61b2240010201c0c5c1a00b04802d00d1300d1406002040454000200203050302d8201c8800c8041c188130f054200030020303032201d44900f140901400081e00503001240c415030700e0304a440c28842c55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 154390296 1250 154389046 154389073
    0x5090f0f0303130e010503120d050a0e0a12030f0b03030d0506030f030406080124020312070201020708070b0a0509070602070302010810080708060412080106120c12150513050606030c0a0201090c0e0108 88
    0x41c8043c0c603023009001800e100c40300c62202660400e1390042c640c03c234001960210018a2428011100f40c2564401d4480d000100c40036418030070380c0e450402044d0104004a03000b40042d4585c0305041c1078440c030603140c101055480e41d05000c040a42d02150741100d5a0b169949005840c280091081e40e03070036640c2480741550600d0b8011654410b4a059010794544140507111844600020300010110b41d401c0c005c01c800940e01ca00105540e40c0540088185860311002031350903150020509602c1340c000240c200401a00055130b4000d40742c0c2400c0040030360350340940c50804c501c031546c45a0341e584101c540c00141d03c080032034950301403401003071110030280c41d07400141d8100c0030070300c1240001842c2a4080752210410fa01511f0030161620b06064140e203100f014506031012045040241c0c1c4103c4400c001c0d604e030540c20611001920201440350307181440c001541400020060b400d807000008803840741c03502c03c3d8402c031115076000c001c1d141216101c0100041450007401000a503104802c04078004 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 154391546 1250 154390296 154390303
    0xb0306030d0c0c0302040203010e1602010b0625021f110a02090601050706090b0705210f0601140708040b0909150a180209041817030705090f0f0303130e010503 70
    0x109406030040c60654240c110031649158902001c3c3e900954041c004030059856000450082046000071030041c20f02d0750701c42d6104010104508250780c034007030b2001c0242e11580c040d01c5004100006204a00b4041d40e00c0642103100e5590080d03201800544481040302c1640c400c50480780d0541c2e4041803984d484079855075410004101a50107841180011001d6105d400241111403040a0206500c038607661441c2d0f02e180c0a59103400461808904580090302c0d04040720752004034101407044030b0800020703041d03105501400c51810001601b1660604001520846000d41d620194455440c0d0f502e202c00441a007118151611a500c00000714100ca030b4070280000c02140c0080840310560720703007043c25041e40003030555000701c0c2c0d800380611950707591240314021864a0394603008c020000d4515001c3d4045d0740d81c680d1070300c01d2a01070061201070703548902603e00088042c0d4030180904020700c002205079007440305503941840006030715034101d00d502442c0012210300801084090741c03124201600c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 154392796 1250 154391546 154391551
    0xa06051506040b0403150e0a032106060e27010608070e0402120a0902030c1203090405010603060602060711070e070309141f022d03010e010e100501030b0312031905010b03 75
    0x90f5000340000e2010030b07401a03034007034455040d00002030703030041da01c01d502d08105080b80140d0100e81e1451800030000c000d003981d903112040381c000401c64141465406801d0054250113240940a40001303145040ca00c044494100b44c50160f040040d5079540600800c4c1c010101e420a00246003404607401a08041c001c2d0381c1440004822600b203540c0741c2c40000020900340c0000da1b454401c441e60303c1020340b654400c04000141c004091642c6100f45001d00c01500e006901c00c0003003510b0311008012056010604035000501c61030260500f04440609901c0d04400350841e038600c010181c1031101158055100c1004603100d032040d0450b1500b05039070a901c4444502c0a2091203083e400700408100365940140802e0110702e1480d204459a0440012140c0d40740c0c2c00780c0303d07000700000188140a22101e040703005202c0664068000e00d08019070000c0407510344582814151282c200790016503050041003515410f683d00e080e20303880e00131414021451304d13402404050703182100110703100e24160b0860f403 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 154394046 1250 154392796 154392809
    0x1d010f061701090903030605040c05070b180d0804030302040b0406030902040b01020f03180a210b0a110a03020a0e030a060f1401030c1205120705030406030b03061b0306010507050a0605150604 84
    0x110306030301e014012005040740c0f04c0d0450400d5510200494285c0d100c1c4110320401100e07a07101519100c0500d0500040b01002c0c19440c01031401002040090303000050392640103402c0d00e400f00d0075445500e404d070042e000b0b41d0000009400c1c0460080303a181c1d07144d800f800300346000300c800740414114000107a8445440010907105608100b184000390110b000e908128248080c3c2451281c03542c0e0050718000c00c0500054040f040d00c10b81100d800d100480b92400e8014008403010030060b0000c850075001481041c010700c06058004ca001b941d998011700da031200c00d61010f0140d440400b1286030002c0180f58034509110190b24001c44203443d500d800207000c2c1078035442200d1807143e42c280010b020440003501d400311114070401c0059481c2c20350312805085424070800003544c603941042d0740030781920030300401a4001d5015200f00003405400e08400904500c0d810900791b502d85500f801201d0622a800020b005882109001800c021155101c9849000d040e9030607071030240840100701c0d851155100d000d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 154395296 1250 154394046 154394087
    0x13030e01050a020705150d1b0e0f0a091a010809011401090f0b1504050a090207150509011107150c02190b0c16060f050106020c1c0c1d010f06 62
    0x244195405000208036200c07141c0116980345540d040040c0754000c64845015031a04049191680c0641038092001203140900300001e810f001020002d000302441e0128034490001641031a0f00b070744808030b07110f014041c2040c0500030740914a285c1e411001c0380e03620541c0042e42941c00150849070610070076816669661155289920b400310000c090000c4d03928405074030381e0b15440b0405541d1100d010b9a00048800c05003925189003c08014607004180c0c0401001c5004200b03010001d0071400030145010202c80d0001115110702d615a8018407a030740c054090130100144400502590702c007021002141d582040c44028250b00c0100e03124408810003002c1e11003084000c0700040c05d204052903000c41740a603c0c0d0304101d010400c50882c0014180d056402c1d90351101c0c18002c8980c1c0380103042c0500b170180000c040c12451080421082541d1082c2612038804580000c810030810403207200040c003400741482c480022000180b1031608081c82815a0785c03e00c500300283d48e81c01480d6000b0b8050700001407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 154396546 1250 154395296 154395317
    0x607081b0903011103090a03031406130509070b04060e13060303090501050315040f0903030c090b0f0f04030204140108160b03280c080601170402030d0c080708041202091303 76
    0x8003006400011501c0c1e49035490f0140c0c10783c0b43d03090501640c440c030060303030090119181034140502183c082000d50a55a40100c1c01c00100c0d440b104032340c007040c40421000080527560f0403541030030310122f900401c145000002c0c0c00902d6550043c00d121209008503280d50b10800900d18580031102d442c40014046031141000700039960150014580c003520000444101d013500d9000034080302c0103a00703a5005180d4811502c000c0c96071611902068012a04111031060304180250410f8040e00754003000b4580b0001c1d100c40e00d4070176072090f600150b5001d04184000d50b40380300c401c0040c1c0c1c002d014401840c8240050401900d0300c042901c0200d5804028180c07954072010170104668070040134643d44100c0c0d000540005100501c5209008045a6105441404c081c0c00041c103802e0410f060300b1020b40320384140005a500403401518240860905031000709a910709006075008040c0003501130310003c90000356910031544a55405071003210b40c4136080e03a95084001d08050b032404050006002904ca = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 154397796 1250 154396546 154396591
    0x3020d020402070f1e03090b0a020c100504050415090e0a0807080a11030309011b0f140703090f030b0403030c050a08061918060f06090b1602180903090102060708 71
    0x14040305004010f2102c0d0007510307444900900040c01c5c094021604442c840783c09142e400008000a081c10b401054500158810300035501c02182c2c085038481d02c070009840c407043d03001d442202e0003400f000e802807000d0801e1040c0c5076181485485041405400c103000650a0300c008121040101e42c0100001d080016540b11041070381c020b055100d00b40045076800120801040019622403080100007280614990309201001c00f0104000d20512582001550703640c2e41000f084510362400e01040307604c81e04982012030700e01c516076114009c0100003c00c00b20a208082030218440e40c042c1d1010b102c11040c071001241e182c840d000d4100001020705005c115545011901c4410940c01500f0007034660b0385441c0000160b900240b003c000e590b540310380401c81025042c032500020615410007109591070805803141a20600d06401c0c50003000d015078a0456540c5004000005c0d9030b0310540c001403910b54109aa240c0c01385e00da0300e02501c50b0b20002014a84100d00c0b442c480d00400c01d00680b901041203 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 154399046 1250 154397796 154397801
    0x605010f03021c14060f010e13020711091e1005011407050f061e13050628021204020f0901080c12030c1605011407080a0f030906050c1305030703020d0204 68
    0x540d00c00940321110009440902c40c040c450410004c0300c100f422a040c11001c0282181142d090141444450003040e03000d46d4030000b58045130f40481d070340541c1c0c0382598600268103047ea90803041d8060000818410030447c2080d14030b00c0301c590403c07895161303210114080410315461045500050002c11b1624003c101a400741402c68820742c102d502803103a0007200c03801c041080f50207285956400b5988503501005082040d0084516840394a464801da02c802c1d0710350500800c540f90914500a0071150061404e010720410340f1609800c54449460030390010242809076401e82c42540244014045c2d45001d900580c100d072042d40051480342400020700c00004846080041640800d00204c1c2030160300344001c048404c8160060300701c043c1040009080b8401a0300303100c8101406129910003e84030f0001c46140310305604100980c0c603801c1c4400c5000d030081e070b40003c2c20282010248204654181c0141070881c4003480540070140c0ca8005042e6070f0030891001940c002c0b0800044005400d040c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 154400296 1250 154399046 154399057
    0x4120203010b040609201903020a0c080403030807080901051014010504050a1401081b041406041d01062309060f0910080106020d09080628060b13090605010f0302 71
    0x9400810344582c01e50000c3c04440840e448000e825131100300344012910840c0780a40e070361810400d030a00b00b2001400808170044585020320603d0703030010b03000c0d100600441e50f100865601c1050103903a65101d24006084110a0b50307100003092914001c12019201030003040d2041805201c010300880c582240c00764200303a089299410b0000c10000070580307480d291028405441c01d00761001070040000001440c003940100070940d2000c80d0f003211019004504100c1d8102e91400c14250389410b24800014203521aa43c0f0036044043c00081080c070188070ba840a504030382c000c1c0c0358440d50028804548100070f00340368100607070b1801048a50002c0c60807001a18840e08a03800d5036051081e41c0d80491480204801c2c448081030441c4010040c4503410020885045000d14044007207a10700914290348420141846040c0c803400c0c0d000d0044a01c4000d00d0701c5807214035034014000241c1d10341c3d072182c0e9540b00500c4460480c00c0064042081c0030240280001c892041c5d5400d81c400049900403030003504503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 154401546 1250 154400296 154400299
    0xf06130e01020414190b04090e0114070305070206070504151202040b0a050d1a090a0207020d020402030106030c0e06031b0711030a0308070e040e03040501050702030a050105130521041202 82
    0x350600081858401d00c041c001074010101036040f0110500200056080c14900700401c5038014442449854000701c29102150b10001001c108800720222550140c80e190144954500d0b40000b00159150301d5000305001c0d0400c0d80985140e41c64110701200c4a10550140e840310b55a1a0780201e1041e20424100b4803070030500c900142071507110600380c00243d104601440018101068600d00f040240c89418204511007180c02007082c04c840208143c000e00030480038aa941c0070841d4015074840201d899001540184219500d60312484042d000705481300d04800000e02081c2030301c4960501c013003101c1c0650701543c0280240302451810211a5002141c00c641940c0c110311030100c00c2d01c0c2001544070151083d2510441c600c1c1002000f0032280c076074003140c0e00c20340c1000d84105004001008030b50540c0c43c00e02c2c05681c0e540043c00802c2c40c04441c003000400561a00c810480f04002c3d51801d9400584a0420341764802100c1059800c2d180206005100030181084100440c24120002a00e214030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 154402796 1250 154401546 154401551
    0x130305250507030515070318080903010b040e0f0106050d050705041d0d020106060807030b010926070b03090c03061e10030b1003060e150a0509032503020c090f0613 72
    0x240d9541d000e04101c0c183e4000c59040d400352441514503921144c101364030103203d280802410300080000314030400c0c0032102810000340007030b111580380c400390800300016001034000c0c071000301c00604940d5554135068a05501d5413030000e000c01c0c40d10300080065415034001c0d0080c54050b0801c1304001c0201400c44105070582c146082c01c04680f0020310412035030041076000015001c3c03410a01600d002e40050291040501d030822010250382c10000b102c0a855800c410040c003a10b0314441840c1c00520480340c02013600c10088001180d0700b03840e00075031203120a1002d40c0c844c0c25084007416600c07038040d900c10300c8101e484a00d0040814001d810036500103640522150071a42d0703912261000c2000342c0da00500010340b950280144403082c00f9010600041c0401441c981c541c602028000d800050903000140c0e4036000881c81c84142003060340c01075860504501100c2d0506001c0d92100d40c0300707000c118098000c5c3d0b41003501d81d01d0820b1005114480850916005503182c20030419184c08082d0f261103601c3c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 154404046 1250 154402796 154402867
    0x10c030e060918040602030f0f061f021006030503130e0105030a080a050d0204030302150c1c0b040204030206040e0a14130b04030210060803040501020f01021918051017130305 77
    0x115143c0d1080c00355002c0c100044c0eaa05100ca070000380014024529000c0b900801c00340007440c7c642c4c0340420a0700e16440362610004a403042c040342040d034a05003444180d400e00401005008010009240035a0101c0c0303d0f840c85030b615500f07901d40303c1003407040d00d40c035400012107000030034100b02c010b101d00c0e8035529240d464005800d04100032600302d81c0050700160300448464100461000529401c13048120307105042c107903c0c2e680300300a5881210421001921140355480988494055501a5500810740c07901c5903142c1000b003482040407600c0090306030920740003010702c60341c10a40c070b4050344081002c0001032043da00c42103c04480a442241140f007520500c29000b2128490b030ba001e80180e1014640d65440d20000a103440f0094484903450307441040a10400c0b0a0307001405101c01450600c802402050242d48a140000751b002c50b4001822a02c40b050581d4003001103404100c2c464044140d41c2c64201159200101c1444001c0114204001c0d990f009070100d40700c0341074a40e494000c5c44858 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 154405296 1250 154404046 154404079
    0x50102070e1b040f0303031a060901030b06040305100c080c04320301060e0106030b01020118140a080f0405130203090d11030d060b0714060f0a020d06080d0e04050105010c030e0609 79
    0x99206074481c06002132241014010140c0c140160400c3c1c03030860141c62615103048000561610036055000c0c18981c1d101d001c170b0b0081d01c0f0003094074010364026003904e0340d01c1c03905040c0314080c003050031a080c002032458002406c0106045c1c29a8191a0306913145800440280d04071400c0754007841484c1050725500c0c010340500c1c3d4090180801070f00032100c403440d05526040d03001d41582c0c91100390b40d06690403c5121600603110010061100342c0204000400d00e82500790380d410140e542038040c000c42c200088852201c5a07020060003190000e5a403551004200f00d424400ca020589095116400c0815414044c0d0704c110f2442e1000380b054000c1d01d181c08103c0c05090222055544034120200010130034505200c81c0c0c4010846101480c0050503440c5820040800b164074000c0c110a811075020550300d0a0340361580c0800040e00d860400c07181900c01d40103001d4840c0325420803062113242003000100341544144581659070b640740d21036008a200130402c000603500f014281a070400307100d40459040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 154406546 1250 154405296 154405351
    0x6090b1602040221010909020d020f061216090617060904030e060d09110d12080405072d080d0c02130b10050c060906040f0f0c030b071d0a050102070e 66
    0x40c2c041051a070b04c410307070341004908121005910003101146400416400750301e42040350f403074032681128040348101b000300010b01d43e0b001c2ca01541d00c0c101040c07030400c85101d0280e002a000305d14143c640e850115903c8038101e4641528009500c3c801d2040400b1035210309190138120340091203400c01d4005041890089007440c0c000e844420112610b5100c49002e018881c42541404031054030a0301c50001c10b9100c0388a980b080844600c10000c03800d0000e000d0003410700a4101800e05881e8041c1c00c10410f50300049044115249e079020714003030003000141114001460b448206080d120f0344400e004940802942034034940d84d05141c50f4407007203280002d41d151002220018155210240c80c2d900c0b0407869890300000400100c42648605c8c14003003c25000502460100c0d071182161006002c1d6150000002d1101d40c401419900c1d20810300451580002003442204500700c140f4030080182d800700502504203100302c5015070031040b400e100c1d4040d00900c6a61108070704205130340d901c002c050746420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 154407796 1250 154406546 154406557
    0xa0504030b33040b120c011d040c050a0e0d02100e010302130611150603070b03040206090310020903010e0718111c140106050703090e190e030c1606090b16020402 71
    0x24800e079490042c81d291901e44994078042100b034600405030503d0341c182507030b66444007000c9411700110303540c0780181f0124007001170b4295001900074844251680d80160282e0840040c49004c02d0966040e60035038140700091244603600149032a80e8400e0f09c48041e90008041407030a810140c003080030200c01030025041c50001c01c0c03da43c1c1c5000384d03403841c2c0e00390b400c004000c880b400c0402080000d06c001c682c2c000514038140d0300c0c8100035641d240c882e4070000c0c410b8806e460341c150f00341c0a0400c04190352401c541c0a4900e0a4040d0028081c0302c0c9000d030405e1b25881c03e4054440709003010009052801400d03801055400310b01e40e041031422100c0040c80c41c3c061411020761141700c0d100d031000e422842800c40e04d180100b0050800c070341001d41e42c1d50041c222000038002e1101c0030703840741c000520f1082008101c0040140c04036040024000c0041880d403264007a114920a5108009044248000c0591103004544c0e8551352000001d0610620f0940369010112441d01040e85844e1b403c0941e980c0c0c80201b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 154409046 1250 154407796 154407871
    0x150d020f0d051e07050105070822050409113a0302071208030105041514281e0b120f0405012a030b1903030806030304030f1b08030a0504030b 62
    0x104400950880c40e240124a402450411030180840d0740009c007808103448096100140b090303410903030010440500307112a402560701c94101149803082c04800c001c1c1e2081d4203016554100855026644002e5100201c6000603681c5242120f1198801c680c0c008402828482e02c10745040550352001320800002e81d910944c1e0407c0008010416450144103a001c0181100e008800007450a074002200302c400c5c404040c007800c0c22059a4510850204c0040b40d030045051400c1083e60b290702100017029040d041400e41036580a0004c1464614501950000391041360001c0301d07039036004d103901081d020250003201c056480f400f40b40c01407030402c01411650107040300c20b5083c040080800a0507103958200d124058120f02c0d043c0c400c000381c06c090b03410960741c250502c03440075111503002c80c0c510f200700d901c06015600c0c07115000c1c00300310080f03c8003801c40000c2c3d004100b80b141c036000843e8413440340c4006000852410401040000e6070020019400848036596140050444807482c0c3c100c8044c0c08140e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 154410296 1250 154409046 154409083
    0x40f06210e03030f0604051302010c0c0b1602040e0a0c0512010f110705060f0601121a0603010803070c0609060503040b06011101110408010e0c030a0b13050f0114150d020f0d05 77
    0x1200340c2c1c00145044d64071110491302807060703007008006c0d811040f6945c0400390402103000503150500400081030002071111510695440c846c4040c04040d002c444d100491051b4101105014010000191400007a8004a6030b2000c6443c290030000280746104c441c0301c240d500e91801200c21401c070310411103001c09030050780f60340e400b00385080c0b030402600a001c128022144024400f80340d81c441c00c88220951440707000600900c0e0300320100701c02c102e2010030682c000c1000002007039002000c000707040c00610508503422400c0d100c0701c0666102081d4052440003500500004010903101c0b54684d42120042c140142c0300e517480301d105402d4415125200b42201c000150410007070001b4403843c034054400602900c04603040500081d110344841101030f0108a0020114100d660100d0203141d40c6903000b411201c12000d6156070b14081d09446100380059a0003200051850701c0ca200c000c84d24001c010030b000c82d140e41079400c0000b030501c441c0001e40c0203048000c1e0b20000070820003003030b1001010000395 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 154411546 1250 154410296 154410301
    0x9030f01151a0310090c030e06090a020108090f0d0e0a0b0315100302070503122701090309060c1104050411120a0209010801090c2102060a0e010f05040f06210e0303 72
    0x802c02d2a00e50504070358004001300f10b45540350309140c10a0300c80c280800700da82c1c01c01040440142004080907181401084180301c0c09200c00504051500d01c01c1c3c9848030301d0b40d103c00d040b0381c440e210400d00703200b1504198111001c071489101014103050000f0054022152502c0c80030f65950000c480c00d13040030780e50950340d20a03071800054180320310801d407909610f00610f5039616a00d9000c1c4607041243c410500c800300b00d8080c07000c0b12104041d0701c055502541030781c803050060b011701910102640803c0203010003140a511814a5261940c1c1011480080403a48010310000300801801a900c907403484403452042c0d42d0f45e944080004040b040109005c1c0354500400402d036006a02c401e45681c54500c2240005030700c0d0298000301c42d2032518104200144c10740341012a2100080294804d078002008800d01c2c0d08402c0034a42c400007a40c80321654803440800391900d1040b03000c1d6000c140161182088010f200d00d00360b4034007108121581140945140d20107050380d20346010f40f44a50004803c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 154412796 1250 154411546 154411559
    0x9030306040e010b032a030d081f0e0606030717010b0403150612021e031c110a02090a0b0402041802030405061308031311030a0c21080f09030f0115 65
    0x5814010300c6054020002e080300d040000c2d94130b85180e5000081e1b004009500b10705140751180c01045000068142e07507031821550303c018100e8108903082c41255014100d07070b0f05408420032150003501c04888812090707480c3c883c100001904010301150030002000500c0f01c8030005800349038003d0140b001c10a03240e50461810403030152820301c010b01160710700001001001701801315030000f660161421203400d941106006040920540c0301c030740610a204c5404940d420345030840c3c0507280c240d580d14440343c1956500a4561840500195110f0952004220546115880500e015400400c0103180c241c0c1d5100403081d091075029000c990a9000c001c101c140041807020036840004226072581c1020740d07548100c0c01d07020280c800000120f0640f503420410860050200030018020210340354010f0350324103481d44071303000d01625018041d100b1519080815803840141941c1e40007009070b0528089000c000600d820900180d90b0510030030030303440c1680c0000c0c42862501c01c210482c00505038103008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 154414046 1250 154412796 154412801
    0x1a040524070c1707061707050903100606050702100813021c0f0f05010e030a0f0806040f05250e060706110919080c0604050105030f0601030b0303040b041707050a0b03070c0b0903030604 81
    0x2804217091003003105c543c1d51090004107030301d0303030104183c1406034841d200ca00109161441200f03400301010310344000810704607046001750617103c0c803c40b008040c0c1200c4000032a0501415100000401c0c40700f03080380b00601e0308180c0302801d19154403000d501d00070562120341414200c400e054807002c4111021302d00740700c0207002d1f4000c8595010300443c54401030b050010300ba41c01d421501c0c4c04220055012810320f5540f50440b864407424804140101c0c100000014465100003a4004140c802d2101a0907a03d029400703c1d400108014061400d1001376196500581413080200003140c0003080f4024030341d940c4c044035076400c64000e40008565410006600d04d44485000200d209060511040100341e030320808036544445c03040c17000d190079241c8070016000b421241c42200c2d454000880d002c96040d5164026008840e551a4038925802c01000456145d5000e4080d05400c07034203107107050020144081c02580c2016951812680506240d103d100000c20240c074181d0b02d60f017000060114924050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 154415296 1250 154414046 154414049
    0xd17070206060901031401061a0c07080d090e0a0b030f1501120b0103080d060803191206030507050d080f0a09080d0921060f0501060206011a040524070c1707 69
    0x203000406003410188006940450140b1000340300304100e000761020f00c1c4082d007080707005064040c91840c213040c0340b000207440c580010382d0141041c4920b510001e6850070003d29805e4081d0181c940c21580d41c01c2c02da0100060000501c0c92400c2c40c0c03550160840d0b51404c100c440304500706640504144040c00241e206c040d03106074028508400e0803d24500426034011580d8116984000c1d07003641c2c0c440a0107003c000c0c002c983e000c0b03802400085100300d5105501c030410b01101c152541c400a02a6070b6402080480d10940030180082d404081c042c84941880b052500c10f241c0280c4400d0f040005060300340125078480c200960020318080c40c01c110320324041008a03201226030a0951001d03041130068503414070300c041f802402010440d040c80030b111003640250003141d086a1f09010320740c0c403040041d5407900284500764444065070010810039842030140d0b01503440040c2980e81110075401100301403a0000c21075a0f0002c010086880040e540b000c7e40002044020325200440c2050a201400e05485 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 154416546 1250 154415296 154415311
    0x7080f0705030402060a0e042a0f08090c1507080d060504060e0f0609070c06060312080c04030302030d150509040f030e0301020703021c090e1f120302150402060c0d17 73
    0x1e100f8440160f03180019245004e81a2a048049001200000c0e0241980c201c2501c4e42850860171044041241c0d12089030f03915654940044880c0003550454030304208444011464111039460000c601d044503281c0068003410038010708080d815260060b030355000302260132107955101410056800c241c0918001040002c82c51400c0b0702d00942c0104280100070003d44c8034a00c850000388010340a040c0d500f402540240301040110b482c3d2034403c05003040d00c100703500442c91180c000351091503000200d4050700d5150307002d14204107804240502400307290039400c0480c3e0390ba22000c9a03d032107040c00c00384682c1c01056814050442ca04000d0040d007021400203000383d00421070300300400c1d00040c401580030080c4034000e0054507011011660795840c0c1d08090050084901070084283c03484c8224600c800840c0344106099644680300607580c000d1600040c0907821409100424940e0082c6003644240040c10741c2c3e19040741c8041030780c00c054240040c0000300d00d148070208441101020704da3f074403041 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 154417796 1250 154416546 154416557
    0x80c1c050703021c08040f0c210203061006090b03062715010806030714030102070c03030c0302060604091104020d0e070b130f1214030705070e1e010b03070c0c0e07080f07 75
    0xc03044020400c505c0200054815041d502030b1200b00505aa4102c005001c0240c541c400c42035131106042040d00b030250180d100340f0034000450f008001038001c0300c0450b949a110400e00c10310b03103050b103080c6400081030031b5441420610b1800aa207c10b40c03007980c0702080300348070303000514060390340c0f08124200d01d12050400a160041001076100080d00c0800c1d00e41040c1c6140c216401c07540041c2c0a0302c109140188181020311001080640090100445600c240c0964506a40d41c0c428407086030303030700d620282200d2001015003495040c55401003011089885000c501040030302c4910749401342c66441949604000508600e100510405600c0030b040c501c0d4144856502e0310b100003c80049405000e0b040f21116106140c002c0760400483e2545c55004042d0f6a10546e03a411721140000c01715940d214140031050390f01d0001c1020403106040c0c42d051010141140c0f41c0b61402c6428560070313003003180d1041840c00d01040700c00320b0b21502c620941ca590354090040c0b600c0302e01440d80f5030380640460103000303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 154419046 1250 154417796 154417843
    0xf170c1b01060620070302130207020a060315050409021201060f1e121b15020a021203030603063709140d090b07080f070b040209100f03080c1c05070302 67
    0x41e8004410b410b1142a4006907120100c904d00941c2030075500c0c2d20080d40031141c4103002150403c02e0300602032050003183e225851659400d82a410b4404514800d56810941c103018000317407503c1e40c0b02e14002c0303001030020340e01800600640c5085a2503038000540c84040b0810030008a03003141c1140384458a21003039928014a0942d10b441d188094400080c0403035030514080090031b003151030f0400200b00b5400c01003402c014041c00a03456107101607099016015400301010341000000449003c2c00010b0010310107640d500c1281c0ba03c13640b44000907054600030020f00100b81500b801c001101070b4182100180307101316450407186034021749800700001d820007a8100e51154120007072400711036040038540d507240f600386411041407041442e0302007042030100d81e141c1400f0320490124442ca2003600d0412080d114542041c044071407504c02d0414034403c1031014000100044003815911058000f2641034802004c1c0460840d0603810360180051008107284043c981e04120303031036852050b4001000c0c0031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 154420296 1250 154419046 154419059
    0x1103030406050703021e0306040f020403050613050f01020a03140117030d05071701090c11070510050c07050307030510200d1a04020d02040e090601060f0f170c1b0106 73
    0x2404018005031106940c0c4002450080c00790301150b030005d1340c42088a000c0d9040c040d40c01c21a800076161140103924140141c0b00b0300540d40308503000d480e0800000c3c4001d80e5503890f10700381101da07400b0490340703801000200c00038180240007403d000b0003287c40c04500d0488180800c4010541607004c0c4280060f1548094140070001c801ca0700010743ea0500403605036540b40c0107803104400c00e111506068814000015501c0c4d440d40540030303016056488410b4058502c04c031581e180d82c0760280c0759020044904848450f401080101544001c40c03081e01c0e01c16590f0300020741400b51642c002e6800c1d8011000d14075861005202d41c1ca5040b10701a0320f61a040c0c1098507641050040f4190241c0003680c818507111116944001c20301c500c5001002036545107141848280650401d1240c000b84920503400302e8968180403681c54141c80140d50703030180c2e041641c8411102400602c9940c000d10107000d40780c0d0345075550b600610f4810751108400c5580e846c1101c581400510f54080e10300c540c0d0345041c0b4140500c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 154421546 1250 154420296 154420303
    0xc0304080606060a08041e0f06060e060d0804181107111002070311010503040203100e1c0509030a030806060d05072f06060402030907080a060c0906080c2d0a0903021011 74
    0x2050300100d5034087c4c103007003160510340b118150f40e0151000540317800c01420400c25412100aa64450b408450151505010711110003940d1100a0824409100c04e200942083c40c0a00030441350b2803021407040f0b450703a401e55241e401010b05036142d25005601c48007030708241e006008610301620041085a2031074036421008514185100d040000c004042003e5543c208402c4100364010601004529410000c955880000000801c0c0c1001801000901d041c060400e40d003e0507005006450720340381c80d5904542075000240b0f0703107511007400d102c1c064089046108451050146845504034600d86460104101600302003218601040e101051070801001c540d0580240c02030f20b01607203a440c1c00440c1d50130089507422292040c85010480000e00c41103810440f44003d641c3c9031700892503201d16048509030000c17146500c8408003004600d81c10100710f440369803082010344102d0b00e1490ac821207281c0c560301c10b03568840001c6041e1410300070b51034080c1322200916000e0600c011144040c0302895203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 154422796 1250 154421546 154421551
    0x8040c032402210618011802040b030901020702180903070f060e010e0a060c08070818010b0603180d050c0d3501080f0703080d021e0c0304080606060a08 67
    0x700c001e85484016000c8045503914840ca80001075440f51503100b00e900c072900d204400592481d400101180e120300700001005501c500009841030560308055055201d407018551000702140d0030000042c6911070a0007070750044000b50000341e42c0d1241801000082c495500d8100008141c20040c402000c00c00012210740541c07154182c1ca1011240c03c04400030b2200c000c000d40075500f85000c1c0d11400301d01145400e20365105030404c000c058002002110200b4085648001141c07210707020039100300260402c040341c40305400021070381000d4400810a550029500294209500740d02001420014444101c40004e03900d8013504102625103100d99494103103c9038410b12035451880c000e1380b6400c15407100309050303400c201c28040401c11f0038801141d40034403a0002d140507001c60201c8854021824200300d81d002000340e4201145402c9000082d4800c50480c00380141e42880c03201c234840f80b00041c00c410020040510b03201c0c1d191001a50600308020203651003140c040005a0015402c04500ca4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 154424046 1250 154422796 154422803
    0x708060a0f05010f0306080d03060306050a05090a14030408030d0c031802030c210102030103110108070f052b0c05040810060315020f04090e060a0b010e03060f06040b0a0305030702010e0108040c03 86
    0x4800501600b80e0040041e038208040900640030240423080e0150000c200301d0f8810b000400c861b603941c2001070103c0d0002d481d0112141c00000a1f9408a8030610341802444040d1007074902e0540d5071030003641341d82c0c0b01d0008000c907240c84103440c03516140c06101d1208a1050010b1907102186d50340c1c0041d403281201700134070384503ca40042c1c40d4422800c6000c000c0281a2035002190f80756124117280304640e5654401d00e00141c540301c002014036106903001030400d0103c0d11402e0500406849030201c60385424075500b84d1114082e1000074052980c010b45801000c2500c4040e074850a202c0041c1c2440c400c1480c603089541418003c01c0010100c00388840c500804070001a200c04200380c5044051107135070b0011542c1400e0038680001c80002180f03850066008013402c0111412001c015039422000100d0396602d9040900090300388004c0c0190783d54406401000029504001c1c0005802c1408a8006403a2617101284c020110350b004203011220500900f00b1001c6480c1aa5800012480600004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 154425296 1250 154424046 154424057
    0x291e091c080a0209030631030c03050319090c03170f09040c090302030307030905030d0305090a020f0a050d050105011802070f03050d06090509060f0a0c02030405040e12040305060708060a0f0501 85
    0x40450102d41d0580e44403007801001e40301941841d00721495500c0241392801c440c0c0b014101101606244440d448807407503450b894440c00034443c0d4401ba0360b0340d0001000002c80c11421542500c203040c840c40380e1041907203d0003c0704025421030918a41178024010132941046c020003000f138081d0113060940d40d00c848111004a034282c00702c1c104441c00c8081d5880290903100c0400d4500805402c0f400d120140c1e0820340490700e1181d00c0000480c181d940030b80c0e0b00c650300c2e0051a010b10150510026100d000400644a104001d90303401c0803a001007401ca10036101650f5400041c403e02060324010a00e25260315800d50600d020b0351034540c00ca034070b0340d1301c01010702c0b03000200e10f0a40b18841c1c00510003081000c404106070300c1d06841042d128581200c0c0384078500c0c0300c2d8001036044a4140301c0e072160801c05900540c01e09050400340700050000391546400ca10450161075104072090000f0006544210041e10300c606101d680a84203031009040303a031003000001d00900140c94024900404c61b802480c02 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 154426546 1250 154425296 154425301
    0xa02060f09300309030a0e01092304090816150e031207030b0310090b06040510050609130e03090a060f02120a0302071a0105030c0405040b04291e091c08 67
    0x40c01a08009000184600c1c40210030031440c44c00103c0944403909517a1502c4c0c000c00c0310710700110388503c0203009601c202880342d848841040207403000b4141800b00540300181e015410f89507000d1680141548801044010060380f003040b4010a89e0040400340c43e205200c0d00740c280024a1700c81c05050b004c1000000b4150019403001e00c6a0450030007014007905039103090310070421550203085045000d841d58001c24000c206141801d1085502c100003256819012900300810405c06500089503240c0c4820310b10755480580001e4032074200c00110809c001d6a55004c40c4007403000d52401d603440107090080ba5822810899008100040c0c0b0f102da00144030760321503201800b40e00034018040050402d0613080c60460040560034030b00c43c1601c0e8110300702d03810040450700700000d49008071401800c50f094400403c0009041308171450b10301d128450036604d00524901750074810041161502e52191514425209650b07e510f1982d0b002070b031280182c03807030302004221f1600c0803d5a165030f60401c000d0000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 154427796 1250 154426546 154426603
    0x30405150a0c2d050c15070f111b060c070504020f0414150706051003050307030207060210230406110c0d2003120601050903071707080a0b0a0504031209080a02060f09 73
    0xc1002900806d4401c1d40799061118009286655404d0b6200c00711b504190081c00c0f9140005c0c0e524040000310703446102250141040c401c490700030301c1496180e8429914041410303a42c0780040c014194084080c16116854460228182182202d405000c0c2c0a0300b03509810001c0c111088404d40e0350000c2c4040b500c0c0e1507084000804030700c25880649a40404221501056804104001280e500f54211000e144041c40150101d82d030b980d4141104207090b40000c19072041700d105460303125000e60400100c114104107840c00c9540064582840e540052450742c408940201140446009103031207040300801840c0c941d560f9220b503040028440340c1d040001001c0e03a00c507c0403100507030801ba094518182e40d8000803200348541e00d81c020700c58090740d00c3c08104c0c0740c400100642c025412050030700c3c07540c90310342c2504001c20004d8003d80c1040801c0c2c9540c0c0303410200e406004069032007107060076039400052100a0170300a026044041c000010800c4c8001070740002945205901c06d2184a44540310104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 154429046 1250 154427796 154427803
    0x60303040b03041b0e090307140304080d090f0609060905040b030c130e010b15030c1b010213032f04020a05091e010f03060f0b030405150a0c2d050c 65
    0x520020740d0407000420042004411041c580c1540300000e950354402d5240e580b5264540c80c12281c501e0180c0c8140007410125140988961203000031105581c50903413211005400d0014541045021541c10801000303e2030340702c0c00303960080c040703440d003040864201000105080c40c0361054521840d202d0740300403540d56090008907a00740c40100302001d901d14134a00007020382607800784080503510b0030980b2540c50401000800304039968102161441d91403140312001500f0001102c201458003031075004c00300e2801d200600d0440c0050603040301c014075500e401c0200d00000e078402407021503010000c1ca23840d41d04a402c080382c00c20448000da00e80005a60072100c90007142c1801303500c4035648503011250f0382040860243d0b40f1081e40d0b10134099503000d60640960b9800c1c0f09540301020b94071810018194460041c6030854860815a8803500f4089400807240c3c0b000c1e01d03001d210036501c1c19441011600100c0400400c1c800c44001743d490941c1000480681139011140390a0240010305541d11000030b0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 154430296 1250 154429046 154429049
    0x10f0e04060311150903030706090f150204141c02042003011d010501140306090402010c0f03020f06010501030e030702100507081b010c08062101020c0d0c05010b1507030806030304 79
    0x360003040380c16038a0402c04040c03624030601a0007101c0081440ea40c0920302c4003210940e05001c0e005518000c070503605c600003042c1c000020303035450001c000600d0004101c006003403840c255010f80980c5035070809000d81100002000001d200d811000720b1440d50b941001c0c01d40c80c0080d0100c50029204507040c1105654400c42040c3d04001400000042030440440c002c913850601c80d00c0000702a81c3c4c803a030065607480300c41c60024980000500029a0720700e005001c5a6000d441850045041c251507500c10791300220a282c01c5000da0841800c0c460000400c014044c01054240b8040c840d00740b504134201e40341d10500e0030107170180105019015070320b4000c1d021214002e900c4071000756106101e00304002050300d260004400c950a004070030001c00d01c41d140c820300403000100603e1246070106001d01110703910191060255400303101d600c102c2d0006010222403e2540e8880440e505600e00c0c2032400c44020002c0c1c1881442001e0124030700ba521a0261400c01d645410004440d8603000002031850080307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 154431546 1250 154430296 154430299
    0x60906060b041205060c0a080109021303060c03020903062203050c010605060f0403060609090c0605030702010b090114030709092406211a06220207020d050a020a14010905010f0e 78
    0x20700010719400721001042c06900410903504991203503004001b562080c2890180066070000c01480701c0300c090350081038000140d89104001c556207035682c1d802d44840b5656400403e5010805299a050505c55aa801041d101286494030484682d80e205190b05400103000c0102c003042c200e1580c41c003580300301c01a0200400c40381c0c888943ea0014030440d03120340011602c4e281418000690b80c40c040c0100000954002c0f52144145d052010031142600000d04500840d901e034580b0642a07140d90350401e0182002d41e00800314480e05d801450303e0f10140d6031001c400031707203041c41c40004a85520001007200c14611030915003141c2c9000e40310042d00c643e03000f01101714550089981d0107801d0000040b0017601c80d507043c00c40e4104070581c0b4440741004490702500708003002c0d1084c1205c40c41c05a442681c01c9501e01c01403c0c120103070003003000d114201204032603d5024021050540c90909034240c010b0501146a003007030742c5103100003001e0500f140300d02410700c1060085030030224090f100c2007075403500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 154432796 1250 154431546 154431569
    0x10e030d05011502010b0604030303181502090307140a030303090302071505040e33041d03090418030e06030c0c01020a1206050301060e1807050901090e0c0405010303080406090606 79
    0x218090810003410300307200701c03040f507404580c4440403035006000e08081c10000170301503410686182c5003500a0444110503100d82e04000e9074800024030141101000048619001a210000542494900440d43d040380070480f21001d04005107584482e007080680f0781c07600d00803810450301d1805914088080c2c0003074034040c3c215601d80101d02e500c8805003003154070f4a210440d041c0ca48001180c0f8100340d20307a41d0000b000c40c0041d00148810048030140164802800010703607071702d12107211401c070300c0d84010b420656000041d15504502d0207000b03d101882c0c864420910000b20703560f0281c82c89800c10301d03040c001c0c0d00110010307440441d14029100e507511031a00955845803102c4004000070448516001210303c2c208005c6040c1c1814031550042d076100d00c6401c503003612115181c842d03116071080c54088a1249410120311a1103d200040c001c003245ea07004a40012560382050030040904003180c0901e00e410010000b1035408521181c10541100e0000799403e082d090400c06410242c00c041c05158 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 154434046 1250 154432796 154432807
    0x206070305190e2817030306030601060e030303070c02010e06031f0b0301080309010c02130212041e02010f0e2e020111040b07021302040e0a0e0609060c031305010e03 73
    0x1900320000305480c280c0300d48030002c0034000d11000d41c0d90460442c4070741d400840c024540302d80c801c148212254009802c84070749201c29515809a135080c2010310601c40d080c1c2000c014051942801c22240b40580034031308010f10350109050100787d503404018180420802d8400300d4030f0640e4010701004450b07417070140c5401d54a20340414100c0070402103070425082001c0c0c00400040c0c0b0000364060b030b81610101c4c00a180f41c42c9482c0011681d9a00910050303901c000815103080001d1440c0c4002e08090b0b22580a030f00c420b103050b090098501c0c0c1c01450b2920001b6000b45121300503a4440d004a07401e40c036508204031600d5140001c80e0001c1742c00c0303600d03500003882007614806044020140001e0345909500138440d030820040040340038000d62003024500c050074803260b801444d03d15180c04018018079401801c1584e40c403040d00c0d620038155401c7e04459a5083c00744012201844a04d0380200c54000030812030403c005412607500c001031840f41410b50028035a82001030070340018110251500c05c03280c891 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 154435296 1250 154434046 154434053
    0x203092b0b01060807030b010905010e060f0c1509032b020c0a05010509191e1407060305060f04020705070614070b0103152415030b0907020d1d0f130603020607 70
    0x6000b8060400404c900a00080c0041e1103400761031076010042c0d440503460b40c9408015160059002c0200707512030010700c4514404c1c48800094410441450000c040064184554842d8801c015003040072039042041401c2c1e5051505074695035286000f90b21149510500c8641e000034000d01160901a002e24a45403042c40700c1500081d0207248030200352001e4144c8002407244603441c80c003006001c1c1c4600714604041015011881903400d000e03000c00c1c443c00c8442c00c801c03403c1813015001070b80880d6540c002d01c04181080b0b000c0005100c030030b0710118601115500c45a55509440c800c180802501100c0c800300780d001e54098480c5c2c01d60255000044e56142d152030403110202500ca42406450309000160403260200c443c0510074081e81d003008002d051000200303415048480180501d602c0c0c3c042e00080c0d456050420344201403640c060101c2c00c2100100034160740d40781d03100b5a840594040c41d41a40d44d2950011112000c0850784002042c1d24000301d0f40250105174006584801c0106041091 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 154436546 1250 154435296 154435313
    0x190f0212030424020d150f050312091801030b0f0a020a0503060f01180308040504050c07150902061201031101142502030a0f0c0905010b0406080402011101150603091e030203092b 78
    0x2c0c81507008022581c07611f442c1c4241c00800980304982e4154418410541c0d041190700007040c210001030602c828248020040b100584e0b400e81c01103a1b04a011000c02c000316034807100458001000e076100f540f604d0b14000c030050040c00003401c5a4410031241c50015660380c06054620500904282e103504c0107a0341e4180450030f9041449010b02860a00c4000b940302a1502e046903c03656010020705811110030f0a02e000528086808070b030403100400900d240b01104481060080d4402e20034403558644510004000f0108004000101c103018042e6000c00300b9102400302c081c502403c400e013140061400028600380343d00c403000c0e1000d1200c0368890107102d003c03103100c4103956245006006599a500000b1054800d40c42520002100c0320007003801076105a44003842070000310004915005009290b90b50030001e644008003190341c07000c1c803008001103180c4c0500c0516031504960780385510740e180a5201d11802d08050302c81c0169202c41c1441c1310200032103808542400d0b82400305070300c003842d14025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 154437796 1250 154436546 154436561
    0xa06020f060108010b030604080d0f09110414090717070b0408060907080706050d0f09060f1a040902030319090816030308010506090a05100207030602190f0212030424020d 75
    0x3031a010300030010900b044140035541d0140c001030b008028550b40d503201e0340810341240e400034009549030303505041c07000128040c3c0f24a1038080c65890300f840140508000441b40d2071500b401d4140d200070100a84407001141010071103000c02007a4003407a0441e03419505100064000b845079a0002c40c0c00310b50b07180c001609503c40c0d4a1401152100c540710500d841d580c10300c61140000191080203000d11a17440c41e0081c20b0b011031250008601e08086030703640003e80b4045e0286451581d07484031111a2803003050000c1c8180036054408000410700c0b80c020039240d1041c440590b104014029034003007440d00c200e4040c07004080100582e100c040110080c12550740351840300340c0001d030340d4500120f440e01c0c00b242100c00340c4800401140c030700c40c03610040c0b14074030012a03054410342c02580d1000000c2a00d45c0020002207103802002401d034002c3e40e03000343c28500c038170100d0400c40d030107004584045001101140e4006030400303403000e9400c45400910000b41050000c80b0403c90003c580800020210f800403036 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 154439046 1250 154437796 154437823
    0x50705030f0304140103110408100b130605011407110d030e011d03030703030f150306020405030601090606020d08061f17010e060a031518050706020f06060d12020c0a0602 75
    0x80300181c4420005070b89000d0b0740074101c2440c0f0200312400c25580a0391009031010111a1814201030f562510981054804445000300e40d07200e51304000180b41c00d00440d10308035810141080114203040000b05084120f0300c00e00030010700000e50314248040b04014040d5030100401850300100c203498002d02c0901e0300d02103580495030a00c0c0071139004d02c80f060304940030740f00940110305220594a0440203400c0f03503403040c144c40342d07102c0740c0105554a40301c0400141d0300510000d07940b2440c2c0b0b0b00789440c00c04164007050709586070490611501ea40031858006280142ca0030f5041512a800000e40b4100d090248408118400f88555072850f0410440d00000340050512000e0382e03a034130400300c1507060881300980e028100410510010b00c0d4080404542d03103080c075000400c00c00d4508040c0941c03072050030130340310b40c1c2c0011010400242e0400901c800765001070054046400c0901c0811080d24800100400d24102c2200d20350f0660710030054803a800701d00515403058a81c0d2410007a440300d075402e40c0e20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 154440296 1250 154439046 154439053
    0x6030b040507030b0a09170a03090c06110c060408060718080601090b01020d0807080c070302030409050403030905060a09110d02060c0a06150617010306050c130801050109180f03080c0d02040305070503 88
    0x2c02c01e807918411100c486807c91010381070a840e081c80f4003150b500031805c1074141035a924903040414060301c1c0303d40180040340c440b02d5541414100b442d282000e0500c1c2c0b030344110400c00c010321040c0030215031a500312009041c00010045410301e018050a041d8014400c0d600c203040000030440015004044121020707000e1307848003142d40360101d81c040c82c119403030303004121040c011420307000310300004090490192041d81d00b4180c0b910b451000f5101c060380c0640019840300c07803100a00800b0b108041e04070600c0e603010406c103071890b0340b40800d160300304810038843c001246034bd6043d0b403540300c1102c0440720b4031f070700340c4202c2c001d50701c0c0c40700081002c0e0810200801821001059030703070040100109100c8003075120786c207503031a5940b50360142c48000d04400912500b070100001d2410f403400d0031409040300400100303443d0304000821044441e8900c401c50f07c1d00780c4105c03542c0483c00070150034604541516108a5a42d50400b00b800c443c0301c2c5000e03041d4940c2c03001a0000900101107200c505039841101034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 154441546 1250 154440296 154440301
    0x51606090b0604111e0306040605040908030f0f01140f010507050307060f2909041a011203020615060d240f0f080c130b0f040507080910021602090a06030b040507030b 73
    0x4c10750f000c4c10800201600c1601c0849101100c908041c5a04c540b0003003012640c40e07151000b0a058038a2072800b06da0042d0044188100d43c000c180d0300a5000c0c00a01d00000c1640c1342c8185081c1903c1c180650501030084038a001809034810400c8500043e0008101c03a42ea141510b03240d001400d403010b030141c190307183c02d0001308a80314050000e10b0002d910301040d0407602e03d00e01007200c0c0b40d00c090720840c0d00070b00700f90000300243d88514008cc000c005038859846c0954890401901b0950020003101035500800c82e40c04071130f9141000e07070381e000e070701d464000400303d114019203c09900710010001c3c04000c56a000101c903050049045c042d12004440300700b11544d510011540d9103c03103000640e120300c51401c0100d082c540c0e54450160000002d004810315102d8201190403a1030540303542002400800401c41841802c11207101a00d1141d0011442d042400c10708401100c180c0c0030081c455200903000c00c4417101a0340180000e5070b0041c5c240755580c2080d144c0256a5403181c40700329175014081c0c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 154442796 1250 154441546 154441571
    0x70614090708010b06040302013914010c0512150306090d0e0409020a0e0a0b04050403080103140a020105042117072306040803040201180f140a080d051606090b0604 72
    0x504001040040e05c640d04207421a0700644078414104d0038141c40f8203c40901c00321010030004200703032802c0c1c7c11103c14194a82d078103040c0300307034410058002800c0e8108903000800c00d510100702d0301040000c10f0010502d84614414403054006510030940c10710031030b428000c16510200308522640b08a8032103138400c0366440d007804103071045420040e5124165140030080300c0060103510b9401031810500056602c0d0381000901103c1003500c0035030000e0510001802004900c0c0452040511440000d14010220b580020001e21450289590740f048020401003611549814804201d43c490004d5400b075503019405865a00107210175603448030700381c40300c407032404a80f004070840194043c00742119070f6580e158211941d0010740101d04108078198200000980703c01130b134024040110b03c0700403251900504120302412a03c01a01c55602c00304108100b84000684074080489802c1c081e40314150b000746006a48141c00d4081e0401d410b22a6030000c0040d500d4072648191001c07101007100501b800f1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 154444046 1250 154442796 154442801
    0x1092102010f0509100b01110604110a081c031808030903181002070b13170607091401020a06090f08030406151202030d080a110c0708060718060507050307061409070801 74
    0x583c164060703001920b401e241740000b6005501100010f041400111603078046413031a00404a4003590349804d2038083e61968078001d88148000d06aa2004000380000a40041100054145110306150f41c504072100e040500388949110140c010824a45925204040d00e0322980704031404513070201d2400c15400d40707141110b04500ea00b03115500400140b800c040d00f58040341e1002d5200b1404044102000074041e0100410071a00c400c0c9202914030390900c204e02400400c410780012505c4002c0004a44140c0d07030000380d03002519085a00070a9031540c905120001d00c4260601509961000080009101d0380c0e4100712011658500103800c3d1036076492900008501050700203505030003c1035542c811902c582c1c0c003207410000000340040d075469420f0107840540d04c915607211b120303000540108050700d0184107065120640f410000c10002e804104407222280300d000e00800d01c003022072803400703004040041c1c800c120760102d0100002e50a03505150300c401d404641603817961080c0000800c1031041230 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 154445296 1250 154444046 154444051
    0x50d0b1e0c040303140405060703020d0210061a031005060a020307031805090a020d06050307060c0309140a231008040b06010306061d0301090b0f0601080c0a0503160201092102010f05 80
    0x20101d904080c116a03003199018444002229400c03410300c00440c0130744e1194000d03e01e85201f50002c0119032450300f000390505a00c0110b80030600e2a1910410070502c51000103400c0811201036159a42d031250398102081901d900b0407a04075a0100d08074501540020003061030074040d440d001d02c0044100f41100e800801c50003080c2d00039545802084000c40280c0142260719003003400400c540d511400402c1c80c0800d00c0e800305000a90f40c0042c003081c590030102c2d070805451802c0004071400600c3c804125a2005840f990318604011521120300581013000c04a24000080c80300310307404115030004100c013406031800d13544005444007040c8658064131968040b00c80c0c50710781e00a122001205000c0c1070341c03204402034041d521550a240042c11100c03082d449034001001c1040c5500f401c0d000100910001032a03594030640410110106940000c1940e60140b100c903050340a000400104a004d4062041c000b80f0309000c622a0119060031130140700d1080a44e41d0080051400e070403482016210309 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 154446546 1250 154445296 154445311
    0xc100204030c21030507061407091a031015020a140706080105030114040b15030f0303150307120f0602040e1003060c0219150908030109021903050705030f060a050d0b1e 74
    0xc070210100005d0107007001c0d200ea68003441c000500b80c60380030b5030941e0300b0004585039030010301c4441d0180050101c001c402025100e12124550841c903081d075a200c0d00c00c0c00c9020786071940c0e160440401030306200308040304078940e2000a003000308081c003520b0350b5203041c10b0040c0c1004c40c00c144004a02402c0510594101240040e44194103484a4a51032103501020b022101000c444607200c42141d107042100b200c1d401020001190380385007950742e614030310070158200f5200e9040f0728020031903451480e651000280e0400101c40b00070240380742c03240c001d1080350301800c0511195401c011003055058228821240102018000c42014030001c90301c031002d9170f0303d032440f1406203603205001c6901c2a40030041c034403800b100020800c40316150b501c15500240e000400c4182c00003030040410050000c60081c040d02030a040c81281817108014110780001043c2001e24000304c4009025a61801600d000910002d00744442c08806424804051001110060760440e01c040d500d0510300d418240540c442c508 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 154447796 1250 154446546 154446599
    0xc05090108130503040503030c0709110f1c0b041107050705040510030f0813080a17040609090f0617010c0e030307020f010c051c0c02011101050712110c100204030c 72
    0x141c0c0d40c65200d0302c0020a1040e00c0a100c00e001c04505510f0030401481c07040385450050000358500440be005407024000c0c0c83c0342d554810303c4070038503044181c0c0603038a005109400005040c1d0100d994940209005c94100768013030b06181d200e0480c030302c003800104110b6000f1800c1e180000c1e01e503401d00007600c00591310101100740c41d038410008034404000c13003640d2a11075580c081c54880035100000394450150061040303500920300d10390412010000004403208489509401c01d0320f444c10140001140d840364006443e185c81c0404030038441130340b0040c041c01d207029074541c100321130280310760003041c83e10786501c085280310400203410700d000002e07119202c0e0300400c80c95000ba281001110480760010003110349201c0d400301b1002e101e003400e1400000881039a2034070015440c900004003075084d903075a29200750745042c0500c0080b50307014010b4614600c5c000808200d03100b20548280e098801d43c00100074a014038400404a180b50343c000b801200e010f5280e01441b19215659031100110113000414000c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 154449046 1250 154447796 154447801
    0x19060305031801050d02030a05010815040519050f0609010b10020304081c09080307030f1b02090127060b0306010e030d0504051509040207030f1d03150a1509020d0c05090108 76
    0x40041403101030000b0189011410720000e5040035060343c0050b144030340003984400050240c1c007802c001d2403404000c610f000c281142440e485d941d03140c034450701240360140e0000c4440c1081c460104040704c090403411003155024074048190300d00901500c840036218041c03200404c0741d03c501c00803d6505070f0780a440501250819500a0791421a9081064051007004240010802002d00240486500076110002e4484000342c005004020f0a09080442c20401d031958002d42c540040c01c0c0d06640041b080e94486a240c1ca8042c1d104841c3c110305c02c003406040c01c00205804134034202440c000e090030f0321b03070141a600c401d04064580d10540d55040000f04140405c0003c2c1c0380003200b402c6011500c8914500d45065100810182d1b442542c1c1039021030b160065091140340c0c400009d0038403d0785030401000001c140b0000984804101003004011841c84d8089004410190300c0100a42814110b521200d0340c0c030341a19029400003c0ca50f00240d2803c44801c800e00d0041044814095050b5640c3d00e4a5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 154450296 1250 154449046 154449067
    0x501051017060f030a0609030311040e07080403110a030e090105091e0402011206080c01080a0507021b0f0414070f02011406060d0906050a0e011104060e061612081906030503 76
    0x1524024960380c3c0c00340f0310800c000700e0703910188484101140180c40c085100d21103814050261240c035905c0c0242c16404010030082511079419598000c900340c940540c160b203907410101c4200020182c11308150103041c14070030405400201300400c1e91025112495aa070b42d41c010030021242c01c803202644082a030807101050b45280e1102c2e82c0c8644141040081c5135042c5100e28111a40798101410b650710400400c5100e41c0c02100681d030000f0329143c10b000b6880c1141009440f41d040c4c195030101c0e1028943c0c00e031074550f6450840b01000c0e030007500c108054403aa07a42d500d030183d0b0a95110001c1110b82c01002402441806a0b119070401c0c40003480075901c2c2c1d41e05102c1c0302d60004441020a55030b03000b00c10009106402243d0141040e1000443d104c0008203c660856988e141410043c0340200400c01c0f80030b400079190700c0000400c03180c5503210004c1000003204607a0441008000503030007541340182641240955000b0444140c1501c110401d030403004044074124000600b03560b10900804059 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 154451546 1250 154450296 154450337
    0xc0801020a0f1404090515121f0c0509041401061205010e01030f03050d0f0204050a120b01050103020306031006061e08070c14071e14011409241305010305010510 71
    0x182103480207461319255440b40c85004884c0c0581b1b188100c000ba00030303c103949117400080c800907000904080c2485120b40306540d410036444000102034180c541c8000c40045010308140d40006101903c140080c3c1a41c41049400c0002405030401250a00c0305180040c160b510885060791098076480402c1d03421343d03d5080c5204d1442001324100315081044078500d00380760041800855036240003589032414001081003c60003030300804002d464071040c07400880c81c50041641110020301300141c2e2500d0b4080840d041075905021061b4803030400100007842c0d03a1100c020701c00b0a5808100d2120f0420b0a181250040020344220340011030a61222002c00d102d140714030280c09029086030501c0d980d400a0b1900e4039008000c0181c40040028100003000d40821a15403c0d0001d103020364045080358a1510039010700380a0314092402c0101c0115100d17424002c0400200300c02039410303102c51005511050640c0720f800f0305400607091200001d0942407090245130603030019154460400031a0241644 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 154452796 1250 154451546 154451567
    0xd291b07080f1c05010312111203040c05030d02061906060c030809160b04150504080318010903021806030c1c0605130215031e0402100c0f1b030c0801020a0f 69
    0x81000400c204510420440c144614044003d4004115507146041022500070460243d00070f1100d5649009100040421b44400e1150326440054582d12541488000110b6503000250036110340514004250f40008000344182030707002c0f100f88410b4510402038180c40403072207008003060600303070040002400b030900c09078005150700403a0922102c03101c3c080c2c48400e26900121440074001018400c54038044d080c60b50352149422318601d081d107407000260340c0384155050110054080f41546550740c1c4a6040c1c8402142c00501906022030b4030301c04c11b88410020381d10b041c27283c03103200302c180001d051040c83c1144180070303e640e160340d0f11040c2d00c902000d002c000380001c81400090542d48010390320380340204e40d91004890401e84910300810044909030b0341011140c00f50400c0e8041000507a0f8040d24203a09107064a0f1000c4e000c8540d25141001d10706c41a40140705a1088100505412002402030b0441c0e01a4aa1900c150b50310b016071401c0b4070882c10300744001104d07811704018641c000c070072219 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 154454046 1250 154452796 154452817
    0x5070c0b010504090f0510020901081f0302060304080c060f250e06070203011104030b040b1311060a0509030d020102090f0409110402032206050f07020303060307140d291b0708 77
    0xd1452544c6c480b41441c00c034880302c0e5000c82d8041402081d55a00402003584540b480e08500c0ba110600840711114504600c00248a00000400101003080420980d5040003040c000c46030302d420f20a6100380720700c0040310b03203503803024111186d07034600340d0724004180001300c0d50344039001b40f800b450301400890340c083c074000d0f41c0541d08c174078405449a482350020801580900d00c400081d040038900007140389400b07000030010389910100d44c0c0c04100c0c05006400b01d10401c841065540706645400da520b4041e10300025450f0240c0040c140d00755406400810100d13408585903140c18030506c0810044442203c4060045108003012240702c0c00c00d40e0080d81c12480512a440308690424621a44102c440c5d0301201c09035101c805200400322060714054100907940003440c110716044001c00d40c0c811035442046030a05500e0214002c070345480c0304001240350406581ca04580c1c905c0300406907038440d040003c0d010104140000c080c43c10802254420807090358040f881c10250352a81502030300440981c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 154455296 1250 154454046 154454063
    0xf0210021629070c050414011d070314040c030312020408070b0f130605070c050103022b110a030e070501050f070b0a18060e0d020303070f030e0c09071205070c0b01050409 75
    0x1100407902e4009000340c18400c00c010f54401d8108414002a078150046468501d20351000620034201d503a41d0002e040010912840c14070781c0daa90b400c07006031200c0380c001003449850f20184018007001c00b00030029a4041d82f10846031203403c0200740128030661240500c070342c104680a02107260004010181c2d000494400c5062042065110410f04480d038041c00210340006041000c00c10000c0301000100402d0138210b00f070040d800f0040c2940202d410480815065180b03000034205a241c1c00b11907800c0100c4010303078450b01101000340003000c01d80c20009a6105241c40011250b20800c11100b070100c054507030504040451342e441d80074100c0640a0076031245c0380c00015070107252008401d40d0007406108003203001044401c0c014148002c200f804000c6400400400a0725a0800e072044a454494a0002808101c0035209401d16110701c4c0c0855101702540c09000505074480203a2031050a440310400160f100e8031026a5180c401640040ca0b5229202c0100003c2c640340c1e02140c812405000b07131 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 154456546 1250 154455296 154455359
    0xe04020423010303020c0103060b03010603050a0e03031503060105030a050a0b090f010c090509070c1e0309090c09081506030a08090d0204060b030702190803060d02120105040f02100216 81
    0xd84640403512901c405000c4180c800400a255040190700f038511020300781003000a08001d0080ca541c40140210810305441d100800c440c5c0c925640715880258400782aa5103a04096403c40741010154001c1c9110340325800c0085100c0c5008100b58072815031003c0105112181c594610200c0d040081c6005144e0050034200f0319213220030b01541d408143e04c1d6841d1140313281000c04101400b07001600c1401009013414105000400c8002e03058600001403200d01401415483c0440d41e0980e60340000c0c0c8605c0c02c003c2500c070f5250b002509482a078001e081a00c034440c07150400320301c2444046030440d516030b10418081c40440c40100080071600000740c04008101080d8000c1019036600d03070b02510321581d00108121620758117106002070b86401c0d401344a80c08905444551050201608891260340710075800000c550340c8002000d455550040280a98a814140202e5504501c18164000c4004034015403815101040d05580c0c181004590408142040c40b012001200032100880440c2500c20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 154457796 1250 154456546 154456571
    0x601060c0c0e100303091d071d19050901080a0302030906030a060b030403020f0708030a0e1003090f050f010f0b06220f03050303100f0b040e060a030c060c0203011d070e040204 77
    0x15a441003010f072030241c002c0341c40e514001344001c50320b9000050b4003a20200d018041842e845c0155000015864a4025020a0411120300840c0c01c186240c0c040101c6d00c44d440586222814101154000c03141c81c4c21680c0d03201d602d2074440b139039804001c0c0103070020003051405d81f424102550b0000c0c00044000b40e03117034070303a08040095031040d46c054015a1140004564cc25420408603028040c0f400c0554101440703140044c1c0b408031150304440c03151031007000c0403040d644664400c450203600290020300310301e542c3c1016604d8076040d0751000455403c00700b005c0f030034003400e018000f0380003809400c036450302c034542d08550003c8901e0a1181e28240c0080750014610382c0401c12000654010360103140c0d203013444030206440c0c1c0156480861070344166031040190090348070568084a81d50f50820044e980c40c10000742011080740c00040c004031114001150300d551040c081086144250001c000000c96100c90fa4654500d00c1c99402c1d140d030100c80140004039014280541040c8050004030b036001800303a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 154459046 1250 154457796 154457819
    0x10020d060308040306020c07060e01051b0c04050106050c01150303080a050601090305061f120f1407030606060909050f0402060d0e120703030b0a091b0c0503070b0907050a08010605030601060c0c 85
    0x500036582150081844c061074881442303450000c00c0581099032404043e4400680980280e80d019181c075201c0801004200606101c45406c142e0300402c100f00942e10380784003400341d40021030707152259882c1c035000d42458281449028240d9405444444555403145030400c09808001c5c1010b04100040e200000080e9081140e24028201001d0031078140b0350345400c00c40c0d5911076503c00c40c00361006641e034401107105401c12511098000501c27400c010005400140390540c0c540c001090b481c42d00000203001640100e01c4419070780510350600090301e508070710311b01c45081039030b010703500c440100034000507005280e000401e01c19103502030b51400104000383c0304054002e01d0054002c6600c4021180440c60710f504c00401912100a0070400d0140c140d058401120115031040c051043c80c0c2400c00074404e08009490b82c40d64000303000e007154508204065100e07080c511030300c6d004098080021138141d406004072001e80344081c00810240e0300c4d0160403511040711140c1520340c414510804940b01b203c1c01c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 154460296 1250 154459046 154459049
    0x40b0d0507061115040b040f020316090c030b01030e070509061306120209060907091a07051e010b040b03030d0207060605090a0b1e0915041e051e010810020d06030804 73
    0x152100c60345100c00c00c0707840381002d04c1c2c1d4215180700341c114020040044d64035850940c210b904076051000c00e0900f0710200f8071780700d404400184010700000740080d01e009203400ca40080945075800340b1242e0010300040d0144c4003220b820380c00310341005031700744038a0034010345a5074481c000403ea038a030301e0800490181191038540080e0040c00c500385030201542045a0303003503085001030390600c9252400c1d8400400c2074929008a09021f001001560074090105055403aa141c018054500810504901d11410188210072600315402e0146d0749071980742c28801c0c8204280d0250166141c5030350f41d1032840080d0300940d03007240d00303503038600c004100c64441d00279140c4281031941e800914081a9000c0105185598610440740c020100c900c400766100d2181c81900b04244000c0c0e00203d98003000002c0180c483d41e030280c1014680310603864442c0d0000d401441c002d003104180721080e480504124201c0c05c1007402011010317404000a01d21014403507009000d030b03024001001500b280c1360b079156203569215 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 154461546 1250 154460296 154460309
    0x70f051b0109050d0513030f02040605060c0a020a1a22090204030c1a090a05060a021002130e06030604030e0105030a020c014101090207112106070503090705040b0d0507 74
    0x42c2c2040d541040710800c030003501c2c0d00450500da0700742400388185200400c2c01e408014520040d480c0228115120703600900003070000103122075183e0694090099444000000a23440380307017160700008080c50350a208070481001003103442d16050088515000ca004d80031949802e42242d500c00050300ca07000e01c0613202071403041030000c640900c1c0214249402d040c10139000d01d4400304101c020390740e94502110307908a44040e1510361300c274483d1030800d03030902130b80310b001c000c1040c0000b4540f0240900c0e01c12440035501078800c1c155203502c0741010316565220440d0003c01050310501e00048640c014000740d41d20040600b802361400d1030f400600c0b0f0a40e03a4110440b00300d51a071101c246001100c00c01d10070300c0038440490710103110301c040d03500e245918018800c903494641d0000700071040c41400700f02809851006800c008001e001e1041003100281059148106406200c01180042d4820000c072405208402c0c0140a26070900080100401c0c419400c5580096005e200c140080c0d000d00079400140403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 154462796 1250 154461546 154461551
    0xa020d050102130605030c0405040506040f0609020a0f0201090203030a030914120904060603180b07170907090c020313060f09080f0d0e030304050a03060504080702030f03030a0b04050609070f051b01 87
    0x124920400c50f4503068001c4c01c00e101051007002404240c480c251000c890b0111008146901e607240440c00621000103e0203440d4200800441c10700581d4004005c3d40c65140d03200e2503000b4400c50300301e080740c2101c04000e40c10341080003050610361081c1c001010060140b440f5444080f2500e00c43c9190110991002240344000310b1640c403580303020b1184400601060909000f01401c04240c40300d80015020000d04580090011810440c403403070408640e40c1500c400c010700c03030a0101d50140d0321106807140c0c500d624100009084050710220070740d1101c0b4004060051090b00300041660300c0495007040804101d40400005040703907080202104d00080d0b180582900456008010800080c3c0c4043c9030003507008000800113521180c03d02000c4981010002919407141c0c82c00c070b24107101d6280c0196152041150440c0004c2c800700003036002e038040c54410456490380c2018441030b1481103580c103603c015140b000400003400380c807483e030006d140c03480d0007460002c0420700042a000000003030041c903036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 154464046 1250 154462796 154462807
    0x603040c050d1a01050904030206040b0907050307120506150a03060209030c0d11011202390601030b0709120c050609120d0c0c1d010501270e160c0b07110a020d050102 73
    0x140ba0f0845400b629044e6600446031500351006991101d001d0001050038130340f5000500c0c40039003403280030084e05000341595805540c8200900c2c807101c55040030b50342400f03094040b030280a00903008c040b0403031000d00441e44480c91500d40400070340210101c0303500f500a407034002000317551f600e01e82c240742446031801404480100c0e0004240400c440810060700d03104122a401404c05e018402c11004001d80700c05000c00350f031456141a001000301110040c3c440e10001204101c50040818171801c190340ea040300542d6658105c0d80c60412100c03000d040d1190b500ca003072001d401c00e030004003030041c8003800030b00d022940710780304a00e0806801e8500b000900504007100401044001c00402004031000249201c0c9030a07144400080048c402c0a0601c40c0304003108100c3c0e28a800c180085000c0003120403105035550820b540e0350034080301e600d005044144607462a8900401d84072203141e030000c485c1100c1d640c0d088410741d24810b01c0560121a84141040d000050b0780702c2d02c1000495104000241c1c552 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 154465296 1250 154464046 154464083
    0xa060504181401151406041e060f02010b0901151704140c0d0b0f1803030f0402150a0f030509070e0a020703030b09090c01050a050d1b0207050409020607020603040c050d 74
    0x50406180c111101c0e41843c03000204c8903003458410041e03030020744040c401d02d01c0381000150380f442994442e101000c00c1d1f411783c1070360745c8588192404a03441c0c0d071035000c441c0c0d200c808201c1c200c440803528681e0025004c0014403e801801c02040c1e4603000c2802c084451040c83d081a00c04c901c01110704440d100c50f03090203400224428804699180d0080d1819540d0212a030340f40c411600c030041c0003050740d01000001514010410382034000200c20b17101a20b0792401c00350040380e071518085400b0713400b4801c00c60798104004411741c01c69840c1d0506940d074075100032610a0460181c98090803142c0c46121700c4030041602d804420700113010300c1d1030000050307545005160150540c5c2c4100340c090300c9000c01e2401c001c00300a0110704148581800d00e00140d031680080c0e019100780c05442a03415250b40380001110441f0000c5040a03070a800d01d0b001c4170007540c1c0d20010401036502566009400c41d03403d004d09001070410308041c50f00284142050180140c40f2404a0882c0d11800020f8403002091030007484c20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 154466546 1250 154465296 154465313
    0x609030a1b12050705121f0c08010506070b13080d02131a0405060a080405160b0a03050f0108030904020d060305062401020606060708160803160905060307170a06050418 74
    0x10088081d000080c0b0159403245500c03042140b10311400749801c08243c1c403203502d0a1140b01464401d1140c55604c0000d240e541e40010300d0040c0d01c28001c94046070012400c0e1422400342e62040b540801c440c60b081d5210000100c0f001c00100b07040700c80c11300c02d100006c1051307003c1c000350818082c405500031042d0310703001c519481ca40e0141c060722203418003040103011507240c2c20116a0f41d4900c07070405c00199115403621501d0712051003200014a200f1103000705030501d560001f0003580055031b50621060b110b402070040020b0f404e124a0160b9401000084000e060907005001c007a0340b00c010010f25580c0c0d0b82c4070781d418003038201c90000381c010b9040b544074074800078072034420b8200000388010300e40c51620402007042445010780c041c00001e0046141510b212141c041c0c4000d0302e5004001c80d442c0d040c03481c42c20210099a00344900418181c080c00326040c01e1500659103d03802980d035080b40012806503001c06098050254541181c48580c0420b041d00c95024802c010101d01c40c2d1141001036a0a04a00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 154467796 1250 154466546 154466549
    0xf02030f0124120210050703050405362412100605240301030206030c09131b020c13020c0f03030903090a12020a0e0601090509040b0f10060903030e0609030a1b 70
    0x840203400300c03e0034050b0b164000c1c403c01d41c280600309076940d4a41c90074203440c0e60090340d204591001001001c10009020800c041e41400304940009000030041d101e24000c241e811502011901c0003038010088a40041d4a4a08000c43c09024805a5500400e0b010b007401090810030004a4944004100c1800e160403c2d008c4003002800350902d000103498026441d100622029110320808000f240da14006903045440000d0300814004c0004288a0728401600901c1e150403075500e10071082e268242d0020851505208009044006005007810300c440250021030448a0b944141144044658001c1004500901d080c000840d1030306514402c11100391005d030840d00c000e0410070440b90060708c6448505064030802e0342503003039a94034100101c0300c80110764861540704903540c00b40030600455403142030142e40355411a001a90714010824a00005480303481c0000c0d41504c010008a40b05841c02181148001c2040c0d103000e4042000928100b0b0504007500c0b5a00801036814000c0000c415220 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 154469046 1250 154467796 154467809
    0x308090703030e041d03070b01030b010f0e01030206130519091a03030a030c02120d0e07090905030f0304021c080c0105071409090c090a15081e040f02030f0124 70
    0x4105070859038020200030900c0b0f15180640e4a40c204200807084540c000b0105c51a02d0088070785944441c101031504e80004c0c03100741d0303540901400211380700320315014203801d0301c07006000c89185134a181d0a000d600e502c004010ba100c04803943c40130031a0760310403444445d000812040e4182d4141488034880c122004042581d0404504c000500e03c80c0e01c0c00310a440321015542400140740100311402da05180d41c100c904c0702240400203100c07d00d825640c1c0b201c1a681d410908841401d5150b021410842d043c0300c0c0c6c0a4075990043c0041c02090b43d488004590081c406402403401c641241220001e01d00181400c03503010202198024880000344200c50340241c0ba45800d001c402d40c2040000020b104030f95101e4041c030340120010703070742d882007008a0310001c4006c0c00304503106541c1c03903090703214a5100c0d01714800104c0c900042201071441c0360f10503111007501c401005140d200d0390380b640314800381c254080b81c040c0500034404643d00c07400e21512803100c00ea0107041a06124101107c0c2000c60b20341c2006 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 154470296 1250 154469046 154469053
    0x18080604140d030204032d0803100f090204060c0f05010b10030c02060703060e010902130506030c13090603170a1b0309080d050708070809030304270b01030504020f1c05030c0109030809 81
    0x40010850340007c8104c00d521951406403280d414050001002e032642d00c015001040c00414040c4040032500054115003040880ca40d41c1510b038080c020503403059206003400158031040321408260100070340340c49240704e60000503130030a004000c07484d41c1c0c510340d0402f40480d5699858442d407a4042c05000e07031000c07651504002d020b003030004141a40a040c000d907500340d40c0c040f81192511403585010b00280c00b006101c581c42c9d145c0b8003145649039000615a10307418030522030018484c0c41c603008036010783c1d42c4580000c0141d1140428000203420110b400000c1150381d06080074016084103c1044082c007a5031041e940e0f60070302c00f0b02e81c901401102901e08000301040071a0110700a0f4040d21000c030340c4184130942c1e0311825800a481c601030f40d04450703400e030110301c10740034514140429180b05928280c800d015a1110342c0043d412603c007124041c0d045100ca1404201624040c00c5194070003602d64114000400b1548489145411a90442125a654100301d5062642058407154005600c4008 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 154471546 1250 154470296 154470299
    0xb04030e0d030807050c1608070501091d0a0906060306020706090507060507030206060f180109020705060601030e0c040e1e030706051b19020709050405010c1206050f0118080604140d030204 83
    0x1410510000d1118041103008120702c4461b40c0140084a60b00014044284078680c50302d0907a91038171b00c54401c241c0482e1952000080c3d10f0b2040d00e082a100081030307110000c655a03800c6810203403411880855000c0d64481c408000034101c1d102818103140102c100290320005803800038075001181c1c20202c103200e024400140000d600180090740403500b501c3c039050032034000d004a1300c0703d401c1000900b12a14030b103001140900e101c0d80a0301c0494003ea040700c0c0300f6100c003801074041302d02c121403130340040c1c00030001600503051903000001c09080e100221041455011000e0861044280300c0303007615040007448409107c441d00401d5002909503003040080c0d100c030303e4200a130384100f45000070000e0305081356056941c0203018903001000340082c140050f2804c0d00d00f00c1d008000c2003030f02c40b02240142041400ca07415612a0b1002d03600064000d6849480102c015038000c0c03541c1d1910b080700b01c0095000320300c8007002d110301809540b0031806091242c0840c01c003941040441460700041503c103000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 154472796 1250 154471546 154471553
    0x90c080a060b120c0d02040b03060f070207050108010f060f0207050402031f0506030105060304120306090504030905120f07091104030f050d0807050705120702010c020a0608060117040507151b0b04030e0d 89
    0x80000c400300c01100c500b8030351740300d620200307016006150006030325004120401141100c1e403940a48100c2c035550036074022a031100700640310150300f0300900704840040c090500c4420301612800c0e03040c403040d0044a003103940da07000140603070b44112500c050301c80c0318189450548505003c058080d044c101c41d09400c0d50705050200340c5e030f40002840601554909041814824040d0380140c0180c03049101c140035900d003604001c1c0c4082ca4074822940114004d16980c40315040c0030403a0142443d100001d010404d20b0440041c025010300702d5039901c428010003002002540e40c10503504180d1003030b0060b0007803c60880c0050582c84000700050305105040048400251021809072407204400000039188c03c03007400101c5000079501c4000750020380501c0c1c003050aa4000000e20b00c25030090380d42081c6100c08268003000207100b6100104181d2185c8400e00c282d41000b594400782a00a02d40030f038007417030310340c2503088031080d241c4080d50694800d1041c0014542d2114880e14111000e4451100031001540c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 154474046 1250 154472796 154472803
    0x6020706090807120f170703090e0703050f0c0a11030d0509071a0a05070f02060d0902040509030c0601141512011a04032f0301020c0601051306080604030c020103090c080a060b12 78
    0x30000b0701d0a840150386404201c80200d401c4e0541b00c05c440c0682e00c0c0c0380a880c3c0580090600d000e42d81349400071000040003a4440d02400b88680704c030b2001c003411600c801c000d00c8085e42003141a501400346084820b524800c00704098800c80040e80b00c04501401e1003030160b418018150020707400440d0381140e142c10f158200b0100c0c0d65011075480c00545e5410039040c000d8022107200002903002a0004000e401116907801c060340d950700803502040039485101c2065964031030380d0384090782600310740010001c5201c0c064400403600d0b8040c00c0e1961042c04881c2c2030020342c0c050300c011003482074600018030140d0041070003005c00c00d078506c07406840d003411521101c64081d000005049913004001414030424810818092884c00c00b60080d51140070504290781c8070142409103600815080810800240030340c014242120707042406040c880c1c480d501c1c11513a50303075400c200781d0605443d495150000340302d8002c40c40c01040148040d141d0900d06207014030507907032403c085510451010446881a10002c17 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 154475296 1250 154474046 154474079
    0xf0f05011a0a0822030c0203070b03130f02060903160e01080706120c02010b040c03020d1112010e070c05060114180f060409150501030305090901080f03030601080703090c06020706090807 82
    0xc0c141801c240c1c0d40c03001680c00c00711803000348900d6013548000d65010542c10440b14500244202c060310101a220440f481c210300040384e84e6003000044070400c00100340c41d422094155400a0300940c941510b12002ca46030011110b00a50080d5400300200702001c01c14414074098004080075003209458003000900102da04280100030135950070300d04401900035440711000c03010281c824030642803680801380081d041070718800252070070b00990541c0f0b4802041224258240780d280b200a0744d0030441039800c11100105818180802d005080001c00d804002076030080c036800341c2012116402200b40400b85280042e0f000340c891110061050f001146091540e10040544000031250320350700380818040c000b1020352810350324200000c000d159110700108200c40c1c0c180c07541841a641c81c021550768860108204005401c24004244070358404c0b00750903005401443c02168030307032343c0c0e45460700091001d07804000581c1c0300c0e040810074203030021088001440d002016204e8546407002c4501d009045 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 154476546 1250 154475296 154475317
    0x32070e1002150c04140901030f17070b010b041406070c14010c0807050c01020c0d0b0703020703090305010f0606030f0209030a080702030f06070305060411090616060204090f0f05011a 80
    0x104008000480c820003800c1414450780d003041219080c0502992100d501030301031082450310003c1011110305090a0050480746d01081214428010360ad4408000d0405076400d1000c040030080c40c404151b0704581c0c9400f800210304a50b0b640da2612800381986082000d5540c0504028006500401d901902c43e00032035102c01e1525542c401c800004807003424525400805108000c144001840400546c040d41c05100781c0854607650740160410090744080d41e40104410024800207041c40c0c0b00f500640015446030030141100d944a56505003982e00000009545c0c41e1b03540c1040186d280d050081019440c6086801c524103161540407030303250314000c180070f000c8410004840c0115141001410b0800c0711000981e4401e041c025802405040e0680f4528031450900c0c003c001016035a404990368040001c20b120301d02082848095034003e00200240d501a03400c0c0400a0600c085000d01c00717542c1c00a1000064900618001004464068014918001c000d200300200202180c0480303d00b40d89 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 154477796 1250 154476546 154476559
    0x120d02090301051b1c2003041415040303020c010b0d0f0506060406081207080c06040c1d0c18040b09070e19030b040816170409140601080703020a050403050132070e 72
    0x70124540700180c060300e9680010210b80072801801b2520b0040030314019481208002d01004008114070b54961483c0340099034800b494002c100003034080d60003001c10020709800071500c862808002043d0714410305e13040e41c01d20392020054007001001d101701580550221020820b0310308000d030640e65080c3d950500314000b140020104144900042a0344110030f050007214110302d06850600e000c81240e100301d011200c40001a5200d55040c40700951080070b00032100c9082891031500001d01171005125103070080c1c1e40307083d0085140c80342248103228070a640c40b401c074030070384c45ca003400804503000308007140c2074400800c14000941c8941c100c91700290000d01c019200ca007501c140724038529401030001c000c0d1803240110340c0e07002c00040150007222480481000340800032a100480240100e450500050801c2c001a41e1207000c1d6000d0044207020b40b6086082c60703201d42e0f4a5086a50700301214003460811312104144420119a003a400c0e15180c141901c2030414400c0940b0540b0220300c1184180b4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 154479046 1250 154477796 154477837
    0x80904020706020f030a0903020d1d01030506060c100b10020c0906040203040201111911060a14030c040810150501050c030403110d0b0f07110d0c080705120d02090301051b 75
    0xb01d0380540d16141040359041356241451403c1d2001001a0b00049005d800740e0741c00c0d03041c8507000d0072203a5254180210300c41040bc0c103a1004500034a0010282544848140403240f81144100041031800e0500540020407071601c82c20001c1c41d0340c03016481411075018440030f921070b44440c00d490303401800c203590150f00d079101e41c4016078103401401c0c1c0c0c503c1a4070902410448030261240681c801d14028201c802406500c04140300152141c03030231038070210380c110303401010120780c1000955021603c4000c19080980394801d05041c060440c0e86031000c9a01c8800b039055680203026404010002400c0180c41e0000240c5603a849010b61310001d80745041100c2c07000950b4465080c2003105942c0080c101e05149000c0da00d281090b0704c00d540c2c01c400201080e4403600d64800020b0720048800b81c0d502ea01840c1c035015541e1910320b50240b0300484190050074001901080242d0160000310300d04c0f2009610f600c2c0315002c0c076007160700043c02ea9807030300394100c050b492120000c000c5440443d10385640070000f6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 154480296 1250 154479046 154479053
    0x2011e170a02070807030e090609063304080c090a0603030206070f0903170d0e0102090102070e0903040302030a030c0302060c04050f0d171602030609010506090c0d2a03050708040809040207 83
    0x340550b807400743c00303e03d0005d848020150301840f50300c144001260750303010f5a01d0707007030500c1720821040300c003141c2103112349080411b641c0c5551600c041241c0700b1604e52980c00034040302c40c2c0441d0060341c050050b99000c4850311400e4580241e03515840509000d040203011b2840c0c030002c1da104005000300003030103050103841120b140303c1c001c107401075600030703d101b0003180030480300e800f4544c03000c504d088060b4a06003941260a606000b1150300c170302d05900a140d50b41c106901c020004101400d403045a100810002006840034484140c4150094460403009812824060b04005000b0309031000460b003040140500e40c1d8000601c8071102d41500d0034140b6481c1482c1007414045540586035004c000403464090702c2442421a21481d0b2003502954600d0303d07841e50081c203840c000c1d204990f0100b10741c0300080307600c220840a800e40007250400490241110a400300503061a4080d0040e0b94603404c13400214242c050107084e030480840c0c44c00656030b00d01a01c8685150103003401452050b0740008800d07050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 154481546 1250 154480296 154480301
    0x8040f0204061503050901060308091c05060a02030f070806012a0b01080f1006080303010332010516081003080a02120c0a0507060203030c09040b0109150c02011e170a 73
    0x69034050020465262514241da12903c0700c0150100000e0802c030006030041010301485044070ba1001056040c01c225504000c4d4041445094440f1817200114600105000301300340c43c010740032100016501e0030898005005684001c08050074801c3d00350a000d6666030120608412503054560007031102080d0310100d00398800c6d480c000d070140b5007040010a2100c0007148402210301d0703010458a4540035a00044203852007072081014540043c401000866144d10680710a9000c03030f18148803640c044034a8807441c60300b44502d1000c80e95124104117142038400903201c03000c405810016101c1c81d1001c42400740e90400d000c000c0c19488085080741c01e40c0c0c001c101c2d104040c42c0034480c09448610f601400b03950f0f000e042d1400c1ea480d21030300f000098054000301c01c982c01924584c4900d4503040c402010300015140c00c001d49410040d034590300085c003107511082c0d5015000c00d543d641d9860107081c000144201c1c00e9090254404468012081c0d0b03c0b038001c0392220324206410566000c0781d5030900401300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 154482796 1250 154481546 154481573
    0x11030d02090423190c0e12030906030f04020a05060408100b04020405040c020a0203010c050307080a0c021501121104050601120e010e0a051609051006081005210c1c02010804 76
    0x2050003508284400d40f0b2518254680328003120180303000065810b00c01c40c1d007541c02d03000e8100040ba410201104403800c00000401030804110120391422210700046216640308554103c6009207003000d0004524084428000502d400c98225003000d04111030076894103ca05d9242440550b00c50840906464a0b0192402894020000c101181006401940f0340740c0c8010120311035440c1540344145240036009507800b803102d55480201d23569403c100140100f134143c00348420b503c1080a18a04260741e02a10b81c0070b482146441480b041c0303249419000e42ca00312a14a120b0360030700040001c242d1b072082071092540c031a0380000c02e44107401c140d50383c010701e1034441542c0e040c001d081015040c440c0000344551105184070309801440d41e1036400804580003941c0c0d011150545080401c405445142d20b03603040b40b200d0001070007165403140015100b41f00790070454000010221120071180b070a00202c8032140d020b4503000c03030700102d5685030a0301c035262040090504c802c04000c941032001d0401d0102e03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 154484046 1250 154482796 154482821
    0x915030402040b0a062105010608060909010908030c07140c100507020d140303040308130809010309142d010b13090c0305061e01080c150c19080d0b0111030d020904 72
    0x4a01d4031000001e29086c00c291002c40c0200d48030003034042d114802c0c81141d041329503d40da0b50149031910000c100ca040f07000780101c8415900c400c58203000c222024000c5008565100b2005e80c0d501032440e00340310400e01c221a001c41a0420091000d068036401402c080703500795807604540d14841071001440507840d1200c060240229981e8500c0c540c80c0c00001940a24080e484600c45c0c1e81c0c42c401e088455081041c4005c114580501c0709103c6540070390040d0300c2840c455000780c40050440388240380f516034a611004104441c0b07000c0302d403a9a401c10003c1440b610340c60021f00c00d40c41c0d12404120820b124060380c9881d00c2e035a95101050209403507c3c20081c540c800c054902d1402c164030003029404003110b10500034074401000252101c07000079413004010019003d0001624014103501c1580c01a8040c2c0038503001c2d400722201030f611180703160543c00d4490f042e01d0761a00e208030190002c82d004483d800d8180207030001c0804480c040007050751a00d21444402507a03546500c1c0101d0050607a000d07403503 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 154485296 1250 154484046 154484059
    0x51203040f09060302120307120503060a0512061906050a0b0c0f0d03021207080108100e0c03030412171c1806020c0309010305070305071b0f080c030a030b0103020915030402040b 78
    0x200b00039200b50800e4040342d000b1100b003a50501461001034403072144200082c00e01c04046114051180a20080c6a11200040046005a80d200080340010420700e84c88855a0007550422480b100403120340c050303181c2400410400306040c0317808210a44800c3c01640014480030035030803030130340081102080442e6882c0554070b1002c806400a0003039000006900f040071941e0002880f0301c0e2050071198100c401c1c03040105401060764080c04000e001d041140c550b213006214000506071000c02c0240002c041080f190080c0700020308220f086000310450360981712104016541c045000200c2d880c0c1a20219035000030b030002d01d240704020040c0c0844d00100f091b80041140d44078800044085d0095a100380c901748102d6594190480444070221031107000315407a0341c0150002100f4546800c0b8107031040800420b0390280b5110815190419105c100103940b00052002c10a940350140600c0001c003805e0a609110350b9500080901d1703140340c1e45a011002c0840060107540d034a4000452030303d4060f104 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 154486546 1250 154485296 154485299
    0x30b040f060617071406030708040f05030301080c0108160807080717010f090c090f0b0c030903060903040f0609080d03020306041b03060602010b0a0308090108060105190801050a06020313051203040f 87
    0xc0c5007000e5502c60740d1000fa0f0054043c00102041c00880041021100400d40c44c5145e48804051310b08050180081d1f520440301c95003c000510204004d6018100c007500403d517281410380010b1031054024640e0b64020060001d010190f13401000700303900140c29062070601c560300d10100322403c0010810008402421000004983c40740e07044460694160450501c54074050001c143d0362b0119a2003501410000600100800041d030009030800300142c0c800e032490f103100030340020701d0002c00340d65041881c3c0000404014850302c41100d00014481400e20045403481c0200e0380781c0390380c0c2c1c3c00c000340d061580010001d01c09545a5108960b5010840014001d40c001400300031300509a40c06101c025601c0d00d40304024900c1d04a2128040300d070f02044091170b151001c001120071220203001141406018415015100480040007440d001940e80d80302c0958074000c1002010300c9241e10400035500100211080682c1001c1c841e000d071402501d0301d4124107500b12040b491880355a00c8100d041e90602c20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 154487796 1250 154486546 154486559
    0x1a1e030613240b0a140a110a06062105030d2a090306060503210904021c050a05010e0c07060902030304180f0b03030405060a2105070203121f030b040f0606 68
    0x600d0701d030700300c2c84004880003a80c4401840c49144141000c0d00042a809800c580000c1c00d184002c000c4903100f0718280901070215544103140290089044450540f10b4505001d583c83c10503141002c140c41c01d011442003803594a80e60784078811185071a094603183c49030300a0a28040395012030400d1010340034004000d0100e00100007404500085170501e04001c00055586800540c0c82c5e100380b50041d07000045000e05a0828482d4440228160415000d000d0582c1ca894085c2406140c1d140e00d140210b01482c3c41c1c4000000c84405800244241d0300d0a4184a050f81c188015214aa41d20490004a00e03000b400002d156008580c80460340c2d400c012485040b06095402c0300e80780f1040f41f44240000080801055240e0050b0b02440f5009003041c809061410f01c0703640c2a0202084c51100b1595852400d4845000d4460031184400560300010b9102241c8100215041e030080c501c400c2c02c074990801440707c400d15046840060000a40c034804502404450901c52440660000007000010758944 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 154489046 1250 154487796 154487831
    0x9030a140a0204050a1b0305040c09090309090509030f03061e130e070f0605030f07140708091014030118270209010603050c090405040302030702030a0605011a1e030613 74
    0x7008a029030f0402c004a00c0180a0b40296140300c48068446400550b20642c2140100002041600e8a4030212800103000030b2030302c903000400307000e80d03241729125007000e010304d041e544058010b00b030307a034420001b00c00b500c0986010f484d040b40f412034181039502c0c032502d0140002c0c0011040c6941c084106401c1441101296016240401e018000e0b01c0103140e4030f5144d41845030651188402040013000018008040c01c40b41c698020700301e00b090303410f1094055400c0c00b160007582080f10710040000320b02d0342e91300c0c007050756074080c40f041d150504110118818020f0617003c10300c1820001c41c4601400c28451050303030000503154544841005120003100c240c0700d1203003001e11099000e92070103800404c00621a01403180f044c0380c030340e0f1103c4c40d10345414244002454000c100381c2c11804107012071401650140302181c0710394022040441c4c65410030900c02050504910745916a0b9010458a001d40082500c1580b001c890150815206d5881e01c0124a9259503940c456076628903007400d6035032015244 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 154490296 1250 154489046 154489063
    0x6020903010f06170307050a02040b1c0303090309090e0d1b1a04140f06071d040507090602060123150f0a0201060801051e130213060b0301031106031b09030a14 70
    0x3030b81c2280a00b2941340c182501c9110f00c940250090b04030302020405405c0c60340048910100c050002c0441382c00e0341e40400140c030882c00d01280026140e007a4041410790000c0035801916044201700000360399601c1c2103a58250003900740041c08500d08040000c034a4500e84070380752a4000010035400c0c8090110b49140b203c0446044612a0340141c910910a40c00151030030103a41400003403440d903c1e80b010a4807161006903940c0d0103000c0d2a0f1009481c1d07122800307064014929074441013400c42c180000a800c0c510143c00503001c3d814036001030a0040b80801404601d21020307181031160320846405003019100d0360360041c0d01c10400040c803c2c00c0c19415403202d030803910191300070001603c4002c4400718580e020444c0440459070f400114407415151a05020182e100403c9a80c90060402d17801d01500c400d80d011015140c4e0200c01001441058203000c4d007003800031264a840c62510b031518000c88510b0f281228500301002c2902d4aa40d06c080000502d860f4010358001c6e0b0300e103542c2171015920005c8 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 154491546 1250 154490296 154490309
    0xa080f01050c07240f11032e0e1312020610120b010509192408010608120a05090d08030712090b0604020c010204150801060f0504050105070f06020903010f06 69
    0x3088002801c1500c4401a66145a40580b42c600c540c0552801100f14066103400440f602d0780d1030400f51011036451190000c00c6e0b2800107810780700d14020f081c1c56650740703804d070100440d10300822181c4420003009040c80182c07410916010566200d080402a041c0c0310301c80700a050200c00c0346100310302d94000608602c07411804881030201c6803500020150268203e4000b0101340c4044018001d514001e1034580d4450300480c202c4161150348440982512410440c2810032150250150b000640c0440c0300740182c0f0380c2d60000c1c0601840d140446907900e4010181c044030240c0481c8490000c2e03c00c3c0115503054034010304070b00c0148610709100000d540b080c0c4c3c050001c203008080c0c1c136080545600540829130380041c0140940d0740e410050001031f40c04064060450755003000045145135001c0c1c50091a2103035a1740d0a80c00d5030400d0030141c20fa00c07540c01040144001403008002c9a131340101151002da900c4021000c0345641d600e4401d02030b0142d000c3c1c0340d600d5420405040c1c4449017681c0044d0403600c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 154492796 1250 154491546 154491551
    0x203070c080307030f050304050118080901020d14180d0512090103180203071e03061b030c09080703081615150f0f03140705030d08090d090509130503090a080f01 71
    0x1558403001d503032440346450040c04902d04007054001140160041c5520501a00012842113542030b02d11210fa10305c200101c60014000c550060030356030410001c01c082d4003500381303030b0010394250604d42034034010040342d40da020340040c0c4100c100d62600008000513175440022074100011240380036000b0b80083c15501d000a00d40703440d041c00c036080701e102c1110441d00500900190750800868010081e6200350580e1050b20312a0000001807852003413165030250507260b020181b90454008055038450b001d48020042901c0c42401250404242c181c01c407a4404a820b60310351200c0c0f54a511800c0c1c001d0b0140040001c041e02003e09410351700545102c108440d503882840d41c40c0c0c81c031421004064012402e007401c01150900c00103142c4404001e59880c44421190510b5031400000d25041d000d08258001421060900141803000c022108090480b03050043c0b48a00f00b5020413102c0034020300700c03894810503919100030f201040c401c468140c039000d820040c1e00d545912000d0740c2c61700c1d0341105440c0d640c03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 154494046 1250 154492796 154492799
    0xa050f010e06280c08030f09011b08010302040b040905060109020304020d0206180a091e0f0b0d051e061302060a090302360709032604090f050601080411061b060103030203070c 77
    0x14856900c00c600d45505c4602242552103d01c1100401007009040500c2ea6681c1c140d0846000945105090003207034a645107032096045106110031354066951003030160b4205074034000000c4001c40e049054406643d00141c40c1d40d6180005000d52003024130181d0010000650552200703d40a04180162810350301c0040d02a40c0d80e80300c0c002c50350840c030030200c00402e200050418502940081350b00003c5480e0214840b55a68005508148603070800c6034582c0c88a03134407100c2485a810801c00034401c91300580064035000205c001c1d0542400380007482090006204100c81c3e0042e60a40051500600954015070300c5440c8414051541c0d401b803020080f5218280307040c0240c2c110050721565140e518215014515514220140c201420131011000b403800c128203000904406807004150640303010484000d8450014102c0b000941118100040c074420800411249880110300708800e0b52041d41c1c1e0400d2440a0203036808200c8080818000c00000005041d40000901500c0c0d0042d200485210b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 154495296 1250 154494046 154494127
    0x10030506070e03101503080309031312080f03040212060f0a0f0b03120901050714030a030c0c020918030405040216120801180f1103130b01050d020a050f010e06 70
    0x2c4204085194964004080700d800031905402c215401c00368480940180c94480c2c1e41e005042d00215039040311a0f00100302c4180c0c09502403035800041180b62403910b0544026141c4d24018801c14030350048403100000030800319202d421001505a0142060f10704a0500280ca481540400c1c0c442c1e280705802d00d0722503481950f0910a20700f0303070440100100076180b00513420601e40e40203041d81c20b06003d0213004082c0401c000813541740840755050050741c2d650203214405022907030407841000410400c813940c140181c035090030341c0c2d801004c1c00e500d031810480c0c1c90048078503511540e0405034100d400400e00c040f0060b08829006000c2e4414107000018413400340040b42c80c24002d1044842c00c8110031002132141740d59600800342a4020340700858421410b80890290340d00175990b40d98507503520340d03c010604c000d403003089024000442e00d01420601c82c2d00026403d5505024951081e568060184c41d036a01607000840f542d50042c011940300e0018443e00301c4041603028a00007041036665400d00da2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 154496402 1106 154495296 154495307
    0x10501030302150106050a0e0a2312011e0c05041502210a0c0809030a020406120605010b0403030512070c1e030908010e0a080703020309091003050607 66
    0x55146180003840c0640500b0400e140f8881d0b8001440300c0c030782c020104c030b040030300034a09000300c0307200200026807450540c0d1100c0b141c8094503038818060858a890348150311011940b50a5120f50708030a00c1c00d803070824100c002c410720010403c4003102c045900030140d0f504240782c0b40703040c151100c1c0d00d03400c00c02403002c0701c00140e4002d202860b00b41003004030500261a06c0710516040c612820000f510880790208018030360500400d0f0710410340c0b0300700011090981c00070f009020140c3d0340d83c11422400c82d55501034403010700340400440c81e08080030448044951695806281c00d461445c0c09141000203001041001b60344014400822000440203900c0340d08212007031010135040c60060301c50789880c0c2c012000390b41460100d2610704030108000300e81e203070400c0503250348050b1817904a095218051140780e011034010244a22295131700d40308415030f48180c1c1210301580743c800303040d40c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 154316546 154496402 := by
  have h0 := BRFrame.cov_init 154316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 154316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 154316546 ≤ n) (h2 : n < 154496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
