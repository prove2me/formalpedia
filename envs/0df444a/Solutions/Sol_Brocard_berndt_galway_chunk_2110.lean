-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:40:06.446525+00:00
-- url     : https://prove2.me/submissions/e78cccc6-615b-435f-a157-52730f4b495e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 379316546 ≤ n < 379496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 379317796 1250 379316546 379316569
    0xf1513080a0504080a1a06010513090b060c010213051903080405010e01200a031b0c0504051f0f140402040b0703080a0f0c0503010e0f01081b011211031e01051809010605 74
    0x10070020310324580c2c906402001c071b801d901500031700307080d450612040700a0302028145c1c0700f6203048a80d58460010340759150740c1190501d40b6414000d645840400540000030b0075280301e840c1c420024030102071303d43c802410090044039001819241014078110066540f000c0391111681040a00c85403003040042a041c1c000d00c01100c1001043c50030745030315014014064803108060349503258114a400a206070841e4025640152404542910342c8000d800d2400348120540e8641c0c1c07120311002c5442080c5881030401c441400780340d00b40c04404001440224440d5000b5203050340000c1080a0101e8010943d45030042c54109000840030045600300c400c9540e00203840700060000401000580b0541000a070442d9011488004c103501d001242643c0e003007a2580340132121441080802c0360303805040d01c070140940c0040c1c1030043c500180003c1c00e15030f0044030a0b01c0e102180507494411701145d100b041d03050382c0e0003400207070741c603100c1c0b004030346100c54001c0883c0c4156489100100d010b03240c4400d08074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 379319046 1250 379317796 379317803
    0x1031103251107050d050705030106031b05010512040f020d0206040b0a140c25080d0503160908070512010b040e03070210030b0f0907020c0d050f1513080a0504080a 72
    0x1d0341d4004507a01c4001c00700ca0386461008000c003a2001d80021600840c81e8001c5510031a403541c01c1d00a6842c10b44d08180903a8411030f4103501e03046000080c4424a4a10b41d0300c80c0e24052100300c01901c81006403614000c0d003806028102112001070b0004040c0c1e42d1403034070700340010424030000400380c1c0001d0a03588a60055001c0250101c0c0180100c0d81140305042403000590901c0d041030b01a0704c215603900020b0b5036120304040303216003660110444507424406440c034482940c800c0e811160707001d40280d00a9a078aa8140c08213410b8254031407040100030107456403031000d44045c0740381a0801c251b03800c0010402015560350b119149003a95184510101214002c010310b485810b54010070640e6640340c010b00c7e0505003015041071541da0741c1c645c410900d1008481600a030380301c0c0c0000320320f010314203071489801009030070300c81090001c005040e0400392010742c1203070500034a0320390b1203a90344815076811403122036141442000410308009040d0303020345490038a003496500d0031080e150400003101035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 379320296 1250 379319046 379319071
    0x1317090f040506060f2101030506100b0a020c060c03121f050306070c02040c0c051609060f050303040b0a0e0a0902040e0112021e0a081f060f03031b0201031103 70
    0x1110681040a0020303068201100d0801c403614150700030403e00d00c20519811449200000c49081c44a1100c00400115003070410180f02d560b1680f5065554820640301c90460b8019424001030080c481c0e01210541d4141b90301801c80644100d0500c10345812640c12419a40424082509500d9180c00f0903481040076085041c0c1d800041c0d81440807025054000ba40250440d0081118154000d640140d0955059900140c0b510035100304030b800300721444000b80f6501070b800f445c0350241e45811610081d46c3c0614000c004042d5a016101a8200544915a01608240400c00c100b607900030241c5046019803c18280c00480000040e14000c400c0d0003140c0455030224003404034a4140841c0c0d80500044005100ea90941c1d400065500005403d4207442101d2407190117050340f02c00c10304000612182c0121102c2040d0281840c0719441c20000c030b03120b42d610b0f02d4000a0b092a111810b5000c903074040e1909400150401e405c024034007142003059040c5900c2d200d0b40352a0132142001180b00b2001c400a0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 379321546 1250 379320296 379320307
    0x70203100b3f1c0e030d0c030e060a080a0506030c0109032306010e040302070602061308031b0d090b0f04030c03080c0f0f0403051501030312090507121218030b010306051317 76
    0x714a035100c4420000400c002c8480404c0c81141c80018080fa0300e043c00303003064400c6039030904d82240c81c4617400e1407090300900041504000325030040b0405000340403802d4144056950b91043c182d683c1070100501d80000c00300017080001c12031031010700c0c0300750328110b040b02000031001b424980f801070207911403100641c0c202c0411041c5a0705205c40b030040c08181c1301411141c200340011068454181c40050b0407a1340010101d000c20301d280d80594228040c032200540c5501e02400380070000c0019050a40c1c26041c03140005401b01c0484055070b103c8d560585501d115104a600c08071480c4000a01c0500000010060651a1103015001c0c0a028440d203041d0350342c4c1c505500d082403d01d002880c21005040500c0014400603400000080e8008124000017441e802c01d420300310b1408a1990115050161022760b4109101207954011916500c41d102c0c005815803200c0f24210210035840054080c0140c2d4005000260668101c0b503000304000f072208548100d56196861101080480c0c800c01d810700040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 379322796 1250 379321546 379321573
    0x606060e0909060708060f04020c0a03030204092d02130f0806061518060a090515090405062209030e060a0f030506010201150513021c02070203100b3f 66
    0x440d88403000b54040c0400d81898031024207105000382a240c450f0007142240107141c3c9442c2d0580380c0b1000140b04070354000419040280007540240074072041c84d41003e0410180b07103203540060000000c0f0700a807a00621070491140000c4d0442d003007c4415940c02400024486101d903032101c084c060150217014103040c00010002c2118064189031254042031003500443d4285070b1800030280010740d02c844ea2041095400c030f400310044c0e0000359004160685481d03140300c04201130b100c22001a5010001134a80c04100140c0c1c0e2210300c810000345090200003550259903400000f041842410f0403550b034a8000000341054000100c0c090004904810310b0000319414020107400c16001c0c002044070700c6509000060032901c40c000c603800b5802c0403849480103a40c0d41d04035540440103404464034036541c001c4850281d48001d006074400d100b424104118500a84241582544028404d524110140301c1d0351540744004801c2004204010380f0700d00c000c1c80d0700c0549000074030150000d00302c3d4070b4045a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 379324046 1250 379322796 379322809
    0x11040e0f101d2212110f120304020411271306080109050706030b0105040b033c0106030624020109051f050c19120204031b08100504230a0606060e 64
    0x8012441680024012004106a40351a19601115180441026602c07541c1d4074071b0901008100d442500c2100f0440b10746002060141d4083c0d403007201c0c01d001c0ca0400482c0802d85001e08040b0502c0101c03003a007032052030b00000128a4078203001505003644101e25400b100222545580b00e0041ca9445286540400009002c8000a401c1c00d0504000340084170340000c01a0056019003451088000007042c0100c2c0c83c40340e03079100c50242e00003071841d0349210600041c10624a80041400d21001307400464064040e00406058801c559006429070a12010303010340340d0101101c0308190756031081d040300803a20501c169407510390035440501079048013030350300ca00b290002800601c810300c0501011580103c04500d0003202c95181c5803900b9490152490311000b44690f82c0b005002203044100c0c08070f0040104000411100380d0000d46076280c2d00008035809545046500070a0016082c04050010200b03091a1003030009100444403a03600c1603580400300d903481c0c0c0150300400c40034828407d4624081 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 379325296 1250 379324046 379324081
    0x110303040609031701150507060905010e0706020721030c1e0303150b0306060d0e0f07150801060804170c070515030121121b080703090911040e0f101d 66
    0x40388003840e551b00d480e00134448604451b1119040010024440c006e021003504941c2000e5040402049085a4030030ba00307903a089144140350150091035000102c840c039240c04940d14085121000d04241c2d040c0e40d0480d01d040d03140710b0858407030380c0c80d0107940e09507803c10b90074941d0203129490001d050341070b00035424000d81455000070b903c10010010001203854100030340d55050301c0e0020206403540c01810441c184594504280110712448070000340428280700c0c2c002035402952a240c0c0c00d40d0700c0382c0e07044429407021a0003514202c1c428480c0004180380700c1c01460410301c808140c420041d2500c1c00a1040d84021504060600b0040014070003d8800194124640c0380f1704101500b5038210740d50481c075085400800b40c14480c51300500800d8884607403130020f90320b610501a40d668900d500e009032104031140030b410b0505142282c01a10348001100300e9043d1410805d1074026070340c0c0d0500c8100510401010314000356100c4000080514071010100d20000407130101d4210391400707801140c801c1821 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 379326546 1250 379325296 379325327
    0x30f060f03030c02091b03090c040f0e0c090a0b06040803090f030a03140706020f0703020a050609060702151f031a060904080d020a0309080a2604030203041511030304060903 76
    0x403a03004100080d004190109140d60603100410a513070f540d03001c42804000c40c110348142c40000420028640380100d10500c92840880f410400216030102c030078200c03502c031100044664405400420b0503d4101c00c0242d001c41203d202245144c3c40001007071060f003007030340401201e80c40845d145d482460018a82d4a004c002500100049440c680b40144205240070482d81100c0c0000f0f2298184416601211a55800b0b003032055521100c0d0300d4002e41c0d800ca14a4143c0d020b0140e200402c6884101203145809000c1550007003a0654101c1e050340c0444001030550a43c0c0e04059001d002c1c4001201000d600560083c0030440361684030f1403540441c0e0000802c400d204002e007108000010f070141c019508a0b81c0521001621070803075a8069000307001041000d0245000840c00c150744a900c1400290f15546000d900c07440d111001350a840c400d10280c070000e01513001031000b404000c1104681d0700e417008852900000692a034070400c1e045600684080d110f9a817141444418580c00041010760b001d203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 379327796 1250 379326546 379326569
    0x702090c0a080105060a03090203150f0f0c0a031d2b05040305072d180e0c090718030f0503030609070f09090b13050108030403020f0a0f03110d050d030f06 68
    0x1c0d90034001e0200c0414003541c0e100d8200411b07500c070414481da22850380307030354060100c40c502480e000d00d40c43c0d130302c0c41102e0f41d02c645c02d41c81c0c00040c0c2500c103406200d80145041800d00e820080e03184016800351001c01c5e07141925407421606031070800000c11400394540b0a001e03d980c15400000310000031950341429031014044104001c100140e800100041228695401c2c1006450b0100803001840411301402011003504103000c0783d004032251034024080d5025000f04400c1600b00c0f80305840c1e588060140ba80413a41000092039a4091020000c2000340c0f2020b0040c499140e80d1070301d001240000082d60258408010401c041c01c20f42e40668001c94035041c550000e54624000604035000c03400f600c40d90580301e00d280c8046482d16064840c4031380c80603006119079a142c034089981c9030014482a07205149440308101c0038108030038240250740084d201103015030b08540702c180000f441036815541140c02e03402803002185007400301c01118100c550b00410700e8030101c2909400d958141d084000d0110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 379329046 1250 379327796 379327807
    0x204150e0a0f0306050a0e0609101a06070204020a110d050712091212141813020717210f040302060106141e09040603050312010f05090103020f1906050702090c 70
    0x680e1051400b046982c402c0000c51641c4d2000d44c10000717024103c00385259440b480b002d0004402000c250128034101e016404c01071842882030400d10304410f00c50041d0001c0041250030050b091070740091204071b0460418510404e250000646088a68000ca0000520101c0d01104001030340c10000303071400f00362400c1d528650610740b00c400742c4c2400c100c00514030703a04000a500d0440c021602c1c01b0044602c89005a190780212003110f06180e40403561a220316040c84005282e418113100356441c013600320440001c9554150100c075490341c002d1001c850610382428151160f0704002030418400c46002041d002c2c6404d091034064503212042c3c001c10240407001d2100300d0307150080000d440c04164082a01d00104100c910915864424000d0094025041031808002d120000004185030140d0382501e020a0f80d031f4110003205542c1500036281c0c80281e5000400140c6005106c0300135503100203001040035030480c0c08500c4409100d91140f1701090012801c40e040d031404812085c0d202422003107203031400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 379330296 1250 379329046 379329059
    0x14150c1207020a050706030c08010e070e0907021906020903010f0c05160206090a0618150e06030a0b120715021513030c170315030a03080a0f0b040204150e0a 69
    0x14014010080c020215800020340d00c240b080210041058101d01661a09a240c000050141510340340380e102045c200c100010fa81c1c5413090140e40b0903010b9a607403043d8000100d0411140a1014007600d0841c03050503840700d00c01d2088641003124620640d401039640004106150070764294109003034032146012051000241c1000031161404540015104132541610004000b4041c0290098022125100110f04240c01030414460000c19901c000b020940d00c2c002c04081302c0c0c0c00da0344140081c800120f491642e050aa0145400c9120104041071014502d00482d900743d00740c0088140300e41c000d031010403c0705007407401d80c1005540c900c0900900c1d210001c030f0400c201d401400b2145030250a0700c5200a05104280380d1075403d90104c510152040701c90661401c0d81c00949400e0050600390301104081c0c600000c1c40c0c0ba03003651544800403030303586034442d001c001c0a4405031505a25111059505503580d548010300291420207080c0320249800c403801800e0411204c161406020346900900ca038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 379331546 1250 379330296 379330321
    0x3011217091503090a0605040b09010b030d0f030c030e0f1506180114010c0b01080105041122050a11130317073804050c13050601050919030f1415 64
    0x18000b01e0310742c40d920740b03131241440d1501042140281c00f1130f240a05100400c06202e07a02c60260030284001c0c0089101d082c10543c40b00707242929000410760081c243e07801c850103a00601c0395480c0a0800240e4500002d00003400c1591440c40418503030801920041c141800c00402c80e0040380030364240380301801e00c1880e01c00d1524107020b0359068080d9031b41f69401c9603215011218000341c0c0b0001007612540c1d284406406000155403c80340b1017000d10703801d2441c2c00c010041d50340b944007082c040340588454008000c000d0002918105155442d0140c0c5c1402c21212401066601e1214065882003481c5080441100c40d0824065007041c800304404030210701801c0310030001148014010400781d0341d10b00b0341c83d01c01c0d000075070b504a1a400035007004113105c00450b64190302d21069544441c0c1011080010f0304680003203070030a0100d102400700c01074504006028643c1b02128003a225480764030790f12000624250964212242181041c0340c0d40f241400344001c12014582340b11083d42030420340101a10b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 379332796 1250 379331546 379331569
    0x807030303020705031b060a0e0c0a0e0603250f050402070506220213020702211b0105071505060112090c1202130c0509010905120a0b0c0c030301121709 67
    0x4064000ca0540140113080c03003118a00c500145680c0192844c00d001540c5443c41200d40c85003030380c981001c0140c82d401c0400c000200da00c005290549450401c25001c80e0038901514480e014482c40d0380c2c103c0e818105041c0c421165007000700c002c4031540341400150351140d1a4000501540c014491030000400000d091a006040032030020020b02c02c90482c140304054001c0040d504c050020b0100491408907801044074a00030f070b40e1184603000360b03401000710140e00580d00b1a240d0100f09407a01495580301c140744802c0d41454554604807aa4a54404c0d0100b00b550052006d40d4500a000d4950f070006003126107104c9541080c881445640c85812001029204004110b0312203d140c030300719901e11000c000d050220f00c1c41001040007007a00100503030031443e50749000c203180d8000410385142c81c0700c2c03041c07000403000e00401c4244001c0e52101c40345003024103002101803043c8007401040b40c09201547c080d2039841e030503000e0003040e0308142241305500560085203150400082501e910788907103400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 379334046 1250 379332796 379332803
    0x2d030705091909090b0601170610030b03010f050f011e06081b12060913020a21121115070f030c0e10090821160c0b190f0801080703 58
    0x1515061014042401541401101001030042150100b0001c00361360042d20360a000b002451140d82e1810010b4031b40d80001080688480307288400120315150140c2c2409508a245c9400f00b003285d50b08011a003943c07404100d030107103144c03604104410180c50070f1000e80104460410070700c00c00c00e545440c100d907554600800e0104080c6a0024600d201e00d00780b01900c2210403507a207076031010000301201c01500156001413248035190040384551161040102a450f0018000c4805918010b8105481d10302c00f0038541d021a40c4078040400710b009010042030382c801c903448001050360384145090401c000134072107500c00340c000d4080c0208580d1001c0340d0809a980d41c2000204d00c034164078161007040440c1d0b03c842c6e020042c1d401e0f98848942c04074148044841110484d4000c0900036140c0781c3c0c0c101a801d4240b1135a40c00d01041100c007002102182c1602d001c5d8140300c000c1a1200003d02a41c0d00c1102e20303048110b4103c5031080456400b820064481806260190040d4106907080c0d40317a20744c07840040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 379335296 1250 379334046 379334057
    0x40e010c050406030c090e0a0209040e0c0a0905150301090308070e032802210318030d020d0804080702030d260f010b070501140a090b220206030711060703022d0307 72
    0x642480e0268103810b01a01f0b0800c090ba00514000380004060352058092902450070300601e8542c0e10030004000050303141c000e10141100341440e81d020001e000c02480d05641d1303192420701041a032005c2c402c2c80001c1d4000da90302c030468900f039075000c0e00c6442106086402a40314030004114169005c0880c1c00c00e070fa06a200b000281d02d10300001c0c0e42190302892042041514000040d809030380000180051300c400f0040605981244082548030001c0c1d03202c2d5005070f00844140b15900d44103c0089510510074808036040000b41d4012034644004d2010304404200c0368180c2d1200084550701031012459000d50006491902001160000300c0600c44d44002c1c4030042140c104104d0290440740d4001c5c4407610310201403811040c41030140049174000d81d1500070600100c1d80c0039001103120a0200e030061090342c0c41d02c42c1582400410341c0010726010401101000c0c05e125407105214960043d2610343e005078480702500e82082c0c540e5203889c03080e4070780b0f1764050041c200103000d4000c3c2d80e448203890a02 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 379336546 1250 379335296 379335311
    0x40b0d0f0f060e1b0423031005070c1103030a1d120105090627060403050721030b030607030b030a151503060c020114090c09040501062102040e010c05040603 69
    0xd428141d61104400d82040b0010540d0441e100c0b90034440e8104540d03900c060000b03c021200c1501c0703035010782204480d00d920b00310740d10507244004807094030000e01101c07048401e0704200c40c200d440654000002460028060040c059952401201c40a084000c5c52501c0720b143c070b02071300c00030765200c840c00032400240045a007951660402c076074410f1150000d209c580760410300c081d110001120b061200d42c443c41004120458404030312044007507003400501d141d403a282c80030365260308029000c68101444120107088180049074249204031951804030340640b03070f40101800c000c00100010304061a1040304000703950001854405c20b1303000580c065000c034003091454003901104078042c19605c7c074000004100080e95126500b100d125038020002903072000722803481c240083c1c443c100b556000d50301d120103d20b0800c442c2504244070b4000051401c0c0e9070301c0c030034014640060705101d01440c2a10008103504060107610031044411000708600c54401e07030080d041c2d014138001c1c6010541d03034112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 379337796 1250 379336546 379336571
    0x504151e0f0516080c100504020d170706021204050c01210905100618060602060103031e17070e032503120e03060f0703180503040611120c07031205040b0d 68
    0xc072042400d511406055003031890800304c546510031a0600414882c1c014841d10465603482001c0c001c50b4020702c405200c0b80f82c1c3e19a040c400098560400e54040104815800142c1620083c011044000c2c68105146858103044e401d14812001c054103211964014055210411142d400102c5140344006a092643d040280c600040c82034040080c0303150440210700c840789500300340c83e07015218a040c08183c0e1654002c988414080c031004006c161094146154022a03c0541e100752200780b4041080001802c1050160300007070b1004004529208500c080d41d0800348283e03001861011940600c0a8410a80340030065192102520751030f1407220b111003041c0300f40600b40c0c04c1e60b8010129100b07420595400f02440d201a2060400310b03240c12800780040f400003030800c09890f04076010b0f50805190100566060b40280480b4005024035110300710482441009004041d107000c00600403507040d4900310715191138014904041c4807060000300801c9218000b140c0034065503102c0425160405103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 379339046 1250 379337796 379337807
    0x1a041509021606020a0c210c03030207060e16091a0907140c030d051e0403120510050d0c030302150405030702010c0218090a02031009111507080a0504151e0f 69
    0x70001042c813400060b6942100354080c1d140300d1003500031000e614a100c200008001c0761000030740b022000c82d280c10321800209000b0f5004e812080c0c0182c074081a031007600c00e00103060005001d00e0070a070014422040c4440c10092194820409440e180590b014111600180307510070f002b0300707420401440c14580341004001000383c80780840342c6c0d0202da81340d03e03480700302402a1504440600101d03a0340c0b5021303491280c3c0ba441c02806075406803561402100154041c0010b0000105400c0c640701e1400c100081c1e42c0c41e11a0084150340c0a00d1900311140d040d0f1038000c0c2084040c010301c0d076840b00481e00f0702c408264007200300c91455509080c080400300d030500c0450a207805800084980e01d0150303042009444e0080f40b1180302074800c4090b9510f074410002e08100311001640c0140003014280c410609500f40b4201211f1200d4401c41e000c1d007400c640e6516102c441e40850840ca00041c000b2908004040c800c450358803029a040c107040584101101600c00b02d00c00d84029041000b041c4480e0320f1000d4000c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 379340296 1250 379339046 379339087
    0xe04200310080729030601050703030b03160306091506030c330f020f06190902060706090f030315030f0b0a110c0c13020c060117030c060106031a04150902 68
    0x80d8107680d80b103684d030101d0220301c8100c45418124410321000f40841100403408880c41248145c44182c1481c035a07407422401010f0441201e6003620503076208a40c0803a00d0540c100040d4481c86002c5406902c03440c090740403850301050309041500b0014184006110210540f00742c07000c0c4001c4602024956003c800610083c3c0000c0c013010b2030500350000116841030211030100d19907000c903542d001c1500322071aa681c40442e0b44980102080d0701d01c264010b102e4100d030721030b9030000b08013505000b45c40d1501c90442d03d030a181110104842c01e020130425400d4050030500d5202c2c1706410f03260178515214880011000b01000340f51a43e800300007110281154013004000c04801412a140c0700c9041c8103d07640e50406100b103104444061903440128882e000b02e444030303422500500042e074a4540c0800c0065244100820140000d010b001c03c01041000210300074881c643c4d02141c164a1030308840c0c0c0c006914440180694148a030300c0c0d461994013418041190a80341005a031070b84000c05010000141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 379341546 1250 379340296 379340309
    0x11406030901020712120c0e030601090c180e040506010e09060703020307170903030901060906150f02070315050703180507031b030f1109090f2a12010c0e04200310 72
    0x405142c4200e01d910840364400d1b14030f045000c0107000000c403070507610b90401514541e4143e1020005105000d0250800d801e000014240350703282c81050085400840034a400030034507030115008100a000003001001c0c01407000c0c242c1e210990070804002074680f41e008255500741500017010a400310312540000b00040280351850026080403500e068503640305644014556080c13503004905032201e8491502245d9030303500d1070100c0c50b40d944020394081100d40800f0f41503000314a400404204401581c0a9202c914003001031a850a40300107400c41e807401c484044011203403c000030000300002198410b4a03040759840405104600c040344031010250402465441307a90060030812602400d41d01144500300c8803103416541e0742c0c4009644007808035802415a02003031854440d80e61005d0b0329820b20f20144100c945060f0b007000410510902c1480104450703655550002d4825031028441402500c100c5050041e0040c6070750980000c0084d1804181454001001c02e13010081402c440c0f00401c10b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 379342796 1250 379341546 379341563
    0x706111b12030a120605030d080112051218180403051b120d090209060d050607110a020a060e0a2306030c0904150e010501020a08040b0304050a020a0801020702040b06030114060309010207 82
    0x111030401080d003030070003049020071390614002003440d150100d4000f540481d00e5841c10b0b103e0303180c18080288d183d81280d05a4203402021144104c80c20040020004410900090720004014205000024441c8140c1003017143d024828080000d6200080f2205461100300c52964003c100041c00c0c140f003500f024943c2602d90026105074140c56503041180002c0c0211280c40a07940c0d01c03400d000344464441c40c000d090b5000a400519074070b01035613800d4001c5a00c1800c60b0002809507000c24100c41598005102051883c401c4e4100740c0761a00c078440c041d08114802c5074900051040141902d5402e05805101301d1020000641c100d20200c1910301c0150010000d00207821a654000d00300a00d0380555082a11000008103540d400010a00c502e158480a1903107170034509112280c0c10340015000704c1e0076014020002d80940c0e9101c05aa02070b1144800046c0da80b2128410401168030035003519008000600040203001e2b05100c10450403902039a9140e03030781d520302c1d8440d0300911461100170311030341 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 379344046 1250 379342796 379342807
    0x80a020d0e0d240216020a0f05150a031b050705010c020f120a0c02040501150809011b0e01020f010f0203090714060a0e011101050c030f0603031305010e011202030a020c0706111b1203 80
    0x85c514000302142c44c000d49056a1142d150800d4485400041c0500c9410420156034860341004501c02080c48000390300e000102042c6421100160f8040e0708030303440008101040380700a03c034080c86017160000326800181507000c0c951516a8640e90300d011800380740e002c04a4608251800b42d000569903d500800410056850380340c20000f802c00d071140100041c00200006250140510507042e0070804102d144244480041040310911106207007241140a4581d00c0c000c40d90b0709008844040000603c0581c40b4600300041c2e034a01910b5500980307078402d00c06107840040d1600003c941c44103c00c1e01e480125010108016501101000904806036292a04202500059001a43c0510003400401d80f564444400705942c2c0c0c0203840030400c0681c0ca401c000c0040b98041d490300c0d890100c060625104800070421060220307041101d868410035000030f501c3d0709a840501c0000050040c03418034110043c00001d206070b031025078005981d070030341011741c200007503940382189210300c0301c0680308030396464 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 379345296 1250 379344046 379344067
    0xd09120f0e09090c0904060c030c140f09060403151d1f0f062309060108150f040e010e0a11090c0f0f1e0d0e010513020f040e0a080a020d0e0d2402 64
    0xd14507004140c0c006490f005074054818483d01500d0401c80341304038030038201401311141a00033740c00499104d6000700104400000180310ba84c10140b042c214001c00950315408002802c40b040100003e010f4a0f00440e00c16000f1750029440c0e06541440c140001540c502500e989038000d129903045003021140c0100500c1030300e0f42006400700030640035074030b10100d502d49000565861109442e201038001403104110070358100000c500c01d081000820109000c90300042080c21200c0c50407420350715070089814901402001604580007500540e80700781e041c80c00c90040c2e405801052203a1800d1a030010340303a00c0242e0440140c0350f034945220a0004030b2079551800c814258441c800868802d030400b06a0301c0c0307110042c0328007846042c01c90b00c050245405a800c01c4180e05681030f06551040c0d855604842140c01001a808028030a0150680c1c0c4c104100c0c3c003a00d0a9400c12400041029241700300f032050310b42035420a003081d401042980c0381c000c1100350030b00c902000413101c8015403010a042184 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 379346546 1250 379345296 379345301
    0xa0b0405190f0c060801120609050a02060301140127030210050409060e06040c020c030c060703120c0302030601021509150702031c050a0e0102031005090603070b0d09120f0e09090c090406 82
    0xd041c03007050307940074042c1d13244c5060311910024496200e1110580407a6004030703119400100c1914844e10955003007455507800201c190300300b130b00300170b03141c10745003079a4100e558203c9a400740d9070410000c400e9458040b014110411007041c00b0003801045181d03035a1400da4010010360340940010700040c025aa01c421010320494011210701c1d02c21410104102e03030050002c60748944030480039000e03000c9400c40b94244003030361b40700303210031001c1049940c080030310300e011841031000751821507a004d47d80303090030000249031080840c50003203001201d0040c0564030f14000f6481c482c904551015440c207946542c1c0682c19806040060900070410007482415004958040c62084045410800c65209500780c514200d0100f20780820b8070703c00620041c0194075155903034680c080002030484201f01e0710750200d50b06a800010300081c880c3c1c0c0f02c80e5500100030760480c5142540429280210300644001c10080210301c000001900580403000800c9008009108a42c04070101500050007802c1500c1d08200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 379347796 1250 379346546 379346573
    0x20f010513030f0806131a040608010c032003010501030903030b19210b0c0306040e070b09090604091203112104120e100e2b0203010c020606030a0b040519 68
    0x2c000e00e8001c41c5043c0580003503030181c040507140424400e0742600c500001c25128008031150a030250201d01307c3d80e641d004220117060a80300210b460000000043d00356850394028094045503054030f00d038803c00b814162070444400b40b0f408036000003a81801d900621080c2005038004034054901140400004034080c125034002c48442825a007000040d0001010842e00030000343d01200840e00124852000c0c60304024010000606800c0407031071b01c2c0c5800e00e9035100100c04034000c5003252280c9003140096520580a03a81840750301040c0d07075581c0641c0b040032100014180c0d1421840c00c682d81c42e40a88942d400c541360101012034519039019400d28040742c003140c0180406013452801c40c80f42c8810100c2d141d010384060710446c809402550441e00c1498802d070801c070704107041822840c001940f080303c0c41c0084a150881400781c01850f080d01d080c0390b0301c101035501070303000c0c07050a8070005a008540c9030055240411078a4901e07040342000300704511607600d51a6840d90100340005c6040908 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 379349046 1250 379347796 379347803
    0x201090b121e090a06050402120d0906021c05030408030423030405130c0905120a0602190e01091811040e07050c10061a180405010b040501030f1107080a020f010513 72
    0x30304007880c0312410381c10b024100d480d400030b80c0080082c0c0000440301d400103504148020103158401c0b00403441c8500c0d00e401c5a02803400143d1844040000d650140001c00c1090030306101101034801100f0090018800940014026403000002070140b142540800a08143d03000d00b401c007402402d00b0080d543d8000b4015284034980e8805a024400c00c584100e05d0215650345542092a10344800c1199080700744503140750034002d042503480002c81510003001d01162200685441c1411844020300344a07003d82c125061202050040c050889442c900301c0f180d440769480400c0b070036a0f41c14000d0b15401150b100000c118510400c2c081c401d50484013405070101e40c001144c1d00e0060141d039040c255805440780303201d035032041c503540fa003640f0b0b441001b00b42124005241490346a02003021070100c40099110b466502030100d418040781da89400b50850b42181c2c2c0d4010311254052100354480c0d07128245c0c000b008041c2c0003a901030300c14020b0142161000c2101c0007040b26240c03040b1328800c298403004084 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 379350296 1250 379349046 379349071
    0xc03111c030506030d08010f0504020a05190906080604050f1f0509010f03060b0603040c0605030c09030a03120c020309061b160e010503160e0f04050c0d050304030b0f04120302070201090b12 83
    0x821185d81724842c824102c2c0e030440388885000b0314150601000354043e148500c02c01004200c0300704003c01c1c0d180702a00c24192a66001615482c03c5070041140c500a440144107a003823805000e5070318003035038100d80c100004096070100310000c0d1550700e0003100d25030301140d005240c00000003001940e003421002120b0003650309202c01441c41007001058441214000c14103c00c40000348444d62180d409164800070f0f42c140e03030703203420940c0c80003d00d4207e42240890000e8088608030340035a0503406030410300d152074001941800508030002d503460240c00500d00d01c490301d06c40b2000d4001c00420581405290540c140403400e600d4840d480c0942d0783c24041d490203403050398401c0c0304000a0010303d071704032180d6640c203042e21b0721410211080e04401901c251258464100c09408603921104030340701d03480c41030000307507a624610715104201d02c0c401802c20401103124003c1001050400c01002c8500b0150329005075a0103140c401070b58a0601c5820006c0751400c00305241c0500805181100e01444030f000e001c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 379351546 1250 379350296 379350313
    0x105030601080f030f0a031e050a0b040c02120906120f090c0f0603071b05060115080108010b1c06060801020f04180515041e0c020303040c06050702010c03111c03050603 74
    0x40da030b0310000f07075003003100ea801000a0020061081e001d4030700e005803032401041e90500c450700322180301070101c0c100203000d6403601401483d07403482c403030441c0080098405118103000da00d0003035107842c181e401c0210b4904000400d1149030740d0301401c889400c540c1e5540010142000b03180d0302d8012030b003219038100390f1240ca01c0100251404202400045030000c0c03d1901d541c2c7d80d0282150410401700c0040b4140c48200c0031400050014069240646504040c0442844000307030000c01c40001a4880400c1d82d14200b08038807146c41d004954643e115441031041190b60040ca00035004018a602624540d480403c101000800d4000204105c903040d041c411460150300f0000c800701d4a0640c3c0e1200c6480705001e520740035081a81214000d103240b030402202c408440d036102810b40780d09045650058000008100c20420007001203401b030005440d107142098030039400071380201810f62018051024215030011109010010b86402d501002c90004c91480001e20281c054402907030b0703007071090154182 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 379352796 1250 379351546 379351559
    0x30a1410060f0b070f060606050a090b030411091317030610031404110a030204050114040e12182209030905030a0203100207110613080d031e1e11030105030601 70
    0x3208140c0e2000102c00790703098600a03812a45901400b8122294102404c240020a0241c0701e241d00603d101c1c0c807a142d990030107020040240074180c00c5050442c3d801d00501011034050313030280c2c884d01e0083e50b54100310744031501888241d060901c8024000480b0001400c1000034450146000b9031050b80e41185c0740f0980081076040e81e008071001c07240015686c0010380401c03a641071030340782c80c0009400f100c0b1080e1070780c01040540704240c00070710300b0b801d10000d202c0d031508051040c015007502603009083c00070100d41254a10f4800c07511134003c040c5000e40e00003034036079549402d070213481100c00e000000c000708025004040c003030300c22082e400314070348080000b118103001c07608511595009014180f030540c03001d0128000e401c0100c0c00d540c9440710b601420016155100140400125282c212401c0e03031401074031f149011a00c000c8042010f0a0810030a100c0f42510b400c3c20010f04890004540e01f10381c8170340c000e080302040009022560600740030150f081035a000840c140c030001c0c0c040e1070786031381c1392031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 379354046 1250 379352796 379352801
    0x61303170f040f0201121d0d05070803040807050106050405090a0204050906090a2d23030a080a0b0f040c030609240b0f091801050f09010f23030a1410 66
    0x40d400150440c07514005000901c454000c020400c0c8141890b0485031544000c11080324000c1d0040c1017265100046082e100904000344018000301e454500c2c07a01c0c40a595214960001420041c84100c000c239030842000300a401c41c10140c100603000308503900e0007500301a650308101c07405034000e914110114040340b0010881500c96003600b401050f4100f550b507280a000382801000c0e001040550420030a03184e10b4180c0b9914690041a0b045611710703070400039000030042014a2042c1c0d900401901100b2030f00704000c540e00502e03344000840c003501201242d100b505060f82190710924203004420381075096440403040d60a1140c2c20401e889003104440c000a004e510000000c200502003000542000c40c01841010008a100c0d07007085041c0e0f01181c00040310300c04810340380c400c0074014003a6080c25900300109a804a4103251154589012560411242e004043d091002c001c41555007907c203944280d40e0a0000d01250070001c0c0700c0c145092640e0406420381c03200e0240d42c00070206030700c0e40e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 379355296 1250 379354046 379354051
    0x21c05012102060f090307030f05030909101203120b0a290313110a1205010c111f18080c03090a05060703171b0309210f0d090804050306130317 63
    0x648503a00d0144c6140030b500c00b68000305141c40d8107208250021000401040481c0c070300c0c034411001941c413240c211040260440c0300a1520401450003802001541083ca9400d0b4a15405007804911201c0104507503016008114031a90490051000003400c0e8019280c10007008070042c400a2a060707805028000a110981c2c0510403c80e4003000c4001281d0b130349a80403206000184030708946030351146600400d044404044d141650f6640303800001e5038200004a2490030382c00d0142401071074210f81401c850b0f543d020051107203641e842c1e2213003003c8070031800e00300d000740c100046580b1404100d92050f40c13070784500801070142050a40000d85401c080042d60301d4250705456403001958080c16210340707040020109180003003201e000320981c90100b001103006003550000b4108071511020400c80800c0c031542102041101081280c4440c10401e0644101010400010031000040e0504c0480c07800740390403240d41802001d041c00100c440142ca107030342c400d00c01d407214907040c07207502102c0c1c460b621308 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 379356546 1250 379355296 379355299
    0x1030b01050c07051c02120607030501120f151118130c05070803190905060405060c0c031b0c040606050a0306060309020603041e06020d060302031005040305120406021c05012102 78
    0x980740074400b515003d038500c4056a4080034172801003c0540000e00c449252240e03400694005106100195505004280c0234049a003031004403400c007580d4048a0544d072950107080c01d0204050154000b415030440c0c3c8010480602c0350303855002c1013a1100390070310348e6003483c0e00c18400c000740d841d01340c1c4403070182c0400d802c01601c0c4d060426200740c86402a80e4401000f002007182c2c51135141c00c0c00b40280c4078841a4034000c0c40144102c0c0b4051502c81e01c0c000e0098044403402d81c05000410760040700000702c072044025052002c04180804a54501c0c0c0047c80001a6200d4200940030410540c07200191540c4400c5540900100d965144194111140782c17001942000301080020b0100e0400007405028a00d800361503100a1241e80702d42c0c003241c000c3c0c01e050144a84030b40c000c1003589403c100c50108c600030303e2742c10070060030b06640c060680d100782c0700b4601c1040b1002000071306104059068402d40b0030360000d840161a00000c0010060000740110b91aa14103503113265006201c44c1c0d44400503c0c0d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 379357796 1250 379356546 379356553
    0x70e0103080f0c010f060305060703050105101214070206041b2303031b0f010b0108190c021207051006150c020402131805010302090708041a0a02120702070501030b01050c 75
    0xc41d210500c2660068107480003601c0e0402c00100082c03024450003e422110100000e055400d52800c682403800c01740440c002c0501b0000103008a54420844a502c0702c014185a5860a00905214007070681101c120314003810703000c100900c0540205000d40703e0340c4a04040904141c005c00394000400d094020000c101065903001d807181c00c4600038a45511400504580c01c0446c0741070003030b1414001f1103403404103801034044007003098030074042c084906009007805003227880d011002013008140d52013142075040d141e218010740d01e4020300c00d103244800e5129101c0c0c0e0750034140c00c02c00d17a00c15074003042c3c07408946420000070b45180140500001185190f440c030701394488980820000e5044101c1c0c05602040000b00040d00031407080c40d012012407066400b2078030350b145004110003484018003020501940c0b02c1000001070b91101002118448031605032419140da10911000b80204c05100120300d0200707090249017500003039500201c0c3c0342603034140f20100c0a5001101e0340e00036014081d48651 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 379359046 1250 379357796 379357799
    0x60a0e010308090103050c09030a060905060709060c0b0604020712050903070e04050307030f030b120c18040206040902180d0308041104020f04091d191b0501140304020a05041b11070e01 81
    0x610a03040b161f0840c400f44003503824a00514000390520600000854a40742c1d41c4e203c1d0750400c1410300402e544000281080340c0c3c824940107003d8200c110310800140710101c202b00040131541e9642c190385895410413004610540b0800d405442030f4004805103201e07100f44030001981d00d01035013101c0d105036400b001460034803055503800d0340c010101a49640030701d519a03804045544941c1801034a0b86c2e0b000c0f004104544501c010302c203202006da21640c040c5102507041001503120030045a007201d2023100016074540700c1090000e1081441580315900a01c1010080c00785580079584034020b40c083c0700c8070300854140c00200b104a10500440300c07410070051004200128180c1d1080035100c50411038050900600228181003001d6402018094164110300800303018810303807030144043c030703903680c0c50501810080040d204044904155405010000008045440d2917000c9402000081d0081c400d042e00c1b2400c140040c200c400051000910640c2443d140703c50015141c01201c0d01e20001481e540d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 379360296 1250 379359046 379359049
    0x5180a060e040b01210c03270b090a06111b0105070801090908130914010b0c15070c0b01080c0316120305031e1017151f0e0f060a0e01030809 62
    0xe00e410410381d4140a148000d8258644420030780391155900c0c4040092841800b110140031243c0c2d0b40c1c050090040d101100c031150810380e010781e581c05904640d402c81641d481d4801103142a82f0b90000030006828050017683c1d04071600c002d0550309502040036101c04d41c004040c82e00300c4030100c505500082d400c50040003040381a610410b40280a50b41444c075010780d10200b0a02c20310b085e44030701c564550780d4402a0312111605211405415403050041ca0030507103203141e694503184070b0308264900342060040307485c03140500760b0102c189611101105e803a694400032140c80d1501c0c0c81d409402801858000800b03226150704400c16901042d000e8129400c0740c1c1c50445994200a00c00024031807590030491109060212180c460a102c50003100820b0600c4401600d0280c1c00e086500d16621142401008410420705194040f00b07440201c0e0703000b02c2400040b00c40704825400882140006e03010300c140740b46040880744c49030700c007540c95044a50351541603400c80c00382440b0103000d0410501140455 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 379361546 1250 379360296 379360301
    0x30c1e020102040b2703070e010b09060c150a060609030507030b0402031e0a1104060b031614070302011a060913020705070f18061703040308090a03060c05180a060e04 73
    0x11621240300040c03d2a440e061880c202da80030040b5182c58481004090b0841030398410303410303100386013078000c1c1c048a0716040140f1000441070284c601c2c4140041948001c0b0703192481507400092038902207a444200707405040400240c144d40c6c044035581010f8003c61030030302070021a41240c2d801170041403054919121b803107000002030300881e4180a1840c81031806001c0f0003080540c110f032900038040711409450402e1141aa5541c0580200c1c1001401c0146100110035294042e80c031050b02c050002100c4401c486901d000154490803200c0400da81003850380c1580410782c4448500709103401c10450100300003040c003034002c00542c0005404d0561242c060a900070f040181d1003a81168107441c0c8404034144210b1080d001054007614410901c03889171b84500490004000004c840000241120402c949030b00c5640405480b400340090050441d444541890004641018007080810000301006195511003014a0740105100c81005400c4c640450f04104807400d545450b091501c1c03c0b001d2101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 379362796 1250 379361546 379361597
    0x90606040b130b031608070e01090c0503070f171f0b04080601051903080f270f0f01020a050304080d09170307200a0305010209040f060305060c0c120f19030c 69
    0x2054020a44644030b64001503405c000944046400390220500b8101044082c000581c009203600e070404c802c100060750041c0483e500554140b410300440e02d50f02c0000d4454602800d0081514400c000400c04404202000c0400a24007500050040c0d42e448690208a0140340034417682600484010030807840c08034200c02200c2e8985809036001c80e41c5e40c0314664150010050000c1003040054141800208626040c02c3c0103a26150a240d8444603008500c60000080400d4015102100fa035103040c5c0c000c00c03c0840d8154050b0071a0354440d2500c506603284c611400300c90002c03800344140801d5024040c4050520480d8240040d403c0c81c2068070340d807020443e2444650300700b0201480036100c54a60803400000356004800242e03072805110140000c440e4603100444409141000900019030045041500503400e0402980c03500c0c400414241400c4103e40145200d100008041800f0078a00018015014110341c2d08403100c04800026026115803408190000d04480c0350020030644c02e141e90780c0d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 379364046 1250 379362796 379362799
    0x8031501020708120304020405011e0312200d090b030f0a05060103090602030403030c081b071202072d065d0f090218060d0c0e090606040b130b 63
    0xb40d0071507861800324180504100122000400013082105500381801f8131401001c1e81c4155074040d100400032401060301c1e0b03000041c0007445002c00700c95804e02c1039480f08400e104201102603c800c21201c221340d04c0b40c0800005000c070703034140b0001a07104031883c00e41c0c1c808c41e0340303c80075155036642d80b070301d035000380300080c8881e060640d41c1304010085451803002d5485948a07460016402d01c0c0482c000c0c7c18004000c10218801d8005000d810300d50001c40c060b038000035400031889040c406024016802c049560708107400602c00b55046c49a02001c8141320200d08503507450700804161155030844071804186060b052850740201201d0701c10603400345e840c00f28004454814854a040030350810180823071540da0388450441d00092400d05000d2203081280040c0c07100c2003020200c603074003007824a80068543c25100d40194006406516081d000c0c541d42c5a01841d54000c840e10f40d208a0407a20055503c0c0fa1140310b10400922582481d02c82e42071410381c000c00c0c9401d40c01401188401803c14031414a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 379365296 1250 379364046 379364053
    0xd0e031e1203091605060a020a03030906090605042102010c0804020f04060905090a031b050705270711010b01020106030206090402070606050d03030b100201060e0a020705030702030d030b010314040803150102 91
    0x12112010500091401464203401821402e240280c2e03480724504517030000d91290000700255044141c0000d01c071801143e0500f0046182d0216003000401040c1004018048034140303030800c010001c818401c000030411040f031580072010240c10481c01c803801660b07608e0201d03240303401090151a00381ca0030212008010400b2030416140c1a004098440c10b503a002c03215407001c0324900805800290805580d02520000200c4074650703282c03581d59000510a1340e0080740d07042002442c00d6010f95401c2e2602408503c5401c1d80d0030040001000001300500503c0075518041c6911001d62060280328212a0001c080c1820000e0b96400c20000750300c40e44048921641d0b4a400040f6034803026540403c0c40c0c01f03620006074028001040c8186103102408440071039151400c18010150090311541d004089050011388540301885d18500d54070030084042d42c9807044040007040c913607054000c019281800e907014810b010305d98888201c0c4050a980090410200740f00248007041c140a4150604c0e0f0140b044 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 379366546 1250 379365296 379365313
    0x3f03070c060f0c0e0f010c08030121050f0c12060402150a0c020901181401061b020117180d14030c1e03070c170a05071727030d0e031e 59
    0x14001203c16400b603200c0400c0711600c400000b45050408007811203c20700f0304800c41ca910390303a0580e0a10050003035520a0484444200e022b0825201d0b00180c0b5500c4012141c00c1c90790000d8503680d81e041080d081e031048461403503c0303440410104d11540160b41c040c06400030140060041302c80c80c2c210060100800283c104010056619001543e0081092141c4200b50103141c1c2e000313800703660407403680c101a984110300400030280c0c88640c440b00540e91160003c4104010710049850b80703004014062482d40601c28850608401060510301030302d000101d81407040c54003001d55242c1c86102c000d15050364203000003075544d044040100340c029030000b49825251030002c11101a50402c0e0b51100000e0000d901400c10412224204039409211206a5003000c06010b0024050b101b8440010304022400001030b24101d111015074a141420a1959140061416031064800da210a00e2846842a2810002c0580c003804a24a00c24405006000d0040500d0703c60800070580000046951049070301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 379367796 1250 379366546 379366571
    0x90b01021020180312091014041521060609050d020604050d0812070c0c061215120c09050402090f07020c1009052107091a033f03070c06 60
    0x10000000010401031103c0074000034189040500302c19160f050703030100484640e540da000301401940d4024908021500ca4001000c1018025030780101e14455001006840d6140c0040003410400d00b10704110407124400c109170802d541003480b42e8400b00c2c000900c01c0c8001d04200031b00101860029098510701555100480c605070010181501d24040108214500c0a03030500042e802940500e030284602550382c98a02e582310480c80307017905012003003148200d4460706400c8142810308495260081e180d50b00c0d107040c8203503002c4c0c200b10b0345102285804075958070346116550045401404400c0301d5901c00c3d0040d113840c28040c0c16501036100d04010080940d135922081c250004150703440e0b980f00751500c82070000740585a5840d043c031508031500d41143c0000000c480c1e049507010a004180c43d05078002c500349a85040b03070784c03070b40500511806021007116110036000360500e404441d1800c1daa2402c4c40700c0512001d8009661103142000440c1c099486135000f5280380f80a150006000c0035080b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 379369046 1250 379367796 379367861
    0x70315150302150301050a0803040e010b0304031115071412130f08071104050106030c2f031902121312030302210907140603220507140a090b010210 65
    0xc0580c030f40a000100612050500300119002040004000c1d424141000c0082024600c14003480e0300400000c03000405152003884401b00c80c03601f240c280c50b5a0071461488141851003181d4620115041510301031800d4003420440300e02081c0a0402c40b02034072800603e8402420003039007515958007094100010561030401070104c0ca12a411001c190002d0340c0c103000607900145d00a10038946420f00d98071500c1c1d0032201c8080c0c3c1c620058002c00d20b220355220450000d41711a25200e10621000c5800e544981a6224650303170001e9079021550790070f0b0500400034092056103402240c2c1410664108011512a00c1115506200741005401d210307503040092030500c5000c0804040140703903014031001c01c50602c1200081c0082c010b00c12400c1c0c410602050441c403016140200460300507083c0318407101507031007400d585c41d070003020b0f2000c040c1e90b0715940019212001500f80f15182c2104002040130003441030300146241a006800c1c88a1261545001469002e82403403100501c08451158034280e50b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 379370296 1250 379369046 379369069
    0x403150608011415090402060f120406180305370e1003060b0f09060f030403020303041e020a1e08011d060f0103020f06031b2a070315150302 62
    0x20000203280789403100700790941d00b910707201c002100124410b000c41c800c00c0e041139229604081e0707115641620f480c4003080c4c00b485440c04540b070583d008242800721713050307081030140106d01881041c00042c258030303816210413290410007004201c04108003000320b07008007580c08601080398480b0802c3e00c01484207800031051180520001980c00801103207918204100c0084060a460104409400c012145000e44990350750020b0780d000100c0e50506550f00e1108a03040f0a6803050001d07140e051078134000e59a5082503404070340e0352110303080c43e11070300341840115069a50000c020304100c0d403603c400c030601480d0055008000e034070340c0500801c454400b40284102401851001452880380461260914034040c105041c00700c0f07804010800b60752440701000380c2002c2207901595035110700203100f0019900402c034132140c42d400b04040c40b41e9441400100c40100300c072200c0065154850f1400c5072122a540802070071404440300d0030070050390320b602030446904201c0c84500d641e510b9400094520011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 379371546 1250 379370296 379370333
    0x21303080c060703050c0d1a030312010810020a0e0f122505040204120803220503091005031905130204091b0b070308070e0105071a0402010f0c1a040302030403 70
    0x4041e482100100300c40c90b48805680742c00c003c20b04000e4030007060703882041c00418050382c0f14046000352040064141c19050f10060440390382d030507400f00c1c1d00002c440034031540140c0e0040b01c8500c0750010040c02210780413840d07682c0d0580c2c409400410401c0700e0030450030880c0c00140c12a581486a07208100981c001104124140741c1e02a1307aa034210310355080c60b000640a1030040c0300c200030420aa50310b58100c2d0f980b04a00c15160380d01c1f10700740341d0500041007101c910707940b80134141c8003444004002010b0a06050b581003070318280480069990344010b8604141071149007138050782d04005580301c00d03001521146200c0345100c0e66000a003d983c400001a20308000c803494040603045440c5801000b003074100c120703500f40616518054400c440c0240303170ba01844185280c200070303a8441c0044440007544400420b0744948281031082c03c82c1402c0b90200d0100c2c0c00c1414000381e85001d184106809039000136209580e504400d0325014446024004405600c414030001c40000c00310f44554000400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 379372796 1250 379371546 379371563
    0xb0301020d14100605030109020f0c030f0d0c032f0417030c0105151f210219110a170c060906190213091e050a09020f030c0919021303 59
    0xc0ca610060764080c0c02038101008801030f04000c0014075009804d5078112042c602e80141c48403a450145440780c800c008076450203000016460041c26200700213004003c4400c50f0400102848003c290120340390800022181c0c43c1080c17001109400110801c0d40c95652003812906165035407020300c00c1d60001d90b885900581003c100c1444881007441941e92051020740c41d007c8800504011403c40e61401c0781e1b804400805c0360601845034084c1e0314044081d083d0307525503080741d032103038190710000d4020300f0440300c00c00c07c982c80c0d110015221702c40340f06141d140c4c100035160400480c1d4600482216074508146c10020611041e22a400c040c40210311814822015068514218000200c003806a000454205206111600c0f85900720a144410b0b82c1c0030380380010b807000c2c0c805107480450034020140744009061100304208901550410500c82d0320a961400320300503180c003011b03141c1103c46000d640010b006000208401c0c002c1c1d054030360341c0d07144640062030316501c41400941580315400c02c4d9884c0e034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 379374046 1250 379372796 379372811
    0x10218040f0612020d050a0b070c05010b01080103080901120f0e0109050f0a0c05040e10090606051e060f070201110a06021e0304020906061c0e060a0c0203040602030301180b0301020d 80
    0xc090180e0100103901c160100b08007403c146150f6545200b6010280c003c0e44a6142d400800904002d0300002c0394124400481c68903141c000200000b451020888995090006445107540102c107468140c95000144504005588004643c1c5100d1a1003a112550f02d0340012a483c8a1a21406502d0094280081404c1c0d81ca420140d103000f0306e0b0304001c903085e40056010808100140c000c4003d64404840100d440307160504c400e440d101030178580450261404c5042ea00b0004a94817002c211001901c1403000c03940161011901c040c000d070a440e412050410002a603020490000c1c52161302c1410080c80340000d100d04c1354035003a0075042c1107804650000711250004051801400c483c0e0200c4941e40c0355161607408a042054007074003982c0107401c04500024410b00301e50482d640540e0030001000131081c00340c0d03160307078400080d554100018948a20345040e148040300b180c06854844c3c00035440d43c3d20780981205214207280d019401541e50b2349940c24150717020300051004038084c0e0804185031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 379375296 1250 379374046 379374049
    0x405070516081e07080315040207060c0216140109140d0f051b04090f060f18290403170408250b01050616020105030a0b0307060906090b09090109020c0f010218 70
    0x1c1c0d01e000f440c5100710024080f0200250085086a50101c1c0316412401c4030291140802c0c041c0c0505d6100a00c2c0c01d0900034004c6503141c1c0003405100080942c062114a155100944c12030442c0f80d103046400620204820f04c41026113540700a500b0902034001d940740c4045498807241e81000b100300315515000026010f1414400c52030000b5404000c171030401500910b41e0703905c001c84801201c010401910b801c00c000054480e5442941444851400d41c0e03640001890300050411031100308550000b03400000304c100c062030441c200d00c0340760b25850380ca043d1551560a8480400003e100300c82c505d50402c0f8403200204500c07070552110402000040d010301d61498105c00c011016000b1a000340030031310000e0400c00c44104224200c0d40c0a0800541d80d80782c6d48132200141007003818240d05482001c0e0b00042440e404401c00003141c140b551812811911402c0c9000b16109210000790301624810043c00341c04402e50080c144c1110000271544980480c00d1403500703a030428071410401080d207000c11a0305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 379376546 1250 379375296 379375327
    0xf0c0b030a0c09050a1401021609020d18020d1b08030403080301140d051c050d090305030103030810060c290906161e030b060c19031b050c040507051608 67
    0x741ea40c109201c403d030074800468030310051846400c002141104022030264020300170b504680e9501c4c030b400840c080d114a05031010b58030020f60740b120340307140004643e81e1801841030b5014070380d1300805c4550b000c10b050700d4500c22412040640700503287c1c61800010301d49800c1005000842c40707051115101d6240c00c0ca900159400089407600400c0102800c80c0081c0d0082140c150240142250042d9001d0401e011152801000b0004540074039190048013859082405103040324401d6031a422140da034103803595103881d40740c8250340100b110009500000b5612a01800070040100407910f40e01c2c04195000c0031507034064034980c0b85a0821400d0003c0058181d84031200e1140364180000c118070301504c07000c0414030100d409800c0550350b00d0134075a907585010448a1000302c203400c0b16807810a1640048120441010840c01b0070030034402c001c5016801030440c1d000c07540150180ca00c1078440750610001e414028070041c00c00400b04050440c0540302c4900100a60140b2112600d40079981040c141c1d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 379377796 1250 379376546 379376561
    0x20105071103161502040305030705150106050705030d0c11010528060e06090603070b0307030630110103150e01050a06030615110703080a1805061c0203040f0c0b030a 73
    0x7019003080000318803100c52400c4a224655003c140c0c0000704040a900b00002c0c0a950002805404002001c00910400103854120702e4810004642d443c2d036211401e907194400c00c98002c1441d0814040c80c0103008903503000ca44541e000e0b080c0000f06552011015003125011210100c480c8070044090400d140c000d6034a00400d92000c804200d014102582817000100040405100d004038000107105610240070810007490420300403902c1381803c21001c2d024104a01841d000c1c5540203040f501090801c20700a0a4070f010811032110111a0f030b140c0082038106800402d05140c3c40c0e19078a00c0d1080452005401804950b14031250355042404120080016510200401d82065018402c451401c0c0d8404540b0394141072410761034000c520100d0600702d890b4009041c40c180840c0e0040c540d9049954100702c005e00d80032401810383c071032003004a940943c440309880210031480600e5900c40302c0d030055420034043c240d1110446400d944c0e82d22100c1d081d41055403221404018040c50304c4c0140a08807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 379379046 1250 379377796 379377827
    0x12010507020606300c030604050303010e070207052d090108010608011b020d0c1407060801060e040c02030a0c1e03030b03061005030a0201030203071806030b0a14131e050702010507 79
    0x307080c00383e0303071301c0042409800a80402c1141c144c1401403001d0328040021084956000e002d0b29118a46404c06540f20f030801d00c6403200130741c060000604001e01c049441000c0d2a0024014042e8141962100104403800a03140c0010a07184625402a545000d0500e00802100d40041603007803c11b02c03200d00356450055420402401070304010007040e004101d0320b1001e0a42e281503840806981003000462022100b0324019004440d804905203030b00c044082d040e289181c980c000c41090603810b101c12200030307662000040c0c006006107250180725007002e0005501030361700708550355a44500c0b500c0c40d46c606001107002c02e17030f10800207171135003070610205511484040484010340c2c901804251200300a4000034109540007000402e0103000c0c1d04041840a101e040d075684041c0c8401002d0002e20b0201d9055104906000d40061030044000e1200106440542000c2c030f0354501c0000b10f400707000020b0a890728514400b1042503000c07484d1003164401c140940c0042100c0c00d0500010f002c040398400010b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 379380296 1250 379379046 379379059
    0x40f1a01091805060112020409050f09030304050d0e01090b0f071403070807020d020111010c020d0207090b06040915231804050d0f18080304150309170a030b12010507020606 76
    0x100019403a2000b0103460100c0c0c64004203543da940310040b83e100c50300c0c0d017000c010b083c804180810201c00c50b50009100341c400001414a5442d166812540e9000c110340043c41d940c1700c205107214080c03140356000c0001c0300605160000c60b4a4010122031a04a80c000f144000f1002c18101c0a000389400703c042c045040d0400340d880d100751500c074a40d00b44280c941c0030340111100000d000459105000500c610203800008001c00311540300000c0d03d070201d030b02d0004018880c014021407000e80611602101c142d004190030705d481e01c0c01501c04090070a0180704c82c040b940e9444009202e2070792071140141c42c01405101d0074041d118500700100d2100c004045440c40ea05142044001140051583d10108090510040312008104200c030828220855100d1300150b01000041342d81d00040034105590b40d10102e81c0c001034412900b10211400058042e00580d802c2c03911030f5101d1580c5c4d0051002c030806141c0801c06030f50401c0400c0740c6100c0828055481c0e990b07141045940c582c1809419041034040714030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 379381546 1250 379380296 379380299
    0x3220c08240114010914190303020606120321090a1719020607080612100e030a030b040c05070f050c0d0f0b0601090e011701020d05070203030402010807090806040b060609040f1a0109 80
    0x2001c501c0c41d80208402c031405181503580d20799072110f10003e0303807e82d501c00c00c3c1c140d80c0300c1c2380003500c0d060103642040c09408183c0c2d4254a555011050711800394040041e86080d640391480b0408051014200300254052a54002c0118520b8140340309600000e4161640d24004508078400800381e0000703041c210740050b404d111940341d101004680140c801c49004090650007201d0900301000354000c1246249000f88628003041d012016040d116100c0c0c4003007160b01c07070f4103007800192004200c0800008108000700300000302c07214104862a8000c0307040340c1601c128030000c180e038610024816507110100402c948104040c196600b0790140c02071a140070510700c3d00156080d034100c103015502030804281c005ca481c0c010258145d481e0320010110a000d14206000e01944a03801039400341d0001e20b1a50011f1201ea015081c44412201a14001c1c42141e45549030244044000307803040394071240400000c02c590750781d401040018404144001a41c002c1716041900d00a581e500075410b00860a10 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 379382796 1250 379381546 379381549
    0x70f021008100b0d0e0105070f260103060c050712051b030c0c1e0603010323031606020a0c0b16022e05090c06280503220c08240114 58
    0x182c103011180a0074a89455800e50184035000d4120702c4070f4600d4541c603040030002d115501c80411100c411281d02c0341c5808060382808c6184c141840f240b45c6000c1d28510004000180c003075440b02c07090001e40c2c501242480340e50358030400d260308205041000030b040800e9010410142103041e240c10b10020004600c1c05d8075002c107440d200c24454465074440e88405040142a10f20f200c0380440c0c1d080024445543ea40c0c49207402c0d42800302114048000344c0c1e1107409004118800400c80e014900768228000101c20700d5940d5502940c4107040306401c100803100c4680008510805040c002d002140340c401c090410a20024500740480c0380d034104800202c0020050350107004001c154184904070003107510354480c000c2514084a4900300ea40265000400740307038040031011072003015040041c0507920b00340c80c0d00c0111840c0c00151808940d4640202c013801d441080c8000c0200b0703140c40741580c00c442d6940c400509080640c01401e02150051000000700600c0341089041e015140031300601060100c200c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 379384046 1250 379382796 379382821
    0x103030f0c020604090e030309070512060a020d110307020102030708450607020f0f0604031d010e040e280b0c03072c0102060601090506030a0f11070f021008 69
    0xc9440003031015000703800007507480e0704080314060112010180181d4064524040d81c0b54411504101075001c2e545010540b4604a4410408100d054004098070748920100b54001d510020036040110b64941d20441c44c616000040c510a0105800040e142d240031080580020402040b0016800e144400004a695000d080302c011030f18141800291034540007124101b040c01040e8601c15110b01010480302c9a40010280c55600301e503001c0e0743d981d1580300d02482d920002038a000340411904000c1031213106c0702842c492001803052400301c40307002420002c20100c86100040d1002c940201c1c2c61109581103008050341c4415a880401c820304840b612403402040026140303860404000001c110094030848002030034040055001e80001001141c1c0b1001c0382c003062409026000340000a00070390302514101e02181c0e001b0706003515581d1000c0741e410041a000000c02070312962152048546805400039112143c81414907464403000ca00400c0480019200241d0401c8100d07410004c480740f014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 379385296 1250 379384046 379384067
    0x106051005070302010e0a05160f0509041401090b0406050604150e0c03040f12090f09050403020703020108060303070b1e060312090f150a090e090a0308011a1606090218010303 77
    0x81c03412648075281860102d01412001003510f00d1032103503600c0070003800300c0414080c2c1c00452541c1007000143d40d44244008169040c0319855001e10311000140114100c00950004401c000d0000500c0c80081c0e42c2c2d0001c05c0205070760580d03c00751b940f400c201040c180b41c401e582c0250407020460f180e152511a6000d60400010280700c107224000c80801c1c02c02206425150307980d0340c0126183c0d6541d011400c010204020341c843d02c0e1020703860660000b480851882114040d07500b65020b08103040c1150019030704244060700558140c44200800404107805040c41c50081100d0008145214109070182c5402c00c409001e59129401c040702d00f42085103070300101d400e01a0306440101c41005843c0014603001000e02c403107110030b4000100c0d001d185510981d054243c0f4411401411a0380301c0a40c41640c0f41c5c8a6107009010445c034600500c0180391200301421400042a0000c0c9081807200c85001c2003410642c0c101c41c0603444002940c21890880360401c040402842000a65855a10028420702c5403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 379386546 1250 379385296 379385329
    0x10e0d1407081c02090901030b0708060f132a02070305010f050f040f0503040b0c0114010f230a0f1e0e1b0c010b270a090c0b03070519030914010605 65
    0x643e9030009a02c00d482d019114a46030040140101e50303034901303020668203812030307880e00090310050004405240481c5003a0310500080c2410420001e90480c1c4002008454580340365103420a403441d00241c0b0004d1301d900d107442c540c0c0c050807080e4510700e0b0a03403c0d10300304164120600d0500080002c000c1e0035200729540183c02140e82612041c107170034154203601c03454000844200700002d142540c0e24054020400d040d003840e4150034160f81c2e4690101c1c114560380944c1c0f44140b03031424192015000c0410054400500602700403000d0f1b912034461b0380036031155010545400b2000d4540065651007042c0a0003807004c01c0aa004600d803100e40b000889084030482c00c4074040210300b416048409601c40c40420101501000c110758000c401c4400200c0303020314103400c580282c00001c13010809401001162944461780480944c18015010707a150402001c040421805101e0140c000444060980344020141c9000403007088600b0040c9000d4440c1d42501000d81c103082e000c00290700c4480401c0e100845 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 379387796 1250 379386546 379386577
    0x50f010605012102120a0605092503090c05060c06012603091c020d06020301050a1d060904030c0b0c090406050d0c030618080d06080c0d050606060706020c010e0d140708 74
    0xa100941070028084c420b21740451070a420100900800315038402006d58100300e410824035900c503086203100c1c1c4548030b60010388118059541d03210300d00036049221801d1090006d5600592640c0110740a038109140e82d02480d88840010000788101e244c5014074100fa1210001c07070b80340c0d4801100e5480c030800c01c5107030080402a18044134043d01c000c244000d254001c01c1400e40500c181403050180d003082c0542445040b44030800900001d029010008603650028500ca0540d20702e800c000c030388280100142c082c02840412940004c1c2c460500c14410007000c0702e0152141320400c10301c01180c0080c0c00142c042e51121074100c020540c00c013080c8046a134400c0005c1102411081d1060500402050040204c0f0020440c1d66030038156030400d02c213036000f20b01200c486075a90710411180300b1112102030010341100020508504041009000580c000d90026250500e107000d030a08403140410f01e181186c10040b207038090150700a2007401380c090000005800c0035856111401d80340309e403511841008030b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 379389046 1250 379387796 379387847
    0x61e1005010c081204031e030204050d1202010e060406090507140d0b18030406080405060a1422020a0603140a0501061b0c092309030a081503070f12050f01060501 71
    0x1280f40c00711444908208861034007800c1a01c4c0180c5988280c081e05605064845d01520b070180c071034400d42e030440d24000c0508419070001e4076440d1141e11a08011130455417035402244000004001160256104150000701c048903410700d079003844515000902c0da41e00220a09c10b086d078442c0100b824481d0044100c50a507151030600310346000300c11454620500020900080d050b0700040138a114500032020740307040e40d0324482c4420441e0007580c0c40280002c1004081031003400141084104181c1003018091480169000500b03003819590010f000240c50b081c00f00c6001c00280304154001c030784d03a079080c01b0340d5042500141c0310010011021070b60000c90701b12030003800302d000103600040031a848100000200b80214039480300c28000c0c10307080e041a61012136101c1e24004201d81c80740645a031460140d450b050b8024102c10800d280003540b502c108180442e03d8044c035070903072004015007080909006401d04d041810b0410100183c0a1645020010070151b41c0118090600c40c020b5a080c14492 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 379390296 1250 379389046 379389053
    0x13050102070e2e0807030302060a02070816110402030a0603200112091a010f0f0b07052109040e030405031207260f04080703060b0303130e2205061e1005010c 69
    0x3c410f10300c1d000c0944005850001100d02e00840c1d0042034030f01940c20b035040c0f03517609a000c0701688120640208a024200710208045021405103818144a40584004d0701c11000018041c0e80050300c0c8207444a03502c3c0c20400c20450003540383d0034510040220010351300f901100290104103000e003044074040e00c0320001c000300020f00e9003104185044030200000c5503199a80310340c584c8281c0c0134050011400050100c0d8010056054411040e4048010902c0111940d01881d04800c1100103140065040c000c1a440ba41c41d8020300103040e0000c4015074460346407808061914548020b41080c08000f005024041540681c0003118825110802c0d0048198104044c98a201c0c0b00000c600509000c03d000c1900a4082200000c980c0510340600c0754900c0f5808050700c0f07102d52a4000540030b5010020024015084c1d40e0560001c0c400301c0354070300d92a140b4907211011508100459440e04184208a160390080c00072489100c081d0b280d1a10904e0091162146a26140940ca06204034000d00d032040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 379391546 1250 379390296 379390351
    0x3170c0409020c011b02071203030c030f02270d020f04020322031107050603010b0306040b0a0909050303100902070818030c041a09010b090303090f180c13050102070e 73
    0x8018034030341190703540c5443c1c9449009290074585001c0d4904100100c0c00704900c001138040c01d55810310f2100094084555041d0300400000c9105024140c461441c0c41d8401e4461014141d080710a030f0803651304080505840190307001a11109108000364401500940c944c404c07003409440c1e0555005940e5281d410000d0901c4401e004249d0750b0b40b01c990643c00c20941d002920a48100d00c1c50203c882050315401044800c2c0400d004000d02c0010600001e803032403400b5004941e4040c00540080c2d0003540358038010080d00e0400c101074455900010034011091b260184a00003408000021801e001060340c50340c250340f0441c5a003001d41090681d181e020b030754040c09410b40141004004100400f4000400c000e03800001c0c2e545071281085800000b0401d00d0b240c102c0b14855001000b96150a1400040064400d00204503a4014126075540c80300c00304108881405240d20f03200d9203480d41681e280c800d90071903a40c0c002604540001c45c082100080340d0121542100300420705446c2c0e4008400798251 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 379392796 1250 379391546 379391549
    0xc06050618090a0c090507080f04020a0837030e090718090e0c03210a0210111c020406094202210d0903020313090c030c03050403170c04 60
    0x81403641c1d035040c030480700000120241c0251041d08035102040d540c3c1075007003c907072007210200c010802880001b2083ca00c00b0451a0b4000e100a1111440c00d0311045031070f2900036104c10368402c685c030109d06025001004100350901140f498400ba020f0b441603a070080c21207603c81c6034540101800408030302403900850100d80b81c21200c0094510880d5030b0050f41010b043c8586400c4d560b80981c18903601c150901041d48031110080b10301c00042401a00004800d03540001c48401c21401564505031804480c0c0c01820740240c03185044a86410940f82c0c2d880e15000014070a0b0b0442d40304020401c619900150f8400803a910914000400070083c084038240140c2c040380c208460080b0070041c000003001d11038007030307040307219500322904054480491000c078038103401810700704441805944454003042e04000f442921910559041000b480c800303002040345600064001512104a4000c10758184035402c022003451030144a1400c1c0368801414590341c0240c1480c42c4140240022000e1001c94202c03030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 379394046 1250 379392796 379392829
    0x50a14090726030c100b040902030d08131406150d0b07080c0c03030405060406110a0507022e09090f1103060d0507051309060c0206041709010c0c03060f0605060a0c060506 75
    0x3e955080451130241ca80c052010f200c010546400407144c0c5601f018800e00c44055405801401840244401a19803a4005280e60b480800b035608a800045078180d140c2e503505241c10080074503080401034082d030714200780345e84c17405010380b81040c002042d0040e80301c9402c40a81c0c01c12031019203860880704000d11450405d0741d540d1100000f40010000000782e020700c6a401500308003c02c2c0f001e00c80c0303480248180e012260000313100b80200c1c8090703d0100d0801a48001090316040740d52003010102c1c0f424030b0b182642d0b401003a9070303c004009040c0b203030007155201030381a203040204d040c10fa61021168000130703089a007d25601c141070710402c10b0400045000d0400100306001c031050190442c0082c0841c0c8204542c040e00301001c248107140001aa05d020310350101e00c8212030150341040601d9038002c04481410000358814001c003180040b041031020358000d044c0454601d81c8420107201303468081e4041ca0154004201c03600310705074081d0b00c140c0900c1d40f051000c5910b031140310014070001c1401c1140c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 379395296 1250 379394046 379394053
    0xa05150c1204050303061203090609130612080c0f07030c030b0703090803130318050105030606030910090311011404030503070309080903030f0a121109060a031e050a14090726 77
    0x2c00d10000001851003160101c42c203107108803c081c1240e88a01841c1300e4a90441030620215a0a01c0c00e80c0e20111111101072000588070354840045408035600102500c9032600019110171000c414000c00c0c002c2260b51008000d070034650741e100c02809010303200140100b031004011131401c52080d04071443d06500101090384a05150f034102a8284480008901003801c0075507060550700c0060102081b544142c5615003940c0e0750000780201540010104040c038000c44d148905488518403e030072180c4d019a8400d4852500c3e281c0c13140c219190503a9400a00c3c4eaa20100000258004122a8018624034000c00c1400c050300d07041a007801030b031011581c1808082505008d00c00804060721800055948540e000480d01a031041162019424240040750400c0544402c2c01c003000240703603580c00c0b031500082040500005e100b001809410b05c22a445d10f60041c80000011802500c2c049100414402ca0324144000f003240d40308440c0c0310b888560043c6180182c4c4e10005c0e44155501641c2c0b46054 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 379396546 1250 379395296 379395301
    0x102070501050702070503070911030a1104320d020f150403060501120b0c0c0a0f03050c01050a0e0f070602100906110a21020315040b042306030105090a05150c12 71
    0x20392031752040d001c0c1e00d00070b22035040001020240c07030090340440520001164555141d8003e054041d012140440c089504100000105924510a249945052034020202c428900f0030907160750203072503a20307034070036951502005c0143c2e580c602000050101280c40302c541403242413501080780280e92003d060a03181400000d0481d200e2410196440e20a048120295490031a18101c6010342942c0d9007072075100b41c0d0040c001540c3c4d000802001802414100c0c00e02009154660944070112628581c151300c0e058106452003042000c4089020a40041d201450400c6402995441408105910581c90714001028000036a100c1d0440c5140036030915a06c1c24007010107028404040000d01542c075807a0050402d14282e40300b542c1c0107060031009850118204c40800c00070300300e21218030354803941c0c1c1c100c112800c0d4401707440084540748103600105245440020942103032030081510b4010b4100d940f241c0d00254000c5101c0c500d01240000048860f207032100490291b014041c481c458522804c000e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 379397796 1250 379396546 379396561
    0xe09040c09060e04050f1501180212010603020705070806060114031009090f0308220204020a0e06030a0603031b021c03020705030d120b121f110d05040510090c0e040302010207050105 80
    0x51040340175400b00c03804c00e41d0301c039800d56036015070350b4185010034050350050006d260724000e0044406084100941040c1500c2982e00c00340d0000e1340700d0000300c0e9001a40b042005000e1041348002d1a6400242a00c0c1c50305c4070020b40032902050703202e070100c900080002c103a040ca1074100005000c2c0f0020800c040e88580c5003100440c1c6a1403070507004901c03c480082c2c0a528070580520240c0307080d03003420300180d04c65820320020b9004081c120301802007103110000b058841c0b40103188545144240890468a5130501a00e4032003040f44503071005c40d1240e10b45000d6200d805440c0325256400390b02180c5100c0a0a040381001c4c05a04265414042c1c18004001c3c99440400e000030003184a90070440c400c040402c0003580601c4080d903000d00c0c0c04c51000da1640b4128080d5980c0c0d00c411442d800309071450843d014881581c00601010302c101c0d41c8005100602004101b001c28a11220000f0410b48142d5182d03c5003074031300340c40754800d1501410009420541b00b0b405a55600754407800074083c030300b004036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 379399046 1250 379397796 379397819
    0x110129030106080f011d030301060e0d02011116061202040b180607080301060c060c0302270d05060408190207122d0f02150f070b0408040f06020c030607030c0e09040c0906 75
    0x800c000105100071b600d840402c00c0c08400c89040762240d0f120980382e02100c0c424804912070f040c2080c0d060291f8100c1212070094140f1144051891101d107451200d4105407000d054200451505209030b0b10502003400b40c045401d04031444601002c80002c8180ca94000184151051550003000c14401000005609070044411402d40b885040288000142090100c080b0300503550110301e0707032904011a8800c0c0351240510004c0360406084a052092075072100d514100e01900c0c01c5840c83c1c400201082030112104e0422035600d0144045c201842c907041101c030a03c0c84a0b4800342000d00103104182c2d8141d02c0d145180d0150100c0855016200303000e0800b0040f88140c0602640030310f8802c50400401c2210004903a84d14102101403414954036803160503004d00014011180840b0400c00803e100c480702388094000c00c00390b801030241102003000d05040c02c0001d4254000d043c01e08092510b4aa080401c2e0305488000740c8184540fa41c6a0600b0b0405850f640e100070301540c604240459510502c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 379400296 1250 379399046 379399061
    0x40314011a09090a031206080a1110090b0a110312011503050603010c140c01230a0605150403150605040606032301050306010b030c070203061303110129030106080f01 73
    0x9a00c00c6504008000610071002d4048542502603040f024501000a000e8074040051049680b40040c0c807503103400c1501d142118440055420090001500325070703140c4102110307107205c2d00d881c040f10b5140c40d000d0300d85024094868124203000640750300b064580000c105603010000ca01d8580002ca50b501c0420840c141c81c0300868400107401c280014246080501545001540a50725624580c1c5020340b100c4081d005270b5500d0155549583c50080c00e0f52441036070540c50100031000c00e6050a00422040841c0d04036440030b80580d1241003070140c41d03902c04040e90100c036000060300c441c1c071234941e0181c0c00070034003a00550b501c5403514902040440c1d00d40e104426101950141091203200a50b203001d444400b4400e06a1682c80100144400240e01010390f402c031540d06401810b1034080d81c002410f1030b42c00c580c4e101e00c004190000409040e8400c00d40030702c0041040080100441d618200c41d80c25481403200505626042c24118680e05c0950001c00103002c01401d4850054604246070b010300700302c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 379401546 1250 379400296 379400321
    0x90a020d1110080106053001260105010b0d0c0c020a030606091401080c12030d0908030411040b090a200f0a0f091415040308130312030b180c04031401 66
    0x40d91001d01d00901503d280b9050b189151100d41c1000c1900c0c1000c07418145104c103c900c03100640308160190030300e0140442c013030420f80d4040405040ba04407843d180385042c24840b41c0c0e0307070705040c0100445c842c03820841d150483c828401007a2603626950039130b4106a04d550084d08079030445000001c0c0b210990000d403d407465800c06115115403118150300f042d90070700480d401900314a191314024a031244050324504a040292070a0150300d56241040342c9034000c003590300810000c00c00007000311021007005084400c42e41042611007030300200302c0940d001440503043d144d68032884401580c0882c12100034540343c0c0c4c01c10f503880c0d01d20300c3c80c0c0c0010b800c2101c00c0404903240c021007180b818020781c0c1041c242da11400550030f810200070200b058441c0f08509022001e0001c100102c04203003500e000700700700405400e55007642461842c000e800c1442034a601402c241c41c04039440460381d0380c951440441c10280c09402c0264807062030080d0305110300d0380014012608001c01c0c0d00318001c10342081c91590003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 379402796 1250 379401546 379401559
    0x6030a09020307090c051c0b0616020310110304020405180d0302180105040302031002030a02131e050f21120301060f120c0e090405010f020c032805030f090a020d11 72
    0x140c480c02c000546603605c10f90004140244624406115680240c0403080240072001c18038196540c040307001c6a00999020b1811010441140298201004540c0c4100004002000707a03100074540102e490001a0009101d29150b101145401e907034845d04c211600340c050195110001c0102c8054005c2d407001035086030b80c0001c146003080540c0604142c07001c8a8029000e00b944115a034840c04c000d600051805240f59400e01000201d41004840036015200078680482158100301800442c0c9941d9440503101c0c1041050310255a203644d880703103a000140940e40c00d0450300e100c00440c10004c40b41c106034804030b030220001a2041d0302c0410418190070035103900c002200760180300e4003559000041900072900702400d41c0f2150820031141c691190103000001001c5040c58511000daa100319201000fa90000c5260000c8050b0b40c1702c90602001751004201354400520b1002d4081d0000070022554404114001800000c1c20f01a692040b0340c0100400320340641d503e010624020181200d0b409042d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 379404046 1250 379402796 379402799
    0x30c09060608040f14060c040801050a1a01030903020705040e0c0a0905070206010311220e0712050d1b050307120305130c0b030903120f090d1d0609060906030a09020307 74
    0x841441050140c8806581d038241c20303582c075140d01291529081d0101e41015105031031080b404018408a4040c140d800c401235540e80c03030400030909417100640401e260030720b0041c40c00250fa030702c01c00e0300303281640c2801e02041c0d014a40c01d0a03030401500354003d98005007802211660500040b8030f800c0d403240e0441c0c0c400750042d02c450313074801150004c450207c05039108500520210707140066505002c0b6008052001305040384140391a0100090201145261220101002c0b01018003030b0202404c082490050306405544a02c1e95074a41408003c09104074503d5210b8214a50711301a070b003941d0414101c2e90307a1061440c01401c08480e8084c01c00003e841c01d408103035003000f01185418803540005142d9402e0307082011044580e03002a14110483c4030030401043d0030500b070501640b041da420040d420082c0b4203445064240a025003146c01040969100c2511101c1c146041024100302600d01c00c1d20f850640d008607684e031140c884550341c081e03404010401201d07003a40100c0085842501a100d203207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 379405296 1250 379404046 379404059
    0x504051302030d0c0c03081b010e0d020f0a230c030f06070e0418021e031911040504030203030f0c040b03040f0606080c0d0219030c0e0109060b040609060c020a030b070504030c 77
    0x504d2207a0010014422007408101040c1804050076441041003152810b190451809130b084030f040c644950f90135041412890025078040c04a1100c0711011005441c08000b80e80e1811886100500383c0d403919071508064000a4804016480c00c0c0c01014040320400e01c140720300190303a03010840f00c131f01c0002c04c1c501d20440e050074180100039a0601d0303020481c1400003150300300814a01c80c15000c0154004c45440400b496070104440c41101c6811941c112040300d1074142050b11060501c4140e019900340303070030700000a41c0041201c0e80410950fa5445468403281c001d10401e1055034044001c0603030100520040c0f0090040519031244200c01c10030103241e9801071552240c80d2141e01c0756000728501c45207805405c3c142060010740e01c10003003881d500d90320795540c0c03501a000d42c0c2184450b01443c00040c007062906208400103898001111400c00346002001450041940100b0080043d448100821521402900c801943d40000d000c00903240170f03540146290040d02c0305548400c060500041d10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 379406546 1250 379405296 379405307
    0x10b0a0302010e090a0906060b0904060504050c040e1510080f0702010905030409022206030605011b050a08090607170d060b0f03010509090f07030f0b06010e10030e070504051302030d 80
    0x890758103031651501c011a00040000c80c002c003c2500032040c6e140c007046400503180b4070841015181415413562103803588020300c030864025822480c02541742200b4403141100e404207480c21940c10041d0348645036180d100302101041c901c2d00701500403003910340100d5100c1d00060300e50720901c0b40d01060f0a250741c0e008822403d07194500005002508108810720800f4450303001040c20ba00420310340c0e0394001c405945414181c50542c0408002507954009011541c1e00c003101c403100c2d52103450b0010000b0700940780e058403440c41000c02062004002110007a41e00c2e000e065500c002d80040c070742d003001c910002c0320b80042d80c4048010131100707141090100b8106100403c0e9018042118810303400c40c3c0c01c0c0414000741c24009030040c80d0900c00c8080800014200b0068180075520440d0902c40340c1d500c80ca480c50035098050043c2b414004c0c2c3c680d03640c0b401d44803080142c0343d6250034903000c03599041c80c540007401c0c03a907550880c982003800c2c003082040e010340000703d03218028421b0701140d100c000c0200b000c880 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 379407796 1250 379406546 379406549
    0x3040201081807050a080106211109060d1401050708090a1124030405100510061e03181b0603020a05030103110102010b0a060c020907031b030e1207080c010b0a 70
    0x200308014003042c145041e80030700c100c0710310000c03044403107058589001940303404d41c6070300404407070703441d858280700e00323000506182e40440e081c0e0102101032400c6e64800300030001c1000001c1c090020440091060351351610880b41003a0001c1c024080384a52007c440d0181100b1100903000c10308210118544150014182401640002a01c88030703540d91030401020140c0c0e2039151b408c489464400c0850b001c00c00000718051848be03001041c0c9018440d01d800c0c240c62000341094030891811008002d441e4104100c440d5003030a0345c1d03901c14444002c01064009100003201d04419800c0648101e0070000360101440e181c0005500c2e00b00e1103996940d044040e8400e2480703c40000f28240010800030b541c500e040d0680d11414000860201040000304040e00c003254082400680c045000c10b0075070804102d000c1c1c202d5401d02c0c040c88514120f0900344035005110b0756560415a9660344d10558440c18081000850001e0281559500c85400e00c3d00858200c5c050441c03483d4170b403141c482010314103d40b1000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 379409046 1250 379407796 379407799
    0x211005030d0e0103050c07060617010b0402040609050f12030a020705090c0403051903030603050d1d03070317091207030503090a080a051509010b04061502210f03060109090203040606090e03030402 86
    0x2c6011260800440261201424820a1100c184803510001c2da45005040161601f02080401045900101e03401e44129101c098021841000240140c540c040801800c0c0c8609407105050590020042000340a116010a41900020035000403107540496284100c403000c07941c0141540317031194016040c0c0314034070000340f05a0003502c0d080c414031810541011031a0103410002600340d0740b034032501d007002d038a11484030000f010203500c00103412000010881d0510283c0c010041a0f04603a10400b12041200d0358078020031010605000c1c550340c14814240c42145e03002550301c0d140d0b60385406070390303500150540c03071203508904001308516100045c44854250084010211401c0c580010000c0800c003810031400c0f5500c2d20001d00c0c268503540212001071450212200b4601e036030f402c009080c01a01c0e915140450032520403418040f40d82c00a03100003034203401c02c00381c0d40d894480042e1054505e039840244800d0020007004203100caa64800002c407029407000f882460320070710010b82c40e480201e4009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 379410296 1250 379409046 379409057
    0x1021e101a1e0609010f17070f0807210b04022811061501051305041416170c0c0307120302041805060102150604060b1c0b030c0307090b0402211005030d 67
    0x504e4298410481ca13085550345040030b4010103540701c01010b0010040b1040310118031034000e605c50465111800551242071440d100030080046220605000d8150120100c1c03240c07204440000c540c0c803a811114080c002c10700c54104511407045422420461904c000b020414809000d100400042234580c0314a604604092038100d0441c019101500040c0c400202d043c0380d508040b4031901c4601c00e0382115800041892481e01d850b6404d80520156015100100325522080074441c078081c0e0310558000e00c08a000315110103003144154514000c2140141080102441c40946150560700410070780314078007096502d00600d2500c06056070300c00e030781e5207005a0000189036401030f15000d03429005a0020000b2425954604490070250400c01766014540740a106251941d2a2445010603c2000780c002e01001e20307401000907102c1c520341c421500070b640c4910500203140e880780d0444450031038007040e040c1c0021544075003030034200c1c08880420141a0840340802e00389000210000e100c1c41030782d00d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 379411546 1250 379410296 379410307
    0x3020708030703020a0513030812070f140c010f050c0403030905041a040f09020907050d05010f050a03021504180914161e030819020d080601021e101a1e06 68
    0x71030080d4003d0f017054040050610202c2e81041d800800c20340114086d0b009103441d0451014a0460f42d0006040001070004400c0042c8071190800e2110002d47d00707100300c05440e07052854290340900300c014020400c042c50002002140541c1e4005841568040c2d41e81c0300c811600c46060000704d44084000c0341002c2d07030740c916072a01480c0c50b8100d10072403440e00700c0204201d00c861380407541103081564414082a8081507a6040c1482c2d80b01d8140107003801000004540d10300000b10b04001c00d80d00020f030180c030b01012407000c285243d10854005203030481c860742064026655040062000700400c0f242a40040d4003003900c403100041021010101a41e280700c441e181c1104500d245690000e220307120580340c100000803c09000150015000041c00b1f140d0000e210807000303043c5100e24038000c090140d10400d01907603983c0000d458004148845000c4560900003081c14a822000100742d50058142030342028010141c2040c03030410307041a40c84c2411140138060340007071049030346001c0d60081c0f4140007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 379412796 1250 379411546 379411561
    0x20f0405040507271e0b03060405181f110901020c060904090c090501170303130209060a03120c0309090b03150402180108030307140712110c040c09080d0302070803 72
    0xc030a0f0400721508003821112010420324408654042c142e24800349114030800c090510180f802442c0800c0301031440c180303800c0421007074071400050640e900031552280000c0317800894a803400b4070720b40c803101210100015402e00107008074651004001320707030904800e150f5054846058401c0100160080c024030800c0c4414400c594001002055011b516904480045212800715002620602030041825810402c100142a122411030901e1b40d20030801c0145800020f50b00c44900c96045410208a490700c100140400002e6000540003003d18400b100140b90000d6081d0012442500e0f003503800b5658000020490300e150010a805030096148203030b00c040d2100810794414401010b040007940c40d00c0d00e8400321102604401e640d60710020500480740c1e00720000342d51641101600304d00e0f00302d4690310301c4a07000c11000a0414044d50810411030080180801000e030344002e0010460f0b00c0e600c841c01800c81ca001d00c64001540121410307100540e1090003241d00440c2c000d01c0d82465602d8450 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 379414046 1250 379412796 379412801
    0x100b0114250305041a0c010b010e030a03111c020f01050603071202011115010f0801050109051003021011030c0106030611071208072102030a0b0f0a060507110a060c030f03020f040504 80
    0x1048007000804c00000c500c80140000d000015080100700c95103950b04409440d0071500ca1050403418450803103600d4440c0e40c3d000444d5000240d05203040704224904c9a42c03640f800034080d4504c03011a0803108034120050340041e99501c2101301500034450340e110b0000381500c2e4000b074011801c0514440082d54059401420507004030300c00034044a07601c0400c00010a40300701c0c02c2c0c00c02c0d05a00e1a0340000c221644007402294050000d0341c0c1c0400c12802c08008080501a40f880300074002c094040c0b0100c1d105010b005805400c040f01c0c820340755954203c502e070300c0c020a00c43c042182c50700d29105045e443d420a010a5034180c1d036210a00101c8009601019034081380020280020801000028031119002c0c4252003001101d40101680fa0b09014200f45d05482c500e01c05c2500074604403c11122a54400858000719002410082d690350413030704112005490070184181c00c00c0300c907840010515846580b48007861b00960b281240640c8046c0f0850aa12545540e89400300c410f200c144070724a46503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 379415296 1250 379414046 379414117
    0x406020721090b0a0e0a08060916080c0d0302030c011a0406060302040b0d4703010905070311060405041505030609190b1e073203010306110c100b0114 66
    0x24201420300c2c3d00641c000600b034507510b80020790309130410418027122030801c01000e5414200b060000d00f019091103c1c0a651b10b43c20115148100d24052001c07003494024011070340308099440c02408a001d01646c15140301d8a10508180298a400c10000303e15101e442550165400f14901c80d280c0100c1c8030f8441c01601c03122007001c03040300340c01c1507035891200040700e54865040e01048454041d00c2c0440d100d82007a0501c41403a020340d0612410400080000c0355200a90740e10a000349178608440d40407540a008541016400618140314600c40e460f02c0f0400a040b16000c41c100d885560b074080c0521740303807a910310b1241c1d2811302403603031003000541403500d09a108800c0700301540d80180221141c5810002507611001280c20b0444200381540c02d80300b00840c0799640d10a045421801c41903c04039840b05100103031001d50b0710300c41e101d6880303407140072910714042420440b014828481c031100000c01c140341900d03010400c40196803218061000554441e400b49104080205030030901c008030f0320304030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 379416546 1250 379415296 379415317
    0x160f0f05030a200403050d030506101718010207080c07050109032001051c020309062206050c090d080a02101401060e01020c031b09181915050406020721090b 69
    0x14a803485412800f004060801540680300910300010703414400b604485c80a0111806540c01d12101700000da00302030100c0110700400c150154607681c9092140680e043e02c01e11025550001a080003840001000b80400360b0300e26060300d9225a5500065a403006203200090440c074020380002000451941c10501c1840c06050040c50300a041140f080d01400000d000d900389031380032040c44400c0c0c000300070f082d030301241904207000150040d0380d01c4030600c0f45016005101940320000650740c000c8107016141410070190009814401d2481c1c2000c07240c104414800c014401c0e03c074401c84000c0180219600b51441039034400e4280d003418011603401c0032904a09040d03125048a072262034508001c2d0101190034001d08802d82c005510400c40c9891002d015501c80e240d008091442c1e040d808280000c030103c1c11040a4441103113840c00c0c8054a4802011a20a51030030b02000240b03c90380c1c00901010703124203208600c7c11010b041c007480070300d0545605400640e91550a1000e04603203001001d41020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 379417796 1250 379416546 379416581
    0x90606020d05130b0a0309121103090f01180303031d0606061b010b12010e150603060703180c0b04140d0308062215060e0a0e070e0a030b160f0f05030a 66
    0x100c40080e090103900045e11500081d6482000750244900c400001884103401d207088900122a240c040d582c0740540b0040703c0c410444c200c41120540e016001000081d0031003801d07507000035600e06028000348a00303900d40e085101368242008d69000c000c1b60452042034014182400c0c54421031080d00c01d088440c00c07180a665880c10001590b5036800303002e54200d4032030000811407588401e4440c0c1002c459604440480e0001410300c04250740124440f0b902c04118640001c0c0c80c0d102d204140c100004d115005808040d0000c00804e0316911440104141d54a0008090005050358140300b006409003901500080703246012515500c2c200d5074000000024121804000910400701003c807211243c00000141024a00f041a550070000502d00c400b400c030f8401c603050749401d105608044005280d03000708008000c078050319984801d011000345811841c400c1d514a001e04409985a8100f070000c40070071102d0001502d6640309010203c0c1022a560301c0324210b484080d4954003910180050300c16082 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 379419046 1250 379417796 379417799
    0xf09070812030712051305070b0711100e09070c0209060105040605070b19020f090a05040b0607030f030f05010e040b090607120e03220f0e01030b070507020307050312040906090606020d0513 83
    0x612a004003409800e48800e03072031b0710344a0743c1342c4549800880d92041e0590203007448648085883c0b03565107021751805a40e0541c08250910003124045d201d00c00250380403c10100b440a07450303105440c40c0065100380e4030501c6030b840f04801554a40100d00c01d41000460421140d00000e8075000f00d45d401021844207a50b1150599020b00207980000500300400303140032620380d88070304c0c1c40003559000700015a000c000284460300462260320a034078016041c00040b141c1c4107203051095001107110403400c6020046561540c0c00000090ba06480c255030002c041d8000c00c103494408030713285004000c0760300c3d04c12808140080d40d0014002d03000504205010907c05001d80d5909514000c0c025000e1040090395541405850055804187c02c440701541003440180000b42408504d04d4020f005070034032685072960352000030b1410300250003040d014081c1070211844515000007600070768070785d1344052040a484020b00e41c102e071601c1c8038403c010717800050401c4901c0c0c010401408210420914500324a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 379420296 1250 379419046 379419077
    0x1f0209030705030d1106130309291605010f0b0a1a0f040807050310140103150216060501080c010302160f0c0b0406090512030703080c13030c030b0f090708120307 71
    0x200c455001e140805c050340c0085803244024400c09500190781c030080900041c4030b0310020940c108a02411071b01d24480c2ca9001240d41c0c0071822592003100307140250341d80d2180c0707184e0100011031008045a09600380650803510503500d00032000f0480000d0042d17503c83e49006480070301000b803054858043d070010800004181d81440040c405003101c0c07802404894940824585082d007000c22000e010341ca84101d0240050b211003c003030450342c101c8080750000288034400320003032040501d41544c6c402800700c084100b10301d58102a0403aa4100300b910241c242c0301c801981a8400e04491000413010840a1b074005a00c0e4400711101318002c11450341851745840c0c244c1c04590042c0c101c02c02080c42c1041c00c000c2d5182200003125106800000b55003400301981e005014400c018200c44e680c05408182c241c0d07a003100c44607440082d508414440c22044d40c030b06014868407815220b488070078004400140c901c00f0002040d5080b1a0380394000c28104000940d019250313000602154100101c000c44000103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 379421546 1250 379420296 379420303
    0x150f040603050307060902100f1403070302091002010f180b010e0c1309060e180c130b0a03030903020a05090702100b030a020409030e010305010f120204110705030f04030b06031f020903070503 84
    0xc500c17480d03001a998030940100800c01144009500030000c5150302d0440190380118903030705040542c250305440c0d448000c01940680600540c603500400102900c03c0c4003981500800826210700d04c0402c42c0e2400039070200204000b50700302414a1000e40d004020072060f0b01916a80281103080450401400c625401852880c945c420003103280c507003038140320440807840d170b40b9000a44016046002c0280c400740342c0e12484e4407290103201d40071614010581503503e401111003ea80206849911600c130719010781610014002179010322041000418181010300c1c200d401501c140d0028600b40da025031103600079140b1002c240790103010f4100c142b00180c8a50143c00d030100d10070b032146120f0500120004044581c142d12480300061003a03000c00902411a20219407950140d50200f0014107200405200707100300c41c0000c103144000100d05440c0f48101020740180c82c812510b8000c0c54035400c1c01c0603524091124a0341212444415000002010ba402884882c40140075079aa055035140002d04 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 379422796 1250 379421546 379421557
    0x30807140c010302070209130c0801060b0d06140a12030c021009030b060301050609061c1b060908150c09040e06180c1804020d082215020105150f0406030503 69
    0x649044403044228000d200340040000ea020038a0218241041a000149940c0d4042d019841140c1c003030703c0103011b01c504541c03050003501040c0001d108855031001b04c001c00380d00010003100d0207442c016011402d256001c1c1d0501201c070000700a98065820004040a040c00e1004206e0910640da0a5180140c4508281407003403800c0d40c48540741a403035400d164000b02c2c40106100d22991401c410402955240c4451302e03003008082d030b901402e41145c0b010312802c00340070303000c0503041148051131207910004481c112800e850040d55816100390b40c1e010070b20380e00d400d1010140d203c20400c3c0d0002e0700c2a040e27580944190032008102054074041544003a007851820b0764001c404410600007030309192801c10032800c0500d8242c4a103840d990340311188808608010700001d206244090201042c081031006840f880b801900106900303c4c038020385400030815a00c1004000036005a400c400a8010b00c078440c41080301e8452112200e001c1030410411840b00031509074404c2d641d95000c40400c0c0c04001805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 379424046 1250 379422796 379422803
    0x3030c0504031703060427110d020901031214040303020c0d020a0b0c0d0e180604021b0f030909100e1305071d06030106240c020f0909060a05071407031107030807 71
    0x2d54030708085e410300007560b21340303280d10002046064000e40b07240c55070340d60300c0c009541100921b2a4184018001060441181d20103540006500004401d007c2c504644907455034030703503d401c04011034a400c50180341c040c5110160240e0041c01c9140414204007460f055014801041c0758492500c8107000c0509801402c1c107101c0700d500c840341e00c072069508500e51680b18107045071a0844240044001a15040001c1c40b0500454020950035120300c10500c0d0813840101880a50b0340544101025981c2e0350024886280314643c03950101e9083c2e100380d4550390a5942e0401380c00c100d80c0e105002e40c07084600413242281c07103210b400ca00082c3d01c0c1c00a286920824204100f116150808400b058203442e200c0c1c0107010305110201d601da1000c1902100910604180e0070a18144282800080c1822548004064106038450204620120041f500c5849076040350010001912070010888505c4401417513401c414100300020380c00b0a0240310039076480040d0b40c08039290035071a03a8900580d60031043c1c00310b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 379425296 1250 379424046 379424093
    0x4091406040c0908030409150504020a05070b06060a090b07171306031409061f080d0806010210051605070c0f0f06021c0903021201021603050301050a1d0403030c050403 74
    0x20900d4949401184010030580c60300700d004134100664a40c03a03105511405000300e40c4c0780e113a0080034002680340da00410008004540f16480e010000d003c950002c48200e0749110340c880006d42c4d074503219041d0340b082081c0307a43e268030303c0341440603400e000e6000b5401a0b0f55400c41a5a940301c080c9444010801c900e04502150211841e0440180580d00c8031000d20304a80c1e4450304010030fa903000100c241d44640c00d0403a82a000d44a54030042404281d80c100300002c5c002c0c031205100c41794001d0720ba640500d400307900f00c82c2007000703600046040751004d9886082102d1503121201c034817403060010f0040e05000d206110601030340c0700080703507002005500c05001340400c0c0a0800006406100d2a03681c074101c0e9902c10060035440781300801c85001070100901c203601141030040000b800754151000540002e80c807040c400342604000d840c5030002d100c0e01d84103080840c6c01040100d03042189802000c4900341c05080e5840311b44c0c0c1500544038031010311040117000e10000011400d00c2c0d00b184c03044005100b00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 379426546 1250 379425296 379425301
    0x909060e060103060b0102070b03090303270604050303061806150d0e0a05060402100215010603110c0d0c0506010503010c050f0a0e150406080f04051c14220e04030518010203040914 79
    0x3a05040c4927910240d00000300340100300c0d4450b004400c4030f50003450680031241410350403030a02070b0031000000d091000c0c070a8004110070024000020b6000e514101d440c410655a00c0220781e1100008540d80c43d0800d481d1410001c50b2100d04000d042e1251103c00080390160076107100e2417410b440c9550585841d80204180015414005035580d01740e029880640800601c2991891001c00180705220805949405041ea10440142a180080c41d071000b6140b01d9500c0f400000e14142d584041503c0314095407000080c10f203414031401e1500d030500e4491906000a082c1c00c00344039007021071080c040c0006420f52003a595a50086000407014402c1001e80743c030f08007140145202d80051480686541307030000d100108800080300c140c007498054a844003414948000c880d00218140032044038603001c216400c2e40c0480004030070003010304109081c4103541e40c1c051031110395070a54015000c58002c102102e02401d5096140413218810300440c1c0c9010382c0c0e41420011500480d03031908114101006 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 379427796 1250 379426546 379426549
    0x90b0f01021914030f070b060d1227080f010c1805090c13030308160207030c030b090705130902190e0f181912020c10031a0406060203130b040305070909060e060103060b 74
    0x2001900b04406540300c00408a407582c864102d05101c10901c0180305403a10aa807440a202f48029034601c903603081c160325143e8410343c1e2036840d480c12015500d99401c0111115089125003244401301d04103040c5150024508021f00150290181071888000005c20001c1c248104809411000b14880d81d2401c1d49803802045c5c50602d0b41c4841c4003002103412100007080401c11584c4501c0a5079002940441c16071a4006045d141001550255400c001e402d46448040303000c1e03a02c06c1349460300075980030310054820b848030110805d040c000ea4100290540216582d10345a820080d4849031983d0070f805c03410039140f140c914000c0700e09034000107140700d00d029100b0840c0214640d50761308224001043c4914811002414180858500508140d0340d0b8503001c1d031102d040c1c0b404402070000904104000e80d11110000d4482c0e0010325200e9916a40c120001640030f03802c0b040f2000ca94000020703040403030900071600064045084241d40082e240c1440998422003070000c0750003140700d1203001803600d02210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 379429046 1250 379427796 379427813
    0x4080607020622020a091107050a080405010f050306061602030f011107061a0d320a05070812070609020a0b1b01050106050c250b040906090b0f01021914030f07 70
    0x154083c02c010034440038280141c903841580410b8980304800070540d00000f880302c0301030380a104801381c40c07403080014581c240650320000b04262113083e6101d9504d220030b44001d0300c030751005440040d084001000b030317404c1c074049281c3d0603800f10b4802002e80741068514a101401c0d00e5408074219403c0000181580400009200c0d07200454142108038815040040000740c0d1201140c1c03015000144002d02c1401c1010590451003030000c050180768500403680412a03924007420781c0c212118454036001146507a00010706900c004e0006008c3c501d00381c0d8943d1800085c25400004903000700c0200306c00303c0d01008003805000fa00268a00755156070114560190948006a10030000d00c1001c001a00340070802040c40781043d0703508400c0c403400c07a19000e0103d01242ea10382c00701408550214021800500c41e800a50880e000401c0c144401220903041114040481e4045805a40058101d42c40c070040c6030414500706008041c01c200041c1d14401c5036003590302c0191547c25004000440200b0005403d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 379430296 1250 379429046 379429081
    0x9211b091a090c03130c180213080a050303071211030c0c01140105011b021503040b070207050114041710020c03070204050a0501081f15030f11010809030301060e010302040806070206 80
    0xc0302c0c900d10074145003034440c02c10720000d044100a041e41d1030f421410b00131002401c400402d03044440402d4824a0301500f402034212031601c00310351114101c000344201c00050a510b01c0c0341c001c0050351460300d54520130f84170072034202e83c0d480803107031201c04510340c03544418055031103680d0a050700e0359a0750007050800c0c00c4490302001200e41c4558480140031701d0342d10002801043c240e0801031420080e250002440200010610828081000041000300090500c2840c0034905a40032288460788410040d20300d044946202800c900c801d0204020ba4609800c40c801300c859400c06803002501d401070381c9000d07640201ca02010f41d9100003110000c41c1000e04c00d1a510011241c41000103505000300c080e01d8020b081a41e40390f8841a07a446010003119501440300002d0f01c054044c810b83d603a1602226003c00d084068943d0903041c40385164650107844814401c0385280040d51440c0c0c2080030a55481c178103039890707504040d824800880c46d507a04100b054001d00087e001800a0719001d00b0110594000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 379431546 1250 379430296 379430299
    0x1107030215280b150c060114011403070e030f160b070c050d1a04060902130b130e03120103060219050f18041107120e0109211b091a 58
    0x24401008034560004280800003115038921014458650395440080d224103080d0131360200514a10303082c8080d1000007800c1c02a0084180d9000da03a0303600c02e50243c04d0b08524414081040d9000c0200d403004050000e5602c103105041140101203d00003192501480c4466420180d2058030b02004800860902c04000c1154004171460f244050791148040101407080da4095841d411048007000b0829000b0703801180041c40c14400ba19080c142100501044001a0b0003001c0ea07010140054800e4055040e100c0d1001d841d111000c58404500340c018401a482003c0c607002c2440b10040302c203034100d00c16001314040c900158aa00500503480108030310001d610040c004100f12202600b00103c0544e80000003180b0300c036810350580d00c00f1030b01401c54000c0b40e81c00d45800044540421251000942040340a60386401d00c8903a803000650b000715050080c00c0b2028200941c0042441c004d4a10303485407441400f184d03042e452862603030852440503402031840342d9111922100d1140b000c59410564000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 379432796 1250 379431546 379431583
    0xa02010315080c10090b0c030d15050d0b060406080307050c1206060a14030a02060c010e0111040503280503030708040b060d1a0907150315050603010b0f07051011070302 74
    0x10b04050160348550007411a80070f4104040781d81d10f040d0140010780020146446056a200b000f4400941c895102d002c20603041172500600c020107041402d900d0701a00c2014080c03040302c40f1030f51151032a10600400e03040d0301940b0b401c004a000c00702400580110b91043c4002d01c403580c428810400d808801e44c100d0341013684103030104a1140d07105041c600031115004c8410311540407170f40202c0e0500c0585280a50848400a07410102610540c00038030031302c2d07004c0d0007000f8001c0e203040700040c1da02c1180308855240d405040040340800c41c0c2000c10f283d40e801c001d507040c00c903100f5560b03240c00c0d80c2003200c0d624045aa000c0811041c0b100e04031005074044800c880f0504005465500e02950000324045080340103003d900040030400c00300700a801804800c00301d81f9034050491001030140c45801c1c0001c2c481c0d441100005101e0a05100703580c180da050105550406020188032400350300401001d44082c81402d5081551404502c602c01d0302e03032460900f281c0d0750031203414042d103084041640d40e01c0884 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 379434046 1250 379432796 379432799
    0x61211130503190503071202010b1801030b0a0515040c0e040608010b0306090d0504060e0112091104181a0c040b040906060e03030304110111010906020c0f0c01020a11060d06170a02010315 82
    0x1364080111803140754000309618080d0f0801004900428990901d0368022102900040014110380c011604881c0306001d0b010aa590b916003103402d82d10191020760782000e000284244501d4103400c02e004000c0d40d07150030a00da0305104002400d550440d805500f11b40d6481070b81c803c0900301401410b5200c180c480003456403083c1d054004081d8419803040c20304119440300d80d1106030380308502245004020000a10100e681030400b021a016580e882030b109901d060001c440e01d0f0070b0192503030907aa801c02c41c0791410800c554000342d0081e10050582c0b40c1804200000301d101c04c8051b0140019181c480c0c000100300e070515001810304103010503901e210f607100344104800070700c0310503070015a000207280c00e003214034000022501405028400408003400450348045040380001d407042c5032030480b0200c5072000018401a6113550422502a00d074008815041c40e0500700035004080c2255075190020b201980c0d603146000443c50000e0b00300207600100f034080306544e80340c0603070410925412242c00085 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 379435296 1250 379434046 379434053
    0x6030c030b0c0a0c11040612140d0e22021603030506040f090b060f0105190c1a04050d08090309120a0b090601050a05091512060708071806121113050319 67
    0x10b4543c0c04c0003d0113451503050350159600c454000400408110300600169851498506003610310640f504a80e40b20309031600421138410604d50004810103003500000c0b01155004014100c1076400400340b1070b0b02000034070741740c2c01c22510401507280030750f800041d40c1c24134408000645d8108a20400014107000c1c8140200300490007454005c101140c40700720060002c001a101e03030140384100b2034a907030f44640300105160000c40551134107228407403e03050702d1203a0f417001510510986001d040c6074400000394416901490702c0c0c2340c115035040112400d20340d2050009402907a800200302e0150490880c0b01e04200350440300d160007940050151400d50b0624000c1000301c0e04903c85c282c031034103181d00826000d412a6509818082d4050910400700800d402150341c0c6110985200307000a612600107050305120f2009030074507840c03205154000910746503040300c1c002551020051402d035504100d40384040214014195000c0c150200780c5101c3c5807400301400d110079440c400c60b807842c1c481ca000001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 379436546 1250 379435296 379435307
    0xd0806151309020f07030305011502030301051002070510051801021f0b040605060a09080f01060f0620060a0e070512030307050c0f0307060912020d0c12030f06030c030b0c0a 76
    0x5140c03292058644544140101424100380e0760b000c807100303510001e20900c403041013400402e1158020b4a081c8141e90741c41e0003e00712000d40c01408001a001031005100c00e107007450300268070102500c105c0300116110710006404040302d041c580049400003500c140d9407029054100300ca4802400035100b800a801c10710340300500e940880300405d56680e00c0002c43c60381c86a020304050130000c0e10041e2581e12081e00078051300c005001d500903034410902d0010400c0c40501500301580c210780040c0044a28001054454000c4820602202500682240032104081016074401e101085010070040e40f5400707602e09115003034100c10301400c20011904900030f0000308032508a031040c54070982d1004207099050400c0c14039075440245020001c1c10600388082174002d180e4080c0100c1091641e006084800d90307540d1000006100840c44203a22031010400281e24801102c1c014203001c100303105124208011030741160130848103130003484014814004203a1407260301c10b202d543c620f8544503000c90040c05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 379437796 1250 379436546 379436569
    0x4060c020f1c03091a010608011e0311011e170112030e060307020a050d09180203010e1503070f0612060b04081908041a0705010b03010501140108090a0206030403050703020d0806 78
    0x400d00211100b0780e602c54820b0740b000c072949401c039050102c00c0d603901418600c808801c1c400c80d8001410600045001400018002c000c040e81d040c150328800e2466990f60700d85ca02024805060001c480e201c0c1442940208071a0b0301c510701640d442c4d1203000ca90804221885040c0c202040f000481c0a40b1400a901700d2103c200c1290101d0380b02e510b070343e51200d040f0302d407002c402402000c90048024071507481e90010754610982e030b5000700e0b0050f000401e1900ca000c0703001c00d100d06141d4086c842c011400316400a804507004140c0070313040d515102c0e240c0d480c0783d03030528080d0b01540c00501c00204400f001240c900c6007101403e5408055482c0614014816035142040c03207902c45401108840201002444422907004184a80d22000c5080910121142a810419066481d5424840520811300c0c0c1031049a040e1102040e00a80303100c00c80d801140c40c00e0006100d0030182c401d01c400100547e41d442c0185214074030a50300c580c0d851010b858008e0070310021030b0400c02071000200501c4030940c2d4102c00080d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 379439046 1250 379437796 379437823
    0xd030e0705011d101218020a0608041403130e0903090d031b060c121401270b03120910020706050a052208010f1404110f210604060c020f 60
    0x44000f07141d0040c840700c1c0c821075600300e07901c401000d404006194110442c0a03074440788001c20880c2c0c00e50700c8801d207080600118020341c000d4021500f4002a80110a0300360000d004d07000c0c0c0c218421807081d0359840c580c800d92515070000c0e0582e40402000c40c01400203a40032150750003841c14a10428080303554500d07001001401e000c01200d0b96a40b110f00c00c1c40c008030f283e80054040c410003810b20f0001e0510b07900c070044c18404a040c2011000701f0351042d0002412110408140300c0b119800100e171075070034540684c0c2e07081110f4841682c401640c3c1c5c2005081d0103101171102c116595150b4000f000700b0903e0800815043d90012002000a190804151800c0079070b030b42400382e0f80f086451408400421040c801103c1400b0010000c58410700540c0204410042c0b15001c00c9440080c5a20106501e01120000c200d05c20300e4600b0803007030401c1c0084c0440d0300d00240c080114000450420105041c02c0031110725944c0c4103004100074401075000b9040c28110b1350010b064054a86003510343ca03410302e2070f4420b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 379440296 1250 379439046 379439057
    0x40f06091a0a02030d02130e0705190e0303130f0608060a0308040308070c030209090d08011d0a0c051c2304050303130c181401080c0a0e070c020a090903020d030e070501 74
    0x88400380280704458148400845c2150b845100074140210b5000301e000d0703000f0795422080000d04450160044030040001c21280340111011000201d4010202c0701a40307030140801c0c86185510a0500140340151854040b29070540d820301100800c9900d0081c121032003078407100400c001003100d10301100c0a072500100690341e01c92140c10001030429141d40300030f40000503c01001030114010070940c03a0010079031f81e203030500d9a850003e03103885c03039074910030490000c085408240e00c2c28042e44840002141d600380b06080c0005101600f18445160400d600d02c0b035210b01c4000b8204c1806502c6591a410b081c606141038206600e03110b80c4e90000800e05071a0143d170075240340501002440840060580070301008540705048041009000c544050810f2403d5070b400104031078401180c2072043c01c078081d285240c1c041c603041c0c804482c1a0302810341014045011001000b50300d486455030040c0c00282404540000c503864000c1c0f6003c001c10840c4105407426502c04540d10010907100220703102480c01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 379441546 1250 379440296 379440307
    0x2120c31030807150f0c0212031312020d020c010c08030f061f021b090103050d120b060d020415020d081503011b0e0a0e04081e0706060b040f06091a 65
    0x8540403240c55007020344070b0b580120700e0008000c80a5860815250119000e03c03511103650440d0341581c4c2c40d0301e00000560403040b40c1e22200d11030500039550040204110a19084050721524165201280d0160050304900264159a40c04014403004000b0a190016003080140c88003005400302520707885410f120000401e1031076480103d101c0c1c40340c00703844601c049140d0300d100181d03680c4043c0c41d5070844000c190392030b0111031078102100340c1242c1d00480500100b6049030400c483c1d0f440700a441081c1d0680c0c0e0790600340795486410151100c1031402c840140c0e00c07030404c686070340e18500401e00002103501c40d5080b8041c1d250310014076a000070308030103c00e08501c039550000b8090621007000b2017514018410503400c8a900c8074508155000c1514980d840c651a003504036603810045a014280c080d0820150301060400c419021104c216001035908109050380e516003a52030301d510510f460300005c81c05001c502400041800140480d04101a0551030211500d07443c0f4000d004481550501181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 379442796 1250 379441546 379441627
    0x160f1424012102030610170102131e0918060501090c09180b091e06061204031d06070c031e021f03020417070e0609040503030402300102120c 62
    0x495031100ba4014103681d0301d41b03480c1c0c1c034540c1039245510403c111540c864120040c841341c10b20882e0046d141010103501040d0408030300d2201508200603840b801c1400e2440080d01c14403501c0b034a903240440c00180340f0320f1b29040c18004207645068200c40000c1d46840e000310901030f080f14003030341240c010700b405040300d4490103c00030007001d603284055005070f40c40e001c01982c2d188200ea00003005860f4030a202c4030761190414042103000e51254410800c81381e20100e00801c0c010a04d0b042d8401c403040004800000f02ca020400c039400401c8200c5001640c450140100f0803500140010145071001e4500314407040c0d00001d104078040c90340f01031260b504508042c032841c4290116000b07401e0022221011802c400c950580e1142c95209030350b18000c0240104402e464000030907801150000c3c0114111f46560b02003000803041f03411b490b041c081e1a00c800c8a0b18103001445010284021400141c50750100181440655401060905005070811002a203102e21000240c1c02111040b8543c00e142103986 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 379444046 1250 379442796 379442849
    0x2090403090b0d150e010302030706030216020409030203030403031a030a0201030f0204080604080d0c020c060d1d0f0102071703060d12050d0f0207050c121002160f142401 75
    0x108003080b02c000024034107440c0c900c5904403600a8540385200c0c0f245076a0344810030391000082c00004d40c980c11800d0100201442a00584142c03807443c038995000c0d51030b90b400101129803c040c1240540c202000300828140c02d44111030700c0070140b2200e0190f85c2400700020346c550200000c000e041c5a92031b140d000000a0550540b4040d02202003191800d08207800d10840a82020080988460801010b06181c1b40302196268040e40041c103280e04110710460382c00041e10064620401c2c0040d401441c1d01040b0042002d2440d11b004000016540e03841b03030800c1220300410851140342c0420800600010780c441102d20202d06821495090312654484001c9485100e403040c4101002d0400c130b002950151075500508005100d403045400c4102840d080c0700d401031004240d00d150350030540b0520080c000a030024858440e0644190815100c5075817445104880c1c2c0c181a601c591003404003040b2075504100c50010401a615807030303415211800b0480b04035205005000e13002e1340040130745900d5071644 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 379445296 1250 379444046 379444049
    0x40b03010e1011120403020f061807030f050a060603061a060918100f0803030711011b0503060307170c090f0c030115050c01020318010c0c05030f090a08150a050705090d0209040309 79
    0x702d0004e44504050a000b5035031400680c54000320301800020840d80b1001d502e03601b89450280c0084c10041f0f02d55120402d20076101002980d20303010b603404545c0041e14601ca44000f540c403407400007031042030b01c21412480807a45c102890181104119081c0199142d40b02c00d13611200305000d44500d560340102d040210b440a0344640900c1c00e40c00004200f1b1000070001d103200300c456a5901142c0c40e011700d40769090301d00c1d03148044503007814045401d03400ba04c01c8009503400400607045480d103664403201c0a61510704000c4200c80d80c0c204c000350143d1071030042c1d00a074000b142c2e268020340d8ac6c09c001c14125441d00c01032041c0e116150f40248000745041c01082540c0407004204021902c80c40d081d090007140d0181510a08055442c048103145003a01901034008016045001035080070110300315100a6070104082641c804444803000640b1002005960086600110110400c0c04c051002c0c4054480141103030303041c040244020049619504041005160115080807250305c890070107440401c4079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 379446546 1250 379445296 379445317
    0x4060f0308071b031101020d03060509160315030515070302030601050d022b020309150c040e060f0a0f14180403080a110a09050307050301061511070906060e040b03010e1011 76
    0x101c3c004280a803d0300c1c01c001c500000e80a507170080d01c0017181102118010300400358444240c0c0085072041541d40302c0e2160181c0281400241004042405039280607154000c8a4130b40c4400c1c1c614000400294900c6d41061050034254190f007006070001c0e0403400f810480b401c10741e0b8003055219602002d00180348003010720406001b144c1c041e00c8419000f9610032215000544102d0227520311a80000c94010700c10380ca13540182c0e04007802e1080e003e0010a014040660044003100302400c1d43c0e0341c42c01180700500300d020522404910b020305200100c00f581d0380c078034414002c41900340140c80464507083c0c2d020742d140c44d104241e5600d00049000500ca030a001e00c00c0300402082c4520142d4200c0c03201801d5072030031421500f4640e5a0300c01c0500f41d0300180546040a9503480c5032038042c6004d09281c00840100c01c060719030301038607010b2810440d07000e035001400284a19180329028140380c802c0301c22543c81980280228a07240314407640c2c0d0010343c1401c00d6200d40c0e6690303400c0000b03c401c0607103036900e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 379447796 1250 379446546 379446593
    0x11a0321160318170105060f0f131104060c0c14011719050405160b07020d061d01090b070f0c031d0d060e0102180a120b1801050f0403020c04060f030807 67
    0x46400103100d0760b6107410b81561300d5601e8400814885e04d03021b60501070b4400010648001100d102c018800700344186910100400d03143d0804c206070181d42000740c805412540d40304007440d05142000d40290303050384e12030070b09103000c0f01e0030280c540d91203130082c1c55040300038000101a407a06620054000f07001d0090300200344c81c146c14003040140c0801c1d41d000c540c515146210b07049483d00b0a418440c03040c40300c000d50082064591000041c0d45805c854880071603818800842c5003000c6041e400c1d10400c43e0200c555000d0b080402c110a03800402e02151880c00707150a6512100d42d540c080c0524211694000d80302d0f0203400b0009840d6103410b8000f10003980114140907140c0c0d6100d00c18041e41100c40d42c8030f4002d40d210781000d142e06000d41d04070111407203070800d038017502c20390b46841092080151007107810251800341481504424081c0e1801403102008000e80c030702c0c090500a00300503500321280d00c00d90620b801007203006441d907100b80549400c0600300d1340e159103502d420241c0000b41ca00b070007100e51 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 379449046 1250 379447796 379447799
    0xe040f2102010c0f09120b040c05130e0d05040510080a1b0305040203010b010e130b0319030e01080f07090504020d0f110d06050901030b0c0c0f011a0321160318 70
    0x1c0c1c0c103401a0f840c00d4074584440c00300703904c2000203a80a00880c018002c03a0400d555100d00441c400c07803612900180a1440148940e403104003203040324201d140310011590300e41c1d120f8032954204200010725a626480c080b428941010300040ea803c40c0803445104001301c0d000401c3c92021243d100100460310f402c4071604607400c3c0d40002d0043d0100312026407203540f1b40b004980482d406180e660000c83c800522401100d0030b4800d60200a041d00003045405100d480d5070605903500c4090b0418081e8001c0d115801b005c41d00e40001811411f004154201c1c5103591303000e00c004140c1041c58041944e02c100c50140c6c83d01c0c04c002d0424014014002480041410031498020b00c100750700040000c9103130200244002c0d41c40e0420b00a10f0303102031000600d500604000203044ca01c078500076058600e03100b41602c00c40840d140c40790b403c1d110050b23045040111086280d001c42e18042059220003180000841c400c0e40351035030031142e213000d02c2c4480040400380c0c0391a6010540714004c044d200c03c3c0000140751b0445d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 379450296 1250 379449046 379449113
    0x14032d0c120a0c08010204210501140a020d2003010918050312070206090a08090103020d1404030e030f0115121703011217090f1c0b13060b0a0e040f 65
    0x1d003510b00d81034400e0340c2e031542c010420042c180206c60036100b1190880301c0c240e60346140f03400d141c003443c0c0c0c059801355602c1072006080608114410b00031075004c0e1000d0f8460031403c1040f0211000c01c0700b82684149400d200b086000940b10039a81120308416001401800d402400e005401d510030740144140030000305a0354110010119501821055003185c2032581c4040302c199403580901405080840c003481000308035842a00245481e403d461400f1030003242d20001c00803c0402520304601140c0d06100040f0241010000c1503590081c0c0341c020b2102050f00030544105000c02e0282000103100c4499120501c40a0743e035007110280903520b0f195996030b4a02f0345910294500d031084843c0c942460054080c00035042c2603402d02c581c001c00c00d0645480703c4080103e11603e008015441c5e81800c490a00480c1c8000e001c0b901c50055984510841e41e400e24010b4201e40c0070403035040c07207400c040b030052081036620100542d005520807221090018035060014003d0b010f89106000c0664580d85074225 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 379451546 1250 379450296 379450303
    0xb0402270a05090a14071103040b030601120c170c070b0109020d021201080c030d031a0d111008041509080d0207060902150a110304050f0105090a05041514032d0c12 72
    0x6800d50490b9174400d07200c13601d080701c0821190110f15101e6205000900c01071002000440d04000141049075590326204426401d03102000ea1010202e10040500f00107024035008680c0d000101c24492403030032245a031031408015060103083d04080d030115400b10500c102d0360440d14100c40405101d10650b940d00c3c2210365901081e440c8a02034051251000a110700900031030300c404083c21140c682c00d07030342801407050b060000c40c01942c0700c88242016201c0d031b4456001458402c08184e880c85107d20301802c0c40c2c4511829640346001c01031404030950080ba482e0350907101034500000b030169850503682004230240943c1e0300c0107507020b80c0d0703402c003c11056240340040450303e0703150f210080480c4e408e0802c0c503100e0140307104083d0007040a50910f505503101d0802003514030801004041c005494801007011a100703005280c0040045c0304d0240415250060074482220084008041e201d840007000007000710080e0064120b03d0b00780801c01c088a40510010720302d20800360070901640000d04031702d550f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 379452796 1250 379451546 379451561
    0x2030103050313080616111f0c090b040f031b08070b040603050604090c0b1c0608062410030b0301091208061002161a040801020d0f0b0402270a05090a 66
    0x12801c3c148600001c10000c0811180e1042d9604080078148203c06c00f4203540120000031440f019015180e0086000300d4481420b042c01d459105c0c000030010540f41024103401102e07000602e103a1414001009003d095000500640c0e42c0302d001c50a000024803000298400c4c1d94000c000b107802a10b00100314410000080c00488000d95818010b030385940d41800b089480d481005010780c00c054000303000b001d00203001019a56188200303092404001211300c02202c141e84c100a980e50040018807204030900c0d001c4480501d00c480300c414005081300c0c00a04610f00d01170700c180906803107400c061081c2d40c2c298002c90b450f64001203002507596020301e004003c8030040354104e1040d4500b000d2038120b01e00c000381e4070305051440ba03048801542040c45034449101141700c20340780e6540070800814035a000b800a8410301c1c0c19040041516054018072034265011407c996010703d2040c040000114a4100311030225400b4004201c54039040304049a944911a01b206820080e00e00500c035070380d80154401d90 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 379454046 1250 379452796 379452817
    0x1b07120c0606090902100e030c1207030b0105010234032001180605180a031a040c170d140d0603110306060105030405120306010315090c020d0527060d020301030503 72
    0xc0e54854241008641c04036501a4010100414001c82503007e02c400ca400d400f0018101c403040d4441a00056500c00c0a24003a10741d600540c504100304440c0c00e0713545d03000d0a003d001400c5030880d41104903d039a007590b42c0c1413509009602c0f8806800c0d40c1d840c00c1c10044d61308111500300780302210044100111407102c1040c00118401002c3c0c215a121210744000d0390010f0382e425140015581c02040340c1c103800c0c9040d5600c05c400440c00800604190383d8408440c0c2c0d0607107548101d2078a4102500480c0650f40081c03c802c031150b19110b00750401041e10303552503a95080c0303507032b0041854500c1c000740d000c0c0904c4d100343c00f0324005010042c0308903c81d0f164000300048040b10345681d41c444c0111082d0000b42d4000302160311426050750b420868a010f180d03c0702d41850001003807842ca602010719076100d076100c4034505a1300d1500038050755040c059680103414600b0814500401e030704040b01420711301403e0000d144448881800a0360b101c0d42200e1048101d01c0096403256183d04050362a94007100170b00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 379455296 1250 379454046 379454051
    0x71b0f0c030305032a070b04080d052503150b0c1005010603021c020a0509060d0207080414010e04060312140f21090a0201120504260306040c0c0b1b07120c06 69
    0x71903e407548004e12031a040e031740645e5142408200d51f00c0302035052026204449042c0e0610202244450602c0f415108041030000c8240c80043ca42c00c01c0e10a0006001e50000c2508040e0008a80c40406442070100c3d00d4600d0241c4c0e41d0072070366640740d0910f6152281103608034181800041c46030340c0764011f8003a9203010101194801030760039100d4101e20601908901242091141f400245098006007146502107080545800350175030303400f010b40d846500400c50410080000d1161542d00c038041c0da00d03c907410b4038100080d60440e221000c0d0822107807240e10400c140e10f000090741090103000d03101e0340710002c0407507138503175034615900507450703804100d01164801c101d800505490700024600504980684070000c1c00601030000d81c6c043c200060042c0c3d0b580c3c1040c1542a169205145169920a42d400c0f040342c407420031108100590343c3c0806440c080201d0102d01c00b000c01e59110074160481c1c401840065421084030340e0080b03070302411801a090743e0319070509060140d00001d040030340364440e1008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 379456546 1250 379455296 379455331
    0x311060406051b190507020d060504050d03050a05100e070306050415050118120807110d150c020703050316050705090901090b06040c0e040b150f0c07060206071b0f0c03030503 77
    0x7030f032a6030145080e002c800800c0c800a00800c0c07030160f8014005c0c140081d0440c1c5803035540c0c3d1250b0082e9103050320704a40c40e6000200001000764513208070340e00060f6100c4140007508100b20204403944d41d83c0a1a079000c0700c680c0c0454802d0740260302003002400050020b014206226690100c00038103486205e020445c1d1218014101031084001400c0c0c80200c41d04003007004040d141c01c0c0040d04600c0c0101c81c8503040502e072500ca030761010740c0601e00920a000c0006003c400f5014002650403002000095604c40002400010400300a440c4100c440c006c40190003100c0703060081c030b072844503404280c000c00c540082c002d07081b4042d004040d40c0c0740a08000031035500c429042c40111a42c0011000000d6460103c1000c00e01e000d4109070f0944170018001800440740f00700156480c0d000c140a00c2c0c4480000425140410080c400c160081800c1e00141110b07107007070580505030002490040500c0101c060055041115500c9800c01c00c5420a15031032145840e031401412907070003652580c140d9232000d14cc = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 379457796 1250 379456546 379456591
    0x10609050702010501080a0809040603080d0c111606210c020a060501060804020607060c0216120213020307050403120c0506040b1509190b010c02030d08100b0301050303090607031106040605 83
    0xc0ca80c106d8221400070103410311280c036101c03141d4001c500f43c541e00c140c444c40d00001140f00700010307000b5003040180c0055800080580a018140c80c03071211819034002412048030b603101c109140c1e0484072a424511129480d021003295581c1401c2140c200c1c1030301e46107612041c683c3c009400030391070b449418100a02e90702c4540039550410100e40081d4420340410015000900c40c2d00100070790842401110380002c0241d8200c503c849054225414002511031070348150314101928006580039910110b00c0c608116900600c1482280400b402e0070400040010301d1034424602c60b02c40c5500b10060718803a0405103031464001d401500c24000742004440740e1002817604802c0540604d54a171116060f9030010178801d006080340c00d01d04c1d81482500c8500030b001d45c0301440094500c007450740d00c200143c07415064401d80ca401c1d51b00001c0d105c400c24401070045880000858015400c1211401e4490700c0519040707a03044031400442d04103003e0b10060004000e015089a401007220109940b0044c0c102d20 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 379459046 1250 379457796 379457801
    0x108090a0503090103230114151806070c1a0301050a0b1620060403050a0b0903040b04090b220c110109230c060f0d1512030f11010e01060905070201 65
    0x140180d0001c004000d038079802a0301c400300d00c06d400542c118400080840c94040243e09910100d4681082004403001d0301d40b65001000103003104018505041046038a0a00e04407036920842c000d050005401d4180000c150a200083c1050186481710b054100c19190650300b0a200300b9002c0c46918001248602503038041c5d44000d880107040301141c1c0075907161007030969000004840d0f03030021050301e00751680b1044000c01c007139030140004201500880c81d2044540c40d0003070181940c0c0e04140814451005040101c0c1d08841c0c00d6000882e9420301c5000040385540350010f0f0380c0501c00c418140d001542c14075080500c0302d100e162511041c07001c1c100da4603803d0300c81812004120024001c603495821920a00300f1040062540485e92800303520350118030150320600c141d200900c008a46043c0801950280d4000540e580c514281d04500c1d00c40c4801d8076141c0c0a1004082c454401c2c800c030304079842441c107058120301d400024032078000002078460007401740e40a020301c40c2d0f0401000440032070050 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 379460296 1250 379459046 379459063
    0x5040302011b030225050301060603051806070207032409030c030806060a090b0705101e1b0804120e030717060a050402030a03051c05070f080a1b030c0903081206010809 74
    0x40d0064286a0a403410b10117401d281d00c2e04860228604200204143c1c40c24441d000c0584080e840009050515641c40c00c03858603103155001d207503804541000a05135000c569802200c0d030003500002918011240d03603003240d24046400d140355107405610004d156004080c850a00d00980b5030000546484c402d0100e54030810f070100c004103920b8501040807030141001042c03454005d90035141840c50f01032446050700c91424100c100846124071031400d00446200d00b050401022140800c0c90712054005855540700400203408070500c1040040010b000d002c204141c510700500350b40c14103450350364456000744000b000381c0c1e0394841c180000d03059020078420307940100c0c2c000b401001d051000e558111099400b501080b001b6605001440502c00000c0c00f03028002c0c14940c43c1c0743c0c05514401c0000384110f000900385203440b814110003900d500070010307034040007100c1c0f40703008194a40400d80c182c415008541c401000d2b408001070080c00001c8a40e1424010382090340d40c02c50725107501e00c0d9560b031002e01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 379461546 1250 379460296 379460303
    0x415030e0d0e13020708130905060f0f01180f1403010203010513050408040e0f1509060a09050606070b09031305012610080604050c04050711210f040605040302011b 72
    0x10106403914034010b074820400710200a00300364001c8065543c2c0c405a070844042140c12040120324400f00003949204200509943c0a0030402d900d0074000051f120300140e03c0f4607009050fa12031843c1264800c6c402002d0101030b40a240403003a9450050171410b40491180b851000f21305820060f44c1d24040c000c0320304840e0020560b1062010b07590300a402081c0280c408c4405180070071000a1086220800d0351140356540000d1509103003110600310814030102c01c01d4825010b00c0c003084001d507240300c103010642c0c000b07040c00103042e691000411014490100003404421a81c0108000640000000d20050075106403001f070850761030006540d81c100c415202c2440360000200c8912040041c91100c3d4015805000902c80d590344170326030303414000142c80030380d146d8010100110351170400d80250f540080311881c004c03c0802c4001125030300c0f0b141c091405a4904150511000c0404001c426a02d00040501100343c0d600da40b05000303011a41b00f03220490110700c00b003460300c80a0110b46031080c0703c181c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 379462796 1250 379461546 379461553
    0xc020f0f0106060903060e01021209070f0f0b070b090705121c090501050406120216060203070320070b091219080105010212030a0b0d0506010602010b1c1208100504050403050415030e 80
    0x941d1b40e00e202034483c0d40ca4071340142d9401d000c1c2d00ca01070892200c05000d4500c1501420300d07682015000f007040070090b04811403800030003c00308208400340c000c44550030740000b450a0540c13034400110381420000d500031940001c001c0350700729032003030089aa0110f0f04003d0b00c151900501148007a039010406129aa010030000e00003000024002d008450341d100c12000300502e0000303411003802c1c07203071150201a030b5020381c0401003000e0150548144c42c0381c0d04001100c0b608121507001c060700e2a2043d050b000346080140c10104812001c10850b42c0309411003440620785070384140b00c0c0d4154203211442c0d850009070314000002040e50003c5a4000c200c0c0302d00c00300600d5507903140340d4140a0901c100102d5003110060840b031000c241d09001c028044c103403039400441c0c0d03901c4000410901006203100d0113070500c0c20340c01c81c00c0081c2020050004a5015003000040d981e5095820801c0c084542c0c050781d0458101010030040540c4400100165603038480f1400c00d4500b1350204404031005044901d2043c1d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 379464046 1250 379462796 379462799
    0x2102063402031e0a080a1101050901050408040b09010504170105041709010806010c020102100603060b010905041109090402011b0b040611030906040305091329120d1404090c020f0f01060609 83
    0x80c00c1c54080f00f407902c8030021126605180d03503032440150311000a400004115080c8000b07224800c0c0601a044000b00f4000c4c0020b040a840d54081c0303104600c01c81c0841d201c00110f419081c0d000340c00ba50000d0261600a00ca00004e01d0b4040b4080c15044800301c8424003108401d0052440c15025100e4484060f52114040c2d62020015520000d0010060341035104803e443c00c41b0386001d0207018083d602c16a00070a0b103025600c00548000b2170351b04500e10a41c2400303000e04d603000320402640e0f1150801c4500c055903441e10300040e1512264900c0301c03000182880c9002c018003200d400c031203003e544102002c0140f4082001c1c0c92100d400181c8150804c0c0d049200868040303441140600703c400030080540500e803203107440c000201c50324041e840d043c0c02100c9a4500c141000d580c140c00440344182c40d201c1b1001c0e0086050b903210f004004031441400080e060b01c1400100300790a581c0130b44124001040300884051010b507584032082c1d000c0c11248954200a003403881c060282e071080b200c003a114010300b107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 379465296 1250 379464046 379464073
    0x20703030e1903060903090e06010905090a111e03010614121b0904020d061502070e070c0303113c1c0e0109141b010504210206340203 59
    0x40e40c42d058055145000240120205106104d400003140c8a512500712041c0b07004035090500c10002d0900e8144a071030402000980c45140000c1d5200c0280c00e0001040c8804056261440c060850500108003082031548080c84210000798146c0b2580e4840b182c56115003c402506407048a410000c0b0210141c00325004402c1100c207400b518031100c1c100c90a00040c803010408030307044000007041d950746441082002d01a58005440c07120414400b07051800e083c4146440c004501601540400c074150030780c0070505203e40c2c840e240144c040d909480d5282151481180c4803500c0d6000d58690780350038100d5008030103071802c011444080e0814a02d050401212810800084a0b4484005907032130b014590248502031090350f2001c0c5c82003810f544040286e000b024504001c025841d84111701e0603840359501e80c0c00105940440c0c8520001d251401045644104000740c3c030880250460310210742840380f003411038a45002080c50a003c52060030ba52800c00181c10011240650150807000910415 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 379466546 1250 379465296 379465309
    0x120f0a03170f0105151c0510030201030b060c070e070c050106090c0e010c0203101113060305040506180c0f01120c111501150822050307110103090302070b0a030e0303090304090c020703030e 83
    0x804001740c0e2186d080013001ea4041e010b5071000c031059030802e00c1000c070900842da018410456141804d907286402c1c03c207580c0c0d4855075880341d0300600c3c0d42d5081c56400100b5040c807500d8220285030344080240f11017540e440c0d849003d858802003040206082d9282c1030800d500c5048070128003a0024010715002c3d030380481d018010401d074048400d05103030410085001c2d100c0301204500410307540c1d82c002100d1a160030107a0921001400903a082c420300d410000100c4000a03c0305016101212410000c60300c0c107005031003020358000e101d100c05007844840c90340507400102220713008940f24256020382c882d117051620060802d010341e03c1385c190042020950580714441c6da55100981c220600700341c540d40c1d5030100800040348812a501c0d400007501b80100701010709084d00d882800c0c01c0c2400390000c0344c0e401945540c1d01d4006c0c030040c071402298000c00144641c10000e0081e4114007620790f02d00f40007284030707203d6000b40030b04680e1303a0600c0c412490242c80019a030084030b8140d91144c40d07904000e1304101c2c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 379467796 1250 379466546 379466557
    0xf0c0f020c09010e0907030f0b01030b0f0f010504020f0d0f050603060a0c12090311300315040b0f120703051b1003020d021c020903060609070e120f0a03170f010515 72
    0x20320300c1086000b10012340f0060740305070303002d0042001c085a0b600d180b402046014006050110b854a20360602c90b84501034403256041da60100c82c007680310f10300034409150b64050141402c69450515103000b441c0601c44d40143d0060703505406484082c1d8850803918140d030303400d28580300003803070b03001400388002c226510902e1242c0c030038604a400010154181072410350401110382610340c848223081041941c860f443c04480744409242401d518001c00c1000b07400070300c03625290159440760b1030180c50b40d451070002580c0000c000e000301c00301021480643d55680d043e0004545030320543c0d42d40c0e100043c0c1d4140c1c0d20034142d80208520042c01141d54120069080907460040503602480803c0041c1c1201c840e20345084040030b00140c90b020440201840c00c6000b6200d14010343e4000107100c0c9250744030074095010902034400750f40c201c1d094205a4542001500d0851043c01450480003c06034020a40900d5141e80118880242c4901d055540c0d00082071064562020410030042110324890000c2c02 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 379469046 1250 379467796 379467811
    0xa030f1109090a2901060504060306120206032701020c030403060f060e0c0d0e03030f0703140403050a0e03030d022206090b0417031903020a1403040b0604020c100f0c0f020c09010e 79
    0xc181c03441c0c10b1301030b2040440a8119101098001c074090150b9030745449010001d21420f146164010540d40100c3c00307501c030141514800c03a803000c480346440700d540d5400e10360f03d0741036000031541d440c492044280c4907003250000700c071080d00381092241817488074050341d0240c52103924402480d0329000403a070410382c45240c02c208454ac030781c48030b8048243d052028512410717a005081c1e5403803400c032100408598481e88050400e040e09030a01c030210b07900a081e81c0c0c1d86200340c02c0106116024400292460154100c0b00d250107000007a01007141044500c82156109070300006006c0a490b03803030584014030240103140450205010800104440844603807080320030740c040d00e180810304041031102880039540c0314086a00026004025548107120301c00f4400c03411186411405d150f0340b0701580b000701802080c455900498150701040f401c0c00f540307000c1060b400f4100141c900317000e41400a0f180d1000400c0118400402703846100d0700109030281006002440c0c2001a802c25040c080c500a0190000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 379470296 1250 379469046 379469093
    0x9150507120603050a020f01022409120403080d0b12030d05060a081b010216061b0206090901030f020a050603070f08041b170609010b0d200a030f1109090a 68
    0x44400d0700500c50b07203020714020000f404a0640c00d005104850b1824030601e41190300c01c03c0006200c40c2000d640c80c001d18000d0034511402d0300c40001c031500e0914a20300015040e8400a000810040c00a00400000400741c6051000c00811001c001010310b81a44628140c1c00410828840310300c03591041d07901640083c6102031203602c80d2051841c1099074102d00b600e052001a0400304c960701004070191144418901070075503801c140000342850640d400070801c2c40160030004013155038100598440703010141c401e410a6a61781071420720160b681340700782d000700e0800e2004561401d14030201c0c0d1041360540c85501100f240349400302e50318a001031041c1d445030014803006494141c0f004034000241004034620320705140130310104e82403400260015500741c5c5800c1100b10b440c0c451a5886014640010448003c040c0e203420001481d03c0790f81010760b0251910b28080104030100855079042070080006000010244052144401045d600503c0c1c6600030703c48074001446003402010190b0300c03491318 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 379471546 1250 379470296 379470317
    0x302090c210a090506060f100810150c1217010302010e030106080730030f05070302010b03060a021908070e0609150a26060d06020d02070507060201060f0909150507 72
    0x4003601c4034000d480c0000c00341d0700c40c075981e010300404000c003a41010040314003440c000c1c00b28000442c0d5542d5212a8414040e280c0b00107001c030000e80407188014049249000110360402c0c07001030080c00d4103101140c00001900e02d010100b4030401c4d50b12032203001c2c6003041003242d00355001940ca2203100b8480c070fa495904c0c0d41010034502c170705020801c010a5481c0c0030640001400441c3c03880003210000340d4007056242c021010100e41e1000914144c00c5150038a20b581303080a00701207014101aa40d2607401d0b101e2002407140c220701c15030003008082002030b03128010180c100c02c1102c03c1182074030001c0005c1c0350742111025628010700146250540100300d03411100d03103840c80d4581500004070038000300325090140c0c16001d2030002031002c64500b0360f01c101400d01c2c15031700282645a42e2071015190541c0410034070315600f102c2d41190381c280d40100c00c80d500d09a036590007e010340305601074522030700e080c134000140e00c80721402400798041d4044501802c010380d0510740002840b000b4088001c202ca038101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 379472796 1250 379471546 379471597
    0x708130f0507080d030e030c0a0813090903021023061002010905011103010f050303030705070602130b0c06150102010c0e0402070203240106021b1003050411060a0503011e0302090c 79
    0xc82000300745540280400c8010000301404846d840c0d094261160000c1000d403699540105592101c44e6100c0c0c140c03034484410000d022100c40c1c0c00d405c6160494504442e4809054002a800c002c490002c2c000340644d07006003802c2c1d401d14030f80ca00c1100da644803220100f4018074050040a80d00442880001031480483c1c84e800d0a49043c1b070009400c1c0b080c000010702041d4103010700301c00903001c20b0b070045180d428102e000900b81e2207108005031078140e02040340501a416250100300030b240d0341c0d40203502e90380f1098526458a400303803810b0305c94041c1401150017550041c050300e190f03c81c040c0c82d0341032020008818403000c0d500100040340c0c14041c034281045280240300d145080700f00f000c3d441805941c1080400b82c58000084010050b0702c0f0040b840408541d070348034210120184078a07001c14551101d2409950b42000d5000d003c1c0e0000c4049550b0b01d450360302c00d024504840014400869440d001d555003806030909000107508800c0d48800200415400c1004002040c03206149000711000c904 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 379474046 1250 379472796 379472803
    0x60906060406080f1b0f07020a05030307080f1327141302040504050c09041b06051303020f130507030b03060f01080312130c121209051e03030f0a0f080f0708130f05 72
    0x1b040c0c05642440811490258144041170b200030f80070940c000d602c0d180154039144540d00424010030b01701400003596844103003c0f102c0540003810201c0c4000d29180454130400c02500b902103210003883e19051407050340d4842c41c80c0341c0d8002c2e2540c1400b0484141c05400380401381c44010400d407150721400312446000d455416006200e2800b60500c07205200107a40c410020311400d501c5035041000502011103010390400c1c0707400880350304a0381c00e1543c1000d04041180d880c546804c0c43c010174030741804c2183c4160107804c41e500d8198114182c2d20141d507002441c9440110030b0044004030303842480854005040d0740981500b0030030100090310032088595401e84070b009650864158200340782d01030420040450104021210641007140c040fa0420b00882e00e645111031080b81c0390005040b000c803298030140120f6040109500d80d0b2995200b051402078000080d0b03511100018080c2400124890408000d1500512148d17851a80c1919903242e0606894600c040540d010b01122142e400080c2d000c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 379475296 1250 379474046 379474057
    0x4120602090d080a17061c1a0414010c0201112505190c05060a0e06030714120f0f0403050405090c040e040c09110c0a0b0403030b1305060906060406080f1b 68
    0x800083e03541d40441c01d03009104002c940b10048201c95040d00b8000c04d81e07115500844001042100190748003201c0c00c2c601c03008001c1d020031034070b50420f00741403000f404000104121500c0e0510002d020001564404030708030f50b4030141241101d1014800d4501051f442d60002c0e01e04000c0010f400c0c40001c540d21030a003400c480d402c1c1207040d594140030a00410140450400c020708013124603070b0415505000c09442004280b40c1244a28400030000300214010350003071940d1010403e659031035451106809400c190140ca8604407104030b1400150035601143c0c0d21841181e050381d07007909240c6040c09101400d24003625980c1c04000a0202241d0b01171550f8516200f203020700b00b4002480d01c2d20311000e0403100e4181c0000707650314081127160b146100014690382c00d15404501c41005d0340e6213040c02c40003420840e003034a44c401c1c201451000810310325001540143c3d000c5400004503100d400800210b4403641c030038400032a00d580c0010301d440c51006000765200520b4012240301c542c06030384008081c0d11a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 379476546 1250 379475296 379475303
    0x504201206010201140106052208010612060b0a120602030406090807150b060a0918060f0e010602060a020910030c0c06062903043305010f0608090a0804120602090d 72
    0xd60080003403540e424010743c0144a005d810340f00c043c1d414860f00501610408009481451803003070313090300d440081d10999000340203081c02082200d446144101c1d44540d042d400b902e00608003010b08225140c41441002111b9082000f100d80407020340d240000f80d00010070607540c0315900c0901101003082c40004058561168442002d085110240c1d40203c0d010f01ea5140d02404003031148c0140140c2126102c0155401603412a00480701000c42001501c800d40003503001072a5000001075800c00119264140d400c10b40070750340350740e840c07800c4441240078800903154041d0b0849e440851850183d4403556810105151034005000c860b02e0304001c0d14105e9001100084400c1421284001034210303c100c0846150580307440e508141d1244180b07003801c5445224204558a981110700030403034541300d1031400344041400a07683d24000f042c440d4003071303100f10004030b100348001980740d900114035501020750204010b82070505201c0800e1641c0030051046130002d07030030050a800c5580b46180c4030a4a0b11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 379477796 1250 379476546 379476577
    0x40f0501091a060912070302061b210f09010203090a08030c0c0319110316060806150a0f0305060402040b0408010c021c0c030c021512011419050420 65
    0x140003a52400c036a002c500600c0b50707040494401e050b66441d042210240c2100301e400500c158007030307040e407802c2c82100c0d440254000000114540864011403604841601141c107640c2c990200700789120f03540280b0700c884036030414100054101440c045014113486d540602c1103905200307400011502c070101d0798020f040c1c1607002042400ca15502000304020b03811b025000b4000034110542c40040d82c40c0b10301c90051862400304546501034400b00b1001100c1080c4c000704045003659000054009a0156003007406081303c0f08900f00030032010350031690703010070940c2c42139844800c9040440040001030300090f0b002c2c0d020800000c00420f8580036101508888000103186002640041d2802900b0320810310300c1d00006206109054116902d440c10f1509801d2852940400d8130005a48840408030405405404a0a00500000e002c0114182c403d81d03221104500440c00807caa0445600004c45404042e88424443d600f4503030070402c1d020320945d00070321007004031844205c1d0580000c13850f060440e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 379479046 1250 379477796 379477799
    0xa060906020c0f0f010b010212030105040b01020c0d030e0f011403041506080106091b08090607030b033406030e1b040b0406060c0b0a02090d0f032a030305011d24040f0501 75
    0x4c00e1003492803a1009000403c000054070883e00b40b90700051188034450342e610784c0303448003590003031102c1c5416180003448803100d14214500644881005500c02d8040c3d00902003092081d40500040400380804c00c0c271490550341c1e5030780d45125007020f00c0510240c0030384407040018005001d01030207015003050340c00400c001401840320315011000c0d800f0901044044028441d0007440410a580c212010385008104265500d0100e80f4010b41c1070300700000022010510b0322008804104180050140030640c443c080d550001203007901c80e10b503004115504041031340640711010740d144071a00c0d1000351012070b04104c1e402c0050101ca00d541e000350f001c10f02e034041980400c08031040940d1302c00c29001c011420009840c1c04a0441d0900020040c44d001c0214001014140500207595854080741d625280030389003071207032035000303a0583c0040780842e081000214102202820900805680c44080001c40c0d59a110625221040c0a015984c444120101000702e45030340c0102c00004d48854004a41035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 379480296 1250 379479046 379479073
    0xc04050105060708070f05070627030c0302190f14011b0201020d0e01020c0307090219090803040306020a121104050111060603120a200a0212010203060108060402030c04050901030506040605070804050a060906020c0f 94
    0x41400032b183d0300b5007e11900e0500c00240d0501c420015281c0554402500340b00c0901a0b51802c0314a030046114000d40040c001400880d1041d6410190420fa807017607525001c0c041c0c5054060519000240940c01911262040d944510404203441905204890006644c0000320781000340f00d4001150140d00021308c60011415240d003550001280d1504008883c9802c1e00310341c483c000e81c0002041c440c2c000403441c80003845050746000825500c001040030300c02c3e17024060f5880d8058883c0f40e01040540d502040c03070103000b003070582c0304000103800b5100714007407400e81e02d209a000030640781c28454682c45070085004001d40404901032450b004018011950040002a10340c040d000c02d001d0b80100200500c42c0d0b4410a10740c0c10920a40b00540c903070311001440401c0380150380100e500b264040000100f4400c000900c24001c40c01a4001c10482d01c4642e801c03a89035102b2540944980e2107400c9903000104954084201d882c007600006003444154003801c1d0503d0840021051558481c03420382052 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 379481546 1250 379480296 379480337
    0xc07180e0c030f0601140607060f0f06050f0d080a11031b0c040c050a0c03020712032a02030a0f0501021204050a0302101a13060918050c04050105060708070f050706 72
    0x410044005003e0025205951a601e250500480a84140c0c0d50381c480b0850b201c0d03505480007954030503000e02481c3e4903440081c1c004c14500c0590141c00781407800014441c00c113420140b404002c081c0503a1000240c9440f461420b905c03400d080300c100800e904490041031428006000414110300c081c2c54130351030122a0740c0c5015568000244940e180c042041c0c40c0c1074001c0c0450740030442c03a0500b403468044c24107080e41405801c1d401078400058804440e0105580b0080c09400c414442103c0e420340c9a10041c885100b245510000303405900c1041c009010174040c0781c007020000c0c07040303001500d0441444801800741c201520201d44a612800804c0f0425805200c50b28040c00440010042c4241c02c40341d02d41c12004500c95540103030101380600994018a812410180c00b090005005d00d051505200c405208030120a40c2e943c010014000c040c0d02e00390082904894004011a05003099900d6030083ea42c0807050840d11003008207041070000d00c040c800b904c01445c081d00d9050408a103a5040d071030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 379482796 1250 379481546 379481563
    0x4150513140114150d080c0708070902040f0302330901170f06010c030c0c0f0315020c030322050f0c0102011a0a06050a050f160606140f060c07180e 65
    0x1860f4106440c181c542000800020b911040ca2945810003601c00c1300403808210380d4400181103900f000580d00c0c8609400a540c90464400d1022502d900d613860340940124042c43c0507211044000300410005842e01035803034410001586100e09071552120550764990b290451034a0768050003044840440da0414140c03190702204000c0b4440c1d9107049490000e02850007440d40703050000076801c00c403e25100d13040002c0340507400b10108890310b80340e00003450078400d14842110811a80b461b604100c1850b8001d4411042c2003c000350b045896961b01d004020f40d80344404c151000c500011a400b0501c10001103d060229070054841d06240c50002400d5854641010354000d40703041d00141a502d480202204a81c66843c0564440c1c4004000301c825100302c454401c6000700100e007000c00000e00720401c80c0803a00c645410042d55503105141d4152001d9050502c0d48501c00071200d407818200381c80242445d05114060b00c001c2615811084110034501c4480c848984c1d4810302c85483c06020041c044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 379484046 1250 379482796 379482833
    0xe191a010e1207090515091806060a06080c031b19080108030a020606060d0e0d050913141b090607060501030c0e0105092a0301030b0a061a09040504150513 68
    0x4041998a0007030f40c3d6440e10710035849129900c100003090040c10840c0034000c0784006012980a00b440c0d840030551002c030500580503030194602040803450020181c00c04c035030980e200d40300160b40d00508201640c000406c00c2402001900a482003084103600030300d0800b4074214403100c00c1040d118014620b020507080708031554420001c484516400041c980d0344940d00312812580d41c0d907210b808201600700003a10012521400c960000c2c4070350030201809002d40c0680d0045c8420080e03454010a85858002800d202030b282c81c04550701c550b0090117507400c641c50342150fa01d4091032602090880d4003002055410549d01ca005104102070404090024420b0b400d00c8843c80d41003200045c41800301804040281140c10740d041c1c0b0a158220680792108400648140c803580c0d01c0c00c040018020850f8142c2000385041004601c1b41e074010780c1c10030f0302d5500134180360401070310b44180b100400340a44113881090015000361000344060203140c0c407440280f0300d0ba0150800c18503004a08818401c203d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 379485296 1250 379484046 379484059
    0xc0301020a0c0b18030304050f160f0b0d09050d03020406031a150c0c03031605010b12071211151c0504031218060c09060e0109030b010e191a010e 64
    0x980505900040400d51243c0201c02c4000d9a2151041083e2501c407100800d0014000801003000780b000214000400d0002081a9044031403c0c1007050540b0100e40609003c0000898003800901031a40180800300d840c2d4030002901003450319013a01d03220346060302000103500010207000c0f0310f0341401400900b802003210010081501c000090040e080f4544c000d420351404511800c07081420040d20241c1c0340003405890ba0ba200c41d0801c031004055030503060b6003030f60074210320541e41d05082904c1c26411074060301400d48241412040340031001440c6e81a11307440892503114000341d48111072909081c0110809907900c890001e28952680d0070317000c90781002c80c5003008010209820444070408110942400210105001a84580c01003076090280900d40741141c01d85078175400c038100800361207298841c00110a84840111071101c2540802000848054010062040c01c0200c1507004281c0c4a403011642d14a4600b2804071004042c428404144600845c481035070085060415a030b0140d0b00d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 379486546 1250 379485296 379485307
    0x1110708030a03090f0606080307030806030a03021c0201090605160306081204051003140f0f280902030a0209070c0308060901080a1401060b1305090c121503070306020301170c030102 80
    0x526072a40540d03a507690616484404c18800c008002c14605440d682c4100d082160035140c2c051035980780c02140381207010410103800325a80c0d00e800910a40407540c90350040107003c001e65040410324501004035800d564950140c83c00080c2c00b8010a8890007500e040e007044840d010320018241c56041e0700c091070030703084010296411609074048030151541926009050f0344940b07011030062943d100e4488401e04e412041c42126040880a24081c0c101c1e088800091b8603010404043c14400d10b000094048404030000c84110980e0001d800860004003130300c8c1c6402c1d180d000b00345480740071649007000500114040c403c25800c0007005400a80c2503c070070010b50b0501e6280f55640d0030707122014203000385119401d2800e01d02500b1600160071b40f0801551a4400c1462200b0803a0107805010321074090500051f040d00d081400f0b40c1c8442900d4540924280c07183d2041ca1002c941800110343c1602a40350302102158440c0015070091120f41000c401c41102200294200700f100c1444070311a0b40100700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 379487796 1250 379486546 379486559
    0x40908180406030302070b0a1206091a030106230a0909081c09170d0b150405130b0a0e07030603170304211e03020d090f03090905010b190512090606011107 68
    0x82e4041511101040c441c0d4641105d00240c27100030340c03085038a000300c1c00d240c8080b5564000e50401c0c80040300501d808070a10144500b01b41c00d0380c0041c003130a0b232601d170801104101183c2c130000810005134085c02150200740c45d56031175000e40c0d000807007d40c1d503c48001080c0d41c030800c00c00040402c0041455041041c44e41c1940c40702c801c160000f10360300c550350740807900486a80c165070215001e100002c0c55840400d000c4c4000c43d402c1d411610401748581d004050100c2010064000d241f400f0070000c0c504500c0d0380c10500c2c3d00c940a42c0290001d0100366031303400301100050010341405d105000e2001c00a84916017407900c518034401f01081840080140c3c0e80c1d819140740c0001c0c01c10f200e445150203800c1c0e2002c00000450090040904540b207031070900c0740711401c0c0200340e05840030440c040d555820000307445059000035140c0a12030684012010040e185a6000443d6525250189482c2c0a1710301944058000100c1d102071f90000c1854000009200e0b4540c2c000007900d5404917964003900340300341344c1036 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 379489046 1250 379487796 379487803
    0x12140106080601050c0105010611070b1608341101050a1403090a021503100b030114010e130207110301230406050705040f0f140d110d11040908180406030302 69
    0x3161409001e80000810116802501920304010005008000c40d41e03480c4401441c8040d000f990588901a58801150891209046402c40141c4514006449140d030b51003650f00c3c0e0007141e10342d054900c00700d000c141030050f40c4021481300b5501011485105000d081c101100c2c0b080e000c169041c8103040140b2001c0703541050b41e4040316030309110015100c2e40d80c0f420160404c1c0031640d000b9803101c120184000008010340113103000746a0840c0d4012641d448200018842c4020301030055001c500c012009460740c8110300201e6115400391103030500d600c0c4281c11600341d0b001100211082040030704141410b080034840c00589011070a00f4070620b0351924007000c81c00ea000360001c1d100c00d40303a40000c1d520300e0264040f00d0062020f800c250240950340d1840d40e1947c1800e00801442e05004003004041e4500346500002e40b40c0c0000b202034031150088100101001444000c035030000342c02c0c5090b05207a03564070940e101c0d00c1c00b030410903654040c0180e0070b45620800201652140340f4001040c00401c1c0d000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 379490296 1250 379489046 379489049
    0x50a03111c0e0f010c1e03050903120709170312060a0f180905030a0206010806060a23010c080c0d180b030105010c081303060603050c090c0d020d090b04060507121401 73
    0x14000003110307442c000040b81414502035450701c0541c24801000802a80140528080d1055111061020b800100c1c210152030041c1c2d50b50100d075205001b40358626064130b034000c3d0000300038140844125501c0ca02c040c08000c180e01400e0031a080402c0e070803c000c04c41c00c66594810000c994440c8201d04000e1200701c0c82c0a40d0040440c0021410404100d10a09a11100d00a074100084076250035052a000707581d50303000d004000c101c0c05540040354842c04d21380c00754003c0c0c40c10901d0b00b0382034a61000c0140440130f400788103e410880321000707500118199100400054010401500c0000094403000c0c0041041c9021a0784484130841c007000000d0106050324191102468400f4400f40b0500308800350b40181d0b0203c00408805550001c100840e590010007100c0c4200241d80c0211000360410043e00c2040f280d00440316030802c01d01400f018194001c2c02d5558502e0f0b8009540061b540702c018403200c04440440c1c51551310f4003482070b429041000307080188041e880c20700c0f40c2d0701094050040381006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 379491546 1250 379490296 379490347
    0xe0402180705031803040b18030d030c0c021003090c030501020c16030f021918050f011e050909070306050412081f06081510030b09090a02030a080d0207050706050a0311 74
    0x104c1300d200c404680d00344102c0b0014030f20040721940780e011114480c0141c0000c000608d109124111444161f507010340a01c500504080d01d442c8600500c41e000d11940803c5410348408060f0f584040e4000107000c4c40704400918003030000142c8170749910b40b42c20b141c02842c000604540441800030000610281c040a0310181d050f110340010340700840400340d4514158100c030401c610f003903048604882440e030255110b001404d031005000c0c0d0f6206800c110392440c009502c0d00d6461030704001d102e1030812600c0d96030010821000ca404050352601d412003281e03015070702140d01040c40290704003507a603c100441d8012000c480b80310500d406001c2c0d01c1800601501c44c50080c005050001040090105820300000c200501140801003000c80000e00030840d298910707104441040100c0c1c00140c00252a50025074090001d052114080c2c4801e0740c180c000e503401103107540d020004480016400c0c010000240015210151511032995002c0d0541c1c0c60354600d1511408280070307244000d0b503442810240c1480 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 379492796 1250 379491546 379491571
    0x3060403201603080a020312150324040b040312111306110d0e01050f040e0601030c0912060e0a080a02151e01090203060a03240b040603080403080309070806010e040218070503 77
    0x105c0c00403d81c1103004034100200c40a020368104040c1c51000311443c1c606000880540d1181c4842c00d140c0c101845048103c0164401c1e240000382c000b8800d2103181c0e800c03500900300040001616000b400a81e40348201c01122504041080700d10002c096a60002030131490400d420485941c40d21169240c4942e4132035020800800c8620000b64010001c40350300450301051035a0715500d03003203c141000010740303d2500007487d011041c000789124026071400c0c0d4041003661528a03c49403601c201130002d110300c2c584240a03002c0e12000080303000b0001c9c10b4220b1030360040c000d9002c40411907031001070f00400e5112107078800014051a56040100706054840d00000180c4945444001c10032130419034000505031001e0381d140300300f405411004841d00044118050241003010814002564640c0c0b10003412681c00307010504c002100c010145030b004003154100da0307105644402e250b107814002e13031001e4500b038207880511080d4107100702049101089210034000e03a0034603202c000c02034400248a8200000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 379494046 1250 379492796 379492807
    0x20a020d11030d0f0e01020a020604050d110a17061501020606091f140406090608032b051e0a0203070903030f020a0506090705032503110402090306040320160308 71
    0x280300c0320310080c040c05421155000d448410181c07107045042c1084d03001c207040c0080c605940d0300c00103c003100198060402d504151410050142c1c14a03030000c11501004500d48c607024a07240c820090300105000700c480e840c034603410000c041c2000b074042c11000d0220200c0c501129580d80002d000c50708141c040c0e072070f0700f00303991440701043c1c00c0c0380d02c0060801030001d40c000000d142c43d40b101d46c00314201c600703c2c1c0070080107a40da10300303d041f2a070911035007166400901c03c1c52101c2d1003000c0e0071001060181c6040001e4005032007024101d40045a40e003100040085020624881c2c0d55051703580108820b908521794140301d0030240241106200c01820082d140c0c0040c2c261138800c0c045007540d0783d8080101c0c0d0581c01c20300300054880000f40246402031248807100000f590742c540700081882c0d80e05c03010f85802405c5483da107010245915200340c100350208000c0925442c02c00075244141d00955848500c6083d07506018500440400440003951040504e603054a000f0500d200880e548180840d5958 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 379495296 1250 379494046 379494053
    0x120c070c03150516111522080c010b04140610051c0902090603010516030209011404080a02090c0309030d090501090b07050c120a1d030c3c01020a020d 66
    0x35260802003480480485400071580c030350b004540102d000102a03004500d005130708845000c6940030008040c0d0165090720b081da034180511941009055220561040e081c942509140400e140202d03402c2d200001d0405040c10280f0a0400401c81160305000090a00003100703180d680207040188103140d030080301004980900c088644568016019400390640003001d04014049082c0c1079009018401c0001c410340341c1031181e01d10a1840311300c24847c10320600030880c02900550041c6050212024200d10042c0418001d0070003020039400a00301c41c1414410301c40841c00c0940b008144580c180240800c6000100580307a07030010200300095040c2850030824050020700d180039002400800901002c41d501c04003c0c20112003400861f41a4003d408025440d4480ca0014500181c128400101042210010502c80c13510003411960468a410009170030450194400d41d50007030340b400c100304032800200d180703150030002c1107074a0046d0588000103074070750f40d810030000d101c0c5040c0e56144041 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 379496402 1106 379495296 379495313
    0x1809090d0e101b0305071b080c040b090c070c050a090e15010f2d090203010503010b06030f0703021606090305120f070c120908030c010204140303120c07 67
    0x245031083c0c6000c440301e01d08411003c0280070029400800d1200c0c41085020801c030100d41840391500501c10301c3c041e200746c07020703000340c0c10041207a10b0b60380d42d031a209611840090446030f65503a1454404004140c541041d40d0080a946021441240550018011342d15140c03c03a9070250301c40103400c1e0754030002d01c202880e0380c901c8070091140502c46046075210510242c692040c0d501314154840b6030300d495401c11400d00d0b501000410840c44c09000c2c41ca02a101541c03810b01e10b042c40802410110402841d440030306800003081c10346040503032041038103035800800801c015852860010300c0c952201c2c0c00b40c9900c44144ac041030455403510026806041c1030f48030700c8542c1030140c1c0c5480c00c52000400405c2882050040080c543c00248001c0020b81c004c080016612800c15440001010425858600940c0180246084201d00d02201500300c0c90400d000380d1203d0091070110b11 = true := by decide +kernel

theorem cover : BRFrame.Cov 379316546 379496402 := by
  have h0 := BRFrame.cov_init 379316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 379316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 379316546 ≤ n) (h2 : n < 379496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
