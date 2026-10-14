-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3299
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:14:59.990833+00:00
-- url     : https://prove2.me/submissions/fe3568eb-a60a-45b6-81fa-47e3d77f72b7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 593165467 ≤ n < 593345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 593166717 1250 593165467 593165471
    0x5010e2415040c03050a051008070b0f160b01030b01080115060305090c0a0b0414090f04030509010512191b0f0e030c0901090504060c0c0f0219030f0f0302010b0604081c03 75
    0x20700c00104003500c122a400c0c40c0402d032500180700d1020304610602c0e9002042015000c081c6081034103280d2075901520540310032140c04074001d0082611041101c103040000c2d500741c0e1400c0d43e03074039003900440024030081d1800d641c1f40000240f80700060240b100803449070241ea112560030700d00141c001b0140608071000d58490540e03407e800e51100014030b805061069a0f842d101c03031401a0700090002c3c904000c5000342695800c0c00215240a03445075001035150824036200d89403480100d031280114400c500404074580140502441c0301c0c1d90a10301e01c0441c1c4000e10000a84c5400000c1441444a60348005524000b6156503144515209031281304014144c4103904031020004d4048102a00300c3d100071940e4106100800495200d101100c558904180801d100d0680f259040e074005d050010380074021285d00481140014402c1801940d886001035101428506000b45080e1a2a80440141d8079150000078585003101c1554101c40340b000040c0795100d1180e0b075561103846000309a8050603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 593167967 1250 593166717 593166751
    0x106082502101e2a03110c1b24040b0711030d091a070201020a12051e0d06062109021809060406050f19090c172118040b0a0302040e030705010e24 64
    0x84014023001004200140c1e101080d0107401040040e12180d900340107041040074640c05d00b000c0d01030300c143c47c00c0700c00042d43c0c26101c205504050420407110281158140100341034031300030a07008014002580e6080b104910b0b5140203d40a404c01d00c281c40001c2d0159115004100000f035441c58951120895450640d0410748007222a204840310070307915540040703000c41e030012800458868600180868605000c21051714006400366003058958a03641e2512008244150340710759002410300c241100c80b4043c40d01e0010991500c03000c080c1c80466105081001080c14896914080c0d4010f145100c500503056209101c030800502c0742d40002c542c4078054680c00182075403900240c511002d40013000c0c1200d0401c10040d503201c008545d1801c00301c00c00a001001c103080003c02d00003984a4250f40010340300304280c0001d06211b241380d00095000e41800040c62441401002a00c2440d2213030b07000748440825441d040b6250040748917900c8120320700340c800800c42182e1425140c1c0007070b42c003d1011100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 593169217 1250 593167967 593167987
    0xb011503110c01091104021911010e0a0c030201180308090d02180c0a090b03070e040209130f0204080c120d0f140708040303080106082502101e2a0311 66
    0x70740c10510360854a43d5407403440340b0610504114280c1c0e1403008490840c034044200e11460300081003211b40004000c00740c07084c00c07d46182584000d14070308280c03044a007113901614000c0700b0781c00140000c1f80010340d4880034100e1070090a82820689a10000301400c1000c0701081c0512035a40140690f0301440407604c4900e01c01c8a1428140965150704c0810382c0c41c1c03108640600103448030703446413444040070010021815400b08010070a168100c0b405641d520f079180000e40380c0c04160002030ba0003440c02010388045d021560080080307480f1041030b10390082e0008200001149903140c040116007014007440311551140c0704c8460140352605040c5018485000d108140c0d40003d14100c03540200000d040c018036420559140c014078081c6440c00c15850010603602d203070040c0d155060446404505580792032802400101e40c2640069804c0025890b00c001c51007801904081101c0031600d8210303176076403201c40006801d1007498491504641c6120000045009044d00403001032106814420721006c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 593170467 1250 593169217 593169251
    0xa090e0a0203010302010f0822020406090212060f03070503060a0509161202130903020a0b070318080403170a210612030806150307020d050c0a050708031908040b011503 74
    0x40300800401600e0390704500c005095640041c0f094400d2004800400510036080c0c031400701d4181130401c00e44840c81603440410042d14254020741c000fa80049003611000344846225880b518044514650742e903101800d264991210b401116015000580041c00c425010340025401181441c21140c84082105ca0400c2c4d0035180d4020081c9420303104000360a61920006040ca25070b204e40301001804056a03020759104500c0e1001132101c040c0d43e001506450082c1c0c0320401e1107100070281100c0c600e0510b003551044c2d03c1408100c1e4104905a00b013800800654143c1d213041f001500c65251850008092030b44820103490510305080c1c070f410010401c46805584070360321911a454600301e904000d0100403120040f401d03901011b58007402007145043c0d000903200715184890401c10750f280c094405060401502c03010103400386c4200a400654007600200820103200805c00d035501d0014595800c4840740300907140a8010000040140f0180807804024030501c80c650400040d5000c006800300c0d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 593171717 1250 593170467 593170471
    0x10b19030504080c01050106201204030b0403090329010b0c19050304090c0e040513112701151803030f030509031303051b030a0f3206070905030d02120a090e 69
    0x29000450310501e4074224a4000e40202449d014208608500c00040054051440017400314644207000c28207041c05020207501540c1c00214141c01c1c041c203001c2c0403090042d1041614010103e00000080d005180c1040d100c3d03c401460107000550b00c1e000320304003109030b000002d4915020402000440f90b81d00c0c81042416036a549403484c40d4000a000c00c412180d00421900355103402140c150b001507840076095644507011036526906031500d1b000ca518030014480d0b0a41c00940078400070442c001e03260a01780e0468480e5a400c2151550342003201c100700c2051100038041904c1d60152407965000c2d40110383d12128102c00ca07070610740d030000300341c1c000c85903980f040e140c503001a80c1d641c0c001031104011801804056005000442e1250b45421840508a00c042c010f410300240020821500079286a6100030003104c406001e0501e06070252504400e995400210710300b101c000625042c04100f0b10809019500580401d40060348001362581c8070140c85004c11200e84004070b502a02c03a07076194 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 593172967 1250 593171717 593171729
    0xf01170a0b13020c070918060203040f06060503070b090607062913091a0405030f030a0f06060c0308040620040e090717030304140c040e0105040506010b19030504080c010501 76
    0x108440c0090410300540540c40169080c1c1280104468001d10388005051000c1ba0f2041c00300040042c0110035640d01c48440141c0201154000000c0c08140304075030799160101401180c042008641d601c0c20035a071045140703d141d8840000b484103c0c0e0500d0f01d0000341c01058040d03a40460b901502c400c1043c200d0054a5400250300c10240e06081c0c14240b440603051f0890212804001420b0b880e1640d03502488078080402c80c800c0003800080c200001441501c102e00c80d10142141c50b41042c80141016140009040e14990b02d041d0000074041d1158034800081601625648440d8542ea00d8190142151001241c2d81d1040107200c00032a0403080014001440c880391307103e00c1c2e8108807190030f0400721964000071080c04882518107819001004907904264401b44c4040e40303030680e90b00f950a0168000b403482c2e0243c034001400c0c0200e1019000148250b102e4011b458031030780c9030386499400340158802d040002e00b0203030384501c40600982c042504540500e9a0ba800d0141d915121402e50310242c100c1c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 593174217 1250 593172967 593172971
    0xf130b070c120c1a0c18030703060c090329041e0c0609090b1203040b130905270a03020c010e010513090212010b0415030b04021c06320f01170a 63
    0x10024021050300c400440115096500301c0c4d810107046445081c0644480f89184031000c1d46101480d075000c05ca074100566101c1e40501140c201c00030f01030311420561205550a805034005000d8603068a22802d11811403140852420388aa171107040c0a00038400c3ca820205220102c0340001c0f84050a20300300030641544d940c18031030306100200c015200c941480310701540d544844103078214004002e072001d50341c0085456886c0d030303050000c072070f0154860b510400940785400184000b14480d02030a032094030400082c1445103841a900c503940d0700c00b40340c01400603048600421565803080c0c003904c4142ea014980941400000c103030b4038012007050392084080380c0e800244804540d0030a0100750051900407111401e0515005240d03404c1e40c20b01c4d41d014101503480010708856a0780d030741545d500f002482c4503180400c402380c80802c020301150150071507400d888e12134240301d10300105520000301c49000030303041c2d03001039041445402c0000010b080c0c14440b40d140c00c40c554058449161388215a48100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 593175467 1250 593174217 593174237
    0xe180a021204230f071a1639151709060106090b030c040915080118050105130f021302160b070e0a26011808120f130b070c12 55
    0x220985000f5048100b01d19001904100100c0d6030111302407081390041c044a503a10090758045030307210321512850740110454810800180a5114102145114002d80c0c0c0c81d00c1416183e031424449041e4402440109607661052000710890400906000110b040448510b46082402c2681410480b49116076510050040002c0340e07001030b83c1001031018a8985180d414200303004a200c2c8203600501c0343c0b90b034a82401400d00b40855030b940c1d004203080c0d0000c00240980c0c85030200000c2c5011030640e1700f903080c4408504080041c1c03410541140d4000b01d20100c0e818180d09100203001d1030300e190141e082cad0074041286000219a402070300f403485a030b030302e00310307841d2494000c0c19406042040f01e025203403540040c04179010207030141010401000701903802c001e00c4400180034001ca852010b0005002c07140110801c00380d1780181000c9003515546d11301607a5104005000c1c91b6080710000b400014081c104808200080e003400e0b005815450481440c0b005919403510035030900c180c100009001c911 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 593176717 1250 593175467 593175503
    0x306040f18081e04032f0a0602100608010b28050d080307110d0807200f070608010b090f060715022a0c0901060509060c0607030207120e180a021204 65
    0x8041c0c1d0904682030f43d0507081c01e0850300d40001401c41a1180c5e1680c020b500c103941c80c2881960b01c140340000c002840d004005884000094640c00018203c500c6582461804200c8040600074910b01e03200140110510882001c80d2401350840d540b4003100c2030f9581e00d000310700d580b5035100f0b0783c4c0014042e0701200d50320300300801d00a140c100364a085003059000f0040182c9290740c0400e8558000641e46000003205280740118041c162881094401a1090030b10a08981e400425a02d0494482d900c50303070307a030f682e8a407080507252081c9074107164058220f1000060501d03022000e0b00d60240100c00307005001c0e01200c0040d0403a403003004840002881051444100d0000c0308c203a4040a1180f0054000e10800c8008200e103d04103001d920280080420303400344940b9400159031400b68201c0031108141480340c005002507000030804d4911072416804410b1140c000d4ac1c02140000e4042d00d03a0301c0000c05402c10000c0340703001500c02c0040079000c12141c030301c1c1945003900c80d01a500640601c003010344189 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 593177967 1250 593176717 593176747
    0x8131a0c120a060f030809060c161706090703121107080705090c1206090606120f01080f0d02030904051e04050105010f051e0907020a140703060507080c0306040f1808 73
    0x40c9602c02250820b407060141076041d00308a4100c81c1d10100c126200c916000c00212640240b8022044500c01c1c25242c0041040307101085048590100308440c0880c500b28800341c035507004980e010b05a40c07186800f0400500d0708403c1c1e40b40c041e000d00d024854942c540350b210b410145c10380e200a002c0d5118080500080c07902e40d041c81e400c182464241403516985442000781e0342e07001040c9078850340065000807145e484030000c4031003074400c102500c0b0f06803500041400c20300c4000e00031805140705044002070091400030300190302d46078540095050401c1501044003a02d8010701000c0e08014003510441d00410400310070f030150307100d0700010615604055500ca0110704560025104521144440600304645107107107060010642d0001e41d641d41301c520503440d0246240d801071190802d1800d50103840340220380941a01d100340300610003600ca82008480440094840d0303d01042d080000c1121440e0603480502d800ca1410004210300a6000b440848104000c8081e500004005282c594100d080c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 593179217 1250 593177967 593177971
    0x901140105090420030c060c0604050c06121f050405090c0f0a0f060813080703080106120b0901150c120906140f0a050d0b030118030f0c0308131a0c12 66
    0x9440c0c4907114a00f9032640040b60801c070344500b080b10540e41c254011520207000503401d603000600901d44d1503017800481e80da5001e040b07074180c2c4d940c0521040742c0c5c4d961424004035400643c4038441d050042e1540c51010492060043d04205800740e804c0c000a0551941d00402c2c0c4a0030342003005c1e10b510b2007481c051100b00d01b141242c00b40714000c116000c2c03010805d0001d41400fa1840f41c64100e0076581c3d251715050350400040d801400c004004a00e03141010b510071205c905031112035907040347c4035003618040c2082d103048500160f80302103641c00501c018120440d4200c1001030034a40090800e07101e032900078212071002000800203204060900101c3d0704203d242c43c4101c0280d0409203401c6040001112038021664030701e040010008019001ca069504084401034000f4005c0116003a0803d8412025030200c00813000f05500008040906005080926080b90107032100302c0a60303a0003504049502401c80c08841002a9050100c000e41005682500c1481251035040e501d10407461019011000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 593180467 1250 593179217 593179219
    0x22020d0803150f0109150e030312160903050703031b020a06020f16080c150c0723060a020d080705070f050a060e07060c0f03141201030c0503010603171602090901140105 74
    0x104803d40e0300079036804a804011141e10803031480e110320207250216030002154250950601c00414090300340080611a0b0740603007482403458203003041c4460150340a20307007484098215000000c00b000800d02904500c079003042e010303040d0240f148080e4005001c00707103150030090050f400983d01848000381040a590141030081c4007207040741c40c0000280d030b19850203890701c1c000d1100666500d100a20442a00d601195000541d21800e0301c5582c48920840d4065000400610b15014840141405011a01103005076030103000d4941c00102c0a540341d98002c0c160b9420044208440700120380103881050441c1e200d00081c001c0c40d45941800b805441c0044820307001174210f0b400400501d41c104088035980d45c6d0001d00008014ac1500303098803910305080c622050882c0c0011b00038140c0001c1070b0010306030f900c6002038101c0181c459090600325400d80c00010101040703d0002c19a8074100070140c00100c3e0085410310b000d0030b5aa01054204109403801c0c51182e44070303c0c00941030782160105a000d800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 593181717 1250 593180467 593180479
    0x180501050f010c050c0f010c1212051308070201080601111006080c1807080601090f0b0d0c03060506070303090510090b04032601050909010e030a09140d020922020d080315 75
    0x8484d121181c03a109500b0056104001b84130698100e640100c014441d90368004240101011141c500a8040072040b0402118645000c0020b0060070125603121209900300c0c0700700b8149080760340151034508002c4d0003235042c0a240b00900510ba8410891201d140c860200e02151041ca494081c501d0854010400392094881e41c02c0074040c0c180c0c0650295100316140b030311134030b1504c0c1c0d500140c0710b0045a0308181c3c3e4101c3ca001d00400c4010310000101141f00c0e8a01080041388200d040c12000c4a200e40111139101104200b048040f0340303e03401c0072925038000d005440040d010310f5088000c85807044004c980a0f031681041005058112504c51030401c016079400e0040301c80381510100040b0140151481072140d0f0010401501d001d5220300700740c103402030440350342c0c1500007005000c1080031321649840a01c3d03c0c0b0001018104080000d42c0b141d800303803102e140358032034403a4498902076820161004503d80d50600000d691080c2c51058454000c2090550700c0c02c0c1885108404550036609a010300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 593182967 1250 593181717 593181737
    0x3051b2512050607120902060a03061508010b0415020c0d24020c060103030f05130b0919050a0b1e0310090f0c020a030305131a0f091b0907030204180501050f01 70
    0x40c80403504681c01368252425150384c0030a4414000108000c9201075082500804c00502d9203806620010076207030626001640307081e44c10401c4031418401d00524101c000e007030008000e0400742204030094503205c2d0041d42d00780120b120108496081180d0300303a801c01064403040e907100702c0c0700000348281e00d06e15030700750725084101000e199154010b04c8003d00304a14003c5190700c5074400c2c401c1d90320b000c01c4101e04046072992994580d0f00c640012500f01e02c140307454144000140d4103071444a04071900038040000075031500000101c1f0341c000c1080c42d160b44c0c0705004c4003d82100d101c00103511800031103420811075030400d02d1901c1114100c3d95500c0036140351204c086a039a4001521001146d4140f6020507503071b50742c0ba00e680e000c0c84101c0004291100310510307403806420240c800d501c2140c00700610540c81c0d9601610720355030501485414104d5035411a1406241882404668040011305000d860199561141044041481c1c015026155158010b00c020300c5d01c3d1052041e142024a4043c0c082 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 593184217 1250 593182967 593182973
    0x824090a05070e06060f1204210804020f030708030f0310090207081218100b04051018050717190f060f050d1109040510060608010b0703051b2512 64
    0x4100d50f010381011800e850000560503542c2000b11420580d0500d030490320307070001400080d000340d000d6030220b07a91804000020400c5207025405181800d07a680ca201564940d40c00340f101b0440ca07041c03050b4060064110108520000b04010140c0b102c125594581d40e103448010041801b04a4012000c1e00c4d004000c1031010689103000d480310243c0d4600b03124143e0300c4451000030345c02c900c41d10420050240d4103104240400c294044100c0410646082c84141d50300c1c040000c4843c41e9010301c0541e0304081d440c03580c203100b2f103601c0150b001500c0d060512410000c9190108403040444d41c0001d954521040103c42043d540221054440144801e101e490704051810950741041c1c000d09004000110710241480080590580c0000e800b070154449400e0030b0802540f901030750301c280000720b400d002c0b000540702c1c441e01c1314a04a44c4102c11150415080d59000c8031241d2140911440f4070b00340c9410400300c84c40612100207500804040d00021265100c0405c0c07003455164802130112040c034001c0d07808 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 593185467 1250 593184217 593184223
    0xf0c0102161104051e060a090c02030d14041a0405030705011e0f0b010e0d05010603120e030d0f05070b041a010b0a0f021b060708040f09020a030f0209130e070824090a05 74
    0x129102102c0c0c101d440755905004507c42d0951584003030311890418000d6444140c001c00203013070562200c0740c240304060140e110744445400a840081c40030084420800c000440c000420340c1161090381904d182188a8650502b03407001c6941c4200c1c51031510005424503080792040d4004158425800e020641a440005e0300000002c44941c0c0910780b10b000b031008000342075014030042d541c040c1c012a2811618100107002d2908405098043d00c1411a0301c800140610964406103176207070356440ca421455500d10744134034406041111048912b4803001e8802421100c002d000c0c020320406952204461403000780307200241d503010b109640110805240c1c0156001140d540c0540030380c0c44582ea000c55152a41191150394408220001e02c00e001007803841064005250701c079810707038003400307150320160040c0100d00ca1490313280c1d480480094841411a140c3d0400825400140140c91142e6500d80c000750400714510846015411001400c01460100c86550368000101400802c10b1000d0b581c0c420366 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 593186717 1250 593185467 593185501
    0x11040e0601030e0d0e0310110414090f07051305101107061419020c0909070f050a050f09071e020309180c0403080306040b120109050c01230f0c010216110405 69
    0x1048003840e540c400e030761410007d0168204600b401002a00951075405600e900140501d40080e80003003140012454158a01800b0741c06070b02d400000750700c841c2d109076401d07482002c8100100303040500c005a030f599201c2c2c1c1d07110001c040303454207560308030901c0e0380a04000507a00140c051000d0f030030184201c240040242d605086200084544c03007905200103030700d054000d01440340d001e0982d04c20041007800c0455200d044138002c0300400455511902017001e414150b008058011020071580c40c01890091901a0464510b00384070240c0680c68800d901081d60050030040036074000165503d160030010f00c600501e2500f12130201003410441703118105881503102c0a812104080041040e6659683c80100320510003400b010303c905141003060b010309802a000d682c81d010b4500103001c10350080260075846804503414880d0f04840c4050f4810b140c01c103240d44000d07107205126521014000344010600c1c21451a034800003d005882c1c15000c1c0c10300c480c034a600442c2410207105100c00340c0003440c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 593187967 1250 593186717 593186743
    0xa08030418060806010f0f06020d0e0f123a050a08040c080703060c080703092103061701140a11030103110f090411030705030a020f060f040911040e0601030e 69
    0x12008461411115000c2c05003030b00200b0741405035070000106050702e4900a002c0f5078000c60019803d982e52902030303882c1d0004019440c00b1844429a0350315074a80607200c030000e200b0003800c44002210b5000c24a1600c16a204010084006c01210644841800c418042d10b00a6070320751580800310350300014114001c42c1d041005004032280030404010780140c0c040041c042483c1110702c4581e4a04064024113400d442860105480c0e001080640d07100b4015103011a400c101c100c0030ba40e42c01c40704003c190203560406070426a5586000c40d03181c0c070540c041c1403000364010010505001d003408003802c0a0000e410144043e2a00d082403091071190800d890440380c0107526400528102400302e0045144a54196803103107080007008200210004180c0203402c0070f8045504243e151014103548040702a0083d6000c52401118601d038a0504010086091100300103030030540e03183d1841060315404030080c0c04404c40494280a200083d21886900c03400034078040c44000b10084099841f01c1c2c0105801e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 593189217 1250 593187967 593187989
    0x303030e150a0b0a0501020d140309070b0d0c0f091a0702010c140601170312010b0a0e03070603050136052e0305120c120c120703050a0e0a080304 64
    0x4144004050148041401e041540d103290392501855140080c07150030945403107040e5401c0f0214581d480040c070040350291503259210407250016081c801500f00804010300d6109414011880301d81400c01741400900301a80401c241c0a02800a010b0040c0c1031000d00c01c001c921075042042942d9410406610041542074a94400c05400104c1d401c2c4156031010b00100300741507e07441103460001d5040d04a40d40c40800c220110304200c0044d803a0b201d040d036040512945040140710001100d401030520b0441800d040c0709203036401001c2410461150300c8600441e503500010800074504031000c804075080c11002c14000031308020001c0d10ac4010070044130400e56960001611021483d481c90300000f200b50750500801d4102c0700541d940e484d00d00003100e40d4002e19082c1c0041e54680780944080c4820003016090711214000081d0482d080345842d107009205001c03905401da800b050080010900950711560b59400784040644908040040140138004078441040311010101c140e4043d01d24000322 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 593190467 1250 593189217 593189231
    0xc090b03062409071805010221090d020a24020705010c1b030b010906031a1003020d0305040911030f090c060d0c05041701060305060c09030a0f021207060306060e0306060307030303 79
    0x304419845150b818143c109000034113026940d500050291018001640303044203840d21103004a86648441080f07010303240d11001d02d1000f0748064000352000c5003010300580380740c50460700084d54030109a030042814010301a9110f5000c04641004c00f98518240010301100d8a000002131005032101800313003400029515a00900f04911235650017190032690022855840e540c49400401c154401161010603c01541c440c194036900c49a104144414422030060714513020300c620b80950500480402100308000f154526030781c030540c40c0301e00380000c0306c1e5202c0ca0140d00640003000050490445640104001109540c0c0e030811a1011103122001150010030325006441c0c0c1c1c06541c00908840d86803102a400a83e8150b1140003168092811070b070158440d2100400248111082c1c650990045524840850003640a0900b21072000d082d0000540e86140c00c141030450541050f00000d80b540c10070040d05500c0800090171a404a000e0b00d0303d82882ca0009607218101c0c44010241030716554 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 593191717 1250 593190467 593190511
    0x80c0301270603060c0323150319080a091d07030b0301200c120717160b0403020f0610080601140a15020a021801030b190209030106060c0c090b0306 65
    0x415816560408072003840310075180d03d450070160500c40c01c0000024a80485a59152030a101494001c5401640d01515498210b464102850707030503007242d00340c80b0f0040d00d2119140d40f80344010070329005100b001d444220142c00140701e0310b407513400a000b182403010f5155441d461481d04981103c00e03418000381c0b892801002c60301400c1c2031490303510754207030301441c45d54584504001441005034840c01c5e59640c900c5800c07448014051840040c10004182141d80c110000107001440ca202803e11181449041651396112140f41147c0441c010303042160607000d51441041a5608501031050309407025040c5200d203940da04051142c6e050044007941040d01c140c454804110142842c00301d81c0c0103074042e1600280d42d54000440c22401500c80c0b04240781c4d00303040100e40c03d059941c0400b010b062600d0307016980011908123506086507542c200141d100c5603070244201c02c001c0040c0c0c1c4035280758481d1401c0c0203c0002a61340000c4200381040218005941c01098581c1e000c4100c00504102c100565 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 593192967 1250 593191717 593191769
    0x609052211060c0f0607030c02150703150311040b031b040b060d02070b10060903030813032c1f14070311010f09140f0304060c0212060a1b080c0301 65
    0x201e5140d0800e20004112011960100328502015250303000c40341c2c5d545680d002102154030380e0030150016000b403003080e01e03440580554150056124a00402c0007466100301a0912080d40d1040724034a03440b211400315424207001b0018450422000b80010040c010850500c54460300c54061007145e0f501c055020a64840e030a41e86c58800c270a00440d00c558461420180b48001681c0c95112012000d0000400c03603c666000b9041c0c99159a40f11001e03265090301990b0840350410481c1480701181e0038120740f0907500348a00041c1540414001ca400741c036024811030019500d0308000503029026042000c64001d40882010380a030b890060b50f4500c282400c0303410350b410145a524650034420b0b190b510349682e0700822202c90244422030103003900c5d20060356550600054616142d0800d01c41040b03600c4c001d941040001780003074110f100024070812120706128044900342d40c525a1001d400c1444424460b000710780040c04d040001042c20000300031010b60005128540254090b4820314000c04008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 593194217 1250 593192967 593192993
    0xf062a1b0822031416080a1a09011d061614030f0405030c1006050a050904050d180504022106060708030a1505120a05210d020901020c030d030f06090522 67
    0x8020400d40c950120080680c6038080c0305a502c401721180071021520340b10104441201c40d50003082040c04004003c408503123800014503102d41c40d560f4520a49a500740c0780320b405074507001180038007194a0440f001a03905c0039034032006020850006107442481b1000340440f0b4001c200c02010103811795541c07504914500c0748641c100424041d1021001000d41c0303940080047d14400c072030300d0726100c1d03c403002d225510030101e4025009910014044200a0140b080101001d0b1007030781048440e9202c901040699105101c005c807249903400c045103004031184142d1340c105804980c031604d40285c58480701d100d800040d11f00c41d0f1081da40c840d030340b0340103022520071002003001030314041e1420303542140c842d01c804e0b002400399400c1c01000b40c181750b00d40810410000403c1101d038418101145070090360000d401600046055103c4c140400b8a2075130100221001c6015942c0c000c10100030400201c1c1c16601075500481000d4100424050b080d14090025035500302c0210864280c08102d0401c40a0b0005c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 593195467 1250 593194217 593194223
    0xc02091012060605040b10020c0108150a03080306100504060c060b132310051804140304180b010509060322080a050a09210f062a1b082203 61
    0x41c5941400400806411040407103400f158100060310b902e01c14820302c0d51395080d20380c0058215014010381c07503018000b035039082210201e540c111852000c001c40d011507459042650445004010045c0074a00302c420724944051394034109007850b282600c0640072140c1d008000302800e4a40318204442e46900f2103014403c4000c5805110940c903810a9040d80b8400b16413106820884100090308003001040140407264042c05041d844910a600d140d020b080c0a442220510840041c40b50b810b80100050320280c442c2462088003c000c08c1c1d860003c454075001c1d89070603c001444445850341d20f031015a03178004911034030340c9240c581080c407a02c0d035500c0000c1c000f0180c00000c50003076250f681c010083d01e02103030340e070700c1d0300c01455281c502c030b9400c4046000015030310110b103150410004000040d690a06445130b040071030032010345d2844081c00075000c0720400224522800004006501c51010316000340c501341d5400c150a02d5841d5203000d8452039038003040c45040c9240f20301e02d03100060502c800a5030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 593196717 1250 593195467 593195489
    0x50a120f0b1b0a0c060b01030501050604090c05090a06181e0b0c1009080a030b06030610030b032b3b030f01020d0b091e13140d030606020f0d0c020910 66
    0x403e210280c20200c3c000c2d4165043c07441d140300303403005500a100f0b142c140d600c0200311a050914113000c407000381000d080301c5030800c9014841c291054541840307081c007802a9403108207916070f11307059104203448598012102804000c00708070118502c1c440c0c0d0000d172441480700d90390700c40c40013410358a060991201c081c10b01e8130348185030041c480084064542800f00b50b405024410044041007180d00064441941c049454803024240a0080d8032040d0030030805015a900130720040c22850030b070411b5005030a8080d00203450000c040d80e10507540d00d03d08600d14181d1024030805003841100d1180c4130a800c0395204050300014145da820420b40d424401a03600956543ca0284840c00182c040900042d000c1c184120205044600b02d207080b40201038929810003c03980c07143c80d0180040c0d090142a11040b205c1c1c8501c882e615401e00104049004a44001c50060328200009152490b4810103940344d4010b441b0300f12340c1c0d903880b0400280c0240c040b070b05292140c1b50041a894441c2c46607018925102c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 593197967 1250 593196717 593196727
    0x70804033501080a050309060d090212010608100e2d0304060926121309050f0411010f051e190f020c0102030f03010512010f1104050a120f0b1b 63
    0x4801180d403003058940303601c1c1142507076603c0d61050383e10300107030314001c101da08144128485800c3c54005003415a04c40c910109011007150085144c41c0090044030060b651074040501100008202030084244000010425405001000d580b0b0b2040c0509a0301002030064240c2c070004640040942e003200e6010590f41c0d2281e8403e005001086944034603004003c10050382c8542c408030f0803400c0c5c0200d100ca405802410109040c2100c030341c6c003145081c00d1103c003442c408201c01c000d40c440c851042011701e949420318103050070600ca214010b803000e541084510030110341c621f81c0c000c0550b01c824003201d080c81c0c0300146d0008071030440e000d202000e14942c2211242c8000603070307001c51501640031464003030359940c08201004984078072454100b11143c140400c010480b034204200e6400301c80d407401c000000d40140320466070068400c0e19151110124002c2070034800c80c60143c000100818662641c0c902c0060141d455900c00041140c0103001c08241c0f20020701c00c6640e410710f800030002c0c0380c0c1000342d4034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 593199217 1250 593197967 593198027
    0xf0a030c020c0a06032a0e100c0f0609030806040e03220e0709061805030d110307060510171f0507090803030106031a190302061e040803280807080403 66
    0x100402003980c80e1031031596050b402e41c40b9040f081050008811f980c1d12030f40c01800c0c0c01b849200940c41e00f5000c1001001f104101c08104850222110315100c0d1401140c0c01e0341c01d050043c50403c0c0500554801c0340b810b510500040d0001045034400c0030304480c044510103410105014140076903101301100c6211100b00440c4580c1b100c0300c2015500191195600090f14a4160350100d6190240704d03007551108070204a080d0064102d0781c220701882c0d045134900111940c4110968006503038201090b100b0003400e20140c02e4015081e8880460f0348000c03c481e28440381140000460600d4508045558402280c0c0261043d0341740f43c09011a0340480ba601e503503d01006006282000306244031030a050909007041c40d15084900c903642c003020311070500f00c0c10f50302044032a500000103610708050784d007940091400c031a80504010704104c009561203c072541a0b0031500d603c01ca0f50940841510265244669000403400e600150b0358900034900ea0744501e02034800446181c1a48035240715103c02d9514 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 593200467 1250 593199217 593199221
    0x204090e030a0206072a0606080d030c0306090c14090f0a03110103141302120322090e060606120403120504080c1b1e151209070b0f0a030c020c0a0603 66
    0x2942d065801c480c07103035840303000481388040d201e4425060480350702030042030140b40f4800f1403503141c000c500c0001e18607951400382e89018841c04200f00401e454024140441d43c061040c10010300000c1c40c00d21451081003001048114210440d48102d400811306a00f071740c850301c24150754110003401c0c85408507101d003044c10f114003030304940d280081d08143c1c0302580004400c0459001d030100d030181240700d8a1035402c0007021050702210003400d210038451826080c50b92210000301e50b001c0c521412205050210000c2035400c4182a00c1d819071081c4203000a58075100c044a8040e948644085110348031858110b405907000009240024101410301041c4400600100f85051005048038010040c1020380302010a42c52011540a10040b00d0440340300e01101c0c0b0032030303c0a40280880c08000100c0030a1600b03803c50b03103007101401e010300c08028142100700302d080c0c068440910100d051056924040c0400c1c0300318800d10040580795000044081d008001902800100900101d1116202d110042c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 593201717 1250 593200467 593200477
    0x60e0c040e090c0a0509130c1403060a0606020307200925020c060f1608040305071d0c271509010e0f090105010e12060f100501050a021f0204090e03 65
    0x844480c070040461401034001079042580c45000d06a002080d180174104040d541d402041009484130402c1e074140040c401c400d03c007001e08540703420030040189480c00c0c90f281040090940a5492400600707119042e0000140d50100b40e000c5001e080b080451300b600b070035402c0780e04d540c250405441402c6c4402c1000c803914103010203148007251000c44800c4107040b642d4224441000342c02c03407404c100441c455034201c4002d003041c3c49000b41c00b81c003101c21a07552512a5010703034402d8550f5041108180300c00701c0703110075080220185506001450800180e011510f115101200410291030385215081c0f0254445050001000500d010484060541045840d80c003241250340050b44a150209141c03070043c2c642c1041a07c0a03022a41c1a0b00702001980c01c110706001d1240d10919108042d2000501007142c6441201a00c1107201581001c111000c410700703603038101c44c1c1804001d0110b44403540d8001480360384000b00c02003402290500d030205d00c00034401e6410090603141072040308000d490000000b00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 593202967 1250 593201717 593201729
    0x60712020120070209191d03070303051608060405310219030b01180b060d02040e100e070e280f09050c07060c0201020f03040f0b01060f02030a050c01060e0c04 70
    0x40b500841003141100c0e4843e0300c2000b58800440408212140340c0e14614003c0c000118a000078540c2e103800121049a20310711041d10113078030000d420800c06a0500400c0c0d00b00c40c40000401c40302004001c043c185140042c07181d8007450350b07040007510103400030001080e040c10a6940981c00801a910220581c082c2082603016440b0720b18840e0520018038069011607403c400e2105469007803013001c9415a07103140b10a210b854980126a070b190b03a80c2c4004010110200c00016039951070a020448046402020301400c807031055001c020561503d1407080c0e001855103414010000102c000680c541780401440142045512200d031002d101d4924903015920000d06880c0141d0395204140f00799403048400c1c0190700014450f56000a1594010b407041040a00026080003503050101c50190003c0f901599401120500c1c0002c1c8030207080c80354090203c61404004c0503103800c0300031b5070780c0c40b40721482c0040040015800240b1b41d4298041e0002d4211101d81d411181094090702005403ca8003a034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 593204217 1250 593202967 593203001
    0x90106051b061021170d1401030b07050904061802040806010e07050703120b0d12120b0604051207050301090602041703090a060507080c070608071103070b0609060607120201 76
    0x34510250000d02d9521442c0b400c0300c1e4881050502120103443c541c3e000034134880c2480e20154500040900090041050668800302c0d100d551400c494019510504034905000624000502c040380b4800c44041d4001d8032410559a0b8240c444086002020b095006058061038180c406564a0440d0000d0017228501c5045540381d988912041c803075128181e900001103981005244c0001e40660070080300e0620305000000d0030010480418200c841070b030f81c211074582c440d507500c00005c1d41084000c100d40e181100308104e0f524421002c01d40500c180c0c094184034204180c204084c1c08020021000035010280091009400514011029400c54010141082c440c0c1c194548a50300c000259070714154000c14101015250a00039101b560200400f540c21450400c00c511080c241008404020202d83e69010000c0c9401f6100400741c0c03a145981c007007a07800030020b01c0c011400c44003404d5000407017200c556661340c585a002800e40d1060078001442c40d181d00c100280060380642c00301524003104551 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 593205467 1250 593204217 593204257
    0xe0c1003050108030706091506090c080c091509120f0c0f01050309030d020306040f09120201060614030a0e15010e0415141501212324060909010605 65
    0x41034003591000d00520f910782d442400440d01107400398201410f9980a030389041c0f80510304a030308205841c019001a514203880f400c0501d40164003842c0b05034802c2c4004100303418050040300154040844d5901d8041c04440454960042da852024624968104004030340b02e000180ca0501c0d184c0015015840c400c5c5001c0300c1039201c1d940103070300302c81c80341d006203001d0740c41c001c005a085c60094001611841c0c00680d1003041c42008083e51040f60b100b40d0091450101217100b0b40402420350b00f960f0441d0b81003080b6417035010341e81154041035a03001680c0d5075001c034103032840903035443c908549075003819507540840b0000608090ba800b8090300a40c021000030150025124929082c0c0320b60384000146000105c000440d400030050000e103107080145011203034025080302c010000d0710140040c0342940d030359060080030040313900c5450f10202d03a1169512150b1426003207450300d0b081410700500c60199882d010864640e2004126640107800502d11201c82d6103881009040b0b8103c00d14440300105a458 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 593206717 1250 593205467 593205499
    0x501050904021305070c120507110a050a090504050a0c120308010e1006030c0c050717190809090c07060c0806030606041415010309061d1504020a0b0c0a060e0c 70
    0x2140d8801d035006040d100e8020000b80c1e04030000e2030010144801c00100040440000301c51281100803004569606520354019043c544c88042101e03044900c646500041085144c403000f504200311441c01c080003070561386600b8000e080c040120001491221058000300d0103100c0002e814000c07900a503101c040c0c83e030701c0c0c0010307030802c040c20f4030186591140c400c0108481c40c401c0e049a00e0f00030b850301e041000c21104ea60307002e20701640c1c1e030846003411850103a07a071105234041210031101200c0381952000070015444103030341d51045410b194002e4003450009400308078032100f11040c1650280c810050b140300c50000030703d0180d041c2c0b8814428003400300800c07014078090003420152210814146426281c8186400c0b0f0003204224440c185030310340707440b240440d400e88140e0032958000c86c880c000100009041d00d08001ea05e45448030b40b55420010702015803544c1810a090b20650004250b0701d00049121500d0403020f403100800e07650500442504051022418003080070701070381e5800075000201 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 593207967 1250 593206717 593206729
    0xc031d1c080c010f2f0304080904020d0c050406302c030a080a0e060105060c010902030327010f120b0409050d020a110609060f1809010b03160e060d0f0222030501050105 74
    0x42907020105c84144045000306140000070000d842c4018001071404d40354054800c10354148011080c04150045010042581c20000000781590100e8a401c0406c50305000d42c004001c00102c1d4044071981d41c062040e103585c00380c500c0c42c800e0b0b101d1100428001994585190b4940c03280d80b020307000461b580e0210755500e43d0b60183c0340b01c0204540107808a682404180043c3c0c1c0c102021071070840d900c0702903070005620240003c0c2419401910710328000750385c902c407a0501d881900e030798604002807049030f50380c2c450f07000d014414940110326001c036008030444005805890480806010b5000c1d0148245219070006581a1032503ca078140560f0380f103040701000664016110b81035040a0100990800414940c001b0400c0300c080810f03030b81c2d80b111060003082c1143c0c426080344507115800804c0c00407003d107000f1808800d046500e41250314070720b400085000d500610780c61001b00b58035107001d1854214983c06a81842407500501d071101440701011600d2100d1a00c001d40f0b055191000205681c1488 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 593209217 1250 593207967 593208041
    0x1170108071e121b09020705010e011a0904030c0c03150506090c04120b061503240301090c0302061303141b0303031e09030909070c031d1c080c010f 65
    0x814002c00010400f501c80c130032134110400401e002c00500b003030003260071011803003d01241030241c1c00008840c6684a910740c2101c44401e42c0d810359545021015aa0b1ba580340c000a81c481e50600d400c5090b100a0300d001c010810458000034100405884040851a00d5a000501c103010850355a0010303241c0521148091085000d010a136252002141001c0b40464042e01c3d08003501911040700040c5010b002c140a0f003058840344861040c8180d0360440c420b8a05003080c003000214001c120204859540c41115034861000030301483c408038283d00140429119035000b940c01154010344620034440050710b602a98020324400ba0010b0b03140303001070800000341c0388154400192441c40030001401c0110500000b003003107001e4881008115103544440748040c0c094112500c4408030120b1516000e09081c0044241d070301c104802c070003c1c00196843c036500450403245003046224200640c01c000025101c1e8030540055503003811000d40000d80c403503100c42050fa4840c0d04200d1461080e02d10940c01000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 593210467 1250 593209217 593209229
    0x9180601020715050c030703020102090307061706010e0105190e121b0d080f0f09090610020d08190603050705030d110718060e04060f0c030204050108041101170108071e 74
    0x9080c091082600004142c4880c3c6030904104d410855840c40b424516407080070f040300148d4001c950800c59080c100140d07000380c0642d00740b2201c80c2c5000c280564103820300802040c100076040e68880d8081e40140704031284d0304050fa1051400c50b00f148805000c81a10806103405001c078120a0300d010440030400000c110011600e081c1c8501800c010440c0003068418140d481c0c5004003d02e650390000305c1c0c01482c1041c1c0385213425864140300380821140c003a00400050085004010150300d80b94046140914904c0c1c82c106500142c42d00d05010310020b040312507000529240c90404014408006545001c0b1401102200e120010510f0110b80700114140c40d03280070742c050074040c00600e92203a01d8844440d800000001c24903944d041504120f00180e9040d00d00381e41e03603081444001c6480c024442d5201240c1002e41c9000d00c1c180000b84a008000c201034685480030440b20385981c0304419a48082c401c05500b030616503100e04060752103003030911560303960f8160006103071801c2c01d09180800480700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 593211717 1250 593210467 593210473
    0xc060f050315060909150901060c05190c09020c070311041b0804024b1818010204060203280c03051b060907030203060c13030f051c050918060102 64
    0x2510b12410035600042044594022014042400103446104850b4803e842803d1640d081030811801c0c00001072040c0c01402c104000751040d0404200005403c031200c250094080341c80c0040c03818448500c0310b013a0458000369000040941c0240300000d1141c007528041c0d990b00228026940c2000304a8074282d4180703c200040b80541484907000f40031655000c8d0014044517400301015408806200320040680000721120001c42162901c400001409020f0740e80400030111610000810f018010311004c2020300010001071440c44a142128407038040d104000d54440f511044069200d401195109005030500e04c90303c0300151080e128222400c9075600c603500c0e442141c0d00c00300c40031351100c46c0c0c191204090807150340e03240c03000300103d81c410082d000180c4416415441050b0034040c02810800010000b402070942c0548241d000f00d0440b0751041450034a4550362a00d00d040c4151080903414040300c28114024054200008090a0318215482c02001d003807041e00b001c24500c1900c0850040e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 593212967 1250 593211717 593211721
    0x90106151112090a21051c120c090b0708120f1e01060509040e0a02030703030809010e0c0f010e12010606050d0b0301020c060a1802060706092132070507030c060f0503 73
    0x1d05e0342c1044d03100010016207142c0d0103002c0b91711198644070f944e4071010618040c994031192405d5001500c03800e522482501841904000940200040004d00481c1070140c0d00046400801c5001012075002001000d1030080c42c0ca84400a03454030201216004c5084c40c201d80600340721000c44101905807545a1102070400c0000814040106507041e52200c0b82d2080c0c1103078601594007001382c480150f01c41e079640c8030a450120910742c00c0d01c5415200754000d42c00700e403414510f03507958242c00961890a01c0c20f030803c04e00850001e0f00c42600c01481e8034280d4640400419055031080050516203c0960148003091000301451b08030300c64a0880155600900c011550b400c81903048800700042c90001a8400d0074290000769071544051411540c0c03643d100b10000402c2407030072468030505415190300d1000c1c0d05825001d0450151440e044980c00230004101d4015013507080389010280c0244050b035114002032500981d250380c1030206494290f407000780007680311300c9682010785200345075580c903040d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 593214217 1250 593212967 593212979
    0xf06120b19020c030d1b0e030c0d0c0b030a020306040c110d0c1b060c0c050901030c03031413030f02180c09041e110d0e120a08090106151112090a 64
    0x1c41115103500250036001c03c0950f02240003000030305103a0244100004400060400d40c00c84240d407a143d1009201c100c0b07444501640e0049200c01c03000302c00f560f8190032841079141405040c0c0702d50b0002d8160020210501030429281e80c0618840c0505650800610401044c242c40c03020400c0107158896000036581e20100b40720710021130350140714644604400b000805201d142c042903401c060001000b2100170400c1c003400614050083c44d00341d41007000d0354159100c0b86065600b07400058140840c1c071030450000404401119100140e07641300c07240c001d40302d20300352a04000e00401a40308001060b0318001c1c2c802c120a0700e90080e0565000c05140c00001c4050001601d10b41c0481480010828200d1000a52034040c50500416215031a40e40d07080c035841d880e003210140810b0a41a6000510002c0c0040c0100212660240385041498a80e0740d101869809044160004e8581d4108010300c1d41c441a0011700019540f80302000b03644840c401c0c103100700030300c0c0500305110340c1c4020403d40401c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 593215467 1250 593214217 593214241
    0x2060f01050d05010603060e0c04050a020f0a1b20120114160201090602040b0304050d02010504020303090d02030a0510020a090501021f0b13090503070c080d0f0f0219060f06120b 78
    0x1d03c1240042040e0f0394030f417100401c444402c0c40004440e0403001c0c030501149070501c112a80100100c2c0110309202c418820008a8090b662102042c0000740c00304a21004d070076103280c100e865118005c00845c40c011801111607030100d00741e050160074241142c10f03c248041c00740307540010a0346541301c09581c440e00344035600300e034802000c0c06655840c0c602c0c0010031a18002000a4071025602075035030f0600e440d01510302304080b4001011640340a0074000149d4011044400301982250000c8400c001170000070304240d01c0a4000301580300303c000034481c0c0520f0780c0190144980540300e882d5003903902c0d001680c44035401803806d00c50b8501013800a6040c41168855101030740d0280015801020524044003190121101030380c140d0b00111301041040300301c6a030800601205030203840c10b100c03541c0014103480804440c031003d00c1003000e08000554420401c4201d281980303060502e41c0c14031810b1070001400320355001c5104a05140c00415482c045940c8910b038186d20026002a656410b9100d01c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 593216717 1250 593215467 593215489
    0x1209180203040f08130b040e04020102120a09050f060d020c0c10020109020102101d1f230f28140108070501021c020c0a08030a0306091808031302030303042102060f0105 74
    0x84509441e94006c511540900007903c0640300e0040c2c2e9214608080c00003925018104001c00005001040804400c5500816040c125402568003840d41596400003a0481c010040c0c203816451021030041c3e400e400004403000100d07401e6544d440150700c10342049081c2c9251404c01390250b402458648a81c2e49254030075546490810340e200520b65500c140c840c182503544030303096115901403a402c2d001020310302c100c141f4010280346851080d0301c013038121101d60400070111626007151100144800800c800b40705ca81a110300d5152490086d02c01c0b03010700400d81d002c6020480d40141001180e0305100040b00ca00380e40c0140c0050503240b00170642081c04240a200e076008500648210708803c4e141d400441000d801c0f0701d40919140c1c241080c004040703400030342c000e620050070300da10303040e10a80400d4038000241d00404807030b90f25900d543c201003140d00815070082d0140300c0007080000788034448010100e00020460000000900004e04a039950000e5542a5020b00c21100400c070134941800303d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 593217967 1250 593216717 593216737
    0x1150e090a03140910020a0b0c0a1d040e030301170601091a090907050a1706070207031e06150f1a13050d0f060c020601060207062303040f1209180203040f08 69
    0xd49440c3e80b0b900801c5d00441c01c52000b101580c4401100400c01060030300b019400741801007454200444400300604a60450050000380700350001c2d0b410650b291500007402684903402101d80d203580d00c40300098200d40351803080b42d05005030303000840c10340e009004101d1614065003a00c2c0c03d480c403440400c07000c1103010305101100e1151960005241d1030328840342e4010580500c00300441000c0d115414140b01c0003c00078011500000340500c0040d00c40ca00c616510b881c01e01c1900da004c100f13850076070000c10304c502c46900c403240000800601d8180c50b42e05801582e42030f80800c2509681c03c1e05280f000e0003080c4110405d03080f400e40501c894204000340c0c8100501560b1a45051640c0751114800c4804031030003500160400e0005201941d01005102c0017000280b03040e03800604d00142e00c02030000180200315907400700201040c2840001e118140c44a07030054011880e041c06408050a4030340305102d84403640c005030010010390750461096900c07854105150480d0f520705030780d445189900501c069 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 593219217 1250 593217967 593218007
    0x3020303030f061206011215140c0a0203090411090a06051e070c050d1208160c1104110a0201060f0504051501200f0105040b010f031e0503070b0901150e090a03 70
    0x14401e41d0f0304c00c020309802001c80101d00b401291035803c003e1000c400e28021103124138101664081c810002d40b20300c13540704180b103d104d5100c4041031422070451180381e100c42e50041c2400e0b4a503407408140d030020103c031002100c01d440f403d40d0700c1e84207603202d02416115a500b41211580c020b080200b0400401400e4822040c80400546503000200f08246800050b160f0140780801c1440d4590800035840d089891034641010a2045d1a8001c001140c4030000070221781210200c13030031948581d081044039048020b08680ca80000b000024001c1c65984940210300c800448000703401c0c01c01d8410240100c0e40030600e00025a8a2070040d112241c0404840c04001a40116200021000c1c000d00003d4000e03000081003038145070510317942840040c0c110958001c8807500400c002064640d001d5940780c0c03220790034035000d1550300741a411802003001c081c2040340000100b240548040d0b103c034201e400d01500c0d810780591508000c212241c0221911026035101c12003d00100b03000ea0011440000e00c2800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 593220467 1250 593219217 593219239
    0x103061107060c08060f010207081209030a0f1401061a072603090c01020f0c0d021002070e0a02030901050a0b06180402130b0901110102030f010b03130614090705040603020303030f06 80
    0x16150480307000402d0580010304c05014400b15240c00c0d0041010750b14248014145903041132103040e103d2600c000c0c1208890344c0068100714948050203d080c140b50842074098400589003448117107118038070200f0038903502e0810040382d115800c07400303444290b406d0881603050007030720f544240c1c1200000c00340360301c03120003903140c4100c40390960000c0d8801c0f503840c00a048074400301d80001e4a410908010b050241e000491182e005441e504c003414022501201d5100c1034002e00f501c140c0c1000403e40120118440070030404c5000c4d6019002940600031f100000c20503541d409904e04120303400300d0307969030b8842010000310b504855518502184c0c00001000185024011450b403000403283e41e114642e985400701d001a10366810081100c04404c86000070351a5103410b51116035800c0050195240d4540007001060100c90220030466056600a000b041481c2030304041090300002100d8021640c1715911300402c0c20b04140c0120b03001c6035406401107082da01e620380c0e98548500010625034219001c111 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 593221717 1250 593220467 593220473
    0x1020c12090a0b090d0803070504080a050604111c0b06010e061b0606220207110909010501030c060f020606040f0e120d1a10030b04020c070305030d060602150103061107 74
    0x14100362480310310060352401e007070042c40740008441c0e01ca0882c180042c0480551030311600e407510196030344a15640e540342e0b140c1c2001e07070381c03802160080d41700da214110728a810030000054142c0210b01a002101c0840030380c00c10031600094241c018500ca02100542e000059a414245900700d041410103411070a0014013140e070035002021800104003000050421259013440301072342007a07007514240c0403240007044c60f04044804c12040100b8a50008403442401481c0d90386000c41c1030003c105546501342075951501a00c802e00091307038109900f05000816500443e640101100c1c95000b401040d503031481003000801c0d44000802107a600e501180b6000041440701804443c42c40f588191200545500c913030480b03d822802046031201c040c200b2480d40d60707621140c0b40c2c4015901e80420380f0541e910124002e4015130003c80028441d811020042190100140c8201074030b580b4100300c0360f641c5503000ca9483e02d080f9684485d1070034150040c008260503801c404c6a540c00b51812514064244d0707 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 593222967 1250 593221717 593221723
    0x3120e0901121208090c151315050715090215070201020f0136020d0507170c0f0907030b03061302120c0d020d030306080303100306150302100c0c1206021902150103020d0501020c 78
    0x940e80b1f0111040c0020108104041c0d031444d00041c1c1342208042500d100b915034017506a1059807005801c4005245c403030001d01d0403036000f8880d42c6602802002131800800051b117865000108203d003d40155031506004440c1445041451040280090000c5220500d546918003c10211803c40744031140002c0c0036031180c20300841624411001441102d24103441e80010b9800b4000484191f003100100f5881e95072000402e5074002c1c0102d8001826499820741680180001544581c05008060030001180808126242da0307a0099803038500e08250328404540324100e8401e280e50148900030500b026007040d00c11400e0052103800c5c00034110b030320b8681d020720316041160b000400c194a204240104415801080c003504149078019088500b1360f8005200c503400348102c64208102d40c2104410311550303045c4c40c001450400e4850001c40c0c210706080c0b0281d40056003502c40b006504440c04800e5200290b00c000c009801f1200382d17000d90031907007003105030f4180c4841540c02e90340912804080716028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 593224217 1250 593222967 593222989
    0xb0906040c0e060c0f030a080603121315020307051b0f0406050901060309051005010f060906110705310c110a11040207032616090b0405040f0603120e0901121208090c 73
    0x652200034081c64604101403411150f255051a00000ce0114000002210f408042503480303c1c04141402c4070460012851805500c1c4090f10314450b01c0d0b0540a0100d5a182c4005008000c1d107485403181c50170700c2800290745071485056006005840100a041c0c800d920000d030140c0705100350380211003d0640242560001e80140b920200d80e01800c108054010380e100c0c00500903030604241c6c00d1400020191121711a03c01d4600442140c1c0c160b000071000110a06d00d1169250110340c2c00040980c0080010288050010b01046054400c410b08200c0040c001042a0340542c1d10104952140c0c10721000c1c0d0030102c0214180700d8045071542402d54444c4242c0c40854040c4104101c5241119000d00c3d2010118801c41c01d011020000340451043ca0040300c0c00d0303400a40d800b0403410101d030064401480241e2010780b140030803402206071154041d040440603079084a010317050366240c207005d4410081ca1800208558280403000300401d004411a41c0d001c18010241d031071a00e00c58002c80d4150500c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 593225467 1250 593224217 593224237
    0x50c040b03011103091c03050f070c03090f0306020d06080c0a0b0d1103010305011e05060a030b0402030709020f190e0d0f0510112107141b030d0b0906040c0e060c0f03 73
    0x1084001c4d01b4000d481c03080100c00d50703d5502c0c045c0828200303601240101d00004c1e003c6e80030003d1122107603040c1030041c071200d401081c405078440e010b9175807800c00400a401401c400d4281a04104002400c0040090440c401000090149a4151030214400c4256002c46180e047c0d068444580701040b00445010f9802180a00c2c00840c040c142d001c0e013603000380f1300c1c400281c080c0b074a400140b14203078890f2942001982d42c40f41c01c007640d5458074000a840c10004d940042d0140d400090b01015004426024011021548510a2001100705001d440c0c02d07905150242d0041c44621428000c00c0205111440d02801081a039040e034209010103030942e00d4070315402c5003003040052000000520300071250b92507600c0304c82070a00d5041800c001000c51014000780c2001c0080820f5195420222044140c0a01581c0c021240d81c1c0e503845241301d004d8880e40c4d03209441094032400190881c1054020312801501e29a42e84000800318020020386801082040f841448ac58030760032640c840400c01031100c00d030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 593226717 1250 593225467 593225473
    0x51209010e121903090c050120030d1b020105010308121812131d0106050c0f15191e020a090e010b0409060f0e06100c0b1f12050c040b0301110309 64
    0x520701400c64049084603c0f0b201050f140000c503d01064216803450140d0340309280c00c03030280c4000692518030382144001c802080c0000605402e0410090b80f00c0684c104d5210001d052511807001d0a82c200d031000d01c4040c08483c010801c0c0341019400b1003415a1001060300103843c1c040b03080d0703d0140f030300e40c0d910700ca4010008001000302d9401038110544004000004100c010100322400354800503206101d18400e00602080071445551705001d0180c1c401c40400440b40c040c2810400c0c0004040b06449036000b840d00c0340300c60b013800700140c003d1101d400050801c0c1340d00582180c0d1039100030b41c4192052020010881800704030004400303140380c000c0039582c0030180c4543c104480c0c00210b41507580008052561402c040100e903201c2d2004c2079000c1011984140c400c40c6109050700d45240e0450010000c18165080103226020182d40c0d0700321040454404440f180c0301e40104e0501d100d40c0d280541186c1c0800c83c9402c3d0303407405401600072001c000d0004942850f510302d60709801d8006a9500f4402e030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 593227967 1250 593226717 593226727
    0x30504150510060e04020a0504030f06111821150c0c0706030e1b0a061103040902120f0601091d0a060e240a0b03010b0c010e030a051810051209010e12 66
    0xfa074880c0304555030400c112000c528120002802500500c654400104070b82c40f002380c0d00d0306021007a40720b8448101c44c001482c0e80d070b204141e012458264465681c502c0b40700b021014106503a201c4080a41c8616030000800070034030f0380c8a5001036000005c0c5400e10000b010031001500c084144460f0004180c16100820301c0c1690130100e45c24180500c00304804011245410386c01035607891360100031244241440328109400342503503030451251390003120401d0b0000440d03503110988020098070910400901e00d5942d00c800c00111020034a0340314100310410005c4484030145418500c0e65049140510002020365503a0004401b2000c11156000c090b410810035224884e4a82081c03c44100e0848000200303c0c20500034a8032800103005d410030806000c55641c1505000354005084040c4d920f040703940b02c820b050001002540401085803d110900000072201d05020030150480d2415031038003401c00c1a104823588945c0d00041c400748142d034960410b5000281c0a005401e0080f4607200500d41e65 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 593229217 1250 593227967 593227979
    0x120203060a05282303030a08061003020d02030c03181614010c14030712081003080c0a0b040c17010908250f2609100503060f060d02090414040b0403030504150510 71
    0x50345000014000c0d04100031400707c07903910401079580882e0484034a0280b00d03503c82c00318001d0290540c034030b100910000601417800e01e080301451217022586040d10313050420551107900d0b00400d038484410060384183c140410700060604903880e05043c0351880482d9484c2d150038511400407603d4540980000130401c0503c0751507481344a07012402e080c220403e05105001c0b00c81e11003540b0001c0d00d00040440c060b04507401c00c0c05075284498120100c6e55160900d03003007070401150244503000d206a810400034101040600401e00d4480d00005000c0c00d00121406000b030803075641240800f8007040800003800a50640341000e01c04d0b01a0060303407079000c480b20682210000d00c0714404002481404400039a680301d064504410500341b4196890b0703150761000c034403180710218040340d12810110340c0040c01146036010b4046e802040350144800d00040e1106040c203801a0f80c06003404011200040202c0c0c040e801468106202d2a407030740541445d0cd80d0b074030403140103591031110112019020400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 593230467 1250 593229217 593229269
    0x60d0b0a0203010e06091303050703050f1911012304061527111e16240501030b0c0711120318030706170603010605031c120203060a0528 60
    0x40005d05480784a01d905081c01d0310800d107120410018104400041d188040600c030b003056509600c00402d5241d11221000d488084183c0c611001d94001140c041c1d6124000380140100701d40c179500903441c4200d000380010a9100041c0042c004c0e01c202e500c4092a424003010200c10600601580501c40c075001b1165010140104100395071014850a0045081010500404a41c021209400c2036102c42c803400040c1003050044103810707001e10485040400500400c9481140b11381e6203103404640f90f02e2a5032001c0d003241c0c6d0038000500100b00366800500c41031045801003e100340114080060a0b10358000500ca41c0f404041d1a15660008115034080d12415000b42c88901800c0703001d0719400b420b06034028402c0102020803a1103420401c00306030035450a500c580c01400f00941550038000c11506c10400c0070b0319003c008400180c0c41c8042600700f85c424420381303002c0c0f81c0080018002d14505802c00040203208180805803041514040804001a0761200001c1071341c064011a00500c0000c0100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 593231717 1250 593230467 593230471
    0x806010e0609100603050402040f110403021203130b070f051218010f020316020109150f020d0c020d0f0204180506060a09020f071b0b040602011a0f01020a0308060d0b0a0203010e 78
    0x8011880401800348000020702e0610130381d05940b50003d4036940b940000b6000d00303107031807025008910b841c0700b07042642e84a40043c02628000e894000c50f0010724188035581b03100f818a101c0540880d90303010301a60242d003006210903030082d10350b1079480740350752206420a0f40b203099450f85403500044e032400d0100440b941c0c105030312090a2125113160658406900c1c0d1007444810110458206610340c110380c0909011f00107031200000e4801228044c00000e4400300420300d2540c054402c2c44021300d100c0744501d004829503540900340c3d4001600d0782d070713962405812001040703a00c940c0398054080b40005c10f48444140034080c0300180340340e0505000b4805050015080250741600400c4007207507003007644049030010389c2c4c06146640c03e03108240301850a00c0c03940d04407581c048400580065040e5054001110007080c0040d40380a0400b69403c00216840c00415140960016241180406d028070446070340f118018250f030003800001d030790b003502e1401e04480441440e40d0120052080000d0342c801c050f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 593232967 1250 593231717 593231719
    0x30515070e120d030f0e03030c0a032a03090c090507090e06190b03250f0e10080a110f04090509010b15160503120a050708090d0f0e030f070806010e06 66
    0x407103800000c69110b900c0f5002d00304060709064032400e0380c09021800f544140c0c40180174205403a01c03400d015606009943c400010b07a80002d0912008544620094119154040302071521100c0c2e50344800c0b00754054403101c101982d480c082d143c40081c00c1c3c0d02c28040c092040100c0e65548001d6414000403800004000c1d20752070043e000c900c1010091081c1c1c609100656039103203000c030b4681e5240504040c020004609610005542d082440045174000c0e204c04030142c0c0f90348411012000036024450801d8607a4032250002c1c0c0d0f1135000c0740a03820154070040011001c07038401e07131402d00c030f0a1005600e0350065000101d2195207130100031500c030081c85400030401c811214502c2d200c0220740640424000c000c5c2c1c2c9403014000445441c2008020170480352110892080d580503443d000000400070f1208689030070105108600140e0500720100e4800d40410060300c1340103070004e01c840221016400303130104581510a0001d030044542c5c04205a400821001300140312540c1421545240700002a01035 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 593234217 1250 593232967 593232979
    0x1b11060a1806110405040212091c0806060a030b28090203040c0e0a060e0a050f0f061e2205061216120303090609050607020111091f020304030515070e 66
    0x306201c500e010300640c4081d8200d5408034903a071000d0b01504076480341d03070700070b0b548584000b5802850f0201c3c800020700c20000101660b51301040c40c41220300e055070800d10348000601940005101c0d140205c0984820b08107464001b50140d83c000204481e030030b8071a001d441c2c0d50304160454000c0c0c0485529280503203a052003d40c02c5090a03601c40f2851513a42c02102c64280b40d40d0002a00c082141d40304500403c05600141c0050410b21041c1000740415250070104030303150710000d20080c0c50611864050000a401000c000c0740100c41c410040c0001c101c4591300180400780c0c0c0da41c101400e200a403448004900c00a401c0c101503040000100140c9070096040e080680b80180c002c0161a5000c211010001c031840a143da0f45011001031240e250001c1030399103014002d03000d000700003076481e1240e1100e4008111388014151040001e002c0c404100354400290105003807246015090300590400c10300440f4140340e180c0d65a2800e103040d50142201d9a10300c1030420201c980d004100720040d400958203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 593235467 1250 593234217 593234231
    0x1206080106051f11010f02180f0108062b05010e0c030d0819060302100f080601110a02150c1b010f0302030411011d04090602030118020c0604060f1b11060a 68
    0x30910048030400700a038014400800c10285a005204c14944209035000030030421000c004032900a420000045c0c280c00103e460000c407a081101c0d4098401700c050b11001e086036120f41c10095005192410007202c07100c030540303c9254201c1e10004200c0284101c00209800c0c40e010303615450681580c070610312075441034030301c092100d0b044105250001c1c4000d508071103d5000341c20900113060503500003500310011501010b00c169100c20100300050403966a070801c0d440318401120220035541540102d038002a62400c0186003644821051401d00040103050003101ea0303070700b800c0034071507400312020407203024121710b0301e6a1090300001882002e081c00c60850400b500c640d44400290031440d4107218010000c2c1440540c840644800ca01000b081070007801142d00e012800f80d0820b00c40c144064045005003000300c603160096130602c040c2440106499603540e01c40002411105003c08032640c1c2d9400c00440b685c80c0c030b544440310486280c4811224403a4104c0031454050010000c00c1d1a0b40f030910 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 593236717 1250 593235467 593235469
    0x9020a12111e0c011503080712210207020d0c08070e07020105100302010e010c060c0e030f030f03161106040804030201110f1c030213091b080702070e1312120608010605 74
    0x410b000500d82003070b2682c0300d02000d95540c0c01400f01a06a590072940e64400004001d00c18004160140c0720718054001c01e00d01d00002d0750044840c0403608401c13940c00000410a9a0b6a0301400c02280024450280c1c0140c80e103422030120300581000425030400c803028440b44050244e166001801c5200130001d92614006071030340d10342d0601000313040003440c0d10b40403966842421441034083d04020308010861040710040e0a400c0000c4409010340500c410524442c072011081e01c024848100c411842c40d070340c2d98000780501400000d0401480340040d451120802d080140a119078441c4021075a140e040d800050001074114040100ca81e00003c0030070541d441c0401e044048103441e82203514032a80305032090300a4003a2208282214021a0b40007031510b04a8000014404e240d030000080002c1480e41203404a800b2100c19002d40d0040300100072407a542c0045980c070002c281c9218030010000e581c4c02040000710004003002900907120002c0c6c410242c4601030050180b84020401a45004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 593237967 1250 593236717 593236747
    0xd1109130e061e041124130f030f0809130903020a0c090e151801020c01060e07053f0708040308061002070302060a1e0809071505031f09020a1211 64
    0x100010105018000080300e6a12603030b06e100301d10801690000c2c0c09a01341d030341d00d01554120124403031a040040c40c001a016003200035001c25039070040b0068104000b10f888900d2168441400650040440302c3c0e00c00104003188070782c05005100342d0141442503c00d082800540302240c21081e150380c9800d05901c01c182c8000750480c020315000480200958440303484040c1c41e920302074011660750002076040d440310b2044d8044000e8404004000949481d248001c03125401004d02c80700c180761504d4051544031410104800704a0035001d04241c0880b00c50700c0d144a0381009944100104040ca402d0008040c0c00c01081c030351012068be86a120403843c243d0007543d0b080341d44070180c081c03840080d02d0f0700c03003038031a000b4444481406c100350340d40e181008200401e551021200c0748020701420f00c010407220312280c0e14000c903840d20b0fa180390071b6403940c0840210101201e00070001707106a00c440010903c4032400501041c51058840000041e00c405054041c2d6440c42d5112585850070050790300d2234540c01c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 593239217 1250 593237967 593237971
    0x30b040209060d090503041802030f09010207030507030c0c0b04061e02160905040f050313060210020a1e1206081b100203071b050d0f020f0f060d1109130e061e 70
    0x94902180094417414068194070076900000c480d1200b9000c41802c40c03000360000c43c000e2028078001c407510780e55030410030f00300c1c090b80034028006001081640e0219100e1242d02103014018882e20501596540d4083c0e102e500c0345d4000c0000c6044221040140400c07510f81c80340702c4005001400305228120000d02c0300c0c0d442d034011024041d40d640c020030f00f4048000025440c0c80c3e030290880390f5440003241403607100c4807184142d00051065402c10008110395000750b0b9149a4141c81d143c10540391503116500b0b03004440382100c02c200003e00c090506c841c0d240606401000d000b0040d103c02d46a000112106032840c007407480c0180d0f08a543c42c24102d070300004844009801c00c02d400100b41c07404204c042c0400c4264000d5610482459000d002c2c081c2c904050401a80b00f1925076480c036580300240314a68450266495010209200c0045407410a80160b107060b03000b40740003881c041d91800000d100141000a42d0280303640c5500310440458204100d0b0b030403040d16440d0648114100c441c1030400c80c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 593240467 1250 593239217 593239237
    0x1150602031c090c03032325050102070204050f070f05032710140703180c0303120b0904050f012301060e01030207063803030706050403110f060106030b04020906 71
    0x4100d400d1940031083c1c0c401c49040760f0194806104543d68280104003204a1521081c048401c05100d80002c030740780c007196008618102030480c050002c41c0b084070030156141060300c0954082000e8401a565445054400c3c60300c00c041d8003407410300200c02801092075404e1001840010800d03c00c6c0300c454104900c0c20640080c2030104410043d070b42503810604030030540e0152a041050100300082e141444a208903940da8003041200d000c0030107006090014500500030a21401c1c060001c603216000c4890b500100030350210301c04100340c01054a060048038140c0300d85d08a0f42c1c000614210030300420403141d1300301e040c01a50304110317100e1101065062055209000c880e11054409074000c2c8c0550f0007098101d00b00b00403c2c400600c020740c1d143d2610034070030304002440205038031010248154151615001d0019820044c850355060001c06010b001a4240400030b0103607030f8038030801c21040300f2402c0c08102501e66545400d0014040e038500d4915507208038014040c4500300e071103c80aa86000d20 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 593241717 1250 593240467 593240497
    0x7030c0c0f020f0a080c090c0a1e0908030706060305060f0906070c15020307110d0504141c060219261303111b030613020109050d0c081507020115060203 67
    0x707200240101400801464014841d10750001c0c10317030340c041404442014160741c882519545e00d06100804d1199042c070714046640c04d2404e01081e5080f5201d0f41c03201685042c00a00d1035201c8844515680104004640e4241c0b01c140600c1003007000e002094001c010300d1001645820041040c94903400004c08400070040402c40d440103001c075088030f1404a8007801c100715030700e0a04040080a400302e945101105108500100000d01d1081d0211011903a0720740010f040200c4920401501000e1031a514400903050766260000c1903003880181200c050415031502c41c603040010181ca40e0f0b600d2040099600861208002c0c40d4027040c100d2a408402d00d0340040c80d10b5010b00d0241c442c10b8000c0c400003030034851681480041441104081c0441d601101250010b40c0d44012030002070b01c1c082c400a00003109001c0030081740c24901d0603480940d1240940240b002d8484021914107800952500c10080007c0240004c141e020310440e64108140806000d4a07030400c50040e42c0c0c1e1242c1d0010381c1c0051 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 593242967 1250 593241717 593241743
    0x8071509050a15050c0a080406081515180a03020402180a09020a0e0d060e01050103030521060a050103110f0d06030b1e1512032128020f1c0c0807030c0c 67
    0xf085c1031080d00403143d0302208170341d00c507a100e8100a00302001200c0509510040c408003015900c1e10108021503100c0010f40c15141441c0301040041030032483c00202d030403043d89080840140d45600103860307000301230500d100031182e44e042040750f00450355114186140c8100909203207560311121041c0380f4802640d0080d00740307101d490414010441ca0300d8001d16035103844c00210425521900814032028060f100034110304807a42c04000302c1c1c0091307a48a81c400780740708080045501035000721004120071500b590805e40c0e91081010030343c0c800192a410700756504018001c103d1107183c04c980203010f01e00702e9650510803c04c003502c4c54601a1109940d2000f180964240391303182c4560707440f48454002600c2e1110308154001c041c40c4030510807060200c21250009485403418001d2031039203e94070102c0e000c01c5140d44002c3d0000c1d80540d00421035043e08105034214a9000c04401646442440740041c2c95502944000c141400140c11441058200609002420740c005500b5407020380007030f1011480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 593244217 1250 593242967 593242987
    0x5150a08100b18070e010f111914070f180203040803150a050a08010f0501050906150721171f05130209120a0b0108150f1008071509050a1505 62
    0x8042c3c05a030806801c4180080000159011219a04002c400e885803500030312410300596004070540b148040540c001c40d00141260010074102806a00034844500c1c4069001032013401c2c5a22500302c0240c13000c582100700082d0754124800840786240d55021400c5051030b9603002c032984405000c843c090b00c800704e1415081e41d0390080c040028040149215500742e40c810000f406040420160080300d481c04000240070300b8a1203040b8803c5100401001c40c180c010350405115401403a0199102c601410304c001c02050f10070640368940e0003944503060f030400c48801ea5803a02030000c016001900e10300755500b90400c03e1803040f0f02658401c9551a0b240307036900f0003000090083d80180c9500140b1041c2d600c072084004904d1400890040d85c05600b2681c0f0781c0b900c0c1e9520340c0d00c100c0709000181c00000082444410040160300000c4858002061030398840309503181903610742200c40314013102e8403441d288a4101c90b00b0402008141c50620300185000c1c03030300302c402c01d1251540e800c1c000300251900300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 593245467 1250 593244217 593244229
    0x70f11011d1e0307080d031409071719030c140f030307031d12030103020a0e070806010813020d080310120807170d090b0711030c07031209031505150a08100b 69
    0x3002e40e0150403540d9072036031a030350306540302203c0f00014003291401213841400083e120601c2d200d0742e04a002041c4407480c011446030410072002a600b0140038021080200075181040ca140e124042c5e070380c200d9403015604049007224001542d054a65100651141c420040030007520761003540f0b07080005464010084100802071964552070441c0112070580c02540c06da000654140c9000341c44034241942c460002503640c030810740e0441c000c245c030840010503c0d0f1281c23010550140c107601c40e045400f00d2a9000c11002d83c0c0ca035408544542c8080200040030440085000041c44020b242e4507c111094941d201a4800d80e80c01030264020549000c1d51203e45100711080070f00805010082d1030740328103040404250a803003240c0040c05460103007110f036800101b0355081440e15400f62002c1880c50fa034040b501c0950314944810702040b1440003001c105c0c4840004031070440031a002c64145041c0900ca900f10110801030b034810f0507844424480001c001a82900c104a410340005403a0610400124 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 593246717 1250 593245467 593245519
    0x3031b031f0f06020f03121504021204030804061a010504090207080c070b040f05041a130b040e060a0b0a0806071b0c0623211b070f11011d 61
    0x1900903207000001422110300d038641c03049498035030a4602626002d00c1894403446504101900c83c41110003140c910080c2c404407940c01903000b800140340650180f4000d03040c003022201a40400c08107070820041c03165070301030000840d030820a482062604000003a11b18000c0c0e005600e880c55000c655203081101c0c0b07000f01c4c1e03207505604080720075496032652042d1f41648030b40220313403044001d4600058241070901528180350300681098104071180800d0200c1541c43c407212800351900d440c6c5100080d02d0314419a802503070507501030711840c500075124030181c03801c04507080d0180d80d1442040014050200d1040d030001c0c0c40d0b10b414001b0040701880e4171568401204042c0610100c1c0700c000944580140c0309060340d0490303049500e0fa0301e40d2201140000c0c0182001c2c4c110034008540c048004050000300d4950049003022180c81c410001c401c07124842d005560116260700d1002c42400502004001c040042807003443c4c03100709000c001282410602c891581a40907680890398484002a00e2417014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 593247967 1250 593246717 593246761
    0xe070e10090e0303090f0102030c070809370b090102330f0405150105061603090e15130c020c151e030a0e010207122001050c07021203031b03 62
    0x1200c6004024251510781c0c4c070070b8403881c03224401d02505400810042c0250fa104a00f038210050801e40503403111041d5a105041c0254008105201c40310f210601082011000d100301e1040704040b045aa44da00c207040c02c82d00320b607140c03803414880700c1000d0381c0c006950b5001e602410704051b2685140c501c0340c81c0c110030213211f024082c000b0130700700030140300d8060040d0b118900600881d211508034540228600342c2c28054690442e2080201f140401d40010010800a100f45880c80391550340c0c044101c0544801c0c2e4201181c0c46407214141d1140c80d00d420304e040324a080301c01c10000c0309039100d0301960b80c0110a6910740503114400c02c410204040e00103460b4208010721109180340d070070426034a015803084446503002480e0409500150f1014401c2d124070b00e03400384c1c2c000700c0d541d0f1240040c0e030202001d590a52044100c125019004032081c080c440c05000a0400c268841030184100609615843c10010f200e90040c4108041c0410b01842e410010360b40003e05560381d265641d240c106000240106 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 593249217 1250 593247967 593247971
    0x63c030813030c061806171b0903161e14040b1309050c0a06090b072d050c0102190209060904030e0402071b05010c03080c0d0603020406030b0f0a0e070e1009 69
    0x5082e5042111204e40c070b042010105da026895807815a25110b4a00085440090703030000111034020700240b003202c41030990982da042051050000f481d080c6011010070101041c440f0403c0580b411283d000d80c0350110300c0c1400e04240c01c00c04c0030241c8078208418940b0a9413900780c1018540c440080c25111142e102c0011300120380d8908280d50b8907982d040c005030103201904800210300d48510b40b1441030700c508010369450103946896100c015441650850001541d094045c1450b40a42040800d242c0c450303009806c8142c105800a82000030000011404100250201c0016540d850015034481380445484d244c54580b03003401c0324008980c4500a800034400526182130050103010b000f840004e0184928517581c42f00011101f803c046500240803405210201d500b140c0004081c201c81c4c5246900000d910365243c000030203983d156130041d00c0100304502032080d8100444402d075031100d06010309002e601d240106107550303035643c0d100782084140101c020035051003584483c18000d0114040c1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 593250467 1250 593249217 593249219
    0xe19030302120c1905030c090607050c03030a090906140d1202010603021c020a090c08060108130b011502210f0702010302040b07110907080601020a0210030f063c030813030c 76
    0x81400345501500380c03444003501c090384540405210f80304591143d203d800004e03007002052303000d2100c182c005100440c1d1038092050401c030780b6101040a029401c0d465520414801e25110041040b1011904219402212080d42c00400e848083d41b2100640c0c0c4904e0031b02468101c0f0004a0044c001900000d5200b41100e1036068980440c84500350424001c844444209a40c7d41e440b1081303c846441c003401080a12000844541c081e07084260b00201c1031043e44001401c80d41d034450644401d030004140310309402503440855604100110f1800c4545803800c0d602580c05400c01940d026102402004500c005034003030440e440780d01600d00414441003566151010391424640440c610850b40d406070100c5e0000400d40751080319102e001e50310680160413071001c180c081c480d0b004010f0011b00141a2a501d8811281046120304401400351102030f559000c0c200d900300781d0b94014101001c812014603505d9000944100c03450320b0490717a005801e1942c0301c0340034500182a01c02c9502c054462034400d44 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 593251717 1250 593250467 593250481
    0xd02071a0a0b0a33200a02151605010207030c03030e0c0a091a03031602010201241802070209151903080d05041a0406020711040501080c0d23030c100e1903030212 71
    0x5c4805c0320800c910103900d8000d15860929a910b42c81080040d511070301d51856052400c0030080280009040d81980c0d01030605940c85032405d9a007d014100e00146032200030600781036141c4291140000c01d01b011703042460010300012444006e60203000d541d60741e00c551211040390b401c0c5c92142c5900000d002da9032074482d800c06000c41441d09030416405542428036034a092141034150b5512022102c0400080a007400007281c085c81001c420360050b694204076200c00b40eaa0803440c5449001d5010075595440f40d00e1003406150002c582114100c4081d041e818400100110203a88480040c404005400d81d11811301e910282d0400c4020815004107a0912003403103903036001044c425000782001a61243c4207418881261f509200b20040c5400502001d003c0d454038149440c81305001e08418101100b50052096900309007460314009a0310000b01081d0a20f400d02c1081c4a81d40105401c000040d10801aa6202e2000d02141502c81c0030b03080b105001c15000e0350680c1d000c7c9046030891034003841c02ea5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 593252967 1250 593251717 593251727
    0x61503190318051909050403030605130203060315131b090608030a080c0406080c03131401020a020105100503070b030a09050115080c09010b0414060d02071a0a0b0a33 73
    0x10810103900e011400c0c011556090507035010002119081044c070b40c0c0c1d850410f0721802404064000c07800c05803950720004555440e04100c42025015640041e0b41b0708100c010140f504507410710804c204080c07102003000341401b0081d1410b00a0300050500200c6c018401d940d00d003c039058100036007681c5030603030104903500004050090f145464440300c0c156103921103460001c1c040c903c2550700154075840000c6d00840c1c5032014540040e000840c40c0c40707044d1140d40c1e0240381c00c00212030351034a81d400305000d5a195030900441e030f00002c3c140c0d000254107003170a0110f03848185900859a982d2800408078110828950245911a0b0030000810003621403584079404010340748a00003452003449403014980c030707010507418100c4a4500280b460507162031906100420344809060307100300b052000c00000203103800200400c51180d4900300f500c0b041a103940390302d45000707480070f461075150203074410340c9403100103000341a00d024144aa0345011003001c000b0115114541a20060b41c007000c1c40c011081d001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 593254217 1250 593252967 593252987
    0x130b13060825032c06060102070905060d060228090311040c08070f1115040c1a0d0b0621160212090f010207051011011802030615031903 60
    0x15541c2501e5070301e500c1c2c1d207102c05561598407003044804030a40c141209001c1d910424000304442103800700c1a0f55900305400380750080c102629982c004400300709807981d043c0010b070b010782900c00e0100110700344540031908a403141c1c4030040450390b000580b015056651007041007184002d0807030210b1504a48802040000e140c401155001c21000345482c1528013400307000c04184095031021816540c50004a41d11390302c08540d9401c0c400c440183e06030200b014050f8501400003c01070800360b080618103604031f0320b00c41d401100c1c0f8045805041007052512310441e192401e1a043c0800c1c000c50441c00078182c2d102e40310015032900700c4050211100580071110383c0c03040c070700c07030300005001c1c984860141d84955080d01040110802001005403900c0d0010604001c0b09040c8125000c2648540219094407142c85c59140440d2041c1524004100d0900401d031101a004c0d090b600d08080c00e90102e0340e962405840d09031410300002c03102000c1d46003040f4241d00001d0b107030b080c0c20384815241406003c001207 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 593255467 1250 593254217 593254229
    0x12190c021203040e0a02071208070e030109110307140901180f050403032003280e0114150607080a0305090f1f0e0c0603070c05010b040f0606110a0c0506130b13 70
    0x19000134030403001520030341e87d8454002c0082291402040e508503100c240041403d000e0110041d194219070b142407107100103940c41807591001100014080500d0700c00c150b8002c885c40140440b64041a850325900e0b20304440481c0025200000b0b07510110700580542c0742081c001600c0c0000300800d140d8143c009402d480310400400711b00600a4503101164801160050040040520b8400701d69481500720240350340d0142000400c03021a411882c00d40300141198401c1030102c00a200c91504070924140594408880461401600b517540107600e0192950007006c2c035a5a0001900c14401032104522081c2c000c0c0580d5070115543c01034030741c00158401030b03042c00c0746007404800180b0342c0001c20031070040c8000c100c40e08640d00ca02c400c40e15144143c0e001c54455490303403a40e111548603400743c1c0d90160302040010410070f09066008208a0f4000065162548016042e001040050302408142d070000c1c0c03142a41c824030026505000d0540d580010280ca40024071200704180c00c00d14036003a121 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 593256717 1250 593255467 593255489
    0x1305010806010e0f22020301030c0315050114060a020a050a0c17160509040507030c030c0e091903111216020f060705100b15120f0912190c02120304 65
    0x840800440703c51090b520500e03004082840c2c241c00f14074003a0881c107861035801c0e10860207814840c11450680e0403c0c1d00441320074984c41c10502c200b000e0000d02e0300d040004000308000e503600d05080b42e1100410645043d000750800030310409124801d01c040300c03407290040100c9008100d68a40225260105e07c00c1c50340c0e1445845251044040100e01084007454102c490110700d070a000800100c0703100a40f080b9018031130010000000b54280c00b01d07e00850040c8074800325540390003100707100c1000040c84c054551708880500d01c5014801140c0540a6805142134060843c020105501c1d2207404100440034500204082492401800d01c40f080c440c4280d03a02e02500f51304109021700d40c0910000144a1380040d4442000c000c00d683c8460100c1c04014000314080d90340c40c5601e00d059000400310501c18108408003c10350100b54507654100080c50000c051408a0072540d1000303010f08904503810b0007010042c0e00209115101c0c120301e6503001441800f140c0003400c0c01c03a030380354070900c04c3c1a4048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 593257967 1250 593256717 593256721
    0x10c172809121b0302090a0207050111160b0901021b0105060f150a0302090a05270921130509130302010605060901091e1a130b0c070b030a0f0213050108 67
    0x103106003840d00031201d40072010b01c44550180e56242403500c0a040c1e8802002111030000056a19808070902900301d1101c0140d550019041403401e41c0d00750595941204001c00c21000c00070313a10380c20040c3c1190441d80c00e20017511407000b00d40c003912a010490320f91054002080409440641c0040d00640040301c4045420380d960341442040101c183d1603a102c035070240f04582c4228003980050403001070041c00346c4005c940714000150300d01c403034605072002c84091181c0101c4117140960426040b1801200419002c00440003440c46885404080003100d00003054a822003668012080c0103810002c02010765440c055112287c2809103090503001503007050380015590034201c084464040043c0e60303030000c990411164140d045c07544070440d14582c0b0b0f80e41c070001c0e08010031100004080000c0303000640d81c0d1080602c000caa081d01d500581d00043d070402445010100000726141142d440202d41610b81d42c540e1041402012041820610a400080d28219281c200c40303000007030b1038090700c48030307915 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 593259217 1250 593257967 593258047
    0x30308180105240d08091203070f200d0c0b0c0a060501061110060b07200907030e0708011e230c03010609060309020109060809030f07080d060803070809010c17 70
    0x4c0840928081c0c44480f003081010701600300340100c2c006084c0b00c030088915140c0e0b0395030341101c0c100c410315060701d0541001e00700d040f05e400402500b210b00b8204a07501d009035038040d25411041c0409100e42c5108800010f0400e200c40c1060208a07034503504514204115a541d40f070281440f001070600c181c49003c6c4244610300c550041c894541500c0c0c5010b0690b051445543c0d44000c0c400048456180a8010a00d0450b481d0740700b00009106c0d5281b0b40e00494a141d0072110700746001610340158800b6410889100b4400c45049807034a00c0d125076502c00310310030851f0f42d600c008810280c4000c0d45a5a032003000c0141c039440900080d81203030300c40d50700c003000241d641408030304070703550148000c1c001100008104280c07413280320160b0b044103144d8181da1800c00c880940d04041e80c0b04442c11540140b02042c0e2a005032050300c22600280003c0b03000d1441d01001d550ec50807288202900c01d414010201c0c0319074144020380d03412025100307a49100c0382da0783c03542030a11124a100000c40000d0001010400340b00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 593260467 1250 593259217 593259229
    0xe06090709060c080a11031b070b070b04020f0609030613020108061807140409060909020a15081303091205030714030c2a1008010905070c0b0103030818010524 70
    0x8a5a45658880d078104040c0e40d29130301c603407000e2aa0820065540403025074060b0034801002c01081056010f0721003030b550594141030004680c42000034800600003600030611380c80720030744e00950440f0384103241c50480740025480d000c1c4008158041c4165030800000440c175a00d1525194001d881d01c20095407544108400079800602c1c00600101401c0419a40c0d0300401c28999500b0b1030f039000301c0c01c0c43c1e11100014200c0b220707030b4030003071401d5291110b403410342c01c121401c44054814640c410328610b102070f00103001594041d005124114106285005040c402c005c441c0c05008843c00000780b0745801c0c01c2490350707030b003000d031095480c07805400c00c038500e042d8000304403100503440380060051040c2c400781405241122231180f5406980100c0c10407550f90342c105464500c031680d5100c0707a07040e50600035400110b540c000c0c00c1c00b080c442c4045465010603d221b1680f81120340c545841403d941d10004a003d10480e202641c440740d43c01c0c1824044030114580c59a4170302070600c06420b0b030480f052030802074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 593261717 1250 593260467 593260469
    0x9050603060403050a0e030a05061e09061519270c0905091303020c09041a0709080c09060102160b0a0e060f030a09030c0803041b0501171f0801060e06090709 69
    0x4041130041000c181c000e80209100300340f0b11401001d480c101180b5464540c01e100044035140185245224548904c00200c064580c00c41e030441e008120510b48000c1d020404941c89000c10f1158640031401442111402c0c1c083c0082c0c0b0002e80c0414825840e901c80c8102c0a00c0807041c2c0c2000da040c0f4038900261441910810201d810091440503551500940140c01e181e2091042e001c5001b484000080380e150503040a0040d8131413844540f4203081610080d4401c1d0001d0300754020840000010848040000713101c81045034212000705594640c0c00c0186d2800aa01485129600c12100e000921604070405400340d0b480300e4903401c2d114600c00b0301f042001d20480344a01c0f240e1005001103540610b660384200303801c901c2410503581030006601c0f080000d40007110100ca01c1c4070410b02c04020301239482c034641c005120138280001d500c80140b80700310316600010580c5000e2421240300b65001401081c0f1240149260740080042540740c07501c0c07524000e400c917101e5001d8515540414031701841140190 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 593262967 1250 593261717 593261723
    0x7210807140a270807080a03090e0910021b010e0705090c13030b0a1e020d1a01170a1808250507090b0d0204060905040c081c03020705031b0601090506030604 69
    0x6080000c01e59400b503912074541d00f25100d0300b4160b04003044210301002008003900c4200300401c02001c1da441c2c0100012402c2d040b24991a10075010311032501c1d40064542c01001c88a8800758a500d03105911135800c2d5440a907510f00366007050f103032414240c0041035403001d94409072045a410741d15450814502d2045210f0301e0500180280100046114a0012500407005150128080c54540d00c50150703410841010250b6590024484003a00d01a108200b100001c008841038034582010029104412080000c07102c00c02c50800600703621001d034001598140c51030034403980101c050400700c1c0c3c0342e0402c5051400461100008807028071304680c40e03003142c5a100c002403001d1410480041e000c1c1202e0009140c001c0250b1042c800140e64901412026080c0c00d00c0008403464641450741d8150801c2e4005078840e000340d00b07600300c4850380034000d081e1182c0380e040169032054030346402e911b94030800790000c4119a0208003040c1280005c112641204c4002c0300c00c2c0500d032904ac6c101502c80b842a2001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 593264217 1250 593262967 593262977
    0x1a1905070f03090c121415010b07080a1709030c1e0c100210050a0c02060610080106032c0f0d031506030b130e0124080c0607210807140a 60
    0x110114030036042450f840384a8007080c141d056840303010320284c410048045403e0350260038540344850307082148000f402d916800d00c1d00c4c25490b00c00601a01d20806201614a00000502d003a03082c1c000c101c4d016103d030b010b11090303c40707140c1100e0034ad8490b0425003441800780900701c9070700d14403882c11140c06101c848007406440b8004d650304c10002d06000e004141c07821350180c0aa140350707500e014411184201c40c1d0140101d100d0403007080003401c2c9040101003c0c80b070901481c0b55801260b02039600d5064803000e0400140b541c4c5071400020000b16000503503c0c140020800344060b0703940100b68800865000e01c212015081c0c0f003141a000e44a20303103c0f0344c9841665002c02c1140e10310a03080b020056801515a0b260050744586c41d84c1983c40c0309540e00e0b15a03441d207030711626010755144801403a180340e00103409038908003090551600b5810342241d1080d000400d12009003c0103480d5181c0315410740380020300303006a0410107045805c013115080045490402d881850030000c00446001c82019626 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 593265467 1250 593264217 593264237
    0xb03070b0a050c160609030b06010203070f0605070212131e18020a0908010e012c0a0204050a180309030201171e0a060b0703120609060503071206091a190507 69
    0x482c0d40740c00c01d240e400803501c101c8050400d00d100782028078016102941e940e40d00c0504509050124400150000d4110761041105034042079050010741251b66001c9804511030301e4580e001c901c0e0130608180d2441d030010010750040b00244078007501c07007283c01e2107a085c2004502d0060b041d0000340343d4403034444c4503e0643d0303003020100f11070340c000c0010810505154102503120000b050071142007801c1c5035101d0b07547d0002981401c511076924002001000d512408082c514100e0940310b151820009019544a102050054100390000740d14207020501c15403143d122400c2c01089050280701c140c2c0070904003015655448036a00304076209050503410b141070400c0e224914888a44000c045142c01c50740c400012a44c401c1d210000c02c0082d00036541e07003802d801e88110500c11150564400b2090f070f4034002041081e40c50108921081707410503440e1340c104684c1e909060020740203a280c000c0030040881c0010a604411945640c001d4107040d24072901800030b201c041c0c085840640d00f11001c1007810300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 593266717 1250 593265467 593265487
    0xf0813060c12030c1704061506031a030c0d0b0a09080c060121031704030e03030a02010e100e060606070303020d0609050906090c28091a01020d051305061809010303020c040b03070b 79
    0x14046c1e003151240b0000109100000720300c401c8048160401c0c2c00080d103410800300c0540c1640c2c20709640984c11406007100030000d0002400f004402280145180c250350300044031500d055101790a0b40e9086507650355180020006e940c0c850109000d21800e485d0030030301c0d6184001c0c425010f00001c035896110b20b0502074001f00d55514130b1200420440411240c0400300059031000d0018002002041d00007041c0104a0030b203007402c028440501d144010319040400754020710018200e074004c401940e040b65201d01c1406d040f80039210b240780c80101356041900024986041d580414070518090003a10f00075180c0b410300300e849100b14103400754002038a0103000020001703400c030503c82050b000981c040703031a41c42c080982507850790380d254a41200c0d1380441c40c009580502c401070300140c56241c428900315039080c00d804010000d0042d140542c0010442ca030780c80c0c10b180400921258010201111580c0d28a8001d40d980204100d15016038200743e440780080c100091b80e03c0994143c2000b442c10144400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 593267967 1250 593266717 593266757
    0x1090e15120606180f0106030b06190e091f0605300103020114070b1909060e0601090b030307030806060a022b02070e0f040f0813060c12030c 62
    0xe80003400450503000e09412594800400d4001501140003600b242d150079070030400c41c840240b086903c0d8003180c004100f419021000524151001c0381000100c1c0501d00010600314040ca0101560003030280d030410248640204525200c19400c886500c4d10350356040441c01c800000d944818980440391106002250152000d040b2814007514082840700c501068411a00b044083c004180305980d0014019946d11004c2d001c0b21000200e5454035029089c0c0e145044584000c00c40352440c0c1c10310f81b05903140881608100800c58010009001031218000c1039600c41400703214689501d07160185010035410301000b541ca8498148d22040001c0c1d4845040c84000e038000c0303200c0300441c02440c00e080008030070301d0354140d040d00650125200001041d42c1c0649050840d03040000340c0940d010401c000f6059000069900c954403510781144c020b40c0d450801114040c2520303400d1003000d042c0001c01d1041e4041c2c648080140294072a40400d101c070f034001d80481d260340341c6407170000711041d10786025501b1407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 593269217 1250 593267967 593267971
    0x20031506061e03041406102c0403050c100c0507060b040b0301091a060103020720031e030a03150302010509120309031203060103050601021c031a030d050403031d01090e 74
    0x14100710b1906164442001d4a01c200100446152101005000c02d2000030815000c88100100c0103103003504001c80031000d404002c0c030500a0306090104a1721001d035101a29040301d59a44288280505083c5409003d03030304070390000c2800f4400e82134240c1a5801601400ca1046500d40b071311843d210b003e4031010041e02d00c0c814001d8100c3d440300607003013180e1000d2040c0703038090f8003401580d940c2c075041341d0416881401c060320046c1058010302480740401c80b645110185500041e81c00d00c44e00900301c010a051030840c0500e6911400b090804002d1041c000c0010328502110703680400620407003c00900e1010007500019000680600c1620054101070903405280504402200d040100490009203850040b6214040c850804010701006580500a40760021400d00142c09620042c5150301a40c60320301b5a400704240c7c0340c160381e00104114500790101d080010381602c00303425420300003804942c442d104c02c900080f0348044095400244082003160600140c1da541041480c004622501c4000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 593270467 1250 593269217 593269219
    0x8070e010e1806011710051e090906010f05010306140111030f0a02070617040b040204110d05011d0f010b04120809040c080a060602010e03121803041220031506 70
    0x1071030800705842c1d079811584a841c0a4442c0c01c404080c9055800105108004425508020710000c184602c10200300c0d4900c0903130341e060303c1c200616851003d40e45001c004890b0480e030004a1002400345800002c69002d05903240780e206403207201d503170f107004404496140c030689150705580321055445601c1402540480c1d5440230440b81064034003528004160b21503c01440503a2007900f00304401608a100020444090740d06a2079a1901e0344503021036240040000344641c1d84c0d5101c8201510700d14041d142e20003a001e100300017560f100c46c4620b031b444d003010103c0791038141cac10300000b1040f8a20404050503074400500003400c0c2850203090981c00f02d0980011500e072101800103030326903103440c407420700304000e9581e4070040e03420300c05220011107034550040021a41403030b5a1075110070f03002003102c111084103003c00d035095a62510b0140c440c00e200514100034080010000748401c030914264038054000c08442000300c80040b0864103d4044c0d106050301500000604403403110381400340c5900501c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 593271717 1250 593270467 593270477
    0x3073005070807090b0307090c08040b060a08031803100c170601051e0703030b0102030a1b05070f0b0d0e150c0717030109020726031f050402070c061e08070e01 70
    0x10b1201d560300c0c01c10303401d40c1101e0101a0b84880c10040c0d40303000c011314030003441404d10421100d0540311005010420040010384241300e00c0c004a01e298658600d11030050110b42d0a407505c5555820b0520201040101c01a200f0300c02e20340c00307030700c03120461007003d203a803440e511400880001c10b00c075110701001c000d01030b0341841824062003070603400002e03004a036136802c0380d0030725a5000d403458040d00b100d00ca1020749046500a21000c16a10b410546403c1241a42503040081395424038105207040150340160718041c0d0000c600080c2c5c1000080980645502e0f04000c2c0413408000c44450b9031411007448450404846502044042c000380000300003490040d21800d50440b181c80400301d5551080c1d1155440c66400030348042409240005c05602c00250f100302da0342e1003d43da0300122503002c0a00b4046840c0c1c40c000c56141c5044203103001c42e0003403c0180044d5181c0b2058101300144400344d1003510702107903070205104600c01072039201740c2014241c0d407610b5141c0d8640c0d040840f851a40002694103204e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 593272967 1250 593271717 593271719
    0x6010c0f021e030d031e0f1812142a0118110a06020303010b030a0c26060a080c0102060408090a050307121101020303010612180614060307300507 64
    0x18540c5014944000e1880502c40d61801650092518216189808004040c6049024a004100112160000b600d2400d010841c4e91589aa480c0208041d41074010b603000594000400c02090b000c1000c0070f002d480c0c5540c01590007070f540341842c1d84250b03140804210350240800c185904164000703207543d80740c40700008540400442ca001007208001042c6c0301002203c03044042c40c50042850350180060344055429545089402006070101038070300312a040d101e064041a6a1203081e1510b02da413050030a070b01d00d141005240c04a220012346030036000b03040c140d5012079181c4000a09900d40c80c03044c4e00800c41983c5030340f15400190007622425500c030983e944d000030350b5030313081049002408103580c00d40300034002450922030255040c0c0d00302e810b64105100400806400480500852440c4480410b800b58400c00100c80010010b00051109207080c20420141041e00d000364403d807025811100e03046e450707120f148104900a20200d0400c40410100f142c0710115411200440c0d100c2c1d0100d500403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 593274217 1250 593272967 593272969
    0x10306151d010305121e09010513060e03100c020c0f040f0903030e0f01090507031b0f080c03060a18060b040207050604031106060d0c060e0307050a061112040e06010c0f02 75
    0x141142584400d055003038010700138030905010039188215449240c51910141c0081d00c0c0c00700d008036a80104000020a4511b0307103034020003c590704008940a029403c607100c41020342082d0942c610301d03019108201c105480c400c844d200e01040304c04e20b1b030000c101c2403514400b0820010b40c148089c6070002d80341e0b20306032044017030750140c4052248651000300d0312100c10919240f90400405100207160304005980d00440c5011441d101641d810031105009000911008096180158003403900d030110741100250b010310124910f5110382c0120251506d54039850444800d464880b070004841501c10700e0500c0c0040c0e4642c0c05242c846101038400350800382c1a0307c82508100c41101e080d001705015031141005c0ca10213000c0203500c02011215120f000d02d05884007000c1c9061805031300180840c6821585841d0b808000c0c500c01420000d081019617611504001c0c51482501f0f899845446904040d51005600324161002d450781e0b4034003e80182e994400450b00b001040c80c080d11143d0741c2050321005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 593275467 1250 593274217 593274239
    0x90905060d0b070c1403090f280312230301091503051506030d03020a0f0509010c050a061d0a0807020411040b0310061d092403071508010b0f0301030615 67
    0x7181e101d42d20344c800e6000c040c1c24009010050414541030b00e40040000300795650b0f4001d500010740805940403101c2c0741c809480c1096540c6407180c2c108280d034070550300104001403e64880707800b800e1666a0b9032001d20f205078194808c14a140c92500d0603070f046c801888a054160701c4a40211250310b102d01c00030f0340e80c2d292142401442d464402d102c8451208100d0b00341007c01c400400790b103da1408502c0d0414003a0002d0070080006003440030408005a400c61a82c41298000d90f259004410307140c0d40d01d11494104010284501c1c0d00404003503640301840314240219000c2c1402c0d800c0080c41e450070016034200001020782c0065000001c2c03090002040507440c2c42d018612464100740140082400c040c005003c8080071200b404244a411041c0119511044c0140d6009003a03000d03200c0c100d44d0030307585010b502d644c81c2c900c040d014400d5032000940340701c0d5448041d49080786600c60401c0c1d6601c170143c4401c54442d40c48a800c103140100010400031300726074400c81c42545000303519030015441c0c07662459 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 593276717 1250 593275467 593275471
    0x10315140f010603060e070f0c1703091605150d0504230d02010b062b0204050418020a0f050d080a020a020406080a0209220201030f1401120311030a090905060d0b 71
    0xa0054001070050060355010300c581c0000c1c0c400400c4400203490070810040c40405500e8221041250540c564410401c20441148881214820503520b034500071015a80d6401c28400790b001d030528803d800100d80c245071100700c1c912041140c0e02864003c003001d28801512029004071010309000ca22619017061100603203905414400242410a00074840242510951501c072071280d80104001a1880c21240908280400c2580b80d0040440f0f20303103100f40280907d90150387c100f400c080030840f611740020514840c0520840d08a40700548680c2d007410421428014280c01a951700d81600c0456034140103401c000e1031500c1115119174680e8040b50641d0040d078020316a0b5484000003400310b01d48001c400341d03c0500011810701e440e00060f0044200d00058601a040c95074030180803a0f01c81c0d40c0e412801d03100c4412815010070b5603544c0c1007030002c0a10310400380d0000781440c070200d4000b41c0110032640d130b513031081d0b682c80c0170309081514000041c0005041c441c0e01104503d0001c00144078068418 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 593277967 1250 593276717 593276731
    0x30303021c0608070e241c06021b070806010303020613050f33070210020c03070c081513080406080606070b04030513060c0c031b09020403060b0f060306010801031514 73
    0x1c1840d11a00c03100c015000343c00b0b240c00c28980c0b000325031b26a0304900d11300c00490303048400781412001c581d488100304601e0240030b04120b0000892440e500800c424071408542e03441c0403652104e5946000c1515102c0030300000340181c11520109601407120350303403d49490b000d4400d8a0194a402040d00e14104214001502402c1c010244c3c1c050311000034000004a0007019001180d80340442c4000d444042c038010101105502003000d0700341c41d0003042a501c1c6954060f0f480b01d9025103e208a030382c0c0d030086120006101d01e2a4001401140d03480c0180422194059045428241803403000c0d202854000c001c0364100009002032800304602d9010503020754041d0b2200c1381da46c10b6260042140d4000c9401100c14444030320007201c000f5011680342c0c0d040342d0300045600011110f81c103604450b200789500c14002c09002080200030b000b01980079040561040b03c0181c0c00304c00c00c070244a800e010440304180803403012001080424050320403040c02100841c03000420049980c2d1462071044107681074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 593279217 1250 593277967 593277973
    0x1c020712140c0f0d09080a0218090c0409080705010b01021203042409030c141f0209030a051c0206010905130209041103150114060408070611120403030f03061e030303021c0608 77
    0x1407203145030018084c50286c903001c009044500b060f90040307507440c0300322082107008050076000903070a8007091003a0074452000501c07c1c04105500e007804441c0d500800c405807070951030503035074104540c000540d140050406644140c203654494031000b0200e600c0302005540d0125951050130070240c00c2c46411402882504c400884c01d800b41001d01c0718820303105421115900a40c020310440c1d07200c0115806880955802590350345810300828205010488014500d01c07410340e01400300c40182c914054645099822141c03244e07039801345442a95401e641c501004a454420070000d42400e007034650380f0030b01070100c00e00740c0c0c11100d000c2860a89200e0212030340c90391b440e0050041e29496004491482c608440b40741c101428800015150411486040c0600c000b40b4213460f00304c10f09001c80208842041100e98030780d6528140941072500030040d020010b407420303201180c40c0c254494502c10030107a9810410880f815603030154000c1d8044032407030000004510070302e40d04001c10700407880034181c0b01000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 593280467 1250 593279217 593279233
    0x10203130b030f15010c02040203131704061209020a060804030c0b0a0209030c09040228050607080307030e07080d03090c0b04060e030d031a010807031d031c020712140c0f 75
    0x40406001c01504d40c1c40701800c43d00ca100c905130303032000440444a804443c0140d0325110407181400140741c24000408a1000400002d010381c0c00c900075004035022500c40c0140003aa4100c0341d800c0700c04d003400096001005460501c5000d00c25059207034002d1107810012010340e841c0e1506503804508441003c84190005481041c42c1800c1c040c0c1000c2150a4902071294141940041c071b4141a4098100100c07120501401c1d404962094190040202500c0c00c0d0762000c045c200a02c45e503208492a0703011030f0403d0040502184000b8452080f282c840000e0113000d10a00d1040b00541425078040c0d500e40d1041e90701048549000004100400498690b42c4a095070303041403504043c2c2c03460f0110145880c00c1c1c03142580000d100500314101d0004d02e030488265845282c140d004010b540c5400d20001408030300021000c400000030100d60042c410351003124011034a000c001d82c800e00c41c006020303600100010702064003550550b04c003011072061040c184580031109a140c0424010603410b15404988 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 593281717 1250 593280467 593280481
    0x3050307031515090b04211a0910050c0304021e0102160e0103030806060403050c100c060c0306240e0d05010b151c060b0921010c090302030d030509100b010203130b03 73
    0x801c440017008040038660410785450b81ca09407140c000d003886160003000a40d01d030104480781e8098040b50910810039a00b90038003c1d1007503070b1402142848400079140c107002c1043c02c0c0000d801d4920941d40103104d41c600c288000407080110480c4c0c0b62032410740c405c91034541558070382d2000101c042c12040140c00140e6156080042158401501850040004003c180082140815481d103050030680f045000100d4007582200c8071500c0c0d42000c3c00023032502c8840b59101d64036421040c11a0810125280f26482e00303403d1301454040550070a011444e6004082e1560804650140358a40038100002e0308443c03d0340407407c11842d880449480b5080098084814001820007610f4101c14003000c11a6901341000c03510a0710482403414451044101156146003410701d4503800107036103070024422401c801c04058021072141c00200d02c0b902403114080c1c0030512074800c0c64071039031180000303046400240c80411300801030f510101e030450100304281040680a111814014032015085070b40c2c9142c203003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 593282967 1250 593281717 593281727
    0x6080f060406050a050103080a0309020d0b0a0e060109020c070e0c09061b0d0c0c0909142a10080f09030f1602010f020c0603010b0f04150c0c06030504050a03050307031515 75
    0x8001904c13031482c0c500188041000d510503030316010060701340062103168078000140c400d42d030084000c0060304210704000c00c0b100d094000e2a004910101110709698075200d100b8103a000e48004003180380e221b110f0821010005107013440c4c01260501e180d80ca00b0b2801404517007a5030004403000c400c2e03e02c45003003a01d072400030441c0300210300e001e00c0c00b0b03001020030f0b03610340706209810720454111989410000084c444058005c10010036a101241c984406a4100c8007005007142818100c0600c920041107290400005030403000000e0358800c1c8680e40d40d9241a1030046014028106500c400c1c480c1d03818101d44000141820148400d100d134051825100060070142d12001c07140441d003118001c442180c840b003055074107403600400c04640b100c05000000401d801544d0164000305100d020b41c6880907044048000424003a03006e815000e074441400750181c1c0c0041d81e00402907406a503020b000300384640042e6820044d1480c001c99508620030800d46206129004402400c240c00f400d241c3c0c1603084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 593284217 1250 593282967 593282971
    0x8030106090f03021f030b03011401090c05040b040317070804080105061f1d011202040e15030a0b0604050711010e16090608070b0703091d040c0b07022206080f06040605 74
    0x10841c00c00031030455021400c1718200424010b075621a107500c02c203001c1d020350001c0c107102e10041d00800401c142401f601800300800e1160007090b6103402e00010019200304222015922003480e0303a40f415145a403103c50000e500400102014400d00c28040000c02c00e100602c001d00c0c03840000315590401d98200302028405080d0700d144800260300c90340000b034000c0040320140564000403444a0103110040c1c44e4000801c407041c00d114800640801c445511540300d5000b8400b4008042c1c0f0070000d0f00a15543e120140009001ca10ba100c00059980c40c064000d207900c06142e15140401610949000d4291103503645020030580044501680f0010298540070082034070050a0007503510b0b101d07001d5122140b500070800171103000552081418083c100300c40c003c01981e4080b100c07129801d00162005a41a02c2c1210100600c031000035000091b031065840e450b80003006041c0c000e410f51002e10060300303610024500e082c0c60741000180d515050050b01d608080c0030780034081c81e207881d00c1c0c010111140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 593285467 1250 593284217 593284229
    0xb070c090c08130210050c010c020601091503170f1603020102030403030e1c080606130806090c010816030207050c1203070302011404030c0212030f0310030605090c0f0f0406120803010609 82
    0x840c2c4104070b40c0307406190b20004426010380300e100c8114008901118144103105d00d0007580d40c00c0c00c01284d2801c1d0b00013440c1c0e0403603914100030450f2440c0d80050010f0340703c651202602c02c8035801141004001c0341e100034070791540c001e2900c0e45440172840900320f28103034038242a40980d602104001c245609400361420f0b180101e07020b80721014070400c24021b00245c0c00c15200070030500e0700009000d600c0d0b80f01260040306409280c015603a60310b4030f003180d03144422a0078940030f00800004c10203a500909101d8000c11001d0142c401d01100004120700035002070348140c615104a10304a516500d5040c401c42628524a024558805090a01a081d0351500c1d07800499424801c1c200300100303a0040c1440f5815a0440c2c40083c840f89800e8542c0c0b071801040400031390340d8400001c0c025480c01081c3da00c811607224000c10b018076a2000041c0d03465008094240b500031550640c000c1140ca41001c458171210801800003071800e440701d8001c801c6060074201110540b000000500c11903030800c088000800e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 593286717 1250 593285467 593285477
    0x3050406050313210f1103030c0c030705160f0e01030b2d0c1b0312160207031202060106030606023409020d0b09101a091c0b01090605060f070206090105040b070c090c 73
    0x1b0a0303214142d407480010300380c1c504c10310040794410412005004441a07103170060101c80718406040c00303080400b03c90348a03424100204020015885051070840d41c12a90404120f141c2550b800c02c1105400044002600400300d884058410b0100341c4c5a005001d000c10041c444d40312204560403442000004020903290f50061040c40341c10341703194006079840b04142c400c01c0210003000100780c0c170300b440f00d0700010205400000b00c2e80e074981d0300248082c102c8546c1d5030103020255540c2403d903180d4000703a0b83c0c00c000a079010705140c401012280e004d4220b20b11544482d1200395140045802c1341c2150744158000c40d103c00e00300115291803648607802501c01540c5288141c0b90034000c070b140f65230480c2440c403881800300300c0315000e81c1c1c0c412916021450011600440c0c170302c2441c0001005900b400303180074444c0340c4034012401781003001c140e4030442c24102e0200e2a11040f0340821075160091001c207410000c4c208070100d0749225403c00f514901d4411010301503078904204100d01a10310700e90180c0100303c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 593287967 1250 593286717 593286737
    0x110618010221040b0a051603080f221101110115090c110601030f0f060515041d19060608010905100608010c0806040b0d060c0c17030403050406050313210f 68
    0x15030b124111811103a82006069444e04100001d503140d0080003d10300381c40144e03040210526400400052284c01c00c10b413002c00c2590340c940301032341040240300c3c0c107141c800080514500180030429046564001410b141c001e800144100700d080d10900101071038a030f0b007060810041c04c4142d025861624026041025200141000e0240e40d4201440041c0030102c0700030000007448007481221980c0c0da0041000d11480c9880f880780c4000e0070030142d085020b00d140030120b424a8a1510040d42c410b0200009004040c2d05091203403050541d108098078190780c0c60a0000d8440070074403d42c0401c1d84581c000e00942207240c0000d408892031703948860f9159050802c0e00366043e6000003481d501210454000440c05c42590101d4040001075034000c084c0c514180c0118411303134201c1c01d5004014400c0150f440e140d4240070764202c3d6404191001004140180800e000741401034000d1503101c100b96806030034512450f25107808146415024806c0d44203030000d44101f440c2d00420b4402024810b0620001035 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 593289217 1250 593287967 593288023
    0xb03070f1409092a0603010f0303081003080f0702060c161a0901020a062304030e0a12150914070e04110409050c0618120601050f01020f15041106180102 67
    0x4540d40a0703a031140144102404d1946410340e280f02c0f10500c0d026006580741e6849544c46001d040580c0000e5001c5452400002d010318800102c2c1001d40c1e9015000b01d082ca09200750020450300020340403070744140140480b0350403007010450001c49040805400034400c0c80c0aa402c2c10a04902e91440e4562600708001c0450f80d80004007001095407100e00000d18040d82c0c00501d1200742802d4120301100903480c28081816030108031080d00f580c089071036140c0142d450404400306c45001100900001c0c40140c8070450760060342c030480034280241c1d402054402045841400e0115940110b409609041d041c03205101e11010303141c600040130b95041040900c1900c0c3c295545400c0f944243c03140364005020a8103031000c00d4451610340000e00422802c08a8001c000d44a400034054607001c3e05000d408400c03550b00c0054450300348400300018050101d41280304542901d0000c00943d01c006c066007902c170301030310740c0001402d6440a48102210a040f00800203080c0400365031402070f401d0300c0d001d0035601 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 593290467 1250 593289217 593289223
    0x10c0f020d08011a190f140418200403081206010c0506060409030905040f09120c080d0c0207030b1303030b0102030c071824090501090203190b040b03070f140909 71
    0x103441d1010000c1d42442510009960035100b64804c40c03445d24141c0b02062005c94005c84c0f0200b00000c144c0303960240701600b401c022030500803440b6906240c90030003100c40c01941c1560240c644010365945516054071644007012090b4050f6000b02c569090000c3c0c0d11320404a00300003d034110b4001d19014080c41019280c059441c0c10240ca803a1196035a8800d043c1050b02a0301c00d10000c3c000a0310a0040362041ca51040c02030054001c15207a103080c190700e04a03e6440750124005255006480d079060803c002e0b0460014840520402c041d03104003580880810003c2d0045c500c640070040741525059800d2070001c05071007280c8031040c10741d8428050707401d02e02004140601920002c6000100038607131164030402615a0200f80341015002440c1108681c6203400c059094035044403061004d42d030713544a100704030722003100d4010b917500d080100c0744200405501f01c0340c06401d000300081000340045002078200000c41d4860520303682100410000b40c00381541f0084602c0040780c0001c818508012000c2d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 593291717 1250 593290467 593290469
    0xc040e060a05010801062111070c09020a0807051342080a02180a09090b0c090105190e2e080f040f020111010219140913150e0405010c0f020d0801 64
    0x420700c201d00c0012029604c20b00c0a00300030313900c180d03018823509004500001290788008015580c41c4101c1e070011403064911300031a440d0075001d580b0b40034a40d441010442d0207802c566201d0a40340c10060000511128044568904010081060081e13000304100c800c10300d11003412205120400381103a80560b80c02511540d8469001000981d4503c166501d00c104c4104181c00990b0060126001148401842c1e0044060b00c1c400c45c0f0000043e00c1f848011201e50080c07414290010f0001c101a020319400541030000420041c00c02441d400403040018425001840c80c820122401d9195030551614503060301d00f0042c40341c1400800ca061400a020203c880288094081e0b007812001c9021079204500d104070365800302c00215166070303062032501140c04001c40354400107001e860181d072140c15183c0440e0b00d8004005d2a0030708940c074000b10f6002429100700708101d154002c00c00040d546000c004041d100c2ca100d6000010990301110f000b03800c82c0c1c0440c401c44110742c0000c803481321032604002014 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 593292967 1250 593291717 593291729
    0x30408010f0c112406030106080303180f060f040303200304031e0c0201050706050402060c03121501081e09030906040902030a2d181515050306190908070b0c040e060a05010801 77
    0x4c070b040d0741d08070101380941881d512000d0f140c84000100011120780501802c0b82010400c00c0e600400104080f0640d100000d554101400c0104000308000038020b5001320114280381c03807400035000c81e44054a01c140c008550a9010440711400024201c1e001441a0142c0420b03042000d03000740e407070300000e0003405440f90060506580381c000c1400d5503a200305031500c500c810b40c100c03565004142c0c000101c20348240d1b9140306a280f004140d581640c007802c0c000d44948101c3c050940b800c40b603110f00b080058800b81c4019042e000130002c56481d902c0307600003000541150600541c0c0e03810686030172001c81e01c20b81100348001380d0505460b11780b8460f001e2540443e80450001048030300141c4820303c05410001d500034034244801546101d050081c1c0c02100510740015100c0c00144d6031002810b848100440d50100101c000060b40641d001d00b5501c5044018028000c240c02c00b42680e98400c070317814003038070a1001d6a40c082400c1140002211a0b642d01c42400e41e00c0c95052841c080018090368418020a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 593294217 1250 593292967 593293033
    0x6010b041802040b0310031205030402060d091110020d0e03070b07030f090915150f020712030210060906540c120e03040e0414030408010f0c11 63
    0x21101d01280d4050310054001c5405866490a05c03440c5038002140c54401207070107240d80400e001c1d03020302400a980c0f25503000341c1198503242d10000004010000c80705c0c00c13214071031100c1e0300101e95151074825100032500c6800401c04011f042101808c1030b507900700d98906c260710145050112000e948140c1d12443e40c10f0810852100165000351501841134014503d014604401c8110071640100c5403800c42d45642043c44003411a03e8046030138040e030f42c0004015a210110400c180d0286031480803a82e4001c0c03050f0f902c601c6146d00031105030b4050317038420300f821910f582d01400307042d203243c920f15442e03007680c1c400060352002002c0010400155a243e50386114810f820b8408011040d014040304c0c0c1c040d141d0400008002010152816001c55800780240d803501d05c45500740c2a00004480648440c0c41c05010141d0b12076407841e4201c0c80a8880301e915020a002c00545500240210783e02004032140c0800c5440071107038004e0401c5481c008a40c2164040210400b40764001c1719184008841c203004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 593295467 1250 593294217 593294249
    0x904080409091a09010c0809011a1903060f06030303060f03051b01031b170a060509220206030f0105031c0e121207030e15032205010914060402090906010b04 69
    0x210015048855042500c0300c00b401c10030a013444103500403040f03042d060f20f0b8000c951b207442e820942210044416004c50f44110203242002e49425041501c1c3c0f540380c09001804c40b600c1b40d4900c400c0d0344008039040d800c5921200c06104050f010700400f4080c003101d00700c0e8065a860350f1103065035541242c000480d04800d6420841c203591082d00004d504a000424114a014000200501c00d028111055030161101c00100d541c8036018023545d070407540014030a0320161100d03011003801c501a01003c50301140b010200e03600603190b10b0b024610908804111138004c0d8504001d050900d04070f00607062441c00d820300c2080034103822513900c410003481620706905c04402c14419600d0245400f0300600e060702d000c280c078010075901a050340040101900d101141a8603804041c8550205468072101c2101d107641c03d0991989000740605121300403000441c078407400e502c440c404400e40c0881c2c111160800ca04000c01e60400d4050a034010000c1c400a000070b42c940b0301e00440a0055005a1940001e4070350 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 593296717 1250 593295467 593295473
    0x7020102070b0726040f09020c0a1a0a0608030708041205070b36180a061208030a150e011a070506010b0c07120209061318080a020c090408040909 64
    0x1a0000303080380400c480e9071450242010000c044d182442e09401c0c0402050014042c2013210541d012522540c003130001351404c0040314000781d000034801d541c55105180b81d800114450030a030300c20350180e01c8603000260400000d403030240c8a240d00314407aa45d108004450000701840c0807101110000c0c0460124140c00345042c6040a4140d0b015401d140c00109006000407040e0781020803110f8400d01081d201108544031a1281ca0488403981d4080c1e44004000c800300c9c04802500d500c40c00303085001079500d80398280214103400c10346098881000200070081c1d00b524074480d540c403402107038446021303c0d840c0120406141d1014090b20003e0101d1104c00369004a80c24150744055030700605403012985c50701000c10700d5400410011020b40300314240095072a400204d440c1166801030403a11040d0b40d24010702201305040301650f00d03a1541d4610700c4503104030310007180410a01c01e8182a03038540c00c000c0003c0c40c000c030600329980b040c0f40240c20f01c00050840022101203c190900c00f040031000d80c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 593297967 1250 593296717 593296723
    0x60509180901090210050310060825051c020706110310170c0a0806040b010510270503060405010614030102091c030c051203010303180e070c061e02070215030f0a0207020102 76
    0x510000c5d001350340c07501c050103402d4109029610503085019031001481d9a66000ca9408005980100e0b030b24004203142e016003003014003440445402d500306185040c1099503905c580e480c04100103050954041100390402c11240901400440d0860101d411818901e4144015041500c0b403000c0d07081000d00d02120080043c0705100c049203004202c1640e999441d2080d5442d03100440b4215000103240e800440e030340c40c00b0741c07282c00e240c00580e44030101c0510002501d48007003210f0521407001120424006074581d010071405204509c1600041074051030821041c1d500032146085500c02d9005001c1d1286948408250b1000481d402144801a00d140d040a40304400441800b070038338061406804c1252581c000118100c0e0310039902c1d6440c06440035251040c0b0071403070284941d00d42220001c201600d01c10031400f040c850240b100018031056007101e2520300c81c00112150407542e00820b1001c10740c84e10045c244c00d034007806007451b4a90b04d03043c001035501e1040108400e06e401e03800b146120a5910030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 593299217 1250 593297967 593297981
    0x1090504020417060702030c030a0804020105040f1d0601030b01050f03040f080703021f020405150c0f1015120206040e1e19050612030f0d021e090109060509180901 72
    0x10340215611511030301d81610150603255940f029126080118807503600c00405c0740d9421002c24080c7d81000100b200071200b102c0c002e03005a04116041c0800b003100c2c0c4000701100c1c02448424501e1200100d41e1000802e184002004513042c1460400020043e0340c000d0304403102d00d52400c42066885e916898000d10704040524041e0140b40c0c041041000c0680008806000049000100502e103900340c42c880141d101354007985401c0070511404180040034800584042d50003d41500c2000003400001341c940450a9800c4004540b98503400d041015011715007400351010b0705600c050001d0f1078021074150321071031240e4104100e0203000036422843c01680d40e60684014100b240060621b81c11682220b2102081c1c18540380c5007001082491070441440404514000040d6041c05440070205440c0e801c00c2140000c0c840d020005a410013980801100084540c440c0003600c42084000040240703505420441c140802003141c0884d5558011080d8a6003e20340300303030f0b1555562814181d01520705 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 593300467 1250 593299217 593299219
    0x709091a0a180f0903260c040512100c0f1214070503070c150903110a0302070b180901030b0109060e0709151b0b01030611180d1a1305070b03071b02010905 68
    0x40c0c1348112041590215101d4459000d03195900103c646100e00f03844100f10a68032182c980d80100f1082000e4105a6809600000c1c82e200344c0b1100c2040d81059000d90701030041c0080041d45100310440e100d5000700341d00500c030b4072000c41004640b5110380d40b0421420050030040038808080b00040107944a241d0b200a00340d880002011000700441210010f8140801c1c11004105600076a0780b034000d0014900510306c1d010390040481038a44403a56615900c10710140045803803113012280301d030303c41c03002c041e008510858640d000d42d850400c2c6441110050b8104694141e4030405100c5055070200c02030003501c1d0520b410000041e01550284d82d000107080100c2c400310b850048000900075040b82c4181203d0140409211b800003082c505012071003815250184502e20310035039038250070000e10003035181c0d100b103103d0f09003612070400b110540ca0b4100c8149850680b80c04a80d8100301090240b03000900e0010390450450900071b002415806010402c00c0c0d10348480c0d54000256072040750b0610090074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 593301717 1250 593300467 593300471
    0x501170a0b131506091b08040b04022b020f060403020a0329070c150509150a0f091b0e04021c052a1513051e090709091a0a180f 56
    0x501022040070b0011445400b50319441e102030071b445c14826a40351103a80340c0d203547d000401c0c0c1d11035407405001200500181d802800246e21100b001541110010b410101030400c051711211503c10002c840d01c00c4c10160740954801d00003080140c0b00c0e4410790302a00d900c0f032061401c0603664607400d0140307552103e2185982545c0018000303555002003c04d9005801045500e9214450030110800d4660554601117598818103603504080300f181007480d0003c003220f50100d8540c010341240300c2034480c214003c0d100080305103190024120780c0c843c2c05000300440703803501c0e98900d000c0d00020022504010b12a04010094a09104000f002d120703984c0d2402c0d04599440f49001d48003804c1c8458aa85c440c4180110105040060014a00360550b0b01080861003811600e50800d818814440015800b070921400322441080b1643c0d81d1160551081b9000d41d6403024841c0362000b585c05942c40507001d115500810200d01480751100600380040e41c0b0080200300710100c0b006800e1008040410651013254 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 593302967 1250 593301717 593301743
    0x90a05010c060b130902180c0405060c0c030d080618010305030a030e1c02210c03030a1e0c0305061f021216051002220f0603050a0207060e0a02040501170a0b13 70
    0x61740040c2e400c60081d00e000e50307c280d21400301c1214040982e00e0703071000c1d4070911040110b0726001006042401c80c4500356010000003901103843e010104124102251242d002c021003402c20305034024030905000c5014059502d140c41d05a1a032240c40c03100c60805458022000b901c640c10061003021603660781440c20403417003c40e40252904d41002114813a510449070402002c04000309480d004020702c4007561464850400010041a05100d40040640b10440700e020711420f611944022034a261000700c0c6e6850300004000c0710134050510036881c0600c210101d8145075000912210350192a0740d40b40d900c40400c00c00303a20114100000404601c10328001080110042d0040c2803100a000b49010724141848012400c40d8031500403484003244108007085003d100340c200c030f50001145200140340080c180c07a960203540301100140c1003030344002610021130402d8801c080c014203000090405a15690307000c070b500c0d07040c243c101620a507070140c00709100a6040c00810303080350b40010514a40 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 593304217 1250 593302967 593302999
    0x7060e0d02010f050705041d0402150f0a09050109150305060a0807030602130509010602210412060c0e030102390105070f1b020a150909180b0c090a05010c060b 70
    0xa03102c0c0310108a800c3c0d007003101140e20300b8000c40070b0b60107503449604004006012030780e84a0304907000800a82e070041c0320701c1c0c26400c5810040000c012015000711103d5880010110203040200c0303c0d40964100000c1e120104a621041409103c10b0002e03882c021407e52504000940040f0032034200c88400e0127154400010009260f00811004503528411624281c0e01e078100302001750700344952400f50f00460300e80340c59000f03040000582d50780700307040e210300b026103504440040b5030509030111541c5544001c80c08555800c6080d1110203401103000703501c2c000100349217034414000345050050b5120304072080034503500c00e81d0503130403d10ed060008124a01c0c08140084c0301000d0030aa510104400619114030313003054001c1c0303c42d62a0050103144085191030169420005a0034100c010490f207060f0201e03404401e0b00400d00803444080d0b51602454031400e00310071030386018080c0098581c0800c081203094980a1a54046038404d007040e00207020182421009071410034005a131145802c007510b0301c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 593305467 1250 593304217 593304221
    0x90617060d1704122a170f060f0a0e010b060906090a0b0a08040b0f0106080c090d0209010902190201060f0e1e13060b01080708060906030304090509030909070212070807060e0d0201 79
    0x340c0c3d001e142522812840d080c0388102024100840e018980e0381003000307001c40b08641d901c4009000c5411b0455007054070503140c450070a08265481c49801c4000c07003d21035500c42500640c51440e24a200030042070325040300150700d511403400524020540442c5004540e89c0b140c04080041030340e0000996100c40b0070800800d03c1038222000c403030340d20007500400d840003a11400d481c10723111191039040322929046400079594005040850b8000450344140d00161150001039000704904000980c80e480c582c0680c280390301202d03400008580c5070500c1007226102c00d11214084500740c22119202d504c50f50141c80070841d4246034100e040c030009092020320501c4a84500d109809550200503180c840c20045800c41e1040e00c196000030103220101c0c281d40f401c410165008100142260700e00703540c400c0b034501030711000c0300d81985a40011811003a42c2c20300744002648a0418805001c5e00f441c40e4842c520540903a80d400340c20b980c404292542002480d070b228400a8440d08200e0781603418014000780 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 593306717 1250 593305467 593305499
    0xd0504020307080d091208090d1520041701020f130518010b0702100207082b0215040308060a0506040b0703030605121e030721090617060d1704 63
    0x10182c8500c800c0024044808201400f42d050300d5501c1808092401c0111020074030800c0c0c003550100c008110080d2282e031130780701492141e8459140c2da044440e00022080403616004088440e03841108403201034002c48200315020380301c071401c12000e109440031006009016040d07600721044400580b02c0465038408100d041150300440b40042c41d00c2441da040b0216170400c0c8602201e8400c00d0003501d0045c507054540001c0140c03d4812100c0540c0d54042c00e500d099952049001d04890f101207a6408200301500c4003000c0019000800c0d40503031110740004684401400a41007004e801c010070010b65402024800a20b40108616103c5880b404441038075070000340c04502207860050001600e0410301c40305d8100e030405101a11001d0701120401d02255518114400e240c081004210b0010307900682038506030003400c01075115900380d264041c22804403a00030030140a003520044201e4501214855030004099444d80942285d9240c40800e0050690703820404182c0400c0c0805c0000c03a541c0359072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 593307967 1250 593306717 593306719
    0x3070512030f070201060515160507060c053d06051005030106080a0902100e010e060d0903080c0f0d0c0c210f05070b0604020a110d120e0d0914150d050402 68
    0x40d82d0781d00c41e4101607007210142c0c0b00d900d412552159001c012034441c140074007400080d102c000c40c5500c0aa503682410038a0f40d030005c10209810134180010302c0410002e00c5410f45152880408008902d6001c03000300800a0200c404284078854400e40c6070010780240006190140024503043c2c0110000740141d00240500f600081003c80080c1600b00380c0e01950b401c4a4000d004110824607a040c111001981514224103100b80040041ca00d515824006d021202140000045104581c54000c011103070140901e4200002804100410920401100e95001e500300001906851134201030355140d00c003a130301410420303500f481c1101c170320f01071400d080103070685907200c0741e0103109032805032018002d490000c0d003810131840c000b55140c03c1c01ea00a00440000c0e0038001c54000c100008207181c030207880d0422002511081c0ca0b07074454a828000d01c2c0c0300c0755845016051400b99003200a04016840c03040103007000305200140340945038003d0301121850a910310550302c51a00c080350014180640d412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 593309217 1250 593307967 593307991
    0x220306020703030b12060403140c030906071505010f06080a02030411060304050606042f090a03170a020d08060609130f0603140c030a05060c0c01020f0a081e0106020c01110307051203 80
    0x10b484917005c00f00391113108650540302c013454114401d03d21002500403110310011880108008049562044d01400b5400d1080d1805105208500f05e981d081e104c041e4040216005440740602856070001c002c2640000c264000680702da6490601c2001ca2114000080d001180001800144000410309078403401e01640d00344a080c15441c0d94104034084400c450700340c841a52704c2d1014040a41c8001c102c0104004c0c0850580b944a0f20382c50f01034901c1907801c11801c80001034540c041a0184045410f050190800d00b04601c1c5c40008201c10b841540c184c2c510a40c1c020401c0300c4002c4040d4003e81902012000400c4400d46a1410711014003584a1404040c824000e040041d840e001403a00c1c01258050054504ca4803010102001900b02d0b0b01902207954003480000034000381c58000e000040c075903603525101402d00224110010015041440d800304ca00350042c05000c0e00090000c2d03480001307180c8a001032590b04540c40c10360003600b000510900801030380d01a500c1401c2c0c0998040c080065103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 593310467 1250 593309217 593309239
    0x60a03020937140607020111120a050301061107030f02091f0b04090b041107140a021306091b0203030610050d0501080319030606020a080d1b110c040b0303220306020703030b 76
    0x90f0500741c0c202d150956100ca401c0080d10015441101e1064140d40c0c2c0c1c408a0390f244100c4410700101e034201c40d07613034400110084010030550741c0c01500c1c100300f120740300c0c042c150035410b544426210480b03498003e07004050500102e4041d030180103a00b42264582e8421806141d100c040500c21a031140c403da800c82c900b0070215200500c1e091145040c4000382071459442d01189680790005014050054146070082158030405602c50b01c0740d40c41541184000050142c1c00d204450080302d20042101c44040c00020740c81024540010860342c0041080b240174038540e0640d001142c2038890100f80c542081e081c2800055040c01c0000502000341c10042e410440c40003805080342290064441d020059002c44604808200110003c00b848603092101085501300c041c3c181506001064a6000042c110790701c292402c00140010341e202c00003201e052080d5905440001e0380c070300440a5809481c01e5210802400007040d589031002164002e00035034489107a81809002000d90480c014080d1802d052 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 593311717 1250 593310467 593310479
    0x50409060b030630240f5202190c060305070509041a0f15040902160209090a2001050d0e010209030f1c0e060a03020937 53
    0x20b8038841c020160242e40126002d03800300fa180100d04200804810310680c00c00000001400368030000c90042c0d80444403801c2c009110112000300400d280032800142e401e10501e03101d00b007a14460203090000544041c02d04003010842d1a080d4268600c054a680c801417000e050000034950020b0015000d40d80700c80c081c10f0100c00084500036000749820b580c41c00600c4003d0080c1e200d00c0d04000d0502e061400c0800300d0300403508540c0b5840d600c0c0c0700e0045142c0d01740341d0303407406281071850560306458100186616164503821402540200c920458010443c040608844800d85440640041c00c0134054244180c1150700d8400190083e5980305400c1d4a07408060368001300d000103600180e481d2441e181407145008000c110554504c107540d5002c02104086036020000e41d4400c04840e40900044000703c01890043e4107d5100300301031140c148144000c541d00c1d40700f521842003440c2805a42d1f58080c00000b18160301980c28003800e820b504291000b00e04243e4a0001016115201c0b06040740d182c00c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 593312967 1250 593311717 593311739
    0x3190b1f0803070605070c0f0b0610030b0105090108041e08130603020708040509070c0c060504081005040c050d030c0c0b0c010b030f060a1d010609020a0f030e0706110c09010605040906 81
    0x2000d00a01c603401044004001099644429849400744c0350040303d50f846540d9024128140d0501550800000007c2c04920725001c1100580213603103080030071464291400203480c40c050020090705200c0c01b640040c0c140804000c035a2280c0c0440c2c0480e084451191505612540007200300d40048500701202040050081c42242c1c02a80c1192015040034903100421041402c0100000100081c06e203807440000c510308005006402c041d16829161b13410945118a40324000c0c244e41d003594140030a02c004100b001020005442c0140d40040c2c0000c0c403070030f0584a606140d0b0009004035640b00c000240740c60b0b514080c1101c0c40c80b4800038003094a1250805984150840038080da0703811081c0494002c60465004022056005140c25804907031588650b0854510780d0042e0040c513000a0010b6403d5401034040f0a01000c078141000421060001250360701114054a018401551015000f070b107010000701c829040c1c0201588943c1d80c40b51f400600b02c3e0050301c107140c54181131600114215081d0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 593314217 1250 593312967 593312969
    0x212160b070f33060618051507230a03091d0a0209030114040804030c0b0301030f4205090d0c1e050607030605030606060909070e03190b1f 61
    0x380c9100b01d604642c1c542c15100f02003160070141c6a4540e5040c0301c10f90f03500c203200402d01c400b02d1100098807860594050b10420000010514000003400280102d50b91640790780c040488070075850f074503601607241001165118100c9000018a0906003452240001801d0f6040b288641d4900c2802ca071388075041070703842d0b884810882c0c8041d44c100c0052103192165010345280100240040756928518004504851080c2c4003520f280800050510500403004450790090071480b00081c91907141d03895020b00411100342c003e1024140c14030b0350348003448010741907035044028034068481089840026003901a0f40300100082c0d03044c000050105100420001c00000d620b4940e10100512503071031107985980e240044000a5002040c81c0104108001c028895000c80d100000c0c0c0c00d04020800d46070010082000d4401c540402070a002c580b5210551500003442d030515882002c04100040d007080e03005007004220a9418851400340800c00520710b00442c42044410751f507528002415400c8562 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 593315467 1250 593314217 593314223
    0x60603020a020d1809090804080d09061409060912030306041b021b03010e01110a03110a0c0204050612010e030a12090f030c061b120b0a0524070212160b07 68
    0xc80f1542d00c1045015941e043c1003c60b640f03540744e01c40340d16910124100c608000094945110205080c40480400c100074600703500a400d0030243e00d0701e08200144103a601e1f104400e211100406c1101e074a40703842c0190303650441c005048090488003149039558940003150014421030402043c1025880442c089038001613040e0301400303181a241081004034901401c816401d50750f0b0b41d025410088080c4180700d20074506608042e41d600002c2c3e401000e07940c1201c4024415401004035984160708518070000c1e10354142c40c04281c07541d84200044843c140380a01c03041039420700d40340903000400800146503e4285445140c030820f2040c01300c50883d80c0c400d000410782e83c8034010210102e03014081e00c651507413040501241c00030000c141d0300c601c3c0704190803a9001c10303400b0844240c000c015004075203024509695000b240c0d8509070010b00202c4008165955000105048114101481c0100c032813068019004203001101c3c0ca18541c1c2d01e5901080c074040c0003c1418011a60180102c101d46c68160 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 593316717 1250 593315467 593315473
    0x4050c030a02090f04020c0109030207090c0806040f021303121101150902030408130e010510170c1602060301030b0f0708070c080a0c0b07210612060b0415030f0204060603020a02 78
    0x560740406100030350200c01c940394082800741c0342d5422540d83d80028184001658008511a100d510b4045d240000d15000703030108c03c0c00c02e4030111010742c1c0480d1040d4040c030116000b003010541039014100034440c8221052412007804c1022081c0405045412003540c010354900c4e41002c86481c8040c2202c000412107690f441d07000f0400c008220481c0c025541190103030381440d10f4032540c10350040110200f03038040c401c1108041c00412240c984a0315440c000e03281800d01c0b40c0c82c1d032100600310f1800e05000700642c84c00c22000c241d503032009111841001c02158064000b50b0399507100d042c00400640708030743c900703511105900014503241c442e00480d40559001e4030344102a44495403044402c0e000a40694204012119010080740200303500c00d00500694640d41ca1048003106004059403039401c41d0070780e860801da800c2102c100e0014044030b03c107400900010307024040c50002800b908501c11082d40005160f0b2010052004041c04c25020a1003201c0c20002c80e45e40d4042a42a07001e1070300c1540241e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 593317967 1250 593316717 593316721
    0x9180601030b07170a05040203011a031c0216060e04060506040602032704020d020c010b100906050f13170105220605100302100c0326180c04110a0e04050c03 69
    0x996003240301508141c843c181200b1069000184031038900c42110071074145e58031303401032105504080c03050f9003e000c4030b00130100c101d071805000700c3d5440843d24200001c1d49035907404161418403c0c0b020042402d070084441030305a5407048028000300105018905c194641040018613142007400c40d81186e005030051070400c0a0500700069003540c004800e85003030068002d11000e81d84510040c02003c86014006803149440c103d041e08603161500311500420b004906800000c1d04400c5001c112411858401d5850f00e2403060341d4024040c10309203000d122042400403944e451418a400d03a05203118000708219982c0d40c0d45003d241c0440000e1401e485680f82551020070101e401840c3d00010035010340d0306469507680420f84070b03070b08000001c0020b0a40e074988020103038403440c0b00303002100c9460305000340e02c080780841c0d01c5d000c800f400e030502e050358a0900c4820003000703100c2042070100041040000801e030301c2081120780d0000c600000007032110040c121142c5401e1103810b0080c40907100030383c255 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 593319217 1250 593317967 593317973
    0x307030e060a05090d060203010306150f0506250b0402030d170c25061a030a081b070b0307090e0622050601020a06050a0c0e011704020d11100e0918060103 68
    0x1a48141986000c001c0f0400044040c0d440307004654540d24880c03e0016030f01c2d13240d4141a800c4841d1072241741241c3d80c01e900200810701010350510151442150b42503600c0d00700626040e607071004070154094a543c045d00c010184800701d41c545100300e000b0380c1a110303005044001101e6140c928490301025000c1c450120f044095108003901c2c0301c8030012000d00c058951040141c0301c281d01100100c3e18543c403845420440a41081706541c030400039002410003a40340d45e80c03015a070241c071100c01262001c0c1544c4c3d12004804100307610051410000644c0d890070070318801004178495000306000300c220f86010603080d080080d0072000d00c5142c8150030413301c0030860f44402510303000e00325904622a04c1c502c140810102c1c0314090241100724800180c02000c46401707890301e100c8095241c107000d07100c0c0d0b92002030650404401d0740310b41c2c100c410041c010003910301540854500050181c114800051707104645401c0600e86001e6507084600311015600c2241c00011030b010b10018040940201e4010000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 593320467 1250 593319217 593319229
    0x403110a03170f0c0f1011070c360506100903050618010e16031b050607062307030506150406020307030315080a0302101a09040b06040b0901170f0307030e 68
    0x180441035a2410701c0d00103004084d5141c003000b0301c10603d1580041e0300e01030410146108030440b00380c1e4289901d04000f01911056034002840c4218049440d071300384114003081c85c0c00740d9000c0c8084e6500e41050315280144c0f00c2d40c000d020445555008040880c0051500c0780190b00c03400031a54004001c0c04941c0e5505440342c010031050001030003c0d92181c2480012030703002d2002200404003807025542e00c51030b60425a0a2002840c11120940101e04051085460324800c586210382c018102061b5907900d5410350801c1c01500109001c1e02100d541800013607541741c0c100c64012103046401401e48050005400c083c2d2245109210144c0c0c0304200032000a0b000c2e4100700e001d00d146c6051503088507130f14001c090034144c0082c81200107811800b420f542440075840384940c5060540c8040d842030b160480410003150010b00b02230308841c18100020f1030b540e0346801214502c2c0c00503144c914107507950f02003040b0720030120315000ca2501548403a0185c01100000b46e4030025010790311880001e6002040c002c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 593321717 1250 593320467 593320477
    0xf050913080a020a0209070c1b0605030417040806070903020f0102060c09040b030c0a030b071101090237090e0c0f0901060c0212070b0d11180f0103060503010f020403110a0317 77
    0x3040d13004407a40e010143c3c2d0f4508110b440780d819a1129840c00c4441e18081c030304c40d403601500404108046009000303566101d4140c80e07105610420240b80b4000440311040e185c01142d0280320244910700070428071607484a00700d401c5a200340e64040d000052a030069031202000c60700075041c0b0006104120241c03515400c40329039a1400740c2a18840340d103900125280b00c10940054503480128000e00004030791080103500e24040701c100030050b0301e0b003e50010b00d142c4903040c00580000030b501e40c159420360810000300a60f4a02c441e2001c041581e8942781d00142c00709002c1511240180f6111700034034180904d103407100500042c01070318181e00b056002e48a0158014080c0d820040000383c1081401c01003001d01c0c05000005040d90700c84140613030241c00c0d9204115040070178801070020300d0803090001180143d102044554a00010f20103004800070501c5500c015419800d02680d10a0403005900a1040e640207001180451101c4030a20041c04014800101045080b181d45001d82503100701501e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 593322967 1250 593321717 593321737
    0xb19020d080708060a030c03050109051515190504020a030e0c040213050d050f03072109032114180a0e060a0b2a01051503060c040509130602130f05091308 68
    0x1078085446e6101c041d0702015035002210140c2d5600112403c0c0181040b03c3d0803102410070380c0c0e004628203a0348103a0800d41c244039082c051400880b0507504807580002c000040c2c00b0241c821525a009650b0003400782003030700314040f164081c1d4000c541c0b03070303040a0084603103d401c00c0d00e0451002d45880140110240f107214240d902d805040d4810b501e10300117100411310140501d1003030b4110110090b00f01e41e110b01118240c003d000c403442c410000161031400b00601d0030440c04880840100d03214058580d451100703011003003000c00280c0481e004013000329a0705040d030151a40604540ca404901901d00415103896511008101081011070145402080b0344280861000c0c1c41407840001034010800e908010740203a516070013000340a83d0224219441c99008400a040718146249800060301c92409807500a410b81000200a074100d02c1000500f113600c00011981e484603110640c1c090b9486009880d000341000c00000b40c1403800707001a90150340c411425400601140c1c1e071342000c03540245c0b910703 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 593324217 1250 593322967 593322979
    0x2160215040f06050c0d03090f020904050c0a0b04030303050a0612080309121c0f15090b01051903020901110d05040909030c020409050c2b0209040c030b010b19020d08070806 76
    0x210300100300c00c0c1038100408091302d41985030000c3c0c102d0030341400302000800c000c141c68001d50401042d03048821600c03064054400c03070700d680c43c3c904046040175582d0b0b40068015206140002d50081560010812039000b55010009600c84100e40016180341d0322452840000516802000c2083d101c01190840041000c0742c2112030490392902c0350340c101c011644c80310840b0310041903d00c402401101c41000d410300d400c0142a04025444e451030b03500740900b1880a40e200031031449a40250105d8141c5c0c3c501000e103441d8034110a0300240a03611080d07400c0d0006581c00440780b081440000c0c105040c0c2c00944802e4141420410740300010003200a06a040101d03e803485000758440740300b0703520f08500076001790081041350000e200010121886002c00c401074003091807488042d202e55900016030480f11966507880d5030511000380e41182d0005440070f00020b0000400c0c0c8008802080da41800304425180356110311302c140e803545020034030000820f03100030005800601c110381c000d60000c0000d041d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 593325467 1250 593324217 593324219
    0xe0304031209120501060f0b090a1401050f18030c0303040b03010b09041805060708011403062d0f01080c011d0108100b210c03070c0311010f110a120216021504 70
    0x501003d20359110302514942d5480209003c050a616103220103410300300986450b120300d520214030744403001d224040c1c00c5001000301501c44e82c8660304454110f00c4441800d51264000003404443c5008100014840c0c8a00d00a0407102d00b03020040d10122085074079260304503841c0070b080700326551140d000c142e803180da54445402c511440d603c29049080c000d070001c01891809150281c40c219042c3c0015004001c0392804101c10350380003d400381d01c0300c075406144c50080c010490024084003200d0f50000260018010001050f162400081c1214400c17030403035017040f00310801540c41480e0600700115207c0c1c103100a24040d4003036803045410020041401c9441913803240f001a21b80c0042940e0100c0c40805029410110300c01800c03a500300883d240d030146142003100007c0c00c0c004a8503001400d1014419060218038822760200000100b182d07414042000b500760740300701c2680f04000c07590111390b42070200001c1d202103100f17817030002c540c046401b0100d071615001c00118140c0c195200080e4403003004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 593326717 1250 593325467 593325479
    0x90a1a060c0115080f1f090228120305030609070e120106050a05120303070825050c0f060103050c0f220225020102030706090609060518100e0304031209 67
    0x4020a0088550800080d00040341021880492044d90008106a0162482c01500800455007844c90f00154074140e40640c1140c4408010b08601400a5801404821040100124805072018442d15100761005030ba45440980e480c080003200043d002400c10b01c0058240d09001c03041c1e80d00500e05080c41c41c2184409000201403880001e03030214165100e24082206050846045014220450b00303082200310318900990f40b400010804010001400049000040289800342c801034a030020071b11002110240500654805040c4414900c600307a05941500c01c040b40041c145ca501030080c00c00401d8040c03c1107820f2840050203580543c500251144409000d0310600c0380c244812000f5894102d003c9032801036030284204940181421a0078000603a0301004807641550300c40c000160305c060605200700205204000107151a103020244040c2d00d500000c0c510f2060355000890344520075440144042c0e480310601040f103584140000c0c40040d10780d0095040340320240c501300d1b0000395210 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 593327967 1250 593326717 593326729
    0xb0604020706051f0b090d080306010507060207030801030b0109020c060106141201030605040b06090c0a210513061104052103160f0516081c1112090a05040b090a1a 72
    0xe1040c0c00380010142e4400f08502c0e400781d04d20014003090a05d2401c22103010701182e80c511640c07000524901c000000244d0f02d82c061f0050380c0020380c0060045443d04458900500303991428001640c000d10000c1c00060f07881c40354000c4540c44013181e005000745034600305013620000c40c00104106403110902800d1440c0040c446031354000d40c01410081014241828089826000606014041d40c10b002c10000321a1000d0102c07030b085034039890a2940e421006586040300c0c070800040440311401c240c1400080341244020244d8140151003c11a2016010100d0b50318811445030603041044401001c085d0b900801000c00c80d03100385000e4a00d04803151600b900030740d10511084541440030000082400340c104000d141051001948000c0c06040c010300c60fa40b049858011f00306000403003542611944252089a1151006c6044884c1d168045101d0882074101016035800351641140009a5240c80c0c024018032802c01f51404080b501ca0f1042440580050784c982070b540c4800100c12003035a2986 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 593329217 1250 593327967 593327971
    0x9030118150f09150b36150a032013021e091e04020d050702030a0e0415030f030207080313030525061202040807120303150321030e0a03091d01120b060402070605 71
    0x645036541e88204c8180e1800e51900002d00107d102504c040b40c2103115454040001c4190798004440706c6d0010b10b5a03044504003080300c240590410200601b141d2410301640140c0781c40c9803c0c80581e001c41c10005030045c07190103440c0043d98401c10080d42c8050b07040e40c40403441070048010780050f01e8684a03403014400d4441c15198940142e00019007080c200380e1109a000b03007000c08880030307c490740030401c2209109400b400080c11a10700d5401c1d5000b014020880d000081c031a00007030365103c0302d10340560200340101e488291f4190040e40c0d4641035010707000106511249104a44411090805608590381f41c203001c510b50400f64201300201c0d0b01c2208100c80d00c01807111500c03d10320303a4050714000303080d280f039511105417019088009100180e00713108006000500d4800e01034040d040680214080d0130110001e030858040d00158409043d4840a0705040d43c00880c40d42042c8090310f0362803840203000348200d4014000e2582500001441201080d0b0030890060025041030015102c1d20121042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 593330467 1250 593329217 593329279
    0xa06020f0702091b030a0b01030b03011407090902071a040c030f1209080f0705100521010f0f060806060d09080a170714090609030118150f09150b 64
    0x40803420704214644500040e5101c04038505038040c44c04142410301442c04064022545142c0398071030421164800d40c080d120703034000140248241d20030480d4070980b142052f201d150005400d4880030520314840e0080f543d03041c2d40120030004075a00c0285d2b030316501c2d00103003040f01da070701030440000049406188136080710b034011050900b83d80d401301d40c05024944268003402c0b464100e550482c0d044034000ca880307421520b0545a0200e200c0e2014005c40b07442c403e101020111070810068503900044500c8544d040c1e80fa40c00c09890020f48032940d42c00c80488074418400040d1a544c0007415a0922001600c0c4e40006072102160f081600da68003000c1d038020340d01c0c14000a44103100d0000403e645c41c51540c000c11142070109150740160131006103449481c080600130301c000115168191025802010f0520500b0f40c0e180c08002149041615410300201d040d070b4050030031803c0701c0c030346c6001e10804810660000c90f44d1341c44411140d680029080190b1410b6004504024541245446010001d802d0752 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 593331717 1250 593330467 593330497
    0x4030308070206060a0e070e150403030206010801050c1207300f060e0c04030b151c121d1e09010603150b0906030c0c03071203020306030c0d030504170a0602 69
    0x601220003d180040041100d40b00e205400010030a01c61400d114582201880c58503400a00c445000324a044110034141540110002000401d00d9408501c00c3e050f507402500a0200380c0310070700d480310a8001c03691108254010140404c103900d011351005800d451410b00210f1701c07401c072540248032109103683d407240d0003511107a0901460615105004c05002c1c3e0b00c00700c40c0307a410000b030a01d41c0380c00749001c020b00784281100030800c1d20520160071100268000c103d40e40c0101206003a4070481454a4101d4072141d0407400303d81c0c000d02031204010304040b002100c1524080200401c0f081c11728030a03d0307010030002061101216164585c42d58007a1000341c0340400c0410590208502a040c2c1d980920040c0d1000c0c0a802440c0c0c1d2040f046076041120302081d9622004003040047c114815174000801044007508003050454040d00518420b810031070960300c03c45074100a01c813038100c1e080802000280f0411051041401d41e4884c110024117860883c2e025594a40c0c4441c201d91040100a103440 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 593332967 1250 593331717 593331721
    0x90306062b0b070e0904050c0609030a050708010c11060606090d11124836010603050910020c19051b01020f070302060918100303030c020c031009030e030304030308 72
    0x3c0c0d04040b0841e2003050a9400d01414a003036120141c0b100c0b0031180c842d108850010385081265010801c07980c0303040e00309081d07500c41c0d80e4030000c0d54024007800881c40007045021602d2841110003007016413042c0c202500c01c5241c41f801c203041204210307401c0c10407618807000000c0b040190316900303c0300150308005002001021540303000c421044080320342240751030810a0000308a1510f082c01c1031401c0c00a42002c0c6070f1348040000094804240c4062800803007403c031a070306407840c51031400ca0046c2e0311007002403180d0790322184102c1c141c9004485004050b4050f4a0300701618010750b0050a0082140040d135030000704203e6003000f043e02c01803013a00d2650000c0300c05c00315002010800c0d035940c0001d000404141c85940304541c0ca40d200c602c0082d100c0c40004c203142600e81c840941401a240c04110300c50110f04d00100e40e40c032209000c4c0400d500091400300e12002c101d000041d800702e003070001001010703140b10421000000c1c0210002c02c50411440b04007d0303a0a031401c2000e0005503110341c942c00c203a8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 593334217 1250 593332967 593332981
    0x911161208100302030c12030c1009060c03051303080a0e010204080303090607020a051e0c120102130b040605120a0b1503010914010303210e1902011202090306062b0b 73
    0x180409040c2c251181c140d0001000140d50000300c3c007041c3d4100362410900d001c030000d1003d08501500c0d0000d01c450090380a40059628030f9030106004503ca240c040040042d203010440031184100c41001554160140d4000441e020314151a80a2280c82000c640702e00064501804da0300309a020300161b0380040180000a01c09001c95070788108984001d14995416445090f9220a00c541c0e030600b0042141e41c041d0582d0013030090782a400000f504040065401564641c001e50006440d40c003107000004001c990003140c0c004032801c44181e07a5806007000f0000d1891100030380041c21682640d82c0c0d0f00c140c0d58064481d9990081c1c28841150381c19146d41c50b0201d0306050310304006d41d822100600500520000e5080f0304081d264802407004080048013000c1d000005103034a200d841c005104c3c20002c000c280308150154031041e4400e80c2d5000440c2e10400018042c1d0044a00b621b80c55001400060003508100720303420302c07a030440030901c61040201001805a4840c810007601d44a07a088208000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 593335467 1250 593334217 593334227
    0x4090209120c030c013203010303030c020706020d030221100e090703120806031906020c0c0105130303260a0204030b09030702091b04090e150601050a080109111612 72
    0x100a04041c0501120b040050009403100740444d8101d050003000810300b080c008035100917001402c507810095070a9140f816860320513401c2440220000303410071611607912440481c018040710b000d6002811804c81c18101900a504202900b00f442a03a000e800b0a940303003584007642c050605c0b1282c0c0203089042119203140540c004014814a6018807401c000240041e010024035101600c0d241001d07442d02800681401300400204607200c51050440f414800250700030000c0105d88001c0368582104040103590074080c691558044011941042004c240614001200080418000403550b4a0000c0302e04c00c51206660003c000c030350129091080029a83c04590003803100002507040c0b2000d940000ca0144004140c40100300500d18030007000301100703054801510b0611400e00200307219031281c40e9244014030003c4649401107011034601d50080b01100d0045200d9982c0507907aa090814000213001400c0703e4080900040203555880380c400d898001d50b281c4540c0903401f0140e088040100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 593336717 1250 593335467 593335489
    0x3022a0706140f070f020d2d02030307080a05040f0609031709062710031b05130e07090b181305012105031303030f080c1306050d1104090209 62
    0x814450403007005650103002d00159030300180610741c0f81e507492406180030103401140440003900918402d40c10402c01001400e0421701da80341d12040001c0d412007043c419410030807442d01a415030810800c85c130100340e002c0000c1c0381da0091800c00500d400c3d5247c00140e210705d00e507400b210015006007018001c0004480894000c0c00c1c0244102d4200850705000981c544a440100310382e10250070781d2405d03404a024100034a442009040d249181303e1103002501406c10b8a80042852851003034046030f2601880c1900c80344a5545180007545040030291011240081c2c402c0742803014a4000080c09580d41c00100340c4203007001003400e0380302d001000b806024501c20104c0c0b9150350600380140005043d01d100002c07080fa50042207603403286a070504a08511850742100c041a07140a404428903801c40c4201040030800c3d41c444249e6a10081880060300502d1800c2091041800d4108001c0e8450700140800741022000000da640c030944c6401d500390300a920a0300d0203600418200020f10f0840c808003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 593337967 1250 593336717 593336729
    0x11203030e01060e150406080d110606040e030304030f0201060f0303110c0a140105091c05070503150601090608090c0307060807030c0c02030a021c0b1003120e030d050a03022a07 78
    0x84145410034940c00d0000c00d000308070411120440100c0303005e9030f1311500040014010300b01550b162240640300107103040d1850010340c025110304404118181064822800d15200010203581162075907541124291ba554180404540d2110004500d28185031040d5005610940383c1403800c2c0c44c0d00c01c004e803c041162074035a02c252014841001039080190010010740750910308580c2c1c030001d200c0022490341c540350584000d000b250654108112000601c18141c507422012614030802e03110341d07145130341030407603186002411200f01040000c1c0600c5c01e46800001800607903160301c6240b00071074540501b40c3e2005000600f040c0602c080e0329007510a5070300381003080c601940340c400d040c1c002c079580b0780c0c000d803000340551240c03208020200e80c1c010714130000303d0340b18004605034144824841c003150010300081d18000350409580c940c003401084400d41100b40900070300790740175490340c0c00d444503080030f2044000d051b001c1004141d0408540700d410b122070b604607002050b2091060007d890100f10350450 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 593339217 1250 593337967 593337971
    0x18091505100e07050d0603080703032405040c2d0806060901090b0d020f0408011a09042003030c07090618090302060f0603100507030207060b0f0109051c0209011203030e01 75
    0x12155840e1030a00c070700c05651000c8142d0405445100302216641700e015580460140f600c2400b0041191000c0100030307460090b40c0034821140c2000c10b5081044016501d07403203850080348100700d9424140c05c0710070f8856481c2000d1208000400b0b1080500a818490700c102c0250064120384968201e084190084400c0d904903003002200e10001e0180881d50054060810010076800110001078044907016251412916115a0f9070b01d00207020b800c01221188c141e00c43d0103120300703182c101040d086d44141e400c000b03000c0b030010548900030741c00016580c8094142c001042046541d240420041c0018214020300103241031806100240c0002d5056540c56110f0524400e079000c25030010700d4541000e4001d84109171a2524400a0720b80982e90300305440b128100380407c1810740e01503014054060203801c0c03e10140c24001e00300040e60554451a1f400300c0d0380d421051200f420850480c4418005481012504509507000210b08000980c802c1c101078101031100801c02d581805410f0120b060b607802 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 593340467 1250 593339217 593339221
    0x6060611193f0e03120706090515100905190e0705040213050a0b0a020c011103070204050106030c120e0304090b01050405060d050105190317070303020d060906150e06121018091505 79
    0xb510740d0152100c0000d405c0e4042200028405980c3c4031011950b4403104851440000410704600d00303004a0302481c036172012082c0010000361a029042c41200c9a0021500c1e800c114880c08000304400080200203228010001c51a07450f47d00c010200240840d114200302450101001901a19900045031400307052101c20b150350340020711145c00e04002d08264814041501005242d4000e200c00694824208000005e105406030b20141d45402155980590005130000d0300080d5188030b85e007140b8a9000700010000703103846504c000c0c10403505142041c0303400d03520300000d0b0143e04240c200f0110329940f41c004020300d01d05110040d800001c0c5c0007816a0040c5540c940807600500c5140300e4903d0840025404100761082d41100c0300c900032203e0411580e9201c0318400d000700001d00941481d19080025420050301070040c00d004010014060791802c11402545540d00002038460241c070340c0c01c41c1c00459a45010071000c40380c0c6100340c070005560f60040c1030030110300e90b1400003025614a4201 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 593341717 1250 593340467 593340469
    0x705040c1d060702130c030204050108060117010608060d050a200901080a0b0c070636051f110703020d08010e0f040219080f060406060611193f0e 64
    0xc4500c0988000322102c0b0348400a900100e00c14180340d00100c0d06180c5030400002c00c050705036000e4819a10700f070742c82001c650758010054403443c0400154860b00b00307040c8010850b8520507012150b0046001e00844008501b0360b0303865141c15580d0204442d24001403140482807417031814080d0724130204403000e075065413504d0480d42e1604008030001d04004400c03000100002510030844045a40c001010001040081d01c00101400d110340c40c01c0f84902d07900034400c2c00c008005003620340c054205001d005400007500c4841c200d00201d40400781d015440d002d485581d070781c01320060030b41d85010790098000d41948841c000c0c0314910580002c90039840c0302081c0f1a4400a410340d90b40d0007641611080c000c0c0781e0060f1250415040c59000d50300d0340c0300c0c0c510781d0080c094010800a01a44c4611021701540d901c2d0201034642998405810078a41e2101c04201d078061100b2a000c40840d000d640340d0318221007a21402001da9215403129510f0412804681c4240c9031032814440e081403161500902582c6404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 593342967 1250 593341717 593341757
    0x1e0507210b07180902030907030c080a05010b03010c120b120303160e0411040302010c300305090c010806010813080a050304020f0a0308310e060a0801060b0304120509120705040c 78
    0x100070304d410076502100040340c3c039904000a030080c1d038006042c1007a00c1c1ea90040d141e0390f100d8000381201d095007850117448160805000d10400744020b42c843c3e104111403800500b0050050007859030f4051044018007450325000d200443c02460041c1c80000c0351a108440944400720030340c030340ea004502d00444c040382c100b10710043d107041e2607091800f12114110303800d0011003010b102d1048004133003142d55480000d9540340c0030310b541d9000c0da1018481591030003100d076100c840d440511030205078070b070300014281c0d072080fa9640da105070580c811120810407503c404889030841c85902c40071903400010b104c203507e1b1560344c20490b01401c07514411200e08541d9410441c2c00350b40304200d103140300c4100c03150001100c401701c2e5090000c0c19004e91205a0340e546a200032241c1502c8260040c001d20300049a528410700460098a02c9d10707460f5451501e90360345045030500c4104684041000c24840c0c070001e1ba0701c050594a5080c6128000c044181c107007802c1108841030b604040081c02005008240505c07142 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 593344217 1250 593342967 593342969
    0xe010305030f0306040f060e07020d08010806010e0c21010608010b07031d0a0503010203090606090c0406091208190c030306061704061a0303120a06121e0507210b0718 73
    0x24014158030380e1036100c0813030061b04200c410640e0603410640e0109060000c07018142c0319404550846610700c0c0a6001500c001c1170a010310762168200d0360042c01080c0403000c086400411003040c40d03190250b162004e83d0344501c455094140d02500034010010f2941c000041d40c0500440d81a1910700961940c0252001c0074000d10001094203004076061701d82d45080303100e402040081c1c020b41d03503860449242070320f03110b04a58051054150310049903c200e800d074291020f4850a4035285c40d4582442440d1a0662842c601159110420041d440ea06039a148805d00300c0e04040e1503078040d401851401409407102da420a00801520400d103020780344061003a0380c0c001e81c100c0800202c2c0c1407903a03441405030a14003061600751100141103000700640c074040714404c68421404001c25915007260401d115441e00d0b010307040e4004082c2c41c2c6000e465034450035a03440e204100316140700350740341140601818400914444600e405080750240510800d443c2d9004889242881064a40d07902980382c443d20b03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 593345323 1106 593344217 593344237
    0x90812041809020d0b0c0f0415080601021b060327061519050f030109060c02100624050c1f0c1209020a270903050c070e01030503 57
    0x254494440b01c01d40c000c2c0b810b9141009510b80004004000d000e0154046041148100003003040005100400c0c14401c85251a1358008010300441001009141550450720440850000701d450b403054182003100d009460740c0314001440e018000b081820f44c043e1403c4024240c030030b54009585486000b028500700342284404080c403215040e1344400c134040c820b5015081c00340707140507904441226400380001070b00c1d408680351102921014282503005d038219046e003613a030407400d0148000bd80388881868800a0401e02c151001c400b00c00ca001d01008004901440069014040140c2c44e406e1800d14a07203580018030f1002c0203100d0300c0e20340400300c2d680c00d00f69072401c0e0b2140103413030f000c40e001418940001d10b81580c401d03106001b074403451429481403030002c0320001144102c0000501907521151a640d40d0b14183d40b42c081e80b81c01c00f46200c8172a10040000070000000c83d440100 = true := by decide +kernel

theorem cover : BRFrame.Cov 593165467 593345323 := by
  have h0 := BRFrame.cov_init 593165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 593165467 ≤ n) (h2 : n < 593345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
