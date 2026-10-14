-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3425
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:37:14.974635+00:00
-- url     : https://prove2.me/submissions/afa4716d-c3b2-40b3-a840-140dcafd7d0a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 615827338 ≤ n < 616007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 615828588 1250 615827338 615827347
    0x1315110f130305010b0901050a060315030c090506130e121b0109120e0a0f1203090906230303070b0c0a09051503011d0f0a0e071805040b0a05090a030c022103 69
    0x1000f40c00c1d906401a04c0780102d854600402903601c074542d254068134454180807883c40015111509103602903400500082e02031640000c10781100d511550040500b030700d00a19140b520124002902c41c2e1300842d180f25401060b0b082c11f4000d1150103070620035481514840126100c014039402d4402140051341c3c0303902480b40131070303049400008002d0f44c038105443c2c00075080c0c9020000120580b2034418003891101c2807a60008141c4243e0140d0050444105c04102c1c1d183c8030940e6181d42031502408000147c0c85c0001d121039403030000180ca880e6076010700c1e102c8980e070301c00000240941090290301c0912413805004100e5a4402040031405401d0f10640740d141c0d0300d003c2c200501c00146c000b4000396449948240240008000038a59008a51403c00b07e1000e800716040c914000d4198804401d00031088001c140c82e034a250083d41c055805001e12254030307100c04049034100d400c2940e00c40ba80d0741c040e03442107001a000304801c540d0140000c06a000e00d00640c004081012044094084140c20019 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 615829838 1250 615828588 615828593
    0x10c0206120438010501030e0f06072304030809041503051c170f060f0d06050c0c01110301080c010c0614070c06050108010e102d0e061315110f1303 65
    0x1841c140c00005807a030625410440814003900003106024546c1003644401494002000800004400f03003d03a10403180c1c6450203281c018400c2200035640600b140702b480042c50550145c20941c1e091300c0c0c100000a144c10950f0080000600d10140c00c0102d0300c1707801d0f20001c0400d00602001e401141c0e05440d07500e684541a100900318141180c070200d00a5a01050000e03600b00c049a8a0f0721000940b041e6840104180005052000a2100500300c42c1070600304803200c40c40901034800d24000100078051800c02a01014440c0030900480c4103e90140103190f51540c801c4020420391402490001042900702103404c010650032215030001c00c130761441c1801008068890140109800c7e0000c110043c4d04801d0031b511002c9000400310718680310402e9a1000c404034210084034260707030b41c1c0d2200c000c0c00c1007a414058010081c0c20a0140210130000d031301a138103084040152a8462590388000310014503082c001d010b40a44580c0080c01400881c2c0d0341d05421000301a41c20745694101055072072b52 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 615831088 1250 615829838 615829883
    0x120a0306080f2812030c05091011060a11190e04020c1b150d050c040509181b0907030f0b03160e1e2403030d060303080a110405010c02061204 62
    0x21508076a1030703402d1483c0102049001000c00300302d080c54640801d076198820011242800386a81140c0e224004444202d000c50b004a444d00d400c0c5017190036201d4a990b5218400100c4200f02c40107504400104001d580c90003110303103401c1c00003c2c20b042400840da00c04003c5405c0360410b1003021003d501c070394810703a014000d9258455980b17108030703848030140050846031110b600403c0c1031061040d07124000b250700e00c42004240c0307010b410050300c505444d14000c2c080b01003010184418038094003a90f00300c104074410355880c3d40c583c110007408411560f11070031411030040514880146266030358498031065541c0a000003050840d01c9007910b0680760a00c80700d41070050002c0c044ca202007180340781482c039000303150007510340c1b0400200349006104a0088010010005516050740c14040014251a10701c3c40754001400ea0340250794425081e0f0341d104805045480e0820381c04517111062004004540c400c4020741c42c020f00c060b048906040d9840404080035109a82c0ac5840140e541c0d482102c03e000d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 615832338 1250 615831088 615831133
    0x6130201170c04090c09084303020306040507230d23010615020f0609060606030622150603150504020d0608060a09030f050403081603090302030a151d120a0306080f 72
    0x5010b981c51040324141c0c082101c8504070a2846502c232040d407801800c2c540141000464000c0c05a45c014a040d10705140c4400550084000015403251103248038200150078201104000d4040d1800d816552100e00002c0240c040190088054003e0303040000c03400e003c2c21001385403c0c80c290810a51104019007014041c0c81b40940719800002000101e00000070404d4221005403500f541d01d880e041d0126141c035854404030250515004003401040d0030517409649a080204101c103100c0da1242da00314242c94010104070601d111483c803c0c000c0386802ea006100074201480c0001d402c0f941e0b1800c2d2414005c08466080c00190340c0c190803000e0541000c0f04004205607450f1585c58103013107503241d0080740151341880c00d4111410564104042c011302c1c441001c0c50300103045a0504845290600303c15510b401c070f0400c124141101c03d000400c860352142c40304074902c40540000d00c3c04440703030039490300720b4900d00c820140c403407500043c0c1d007400b48000744082966034082c142c04860780c1c4c00265000c41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 615833588 1250 615832338 615832363
    0x305010302010f022a0f060408070504060e090a0b0702100c270e0414031c020904111c0b18040b07020d020715050c071a070506130201170c04090c0908 66
    0x2490505c80c01003001c0c002c00205801070301c440041c0c0c04c00b8800318a10001010070a908a0f00c0041c1c003180740d00300080c1d42c400b100c104035400c1c40100d0300c6d602054a254015680005903030300504101000615030300401d40d000c0e03a6441240e840d11050700200741a10301000005020482e184185010704601c41c203200c1030415011065000c2a182508030b19140c10010300280800400c00400c441e0481c003881143c074030130565200e000c10424070020b404000e6111007001d500c80c2d0328089001c98640c02074400d0b079855000455403114040ba20b24031030300240c00c522282c80e90085030521800115026451401d002d940169600b108525000b64064034055072201c0c210b042d94040001040450704610100044010358a4000d44807031520b05264588100703030f0400c0074100d04d0b035160400c044800784040d00425000d4000c9074416183c000a01904581101002e40000c480340315a0a24070700c4000c9198004200c00f5000c0c0c42c1a6860748014100d814040c21500013a820710410803010b00100491090040d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 615834838 1250 615833588 615833593
    0xf05120705010c03050d0e1605010e040b0603010b09030106030203060a15090506060d2a02030a1818150b0a03290a031511070606030c0b030f070305180d0305010302010f02 75
    0x2401c00001800c440f40021009040000000301318200c011290008221010072404450011000c04800e03c03409980e801001c0c00241e0103101849d4500e03290085004011020704661328590a040b1600c1c4641e01c24a415a0150f40360440040161400c0050600c1203c50361b100040384a41e04105040d5510240d00082509042c542030103190356440d011251240d80c20100040c130002141c901880401248010100c20b20300030200e80140e0390080000c0c248075425640d03c4040d105412504016003401c1c1c082d07100d600d81c5181030785103000c05ca9806111200000208002500e0340c1d00400c00d80350740400200c10010707480e00a4002d9503d1002c5045004810850317001240192540c04209a041c01744406401c14104180d20700c44402c4650048860440f941c00302a0303524014144103015181e540700c1194940c40300100000e180300328a082c1d034000c0b00c0782c4041a81c13a46030404101d001d8640035154031150203039000781510107039081242042d20315a540f008a084e625500001d4a10200c40306050f0554 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 615836088 1250 615834838 615834853
    0x30e0a080304060b240a030c1b1b08010e07050d030216090b130e0606040921090f0b0306060403030507020f0603191103070c20060708040f1d0112030c0c0f0512 70
    0x1420440c140c0310060300902d000942c00d2019001121458840409c0a600e0311102c025003050284070100b081450606800c91000542d031084070608840c2040d00060a03500007000620040c0352110031561000d000c1e03c1110040d41e1412448840c0505d00d6001501c030554500a44043d424803005032401314000d00810414620b400340001e4890000a001c40d11840e0b4030007102040040c0c01c1c000b0305103203003412a2516402c0811401915060040c0074010442414140c009180c40100040b01e1240700080c040506052440d58151621340040b0022688520301404541c41038843d100a0f5214040d9010140400d140c080090003c8400a25540840b0f030f07010410883c0964200c014440019406558542c0544100e41144020350b03043c80c0d181d9005900044490621030064050415509101d82d000081a9240900d2001c8400401034402047d60407004010b00c5901441241c051802400d2181e03030310003a91303281909100030303070014801c000c04501d040c40142400001440500300d60310041c00b15 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 615837338 1250 615836088 615836149
    0x610050409030e0111160b09012a030c0302030c030a0c0b060a140f0301110304120206100e190e0709020406030b060c1b18040c1703031501030e0a080304060b 69
    0x2038425003802ca0601002000c3d011714504101b0078825104060a0040101c0f03440b01c0d036502c0158040d62100e40000c0860084241c000d105944141c00c0c403c24107030443c11030855076425218805285010303010340c001813103607901c1800240010300a280142d50b44000040c154035000000300000703001c41d03004050724407080c402004000840d1720002400c8480a40043c681c0c000a40501903c42100c05511804028802007012022040c10701240d42c0d025206107a84250694209002a1080c4130500c941c840128000b982c00150b08005485d01140109005006418040c0760403a203a1101c21450f40c0040c0c200000ca525100b6158441401c550b207900d00242242e55a960ba03074040b04800140081c0d1a016203a541d40da02c20650650720b50410180e2440e140c1808503001651781b14503d0310100e018081c02125102104030f030310a00b02852003c04014400004400800c03d0501e010514440c0c0608bc0002c04c5548000e9807060f03104290109807400071805003e500306060350740c80c441c1100e00780365250 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 615838588 1250 615837338 615837347
    0x801150504020c01020c190203060f0c09060d060e0f07140a020304140303090a080a0606060c02010210091e05100c1803030c080f0403060207030f0e100e03150702061005040903 77
    0x88880c225805a02c6124152180b402449801010452841505400304c1c49406135840001020b00890548125a9030038a400081c2801101d41e000200400c2084507114030f82107010740516200b079140001d003141ca071166122000303c10345141c0200080501004a1143e00c4440007884d903040c0d009082c00c107620080081d549020f04d010b000446805542e40388602d450030415a04507201c020304142c4080d030b41d246685e49039a0a500c041d6066030400d034000c900355000b011120140f940c183e004040300c0500350500c0c00144001d1808464001c1c0205190180305201440107240901403000340c00040301500c1440d08803291a840c0c2c006114540c1c0075001d0b4001031003012070071a501410104d40c11070340d5240c8042c0300e215038600180310030408a004020b11007030354094605640f00342c0f81d83c1c2c80c04140d0101600c80035420f0049591103224a03070114152449141c01008a0601404464140b4071040c8508201308044502c100180c1c410401c00c03002c0038035070446600802c000d81d0b04002d86a5152002403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 615839838 1250 615838588 615838631
    0xc120f061f090b1c0c1d240306010c150e190503030106050f07060609062105071203200105060a06231c0614040e0303010e010905060a0e040b0109060801 67
    0x28204a001c207448101d480130000009a0301c2420004001a008105001d09140d41c10400821408544203100c4028101122808020b00f1b5090320140c1465648100c10155480101854100211a00408006611840c1524400030013880120b104400b05151610f42500000b02e0b40d000c0710001c0a030130200724082300310790540e0094981f081e510030f0819503841181c400d49600a00840c58070b2400190101290f102809446612201d400d810000600ca07040b142c2002001802c0c1d81c0180d6420041e4480d410454512244241058405003200e100503803041d4500d8090700007165114000c020075494410140c40c09009a8180580402c05c4801000700030010441030f154221000140345800205c00c80c0c14004482c82d00fa810b00000d42c8401c3c0e904001014009040d0080c4c2c00c0c042155501b900110940e416140a41408030302a071070030820401600000e4441d9801801c500c80c041400903890420354400d83c080c08000c4203a5140402180480c0c0c49548030813041c1e403409584d940c0f403d0664507000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 615841088 1250 615839838 615839849
    0x30b03010c05040b22030b0a051905070906030513080403061a01080c19120c020f0c030a0b0c0d090206120103051212070e0102011b080613060b120c120f061f09 70
    0x28002c017000c8041160341e0703440d150806001d41200504000c0b5425a40d00b00d1445441640e401010324406401e60f030056032001d490030000301d51903030010f100080c4213900c0941d00c0315204040c1401c1840f1a00e944030340c2ea016400540300340391240c800710244040e00e809019400002c1c41c18101c1450040c280010364080c0c90300d0030103110074151320440c4142c4520720851203c40707400410032020400800c06540d4a4070218002c81e5400b0700400040389140102d141c01d01103400445c2049a666804600400c540c007a8003d0180940d40c0e007000b0016841e81d50141171410481c81a91100d9415414440e103028900c000860810b00304104102410200c0106ca5400489509024400f55130300070060740034155891103450210307601d00d10072540b941d128600300e024103000e580c00600c1032200040c400a0343c3c41406961141101046141034040180480c3c6a2048410b4030080c1092008149035031226420b4424050100d0303900240405032411f08801004808520b240c3c1c0000e01d00540d010784001c10300d2140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 615842338 1250 615841088 615841117
    0x70801120206040b0a08060a0b030606040b0d02070c0810060905011508040302010f0203091e03040e01120c1509170a02090114041b05191403060616020a06030b03010c05040b 76
    0x140110340b61582030b6070180034500b88042d150060340070000c180040c21510288258400c000006501e2840030440340612005400705d840c190a0640520030380d030001c040f61507000d0b800c000c558042084580f140014041d000c0c0034020b41a4036000c1482030f80c00030307009480340303900d0302c00100a9030b04290b140c41d450a4040c18483c103a5a21400d040c1c0c010030400079401c40081c000800c01019200100f403042c6000f1300b45003008250a038039003010750b8900407400743c00d409803112001441100c0b20703190038040360380c41228003079441900e82c0d1034018120800740c00c0074042601e024090140340d64080500d4400d503403040c002c0983c0e1f500307a000594140383c1071103001400020002034510f01d450701e030810142122082d0707249400002e12580100300b940702030782819a107110982c00a02492060030140c140c00d0880008078110345402040001903800707100001181803403401c80c1c20040c5c4074003426100a010580700000c0c0c01c111902454227407032400c21940c08002c3c0420040c40044180803c0d1070f9076110720030700c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 615843588 1250 615842338 615842369
    0x7090506031501090506150304020d03140f0d0203010608060d020312130b0705030414011d060306121e10023105090a050703060f0501020303280608010b030d0503070801 74
    0x46801c1284849150038801c010b000040340000c01a0000d9010703080540303421095844000844d44103002c290741c000d60040c0070031081c1010170f20900c0380b08124040b043c003892a10780c60000c4071016605c05902005003a8000c0010402e043c3c204c80c41130351000c815a1841500c503020f0b40000c0d1580790111946d20000d00111790840e2880e04a0112000b91098405082d5540c507d810030300d03500d0304075105425910a0742151441d1551080e03954191030100070001182400842c0d08010190b00010115a04007094490540302840d0400c018848615500c64405100400510b85400c04040500c0403040c00c2c01048020180c1e481405040c46003d9610304146010720100f5412452024507448590700407680020b2124404656005c2400307113070310751420040756942c0c2905603d2400b03144070b10360150304107000003802e02a04142d00d1508203c040c0b0780500380b025140920b0122076060308880d0140c0c0d5200c1c5580482d0800304000003036405181030060071403030409402040d00c441405404480001c160 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 615844838 1250 615843588 615843601
    0x80d05070f0b071b03090504050a0608060a0203090118300207090b030f06190e19022e12050f0f06130e0703200a06142b1407080108070905 61
    0x201400d1440701301007410710780090500400701c081074050140f20718900b5011510b030345d45503c80c50044a8152001d400c0b0340c1d49080d01c9c1c00013900b0042514410307540700d40010460081d56a091320b0010301c035140350741c880c816600002d00000200c4542c44020b030040c0704203581c1d0030b40000710303c01251040400400c600d0701c0e45002ca420b05c400203c00302e12904c2400b00f07124400780301d100000c08129a00c2d00411490143c1c108040d81c0704030801c0c140d060342071400210000740c10b04d1152044525003581d004104400d04190580050307000c103088000040c001904000c05030b0080c06141c1e00b21500784094031240c10950b030b14200794940941460b118814000300d101c3c0300d40454000400d104054025503003000eaa80c1058038110000c24101001c1102410540f00a803600c5d0b04001d058800703079602e643c000a8034042c515007a500200d5102654121200d0b10989404035118482c01c0510b03412000c61070040019550000078006080c29060008910040c003040800007800000c80300180230118045d210b40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 615846088 1250 615844838 615844847
    0x602040602060f0f1f03050a060e0f010b0609040b040207020306090105061201050f0610021e0303011511150a0b120a030318030c02130b04051f0501090303090e0423010501080d05070f0b07 82
    0x40d4030080c10760182c40c4c42031049c80200e6109161000340c1c1c0003501c12180c3c4c0c842d01c0a00300c0c2c9142d070340c80e5842a410301014a460034240e000800000000d0300042c64040190006468000111891542d40c2e4440042000c9414250f500b0300210748584001e200e54100490047d8400d580144802d000e080b0400c1200780507442040440c2c00f4140c15124406010700d4007040d241c499000740110005d11406045144000d4403e01040160405800180c09400c440084808408901074041c2c0e82503601c56022540d65944e002e985107051a03001d0003000c0380e10051801a00790346082e010f994095409124075000300350400c21001541d503045404000807128120f0100050502240c99500541b50104101d4440b481d000d1080752400c0000440b40760540c0c2c0c80044569005501000300092068403080100740341e0140c1050300584103040d4501c00141101e40f0020442101640340526912800104012001030002c54031107a003d1824500e4012207484112141240c49070041080072004001803245100c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 615847338 1250 615846088 615846151
    0x3070b09252904060801050906060304030813051606082202060f21090a020306160f1107091814070e070c020a0e0a0f05060607121d0d0602040602060f0f 67
    0x20b020419255510303003100600d07100007405894000c01c2c044020a40a03d00203094920682d4180c2c0c0e1400140e032844c010b1003e04404000c1203d05200d080c4002c07042c1c0c02c2c001040000303080329641e81040c629018a03010340c8400202c0007000030700380d801381050140e25110101c40d141e001208011340d07101c104124100b000c0c2d405a0703440418070414014050030020200d4070518050084045415030b440c0c640c11965032041096040c40030075007001c1180c001c14060303030040f10001c0c0d030101074900840c4d850a01d101030716000341403150b000341d2803207409040101c50191403603c8904000108045400c00c20446e642c0030004d044030050003520100f05003155540000c040c0581414076440c0141e04103408410040e000d0015202c3c2c016003080001041c40c18242c050f580c031183c01015905080d80e90030002d0b9850340143d00004400c001c00c2240103826180c4203482d2101c644110801a5210318011b4002d05110020b081c0440c90007003001841010b0006266007034000d0201810030074550064400c1002e80c100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 615848588 1250 615847338 615847409
    0xf2502060d0212060901050a140a0803040801020c0f1f0b1c050c0102010609090206030610021002040609061106070e040b04060519140303280c0503070b0925 69
    0x10300080c0c9222000403500a400004164107018149440304001c00108120034040d003a08034941020410202524240d40e0340700d00c0300900805051341e12103d07801d00355031103a008025269000907207000709140820400c1d24041da00406880100e150b80e06c5118421103038007400310b0f019261030b03454143d0b030f40d00152a801e15034111942c0004034254070f070890f00c40440c507010030b003d9464000c0029501151303015150401d0343c020030481c80c40e9103000804c1040c01014038800218841c4529040d600d061520007400940440d403945c030b9200307203400303001009040305002801841d00a1400c1c4040e01340c00c00042d0300c9100c001c031070103c4c4250a100202e0002d14580d4012076101c0304d40d828481c07003042544100030035a03a507641d850010800038424140d0300d201c1c1a90301c680c01c440703844850380c1d40d080c00600d00e0000d9a00b4500f0041d0b07940c5a44500740f85801a0b107007640c1220030750042c440540001c104c5400408140504203040721410a00740010100c80d00c0741c540c0ca000030308840c140d61047c06c0300b0000444c8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 615849838 1250 615848588 615848599
    0x408060601031d250807270626100b0609040b060d0f150f03050613051c05030702161a0903010f0908030f071e031a03030c0f120f2502 59
    0x1d11490104e154091044052200e842c501400b1480440120f01413064813003900704007800300d0110751110b040d03031a4411596030550760345501143e9445810080c0703098454180c0d0304650344180c448128204403950b0040d503e070510300044100123850f92016501071400490b000102601018007051140c80f402c1802c0091900c2c4c4a940c03c08401940d001601c0150104000e041454903143c21103982034141c04060555401580004c00740d42040c0fa1607041e451042050710020000e5007090f212a9013000509008030f0004402c000c2030b554104401203100035200e0303080d40007900c0c120310300b00d03984041c066105003610001000540c5403400d4002c0160a081c072300c802c1004000700e007131000c1c01d50000d5501c1c50084807910013044085108a1a2000220901c0c400c560000c420540070b0b001442001030604219041001c0d40c030385550701340080d240c802481d00180030500c04440c1e4180c140901c1c44480018108144000c1085032451801d44440e1048545200c0c08504441c1c00c002c1d01261400d0000d6001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 615851088 1250 615849838 615849853
    0x624030106020115050d030e060f0409060303210908030c0c03130f0501021c051c1e0e010c141b1e1b0f0306040204050604020c03040305010614060408060601031d 71
    0x302ea0541c0715500c40c402082caa0390b40b10f521602001440b4410034005400146040c0c0503000328a8640b00414030b0701e030444840c83c5400c0e07591110030f082d10b01c1a8020350200c2d052940010078000d0025081685111075541000b10f2807080d69648641c3c040038204151102e004260080703042010400c82d0044003140b080c517018143c0e2041c40740c89481840c040e0328018090018221010310300c60b035000d03031401540d8076100e081c0001405c008241e07201d07031111a0340040c1c641c44480d003480c90a40c911200c402000c000410040e849001942c00e4850b1044800c2c1001400000082d120640030155124200744a880c042c20308012590b2600d8202005010381100220b81d80c0311801040010f013142c00b0682d05132040c10f4803100741040000c24034591591940640241c000140145401d07841750f507000f132004dc8010b0800e140a44490301d16005a00203c07000c0e0740d9041d061041601210040444c180b0807a0420f1a00b401d09540c9a1101c501804090500d91610703180d80d1400c40012400e0320034043c1d40210b8181 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 615852338 1250 615851088 615851099
    0x110c04060e07140406020c100915090323030909060103110c160906061d04021b0105010e060f030a06050c090607030815030111040308090a0f0608070305150906240301 73
    0x41c864281e400c82c0210350f00c070707403242a8a910b0304281d40c00c54134540c020382000000042400300c0078003151888002c00c4200600480c804054030405d019000c040c0e62800352560844c5450044083c80c0c001004c411622580702d40020725000048403ea04019036050425032107400c01070300034168928003120141030110345580700030000602d002d0b610103801d81c0462140d076102080c0c000c940990044800003000780000c83c0d00c0180c0c0100c0c1119480b0081c0c00186412120b00802040003402c0b05002440d9441e0001041041d80003002c0360340000041320640800c0c224100001c0e503c85d110741c4000e008507103c030000703188100702100752401d2203006880d196840545250052201e43d04030b034812050404209440c20721309051050b08101d100300c0d01080d00e80750858645441903000180c266907c00171998010402d0949120400c00800c0f20b40c55140c0e0a0800c1000902038844c003c1c142607100440c01c8009201d592044100b5800c1031055900e002140131210203078115010b130003403030700c40440000000200c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 615853588 1250 615852338 615852359
    0x609110315090106120b060d030e03030c01140f01140d03170717100324090501060b19031a0111030702120f12030c0307030b010c050a060609050c070b07110c0406 71
    0x460015000200111303600ca1031841c01210078100003408150440e4000340c2c5500b050211403500b1406803c1c555800e031610350000e03156500c003143d03050444c0d44440d050b0404840c940682ea8000452503d0419590f0500d90b600081c8207801503103501c20300c2c142e203a0b401814020100e0802d100510b000c1e220081c0b91014010780341344100382c030655201442e00c001444e2200320801c50016030b030b0300c909182c0084004155440320107142041e40040e0035030328041b40740050004d00c00c21000b440f1200100e9214940072030028002340e003020321401494101207846100880c216200ea17501002402e0043d03d56265a2100b861400381200003904094262840300c0c0c5403030001407102811015804888103582c1c0250504080c0c001070759006d42c0c8000900100d8042c40c000e8018001c103440600d07114981000e1a100c071480e210000c00b0a4401e2603598030305000010803070180991250240700060b03d07044550f9601c6000d41c1d8010030701800c0014a0b50402c441c4803003030003801854080180103000c0240c0351004072a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 615854838 1250 615853588 615853591
    0x190908030f03061507030e060a0216031203060f030c06080703180b090c0114030a0908090d0c05030607050901050304021302040b0a020c0310060509040b13060e010218010207080a0609110315 83
    0x2071040d856400703e40080d05602c800c5403041e030b91507601c0b0341e03101e4001801d12090340c004460080c20750040c3c0c00e0459070302f4260703d90200198020300d42c01380d41d1003d40350701904441058200c000540d404910030f00200f803e4040920445100340780015003aa90002c00300d00600e018290b01c094140c0d500d10035001e0081143c0518014103942007030391016402032005480d6a81e0001040c2c603801d00500010b0312211a43e402400c446025401c10392404621000084104841d50411185480d00c1003050001e0b0808020a9a20050606143d481c00d0441000a0508e01000304003d119545c0880e03c0c4a040c052501501d00030020955150b8072000d41301000703501d88a4144e060ba0181c4251009070420507014060b24040301d2014042480b01d80f140d0305d810350200002803580714442c5108a4070000240303148240040e42c0d90600005071110410303240d03000c5d03529803440c6c400e045512000051000200110303180500c0ea030b03c0040060081068542041c88020303520515615024070300652801c200440c0419 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 615856088 1250 615854838 615854851
    0x7063504150b09011a0c010e030c0d170609010e101802090312070c030f05013b0616050711100819020705030403030e030c090705040807061103190908030f03 69
    0x34080c030b1405006201c015a401d109030700d03200d0240c603803201050b80071100501c1e1001d0034400104101c00d039183d8181c03466101d08480e000301ea0081e030700000c02e20f51000d513040308043c0c08007480245003040700004440c180180503d0416111034408106084015150040140103d240c0f001c090720400d56008020b40080d0b0b50b00d8000e024644852030541c43e00402c4600d1251700010841c9041d00759100d2501400254034115481c1d9a07c03540410101d2403035040f421801d51250701c0458a02070b20010f03a40ca225402c0e01030190b5844141030160707088846500203003407a0245051502c030121410800c511440701d070000c1f0303005034845034003500850f4440d40162041322030009203a04c180010300c10704202d10a02d04060040e810a01052000a00c44c03000c2d515203907002010bd6118041040009103288016542100031660004c0d007004814014040c4400405040c105550303400f44242c401600d0380300740c200329907e0881141010a10a00a2070b245c7d010700203410450fa01c4804d406a41d8409500c2610b44 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 615857338 1250 615856088 615856091
    0x10e06160906020c1c1e0503030a0c030c020a031d151323060d0f1b03050c091f140409090314210a020f180a05030706350415 55
    0x440c401d800003030440c80e48000901161700c100758100700d00d081074030214000c440a4042d00c003070100020006078030901007805030717003e541d40b401e1840f40c241c115420301c1c40d51014107040c1010424140d0b004143c501c019134240c140042403001c1c429000c4018404424515031205104035425950350818020b801c08659002e01240036a4503196482c008410240ca500ca13040e43c00c0c05030704090304181000d04107010310003001241c40d40411310740c172b01500d084a02000281001d00d400074507440d41030144607008000307000b0280c41d240305000030403503600c04440410f066105010402503510302c10101a00101105881d5540b120b8541d0030100260000e01026400103034a05080700e045e003280811250110b811040d0200c0480d0b40d0006009110001804e0b01c003001e038280441d0750312944800c01400840907211210100300365210421080c810643c200c540664012481031180745c0d040060380c0140800651180c0c880207542540c558800e400d0540742c8940d1810030b0502082000002c0c1c0144c1c071440d9140c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 615858588 1250 615857338 615857357
    0xa0b0711151c02130f17060c03011401030902030307020d050703150c0905040b030109021c0605010807060f21060303120c021204121b0b091002150a0b03010e0616 71
    0x107503082240140105000016015100c0c040c2ca868994001d052015007030309506130031907640b802e145a51000740c2c40608041040f140e41c1955010600c800343e408019a0307400d41c1194144411004009040602c50f4107060303a5407201004d566040041ea070342503500a2182d140d041e10b0317250440c0c07a030f107503440210b070040294114062100382e580510005a84642d440b00041442c03c0c0800018101c008211500342d5624020000503880d401400e040c0b884902c0700c0c00c119426039113000070884905034866103164100c07500501007250721400002206000d4038002c040031441c03842401101d0f43e1003201011544c94403000004064110000f41c07038480c500c140801c0f6910f03a152040ea1074103144040d84101c03102c10007060240382c0e48820780030b40307043c0900c2040d200442502c1c20301c0317841c500c0d940000254020100d100034546ca00f104400708400c0c00c52010b02074407014a28101010b002c094001c1d0720b000d032650b15070943c0351825803119044c085600100c414034203004200003865580301c0043c1000466562 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 615859838 1250 615858588 615858619
    0xc0307140105030a0c2714030f0a0303020702060c060a0f0f050405061b0d02030a020904060b0f070809181501091707180b030f1f0b010c110a0b0711 65
    0x1004090356000607100c29146560b4003003001c1c000d01c529541c960621072800855250000780d010201684a07101c00501251401e0003079449a1804081d0743d80d00c00d5002c001c1d42050100082002381c401c560500380940c40e02194800120300d4005c03d181c039010703442103004011045840e90411003200c0d48091040040075122078005064640864000d0b1455000502227080c50340040c4044800c41c4092183d0350511050441c9142079034029100d00700c956402040c55252807a091040c1c4000781201c0000b945010001a40c40e04640a40c00c0054402d20000c5a89062a210441c03000c0f00b9940316060b0701c0f880d240c9802c1a48460111101450000c3c0820201040d28144491810620301d100303c02048020f00d071029003049250396174a0000201d03100c0b101c400b2140c4080041d0603040078104040c020f0a517040d1800c04101000e1480e01d003156040000380001640c1100000f40e0b0240c200a01d07855521012011611100065010901c00303a80018541d09110740d81c514004846c000304c0c0e680c6078003103584 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 615861088 1250 615859838 615859859
    0x60e0d05030a080601120903031b030903140c070306060306200405030c1905030a05031b07060503130201020a201206061c060e0d05071a010803040b07230c0307 70
    0x90802400340d4010050300072902e000307403140383c0e1210b4149441205041e00d20010020390b405240b04034046502c5940c2003200201e959840602020035140400403207296450081076240c025000034030030b6800040c2d541e108501031009401668005200307208580c1d403481c6c42c0c0010400c3c207082c42c4600c140c4d1240c41c000e0b05d0441d4129800c0f548000c0041412108030000c0060000c040d101d10001001c030588009459203060103c03111035805031018607124402900c5c0104040354010150459400c80e00050100c9034000707080e030381c12540d5849406031550342440140d191120756080900004107248202070120f01d44005002942d60a44512310b000d07154062181c0e40b18000d59401d94060002c0d0804078000446d411881059805644c1c00f0880040c030020241c100340d906401e050003d0400200c41d018059079071000400101100007040d103640c5441e02d000d4a038000e9000341c2d1140c00380024000144641d15240b80704001040901841c4094201c45695079000c11904aa000c1d010b0b0300760024103203806 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 615862338 1250 615861088 615861109
    0x1b201615030507021f150e01030c0e0f010614030415060b0903010b0609030606010809031306050d05150d1502040512071e3506090a03231b0705100306060e 68
    0x406144010085200240314081c2075107207000f0049000c0c6e074000058020312615180e0080d4011861540c8041c2003090302c400b0100014104841500e20750f004100c10f0354071032440900d04030920801510790b11030340703400a070841c0658500c5130910300b444008203140003100001c191201c0700310000c00200c00800140402030241c1546168190440c50014180754095204103900c243c1110a50345811100411f19200488a400400020302d0102e044030b03070302100c0c0c400c0c41c1d000000d01c92041c1d91000400300040f08504008001001c03088040040e0410a150f138042d100908801004200344821800c245982c96541e8843c00c981d010b200c07241c80360507110720250f180131b0718040d09004d140203001100240c00c00744140014490f903c2c0b0701e1106140c2d59814804680991000c601602c014000750400800c4118000c2c011311190044803070000706024090201c815a003125103455410b0340c005250141000c0700f580c4450303000b64240405860080e8035a01c0001503030203e48422031500b01000900152200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 615863588 1250 615862338 615862363
    0x1501020d02100c02071a030619030b04060903050d060311130507050d0903050405060d091202030306030c040504210203030a06090218190306020c010c031b20161503050702 75
    0x1e070801c415061041e004072554a560b401210395055035541d0f65641046003250006c050b00012040c81410310f0650060300121004d10f82d40c51566046844102000300c0c050001047d02d5640c031500d004050044040c0e0350407880c03105081000c01c3c0d8074185400d4150362500c90702d1196200c90500e030000040c1e4132034a4094869a5901401c1c03112090380d49000703024541c0141c0c14018284400241591800d004000200c2d0071800820f03003002c1841c2c480030014110f601030081d03420600400103140c0307001841e104003440885020405807240e0030030701c4503a201583c0406d42c0140d5135244d950003640010042d0f000d082054000c200559888641500301e00a09107800003201400082526901c2d01581040f03005141ca4029289542d5907980e031400c036400104018020307511001c20405894262040c03460000407964640e260902c0104c0040601031030b103018004820b42649204030302d00c0e003004194525100314421008040d12010081842041140030b000042d080100080b841480499803503c0000b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 615864838 1250 615863588 615863593
    0x2100f1506080c040e13060b100f0509040e37050c060c0f0109050106050324010509190c0305060a1212080615270612011206090f03081501020d02 64
    0x1410300741c088441c41c10180c507204072003006001c0400c0c903003030701001c242c0540c002c9042c01c030808140d45401810380717441e50740c614421865000c407146141d800001c84081806240380c07450365103035100001401813206942101540c420205030049000c1c520b00d0380300540a020044440404021224101d24101c500004209030030045003005c0324200030024200788038204007618071460f09206003034215180032200342c51581d100d40d010010b605060180c2e05204171009400d03400074450401741060a1810f108240c000c0d0480000150031540b0003a4001204103d190140144541c001e070040c0030b080146e501e02d1040d040d070400010030302c8a01e0381c9070750219440f1078942080305072004151030300031000703004540060140805038040300440d0014198800c198904407045a0482225680c1e100d0404500d40142c40c2086001007409074012414110b9211103921041171085107000f0300640300003140240808400c01d2508101074215007160b00c43c80c01110319100c21840f207001240c2d9902c201100c180980c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 615866088 1250 615864838 615864881
    0x103020d0e030a18060c0b2e030c1a1603030b06070f020a05090114040f11130807050616080a050d06080a0204051b070605060303070804081c140f161202100f 69
    0x1b030020a1103a81c069a94001041070302304240001c6158003480c6c101c90b00c09240781c00113000700003018442c5070190200c0700b070301c19030503a0034030a203d01e030f00c620305000000c180000340d03800030144250002500d03000003070a0692680b415180c0008100c2d80c05004a1180c0380c0000080f4a41c1081141d450403654400e19502d04503d90f001400010841003040d072260680b03440240104031100b40042c0744100707140384110015458071520700c0c100b141035005039205100810045a0180c41501c00701240754209001340e90b554100c1c41c05940314460401e030144014109940000d840102003a103e00060003510207100701c0e03072910398800340704198205180035a0030600c0203001140441d8801d50317001070302a045a15003206034030780c03492542040d0700c40440e603881887c0002000101569569150909051084081e0101c803002802c40c041c4240b1061105008103808541c1c11049016408007608100b20b05115148410002e4443d109040c007140c40030b0410046c0c401d4000d4a02c00d40741a6001d06200c02c424 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 615867338 1250 615866088 615866093
    0x30c0602091305130302071406090111030408010507050403020f0301050402060d0f090204110a0f08010807090c0e04060f0f12020609010f05271201021c02090103020d0e030a18060c 79
    0x25000070814a402c200041d141d9a0481e6442c41002c4c001e41c00244200800131181c42e000b8946100c580005030840c450a066800c140c0340c280030745030808000d0038400303100d0a4061a040c518022580204103642c244414080015000401001607130700984010b039252108074103050a0710001d4034000c0d00300008008103442d941d141d07880414517000c9198080303010400e54000800703440d50400708403420400041c0c5040b0341034100340303042e00c5440b4601b065101580342c42c001c04e403030721418070901203025241c803801c48420f481400302c001e04050080c0304115094980643d8940c20400780109050100c050501240002100c401d88004030f03070003010300c0e1030062404011542e5001d44d42d0380c0f40503c0300500c208021842c40c030221000c000741d041029068000d40ca0208642c00560110322281a44100081c82c090500344450384910032030003c01582e1b50000000403002441810703001804145004609000040e01000500e0070b001c540e40c803813101c1317015200b43c005d5185040c03159101040f400f4069800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 615868588 1250 615867338 615867341
    0x709090b130504080c06130803070503100b0c0a0c091a040e2b0f030b10030b0111010603050601080709021c0c2609011a030a020d060609022b09030c06 66
    0x1688000900060720480030044448282c50003601d04032252040820f0090000700e04128407a03200c2e032095006550714505071130f03c2901e80b0000d044c074810400300100080d4400b6030080c03980b000b041070f01c3d1415507a07a0107042030760b15290110811107041c50250000142080180510311541100494011140707004008200082c01c0d10a5a031000c0c3c01a2036100d40482001115403a50566a81c1c00048a0107251780042c8011006161041414034012000b0b000340c564030610040c8120504002a80440300740042e550400c003840e954a0541c00e04d40080100301e03020911034100c500700022544c28948419213202640585034104082408101c8042c16800707054000b0b0078851407600704116600540e9130a140c0514150410007290030b490400c5c4000070600344144e02810812080310481c040d050f0b07000036152011080042d00c29250150a2800d0002c160f1004000b8031800200710340e0750080c1c140000884100e04028400c003086030008800070586406401070b0035034955296510040076665090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 615869838 1250 615868588 615868601
    0xc10030911030102030412030506030d1e0e120c0a0b070b0c280306060807090302211005070e010f080f06060a05070605070503180309060901270e1b03070909 69
    0x446441c50580480e420b500e0030310086000d217000700001c90b120107a100c406001e5840152526009511204056503429400350556100044600c64031012504044045480541d81035415500140940003181e81c054002122a458001a540e0411071076451301001c6103801410030243c1203003102e20014a61241c441c00810030004450340400d02c034900e54084100740c02c120301001c03010030740d140c5007031241e0740e000300c0401e038005541c1c601503550741d007164040703829036280c44410b0343e84400c1c80002c408041801c0c4400e041400313000404010f140f50000c4002e114100f8001d8a81c00b048031401e40c50406845815142d1007500d9a00f01c044c16910740c107062154552001400c8010003000740504000a444c40c02154060000d42c0d4805850303081c5030198100061081c580d201c11a88100301552030340d103440094139032164090801c3c2c3d801543e041d81c00a080c44c41d40c102901a01c90304500440c0680c4031605c018000c031501301c801108464182d00f074001c5484161003901c04036200041c100440043ea40001c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 615871088 1250 615869838 615869843
    0x90503160212060408030f01140109030813051c03090b070b010e07050c01051f1415030a1d06150109052404080d08041205070309180b130e0d020c100309 67
    0x242c0c0c0b140e40c00440716007002d00030b0354200c0301034800006004810a030200130311301502d80751030500700c05552800040c04854051000400c130240c0403030466013800344008404000d00024065071300c541c40ba00308070400c4031102d510807004180040000f00e824400801034600440d80844584016402c01ba42615075000042c8500204002003160344441d48081c0505030140484030f80e0010f40d0313185800c0c800d85290701a041551132340c400100e21640c03980e80c0762180450384d602100310782d039984481040030007604054003400742c00144503810407800c0c4e20010b01c1c83d1040c4103940d6540010351850b4011034441c0c00520456a01100e03022401921040b1141c0750360400801c2804649071643c1c80780c03c24100b58401c1d2002c000b0035070140c1008180319003d002000250307114503200e803400345695800703041d0079918060004500700300c00c1041e4518250390300c46004807500900101e01509940445d1026090707a141c0c440f2203000388554103000c9400001c3d441c03286140103203041418040306034118010100500705 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 615872338 1250 615871088 615871099
    0x90b0c010f0e0c0a05011e050c0f0d0203040303020607080c040501030b1f090e01080a0c1e08150117010509100f0b040525080906040f02060c070b090a090905031602 72
    0x2104165909114019444498502802120300d07448104403400300650310250501c0f84002d04e4000700e07c0141542d0000c6035072802c00a448290b0104220718040181c124a501c0d07110b561030f203002c000c0d000005402100c0c807903030032a40c503941c030341c1c000b26444c030781c02c2d183c2c2940300105010600c051f43c083e800c10320746038402034000450540c0940d0311b200c0d015504001c02000c0b4403010010301940245102841c0907080d500700414000c5900e41e20300c0e0500b402446183d8040c17a0000c5c1e04c0103c910380080043c01460004200c0346008844580200508001c0c4107a44000ea044090081c5007407041c000c00b403094802c90041e0103a590242c01c1c110207800d40d004040b11031030342d03030007500d505541d98410b850041c00f0040d842a50400709010f04111854040c075034105020800c000c100f41580001051540141d1181780c11107076020920104445005000810b01c0c107014444010030540510006052915401c9440104940c0d4420030003040390390350305019000303401c01c01402c004400061a04e4004600c050003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 615873588 1250 615872338 615872351
    0x1508090c1810090b030601061103040b0307051201081c0323100302010f2d0c0b0a0b100e06220e040b0f0f07080f0c1c150e0403090b0c01 60
    0x10040091101180080d804680070b002114150540a10103042c1c110010801c4140d80c4000a948000c14860b402c01c020030924034440440080c0150f130010140001c0c11600da09141c0006491500901c900303400754482c00380005540c0000048080607859035070711029080040950481c0038008440e00a070b0602c0d1071a8031030440300000e6003540e10885032183c035685111704502c0010410701c0c14003002020000750303400101e040c10414290300032140101646044008450009071101d00440c18043c2008001c40c041120707078207a40d04001e0750302c20100c924010740a01004147c90201c2420009030300058144403002c035601059424400c07046070006100030b12035860041d4001c034901114100d811841e5501480480103403480c40c550003e040203d094400e00d44840001c03c0c5210041c0621180034501000c9900b00d0f00044c1185c2c60500c0d2003402140396490038064401070006820741015032441000005130f85018078003101c1c000d0f6450307514509072620f052403180040e00300c84205643c40d50b1f10300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 615874838 1250 615873588 615873613
    0x3103180b0408030d0f05161d12150a06080318041503030c0c05040902060a0503150a0b0408160b0f18190302040e06040203030a031a03060a24150809 65
    0x1001e00000d02d807a000960b07403900d4214001c020364040305070901c0180d0601c03080c8499001d04560100001207240b0f00340c100312640f540508260354100708403d400078546504205440008a0381800450a00e45208483c1d02d8a40c400b500f00c81080c401c410640c2c109000c140010300c120854562000c2d0024004940303d40c1081205400007610b500880c0030402c40e01010307040040b040380217001050210b030100511740e52038010034698407031050b903081008000400101d1000718010300c40444a0301400c259056a15500550302c00d510602a0030b03040c1c4118103101d05030105038121607082d50800c2e001c40d420325a00030781845c200c1c1c0008003100301400820803121059111001d0000c620581c3e00d401c03d41580c5540107000403540080301c100d5481d00817408010150301e00000301c1d01c04445904d0002040c6010551036240980c1118081d035140c081e4100340000c0c5441600305140542082003014100d5481c10f21304a802405486401801d00414001c6000e003401022040d600110b5441981c01703804108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 615876088 1250 615874838 615874859
    0x30a08030c03060a09021914070501060b09010e030a0c030206030c0d0c02030d0b01050703020601061103070222051806041b09020a111b0a03140321310318 68
    0x4803a2a00e80c28008030803c2034520b41001d1800c000e00b100001145811500c2600b844941324a400003410701c548910360fa0a240001c0045680741c0b9004802082400d40303030009a861548007119a60014200c000d02041a01d070228488d07816a622203607030718809146a00740302d800d410003031100911000a000420103d0303564058501552196400b659075054140181021102001007841c10410240510740000b500052441d05690260525800c1500c904006a20b103100e166802500040d00c00c119041c00140c0703001891347c070450030740248515901c20142820301d07440380030780c00c540c0e074401400709020500740304947c1c102c20010803403106035946901801d4180d9001009100014403901203601a0200c14003016100c516400c441140c0b0b00300400001e11034940b54003001d010841030080600030034000f00129098076a81c05d012000001010244000c1300d6000c030f45131030a0070358200c5041020520b540d4800d09015000c0d0aa40380400d06403000c0b00e0060103041043c194150114000c101d803401c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 615877338 1250 615876088 615876091
    0x50705070609180618090203030d0f06030c05060f03150103020720030609060601051e0702032407080c0a05160b1014060301060e0d050c0406090902100e0306070e030a0803 75
    0xc54450710b0b00b0500e000b16541881603080c00d0240200d140078024810071044080d08007140f030182c4408901e00b007031400001c1c1103100c0c031a4a460aa072500551740d200303030031903003018085a001e08581038106a443c2c0511041d841030340342007600c106041002880c14041034030303011711030307201031600609100c0e0681e50950307140c40c01103040c2d005440c806081e10310313481d08200d550342c40400a006050359090003c006800740c01500b1841401004140402203c0301d80141943c01e0f858009040310b000b00605207150683c501c0c0ca0140c410700c01c4ea4600020105070059501c3c0340594503800309a8640f9520001c220742c61303008510280743d1426446041d002040c0c1000c0024050ba8241c400d2142c40c600c1c0c50000c40011800f0120740e03000301c2050004010071504440c101e6240d8006480c41c090f00e40c0709203003003800c20211744032540e405403803c1070106500500780e2100c0d942a10030346e850481c01104c4202941d140c1460040700d0fa260b8001030004004511544000002c001c0260031600456607980d14103107175820 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 615878588 1250 615877338 615877349
    0x117071d01050d141009051e06060d0303020c070b19031a0603040f0609051b010305010b0d090c0806040809010e031b040c2606040507080405030d0c0e18010f0603020c07051005070507 80
    0x84440285051000c2800360009003d0707660000c0d00800c14104110f270311540300500140c490b0b510320503041e05041c0250100c601396030701c4105944143d1307166040f2001e02d1700300982c0000c03004958225100e0075400303813103410741841070710725080044d007854000c1010582c0020070444200307292240707480003e10640164802280720f80b000e04405a05010420300380006848964100f40c00c000042240d6a80c090480b0701103410420007203054807003402c2c0009808616400300704984a56801c0205010fa003502500b1189070990321103215401c0142099034031103005202240a9810025182c81c03031825501c241074511460400c100d008148044c1e08140e4070440e0141004803002008001c031503e0a40315403944450f4509103101c1e07500389038445030354134002c444050025503a2140d150004501600c0c0c074440c640c10040c030b0303a202c0300711201c00800701040030300c9400c0092035158404103245000c2e0007a1402c104846000f0224140f400c020881460740350300108040c45030420220000c40c1c020700030300d4040c0c070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 615879838 1250 615878588 615878591
    0x5060a12090c150c170421030e0a06020c01021501051c02150f0408010506030303040803150f10020d120203190f060e090607020601052e1101050117071d01050d1410 72
    0x40d11410300303c400217140091103003006000c0005124280c08046001c00c01000040c9802681d2240d01d0b080d52440450704d045644a842450005480756001503086403408080c0d080c0c45003400542d2600c45920350038020a40d00200440b0503640700320301038030741c003280394001441c074042a41d05000e4110f0b10762044900c0e403c02d01d80000d05100115003401026040103003680207610b5840c0c10b48038014180405010204036610b03480c180e1003036640b21960900404001804404446100407010b0b40d506a89210000804d01c0300d25500e0303c00005209403481600003150040100980c496480c00408403402c00480c401d64442001c100c9903151400d10348140649801001a8100640c01a26003071059025510039101019404655003e060090b00d02c3c26040308014440503240b101603070030158100503110382e50302c0d26000081510030070742c1e074444283c1e005060f921041d40b82d02c404161888114181400d203440100100940c0c200003a16003460b07030013042200008813007500c8407030400603800c0c2d5800489 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 615881088 1250 615879838 615879857
    0x40302120313120501090203031204150b130e0304120501090203190c0b0a05310b12071404030c0807030201030b040e150a0f050f04030905060a12090c15 67
    0x60412810305154014024025410704034608601c0301c1c26062405603095851041103910100202500003148003640107040eaa100e00822400010401003120b040d1903c80d0f0b0060041c20610451143d018002d00c0130b0900541d084150140802034942040c0200d513600c001c0100107480d03220240b05a1a162007813001003a000300c42d004051515642442001244002003100400280c02000e1101142c0c4855a155111000c43c03509803114011120340b500c500b001c0c0342e02c100f841001e440044201740c007403403191401c4a07280c0c4032080281c02600d55405682c0c0030000860369042c01280545c421900a02d034291510b0348a5440032400b4129500083d0940e115240c184110340e0140105500a40d0685082018000f403c405554a41e01207600c01e42c0202c09202080c100e00c4a43c0080c640603080050034480307070a0008a2039031800d01290141d0005045060205981c9420000c48400603d1503a96001c04a80341d50780301c2c0200501d100486038958503c600049541c1d210240102c0b8a41507150103855 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 615882338 1250 615881088 615881093
    0x102101b021c081302010e19080618121e04170607030207080a08070e04061206060503191704050a03050f0f0c0a09150e0f16090501080c090a0f09020403 67
    0x144001210000c0444159a4064141070f03480545641c0c4403081201d01040c651141c00180e448010b40340007036801c117000008040d50240c100301c8150072102c03140e045401a0f69800300c07211070743c0c0d1540701d0705c1159008400c41104546000c40a00301d0302c03840d0025005482030005044d10103510690054050661341500300c000c0e4075081c002030b60701c1801400d00750315040712940c1e8401c607481299526024000910082054a0310035400201e0b01e070f1b8040c2080044584034207400b540000c4c038180c00c803030450600f8070110360b03030802080303107107071805103e000c001040c81c80da880d0f0940d0200c1002402c583d100520001503503a945101400041d80104007525a007009070342c41c03a08203241c1d00620360440d40180d400590a84440d0712340700403290542d0300000d11071002100d41d80184400c0e805441226040303018400d145403002503013070150706880d400440d40ca401c010152105940c901c03d06000c1901003000542c0d00c81000000c011800d0f0041c0742c0700589403a440ba50404400ca50018401c440d40407506208 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 615883588 1250 615882338 615882343
    0x304080312100603150302010c030315120209010506040e0c07110d030503040302240703020a0306080115051c0c030609030c0209040b1f030521120c0a120207030806010e0102101b02 79
    0x241c0322504d02441030910001e4601150411840001d041040c0b06440b0010303d40710380e0024015516104510010315641d42c3c0815001150410a80c41030340140d0001806203494030031101120b03541241c044190b0b944801d0b01180c2d40209006403100249420700010642e54031003151103241c42511015282e060500b0028580400c070703151341c04003004010401c02c0302225580d9440c0c0c00301c1d16140c0540e8980d8180e204034050030255000b03400319802c10f82d2040070b6204e80c4850070243c1c3d00036200030030504803100300c2c10200c00507020064840c012015081c0041035054014613001800380c2800141086580e02003241da02c001c0740e007501c4101900c81840785282852943d1503846c6003040003010020b007151512034945100707500340019416218144911001100280c2e1303075828085440060501d0100c0403002c065110851120000e0160b841050f852803d900c261901103030595100c80c56582c41100541c0c0310880102000e05622408425103450b81850284031140c2044c4926010296260f800292 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 615884838 1250 615883588 615883621
    0x507060c0815030a1a070306030b0108010617121606140f0414030c0613051906060f0501030219120b060a02010b030105181b150426010203090307020409050304080312 73
    0x91003070b041218080c02284518140c05045e513841c0c0b01d91005074462800a800a10380340d40014407141241d000000c070042d0650151046540264a0500902001c00690380703540c80c11054034083c020600219840150b122012810303d80308890014119a104043d0304001c3c40417510f4184074901c0c00200300030485c0d40091601d8981c10b5400860418458041080e00c4690040c103a030401d400000b10b11083c01000c1140d0902141016030701910f45220741003160240030a401400c2c1090400c0c1000201755100e40b0898040c40d410103c48500203a111100300c03031a42d01b02e0300701c4045a4a443c0b54030f01503503d41c80100021500c613000010072100d410103042c2550340060100c111b50722007118440840001051101842824443d041482c0140383c0000d4001b240d0003140800d000808203000c82c00407c1070700310550803500c0716003803400c030104604020309030b01c002c60741790016400038006040181041c0e00105101c511a009a030b08240d281c20405196400000e0419488001d00041c80345402c285402031703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 615886088 1250 615884838 615884881
    0x50705070e09160503010b0a050f06070f08130f0501090311011107120b0609160c050a080403030807230a1d100e09010806060303070206030a0b04060312111c0f0507060c08 75
    0x2445100541070002c1e05042885c818140a114280004ac1107036503450100c1c2c03070955019044101c030075001c2c00d00740503a801c080e1045e002918010004107114032200c40d00d01c01c07a00d0503543d4045003410b564502c0501c808089066051042080300305003040814041c0c2000b0341858144202c0d00c0215080001c40700304003500c800e014030f91441c1401096060040701032a00e90340e50803c2c02400049203042450301c5d4107480d02800c84000810084205640801c4540c01103040c1d6850b074015844c840078150020b18010342800c6410010801000f1060045485581720000c414a00c0070340c00e501c0d000303d200c819008410701c000540d039103180c09580c5043390f080da02420fa000020300e00340c506440030940d280300c0c45001070300c68000400080c1806030180c21a070303070310200039000344441a500e180040c6611001045074011441121010052500c006508510f8100c26015541403040d40201594030507626004a0200302c0e04100340c00c040341c1d0078001d510045030303295174007105842c020790080302c902451aa41e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 615887338 1250 615886088 615886091
    0x180501051606090512030c03100806091b0a090603050c01020f0a12120b041802030105090c0f120109140d120c080a05270309030d030912050705070e0916050301 70
    0x34801d0a1100210004600e520550002d9241d40c0ca00304589484466480120140ca00104000f4040c05a00142d03001d101234455800c041d64592500360784443d0119510f04160b841a0101491400805d0a510340414082d242e0800180c66050b00010b940f940d0b001910603510030b18120722296410401503c0f43d88106000e441c218001d91360300352084241c42c0b181000c001402081c19140d900541c003c00300c65900900400600e608000c00c80d6002048038420303440f039440d09000131061080400e52070942e0500030100541040d0231000c0000c980c5003680b01d40d4103507503102c402300c00003481c040c400c002c103640320310081403454004d200c010509216030345000354090a025800c200d0941040d0b946402034400900441d0a50704c6100d5254203a0b44040388120982d80c1c10860f1280080c04402407550000a03404e03205541d0050300d06409680c0d034001c1c010000281c40310115070041c4100d025001d102d00c110140c8200d10b5683c486851400c905446900381a00a20f401d800325401003040c2c4002448107500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 615888588 1250 615887338 615887347
    0x8070807230406020604060b1c020d0614040b01031b0f050607050a06051f09060b0301050909010f050f060102010f0b0a1a0408030d0e070e0f22020901030318050105 72
    0x504440000d004102881a403044080354404500d035201c0303821800705062070710385598540080d0ba1782010b48094031101d16002105445003008111101c0300200c41d01802400c00c09a4240100f1042c001800e03039140b0f5540c210800004000120540128000c450341e82103541142441d11000c1d450040b41480034500b0502013102c40040d46030703081101c01c01c4540f1901c416060030540d041292428005020303a180800700419010300411041c00035244107503014145031600681d40494640d801106a0801c4c140010080351400004050340240e00c400081000c82c00d4412620641d50191260340080e03c8102c100201c40d40d09200d850481e60003890f05000c007200d0040411601945c5008a901b0505482e440501d101000400c03100102045021280e552000b0790000005004120186080b4042c013100050b600710400340301c0780140240321240041c1e894000c0c00f01600030345603000002490071400c50402503601c009207903000318044e1f26080c010091684181d41ca1103a40d1700113a0502800b4007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 615889838 1250 615888588 615888601
    0x509011b0203071a0c09041103010915030b0109020313050d03060e06030a0b010303081f0b0403210e010e040617010c020105101d0405150c0d050601031802040c211b08 73
    0x4d100450000244420070700c16119448080c40602c60314140740e40250802015180b0700c0c1d1464006d5049515110003080f44c0000b1920701d01441a4038171020300510896801480130402c69401150024500050440302140b0741d43c07580e0425941d030f540c907408265624030404c1081e00b401c4a09034480001c0b4081d01802001e60344138400110103000c081c003008009800a0700d00407a007110a41074040342945c1d007940c1c5030740701c1e138560b03d96120340412500301e4519406600070b150384405e43c000504454440e880400c0a54004443c051258107049511540728000015001d400c01109091200000b0000c108174041c11130207401d481002d003000c1006022404100031310301000c101c2608481d06044d5040321070310780b41001443d1405c40d84070404240121410b000e21610f40400074113801c420b100040c803699981000540c1125140c140300c0584e81c0c400300304d0340010f142076808142101c016051681c54501e94644d00c032081c1c803c1d120381d460a41e80d146c241e0461240c509040b0501d030750041c51b200c41d46182c2423 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 615891088 1250 615889838 615889853
    0x609060703030c271802070305040909020109121a090610050f04020c0708060702061f051011102004060c02190503120307080718050118090509011b020307 68
    0x4103000d0105641d80e0b2100d04541d1081c00901c42000c52150b1025050700c0110f8010402d440a109043c503e840543c0c804071080840d0007650801a0103031a510b00b03251410030080003802c134808049042120b00030000c00c0c1c12600f45031144d0002d01400101084025481d0300f0403c0340c2002c3c080056940c850801c105690420b102e00c20103a541c1545c289070240e10940100b8041d0041c1d036100d018070700407146d01150b0301c2d0001410a00c0350540b40d0032284503440784d05040600f18100a81800c0140304d40400f07105904011801030030400c103034a040e003010300010303480609001c400722465540c5030310307220010b10b98040d20000110a007a4007542c0d61402c0d00e0100060021080c074030f4001d029000d0040d1005101008510800c010306010301038500340120a1000b1130940d00494603d0045641c01d0080f400c190301c01c0103088100700149100c10b0f40c41341007a00550307040c0013058104090b80032030300010460b00818001e90703000d483d80340d0001c2840002c4441c00d00c1410640921b00d030840d8024014070303009c98441d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 615892338 1250 615891088 615891097
    0xe0f0304050f0f031207051c0813050f2509140714040b03090a0213090b2e090c03060b160210030902090403170117060c0a020f07090207060b060906 65
    0x11601003510b0844000440d80d25015801240d5250080d0300100c41100026001000da1b43c3c80741c800e0f43c000c0c0b403011301070050500c880c4400710b0025510078000364100d503502d503d085582d0b0250b0122a104155070704500d14000551100c90303210b8803403241c4461b40b0450241220f000e0076400300c0074041c01700388944190ba00c24008100e0000c0004190500c062044500c0440303015000060b0103681ea441c2c400005643c0e00200c0404074081c3c03440d442911000c0007070b445904900d50303001d030700054192140f00342c941c071030181c00d240000c80341a452040516849000400b60003481849408214501d143e00082e08480607680031803c00b42082022800480900e1426016564100c405030040c40038020210000d1031110f0000350403021040600040c036402c07a4500e000d50301c4c01c850300700080c0c4e00c80c9100c650340c9024000354a0950b0002001c1054001c3c0900508038088071403044485091004a500b4546001039010400d1194002040c0050205a018a1070f02204c00d65070340f880c24102034081200c5118 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 615893588 1250 615892338 615892349
    0xe0112150c050c0712150b18040206040f0617070f0206160909020a0c0b18030714151003051005040206070213091b061b02031e0709050f09010e0f0304 66
    0xa071010800c04280c0a54155442d041c2144101c41038151902c180340341c4010280d50690705110138400310104041c00d40101140050068408400c2041d02c15a20441c0c2070040c04c1203034002c4041c40042500e001401070b1100821082d911030b12424240380c422400900d01804440c10840d440207106601600000c105812902d8010620f4940000b80800c868a203c15044007081e140001742c42142c20b90701049048845009242142194550000281d400c4840800e1100281c01c24009040840c2e0b01030481810230f50700405544800c004c0808054076a0000c0f101c040d244545610280300744001000000d080d0340340c0110030880d034141900004c02a00400318001d02c560407a42e00e500e481d0115400500201e50300500541e02c5546417140c41200100034041c80c80000c186903094003995020b000750744d018640180c09018290307495400396004000501d0401d4152045040000d04810700d0f215951045107000108021820158901403e4840280c0445910b500180654429400201c1140d00700c40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 615894838 1250 615893588 615893591
    0x110c07060e0925050d0f020903010e070612091a0916080c01020717011b0e01020f0303012d1701050708010b0a02070e0604090c09020c07050d1203050601270e011215 72
    0x100503000700c0b418480d0326100c5c00c410303090800e0201c2c02e070010740207030460041c00c4000740203651900c1100c503926501d034441c400003c0c40c00f0440988a982550015007000cbc01060b140002400b260740100040109482c42030040e440000c1c002851407454015002901c1e110002c0c00682038200c00003541c0d980d00380118503044060889a441c844d1003503001071402d80d00c102104040450950340a0a91180300e1203041c098001d0a11110404070084212130585140d400341e4800405c0341002e0081100000c400392050940580010030b9a41e000204c003540b1809410020905e4906404010f14144040e800369007d104180b00c0420401d0b0045140c0041d2440300e04415129540c210010b0050051108081d00001c0400408100c0030120740040c05e400542d08121000c0d290358a0a004410003011300240c010b2200440c944013030f920075007113203802007014940f40c0880da0342a45403c110800d007c0759507481e000c4072201013080c82081c4014500401d0090007030805e4008070303124a00154403c070181d0030582d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 615896088 1250 615894838 615894901
    0xe1c08071101034506050925060801030f0303060305070b04090606080c12072010050105010203191805090109020a030b0f1c080d020c0607080c19030b0103110c07060e09 74
    0x22461881380c091a94000d1018000c0d81019202c041c0c40714240c2c0c10085062103042c10500c8046400c150603011a203082d90340424680ca50f864505103610388070f104400305625a44000b002c03e100704500c40141001406140d0740b58544121001121281d46c0200184a1480d0400808480e0304041d11010784100d05c5000c80c0303590701002200c404c84101001141c212099861135000c100002e040021000811000c111591300d0b5001a07a4900030f0348182c004200d071f00045c4091803417140e100200c400b220528240305090f1200001390001c0c0c030036003080c007a255002c00c1d0b41d011240c1c5401481d8078600c0555192041410441c041050104004180c0802400c00f404420406c00c8010840e2070031164808211345440715803580710703200c610646981d1300141280c404160050b64030380c12503100589400101c9060044400203801401442c1d0b860340c18995107600080a500d03000000f0300d42030700c1080c01f42c1200c506242c8007070070741c045106c0024054100c40d000c0068040e03041101c8407000006124103c01c5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 615897338 1250 615896088 615896201
    0x601030b030f031c0b0301050112120e10110c0103090b0117100f0501080d050a090e190f1e0902030309010507140a0c1d070e1c0807110103 61
    0x42000e07030b003060780003480300003110a09450205441381c0103001c900c01c2400616104030400d0300b61402802400fa00420218a19001030b061100c41110034000741400e00303a22458100062001c03060790101004981161106000c2c00d0090000c81c5e540d810034241045001e45688502060b020140250301180d42c1e050b01c0b107540a1f104016821841c52001814420700d100c82c43c0c0e000180100b17100302d042900c964040e0725801801101910080d80b025503a0380d50701f92030446940781400015001032100c402d00202800c060500e070240085140c03c200d004034480c0c0b4581d05000104c031078140328046040c41c002e5100016640442140c5c81d01400b46001901c5502d6400d1a5400e038030701180e81e0b146441103420100c100811f008481c41180c102d010261485108030b0b9601017019000c84107075001410300700000c62185401035a404200d1048201c00c940f888943c0d03070303a82c904e03484060b00b5507044a581010710020b44c0c0c180110341070044031070008101d803d04000000b081c3c42007207609014070b40890040054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 615898588 1250 615897338 615897343
    0xc02100b030c0303030c090306100e070c02040902030f0d080105101224090e100b0102250b280905100c0204020d06030b0f06010801060c352d030601030b03 68
    0x9090300b006095a0752030400c410b40f00e0142e4008003e030780c003d0181100146840340203134001ca0440b0301c0c800b08080386031f46198045a204650500072644107075601d840d000981c60810982c5a0b2588520041c100c1c040c4c0408050b0991105074411032042d000f001d1038401140d800380c0748034030488240f074001c03030600c80e5011623001110b0101d80101c1d03070407a19600081c50500e1038021400d0002c480c0d050340c0c1080c0000350003100769074813040f07864056446080d075407585084c0000389058181440ca081c404e01703515094000750307a5100200d1164190b0741c101800301c910a501240e0700c0f110380c0e070b030804150701850700c40420000d4040540e03190a000310700d6029000e540301e54048902c9080e03da001000b20640320f02c2c0100d628241035400d50104d4002c0303000a0f0781035000e9042c0d64141c1d9029121041001c41039918009001e10051202c501a1484c040781d008081d074011491208205051446884a0030481c091519001107000c00003030300c001d6408031540503035103070460341c12000a1070b0220b00c060060300401e1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 615899838 1250 615898588 615898603
    0xb0906071a070f2c19081b0405180a0b0c0d062c091c0c0206040e06012d0518130b1e06160c15170108010c02100b03 51
    0xc00384403040c1041091a84002c0000b00381c452a2150030503013440c0114034203082120304c0700703034000303a4440c420031802c0c038203442d00c04094026142400d40c5151940416400c103c004003105d0908003424094090341d2406015030750b4410902000900c840c0d9401404542d202600000540694003042c0818123a420017011a5040700344881d0502041e035940109448611000412140358021522140401d214001c1440e000d298002c0041102d1002c2c03d04070019404031840c038005014901c1c0c66000181c582c480503200030011594150402e150050014100c0d01e41d0f8441c40c2e5500004901440e2003a89004800140318401d240194a40c40c100c5014039140c0d0780c0c05070082e80002604001a544009a00315070300c0111b003030342c01c80c225801c8400e0780b400082c0510f000b1039114205010440c59200100c030310b0082103001e41c0c0310084143d9518048143e81c4000c0280b4000101c104a000301c2d4458200c401c90300519020000300180c10070380310000e4448801e0840800c62a4030303900740000381d503410080c1d04e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 615901088 1250 615899838 615899873
    0x504092a050a1724030a0c030201050f091503040c08031c050601051c0605030f01060b070f0c0b030103140606062802071a1812070605030a091202010b190b090607 71
    0x3034902d030a044c100c0d81151002c2c0c00c210118420f80d243c1c280c00c01e00f404108801819400808031100a085500546c0e43d6009503c10310140b150500000c09150b81390300105450041c0101510380d00c1c2054109282c0402d46a00000340c50b81c001c11258060fa003290702c4824400c1440071000601f52075020049032640701e031000e03090041032191030400010a42d03a11240459004408071540301a0f00e034540390a980440c8100240e807a824001034001c24000c1031601413043c0718504001582e5203070594000c45070000c1c0c1065070080010110400060307420010715410910841e145170a181801c403020144a814100c0d109142852a4140d20300d03600802a00300540150b44114000101d031000300c940e181c1004074507402c7e1000070450b400c818280a94004400340c0c0f101c016242c2d00742007150075221544041c014804d01a65003540b074000c04c1d6081d0b614140c00c1c25980c000700d140c1018404014441d4410019084101e49807441000286103920403105a041c0503103000c3d0700ca6201c1c0c18207803100c00069101 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 615902338 1250 615901088 615901127
    0xf08011418011d01050a06152304080d02030c070b1201060507150507020c09060411030112030203070206040603060e181c0224070909050606070204090615060504092a050a 75
    0x140e04289406400c401c0c4900d1400f041001029030340c819918112408104020108021701414440c80c10b10640c01710080c2749202e4400c1c80e10355101803807445c040003105640010b03000860b003a0352141c0140a000c000b020215542c80c205018502e07030814216040c402c541c180400041c0e40300810000e5040c0041070000c05004000d1454070800107074540c004110901e204000c544001000c40c5850b00c01d44107040e208028090031607080c40601801c8405400c4140c0079403105001d0300005903944801000a00802d0380d0102c1c3d402d10b49004194652400b41074683e1450b00040c1600046034000707016203a04154207050760755016103030310503402c3c102c81041c0e400a142c1c0084070007400c1040c00c420207002e0041541c402c1c030000d44c1d81041c80b040702d000740c07207590f031040c42008010090310303098200301400c5015880c000342c51031100e80d007081403011513441640814000305003009245480e01c1494011900301c003280344480522045d0500020700208604180038000c02c01c04c3e0341da44222125121070510048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 615903588 1250 615902338 615902381
    0x30a0f050115090e15090a06060b040509072615060708120619050f01050d020c060105030d020318090a1104030803090d110607030906020c030409060f0801141801 71
    0x1031a60207000e11588082d8030207101c0c840003407100300c03e03c140c43e80a40b108000e03105481c980382c22a043c8000144c01c8060358821343ea5407001080c0d0510441c0f0090006d080c88580d0f840c9000c0c11310000d000d00030b280702d05000c85003140c44c81c1c800c1c42424410039040856034200003943d03580d4002e100c00f1a450032043d00890081214020006000e00804d142110122040c460343e40e50f400300030b00c1020b124074031001c02250003410401401c0404050b000329205040141c101050b106403001280c1102c039003a9441d84c04400108440c1c20f09100078140045540b01075803420017448008514484034141840c020040c3d0750008110b61099031140c1480014040450f6644d507032410500e800b50000c5e0740c54003003400307060039031a9003e00441c40000c94030a0a000b4100701d6071880420b0b8000e00c1c50540c19500e00342c080000c28405c25060000300040e05180368000b07a0360742000c01e40042003000d034105d90002d03807411404005958131082220703070000103c8003940f69002d4100c503544c0034003044c02e41c4813881041c1d800c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 615904838 1250 615903588 615903593
    0xa1803022401031211150403020120030c0412020a090603050303220c060f020a12021023041b050d0803010915060e130e03070c06110604020a050906030a0f 68
    0xe0003860000c00414940038030301d0281d207801030a40080c4001444c60103080116885135009903080301d0300300300d48030a54000080900d41010b20010840c0c084005135555269400003498440c1a40d150722080f240c140d045103015104160355110724080c400240c7d06044caa907085590380e4070b6900250080f500140300c2540d8903c0c010356260000c1d84c0100c141602c002841c0304100c000d8015001c000d0704520f400c284c0718940304055810711100b030b80b000214000c050003180802d40c03220b55030701105000c0d40109002c03c0e10305000000c032601154865204501e400c050308000c201d0070f5020340c01070341140854100e548403081c8600ca02032540e12064100d0325081e920b80038801a0009541202c80c801c40a000d071200c1e01d40380b01b41e54070f0540906000b10b44d4001d0240c116051080c0c040c540007a00c03840000c1c210440c000203030301d507410060040710b80640001003032250b9030f0b0080741d0340e0700760804600a03c0f040c10f00380d0025505500354010f190061402400040380340c0e07010410080f1658000d88031200c040c42d10f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 615906088 1250 615904838 615904843
    0x1505040e151b04061d091006110606090114131505040c0201181e082206090b07060c050405210d0c03050d02090301020f0a03090308130503070b0a180302 67
    0x401c5044a003484000002c00803402480d82c525480e00c1002020300c0d20b41450f8080d51403401e00c1c54042d10200311200040940d88400a21a000d908002e01e003e0199203020700003801c068024580d00c3c040c1c0c003ca402c4c0186a02d0b03024080741581c010441d42409496100d000c51020400060580004c3c2e08102c29200b901e004440f040095440c145c0c2c05000c84071550340b00b6400d079105c4c848420002d1035107044610104405000d540c03078629001311007208202850301d51004a80020700000f1040c6100340440c078403803e54491450081469003440e070354a61405240039042d00442d803010708015120340ca5404071030f00c03480031500035040041c40140051082075151198400b1644510740501c107040c43c4a244a00030049000688c0d03060340d5181c503040700090002d01940048005640540d002e03c040201c0365400c0020340b90b4440303236030b030005115121818001e200903405442403c07007031000089840400c1e4088100c41c01c2d10342100d005c01c80350b103030004100010034443c0050544240301c03100034800c00d82d01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 615907338 1250 615906088 615906103
    0xa0905060d0b160915020d110f010204060305150a060801090207021c1101030608010b0d2003060103031e03050f240603010807080708010614090a02090405040f0218191505040e 77
    0x1644d203410060f80c031440c0080400c2d540c2918040540e10100569141d984908410b0100403108400c0d100e070308180c515041e0030381e0043d4000c540400e442c5c00c00c000d0380c940854440d0085140c12206007500c3d1b440c201000d81807503010701401c8025a0002100307800c2d900d5903625084a08462040d0243e41981410070700900c80d03a400c0d105c0d000a00300900082c07804814080c002d04144028114450f4446c6031b6141c01030303541d0b400c110803100310070919007080c01c2d50103208284c02140680c80c1c503c20124160102250300e09030000301d0b001d244c5020107020b9006030125500768807101d00348906403146501c00b0b64404808080740c1ca14bc2c0010004004241c855004c5000030440d6004c100329018503444480317041c241c50ba2030041001007001c903207410440307143ca4207015400205100700149441c1d800e03000301f4150b4008a40c10b072003262407440d50000714144003181d00b041815590080c0700506262254150f084102d400c2d40710352940300c9040c900b160140d20201402040003c0081106000386041603444d6400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 615908588 1250 615907338 615907381
    0x507060f1704030f0f02102a020f0601050405091e100b03120f0723031309051e06010522060f020d080408030a0209041d06060d020a0905060d0b 63
    0x4058076031038018000060480d00480c0e040c0c0b02e1300c180b0251048200c408422a407120b03005c5103d2039070a411050024810100074000d004500041c4581d44002c1a03448550342e040321085610003202d07038000306004a40c49040d035004841c08202512960001840e20168442d0302d00440c8429030720400c005400540503030011b2500c801400201c0c1000c00305034031303a406010b818036030b900c08200402c400341d800d07001042c16a200325100400d08002c5404030380092006101c240c8030764000070303100d844e086800c1d40307200c0103040c401010710092038198880a0401c030000b1103010050030b290b002c1402603000e07405031128802d141482d000080c152020201c80c402482c0308040c04540c0301e07112a107404d8408980300c40031440c00d8413074500da40c980d5a06c0d104203a20081040181d60f9092040340020f076141d000e09001041441801806e00f045a850f660400361f028014521541b000c0c81d0490041e2542a0070004035110010001980e03030700c200111718020b09040c0e00a10079202101006100190f0002c411845013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 615909838 1250 615908588 615908597
    0x4150525180f03030c0b06011106150109090203063d120c0203030103120810031523130f110a1d072604050708030d060503010e1b100302070507060f 65
    0x2d82d1840c1421424440d80400740010743c9184060000c665042442904007006141010f4000180305000d42881c1040d00c1070b041500c4400e0451b20f035581c0c8008160060030341c0007400c40c0381d42426000115003400c1c80360801e4298020300614601501492072800d90300d0801c040c2c80d96461223001c0028032020100b841224000c1c50210b04180d02403000094038180c980c0042c50046001820700b007a15051401090030846100094011000804442c410106914202e0022450f0310301081c031081210036400d0364502c0c40301c6c403c0400c200c000307084050140c041e8006c3c00180ca08a00ca08040002112090710a1f40041c0d0424001a80640d4955600480751140030084042d032101c4008032210030a00140d8428188807000c2e1100220001407600d070400d126608644502d5aa100150b09580048000268031582c46404210754102802091440d21618001d48032400c101c3c0001d28002c00c803a030b45a4001e00304c1040f98501c80f40246c5c110364265822200b201c04083c0d60b00001002120100c10140018 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 615911088 1250 615909838 615909887
    0x8040f03020103062103050c030f04030f20100c15020a020a1209051503060d0204140a11070b070f2c0a12020d0210050f030112050d0804150525 63
    0x561170b28440205101100c1c0301d411021110f9103040703c00340c000c10103450f0140405c1000820814244000740000d5100e819108044000350600c00b040c1a09000c0034120348004000b207011a9070303041d4900100c031a0034103101c45404924101240e6403410800e182400380d2001034240241500065925030103842070107101041644007400710b5a40c2030742c0c49000e802015402c2e004100c021000091a44000050180101600b144c0c0025080d5684203074042904940d04d000d1001b1000799000304500e4915801c0328514124440d40c40c609214001040c0e9001c00038050701c040101d91103018550b240b9500a80c5d89615120007213405032403842d161001a01c10300880c86c0c0065400d40c42201416240e4009102c1b1201507902c0c2c081c0000c440342d280b4090100481048001c2007106803501550180014500803154a421890028640a500c070b07880702c18040f440d400c00c4005510309002410b40d00c400500400c2945400c0e6442c0040c2c02d10b640e0f4801c01041109200643d0740d8840f038403011080350038a840180c2c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 615912338 1250 615911088 615911099
    0xe090112170a021c0309060f1b090501021002070311060a02040e010e0631090b04020f04110315060d060305030a02060c19050319110301080c0901060c0b100308040f0302010306 77
    0x11442211800809a04100c3d0742c202a0301452406201c51130103400c001c9004035503603403490100c900020300c21200c0d91f40e600b940c043c0e03803c1c01c41c1610010800390400310710003410040041d540d401c03841554000c4a400280700c0d01010b104121005641c1030007030843d040e50500b682c02070084d400502403a00006c0300c4c04c00000703c140c150010381d170240c0f1018143c81d60b80660541c45a000680c81c038a0090912450b0064055100c220321600d440c180c0920380c41256401d0504c1080642900500d0b210310850500c00c95502d038800c03035022a50091680c20300c00c56001101c4002c64038901030301462941440c82c007000001849400b0000301400c240e02e60945031a5514645403082900407503003a1240701c2c0c940c41000d0350141c0180300a641005600d0711080c0ca4500031814001075600756400e1512211010004011814042000d50038419048611044030360410700000c0c0341032004107001d400001040702240d424040000305002868000c42032a40d81d42d142c0810b452007140a202c2280020b107440f100040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 615913588 1250 615912338 615912383
    0x60c03030f0c080a020d060f17060109140c0c0f15070e0108090d030c0e12030705190f020f01050c0d111501151103040b03070c020f04180b070e090112 66
    0x106800d594949040700d403038a0032207000a402940c10007a51a87d81e85002c04c40e00d1810082e075008080001d403141085410401040c14800b060b4025440c4501701240f2440081642050031b071700c00100c4048035221107046130f00c1480c2449580500e201d40c0182d03292410448254801d451145006449084001d07034840011981d141044800c0101500b10a2803560b11074802c0e040350000036a0352030405025400c01001400441141507421340c541c0c000141241088814040001802c5045100c0e032094586074540c240070400c980c0b002481035412103544007160f030040d0b00f543c003054401d130116085612001005000492400c1080300c052084201004203028070001d201d060b070304184608800c0c14503140c016100b0440480460300580400d0001046c440b5000010318840c01c40c0356550a0403000b140144940300c103952342c11900036414450000150810050506004c42d440101c050040d91800e40844544820b0602150310084440000807184000d40d0f00043c003c0c0200b680003401d40210309183c8 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 615914838 1250 615913588 615913601
    0x3030603060b1e010e04110408030a0f020708070e0604060b03040501050103050705150405040c050903060a05060a051503191d03190201020a140c1509010f060807060c0f0807050601060c03030f 84
    0xa402c4640c041c009250b510410611170b9051000d0400b24014107003441d0030032160001c0d001148180d101180c1c21110075400307003034006c1c0000c880c0040c0c0002030a0007100b035258409806921500d03c581804260075884a500400040c50101001a16400c0c28607120740600020b100640d1a40b040d804013103a64600030f2480004004244034152030989010284005001c080d081201070050074440c8040d152014005076100b2041e94800166900e8500c0030031806282c80d41000f401200f0740c11000c0c0c00041d02200300c9400c0098840c242d00c00b92544088000600740381d480080740301c0325038038280c020303258000301401c3c5500102c1013480c03c3e0319240404038200c0c012035070300c03400054206964400c01c20449005142e080e1002c000d03252103039480115250403400640d900404c40c3c0d518541c50040d05054422034000d440040b010b4050503150640040c050a4800b42c050080c2c410041072404115204e0119461a6804810340d0900d46e583c1c4000b030161850b00d18240c011a04166074295149014403851 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 615916088 1250 615914838 615914869
    0x60902160b0402120d020f01060e0403090612090c06090303020606041a1201021303110f0108010806010501110309130b13021908040201110f0f10060e040219090903030603060b 77
    0xc040304410344503018a003030302500c140d030003009969120605903000d00946406000e590010030100d03458004d904d0840710349500c103040241e14041070100003940401d0000c00c03110300780740841c3c2140154640c24014000c0d100010800301d03819a0004d005900400c4090441c0d0182c0c0994089503510024401964801000f80050b17081c4101c0ca8181d40c90b042a80700c0c1640c510030300060038542203d01d040343e074088a4209540741c20b0702d4006e075481490286043c140001e000e1030b010000d54904a41d6540e0f51784103000302c42c10f00032181040d245225007003040d41d101c41e000410040300b105400500c80000c003000044280140101c051240302205140201c0f0308615000000701b0300c0250816044071000000b038003c82c10004034240000c24110100300940365a88241c0182480100f81e005071071a142045100c104904c1c01c1c0740f410408803402c05201c40e031050301510303043c0c1710003298045509040c0c0c0c180c100c10754031032034607185401f4181d055101206680c4660000c011a6280c2c03410480c0111205412 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 615917338 1250 615916088 615916117
    0xb060715020a140409050103140c130c1b150b0102070605070b0c0c06041119060e060a031407080406140c0d0e0304090c051306170a05190c0210060902 66
    0x10032411469034000c0c0360701d0030a454a10304030071042000d050190321540c0300344482501c03800140140003c040c0c0c10407481c60050002c105080724040401d52400c0e03190242e81d482580c2e4140c03103814501402d0b0200c0d100f500d0070417070b1940c041149083c92142880e000034a50846c0740018a480c035500005080e400d072071f081c3c0c44040c146142030362201c18081004103a00f000100034044454042d80401c40d06000f280706101d0f810070756041d60140100000c200e40e03a1084045900020000c8680040035148480029104d003540c03200341c070300164040c0002084c3c0c0000c2c00703628002c22004580c0100c41d940a9032151009014801c43c10303882840d000d805441140c1d400c2802c11130401d0086450b8006070705000c6007400ea9090590340c0984404480a03040b20700e0100e14001200601c1d00000d50150b805401207050a03071b052640b0314600600440000c00b05030704d00d0b40c2c440200e44c802035144084480003008100c14071082c8070040009460f200d208034450401401e04102182d000203c1c001d446010141e04032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 615918588 1250 615917338 615917363
    0xe011a03011a070611030702060a1e24150206010501090f0e090f010216110409030905190302091305060f06011b0602070503040f050a0806071b06180303050a0b0607 72
    0xe80d420100b0451030030042020019540000c4c014003581964030101034402d6100d141800020313082104c01499982c8962034140c10700d0950050718a40030003200c40d414005080b54100149801c2a0328007610f0110580403007100003020004480420718441056083e03551599a510043d1920100d501a9118a8814400038040007541c0e10300268456501c8080300d066901810b074075422a80304071102080c00404130040d00500a101c0e000d90140081503404102c80308250702d00500b290114041c8030310681c100080c2d2150704040506010103160002c0601c0d4039414a8030150804401c000750031101401a039000950105103520740d03511400041c0c50300188140e207a48000040d0405d14012244d4580c01d200c0d05010500c1000030784040c1039030076a105a068184410010341100c90b41c000e0340c407a888941008016036010340004036412166004112107405450503501900d0241e8020000c1100c2d02104030074980e05130000c174019001c1d0f603c00c000309000e00c400d00a4a00c0399500182a0a00e5202e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 615919838 1250 615918588 615918599
    0xd090b1602040f1d1b0f153907050618060f1306120207020312090105070602130512030a020a08130504090f020a0503070e160512040c05010e0904030c1b170102040e011a0301 76
    0x5020089010b054249a880c110003e13440641240ca08c0c0e103008900d160b02d03c0324404828144600703401100703090000709031140c40d180009102d4031400500724101408110140720586880d01550350803c030038044c840c1c84120188419411409501c1480002420591946085040c92003212805a00600034140c00848102e03209019400040100d04012081191700c021a81030b10142c850740c80c0101c540b10580b403400c0304101c4030b20107510103e61642c1003040300305422500003400d202078a61081180e41ca42036110341c4078a07403911552000c1d400030304100c5560100030150802109481c4215481241d054940c0141030f0345844070300a445600c000c0e103011580c400742d0400d054a0040c0c6a1900310710b045994140c032003202c40180c0e421a00300607940c4080c0180d40e000354070f2a8400e030302515508118685602c1c0200410742110300506072100382c1d45400c0060b9110342c018800307014004000c1030030044842d0014002e5001d40b04e08403400003064000300d148500007070b0351308000001d100207604590804 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 615921088 1250 615919838 615919849
    0xa0605211207051507110631080912070f06030e010902030d02060f150f0d02040e030f18100c0201120b030709050103050d090b1602040f1d1b0f 63
    0x140021240c1c49000d041100300311501c4010440c25108030701800155003074040c071664510028004505001d900c1c1640d1131800d07000142181d00c20091203888140000040d82080d481248038203c003100e100c44a800014083c81000404001d0400e840c285005010280d030662110100e0080f21032002034001c04212075446a0030408040000034000900c0020a40c0080d03d4100103002410158010b03504105504607040c0050f0b13440640c1e90b0384440c0328494440010300400b200401c15208003400c0141d0b00c1592144d901002e0480c2112084030356507050301141d0411070b0066140c1c01100a801c01d0311035504d003084032403180240c0054881000c8a92180d00545102142d03641c42450140c2e52800e5441a40d41001414000d1510400004465042d81403181c20080702020100030301c5174910302000140c0d144000c55841c0345440307c54242c51b09041c07002801912500500705030712810071400c6003040d008001400902c0c00102c040b00c0781000c040103508014030314103c1061388044818210700550600703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 615922338 1250 615921088 615921139
    0xa06030c030e01060e04020112180b0c070b0a02220503060117031608120618062704053415110303040605040b013204090804080f060a0605 61
    0x9420045501403466080b1030859886034018150410460140030555070440c8600d682c07002510000e01030076200c95100d0901071003140b8005d0004c031424000880282c150401da401d00d591010002c0110f0502c00742c600043e4000f20400c4101980032011004041c400707802000803210090b001d401c56a18001d104007035049019a902c40301c3c0820002c000c4050344590b290306103a072042d41a00d485000d15616026480300041c0001e00401040c580c003040705001c0c151507540710000b11844c604044002e18900c0010f0f1100c1ca07480a40110301061100304503000c01c61440d9a010000c0b081040e10722540110400fa00c8a1100340e2021000c00043c450340103001c05901f9404080c0c00c0c450070601285072802d20711b5100700c034180c908603520400c1c40308205101c81084c0c01400800903040801c0803d0400018024800c3e9005064000f45000040d0035161500068101c5802040031601c417a40c0d115142e07120a440c0320b121841307002d5000000d017201c1c003074492001a01c2c0081d14041e805130514101d80c3c0d58403003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 615923588 1250 615922338 615922361
    0x2040905060f01170313140d1410050c031509040602040f030c030b07090f060c03020a29061e131503080304050d020a0314070c0512010f05090f0d140c0115170106050a0603 75
    0x384400c8d894085140c1416251404860800130300d0301e845211081d00c1281e402414030680c040081051009400c0c012615a41c840821100c08410340c0300c610b40b100c024840d95001d00840e07030300c002b0000140b0029503070100880c0d0140703513007600564401c1021120381d03025004202e04507054050a11105204888143c585440b0340100c9015206586803040407d1003880604d200c1c1c201c6141c0300c8482c048240315241c01c11001d50b00700c0c1407030765080440380345480c1040025000b6000341184098030030140e0001d0102e8a400083d9401181c2c5074104822640d0040b141600c3c03a108260340822850b01c0040d056505980603a540746220611489440550380f0204058610322101c0c0408603441c0d80d8044010b060310008800040c602d80407548e6034054400041007a03041d9000b0800c8858241d4011540301800342e02441e10743c0002201c002401054007481c0d40c4107041e1762a1401e00008000c00442c108185ca611414010b10707050502c00c61801c0c0c1d25140640c5400c210301c030000b041021f0281c1c01501da102c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 615924838 1250 615923588 615923599
    0x408090a051c02150c190c0e01090e010f0e120d060e04060b181b030a0b1f140f22120305040515030610110708030f090103050612031602040905060f0117031314 70
    0x47c0c1d9003200700c403104c0e0b0a2b00461500e990301c8014501c0540300f4400c05401008100c2c00348000303241070070081d49a00a072002d13200411800581c604040c0d48951000d00500507513141d0001905050400b48002c1031070480032400744802c43d081c0d440384010011200c1c800c1c00609000030400707420102e0048140c10192000011039269005001c25503600380181042d10b44a04074007002e400d142e0030052213030400c500301010f100c00811840d03017482c80714001c1b11a0806c04c000c010f6814142500c581c45e8480b1158840b08a120400c941c000030103502c40024800c0742d40860390a095510b03440390040705071106031265035110001c00c2e10444098012451100301d50903503c1959005940c4078022070441d0700c800d00c056006000050341c02110341c5c2511071a508881c0680d070344d1350b1000040a24956034425056a485410385064002c011581c07140c2040000940c0482606d855003403140904420003420701409880300006403c4001e2181c001054580c8108000c60f428040c07854a50402c849138a00a28250880e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 615926088 1250 615924838 615924863
    0x15060316060c0212010c180b09090a020f16080c0d080112020904021927020c07060305091207050c03100e0307110a0e0c0a02100908030408090a051c02150c19 69
    0x500071310910031241c006d03032030315120a82c5c0b0085084001c85103811070382034030000f0300c002a2183c813044030159200c1c02c10500140e0710040c0b04208811400313171a1078815006c1499840d403041280d1503001d80903c041010850b182c07014200e5040c0c1d15110240100e49401c42c6121814015181040b000740c0c00a00291210344945c2401c04020640a941e40180c410b29107804520811035202e403001e002d0210170601c0c02c608288a142e038840d10b605407446000c0c01c2549480218185c04070501c0041007810700c0806a903622400e81c50000d4441c103804a02c03500c280194500091703400c01e507000c0c920020407450080c500d4850543e44400900a511180c50340012811802280320350841c110140600440720400740c456107101802413411114160f140c51141c18900c108002902180a0380c2d0000c1c0e200004a899103100c5010a51144659001582c02801c0b003007440301040a5a0711076075518000d8501010000e040b40d54804503104501403411a42d115458424284003c9540300340b465108405100e540c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 615927338 1250 615926088 615926119
    0x71106040b0703170103051c1713051005101a0d1d1c02060a0b041b08060a0e09070605220f0509060409030e0f012015060316060c02 58
    0x9508240c1086031840400160901410340120b00c918940c881c80324012515070440d075039030ba25600c0718243c000c1240c03c0170082c144a40e00400882e0b000341d2078642510070351301d0001d001078409080d0000544080c01940e1020344003602a002d46486410300c0400f460100345072489014214445000000c0300e08814442c218a03120769025001140402d1054000c6c1148542101806e162025100084030025003589440c0940c000c41d507598848800c0b180020800000e4021502030680300b2a031011a40d40e042c5407858503900b040320302c0e00490069903800301f0305440c1e4015030100b02080d102903213607900c103070130030402c07540b1800c02009010b01840150500080c0b0810041d41c8035010380008500c0001204280312504000041980c8010115018070454100b81c501900c8680d8188805009074041040190181d0183c00c0d20803180405a105030481640003100988443c0b20340720740c8000c0300d2142e000c2081840c002442190500f400b081e07251540f40303010fa09a407178500c031a0040303030003641e44004e4414 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 615928588 1250 615927338 615927349
    0x8090411071103010510120602070f0218011a1e07030e0603010e0403030b0f09060f0a18051f05090a02072306090d020d020c09060604090e07170303130303020711 71
    0x106140300300c5241d0052442c0100309030035100e0081c03070740303070440c15519080110700f40085094585a07003205005036100441d003041810f880510b40080e400c258500fa2078000003542c842d0183c1221000081c90600c43d21020a280c2d00e031280304501c0c0c0c28041944021001020458001c1a94a1180c00c0c49000300742881c001c80c42e10b8000740d000141d848104420001416054042c90504150403583c003241e032003403a0002040710601804c0305010301c40c201141260741d11070070b000310080c0c0403040e0b0200c0000f030415042809801c00f15640c890010b500140129250101304801c42a1580100940c00a40e2108002c070004d4008440075901441d030b108109803044001c0301c500c96011034413000b404540c82e005443c9403410a000c0a120110344c082006540c42c07131390100f403058030710400302c500c1406501c0c0d070400144540142e07000750341e80a01c0c044684c0516140022040c00310762483d10a07440c2c000c00e14800c3c0303450303000c111002003140003180e101200080c800d9000b004218414001055211b1007080400c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 615929838 1250 615928588 615928597
    0x317041509030c0b03100e04030c02060313021206161d061201060807082703120702010c1e02030901032a0f030e010905031e0403120509120606010c08090411 69
    0x10110382020814400c0c00458410200070381360031014245142000e18108050001a1059526490701030020400f014420145141c0c610317001885e042d1a0f0505208144204400d0b46007240300b404482c00b0b2150030100031039030ba0321608003514080e400c0d20300e144003a1122003440a01000d02c070403074601c115490b503880c000b82103007505003140c0b01780960411801070581d42000d0700c50424070003110104405414401c0c08604044004549250a00310070104a480d50041050b0580c911451100b0440032550540c03001d6040720446d07651902da01610200ca2040c4241003d0b2200160070801c0744841950107070300000c482e040016661600c000800240001d1981602600c0f030015007803031011510164140103a0038541c0d0204020001c00c9100d542c9d99507248540d41c00e01c52546441c4505c4c400e50b10050b0b05460003140c012880c888000c0031030b03000424a0384011035107480ba0032900b00c0001e12890001d4240d11560041e192154644da1075240c08003503402481101e60300c541c40e03a261800800b003003c0640b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 615931088 1250 615929838 615929879
    0x180308040e01090501120f020f01020c060c01020d0c110a060c050405030f0d1d031f02040503030409021c2f0c150a060801020702130504080f04030f02090106020c0a031704 75
    0x19101c0d50400203600291041a4852800308207550020400308848102600d40c1c981e0444555440340b41c0900143d00341041901116804140410795459504040d00280302c03801d82c0701004c200c000f070040310943d12000f11003c040381c5070b03000603c0e400000d80c25900c581040340b2107083c42400d003603039140060f190111314658800c01c1d4010311424442c0e1034110b40804c81c0000582c0f10b4002200161001c00d54410644040c81c0d14209207401d0b90f8030074001c0754100c03000b0f0400902500e03621a202e00c1003201a5114190076007032a1848050203c2c249128460039200780681036041c480c0a410010781445810507001d01d84191008004e071074a414000c010301445030510302030710942440c10000d0003080362200d900070f40040e401005000b005039034401603014100142500050540c035075041c01000e034000c040f0240985000092701005104800a0601d88948200c80c584156a204d02c0101e840300f50304007110307170407014041c0e0900004141100260044181e88521401c01c0e41d140566823180c1d000030501c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 615932338 1250 615931088 615931109
    0x803071e0c0c06090b120a0902030a0302160515030f040302012a1b0302070509040c0803030c07061a1318021503011e0501080105060a0e030d09080106080604080a18030804 75
    0x501c01003000c9050303104028041820302d5100686000b8070580148544441800040e01d180c000400001c020781c00449a180c02904450001b60a0318010703666040c03000d6441c0750aa40000b0000300f91511074030007141844203240301419600ca0305100031011401500440c199501e9003240064040034000807005000414a02c0c1c219030000d81c009012001d20280a1542940130807100d40840e4000074900100ca9060b540380425640c0c40c10498007007121500442d02d039000000c01e103c0056424005045554020f0030204035201050b03104503403802c9403000d034a4000c901c40901c0203001040c1e07404182d4496484910310380901c19507000620004016501800d82c28001c001805241d03601d10f110f140300501c001603801c1e01da0900340040c014103014482c6510407170300090490a007501c10211000d0610028040f29440003080748c0203413903c2c00c0d90050342c00542c40c0181c0082e4030100003c1003030007036820030035940c54075500e0382084612a203008000581400c1d00f4200100107500400100001c15403141c0303 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 615933588 1250 615932338 615932357
    0x1406010905010503160c260d0c050915030a0b03070b210f280e0a11010203040b090f030a0f0f02040b0a051011160807030203010c020304030b040803071e 67
    0x582000c0303007074114904003c07062040102584484120002030845410300b0600c2c4599803800c0300e1181200c66400075020810308050f440c0510074409003652826040f010300407029414800c85803030003802c0c078090f401100c02001c5810413000000440d0450204c14012469031044030110313203820855400342c0c040c00700009020701c061400c00d0405156110344518140541402c4080c4003101c00d0151800c0070070000d80423014481e110000ba501d007040f5000c1010300c00302e0a1b007508036459003d07a500540e61061000320f011065031000c8210303010b0f40d910900c902c0c01c054400c2c2c14444684e00c0c507c007540e0944100d49a0030041054207661804407031042c4805405455a031043c00280e55041014900940b11080280034a1b03940500c010440842440c050508112110300180742c040e141d5510401881066030210b00b403800829001e0950303000342c1c000d100350340c45c8580490f84c2e4400c912018146001800200d000103c80798001d54001e8000d14045c0c1d10400000d002c40e8504400b110040c003c00c0c0f5108 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 615934838 1250 615933588 615933601
    0xa0e210306030607030b1012021309150608010807060e040b06040b0a030609020f0a03090507090507050d0608071512020d0c03020c0607230c120301060f1403060607030c0203010b0414 80
    0xf108030380c0000245410301501c038940020a20000070a2043e00034000c0d0b08900c0306000d029941601c021030100c80020000917519440a00140740c50280311120a8080a01141c11801030080e031341243c00c004018480545048401ca800d0401c0f0301003260302a031a01680e40c1156900c3d000b41c03020b801c0c0f010907155152462440a0220740441d40f00380d0089005008104885031050182d500f0164075040100700b40201c5c2ca00142003070301581003003038114500410b100e109a03110003e44220058201c0c2082955258000d13150754a0303d501c80e000d540341c12a0a42e243c3c2d44c1c40b0f84214640d0019586000d0f0920a547d02c0c03200a5424200451001940c00b180541c841035003040740c9034000c400da050074000340da0824060201c0d0100b01c8a0b05950180000c0e003016090020003842d80d03103a4400c1982912561281001419210400b04800000b141c0c41c00c200c41e0403622108403401018020070240c5001030301e6409540d02500c0b444141d9240d5603400d20100191100e009035800d50034400180c0c5030618104 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 615936088 1250 615934838 615934843
    0x1a090d0c050a080c010203030406022b0b100305060a03022701060804060b04050601090306110714060601020f0f0703020d1e03031d07180216080f090a15080a0e21030603 74
    0x150f0248056512007003000c11103903008421250000e400280c090b036606282d50724484482412012014400d4105d284a201207156030301c5503172030002c00c990000500e281c1040c00c80c01c1d280c09803001540a18020001c0005180c0403000c054014404240400b80500c99114910700e40004d030f02c010b0224000d1030400c42000083e00c109541d0001c100d03410491400d04e500003c201c4c20007408000c12850392610002403102a0400741e41009a02269205c80240f0b0042200e031030b0002511642d026210704c000008103024046008210040c0140041450b2851502081003c094402056890b1030f2407080c4640c01c0e5560070401c5c1d007028001c3e00d0214405100c0380380364000da22040d2011245030058041400382c401d00034044d540c1091201005610341100104403071b0395804011004041c50380016501d500d0321007a00151109680c110341480765507a980020714110a40c41103403100040c681800600071614592240c040c0045060494140c038803a004425021300c003035014110400c00c0401006044d03c1c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 615937338 1250 615936088 615936109
    0x2011d06072303070f05130906050414090a080304030915080405070b03011a0c010f0203070810150e10030b030d110609031809070e04090c0801050f0405071a090d0c05 73
    0x6281560002e0304046980a001d000103003101080040144640050380d103e102520504158408810341603a5030709600c5000300742c1072007814052403c006840404d0f00ca0100c50503c10103142000d030020082e10383da201011740c40200700320140f219080b070100d243c800040710360301d450001d610b031180903007071a003802071501d421603110300c221100400040c45034a0401c42e038001c1251115405d240c582c4a030104090140804842c203d00c0c5900c00300030008041ea108002c14082c0c0400091000115200c10700074203c0010021020301042070b600d0012503604180d48034400c8001e01e460006a03440aa4001038280300c40d102c00040000c01c142c0c01c80f503050100788403854000e400440194584001c000d00c00c016511546045031041030202d0008070458040e01d011a840000140208022005494402c0801e0307424011000251700e404006a2110b02c0702441c00c0c06076030007800a10b1828984003046040ba424100c41d021049004c2c0001c4041d0b889070a11850668410f904420401e802c00b41409501c800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 615938588 1250 615937338 615937367
    0xc030204141501050a05040321120209152d0a030b0a030b010302061b10090b010501171906081c020c030601030f1e140c01080c04050303160302011d0607 67
    0x8107050100d01c180070505801d00780003e0074103584481d0400350680c0c00d40103a620141c2000caa50040c980d028001e02e11103d1009010784911641c940075014400c1280500100c590304907450402e402e900b01c0c03209001d06001c100d0401100700098040d4207500150341e28074a03010b4410004070b504c2e001d10340c05008046600205640c80304185103140c40705602900184006802100002244d00c0c15982d40d015200b203401010080b00c5500400c00741c118001e20f07680c501650480c052100201c2c50f58801c6044001d003e0000f21024155182c108d0b00b280781c1d5101c025040300306a51004000b0300184280810540c4664144400d034070841d40403000b078148480d28030100d120350004801400000c3c2141100910150026015003004270001440404641e5126010f0f004498000c560945003c00103840283c9030000c1c1e83c0c4904d940c07200b00f10102039000b180503003545500244001402e00f41034401c920903a5000e44004a11a50501c1024039034405450380c20009403c03100810505503009031007000c2011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 615939838 1250 615938588 615938621
    0xf0604030e18040b04020d1b03030807140712112506080f0c0918040f060b09010612050c040504020f04090e1203060f12010e030d0e0f06060907090902070c030204 71
    0x440100020080b00005100801c0d03003d018011409540700c00c00040e0b40c55a10000c00c1401c03403a009040c400200c0f180c130007200015074100001300054411030359001c07074041c011805820320002e60707107100e020f03541c1613030a02c00c008940b0a141d600d001d04000d80034100100e80250b84460841c24140740b625036803900510b09110f000303814801000d0ba207121007680304554000c0544c986001c4000550501c41414a22400010030014401403000c4050080c640074031138581045191503060a000c8010024030400340451801e001c0743e800942030360041a4031018020304c0c03600d45602c2e600010101e0704418000d14030f5850100b018404032800e8072031204504a410020000d01075210380500a40c0b0000348168090000e492a10311140c40e402c1031103012030382c450000c2c0411003201e4680c40c0d50303800240c400c1541500b4141e150a499102180c090103110b4840040e00e00e56442c2c4061005c8800301403e49810040c8000001a03009080c0c80130f08449442818804415403948c010001650135540d000190312 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 615941088 1250 615939838 615939859
    0x1b18060e0919111806010206070c050d0507030e09040305070c1422020c010e060a0b0f0d0611130303030507030b18010510020a020307030b090d050a02030d090f050f0604030e 76
    0x903000203503094022020802024080700a24003001c0e1910a9109141c0144131116a200c003001e024100603c80c840a0b402c48080d9550b01d00f046846140d11103019080790807401c103c0750310ba440740000b00200d902038201078801d83d00d0580802c0c402e800445040c2c00060022481d481001140000c010061022038501000c000400000030058010303ca80c1c084038280c40c034291b906009840d01540c4042204c500200701a411445036107899040c00c540c14a4860301e0b1202480c3d80c0e1070406902315814002415000c0c29101c03940d01d00f0700a000c00742010b400c02000340100584407000000281c040c501c260360100c4c403401e1501d005000c3c2c3c5c030aa20900d21514120f084014039103104001e89044a1088031020600f000d400004ea040404401c8069010f0003800e80102c140010403a400b40540300090071541c1c9001c102c04104c0b02e9010315402100142c1042221101d10310b09034011609940c0a001031084841803695842d240003e00324111085070400170420003810780103810700ca0000015216210072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 615942338 1250 615941088 615941101
    0x1c0807030b18071e27030609030e0f180a2004080a0b060901140904080d060305010207120c02060403030c02011205011e050f1c14030c10050c13030f1b18060e 69
    0x401c40c017501c005400c04084103444d2410710f40f8600702401150030000801411000d17040081030412240003490040c9209103000d001d82c00c05c64ac00056282a4003015800342e1180603e41004e4207100250703443e0000d0340b0401d647c030340407500c00900c004d094080c01810740140d00e1800c80b100da4401040b4510400b401c2004104486031941d024040c05012034802146558520709840140282000c2518051400001004001d4154002d040c0940944503040b03c10304044c4003160017124000000f50410b0b414001000021300404c4266002c610504001c00c0d8162114140720885400764088800c0e690380050558510340401d4148014240507600c190701203a080d8041781082c8500f074030754850780b10040b61b117138103000e9002c02e4240329000640580c0c1d912008240380035a81d020b0b600c849040980f078100800e92007040c400840320510070004011007500d29540320044504140314043d40c408001920802043d80c00880842c0038081003003819002011241c01102155095003101c00e07102011820b0021 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 615943588 1250 615942338 615942347
    0x1140106120b121f0b0904030804231b030c030706140304080d09031205060109081b0a0b0c071809020306040312150611070603112a0d020c0108091c0807030b18071e 72
    0x2406608402e10b09001c0c4524501e442402c4000400c60840703010380e20980d0510f406048cc1d0000300300c0308800715210001d18a04040d00ca0303a20b07124000200f440300015001003480e500240d54130901408015041c43c900544040640d040d10344104c002900c0000490529800b51003003d4002000f80f0300004003d090152442e500c15968498031044540c2240f80c10360303951580c18100c00381007011002d94468080500440e035404842c050b883d585007800c11440e80d00400d81c4981d000698000b0000e104640781c58a0a95120920840070030083d600c0c0c5500701824001c4100080040c00b1603912064440219500d1504004c810740002c2d08050922121030403041001007618410b80f040c0350925440780007100b800c4400149020851a40d01500102c2000c40d9008100f0750000b0000784c80b50740030b5685000180c0d0701e4150401c0094981ea5030703000e90304e080611500300395610000e1402c00199030711031140050040c1d024030011142149200c001c011140d50f0001d0814040d1074480100401694081030240 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 615944838 1250 615943588 615943591
    0x10110a0803090111040306020d0507020303090d03020d0603021f030e0c030303040b071806030212060d05100f0f140402040c080106090b07021518010201140106120b121f0b09040308 79
    0x200301010220100d06440e0081d402407203120780781000b140c2d8032070750303840c20801075080542400b00c6c2d2454400001c44450001c400c5a00c2211204050400a80c3e0302c1d400390002d4002c006111145030347d884000c40142c60305880040d0b040c84150603030058a08107a0010242c0e42c400c001c0e0391a680010308264169200041903c2d0481d80c040801c1d920740d51188021103c60126410048002c8a429400512207070550300802100c1e0400c0450303045590340c201484011600384030008c01f280d12040041d90781c00065400981c2110350702e07002280b01c501ca8081c450941320350080c801c42116018082c0402c524140c42242c20382c44840c100002d40e503250541c00742c490300b52031044c090154000110502155206414900d8400310008000c0c1c6a0000071500c404698240080d00d000d0742c6011b03034071040401d4402e4100e04036032182d51042082000024030401500400440035000940400001b800781c41c10300c0300e036480c0d460048800021401c015a02c000b9210036958483c05017101409100c0402d9010341d006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 615946088 1250 615944838 615944843
    0x10b0d0b060d020312070b090601060804061d0f071d010e0105010f0201020909101502072105011e0506150415030b062b060f0e06040c0c08070b040210110a 68
    0x55103aa07544a000c60b61446a42d90025414003422130031041038050a800740c80c1e054003a018080d801e075145041160748101c2801518007003240d0200003000101c464105d560741c00d40071082c103110300d022106468540307805c0b488444465000460706000c0702058111003100c5040d00e10300d149407945045107000c446c5106014640c10040c08200e0813003094004d404994503410f010307100c0011881e240e94041c042c40c404d4013404007030b0801d5444810001d0b10018010b4103a03900b90110402da0304c07003100720144403c140b0504550554840347c0030004428010038821082c44846408111480e1076802c10050510000b031001500d401480305010390700b0f505d540c0303006140550030300007100111440010040c8c0190000c0d41209011480c0020441001c1000c4100501e08840b040c081c094842d00c0501028440e80940c80c802c80086001469600d000d070420340e1800814104141c01c0d10203616405030300da02945064449100100501046090200c0a00c9000281c1d1400c4c022140c404690b42d41c440b148210301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 615947338 1250 615946088 615946103
    0x15181c020f0a0b130302040509150115020708070905010602060c190c020a23040c0507020f191e030c0e07020312040c08030720040618050702010f0e010209040608010b0d 74
    0x203000c0703180c0701e101c10440500141103900d603c80701c40300400d03c10845039001c200c3c00b45040001007244e45000182e260a54082560201c1d0503a00344101030914566404400d8114800c13188001000d68051103800060b200da03c801107003a604040c0701a10b0040050041030a07050304004a50001e16013180b201e095201a1030200403044a90000a08884c040e4003c00003000105080015480b540651005d11100585040c010382500785402e5986000d00200650004201201c121803072600c5690900b42c0e150a249142c2d03c0d54540095014420b00044031040c82071584400348203102850341080c00a204010100c0c01780e10340200029200c0c00b03070a85020300e101c07070203011508100410340410060b0611500301c0752107010905000054604090344000644250701d00640d442c01c1a000c0c0200703031101d20541001c2d84203080c0d4840001c040c01003004c0d08555072201b9a101074881402144800b801b103d0001d40c459903454100405c50320f45a01141d8960300d40800e840301603c40c00c141050300380d00304a2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 615948588 1250 615947338 615947359
    0x4090c230a0914131b020105070e03070905061306030c081519020304032001060504110c060103081b0a0b0609070905010f050912030412120206091207020f15181c02 72
    0x110b810031108155001040d8100340342c12141064075010103060f078501c0e1b40280134903114410f090b41c0c0d01c10031090154158001180c28410001030341c10094000d000588450100b61207030184034200e40613900100c4482e402040100690141000184c0500b01d01590107500e50510f81342e2480011001023901c10304a401200150500d4081d0011960840d040c1070b0f0400e40c2c0148000d9140280000c0c010580700710700d0300b4000e4070f0030300a610a40b000182c3c2030004244690841d151502141c0000e520080709008403242148105414070644c2c001070312070500180141000c008000350208010720740310412000392000c00403a80d00850602c450145401c00540e1400d08030080f440860882000e00c15070312000400041c40c0082d43c2c2603011950044100c0440c42030140012610b40e00d003030320000300ca41d1202000c00c45081442c4010000b80d40b0041c01640420049004181194804909107450035004142150305013555441c1501102e0129003440c0801b0104261000100030844080c0c010844003c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 615949838 1250 615948588 615948629
    0x5060c12071115070504080709140f04020d050d0228020307030b0a0207080c0d0908070b3f0a0c0311031803041e0302010314010b0315030304090c230a09 67
    0x30124880050b080c0d0065164601307132201404660240c882c00c1c0003482110300002e071304a00d6100708054030740b1113103084801b621200752400c54018081c01c181da21000341e8844c2c03000203004020b00c0000158035009001d051540c242030002c00201890f4803c0c01c0c80160380c189005a40104055050b6a406002030705c2076140c1c3c08a1400a000d9004020b04501001441c10590079000070102036a0b40582e8440b944a519400d000782c80e80038910070030f889044107000c5118118042241c03110880c0e08515000c1c0c00411298000c070b41c0d048034400b8402d422016005104096825010701038251205040a1110305261640090544002402500d00c0c001c6540e00304070504052084400400201200c3c080030304480b690068210b14a11007280070a14250b410002c0b091241e00a60407511284c00f040d0030342d51000e002541130840c20080d075903d800104070100e41d08005114000e410707801c0366607d06800550a080c14040414a011111071784001e200d8000c01640c040900c00507151070000801c4040502e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 615951088 1250 615949838 615949843
    0x90b15033703080108210d090302010f020f0304020414070c03030207080403241506090311030a06181401090b06010f020a050d0309030806040b060904021c090f05060c120711 76
    0x10080200007620094070805043d40100110b060f2569041a00c0d001051071295241000da440b0180301060740c24000c15442c8921507002000080c060300010542216584c100022039100c00401d008072007000c42071100f035040910a4a030000408030040346241000c1402400b0710085050040070150001903c40410030301c3c43c2a10019a400410000544040e111203000000c07209400541e140c0b0b00751507031410020112160040310f00540f51000e07100e040d602c2c0d1305c06076000300c442139406120300c0300814009419480784607594080c11141c0e2102006529054050780c1c01201040d00c1e0b68180050340c0041860003100036007296090030034041140c1e240da803d0742061072240002e00503004052000458982540100c1c0c8240d2096a944260341d6900c41084111400940503980102c1c0a10000c02503092039802800c221416002e0407030420050350080d0306980000034200e0b0003866070800303502000010000346400c00118401d407400c0420507807101c000c802e0010200b6041260b1690000d90b401c90a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 615952338 1250 615951088 615951163
    0x1409040c0917010c0f0c1214120702070518090312060a03080c030901080601030c2313030f0303060b1804090201030f090b060109060f020703080a110a0303090b1503 72
    0xb00e90311040030100305400c2d64001d1195039403030340100d442c0ca0020080e4500c10210f15600036404070340103d000849680484618403c06542e03941c1c208100004814000c5000c0076a100d842d01e680103181071030610003440991103a408004150040200600401100c048161200241910280c0400d9610100025200811588040e141d020700045c04910004080700500300e03030400380c032240e240343c840c030340110210341e480c68048000507226012400d0020f80c0108804201c0d91141c4060f0900c6611003201e10285000d500031124a0f89042c035403010036805001b003100506034124501e060001c072060446000c6001d444152203281d681004600710382c00390344056070180100d0000c0020220b03e2074130302c21b004403e90b0001c0c04503d460b000060031520461040352404a43d0340a0454245196200da1054103c509030070113001019203840c0d200301d4204105544ca502aa902007458580e60a214406400c007070100340440c0c0c403110310300c81d1139280050b0580003521088516104045210204a0792030f04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 615953588 1250 615952338 615952349
    0x80d170f090319031a0d1a0a0e070f0801060f05030d0c030215240909030702040911060a020a0606090204030309060c0609020402030907090609020a23090d0b0a0c1409040c09 76
    0x2a14030f4203c0860341680403c61201480203070743c595415200c10040246191940200014450540500c1c8150201031032504006030460100f5902007241c002810948150014285039000c0c100421409400340034001c02419641e5110030b68506010200713803aa218040c5003814001158808402c0510821203244a0b028400746510716062900c62203010b403218640d01054224070b5105e12030180382c040d0303a290043d500000258500000c039400e000c080c108040e0300b9909980340c2c002d60450703901e0b624001c00b2924000c0c1c2c050103191906245c41c108640b00f540110096920510041c40000d8100402c038068500303600307004c1982004c51408070094050414021740280c000b10911200c5c003c009200004d4481c0e2610a01440d6140c409150407400741c4a20f90001034604209500b0501007040d445c0c008403060001e00d4a1714010b070f070101e0920007510008444901d203560812007003441c1032240a051110914013585204442e801c402150300961aa90b4444e40c1e50b4560144000d001d00b120b01c00502 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 615954838 1250 615953588 615953617
    0x11010c120b031b011407020a080105060306100e070302030405030c0a120f030225081611090f0709060503060303070606080a030e06040f0e06120303090106080d170f0903 74
    0x4840280204030010030314945688508085090041c1e141c08640010f021603c1800c010f00c00011200440740c0e441120703a000881001044001c0158480200f68405055100008100e0381400003c1c1840d00800070b04ca461030601d5540b042c00824080556681c221085103801b60303c940312400c0c2142035110301002d10501d03104a40c1490104694200380d8480e510700e075191341030050300104081e810b81c0710384451503002141c16581c1c44201980c03001200080b6000e01d540c241003a4541000070743e040c8000509452212608404418600d0150303000d0b0790024500c07240c40070509020074068038081283c00b0b51400e04c20f01200144c5207440400a5406d107941001c018001603546941e9075849283d100019800543c920346141550705000040390115070080d88104841807410350000700015002d8611580103140803180c10003007a00f0000b0754041c0c00c40c1400090414a00620700345404d440d41442401d0052088044541e4099095425801a0301000d00a001e60791801f020703045100303d500c0414540c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 615956088 1250 615954838 615954851
    0xc06061707090608010b03031605070305060f0f070c020105122203080411060f0d15030819200a11031504150608010b0607120c0507061d0405010f12031101 68
    0x45000480078120354054100304082521805024280e480030100700360194410400c540300300c8540540112901c0c05002512481a280d980b280e05001c415030340038003020b14010030f1190b00750240c1000b980000c0c280c00c2401c0801e01e2540060218000c4125501200e0040c20001d141c91f04861120142401e0070b2642d503400d107299180150001005503400e43c1c0118104200c0006401c09ca804c40300142c1088041d1410705140d00b185038050b01e001c4656540b00490f44800000042451020302640101080d20910b02000780c50014140141d0040c54420782140220107000d9100c0402c2c1c0681458000500d130700c10300d5080003c80c0c030740303b01c00c2012401c81213040704000a21100803050030010344401028490107540303072451400d0b0341303440c2500daa10110411068000074a1141004c810040c5401c0810407070b00036032611801c0a003e07600200c0031662445000d507502c4490b00c52900c000f01c046034200100c0d418015041c903150100d00501d91000ca51000c82411305025400c0500c180511030000c0c88103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 615957338 1250 615956088 615956129
    0xd0e030a0c0b1b120406061a0c160302011d0105041502010e060f0103030503010e090f01060b0903070603050c09040203071e0c150504120807030609141503060906070c0606 75
    0x5070000440a031040c00790140425862025481104070f10b5060035211400d200205503100445413000c1c20071240e03d030351843c2c0000c166000d41d1000700000e5014074501d0302c0311400011141403889031003080d00e00710703503170070040c80181e030019030001c1c0d0024134900f5448208442c0703005940324880e07908007191600c0b00c0c0800c00c190a605400c0301808084060a8034071646840d884260903c1c0300b070100030046003082c80144201d6900e690803070b42c8005004100c1d000c481c0c164003824210394841d0400e4540b8030001600382c2141c10b0412410004001c83d00e4108a1864150301c5001c2c00c1c050302c84900d00c29500040070600d41c40c031031400040c080000911440c07030a10034810103041001d030100111014070092407081c5e0709070078a00c2100d11031604141d140c0f9076034040b40002c0300e44010080c090720034195140d0740401c810516100e00800701120840c00001ca08102d005071004540e400c01c040d100350300101c00c0104080c0c002c243e00b904980141030410a004080c035188000c0c202c1130300b08070980c00c002c8003111070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 615958588 1250 615957338 615957347
    0x714060d023c0708090f1908070605090102100504020102011d100f0203070813030216060201020301050f0301060f140d0605040f141605242209021309020d0e030a 71
    0x80b41c04288450401c030000314205451442e14070502c601c1e92140901c40340010a22101c000d00380e0510041082a84040000004940318030f48419002110074614040c80415070400501020708076034205941414180d44c0000c1da40c0f600c669244490315203135008181164000d42184a01c0041c1503014582da010000c1c06964490702d060020349814240060241110043e20850303014032810354074003946581d41c0000760502403274203008604510400f40305101e011219040700002c3c0c41e4503800540e0b654904410000c809038003454841c4207902d8510108040040b0190742000c03204e8414a0300020005040001d100319217134100a000142898204810031818100d4041d81c98401c14820681d4401d03005001d6481c02d100980c251001800002440240340c0001d89218020540c2d000441c08441c2e08102d4005400003030014450f080d400c118030510020380380c0d4a40140000c9803045060030980e0410300143d40e103c2c4180480039034002059219000f0a411211403180a601280c1d41c030042d0200061 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 615959838 1250 615958588 615958627
    0x90402130b190f080106050f0c071a090405150604170a021807180f26030a170106050705030a050a050705010c120e19080c07210308070305090714060d02 67
    0x10000e149214800039207409209814140c5500e40d90301f50405900810b00c4499600c0024111130034440c00f040040c03111140c2117211030074003950503200c4d00d5048070404e0000742c54000e03240380c15040f09020440801c0c0c0300c0009880886503041486030741c02841000081c10300a8000740a50840303d0015072414008464141600410079541ca81c01010224683c20a001c50725000e83c00c5940c890700002c120065011101801c04150611070482d610000311420b0b18543c0042c1c00d49001c04c1c4081801c040b000d281c264414014800350500a180204603500e0079124400c0f11507420902c04040341540d4810b12a4041e11941d6a100008000504200c640600b54001019040003140d007480f1028501041c0419106402010300e02c2d502c40302900350343c0fa0303042034010b010400281e02c0f42020005050322825001c0c03118106444034118482024100102050401070038807080c5414201400310345080000c0c1d0034101d6546007504c0b080064404c0c0001c65512138100312000040c0003082c000b180d20107034a50712 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 615961088 1250 615959838 615959887
    0x40c150f0e0d0224040e09010b01091505090108100b0d3c1805030310262e06081c0f02100207061509020d0c0e0303090402130b 56
    0x201199481c0410401e0403034141100070740000111041075a071501c0b9006500b80501c25620180c205a2110b190070134010045071624990b81d1036110f00009940c2294024002c2d0618111101079070407180c20217065480342109003030403c000e1a00091040d043c06803404090807503d0300d419075402411030303128081c01b01202c08941d2641c990000045603880d1400106080b1145100c80c02000180c4000d00020118101c403500544480c400b2540080c50a2005620464603015501c002d6414040240c5140d0550542c2d0480c841d111103420030078840024620b681b0201905040f0714008060102c0c468101c2c4d8142c094080505202002c20380c0000814042c804581501c00007030100081c4904580c5004800c00c42000750700441554030b11218190001d201c038900804001c1a010403078400d507001041280c0c0100f0035140d000c85c1e075804442e41c5010310000c020f41c074580740315500004c1000036160b10508c4502e41c0b1550f80001d8000d040500d541180d0000d18a4810003610394406007000e103081c41c2c1c82d0052 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 615962338 1250 615961088 615961097
    0x11e091101050a1205061f21090215030702160821131208070f080912010c080601110a0c141003050c0306060c1c030605130207110405040c150f 63
    0x20405521075015114850342c0f594443c40f072590503220890081030041d00c000e8100d0404440c0440480f51b111485140c5400e07036035087c8000724045942e03080d601420b68900c075000e003880c00c0a40981d50300b42d040382a031411900382c07590740d40b12032106920300740200d4510210022050000501c1c8031011501030210054448035600000d0303180f1b245191885041044520129141414040f0003030100c1c20b02c0348503101300449850b01e1003e48a2200710010840308869502000440042c1414201d10100058a031403000344544000580302405400004001504102041540c4102c03081c04010606055820109200809482e5203503001e0321516250740710b028450405e542d91101c0c2c8248900d0b44100d14000c0080d056031148000c2040960240c00445c41da8450410340c10303281c0303007010110000c4009903180051560f03d040180b0880058404444c000e061040c0105030201d001095100e0908004848c001119036a07450180703001401e94000c40c2c0320340164250480f80a4101d40110380c0240c90742c55 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 615963588 1250 615962338 615962363
    0xd09080d1808040e0c040f0308090a05031504200a030f021c050d0c03050c01050a050103060e031611040204081207020406050f0d0f03140c03040e0c12040f05011e09 72
    0xa411031201d403610041c50203a0030441003280440b800c8a29070000381141c03859260550b60822164100003580050b64000307000a2080b24a2030820a400c0c0141015406031a2598070980026000344005001420505030750b81001c0a50211000961410000400c4004083c0e02c9003030950100211041c1203002e04071010a100b8103148090a0b0048103600030001c180300d021101003280e6102513450110140001881a9009400d0030300501c1e1040380c0c4a040001d02d9032450801d802501c910104400c0d058008009031281c90084e18100c01c5003540004e68240e020342c0c0c00010400901c150b9000311124028207420f420325801180090048134021203007400019191420810040d60a0801c03560040c0419100380016003100007141d8418003e0030090781d0790000c201c01d001c0316400b00072007200300e030000030f814000d55809020040d00700540320f54140c00d02c0201d44052454803006080a4849803c03030818504001c0c09412083c07205c7c90124020324540c850100300d0018092801e404c513880e010000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 615964838 1250 615963588 615963611
    0x601031101140301140d06060303021f02040f1e03080c0d080a11070212070338010e0103031404090c031b08250221130e0c070809060d09080d 62
    0x14240c001c2941d4031010501c0c41c0d00e0001c2017030a18038044007154108081d4020440070802074070841004601035009461801c4020403884105c7c1180c00201c1002c61040c13106000713a04180ba0302d001501c3c81030349072504564400303011001508859200030950071340041c048102010201d25010311a410303441d03158051300c864014074142c40c107207402354580603030500003c80035141c200c07076151400c1032100a03500c0407138598a60b620014613068241c0070b185100c0c0d59007848120203d07240c0b20064801000410154140f10321002686018031000e000c000c4c0c6c041c5102c10b601d0710340f0203c6000700088901048841c0c40c200c40580a00005402c0d10841c20301e000d00b031607804e8054118140b1a0b00024503015154403a104d2002c4510503e131409001c44c428220095120901000c4c100c10504511300c2503038460320448041c4190b591642c1068805210002c14001c0b51803025040d10031441c2e01140068440810070003103103041c041e520154091a0810f4620018071010b54000c1015003a03200d0103001c60070740e03903 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 615966088 1250 615964838 615964847
    0x9030f020f01230a140406050618040f020d022d010e10020a0314131e080a1109150d0609020307120809060702040b06190215091c090909050601031101 66
    0x5404034044441058039036039401840c08112940044c0034074000070300380040f000ea040405011602202d40ea0f1750303801809403031718010702c010110b0360708170303001c0380361841c1503540ca2150b09200390000b80102c0750070348440f0171035a405006403100107050700080e030007403903c1c190002c001d41c00241850114241d5416403c040c10300942150290400717400030b00c9055917940e000c41d131128204059103111a01844500e2322028040d8003507006100010f002111945070382890420381d003666001810951084004400085014680b200442c60869120b440c039901c21420003804000e0850450b070100c28800050208161030780200d00e02070080d001c0f01e81e09034542c111002c4914800001900d500801e100001d900d1804000030010700d031024001007601c0003179102140ca46c2d0401c209800e184078560200c010304683c1000441c0d00030481c0d09022000d03085c04140c072601c410288003000c1911560903000540c05010b800d2000042c511580d040025501504100382c03102d0b420f002c1101c0c040c2d09490350b0a41c07507106 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 615967338 1250 615966088 615966101
    0x140d0f0309051906020408160315090201080a0218040e0609101116060b0303070c1a0a120b0109080613030306080304050a0e090a1a0403030b121902030304080109030f020f01 76
    0x3401880d00c503840803804401c02d9072500c400c5135407540030440404d1000081c4815407203807035000003e41d13007103086184c1020742810f8100c4d000415882c6c500d2100140c0c2c0e105520b00e421a61070440107a83e019805942c50038a1400010550800d04080d000303aa14440054401c7c442c01c42401901c000302c0410030b008007690390b60160311220800900c00310448000c840c844003c0741c3d10400340001c1c4001031401103415600001d03000d036030300040c441c0104440c0e0301701e5555508050031042c0350391804100d0072000c0d181101050451380310b9640c6100b61b80d42039004011800250001c002120704920f4550403180d405400c035a0704800203410b2000000c0c030a0b40000a903000d0701c400030407440c01c0da0704011761402440300062080c0100d110303110b103c41c0450103660241d641c0202072a00328515160600700a025262a004164004c45107007114080d01040410b400341104514024a91004081d00020b45540920f80150016510741070700c2804058200f010194070a81c01d8080d13030f0f100d0442c038006d5401c80f5039 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 615968588 1250 615967338 615967343
    0x31815141b130315060611030702010207090b0402120c0a09080a080706020a02070e010f150f09090209030109170d0b060307020601090c0c05031207200a1e140d0f0309 73
    0x1041456035071280e21100150140b0030240c218002115500d85650450700c50003403101d0721a0703540321030a11017181d100c0040300000e480c5800035803800442c3d6000035641c950512400b00b8041c2c0e00c50483c1e0441d40cbd15012101d810002e820a91918200f400f400c4881c2d51200c0d0850300450000f00000980240c00b04642c4103083e0044c03545414100302c0c2c0c641101a50114196400314050260042007c00c00307014014040e0000720101c0714014100140006081c07440c00580d0309000b44010a03980d501d42c0803080704145c80c40d454003d40c5401549000ca8050901c07030303400906500c80402004403030780580003c0d086030002240203101002407101172168030321041d90150016004500180301202080d00486003d180c5c5141030b2903107041a81300c1a0541e0810080090403030351180c244a1441e5014005007450060b4038181c0061001280000340c1c1d80c0f03404500100b1904041d42c40c600602040440d400d84030340c01c400c3c0c0003c01a42008019102d02d0743c03030b40c410080382c0b2800d9a00d100c03510074482e41c0701180c0d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 615969838 1250 615968588 615968611
    0x60e1f1208030408071b0f0501030606032a0302210a1b02060c13030803040b040b061504060309060b04050903120708330402520303181514 61
    0x22584d0315000480d034007407241511450041840500c180700d00340000801060181000b400c02030901c1c00050a0350251f0f88607104150400a03041d94680e0f400789070f407801410340b1005000800041c001039000e8014411500782d0880c01c100410400144c10f44294410700801d807081001d400d09031101030101c1d000c125100010380c407100000742401604030080c62014650342d4030060080c1d60b95038a80150384119030440c2c101240c2824002000a0b941049400ca207084442c641410f030107084600d1540654403d21041544818107141406016800031603030b40c0006e00f01740704238a01500740355030b2130342b00c4503902841024940016a1513445044107600640d046029480390035245204004000e620071903900003442d50068042d029035680c4000d00002e150142c00c0f03c034582c2c1181d00f4144039084000c544a512040c11140c4d40104084002d07030111001000d01d442030385106040443c01450490110491088854004400c0c41b1204511000c4812400c40c188a01e6024100c6d00e01a0002511000f9104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 615971088 1250 615969838 615969841
    0x315150c0803090c0405162c0618030709090507060215190b03010911030d0504030203030d0c1b0c030c09090b01270f0c020d050a0503061003060e1f120803 68
    0x35005100458112011004a5484c803c0ca00001001c03135800b914054900c10080d035100c18010781041000b41081c01c95050740b449a1501c45410907001003094034684a460001222580611000c00d40f10500c00082c0445003019150404070000748085a4155a21320500d6000546684000340322070101c40b445048400c9a11140e095000001d03840b03c141c41440e40b1422088925242481240b81c042e004450103285900408103240c1460115001141040420801400540c40000450303401c0d00042000190024800d50102c55049450a000a1081760000800309100d40e00c039449058074051040f488130b0b91390f030300041300494214003002400c150700c2c180100132800101d8021000044203103d0441c101d4490780c0c21504980311107980e01d036029640ca044144040d030410020380b1420380c508010785031400ea0034025000c0d0000902c0640f2500c0711a2000800740d1081d0045801080e2640b1211000d040c01500c10001414a442e01c01d1800309282d00003900b0035443e206800346681082a00c0d00e035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 615972338 1250 615971088 615971093
    0x18061206151810030320150a0b0102030408030f210103050d031b0c20310c08011703070b01061d040605150306190314010b09063106060315150c 63
    0x6035036071a00441030381b070081782e9000c1c98001d000c10320740600a03030f40c072040390b29200c0140d4080714180103070941150710603c400e00030000b0010846040341080b440040d1188085000401c030050020046911041034038000400c100c00010418052041034400340283c00181089a08000142c50380ca800206c001c1859408911140161007003845030102000b08408690041409120b5184a054002284255408a140701010384d0506040e100f90103100b99000041c004002440c10700540d0108888000289103c030800c0084480281d031040006105680d14032001d45901e2202c10000c11110400101070614901480b990081e210020b00701e02d01d42c84a0003134402240c20080449801c9508540301c0000c03c0280c0490b02c00440c030130001400d100400c0b218440c00e64120704c841c1401213030031800b408072a903540700000180d807002c0c10a2250703030600314065940002000c191120124502000801c440d40d140d0082072038041d03103038203101e8200c0c0c0e40c0444802d140501007200d8001103940b00391800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 615973588 1250 615972338 615972347
    0x10f0b0d0b090c040509100605030705153108010b0f09010b090a080f010504120311031302010e10260c0405090402010512010603020301140f180612061518100303 71
    0x8100010314100c401e1928030f1008207049030410750b254480c5500002040d203d80c3c50500503d00070b04000c0d4003401d1440d103844045815003d0345111034030414000f017412040008001b880e034510080000c9041c0c0240c030600b13010039035018180141880c550074407520707040908002589a50310b1a0242500c0d030640e203010810443c5030011005940d018100550000719020100010403110959000004080c1401d1802503072a092080b440da040c035091199078006201d0500c103407648580200004201c04009200488680600750015039010b2284080002d203654032100c0b019030060608103041c401c0d444413240406a410458006419010420080c07185041102110381c00a106050041c00c01414104001101c44240c0100380066402310040040c105085001509441c05542080d04025460040f40d001c00c00d00783d06008141d2590089500c980750b00004050003607102041d146070f03040c0a1080c115812042c60301c5446070000e04181ca003850400030209004030007200103580c00d28a10f079000d99 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 615974838 1250 615973588 615973591
    0x30506130e0a26130e012c04030909050a0c0306061407020d030c140d14072105040504060b1809060d03110106180c090e0903091903140d02010f0b0d0b 66
    0x403802074924a8040200b003001c2c0c25040520001c004280741811700c910407242059000783d41d0520f08132039514011481e244181c45510400d20b0f80c110a40d42e500341642e2401d41503010310030b0b041c5800d04220341e075022070307001c0181488070f6682032000c656201e03803c4403000c1c100c106071000c9450801c11a0300601c0c0c18194001c00030301c03a040040d800c0c4101e4455415217420f00c4c0400540360400703c40402c940d58016040403850801c19213140c200b81503626203c4039940c0310303401d03541d42600189400d444180100284c0e8000e020084c801e00100c1c0e150740e10301840e40c00001083d0550b860740b040c11822443c001c411140b04000180004030128010346040344d80c1c0c811108040309039542e44c00c01081c0c0c12100000040d050101d4200401c0000030140010440d2090390310403441e01741e40340184492034a0210896802081c211225200e0414000d80708200e401140d00042240d45400b11507104001c0108100d815094181c000704103912145155906648207503580b10340c010041c150410000f02e1045800c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 615976088 1250 615974838 615974873
    0x60603070e2101050c040602121207080901060b16020301060b0c0d081305010c080702060a0608072d03061418120d140c03011e0b0a031d030a030506130e0a 68
    0x5800100600c6812404c464081c0d49900d0794480008050101c580c04100000c1c101491102103132500c040609810006100500480300b0049048041190705009401c84800780070950105a03480c010724030a02100020036004034000d5091150001d19003000006480c4000e900300041c1c403070400402c0080b6000c45004040200c0050038030f40c000d010031070074880e595845036541c40c1c01445c1d080c980c0001c1e140c10030041014080a051010038440f801020035210105e580030f80c291880c0114110181d0300e1056060101a010f6800240000500c4004c4d080341c2c51205044001240c251109040c0305071540500200c004590700011410000b02e6810006191035070041d8070008911741090440c2174400000c0c0c0b80d0952494021005201620410108982100c80710b00d20350000e40c64a100b441403800307540c40042c24150f80b04e200100d600c1490241070041c24050095941e900001500600144000c0d00c0e51409132014442802442d2118412002400aa5030007010740390200d070359000c98540c02c0500c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 615977338 1250 615976088 615976129
    0x30207030b090d0e0301021309110405041a010f1d0d02010306050d051c02030a140d02040b030f04050705040903020a140c10030b040e0601050a0e1b03040f030206060603070e 76
    0x1020942030060749000307400c03007005025400d20b1201d0041c825540c0b1040c00e40f0a910412011a10354070901c003500840342c2186022480c8000740203044240e0003142c4c030080c1c002e41001c2c20000d406442903121191140d0980381c1e07085040e5400d00888403818001e460b10089039082c65055503501d080e480118003644140740100d9280d4175140400e004080e2000d045074140d000c01511144812220310328180c800e81c610046042c084101c5000380b010f081804044c2c00310400141c01d00c0c030720065070122000713492030901d41c0d5a42c0c10412040b0140c0c210480307007901c4c0c0d809000004503080c1303070a000d1500c0b03003501a4011309031045151154808612610480a050b00c1030b13280e4000726442c0d60b404040c0740c405648001402104030020b100940703030007011300c1449400260040c062683d49d1120075058a40e0f942c254003143d91071940e5002c2d5164000c100e010080c0d000b00c10031040021140c51551030b80e22a9099079400d4a4100030701c0701600007034403107402140c0c0c800d1140c0310b541005401d2102105c0f04212 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 615978588 1250 615977338 615977353
    0xe040302101e020d0b1e0d0f0525080f070f05060a0c0c0b18101b0609170403030f02070e0c180a12050f032106040b2e140d02070302 58
    0xb048022a88803010860391036881c0c400342007941c42d210030410708440004500240c0c4d1601d110028842503001d07140100a000811045424802d0030000309038590040004210340f00303000740a01c46108001c1c86050320612900440a401c8540424030310b0886040141079106d05040c10304103d1950415101d507801c0001d100400400b15009070380010090403038660481c2e5500b4204149400c0000d4810420f000d074030903003e2000c0d034076403001715400700c00d0540d00784000103d26443c1040c06059101409000806001c505480d1201600d00a204030387c42031b1203426061200c48000d80c0c4881d02c5d8425051400000350016000140060040c50707040041841881c5000e03516000a076000503036003060030f4030030310340d437046082080c104a000440c001c2500154103107450f680122740c1321556844504002c5029001090300d5407580e4101c1c230306101000f403d9480340400014607452400c038034620351020003640912005020301030b00c0900120030091494510f051442c01044000e944025030031001c41c45085c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 615979838 1250 615978588 615978641
    0x2030105031015141804030809190b0609040f0804060f08061c0212030706110c0c06040e0106050906070b0403031407090501020303010e27030c01050604111b030d020d05100e04030210 80
    0x6070362285100c2d80725079486040240c3c81516040d07070610081404038ac84000c0001049072600000c3d0b114008543d05021640c03145000c58460f001d90701c00504403d0301290108aa582104000150344d0455407142c070720f0303503c0ba42084070107560090038101c2e1101103040b160160078401d1281c44607440e1700301103030320344041d9503524022074014070000d002501c400315600c2c802e40028040325038000411103000d410642004800004900c040c800c52040c000c00042101342c40d1245070581708620340000320a045031505003005009886000c0b0701c101c0707074008100022641405500c040c0140d030410390007107041d82e0a01e002c3e0340e05c1d1a00540344d00003400c031504079294141d84c6101c441d81d8600044020710703150202c0444484c00d40e000031f8860340c452030420001140301154001503a80483c003160303110010a130510082c078214429010120020350001a0790b9403003412941049005075082121040060354421045001080035580200160042c1800b00310241c201d8024100020115a54410461128 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 615981088 1250 615979838 615979879
    0x6031a091e060f01060c0506070509010c24050606130303120e0607021006142b231c1e03060806040b01090b0904020a1710020d0203010503101514 64
    0x30581c0c0c0102d5002100300f003403499003001500c1c010001d07810540d454580319900c880d22801c00402d07500c01c00c500411200c15985c460f00e24664005d40000c0d507029203d10491201801b030420410341940e03030307007414003003801400c0c540d0417142806000d0a029860034216503007200c4152442d5a051901d51f141d020a280601051124a0103904980c004000009400311414156027003a4480952100800b0340e100303950300c61541059004040da52a01401c48881040082c183d2038004040d006800c410f960041210308501c0004620300c41204a80300c1c2c1ca0041d60300d20143c01e98406100000d281d0007280100410000080c0c68405164180030554a403150031407403a040313003201c0650341070100d2001005814a03521503640050300030b9540e50070510b000d80100344a8070785403091841c0203010703920000c46924207201d500c0721140024029903494145031402c5000c0c0d04203002c0c8a11038041c40442e009072195510449203050b101d02d03042c11003039107406c240e8000350038201c40860704540c001e4548509071401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 615982338 1250 615981088 615981133
    0x9060123040e040212150121050f1f05012115110a0f08060d02120f0109050c0109050102070e0402091e0403030f0608030702090f090a02060f04051306031a09 69
    0xc502c8400881c500b43c0100048041c0141401107580c01c407548031400360381c0c68041076065900ea0408a40f200020441500d903210056001401a000b41c018008102d0303004940758003420f20b804003000303076422145840000c0310020701c101d212400c0c401c05e0700040a040551314007480350080c152001c6010710211a80f05a40e44400c51a28000c0006003181c0000d400800c080c6a11040c3d1030000a2480c006001c550511084480a445940000b20000000340100300090301840400002c1c03100d09541d19090350380b0a40c2e03124150200c0e0058101280a51000500c001181d059460081d41900d40d502804000d0343c0140040f045040c6812004800709414903409000c0c0e0300c2681d0010340c12000344030a40c11a460741e0800b61040d001000000c003d641d9284601da048030910400d00c0540c0c903001000e525282d0608402904030002090000c0d0400300003000e8400c498080c0c1b14140c0f140544400380e402c40c4c11034040240280c00f07001c9000100000c4150351030344648500101c0e1707403010049641c0d1081519 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 615983588 1250 615982338 615982349
    0x30a080103030314280b030a05060a0608030a020a03050705010f090f0b0a021e0c210a020c0303040609090c0e1c030e03010b030a030c1a04030e1009050906012304 71
    0x4205004004040d414883d0300381854107000d03009900c1c24101c24102c0b0080508004907802c1c1002d82c04000011001d51104d01d2040c0010300b1100002c0142c5170031074850004840010a2a10b42200040d9855020085855404c0241c0c081c00c81c450441e174040d030f5a5040000107541966880101d40000d00342845502d00082c0a00071041c0444c00c50314184081d0300008010715076843c0184a509406050521020740210f41a4161925204969030380c502e4410040350b107148a80342803075082040d40b4207078010107001c24540d081d17420340440d00090683c2d074412440344000240000100b0421042a94051045005907140610f4042004800551103070400041c40080c001840e0081007015000045004d2480042c0c0007488200c0880700003070b484000008016080c40000007101040003c03c0d00c0400c3d05011100042865080c1410700611205085001d64022b56220081000e01802031400008954000704228140c1d030b920340046540502034041c0304980d502903581c400112801d00080c5c406080d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 615984838 1250 615983588 615983597
    0x60806040c02010c0206060607061503080702100e0f21010c02010606020c01081014060403050a0305030f0f160509060412080910050c0604062309060609011a030a090302010e030a 78
    0x104002088100c941c001104019689031207443c582d829000b081c444d50110b0300300c4080d512007400e0705002d0051b2813440e81414480d8842c02c0080100f0044c030b40a02003c0d802520100a20400c110040c1c3d1642c1a00d80100e80c040c0c1340710714203102450034951011550703100d00f98014440c11046030040c2543c043d00250f101503510b0702c0052050550400c00014807490900c1c0058007410141d03a42440b13420280141c6034042c0d41034144a8442e10713940226801540d001080f1060034526090041c841d42080d15991104044003010070902101103401c0c41c05102d14809403211022100819900c540c007440845802007001e01000503220388000e0070304c002a010700440340d5240c038101c04000c24541401000c00c2400418007020303112040c0020030550280d40004001204c03c1c05140005929400105c0e116803545280100420b0043c017240240c0103a40a82d8601240e0340c94003410391001454101050b100d0303000340005105402e40d030b000905201d000340000501d40c100148024115130180380740d0800329 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 615986088 1250 615984838 615984841
    0x10506090f100c1209121205071a100f0302030c28060201140112120804051005161d010203121503030f132c071404080a0332220608 58
    0x203c0c4070110390404c2c2c40703586010b810b5a800c1051410700c181d1081d0b0007924200b500000d10340c40a00550881c1c0318590403000e040740d0031a08450440000c0d600319440c441c2980040c0d40095240c100c24480c40c00d40c1d034012302501c46a50f00c03800b48103148420140b0750060142c0f400058101c4a103080f030344009440c21390f001007141c46042030441c40442c070681c4a144014600da00c0340e004200e14101d0030840305001e01c2c0142d050748460030b00514042c03595800c15401850201407019641d2192104a440312446d12180007108101c01c204c03100c48010300749103015800030803545818603020b40499a01c591000205042808120082072560300300301d00480c1d440f0700004202282e5104c85480b04002d10441c140c00c4008000c0201e06503540a00c00340d03140092110b640403890442c02000c013900403594000c0e2054545907903128180e0340d00981d00c1c00750040ac4c82082d05154070106202c40601b00d050101d501040f52072200079028880e4817040c180c10701c4070642c68107904881382c0170b84418002c000300d41d0b505245 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 615987338 1250 615986088 615986093
    0x1104080114061e06030702010e01050106120507020607140a050f030901020405030f0309031b01021905030901170f040f21080402010908030a02060106050906070b16081e010506090f100c 81
    0x11a102400d280e01c0764008040c2c0e42c0704400f4000403158045000d413807050b1207440780c036000e81c050030100b41400b05a50a040000c5041a0303c4801002e40c1c1580410a000380c0d00c03140e000340d8507007400340c0f41400001c5440f0608002814248000c0142c000c50345401d40c58000201d02c420400e801c1951644a1a500064200114136003003100080004010028600c0d20300501c00107641c1d15640b0010020340c00d07000d0201d0070b07942c0c0244190f11443e40f0f4507040c560880c400740b4200b5146e0340038a210601013207011454680c2d02d0660188141f01e10741c80341420450751103e8075003c0d8a5012401c0440c1e14400601031301c21130491540c2007060000325030f201c580c000c4c01c1520024150700d40e160040021a0b1052040c400c204c1c0c0d0004016045400c0c90031310313680d5804104007007005031146400141100d0880300c14050380190441d49a201c1d20400c1c4d50311a52504c503000e01210300c514880221400444080060080740703001001024842d4000b000c0441650300c0402140250300d0750400c0e41c0114403410380c400c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 615988588 1250 615987338 615987371
    0x31510090b131e180c0c0b100611070b0f0708073f021c05040803040f180204050108011e2304141e1008011b0f020607091811040801 58
    0x94070404140440b10f00c0d06241581c07070418070820088480d540c8803081e4540b00350103019000d10168200504010525040641800c41c09251003884000b0320307a000702041030300010920106480c000100c551422081121006182d040800144c990481c00c12224001801d1003101040c03045000c2800405a046180311840c511102c0701d01c204202058521b01000c14ad000c10079058104038100f050300031410609048600780102d420007645444001400301740007081d03c021204031800351014801036515070b84000240d01491085c5400300d0312000c014888080f1009589100f0b8130900045a1015903980b030381e039850004c00700c019a0f05180c40558686c2070400d801150032100390420300140e103050145e0f00201c13803443c112100d0000b10a00307000c00c00740740c0083d10380c000425216000f48903510300803080c002002c0a00c086000814141c0d03400d203411b5400892054480c4049440f0311a003540791840481c640d4026010034045640d136045c1c00d440181c07600c4007900141c901c030400042c0d0244052800e08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 615989838 1250 615988588 615988619
    0x16060c1403030712020c0109020405150a12030503041401021303080301051009080c150c0a1109010909170702130609060f08060108030f0c3d02031510090b13 69
    0x80c03580040041008031500603860065410034a000141e450302c081c002980100b02083c0d009501500308400e10042c0803140c1c55200080904403400200c195441c02848030242021600501084080c000100032510307a812a4502000e40c40000d072400360701d80d1081841805a80040b5a6101c01000510041c00c1202204540e2030060400c1180c41c0d082041e940d5450340c1401145105840031189003205954401c15181d480e035030102103581006e088e203088206040ca902d41e283c00759410400024002090340a16095030350000303000381000da1090318024142d84030190680c0c00100c0400110540d09003880b5140003019210030009a0904012500e010103841e60300422140c4e110348010f01c8040e8001c4112035010002d0590782d031752410822030090801c0f41c0b450b0590414114490056210141d039020241d00701d40349a100280000b088800b803080380806c1e04c444c4206084009410954244410201c1810106080900c6002e5507035844030459404007004200203c0500420007414024100d0300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 615991088 1250 615989838 615989873
    0x3030f060608091c020304051c020114120a0b011e110c06090a05040c03061a0309391201020d02040302190b1608070f0605060a0602070f0308070516060c 67
    0x50b0200d080c03032400b89569403014058249900089007021503060b000b001154014072015140b025000303503c00e0510f0442610034416400706002d00c2101d16000704010840d4a06044004c0b801c04c01d40310813080e400200007895840c1c1c140102c0c5019081106442030900031540e00c0740d40e0b2011480c1030b5120b000d041040c1d90700d28038003542d001d01202d182075072050b200c1402c1e58820f4400181c0d840b0f180e003045000c6c3c10681d1051030b01d54140d201c01000c070b00c0ca0b03100452084841104403000c003030714188540d02c41032032502d09481e41694482c0381c0842e00c100d441d050159000040c441c210a14510401a007240d00003040300f1521070b80002c0401c02c40c00d00100d40c20440104400c021307aa07514100c2c9142d0140329201c01e81c424107001d00042810801c1d400107a96480b6007100140e61003150324942000240000e07a81c480c130070f14050600203511840040ca0700280c03020030601c24421455955042c2003a08a020300320f490340144e80d034103581080e9480d1210001c2c800c6a5074201543c03190b0134081c21015121414 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 615992338 1250 615991088 615991097
    0x1030b040207140d0f14030c190206151503010501030c0e060a0c170f030601080901270201080f010305030415091706190b0913050340050916170403030f0606 69
    0x1710b03405581c00ca00b0060b02d05840118241d6a55940da454020034454a58403a0810004180c0c01020030350001c0e0152182c601c40301d0300e4010b21000c2c0108000c403222407100c610030080410052189500c250014420b00d156402c08060464480001071401c0d0841c07650000054002d0124806020884c1041c42400ca501d100c803529120842c1d039a2005407000800039418070500401059550500754082021101e4807030342207e10100030b04040d10030895404090340003810380400b00341b801800c8052141200d500c84000c5203007034504aa0084484020f00b9031000b800380035a8002016181a1203000c101c1e420440600300030b00c1c216a079444800c9089031002d0302c0d1450000e010080d505c40c03105103900420b100c00c80840750046031804920f14400d1071602c0061403015105403807521100524852001c01032450500c441000816110300220030b44140c035070004c415008500080310320742030440c800d0901c1c90300941441e10f03560400840d081c1900d00b02c000070382d201900c4011102e075100710800340006180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 615993588 1250 615992338 615992357
    0x20d0c05030415180c0342151a03060103050705070c0e180f07030c05010f0c0206030901021303050a02030106050409033f0e0105130f0b0601030b040207140d 69
    0xd803e034600190242c1c030318030b45a88010300d00d03103080b45005121102e503009110a8103980c0700c0c40c2039a0395080e94000c920b010740d00c0d1130404d41504010407110f051388450026044400c4001a0000d010b00000c502a004111700950080b40403040c5064100815141340c0305544d40e070400c50300040440c0d000400d420308005080c03000c8400100c2d0740602c2002c84055140503206611040085488424002c00145192107002c80e00941c1150114541044a025080100e501a1750b140151380d0480c441c9461000640c11041c05030051902c08003440d00700492000040c28509070710001e2301c065400b41c200f5985544070418150452400340a8a0040d2900740d40511104080b80d03009044600d2504450029800000074480700402440040350303801c4148000844d11700d00c840c100380003406104144407036035080030300281d010304017020705d61811988550417080016454440e10000c08003d01494101511884e49110700da840d4009031500c0c900034075800340c02c0e034400004a440d002140404c5804c0c40301211 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 615994838 1250 615993588 615993593
    0x301020a0201060810020c1c03021228230a060f0e0f22060b0d1e030801080d02190804081e010b09040b180a080703020d08090109080703031e0906020d0c050304 70
    0x9003140190390341e042c118102803148e0300580190041c0b04910050060400400101d039100d040c0c1103176048039422800f000825860101401c0d5500a1070300c040030406001ca43c0320228200b0750003540314415000000700c007619080782a0900302603600a207260b464000500062180d00094140c21001100c0440c02c00034403506c4490304440746040191406645444040d05501c5240011881580c010748204560381203031119100082e056905030001880ba01c0046441c42c0700061001801c5200e80003000700d0114a11064030718100000c0032030301d0041c1071100040740e00b4100100e02844c81089000d0280c40f6007660b0140c2111400380001d84a440090240f201191804200c0c035040034841c5080342405252a078800d03d4981c40c6000180175610010b40c441c185030b1b003c02d02c50403c4000c0e54600400d0340f21403150600b42d684080014046640400448001a000c1c0d0f01c10030162411064002c284d0800c40b0b28203085992a020580d441500012260395030449440f40000030740c42410218114200b98 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 615996088 1250 615994838 615994843
    0x3160f020d051606050106020f0d091a0304031101020328051005130213080a0302011404050c130e1b04110a080105061b060c070308070806010c0b06010e0301020a0201060810020c 78
    0x2800c84100b44030001400303254164940f6800180c1540188092040e0750b540c1c0390089d550040e030364490410b40912092202d09030700c035600b0142111034003900c0750311520901a5044590f0b202a0084080c0124683c148032829070038000b030741c803c0e441c840242c2140c00ba148080700318610081255451649040108180c01c882c286071035041d24401c3e0391100e8800810860a4020300c5881e1441e41c1d00403920705c002480810000c0d4038281144207600920484500c640b80c11402d6805443c020442c1d00f01d904100b0a034203000ea00f03038002d40610800400e19002440c1c0039810710b00c801040040503031035640605081d00700b0303009500e4920700c800740b10762030040142001004a54180615407044400203080e02038000645001a010b4001509540302c1e0700304411520400d50014000f203001ca02604001880b260207281414072460040e102c00090300050b03515008150340040240341400b0174600b6410032038800344007900000c1b9840d000010b41d0b500b4021031529005288070b1042040d8010400b031011351901 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 615997338 1250 615996088 615996103
    0xc14040612050901020915072a1215050c03060102061503100b0415060804060b100f050c0a05030c0714090618071b0606050f090c03012c01080303160f02 67
    0x480301c006a1a00c0745004280684180840954050300103606200305c07003400b00051079a04d225148010a8100004074034072880c400040a035071902d0b480c40100030341b014000200c4900e511403210510001d8103544803c0444406544041c8006804410800d555804200441e0485c41410384501c0506500380000d5485c1d103510f042e41200d03074a411111090341c80300d40210303212140d40e0100e20801c68413950014800c600c01c8805a55541c01c010781d01d0b840c7d0400034064895040140d0790000241026142624650700208855540b44105403d5202194080c0b0240511a0303198019105403032503c850b24201344403445207a072041d036265081c40103641e01c000455a9030b01d401d8504060a9403003c4003611034040c004011202080315442d80340402c03025a02507004c0d01c204030384540792403400e0018400d1211045850f40c000090800042c400030304030a0003104000303c40c51100340580c60102580342c00e500207900c21904c603407000c0144100001e2100788454602c00d00d150481c000d03890b0000c000d5882e45d4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 615998588 1250 615997338 615997367
    0x60801050c0a08060328020d201302030105030c0411091e0f040e150403050c060403020115080c0a030206090609181036020412050a02010315180b040912030c140406 72
    0x1b170040c800c10841d100c0c8184103404d02d412043e004820246092140386100480c180c540c0b2680030790b006050303814030b2031080da414ac8401030b000b042c841e80da8600b030200400460f00c4585002c0303801d1250004507656208005420b07580f00340c05003542c0d480d110511800100f07050380548581e0030205c4503c00c4e0400000e07140c41e0344141003a000c0e015122405d05485603c41c442da0511180580c40402040c9a0150401c4088080c010007568040d6620b44540b5160ba5404584a50021000c007040016140420140c01078000081401c0d1410443d517002039400d80c0c0d0010380c540c4c0e400c029800c200340c40040900c00390081c07403203116944001074001c000f4030640c50004180c09414808210102061039103138140e6001d40110300e40c01c0154820742c2015541c800c0107401c100e001034107100c030405155402111800c1180e4040d8130641060021115040103000299109a00995103020032004a42d8a00c1024030303560321501c000910100e40301c4018450002814841480c62040004001d46603105809520074134 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 615999838 1250 615998588 615998653
    0x6220510080a05040f0203120307080c0a0e010f02010e0a03120518120d090221010609020c0c06160209040c0e010902160b10030203070b2206021906060801050c0a080603 74
    0x80d130b030b464104080140035030007a406102c4d61407001d004c2d520030700003036008045035140e0401d0781d13842c4041220f0724030405100700f001446000764051594001e02440c40707040b00c5400081038061200b81c0c980d1419500c41003c6d800a0040f0003810030fa11b030948546504695443c0c44501c0310110816415034071514116540c40d0300b04000ba603021041001d501c4004100d5004001c03403080301c020000150030880021980e04a5440c0034000128a4114030843d6010710b50f801c09040c2c14414a4104810b80c0c00000c0b403c10404c00c1c3e422078100613070314041354a11451082c413862128504082a200840314142c0217101c0162040148020314007100341d0f500002c5520a4102d9240c0e03584070900640e0301e0180d80000c1d0941310703001c1e010540000b02d002800080c19480030b082e9250b0305581a102d2070507064400e2501581201e440031002d0704148041d044414080e00000c2051070f594180d4908459044600f03081d000d4002c54444081903010a4482d0094411402441c00d400f100c056134118509454000f10200c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 616001088 1250 615999838 615999841
    0x4030606080f2805010609140907380a02030403031724030a0b07021b03190303020f071407260c0f0118080105010e0601020a0b0c0a050906220510080a05 67
    0x3c044400d1039020340d0764000300070f21445603503101200c06040d5210301141d60b500c0b403200041d01c5c2d42000443c24211200b0740305101c003881d07030710110380380340d16602040aa105c0303500c6c400c05010b601032200034107141650760b006503542d520754140203003089042081f030500304400c8014030004e1861800da1062014040c0103105a0464070070020346802c080301c0c0010410b90b032200030052000d8002c108070041c10f095a101c1c100c1c001301ea4041540341c480d1805104540c4848000070303404684a41d000d0102d21100b01e19040c82c041d90368071684882042020328000f11f503c000e00c280003501405845030b40340c2d025051a43d03030380c800e94896143c0352149042400c0c0100c406d032060250076840350303041040e46942080c0000e10300352030780b04d0f0741e010344030901030600001e001c0000f1600c00d51001410484c00c0d504220701060700c1d120704400c096590300c404801d0040040c144024106580d0720801840c3c05080700120b1100c00002000c0140e0804083d4800b03071280c0c645852404085030800c0d02103502060610000509 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 616002338 1250 616001088 616001143
    0x120f0a030f0306030b0a15120b0a05060d0b04050105040c060503040210030f0f090804051005091c170a021011180d0f0c03030c1b06170403030e030a0504030606080f 72
    0x2800194800381002c0c00003028400303414440d40c0684130501e03840d51f842d00c0503034464612203c1910b41d41c81c01032100214000040c01d07240558029600a48000d00d0458410fa031a01e0720b41140350251400d4076980d5407a018801005520050100281194103009042d8545900050760048885505805058507a05214001c043c103a00204c0c101d400c44008100880b65420500625006400b52500078840c0500c46130310140148155204520010890550315000c141991a83c030441d50080364003101a004400c440402c0801134040c141c2c0a074000c001144407e500307842910041c89409860319030030014003080041d040031440500400780e0b0f2200e103001c07503031410324200e0604800c00391600305a1040801019844401c41140354011096685403c034040ca000480c20082e1084a0210350000ac0d8510800ca14884d8294460702a050020300d4195120943d4111b610190910000820004090040001d64031882d0301908445004082c20440400c0c400c0d40d951031410703000d0f00a000c101c0501741 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 616003588 1250 616002338 616002341
    0xb0a0f020717030705190b0115030906020d020d0c0e1e0307091406011d0303070b1f1707080102130603090c0807060206041a090c010503072c120f0a030f03 68
    0x24942e05480304240c400104070140c50303800c01c4c1421907543c000c6d82e9003440a5a0103404082c800c0c0d4000101c038903c0c0e481c101d00c0c0d010a406054402040c192946203900110b000303072010b060804a40c60300540d03140c50304030042c0103c8000282d1201030024407641e41c1d10355210500e01032010107040c1c600c1e040c0d20301d05d01300003840d04001394051800f060412440403c2c080304051031a000780070030b0b2100b825015050052a0750440d80720b50340358160b44280300b03c0020034841c900f015040101111541c0d06410301e0340800e45180c9454020700c62910384460903500c98001001280c005000f090002c50400600e840003440c40715840c41448105a08c40c3c20341d0042c0080e00714054020880e03c4101d6480d0303584d0b070740003940302e60303044a003a202a011010b0303c4c000c1c18001162144149064005401d00701014001981c0c1604090202001c01034004148032244400e9101c4104604155800c0303211240d0081c1005090f02c401c00c2c54141581000105900510380001e0103001706038142001446020400310850 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 616004838 1250 616003588 616003603
    0x91121040f08031e0c070507123507110901052e02030f0721030c0f08070912052802100c15050109050901060603020405030c1318050607180b0a0f02 65
    0x74045015410f0165090341178005100c40342c400c3c4160380d003060390707441100000700032040b0252001c0745060300c207120300d29018041d000034a1034400340300b0302c00d52030030780b00344990001c802c102c0d10329214540c030020394a41520207900501c0100d4407142c00326030001104106803090321360034481c012050082e0282a00a0041c0c032101154010003984441040c1401c0e440c5100c0c1c03200520480c000d000c9018410341c070074001d00001100640307403100881000d002c1103540d40301c0141034008200c0e074090302040c103402e4896001e4460703014030024883c1c8000700010340101070b041108a0340107e10300c08443c0050325030344070100340e01c120703420302c03014280f61800c00c0802c0b141008664040b032450300b0000b08010f00241d024a0140c12801c0c002c001490b280c0c80c00303030128882d500410340e240d0301c0224050040d04c0c1902586406040f40d040c04102d0110b80044002d261032601c000300c80c00d412540400c0b5100340d016442101c1240c820b241c01070740340c1c81c0c40703046a050b12071254600204181154016602d331300130004003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 616006088 1250 616004838 616004881
    0x4050117090a0f0b070305100605040612270b0c03040c2102030307031d1206060d060b0405010f030b0c09010504031202010209101814061b07091121040f0803 69
    0x290760f080c02d4074011100050440d03181010a01d0030020071b03000852a200d00040d10015181d140c03505043c843c007a550102220b0600720034588544941490350111440c4800303c1d815502c03c0101c003d01440d00301d10b0608024012060046c0030300410010501c40c4406004468176141404407aa108103503003102c222030528041d42500c4009000d100b0942d10480003d5552400d520110315502c055042161a25100400504961084c0041030b030a15002c1d0319510102d115050000f070740c15440006c5401e03600700740e1015090100000c0304000740100521119803000944098914041010740060001d0243e80000340003803a039801c1c10882c90b8004d50454a4000005143d0716120040b060b000b00f141c600e80000c142c0884a00d000001c0ca0005418040601c44000308502d04000c2403100d81259188440040720382445081000070721111548109061030700b170004041d40c2c03612082520107502c0400d6140c00b600150b21030401c0017051407840220401907020440703e07034a4890303454a004429400700b18 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 616007194 1106 616006088 616006103
    0x3041502060403021e031201030c050405060607030f0f1b05060702010e0a020102060103151b18050105160f1b0902030915160305040303110c0a0b06040204050117090a 73
    0x5013a010002d11701240c2c03c02414034031180e000d003420303070040e10340c501403030001d101a0910740980b82d8003050a40b0014034008080d54000e1103024144207120820041040c003006a0703100d50055182c80d88c42403103c00300f02040381451074a074001076480707801540c40c01080c080042f401044034207030303a601600940108d80ca1500d500c26240020071015800c40e0f510511402c0d01d2108841c02c01c110740b502c0c2e0f5072143e582046600980031403066000203041c85424030900c11040c148684941c03034070354401d40b811044005490400c020226548803003218521070040810305034201e0740038600c03844007041260f800e0703d880d50348032504040c1079600c80031403004544294401406900016002486860000f07821421144152826042020401c1e51074000500701e04c184680840541e4010404407000c41c5401d2a0000203841601d409004007101078142c40041c032050014020a40d609030032450 = true := by decide +kernel

theorem cover : BRFrame.Cov 615827338 616007194 := by
  have h0 := BRFrame.cov_init 615827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 615827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 615827338 ≤ n) (h2 : n < 616007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
