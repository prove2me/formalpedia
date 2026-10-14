-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3236
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:04:12.363585+00:00
-- url     : https://prove2.me/submissions/0d046a0e-eaa9-4eb5-9815-fab4cabaa736

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 581834532 ≤ n < 582014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 581835782 1250 581834532 581834551
    0xb03220305032202030d020607020d051c1808030906071b120509030106080304090c02070e040f0609110d0b0a0f06080a060509071215060f03212303090c0102060c03 72
    0x1002c0060000603140f005200c0e0b64001d04642c04032031200320081d150032098501002512440c02c0d0300091178024002e60b44082541c0481203110000c00208001800380c1104130104906010310380b81c0440e102400452207080d60034010072450500c02401030009006184400da10181c1c406004002203044c240311802591904d0320700e85030f003403000000f40102560351014616110025000509a0803500201d903444280e800752a07440d0360340c01c4110400041118004c04410115040743c00044860740100340e458059401103120101030004940342000c80e8000382c1d03007aa072034410000b4440076801550300004207c1710034841c0601e4050116602c42040307100600c0c280d180d40000c1c401d010100190b100500f04146810001e52150a0003465501040c110440180c100ba0001c80c501c1c415003552000c41e0303404002d180e4030368210007080c140784403284400000c0201c030000030380c40440010025140410f4408800d95030781807100800d403428080c2c1003598103541003101000901c00030030040d130344e0141e02003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 581837032 1250 581835782 581835811
    0x6040504051207061406092802070b07030f0515030d2001110403051005010f05060c070b0a03061706040506061e030d0f080f01051f090f0b0322030503 66
    0x41c035015040c100184101c070160003012581d4424801d03290001c0724410403100d004c0c044c0b5100d4400340211010121042c2c00e41c00c000040c8004504001600310117007101d90000141462242d9542c3d4210010584504001a46802d00d40c8111146440f805411601d5032030b03814030280d000da002c203440c1c20580301280300784014511814a2040700408a8102c2c0c0c01e542c0082209203682c01500e4116001130009840038484e0207208605051688901c5040c0c0302c04080f25015036250004110940c0e101c0000c4503014043d540300020914032030f00242c230400304144c401152040c20080344140c40c00e041c01640b403141d40080c082c4004580c01140e601d030000400d03560808001541902c402030720348035100c140d403d41320780d86940400c103a02614002100305244e0f50f518090721101c0030038055000a000751940316100503403035411201e0709200007104010034200710048680d81e403141c00c40140c2543c045c0003030140000c00c11002c0029104c91310304c80c00c3c800c4642842880252001000c038000204920440703501e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 581838282 1250 581837032 581837041
    0x120328030c112503050607030509100209030c0f01050c1b040f11040b0f13151106041112070e15010905010212030103060906270b0c040b0322050a030503070207060512060405 76
    0x543c0b02d00007a54115040303603580d0500c10345c020001c0c001101e20f003d2602074950701050900150085480583e0300400404003c0307401d208011588652050143c107110041100c588803d03003d014042c60031a00000b000503905012052205840302c400d8207442c402c0c58a41c2c03500c04a03124a055800b600c2407000055112008917261250038400d140100f01300c076000200024520f0506c40c0c000069900701d07550700508070300c0200cc43e03948180c281c4000f492403440d002c218881d801d1681415401c81e001600315221947d680300b200041840c2078950344801555000405415600001e28000402e03003071004105c0d801802100e82c169000c180801041c0544502e08002404155004022100150394012080d0100845040313074a03903510104940101c00c000c000b0b100611801c0650b0308407141d807249103185030341e01d500920003402c40400c11150020302c2d25002004c1501000041e510703510946415599052010001e860300b0342540c80001000390400c083c0d0301d5241e0100746036800c005d0507030340422143c44 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 581839532 1250 581838282 581838343
    0x603080f03041712011a0f030f061f0c1713140303090405010e060a0503030f0a05030a150b0a09081902041e0e0102071e050a02120328030c11 62
    0x21038190396550740f4070100e88810301000758000d0a048508080100c40031110300c024585490151150304c1e40d801c1c5040c000910b01c1481210100d500001c010208004030264003151200f020030b0b00410800221080300b0002002f0300180340b402643c0b122103d281c10800b0398511900150b4443c0501d0f0040d20310554403450648041098804042006200340f15960b142c1c0b100d02d00160040351000d01c02e000c084400907040c1408000c5407203603400d03030052600e000e1034170500340d0341390b48050300010625a031103401800d0b0030b1100358488003811202d0340b0982c0d50000900d00a20225003a00005440d4101c24852007031803030184420340c101c3c0c4d030580d400320f100304110701410010600c20b403001c81602d0820b40c041681c01d1040d80280609032103260503040c0b0a0844254101411054200a003c2d900500c1c451015190080c28007521003075280440b85080c0081000c518442e2003140d1150f4041c505000032405150140207089003e00b951900c02c031480b08510002e0b9a582d01d541402c07040c407100c41c282076062103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 581840782 1250 581839532 581839553
    0x1201051009090507031b0809030d0207050a02030303010801150806160309051507020120130b13150315060e1003020a0905030a2d05070e06010e030a06051503010603080f0304 76
    0x2c207840c10025460031101c05805000b113a8100044100c50802003135842d4040c0702914003441c5088004c1d803c044010050300c000354000310040d00d0900c0b441d8014030040e1750400045018061080020500d036081c2c2c084541c0449490b00441002d030401c1c8104a499140ca03110b98941460614011a00c8000340c100325041c011450555400c102d507003c1005159601500104018205170329002c200703170654480f0603158041c00607101c0411000410401c150100d0601404120310300081750f030034495692201c1507030403040c0750f220703c0403a0715003544146a01c40091041c0042c8040d00740b11040c41c1c031603000980b41001a1002006056002c1050446248951075620103084041e0813904150314906020701c60b04503030442400034050204c10700100194002c68402d849038850300800b480d909044040070780e1540101014108a080c104941c1c03e50f800f00105c42030f0602404c0c001030117003414100048110944100140640c1c18501c04000050990040300c121200035242c46485e40ca40389454030310310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 581842032 1250 581840782 581840789
    0x30702010f17040c05090a15150e0a03031107050a061704061d100e03090310021806120415020315010309080d020720042007060b03010615080c1201051009 68
    0x124002c01c1008008104202d201982d804440c1e0300c1a940c2da000001b41600d807480059405e008a1a00c10000d11206190043c6048620f08058814000c408082050180598800e07400136a61541c20300c0001018880308000d014152240d8000d61b040c40c030090242c02a003845150b07440c10440004007406542d50010f40c050001010600c03400030768600e0300380c0c3e13007042c00d5814040c2850044a10803080c0008100c0d0044100900a0141080c1d02c2405c54020340000300c0c4a00c2404480640000c2542d0381ca0040c200761460708034090030381c1000d05105443e180707100020400c0920400034445a59207403180f14520840920700070925442c43e1421221038003818109500c12800411640c080000c43c9086400800c40c640b442080c032447c03101000309488401420254440d003402c00d09251180c605d0041c01854050840498060301990210703003100d50640c051012001c1c4445035030301043c1c0c031206050700142d0861200341441e040340d1300d8441d01101841903d20440f22003c5032100c00740100f10a0006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 581843282 1250 581842032 581842067
    0xe03010b0405091612020a0512010b04020a030c080702150c0a050c060f010608070e0a0e091c020c010f0e1e15070c030b0a1505060a050906040306200c030702010f 71
    0x102e003002c1c207400707a90380c1a90000b07054183c0e00c0100405c2031000280000003841e002014451000d01d4402404403810084265070340030f5403144071941c01519140000c107142c980658000808000d800d50007419150041d107504115042035441c1d00007446407035402608485006646652800a004161014801c0136003400300e5000b800c08200b4601c42001f040c1d812121141c68020a0780e844a8040300e084201071003440d4010704d400c4041c00301d00049210365501c12602011600580501004110f01c141030300c01d4000142e00c08180c0700b0310340d6400522210030804a0800141c032111280010703140c0350301520b40c15091002680f803126195034501420485999000d0002d0399800281001c402680703031030000350b800d03034440340c00701d6550000c4d07100b2241c4240020340420780c603038285020450150b00a01d851300400506100000c2c0a0307450100900055100744000034a90b40d12208130141c1c800e14801e2114440c605101e0700c50421008803c0307035001682440c0c072054000e882070301503815000381511550b1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 581844532 1250 581843282 581843291
    0xa12050403060501090518030c061617160e0103090c090c0507081b0714060703080405032106030c041506030203070c060c0503070e0f1c0c0b13060e060403030f0e03010b04 75
    0x20b00441310303403001e8001c107c4d1807070904800254408040d601d04c0382c29101240399100d1400103803c014585000f0910385910b14000c4052038480c280c10408a105031510051018982c100045064100000c020001000c0c20240310719a915110164070446600c14000810348940b01c2c403038428402c070200d500d00c82c0d1040d101610340d0700380d40368000329249031040c0b009640b00d6100041200d800032052031143c444010302c41032034036217243c0d0116001c21014000700c2c1d442c8424000c0503507070020b203e000040d1448050300744000340740c200209440c1024046000f8002c0b4030780060016580319034000d10068070600c1c100942c0d29100c04008556440c0c01d018094a118504090700c1030039a40000118010340701070782d60301e4103011032004025030400d41c465134542c0040ca0b1701c450100c4200e8000c52300b1166028403500d0002690b2001c80c10105d40c40102c0c0c0301e00d00c1c002480c0c103019036500090311040781340054803105d00381403c5540c0039080900401c103246c00d2290708110110207640c25040303882c0002c4090b00a00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 581845782 1250 581844532 581844539
    0x5060127091e0b0d02090c07062c1e0d110712030804030201050f06031c050f03090f0706080408030a0f2306010e04090f140f01060b0d0c030209030a12050403060501 72
    0x2c0c00d920a110b200ca5043c00d080480344a0319010049440b12500241110b000c3c1c1c40718482225141d121580448441ea00c504040803a030000c0e020340c4207a005003440825092280d012520704058408003040300d426400c5100d0202640c00003043d450341c404909060700c141071100d08551405000703074405001c00f01907400039001c042d40510701c180503610a800030302060b1075003150720842100440f441901130f884014680c0000398111808118100d440c01d00510703188141e004e0617019481150f05100550201c620a40c40c170300c04100c1c144c000e103100c0c940202d40c0c2c01c1c5a51240117034030002d0b244c582842d441d0814000700200e02e504c0501c0200c6804440310341c045500150703080c401030072200b940c045521b81d000d203c200d060034014440c1c0540c0c0541c4060203d4015074658104041e403070040c3e8958810007140e044451401d00ca1000a0485070a009440d01c000c40094001d50b0507003d9000e082500500043c503071504e0016422105a81c04543e03041108803c0004072041d004030303031010301441c1c240070000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 581847032 1250 581845782 581845811
    0x1110f01021306080402010c0312091b1d040c09050612010e06060405100e0a1113080703050606010f0c24060b03040c0501020c010c03081905010312020c040506012709 73
    0xb410002c4400c4403107001941e6070701e0251030100b002c85010340030405158030900084d01c550260389420120b4540001c2c0d005103600c50800603040da802c512824107080747c0c01d1002c0d21b80082100111621701d1401e0441c1d152a51706c265104a552190015803078a031000706800341e56020849504541d00f60003040840c50082003299035a4054409034000d62401021410940184150106550242480c00c0c03150f102d40241034001e110300d001e00e105c038442c10703c0310b02108060145ca45008100d101c0040181034251304000d402c0c01c101500700342c14050b00d1a00b5143c6103030030816007002c19411061800420389000d40d0b1301554075010251001c990300d0042c002c910450000091809107000344e6240c404c20b0349400040e41c1c0c889043c2e080b240070400000122f000603100d19583c030350010040211003100840300c07c20005440b02a001100d1018400b0000350000d607040144211b0400304031800e01280c01c24000217001300d00d02d2000100ca404405000038804111801c0c00310060440840810405c489e40021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 581848282 1250 581847032 581847037
    0x9180f1101200c0f0102060601271d01080d0329010e12010c0206010902070c0b030a090209010306091b1a0906091c0b071d0d0f1203020414030102160303050601110f0102 74
    0x5644c41201c2038403662809500c002091445200103840b1a0f8918410f0f002d5180b03000d1070007058000000c142da0340452414080a50203103007103500a032910b11541402c58003828410344022030f6040602c1e01185640704040a0905000300000e4400c0146011407440102c501d0f42e91030704103075000300c4183c0071400103000540c4581d455209903402d581050344c0f6203001000340e106104003c0d004c03818202c014000364030076200554019100e9500029881c00a07804030702d002809078001e0f10080ea60352160b8081c01042c68040c0300e08482c040c4010030141c20041c04d0744c910090000d000101400201d4030280580343d032012110044401482e90840c1610480d040b040c100c11500216442c0320f030300d008298810f000d043c03180100c0d4084d2000c0340ca522140420f01101038040001580d80c6800c00c440c030004030f084424007441c00b56070b5650150b134603070422403440c0c16030042140450281c2e00c1081482e070614002c06000f1246541071601261946170358004884c10518a22040d201c0d000b41c004400c0d021505500 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 581849532 1250 581848282 581848303
    0xd03020a180b1b1501050910030b0f0f0a09260f130501020f06070c02131d060702010b011706060304020a0e0f07030605040c02151b1309180f110120 65
    0x1248a01821009210fa0710703400c0081010000113a180010b0110349071190000c0e610660520409001c00c2c0d4a840f074142410040d2086c130700800400040c072010994901c07106a11a52000707080c440d40410b903950301d60060f48040c0342040e2a004142c00350f01c114524088981c06016024241d44400d003008003112819081c3c402c0c00c0c050b10030455491103ea402140940c40f44541d030311406440046074090100d40403003140c08610890b659003003007805600c1c01000700c6441a0301c400514403883c042c50080d084034482a000c03810302c002000b07140841402940341d00d0b8803000680320f09459442d2480403a100044540200b640d0028650802c0080d6152401c1c03640700b80d40710354007401280d0b0f542083c00700b2203404d00a40001a000b6120316210702d00c0c500740c0d041d0869280541c44084014580b20015542c11900032031040b40781d000402c006e101c4041c01200c0e0840501141d121040300c003607984a000f4640400700601d154080080c0d45100c1c2c1c0248417230145030143d490510040c421402a043c0c03144107020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 581850782 1250 581849532 581849557
    0xe0727081e06150a0b0307030b09071d0a140f15030717160509060a090f0b070b01170c1005070c0e04060e0609030901030f181b170d03020a180b 63
    0xc3c441410b0700003030a0070303050040c00045289062940d0b91489031700083c179030320506480b4000d0f1103081d02d43d089035520402d00c585d10400010b0341000405c07180300c00003005034031841c2c110200f480003807a208640d5607841c8081725400c40c0141030401060319504408a030800f1081c3c0801007003c03041d0044d00212100a08401d400c40c16038503184041988074040000d40005281400040e201d4108a030050800d08942d003000381e1010b42e21903130b400703103400950004104501c1c0450702c0c504201247c1c28040c050b180301d941c500e028170240ca48643c0c1d42c5048100e19031040312801c01c050041070155044400507500801440b09080e143e0391500b41d5408180d604a034103915003111195200c1000c220035000c3c0d41c03480081c520b005010f20045025044c1680d040d9440d543da40349904243d8507403001162094410b41c40b00b00b07882c000c1001c000105170305601150804000d006e5612a64502040e01041c0341e1660078016200c0500381c00c11551107600004000240186c40d00101c1e021110030040c01c4040b0960 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 581852032 1250 581850782 581850793
    0x150e0603040b060a09020406050315010c020a03050106150207030b060609060705010c05180603060a03022b120f02071a0d02040e0a0b090a1103190b03060a06050a0e0727081e 76
    0x64503170700200d1049103d4480007500070701c040703402080c030f03001d0340300314108142741003c0b6015258000810030300f01a44221035a0b99900420088401d050441950941d00c90025002c5070b841d6407140d2406000c020001e500c24100024094030641c3e8070b200b900c0c0400d4128008002c10744113440c0140545e441142c200395415034141d01c0c0c988610340582206d105110107485851a07038515400c1c442c500e0742c800306000075105c0da42140c0400d041c2012407a0420303401000303064045940f20801030020080c0000c900110740060700c05104180311071440c441d514440540140d55201d0b10902000240116000310000c1d80500c0240810300a140e04049402801144c0c030a109440c0c3c0800c0300100c0311061035613141500d0510010b030080075684481c1c4410908150003140c4002d81000090414000310b5800481d03613900c010610241c01c0c00c60040024200c81c8081d5440da0600d200701810120440d460b6072400d607080310048803449140d9007004c0003040c540f4111020b12400d5011080d1035905c04404450302d100c1c4c0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 581853282 1250 581852032 581852039
    0x109080d05070210022a070812031f0506040e0403090906061101062702090307030506010e09011103040b0f130210031a041515180308030a0b030d09150e0603040b060a 73
    0x4d48211607003a0410350b1600c1c500324102d000c8070b19480c40303501e041c0700c00d01030b00e01e00264400045c072400d40d240e088400f0306c41c2e0700e25000160610040010f182d24042e001d180c4070070b2200e85c0315542100c040c0ea080c024039910b03030b80d00c0e0b01c2e08564142e801e4104644150500d18002441504100c2030281d01d0a01c0d8028880580c58000110b00d80203035030070b50981000d050400e030030b688815a004020145019054a40d50390b207a886203442e0030000c0e4443c0b50404d842e0f00c10040305134428410703440300740141c60800745141410303250503103916000f500328501c440f500404149400e400880d110b50050b8050100c1e0342202099402400404c05046024141c0c0b0300141e5041081c5420321820690b1103c004060b000582000c1110034500280d9044a043c0030041e420054070b401032956680056200b8280c842e078074035060029400303491100840340c1c06607001c0d0714401c00045d008101c10301039850007074203516030514010707003103455440c5410721399008440001400140442403881d540703e1a01a20032114980e0ba = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 581854532 1250 581853282 581853313
    0x30201050601030c0f180f0e07140c1506040f050c19090305100c021203011202120c0901090c210f050c041508060109170c03010f0b031e0109080d050702 67
    0xd01c4c42520700140081000012190050184160024a101c1807040702d40c4c44d0064950100d0050300310303503800e0500c2000c01c80030903404124600e514011815283c20880c20704d505590720382c8920300140c40788040398002880c82e1100e90041841a4655005000604084a16005075403150510b82445540f81803800101400b940920048a0340000140801030040c0306040050400c038010004501511400044042000e0050346c085c0c4500c4140400c1504144100318100c0a01c8840380a40d42181c900c115131995000e00c0705046880b40702d03001c00c0314540303010202c980e50b410072440d0040c1c400100c5401d6561540350300c4403800c800b410b0780400050b05c5000090007030340518407803180c14140a411505587d4481c0716042c3d00240b06050140d0b9040d250280e040759480c0e01c09401034154040d8025041c1c80c40d007401030500910512804200800180300866110f80842e0441c0c51900d920340c01c0c04921080960144200d284c0004e030441d120043c00d42c000026000030341d107400c0180308640d030721a000c54 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 581855782 1250 581854532 581854541
    0xc07030e061602030a060b0a080f15070c021216061704060f020c030426060412030f06150f0210020c070302040e10020c030714190308040f080c0d08010902090d08130f09060303020105060103 83
    0x8808000038140f0504504188564bc440180800c0c2004080d01d003040042e05c0e1070604850505c0d04a01500003140d04c525200d1030080d40f0340c001c02c20446116180490352a00649080e0815004400403404240c0f000d03100c400b86c82258010807845c4030001e000604070004507132418a00188583c440c0002d00214840781d40c6036026640504180250010303040e4140c082c1d44446440304040f140800d49030f41e83e6203020004441440c0d1500481d129090304440b06605001d400c07840481032074114103200510b51050740d1000c03107010081c0510755861125058890802000515458125096541c2c940e0844001c0d1641c000540032101403600c0c24900b081c0480128036085e2410400c03842e010307440925141203440380d1014005443c0a0b03c990022404600358200608030482d042c001044c19a107168001007001c0c40c140e00051043c0e10602401d10983c2c1e03034032b0a003180a0b40145000d91100e0000b110480b0030f0106d9408111614001c00f400101ca841e0380e0411011079000344c000300a90350380d4030300540030355 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 581857032 1250 581855782 581855803
    0x10e030403081c060909060506041803080a0c17010f03021c0201120911030604142104030602250c051005090f061b0a1a0c07030e061602030a060b0a08 66
    0x150b209224a8642d840e050304580a061030f464800b1804075a00d1082d04101c8415103c20340769203460b2400c010303540c01c00340504400d2a9802401074042c441c2510020300f9504090080d220300c6807101c01014032284140d966120b12070640305103041030b59403091003c0c1c04014078403007280110404808248529051401c1c103040d1501030b19082c1a8064a440b01ca004290f102400c503006002041003400c55141044124411307840b07007c1d11080c1d02c202010291400300305810003c90590a4036074881c1d030260510650301101d0f80f003440541c46566030b2400d85840c2c40d02c0044282c42d801c24244010500c00c00590312421503c0950b246070075a40c410308200e44600c00d1440050300203224685030f2159080441c000c00b1343e031031180c2100003c04000b5480f103051403032140e010f035440b04c4144c0c4060448400c50a68680100000d01e000303203030070310507a0090038120105441c0c512401000c114044510525600364814640c001c00341d03011042c03540340080c01412003604082c0200c242c14008201940005243d0414 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 581858282 1250 581857032 581857043
    0xf030307050702040905060f010306180312020a0e09041518030221040b0f0c2401031e0b0a0c110102090604030b060a09090c0e07031b27060c0203010e030403 69
    0x8564600d6000c0d1000e5002c08001c9820659504440010500600c401400b45070b8a4a01040d5545035027860006c4c0c50101110303800103408a4000e0700080d03081408060546074075000540c64403240b520559a2209550700c0c5600002424100010404152025540102740b00b80801c50803000710380020a55200c00c00080c05a404824000760350488031580385400742d61000e2052519480307038591140b90f045024250248031000c40d8102c40418117028102459009400c00002140d03c80c07070090b0b0082041c031000e810500500c2400d007440c04002890740746290803040300103890411041d0000245840c480d0040000d08400c0d0403402000c040c000c4410440c4e0050040e4281829503d40250b0742002a14055126800990015511085010740084240540403c03840c081c50a003041c018160001c00d80c0302010724081da41502e003d000808012003941c030b851301402401d41300290b09a911f404811919810389182030008400e50f10540b8412a14404d60003813017102c100c04038966690040740402400c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 581859532 1250 581858282 581858287
    0xd0e0118020d0c093603090e10090504030504030203010b0a061d060c011104031205040e07030e161502070803070b0610051926060306040b0703090b13140f03 69
    0x1501d40b20364506186405852440600c56036030350080103d6584c0025141c8082c4401038100303000141c52010100d0641c5684400d80c0180715950081642446004514840b840040480d80b9003181862420151010f02020009801c00e030034060807903000751004902c03c0d8285500e40c1c440c1c1c1000c54030f19003142c619494070064944004040300302410980c1926070000307428080341ca0180b8090280c0c29114052114207070740e460950030040b011110a01c42c04d81070140402c02001340d0800381985030ba00022916000a1246503140e42c00d0400039114081050050b852801041d445000b0350740301030512070b07134089403602607450315095141d000705440036104180c114000344103405d11126408a4100a00d4101c0c5000b070840d40c1e020000d079030200c4080c0051900b00e1042011880450700c076812050190121000380b030310f500025502d40006100602c000414400303e02c101d406600700311945540506000264176188208202e6210110400d842c144600c1a18800034080400ea5405010461001e0752 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 581860782 1250 581859532 581859581
    0x7031205060d0b011502060f090a06180602030f070306050d020306160207080601030809030d0c21030b0d0602120a05041a060d08030f103606080a03050d0e01 69
    0x208030061106400001244030400080c040307041036800382200e003091083c000c003103030f50003403a08100230840e403c1401c1c01420f0018681001840c56082644100040f490001500c0c07401042400039500405860010040c0011000e121203001d100300c81545d01004055560410452079031820383c13020f5015000400801d40c0360012030204403560281d4012140e10f140d4071240c19140c500c00343c1c8140d41008000c00c036035206213000d000310740d0319a10610b042034411106845200491840d82e0701003007254030f112258039016005c0e8100c01c400c6070008000c5002e000181c10b110020754030000e01185203540c0c640c00504183c08503c155801a070b01710034402d090740030702d1440040740040549002da01035082d50a100006814100851152a6100403030030b05080007100700750002d5040c2c0142e6a181e42000400220504002c16a8852204100543e01340200b0000610084c0b0013a0810041401410080e001345500040201441c00f9070040411946645030030850884e90406148080400b8401119 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 581862032 1250 581860782 581860817
    0xf010311071b03050d170f061806010e030f160e0405060105060d0902060d1a01030515010c020f09070201060e01140904020402070201030f05040c2c041407080a11090105060703 77
    0x2803000701001540c0e0b401054480d269146070840d8041c1c2c64000580a1015007400c2c806440e00603045440d10061055504201c0b001801001a49130500d0f2465082c00004040340c1c8200300b1001407140140a9800201800500304e4589418401c540c80703d00c0312060002d85107135a84581407107507030440d001e000c00740d08100800910f80e10011075002500d485403003100c05070352a20700a04142c8150000081c0007684500d070005d44175501c00c03825042c54640f004002900744c400c40308520440d1f092030310203c3d01d6201c0c8000744842d9000d901c515006076100003046503880d01503005409031034543c041e05071240ea0342c0ca00e410000d400802c486030407487c90320100c0e00504094015180341d41c8141004a0301000c10354042c000c954044400780c40000b8010030030010048252080050b600d0b0400c20403250307480050696400c0300c00508010311b000204406200980401d2001001420001042d21a509101d040c141244044600705520400040000180e80d2030504221048503525403244100d110030038114 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 581863282 1250 581862032 581862053
    0x3070b03130b090307030306091505040c11030d0b01090b0c07050d080c030a0807030b0f1f020f030d02090109090513240e06041a0c190516110f01031107 67
    0x14018800314260a03100001d082c51140d501c92007100000319140c015a050060580e60342d544244425841c0c0b9030711007144990003443c0000d441c029100800d00072110242200c010004031019200c2d80000b1540e8840004240c200d800c103004240d8982d02101c0c1c50310140162485090082c1d1420780c4010710030401403c00440b201140344c00f0b1800a410150124520ba00315844440150001600b0408000d03d0740c3d01480340b0103041c1000d54115a0040800021400304d038000c1c0c0c45150051644454060140d10821075181004002d4043e60b403120060b01c00040a50099451240451040c900c04501906940300b0700d0b05c1110074800d1403142d02650f45030f100200c0070005140d9142c040c500402c0c6143c908902414101d1540300780141041d1505080c443d0400c0310001d4a800101c0800341806a5050f554080e0740060f00343c001c02850a40008105481501c5074402c11416903841304121010300c586003403482e000d014103444003c036010800004404551180411860b0044140000c1000c101e14849 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 581864532 1250 581863282 581863291
    0x9060906111c05090c0a0303020105040c0f15210903092d270606050a1209050601030b100305120a230d0903020c0301050a05040c0e04020612060301150603020c0706080603070b03 78
    0xf6140005c1c6040080703540c0e0040c50704140d0241c0e4441041c0f000700201c00032004018200042c070f5880c81d505082500d45040c0642c2941800c12014441001d94501e4641140c2c0b124440d0103c204041c2e00c203480c024180d01c1d5644164400c020b01d0b074450138003640058100c0c0c500c0d041b64900b01001d00f8140782005180302d01440000000c0701448461111441c801d02c9981c01521283d2034107900c601d05250000c2051541c500044005814202c690000800c0000c44a0540c0d60104254499a403118580b5586047d598000303802841022410882201814020121540c46a441d5041c1500160030b140b841130302c2e03942040041310304004e1180d80d0169688003400c3c85100b0320548455030408000642510001d0314280101c0e6507034020b120400410b040214003c03c001101c94200345841d030009105405034848a00310380c800c07600002c1582e43c080d405404510030121801c4010340d1607010041c001e401001491a041c41090004150f16004581d400d104200c01002051f80030b003821b44050305500003a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 581865782 1250 581864532 581864551
    0x9220e0607020f3016140d020312040201080c13090617030c060f090124050102011b020c0d06091a10061416210e18070e0d020f030109060906111c05 65
    0x5a004c01204a1740340c01c0d140c0d400b6071021b0b07107649096003880341448190f000d1241550f004001d09403d00011b100041d038003940909041c0e4441e131f11112162034503c01c50b07403900315100700b1240102d07030800c41d50300c403406589918181c4611030034000020380c1d07a48034900785601c181e4481400117244426401000340c0c01903203280042a6010740d842407441c200104c42c1442c2c0d00c0c0792030550501071540d09100c2d040c1c0d41f0310a10849000428445006500c0d0040c0440c241e000c0c900329814902840701d207030801200e00764808442040d14504c404100c00000e0103582c03d007070a004040c40000c3c2d5510900903071950070000e50f0100e150800e01607500c50000c03103211044405207a2080e80310b600052180c80c40340c042030709484110400707001404000904103803078222080c2451150901400590001d005180d10300190383e00440b81c00640006a401007112030280e501d582022030b1801040380b107400c6410707136522404040c08091840e90719913070540144002c041d00d40070003140d2555607a002d03410442e00606200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 581867032 1250 581865782 581865787
    0x50d0329030c0a06092904060c0f0c0803070b060a1a0d06030605090a051c0e040e1501060504090b0901120f2d1203060b09220e0607020f30 61
    0xc0c000c910742110f190710081c085001c0700c00c02c00030304903d0724008074600403240075000803886a1301441e28030701070360103041e040010b101005d008112003110030800c0c60780c000b1708a400c06556010740b10794a034005001190541300c050007080e01c0c2d0428440d81e0003a101441c40b952068082a40e80302000c0e08042d80c0d1404607901c503100003010401a10845018001074000340803610982e050581c40c082152500b02c07081c1c9104440202110b50007600342601c0e00e0112004680d8070341503882d0a2408040e42d54010222401400018041d504040240220360403020140141290b46040000d0706409200f0181000001410080040e41c821040300c68213200d1116000c00c1140040b445250b50308030105078903105074205000d401e1000900401850740740074070f0140281420300c1e107a0400380c0281c240442c0980c174100040c24000c01510b460011030b01c2003c00400014890140031580c0300c40c1a9494005030080c0b0342a21350724100403c0714403848043c8000100e40c0e202d00201e2000300d01c29082c240030705050070b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 581868282 1250 581867032 581867053
    0x1f09062306122107030c050f070503010c0c12050309211b0a0c0506130e0a14090d08060906060403080304050705010206011203091809020a030c03050d032903 69
    0x60318080c03440344402210001900e0150140242c5800080b90100198002800c1c19442080d0407024882c44802a100b103413642c2c1c03079203000d451180c03040c080201140a8480488804400041c0e888100c1f0780440007400701030101181940d00d280c59007005130038092500342c0486c41b517025400842d0060b071003208591081400413010f01c440d010200f404030320800e0010391940041c00c120440d15080d0030746d101401c1050305a81e030b9040c04513124401c1d14021080440c0325651010390928681c0148500070302c1c83c0c00c6140c107140c044000e00c0080da00c5008507405c04045400d440c00000ca0b40721080c3c0d59100c48004e074540c1c00411154010003131910b03900120410022000070700c041d01850060f44190000c244a5040100182c141038058000d5511544091150300202e0341c401307800022150300002c500e010150020660380900f0b001d400207034204200c840c00000b086004910f10084900450a841031114402d5003102a60401ca100b0070708154000184048255450900880ca0a00404903400d10310b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 581869532 1250 581868282 581868311
    0x1a040302060c0d0e1e010c03030e15040b1e0c1606020a110607030209150d11070c0905060306061008070e04061412030921070f0f050f031f0906 63
    0x400c1c420710b036903041070110750000ca80110714000204000c40305012508040700c0ca045c28180c113488000d0402a012070314000b1b06000c0e50100498410041c142d40c682540c80d401c88086200c1a2012a601030200000540801860701280c001da5a0510494107503201c480400e016900030740b403203a0318060100c629000240d1030f403000700080251a01c0f20344003500f8854400d401d10000401c0e0300103042c01007080e40d1b0160b4403214202821030224500c0c640f50001d02920400a1910410142450744005035440c103001ca84d0481200b1925603401c140800c1c1e03600810306d030700d07030b0010f6404c140c00500b0011800c0001e405805c106600070038070718040d16080080c100040c10307112954010480c105500e410f80c50a410311008000b0441401c500a524128001000c900704248680c200078405a10700310700c0e4440030b002c0c03120758000c0455540524495440b40074040748984144034041c4209018040200d040c00d0115103042058404441712120b00104030f040c00c090424601d00315000c035500c2c00c00203446403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 581870782 1250 581869532 581869537
    0x801050108090322080c0909031e0d06080319030c0f0c110a03120e0d0c03080f0403060f0605040e0d09060513030501090f051207050c1509030312041b0806011a04030206 74
    0x900c140000313810614180c0c280c2e0615100e940058080c0b0f545d9030801000b118004102c0700d418440c5804160401c0c040d040399140b5001720060841403908010f00000d015000102603c1c030000884540d03420308070444010f404550301030713983e400071035004081041001c1c001d840000c90300b0f010300a40880e40000c01c00180c0c00284581007280c000300081e65405035030f42d02015980b00400c060f5071190301c464503900d0310503205a507803000501c1c15000250850102d68120299401580d2211040c0690702a0410010150403039011b682d00a51a054a5040328400014849160705031511030348465814020219060340c080e221042040050f00c5000000440911900c0c1000e03024015100e1225051720340181040b03001c200400d5242402d01800c000b1500c003064030345004800312502c600090884a40540720300918401d1903040c0000305000c0441c00103508810f110710f1150306076080e01581c1c4038102030002601c0c012400c42c1c0d0302080c018091075040718440d000004d40088078a040a5030b0798006039407907 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 581872032 1250 581870782 581870827
    0xd0f090f0b011509090b0111030f28050a0e01200a1202030715090c050d0f1202060705161e0c08120a08060f130c0f1e08010501080903 59
    0xe4516086410300a21481e0107014060051154400000a04008084454500506880654a818070100c9138001c5c0d002c504038448680540f512501410420040c540141000f2500c101c0b1080c00d1011420507402010380d8005181c0380c1c2402c4c8240c403003081b02d0010241071103a051204404e4614040100031896601140200c001003005c8105840d0401212800c1c40760001954814008800026510607411020b4403138a840020340c16a0703402c0c1403200c22390302c2d80701d0340e082403d0950010030300400c1989035824074056082d481c110080781c1d600320380d03602e804c07980d0f5000210103000c9004198107205141042034012054005507000308450f0400080c0c8104049034403144902042290701000e1110700882407104000e5070130b18540d8140980510001080b141c450341d1150218095599a100c0c0c24801c0c8460860030820014410009030800501c020309202040d580c5280c540c0d10800c0c074802e010000e11a80e207200c10399107484015103000310007034002c42d070f140400d201914012215401d1260070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 581873282 1250 581872032 581872043
    0x50f04200603191d0c0a050a050d02190e510102010609020a02070f0f0503060c09010216060306080111030c250f030c02120109051c05090414040c05030307030c03050d0f09 75
    0x211751003030040012104103a0b221500a403141d0104024503518600c1d450034058041d10361621a00c4041d600d0801090a44c1000c60340640940030700c64039401c1201c41c0e40111414185586500c0c084911404070085110018200e449212981034107201543c000c4480b2080103000101c0c5d80d6031076221a0007aa001206545c0040e1f03c40c1e18104810305c510401e00c8001c0400f0304043c00b1060070f28001c03d0321408010080d81c000c40b00050010703004d91003003200181940c0402104856251540401005000c140c41032404135820100054007100d0381d030f0100c03806110b4008003186005211480030381401d403d14050b003202c024012941c4040b820916034004e01c130340b00f80e8822264000301d10400030851506a072800c00f0b42e00d4400440009900002e1841c0d0f110345100076041c1c214034452084400d48100c0102c1d43d009814003482080e00949002c556000320b101e0408040c900d40c640d400e2664034018060064009440c0c0000140841d000e24004c2c0a180c14260001c00e9815012081c14151030122008890 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 581874532 1250 581873282 581873293
    0x1b042d05060a0e01060503070c0c05060a03140604020c0c1002070f03060605030d11030a082d0a05090a0203060a02090a0e0702030c12030631050f04200603191d 70
    0x415150402c0307000040d00066020880c01c2d41095070081550100600c444184542131401c0002d212003c5050001400020304050f41c1d0100d581c0020080d0407445111644a40c4c0c440c0072440c00d01c4c0c54003d0790888044031f0014448000c0301d40400550000b40f0214001b58010200089034041070340d580c0402640c0103c2d00419070600d0030003854901084da502c80390810140c00c501054521010003202c00008003444c2021041d207910821500201c500c141d8402d840782c2945400c1a001500d180142c49954200303010441d07561004c15560700d514080c0e40c02507042e00140c0021b03210144980c041c041902c00a00041100c0742c8440d0011136241e82681c072103015071f101283d00e0400c40f0080291101000340d000c45a802c60030044046110600b12440c3c80d40000c034048544c2d03905c030303003027002c8034200c819022414842428003800480d080d050a45040c0d079607000c20044003079010342000d400b0305460400b03130085145554222950142c4142c50a052141c6d544800307080304e100d07205140030010020700501070301 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 581875782 1250 581874532 581874541
    0x408130f060906050405060f21090d08010803120c0c1006091e06030b071103131412030432030a0501050a140c03070503370e1b042d05 59
    0x100307401c40a51140c0c0030084c04000a000a0311a0400e4450003030359001141d07240d0208a8020351114408414089408843c2e8100900318400040e00010744415480c0c4441070f980706d10600303489100e0540844081c1c80c40201145900350240020403070380c0c002100f42c4500c182038020358000c0e580346034080002c143e11003000c0710011820058410b600d902c507030000c0202525658a8500d003440091144050013142e1513860110082401194060001c11031f07106c0050303449060b080030840b28a0301040c05548250726100c81624000300b224192219071560381d280d980980c40c8404010442c0340d141300e80005e450031001c4661000c07c428161180b14000110380b80c90300f0041c0504070740d514006a80800c00705c1c010300920252500480360850018603026640e6580c3c10707003402d941614041d40031601c407840c50301c602d682a410072001c0c66158078480281302c84079a6008451380d90b9005c1c0003540c407420304010f10800d82c0c40c00d40d000640c2d118080382440301842c0070b400c1380301020301141c082001060b200c00820 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 581877032 1250 581875782 581875787
    0x9080d02030a0f0c110f0f040f06090612030207030609020a08100e16050604090507090e09060108010f0501051c0312060807080106050603070c110427020102010c1409090408130f06 79
    0x20110480b20300d0b0400c1303880310035140c101003e110107003031900411142c030014915442c0c1c580003201000002c1e10034040c2a031075032400b00090084d4811041424940140812540c400a200a0f4810b401d58003c0c046a811626014018402600102d074030100d01a00000e4000c810b102241d0a1011ba510020341c52019214003420b044c8a070001d42c4240b06144001c0c02595222800c0e14142d9a09060025048c0d445d200705aa8101864020302c0d00d40018501f00711041100080342c506a43c540d100900148248104a41c2034070360a0142a0b4000d4502800600c07900e1458901c0710420300900d0800075802c4860b48140880301550440a00e58214800174030810b04c090069000501007950564a540740a00d0000e0107103170040001404c01d08a00c0300d0040541d03440d08246c031700d1311502d201e140d0341126104100c070903080803c0c030890140d42401a95850300d400354001801070b002903000680360180a004000321044018021214203200b4050345030355123a10064900603080b02d00b2641101400e05002 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 581878282 1250 581877032 581877047
    0x60b061e0a082512150b0c0d08060d020603060f040507020a110a0e1603060305160e10080303180f06090a020117090a080913110310050402040803030606070309080d02030a 75
    0x40065007001c5004003088005060012044956181065900c0307203c01c3e843e40500841c0172031507003000b200c450100d1081c08180082104502d02d000f00c40346004000300a48801c10b0440d515a80003428924040141c01c018006592003c00245088499900c030800034085500036100440180d00071620042000103000546505545c101c603a000018a041c544000c144801810118a01c01651406100e40c0c001c1e00900007460f44201694001d0320b4850740024803040300d120b00325158070041e010400c1d01981211400540700980040c40c40c595884e11440040c01c2400b585d00f10510030380e07030080700c0c090003408014090340c4520050041d040013400010a02685480c04109581c4200240002000006410210140e2004d1495290000c0400044190880700c0d0400d05583c1400345c1410075441d500c0c001c40c410482009040e0354035444006000c128025402400c1466100b000441d4281c98181c000c0e0040d80c0c42450f0003ca0a2b4903000843e00b04411100e000000d40e2012074210680780d0030000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 581879532 1250 581878282 581878291
    0xc020c0102010b06090d02012309092526091c05030708013507030303060906030215030c04050a090203070219050c011d041805010b01030612060b061e0a08 68
    0xc3c00807a844000080d218032450101500c500c168004640459000781034145208000c164110b600b00501c1024803c01d83c0542e00c460f01c582c190b400000c00c0f00c205480d20342e01113a0003210041f0300d40c1c072001701a24868011651440c003d410b03454200f165030921f010052003100404050415040c4e20281d04d820003000c0a114000e02405004200301107034896905030445038216250000d01c025031000f04244002d81c0000f940b55200301c02ca80010003800210441100c1c0309a5080182c142e4901500003200c3c070703a000c003d500c010046909154911104095500019110a0945802d13510400140c0440e20b41d1302c02107070150040b080150342e41d01484103040c0440f0740d4058103003800503a603600381c484c01c41614480c1404500700b070f5501050910300c0340d0050000060000c0112012140ca0000c4451122108031b98541c00c0c4200c1448551107402071400f00c0e00c003103645903500c0300a0390710900a00300c00f2440a400c104107104d081410503038010100303030b880801140e45545055000008164400041c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 581880782 1250 581879532 581879537
    0xa0609080303040b070e060406180e1e0a020d020304240c14210405070e06190501030914070605121f03150e060f0f0f0c030604180b041208010f080712020613090c020c01 74
    0x400c00484d8105950943d0303260cc602c0a00c03074015500c045002c002070080340c0b038542c5614404020071041105151050b0210046050780c01102201403003844140c41d01f0151f41000601d00740d9143c080b00200304003800b1551b03104103810145641040c103080320400308490503940c41d40320541c10410305a0882d030454001d034003518403c400f0f84c1e0185000800a00300c0c8622030400d942d0707013040c1041c08003061100c44261002006e0318030450b61104001c201d50811031400c420480110007040c171008540700c1c01c3c91401c081c240c15054041c91501d420352002d40c00c000b501d010036102d081d06071400d00140440c170b2003980084610503060901c1164280810402040700381e806800340140041d0b01d24074025a075000070101ca0110743d00000c082c00e00551100244003d10080c4004240700402c0300c41c4c05c42c8121a52243e40e4000769a98400010721400c5ea01c0c0300b02c103001d400506041c04a4100c2903001200c05001030912450711003035140b113001c10314180c0e00500240799104400b480380c61303060118080c10b03c2c3c00d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 581882032 1250 581880782 581880809
    0xe031902030717030a24051302070f1b150206010f050108090a02040510030501020c0f0c090708070c031b140d180e070912050a020a0609080303040b070e06040618 71
    0x9503200100d05142e0803090420060102c0000d00b1701c501504204595115001480300c1c1141d00c0034000e40d55003a034080c3d00d200d0070111016000050f441d1007695042504400c52a640300c9482e11000d000c001100b00714180040240c0d004210f4100709064145240c105a00402056240002c103014031603a64002c6410070802c00284002c502000401d103102c0f82d0111000a1591176030b00d00440151095880200654008100781c03030304070f0700031a151518001c80c005542c3d0200c1d034401040000706c400c55140c0046408200441c2489208000520a05109040584110700c10082c1c1d0540009000340031200c00807013541c1840126018801050043c409042c544008100e42030150386124260084c2060100ca000000300d1451052400ca0004c1420b5481010b81c3e100c40c1c2000307034484200050a90045116070303c005040d51180701e540d0104c1b09018051401c50b2075940c0c811200d03c3c00078001004218900515103035a6465038003c00041c4270031385980700860302691120040b50140d5100c500c0c802500c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 581883282 1250 581882032 581882047
    0x20a020a14210a020d080925170111040608311401020307090b0f1201030311010c05030609061309080310090e0c010512042a0501020c040c05180307090e03190203 71
    0x114901800850b0600300306e580d40b00c90a01c0d00c3d14a030344010200b4101d800c02c8810300c510702c0c9650b104c1070316101e107503c4481d4154040801e003614000381602101100422003000224401ca85481c1c1040280c00341e4403041c007024000034005034484103001c02560944a8800400504c01e24100001d49590025030540c0380002000d449040a4419030400050000c2c0e03445810890744200c0303160071116240c144503540c490800618500604040342e443e50702c1c009140781010f0040c4196440303800010032603007041c1e44a0b014071580d0241045401a442d40342e80084000590000148d0300c9610409404080c0519000070801900d03030311411000c154011005803000781c0d070300c1803c81d049000d00f515603c029854502d04004806250502e00860024070341210104503c82030384502190001d038210341c14144a601004102c5000c00f4180000c5041049603401d070b04101851081c900900800703440710f040d50749646009031036003101e403441c0c00c2d007000890001c140031281c0c0344110301d00980300540c01c0001c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 581884532 1250 581883282 581883287
    0x2030a0221310602040b0a1404030804090f020c0a08130611031e0d020c03040905160c110a08030f03010e010b270a180f050c0f04030204020a020a14210a 67
    0x140e03098600000e02d0509001401c641802c00850080b82d40200c0c00c540d1160399086110403604050003c200040303813144c8040c0d03030360b106c40107035403d80c1d03000040c0034a05454031400720020107014120540c210340074451558601c03001e0001c0341d610750052020715618030b40319170b24050708d204030f40000b030500604002408507002d00009850321111280500c0b41d4040c00c0e10188411809120000c0710041d000250841550102001600c111101e5a00601443d00c4e0401d01c02501481c12007050f000900901407080071500000014818074400f8112241c11908c40d0740c40c50440d8400c11031407a8410000004115a0740d900e50214010400b4596113405e011002d40084020040900c2058503542420302c07081440e82c55640c0c0c0d030010050240c80c416414104070b808000740011020b0705014525010005103003c02c070305c3c00c4036003a41d03500510074a440e0459003040004d4100009030005c501c600b4003c600082d007030000b0307107800000003401070613001d40c80d140c620200907400e546603070108170500080d0540341c1c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 581885782 1250 581884532 581884561
    0x120609090a1709030304030c1d073f091b090e061f0b1b070501090501020c0103050a140103050f010501090b1305070e03010617010f0212131502030a0221 67
    0x1801d0000c2d15944041400000341366018503000036082c080c891000050742d400110400713042c50f140300c0541d00302d83e6401da002d85400700201c11103100010f900c1a5440d541049170b100700c41c01180b40c8000c2592580c8040713603c0c122041e26404880c00000d001420301446240d26035100103080701041800085a6181d20a841c4c0001030b040404032030081c410b404052100e0514a4007808021050035203501e00c00031704940b0802d4560880358503018810000c280c80d4032070028482640d0041e0000c01810002c00c0045000302401024840780c255507610241041c000122028025400b0700c2c0142000800603040d1421100c042e4003d40007103242226400312074031880c4081c0201e000c22040050181d58500e01554040d00340c044440c4d05500c0c2c12400304d1140c0050f500103c070020300100810001643d003a201c000c901c24801c120000320101c1c40000d100f1001c2ca100342d1350780c900c0b0310008112014880c220200ba030b04162450901150045000d881d08928140c110540c0110700c0c60043d150b0600b849041e4401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 581887032 1250 581885782 581885813
    0x40b030a0f08070204290906031903030e0601091e020313021c02090a0204080c010c05030d0c09120b1608040b010501080601050c03030108010518060c0405130f02120609090a 76
    0x710520500180300d034031410340d910703590040c04c14840040c2c250f440894000450819030715040c000e0f03480c5d2030541440d0350704504c87c0501500510100c0081c007042407462400b02411400c1540b152100188104184070039402808640d00109a070710f49650100b10141200f942000301920500c20044d548071101d400721441e60301540c03507030366102e80c102c2e2075a01418200f40c045d40004031f050612400e0407031980244103c4076034000340c40303100d01c10300c0c01149d0019501c0000b40a82d4018002030300040c0761984440b0075800c05003070102d401d9a440508000b08110030006885104000701086810b09840403075414400b01480e00d01c81600d8607035180988260b045c002d007810011003500242269010720102e401c0f00c4019030031030703440b581c0d45c12225000e80801c94030b0b404940d00210340c130011404000341140c02081d10005841c140b034204401d2000300b5005a0201e0318090301c0d0024082e2010003480107003000b00030a4150700301d0f450601c080c0070803040050b040b003005520507401c00021a81081407090701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 581888282 1250 581887032 581887043
    0x6011206060e0f06041a0d080a0309150603060f050106050a0c0302010204170c030d0e090a11070b09060a0e0c0d0602210106200106030308060108130501020c0a030905040b030a 77
    0x104a0641080340040010b074112180000c10035052000d151240b0300702d144500402c81d000d02c41d41200410840da8100000142c0b90003a0860b445200060b1880c400f0b440341c85100d00d130010303620149440e41016070000f541e09500c040e5039003c05000b801030301c0c001c1c00780c05a400402400a5450644003d04611507025090700b003020a003407080405200f901214020400010303103110054032000d0362070719602c070646424840d10542c0400384410b80110040100c0c0c04004000306560ba440041010103420211106406424100300c40030012b0740c00308269001e480350300014403940c50541034103021a0039828406440d41d1003c2c00d0882c440d40d4031407140a0b445d90000002d601e41a1705207860301185802c22010060418060021680541c00040d0b036035000e0140e81403162130010241514201c42050001500048900002400550260b4621500180107014802d003102c502d403643c90884c0c200c1200d840098021205840505901c1500380018010455040080756001400280d40c2d03140c0400c010300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 581889532 1250 581888282 581888309
    0x3070b040b0d0e0f031c050c030c0a111203151906030b03010f0e0c2d1203070f060b030705030f2508011509050a052406040f0b0901090b0c0601 63
    0x342e03540d2904a038426210300f400300c2e0031079142d50070000d840303801540c0c1244c280e4180001e10069a0001e00402c0c1c090350100c0c0d20580f0310f03142c0003542d42040d030200c641d840920444a405c008403400400a01030f081960b2144d203520b9040c0702110100c020780800b1030342e21031400c10390040c00e0304140c00541d05c121915820001001611000840d0152440c0450141400d00c0c01248100c640800714216035000012180c92801e004800f4a80954416800c0300e00d07403200c407181000210307050888081520403d000b08490070300d200d41c2e403401c03a190310106007218165194803e8200c5810100103001c0640422405402c0714000f890145640e1000f070710b00314150860800d6081041c8006007007c001038139800009114204065007240c009004900c1826140b902e00300014000003498410b8600401d10070030703c0f490072005410140d041c1c444c0340310313416449201000002000203070415001c004040c2c510b18280c44046203030015100951681c0041202d41c000c01c5201200c0c01d0102d502ea040d142d0440004d007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 581890782 1250 581889532 581889547
    0x6030203091f060e0a050106020c010c0c0302010806060d05240411031f030b09150a0e0d0e04060801020a170606070c0303050319020406020109050c0316050f0f06040b030a0b03070b040b 81
    0x1c020b070a05501811000001030117000d129070311074000905885c403e408a07540e0007541801180c034400b8400d0080d01c5001c403140c00740019845030346555008040181f6184c00c152108001004444003501c883c005249607400709c892024014a0100003e00b0442c0e04012413640c100082d1064400100f0040d0f011015040c03c0382e40840d020246400795811500c152014940039491035990440c9410091801a0000014004105900910340016284005000144000030707003501d00d444440152540561581030200e10250248081c00c1c1e5800903613240c00c1007000c0e2414400c10940302903ca1030207454100b00c18400f0550304100d01c0116030f818500181d83e5900e180e0504207038502040703242c1e00107000280c00181164150860940b07903008000b511848218a000c1540c1c036400e9503040d26003596880343c100050b00e08003a004105400c0502051054003844000448650068110412110002c814003c00d03003038901c40d03140104402d500802c0c0041c18281302c5003031401540f080d00c115040000b20704 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 581892032 1250 581890782 581890843
    0x601050a050f070f1b0608100302061903110d0f1107110d06020c010f1b0f120905010f0507210203061c050a0f0c170c0f01030e15011d010603020309 65
    0x1100d11a400c4108080c04840d5a868250340036114481d07100002c40003400702e0230001d589500001201ea000309124a01840c4561500c41e1241035400b107070505a40701030088901c0019801001c0d181c19900c00050038207000150041250098007030340d40001814001c5100240030300c45070646d501003c035941114082c25140c2600031344540b401e13661555003068071404541d40c05821010008843e000000700c000030206084030b04044600034070001130301e440701b4015005529841400040d0040d000820031007200e018a07000da880a036100c3c400140181002c0d2100300740400c212003413000300041540356042400009515406501442244145d801c1a0004100c003c202d0380d042254404041410840541841c440c0c4241c5441103418011039034420f034180300300c04199000c184000800590014a1400045006180075000c181a521030304114103e290004e1055900030968103d551b45d00c10712030100081c501d17070182d0000d0203140c0180148144080b0100d03040300018000b5480303102132420304000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 581893282 1250 581892032 581892053
    0x307020f0f070e06150f131d0126120c0f07033f08011502010b0306010308030c0708030f0601120b01021e03040f0806150307050907050d1b020102070b0601050a050f07 73
    0x1c070580b1002882d040b40b6000f0401504010005844002c80c490743c4034440d0230541a0150354280e802c4403d001445204404900000c01451a001c5115003801220402d480c002c10940c07411500280400d03102600503040060008000600002c0c0030298074541e258040046004250240d119050150b00b0007115503a62030710b2006664003000181107041c40025200340740030700400070715650001c107000c9401c0c01405680c0e00c0503c05401011245c2c42d507100c0c182590000790070610885010012200458000300245019650549420416083c0074002602e0240118240300706542450010f80150b0b1300410000707444040d40016004c004000c0c0c8845007103200303540112803104503903c00800c0f017040000300640728003483d050310b000481c2000c040559400940c0300d019800061140000c492074031820241c0f1750a000100c0205208170300041c034105060f450204440143c3d8086040c800703100c000c83c5007580028007824100c0c82c00340703000e07001415032003044000340c6500d100288100800161030716 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 581894532 1250 581893282 581893309
    0x1b011d151803070213020d0f0b10030e030d151509031109090a02030102180406142b0209150108070e0a2705010608041407180903021609020307020f0f070e06 69
    0x100c0d0a01d03080310b00d0b44402504845000100c03940341208480d9076523124822100318402c000c1002d126600f2001c011006810055403500041c0400e2000c51003440d13040c02042c03441c12003121400c0002c1e08281144580040c40c0c0c0010b01007182415041010034001b01492403606001d88a02c0041d41d1000003480c649060020025003642c030000d80c254a44844181d47d079210103048400748101551241110070b40c3c43d568a895501c42081d45032a0300c85280d01d40c55404064600c07030380c1c141061076600010f800803011200ca000844424040202c550380c44020b20b60f1050072070410015125107000442d50990482c01800f60052100d81003802c040b400181242c6c0041103240c00740129a140c4034028040441902c08503650111034070101c5c10a1800b10b40307a41a640100100303264a00d8401b03010000d85086807050701507000e51000c1d56001da0030b000c0100701030700300180e000d6034a00707104800a1500c89031000c9400590000c00404405060200d108412102504082c01d1551500380005a54040405 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 581895782 1250 581894532 581894539
    0x20d0203070305030c010b0f0609091e010603020d0c030921020a05190c0524091f030c0908011a040e01020c06190605090f0402151b011d1518030702 65
    0x903000081090020080c945c180c0f0380d5000b4001e500d60700d8140040ca0455600082c0d02000a102c0b801940c02e1600701190320024044040760403074220b45640b840c50000b13030131907000a9000100006419114010254143c0030b41c50100410b0000d0b803240c620107121000e06134800b049200384189800d05c204013140d46280c01105846502e404065130f15281c0d03200f0030084601c0d110001c000500d6140505091300c40300c90030f80480700c2c001c4c240b11074241c4d1a803005800c1d503800248104486904802c503041c6051390201a240020b9400d03185901a0200740182d100790303610303814090140f02428200d030b030001180d82c0c103a82c0070ad03d007003e10407500c0c003a000d14282429030b4440d410801c016211904200100c1c1c441211081140316110003e02c841c801e0222014030107055410007040040c00e1040628048043c80c0c07000301d0409419080b00c105401c450f0940703c055a440d0a00b0410410100d421600541c070008001d12507107070050740c80f0f2a0224000c1150881039226017031008000c030300303208699000758000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 581897032 1250 581895782 581895793
    0x4080c091b28020706080c07080d09060c03110a0f080a0209040c08161b1410050c040801110306150d0b0a090912030903140a0302130e04050d0201090804060c020d0203 73
    0x11200119503000b0700d19080c0c00b058006000071046002040d04001c0d40d41c66075035500c9981e51818804000d6101c00b00c1180e00c0c20007004012003401481c4941003080340b003203001003902550402d00905642d2244402446910f0811035802020f4000c800d00307440050701d080286840e030b0307071070340d00d600034000c0101d0260000e05010212407950382c8040030a22070030200b400110003070020075045030f118400f4031510994548121500000c40d80701090400c1c259208021225160030300e0003035406136241a104100103403404107080c00940020b000703600c802049165200d080d0303d41140011207401e1200012005800001a0140e22a40c1c54004041d40b11000c5e120b445601e982d12206002000070200982d0181d40096005040078232a028500000d0b816648092610280c0b04514a0342e50010040000f031550030050907089440e00d5551400420902e9105d0a0601e46402c115040518036170285086914104032140012030050a842c159122407404920000c070341c0c070201d241c2c40443d80000e503141c8100e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 581898282 1250 581897032 581897047
    0x1090f06230126040227190905100e010b0301020c0d08090715020607030e061b18090a0c0207080312010e1b160302070501051c1a0607030c061104080c091b 68
    0x85607240b074040c4d8030a0380d90f42d240c040c0c400114050103054102c50b041e07006000e00481c4031504580b8110051140b41400010070a1f03007669450710f4184100101c02c50320f500c4032205004244c0a00c11400c82080550080d4503081080c3c04c050340303490794200c800080c0160480130528082c02001040701802201d00031390110414400c0185d40d6490071103040c0006400e140c4d04030005400404c810380580c1c901c030700c0400b8030b68030403038004650740040c030801122090902c805650b90ba118010f003401a40314443c0016012042240242010501d0704032041c00c2e401000728000c683c1581060781e0450315a00100c42141c1c81e40041417103110b0a80748451460003001c01c0d0014000108016403400314400d40855290558460054034103002e5003103520000664448404034030030158100da107070700c00b240b010b8420001840c00000c03000d030000103040d00090b900c801031500700480752142000d280c0d41c8100301c03410705203444a19560f81e84072420951c0603800394004200f01e50042d01100121203480100d00707455541c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 581899532 1250 581898282 581898347
    0x4110c1203041b05090a0c020f12040810020f0d022805120f060f0d02040e070803030f060406240c170915071112030c010501060801090f062301 63
    0x1c1a601a6103400541041c03504140048180008a901c040c3c29454950b81e880540c01c002d00005040c0030035030240614640107100d0600560101200c0350800d6900c1314242842c192400c0002e0b010048003603c10004800040700440503903900c2c4c40c0c41c10015a442c94030201801d841440d00410114140c1c80d0303014500c030950024081c0c4841a0941c0490380c0c1680c80922441455005440e040d0700280384c000c418045003050042501c0c1c5a00141020411400c0100072500d1710406603c40702d030503007001c02407028481190303890f82d8100c20100c1e8148400c03428400503d03403038402105e2030b8142c0501c0560b00c2c03400500a0701501000c41c0c009600c1103041d90451400010703541b158484500ca42103144400400c6950b48041d2084160080840864a29840103002010890034800712480c0700c00d02c40c0240d281003d02809020741090307a1240c18a500d400c580c0016581ea10900201c1c0b1307800c298040c40406041400384400d8185201405503441c154801a00c800e0640d01c8201c00108001150800fa00c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 581900782 1250 581899532 581899537
    0x7030f030909020f0d0e0703020a09020d022106010f0905030709091a0c0c010f1406040207050f0109050c09010b2127010209150c0309060d022206090b0c0c04110c12 72
    0x20000c5018403103d000320000c00e0710780c2c965000085d440502030b03208bc010110b02c0da000d07012175500c0030401490140b140f410b0344004044ca0160300740303284450080140c1d95a00c00c40d540001c607110f0a00c0154141454006a1190002d018402c1d18981e6440b00c030052201217003680c541c4815582e0541e00c5400c0c0300b01e0352601d03640000403c40142d0b080c21810450850740e4426017001101036501858191200b10800c0b01942c8840b40c2500c59120b07820112543e42002c0c030601c04914803600007052a580c400c810300c000c80405901a14030740409102c260408114001e03003da8154550805001541d1074034001090302494606903000c22011441031201c070b0170158002c0141d8802184c405180032800300d81401c0720700c0f4101d100512608184951441400c11a000d00708280c1c0c3c000c0003508107200400e43d08409800c074910a01e030510300e031100708280e43d008206400502004d01500e840d01d00c80440d0b4603940c0c1c2d48851030b0760190b41c0e100e8007180004003040696901341e8561064038034981c45691303081101e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 581902032 1250 581900782 581900797
    0xe0a02030105090c0105071227030b0708010312030b1203040b0d110304030c060509100203090c040c020c03030a0c05101b020607090f090b010903051f050a020306010207030f030909020f 81
    0x2507103044045007840ca0001a11398052805035900d0b031a0030342d1541d9503098104010000001c2c05820031183c06095402c2844051001c009071405501c03d00d18145508030210280400061100c03500051000c0b510450001c00028402d0501085618200e0301084420076172000d0301c20340d03010115001c507560b68190010b1041940c03100c0d041c0280c280c60b8242501c54442520300401103100c03604981e0000b441d54105039846166041502d4012440d525144c05036401160208a0f40d017004c1c0e0401651f1400388503441003544940b0003041c90030780e1003010a607a0720541310f1460610400920480400c40104031860142c002568148014804031034403181c01c21414003240003500521000500141c440e008040c101c0310b001d082140c2c00f503d00454040140b00103228035041002d00d10021000c0f03602001455291003038044d4035544d00c01001c001804584000e018090110f00420604c4001d03a400501003003940e4005100350441c511514040d500003480b54030203105c860003c141305510991302c1003d030000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 581903282 1250 581902032 581902039
    0x9030207090b060a1101020d0f0c1805092a0a030204030c1202180a020714060118091a060d0b01091e1e020d180c051c05061f090e0a02 59
    0x2040c0c4030003103079069a40e0102e15580154040c080d6003c114400e0b48803205000840c2c00052800c20710b042c481003510252503141504585a1425005440d40240141410004100c0b050506420140010b080e1400980010001c550a2506414200c28483c00001145041465550f108400300e006801b9400610050b02c02e00c0240c1c60010700d0030700341695000001e40c0240224031903100700505c1c0040c81d41c080c003160340b00390342402a00005444240c505803410421001040903600d815080c0050b94083d09291900c3c50030815403000203408106000326003a620051011076544075008501c4038030550b2030150070850b04d80c000090740e54060740210400040c140d00b880b20000c00c143c008040d41c00c0c24003a0380a41090b5001c8d99101080303940500303000d0100d01000324109642c2c40a07100485d01c40c0c10250b60b040e140d09002c102a240c50303804000e0f10071240611041d100b8580c2c94094540b03c0003001142440700c124801d0701d41d03c00403403146000c2e11002e07008101001c508071803d42e4804102004a00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 581904532 1250 581903282 581903293
    0x40b0f07020f030a0c14031204170723120f030708060108040b070819110912010c0f0c03050405060c01021801020304080717031315020c06070b0604020315040c0201090302 75
    0x8030948003103008403801c0c1c56800154070341511410111030000c01ca18054519010011402c00c0054040c801080f2250400003219001d080c03608080003801e181d4280c0d00c10f0110104200c0c000035079050403030051101c5108000031052120300041e07081a250000414402c90700041d0b000b03181007001e015600400345691410341c0790341c070140150781488041d240900340200480010f0034841c49070150301d0b40017243c00c03100d0018060b4840c201d030694036510f00c10070f404d0170081021030342c038201450b0480315034003080700131302c0009000c41c0054800c648a8289008001214000c002410300840031180200b402900309551000e070024807500039000303202e01604120041c400a0340c95880001503409542090001e09030051a0003200d0344407601c44009800a40800d00c01c80109402d0000391500034842010320650b040030840b4000c1c1004103807401184141000e01001c1c001c15000d410440e403004094400580d02c1c2c4841030303090076a00488030502e500070700388041d5182032079040d0404a4030510a808482 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 581905782 1250 581904532 581904541
    0x709320306040f151109040e1e1015030b0403050a0504031e02010f092411010c0306080d05070309090506010507050f1e010501141009082e052503060e040b0f 69
    0x1c2c192111003010178001c035414041200c840c901540400664141c0c03501710340c150403203d1a850700c8050390300c20704c8000d41c104404d8102112142c2c0181c009500c40c40800d20011400d65540481d043c030040c0000d010844045417003401180514200c030080d64000550541e18000d0904003205040703220400c0f0f000965403892401e14600a0a0312420780303400e08124502850480d02d103841452680347d0400811425480340500d0400c284541801011207903404500e56050882070361405030b00304503100c200601040080c001c640d201c087c503803d942d03680b0f070003045980356400102d0b801d0040b4480502039001d515110502035100081c151011040301c800441c00f0200114010300304c8000f44242004442255280c0c4094030386078424504c14403090410142850300c3d40c03070f0180303415645c0010107281000c0b4000545c4406100d59903000e040c03801035040c042c2c1c0c50100741403015200380725500f621a00140e0342d01b1071824000e4101c1e130058a0f622900c0350040c1f8041c108101c20f440c040e80c1420f0b4030303e00c0c0c1c004503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 581907032 1250 581905782 581905823
    0x1206020a1407020f1e0a0f0303030b0303131e17070f05031b0d020406030b070201020706181e03120e070f121e0c030204230709320306040f 61
    0x342c003019002000b13800c194011000b8026039442c2d07009410501000c40d01c400701244c1d00e102d800406001c4610329900168150b00d8058110f03401c036804948264018090004c2d5180791038036240503505111846691a08000341421075080280c00420303584c2001600c01400345070000320803080b2400440c001c0c41c80c1c0d03501c00a054880b450300c02000361a0060302241440303400c0480507040352303520203440004c03c140d8035121078207000015100080140d40000d50001071201500401006e40d2040401c1c0600f40712694490310400340c6541e0700303c0302ea4141c0d510501498046d40e03d110380c480d80d040c800d100180d1522007540d140c1041d8010305c0e40130f100f0450301148040c150509100440e42c44103207141c48041000703490601086494003242d885042010100c0183c8640c010881c01428910f400c40c43c2d03241203050449486401040c0d1001c1060000c010007031505030300c1815010341030f0307100e10541410a90400008890041c00d015425105e01000d000c00c02c908200655580d9006035081d417152030a00c54034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 581908282 1250 581907032 581907037
    0x20c33060a181a270c091c0609020402040f030b0c0a05041208040f03110f0d0308160302070519020114030705030103030e0f100e030c0a121b1206020a14 67
    0x303141d91601d510007198011500703940580c41c040c8180f00c5425000c0004400100408800700d00364120070000515100040c03445420550010200c1030054100b2002c100842c60100e081c0301c1c8070340506001c0c4218404e208050b44003d000e641c010300103540d56601d03440708450000f014072040755005604000660452074036000e80300000c0c2940d540354076103460070840c0100300d46609029600e0520420001a0f09020b50461000451240c3c002502e0038008400b001110406200d03000d00030700c442014040060352156400d0350102c031a1a05801c07400c42204128000e0050010007441e038814040108900c8400d8022f01100d180300760382e124141010028003012070f00040e0b0341c50001c10018001400000c1c019409100a40c0014000c0d40318000d1500010721440c0780c224454001c5440345002c03012a0600f4414213211081c181c07400301443e880d0207a103083d0490200070180103005070fa0140c2807a0340e040e0903104010300c0a070701103501c0d0388010300304034000358842d00c0d00001003030104070303d8910320200d10306 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 581909532 1250 581908282 581908289
    0xc09040507030f020111032d0a090b0a0c0812010503010513030f05030406090803280908070f0206091807020606010e0d020d060b03030f19020102031009020c33060a 72
    0x40e01e580361035642d40b11070700031071580c0403414001448030352029868204050401c4849007400440a0341403100e0424201901805d80c0709041c0003005041e20886c2c1043c040002ca4400854182c0d40d02d03003050003202c03c600d070040020900b00000520102a4000109460680e00308500800064840d1100c44010010482d0010007040640c0d000041440c0590050359100740900710104005141d80d07030350002540120340d00928205c0c106415214181c90140b0b8014070ba24500082010080b5030b218a84c8074008d80700020b080f06001e201c4a000c5480b052b080e00c0d8904800341a880c0f4400080e880094071401c102c81190043c441d06000980640c40341144183c01071002d41000060403580c2c080c0284100048415500541c45881c08051514104014007100d17204030b2016446514080803014501c40d21030880c021a03006005002c0c132420411010003c44400400059640c101045020304010030201178841c40501c56004100355a1420302e0400d1031011025842d07420350301e00d810480058003900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 581910782 1250 581909532 581909543
    0xb090a1803082502010e0f0f0309060c0a0b09031206030a0807151b0c03110d210b0301050c0d05070c241d1c0309020d080319060b03090c0904 62
    0x104000c82d004000d000e03000920803030031070240303d48074000b0301c07102100a40100050799140b410295100b4180b02580c1e826921703e0142118580500350542d0344c1c01440145031140400140260403645e00300302007903d143d40045c0740c0940d8a032201c412501e980080b0500070350034101d60001255840c020420106a6904c00f0311941008800d071600daa02548010241c92507036940c240c2003070150201200e0400c620302990715506003040074900200001c0284941d200036500c5403103040034598000e040452070090000f840c3c0c46100c6003010309405088407040d2640c01d540380409000e680300c1d00c080144800d11001c18244981d4541000460b0076404d0284040c016054101c078056100840c0b000d20340b01e840d80400041942104030010303a1a0b6440f0030f007800c41742e501a05d6034200c61404040000e0b0140300c40d0504002c16880d40e00410041702202600a00001000000600700012080ca000100d4850341d400c00141e038031005011216442500c51610a01c10001d83c01021719116036603030302c00d0341e00c01d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 581912032 1250 581910782 581910821
    0x7120b01060f200c011d030a1403040e01080607090b0711010503060612010b1207020d0504030b0403270f0f1406030a0e030c160b032401030f0905010b090a 68
    0x100840d00464044184820070844904000c6192454200d2403c02100100070f491502803000c005802c0c6000400c0340301d220742140e00c03000d00c90703034004c40e0301038a140e0040700b107a05030002c014501d4294411074004140b0078019500118601c64006003561044d4510b45038084541c0d140d880741d1005000d01803000704807080060324407100f0351140c005143c1241010b041d035400c062207800401100d100076002042500c4002c42e108a039500404044d030740061b03040c0080e0891600d442e80080c007074859070101610ba01c20300c001003810140304030b40800304118036107003d580b02440e901e8680c100c20290b1003810200385440c140401e5012444405104a507041e44418601c155003000380403041d00010950b008040e91145204c40d5680d042c401480b0520000c00508151210a00301d40c0d20014030745c225842c080d6040c030802009601c6035901c00e102040c1103810742c01e0f5500f440012409418140d500300715603820030410f04208101500318200c250b4044420703481640e14110520b00311545001c11903468800c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 581913282 1250 581912032 581912039
    0x42307090f0e010e180f1b040b0604030302120f040e04050a03030e0106050a1a09030703140607080105182809031b030c08161e05010e0f0c12030417030c07120b01 71
    0x5951416400c813038608281c1d01d940b80303424110341c100500b8038595107c034040420740700c2c400d1516100c0d4100010f012203c2c00c4c24a421510025518065541c841154901c0002c10105045c0b807001600c00402c20707208a507049140616060342c031015603400c103e001c28100418403d2a031018002c607000e40e540a0140501e80b0318100690841c103800d07040111006c0800c21201019482c140448405140105164180701d031281c500c0e14a011f500806074009c03c4080f400602c582d13903031344030305c40c080a5034866200c0c440d48410b0070040081800013500070001180e1020b6034010040360700300d9210540a071b11065450140000082031112041c9002400504c00b207100000040c0c58101515200c0d00c0c4403004218140b09590320b034038200a610544c2d16156000540c101001000d00a91060440201c00303044403107a51044950386501d400300c890300c113404c8408441903840e0104251002842c40d28000c40c036280035010010380b26440300340d0072a00c038002c000d00818900f0224245912040d07014181c6130301c1e6840c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 581914532 1250 581913282 581913301
    0xf130303022a061b010608010603140a0b0a05150d03020d20120715020a020102181c02060901030f0f061d0403090303030c05090315101e05042307090f0e010e 69
    0x41021044e50810807601c5603031369002d02c20480645001000080d0442c1542007c00c4e181c4031441a622155100f0881c017000107030805a002d8220b0358212010503940c407921525680ca04000c003443d0f8004040da000e1a0034590700060000350000d46031143d0741560007a40e4081842d681c860041911a40300244a034a66984c400040c203103140a40014000030f4080651003003607a020484200c0142c1d00482c500c0404083e418081040b10320846040c41c000d90f4080002d045284651000381c891417011070650040e0b40207410404070414004410040f07050708043c19070090945025400c01d01e421164503003201484802d919009640548030300c40c60131b00e103560880180101591103020000d0074403001d441034804001121403041d40b02144081460b0007001001e40c0281075000380e08280f6550f032403079101200103c0c25000d64009450224145c031001500b6030b2030501e03c0707444000e008081b40030841c1380b80d440220788054a0580840724815540c444492050840a000d8032082000b4003020440102c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 581915782 1250 581914532 581914537
    0x1d0906120703051603120509030c120f071205010606030216080d18050a0308090d270b13030c12030504060e220c081608010b0f0f130303022a06 63
    0x300c0c890880e040d154980e42c525040c0310f00f01c4104c8110903c1d00000344104680e2038003842800300c880c40c5c89400d2118020000e0b03560008030008601414011106034200203092002001d46c0380348a0464214560300c0540301458400d0325000e440d103510303003c808074809109008071201442c4402e000b50b401109500c0300a401d81c0716080001c540da640360000e898060507001e91844007400350000d40780317124884c18054410b2800a21100d810342001070240002368001c2801c2045040b0388030b81305aa40e0703448454120940c155008000c0d070440c08980c1d00704030001c1d072080005032032040c0c9440c034a0683e00ea00031900c0d0310603000d0080100b40c06000921405100e6601c0180510f4001d09040c8000500410130525004a030400d01c0e007141c88400c01d40310700e50014001e07030b00400c07900ca000014694588008004d0b800c1030141104040d4000340b0320440ca0040001c0c2da051030f0710078540c999210550950740c1074401c4a0300c41100513020301210603d900f94602100200c80070580300710310000000c0010000746a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 581917032 1250 581915782 581915809
    0x50f010504171615021606050f0a030e0a06020927010e15100504050f06120f100b040e04062f09060c1b0f0d05120d09021c031d0906 58
    0x348181080404118110344038203009285130031a030340d00c0c4120103400a0902c40b60401000158101c0c0c07004022955100f01141e8070190041341c603949030030481c1c0085010f0f100c0da0b0712840103840764900c05000d1140ea94000c05c408802128898075010b41c200c0184bd203003104440d0084002030050040200705c20140c0c800e58054803201c998040019400c000a101d400c420380d0360301c00210082024010303810300311070920091508448807803c00c0c0c40103060081045000f8040c54251314841d01140070180b8500d400006888040030700e030344950303c0342103c0001c0441203a0566405081c10103030340020070640e1200800715100024181c0a005c818094480c5500c45000c003500898204042e0740003400900001c3c3c00e483e90316071580710780c0c8602c07020003214103030903d1100c2c442c030211880400040c0001401c0b40309aa102148580c035400d801e090b0030024031030185c020b500080c45000075042503c2c0740f680041003521a8444440d050900000280f03a13004581c0745a40000020000c41e52900e02512030205c003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 581918282 1250 581917032 581917079
    0xf02010507060203040308010f09111614070308180a080a0b0907050a090b041a090a0e0a02060309030a2003091c0f2004051003020f0a0905090f07050f010504 69
    0x4040300790350340700200d0f802100d09400061800c00103100c4000c540300040c008040004003400003880203080b0b10681d10400b00c1c071880300302110311441e042142c0001c0e5200407034444410b0764030b0190740741001c0009500141440d0b01503801140c240500f231420040d85016942000300504046c81217945102c03809001800090a43c4115640000d550380d800c80c0510240611002c04035251825500740030035140c0030381085200d0384040d445280b081d02d03864002940301c80020070105001c1444c281141c1000d400702400780d0840707000410405210000002410076113116030342d41e64200f0504e80d40ea80120001e80028038580c1081005249502c0c0a41c0c601c0085a00d10741c0d80000265295205810b902c40400100c07040c1450202c8103512055152403901c3c0c3d90402c0d113040c0000d18000d07000b45603443c7c06000c024441c803040e1144100355254208000c0180c0710541c0104641d04040081c0342e601c03e6109100a020b100d480d2000c02c3c82d04002d964580341c0300060310f5450500c0d00b0502c1d20340340e984080010303809 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 581919532 1250 581918282 581918287
    0x30f0307093021050a0e0d030e1e2707020f061513091a1e010e090a0b010f21150e030c0307030c02130203060a0905070e0405090d0201060f120f020105 66
    0x22510660103460395083c403030b840c3c140c0c1ea4200610094101c01480051610078811680032138080380e00401c0d092520079084480c01000e140105501d102449001c90a45e0800b1103201f100c80040c800509402c040103400c90747c15550340c2d0307140c01240d65491400702e800d00c0c0e8200b0030124040d54009040810000c0c4010800700c1d4146c1002450030840301c40000540c0ea601a00c03540c841404c245007801904a0228441e010301c0901400d80c484103018103203e20001418984000744811506100200c851130f440844a484d65035103aa0b090104005c500502148105030581204038079010035520b000c2c25448454201c4507044100c401d0001d103403080d0402d007103000030005070307429000034001840c2c410300c25110300b403a880c02c90041c80200c4080c102c0d00314041e441002485615034902c0c060300308490103040c3c003081903580c11f1006c4032060600c090700c0380c115003004240300c2c20650101e2011070801c203980c000c0180701e50f00e012003449080d0031b200300752040c80e543c5e588601151312071311026181401814400d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 581920782 1250 581919532 581919563
    0x15170709060b04030c151409011421070518060904020f1206040e0d0206040b040c050612270309100e0d05010203010302040b010503061507030c120c0c0e090c040f06030203030f03070930 81
    0x4155911440d03c2134882410be0b04011a4180080c03100c5822005615226080859589002c040c07104012240e91188001040740030302c69a079501110003501c0b0980c20540c40c1e0f026a4400d040c1d03a0b030181e58080c8111704003603107010000703000100c121b081000c0e40d00601240e210303510380c001d080704080c01c00d8035240700c80100400d00e40c480c000100f01c801040801c0c1c88840c40e0011000c03501e0301e5a6402c007001c0038400748400000300400002ea50380d0000c2241c030015940f1400714150351020384040d600e9048001800030b0008d100d4194040c40c1200c0c0251018041e502c40e03000115080d200803210035520080812030400002c0415000c2c0c5196840781c00c005000f08070646030036255501c92201200007654005c03e5504209400d80b1080040650000c0b01c101410a517900d544c0b0b0b207041030b04460041e550b0b002e101c00480300c5a00120f00458000d41030303d070b03501244001c1e86e105a00440d40200410701504000845074018000070040c01d1440b21542484940585800d102c44145041520700400030407010703 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 581922032 1250 581920782 581920817
    0x706020f030403091401050403021509040e0d020708011802180c0702040f05071e050405010e0117040305070215090609040f140c0c01060915170709060b04030c15140901 74
    0x1940114004c0e150680214a4404c6902c0108240314450781005024401000141c0702c5401445089107000e51503510344d080d05020400401401400c402c440c85840c005851058010a909095440b00e40003480b00c5030300e0303800703031400e5603410348000350000900d0b44000541c0607107c010941200c01100d0031498408a5000103064a0500101000150780c590501800ba900009005050008190b580081c1d2100000c054020f0140344500d0341844140c144c0b01c010350f031003424005070004400d014503c15081c0b6040090580c0c100b03000407030054010407000d17010003001409461900c1d000400c00c6141c04425401c3c00080d001140491409545513101c40960140b9a8041c80c80b91010f940030544681d0f040da40036084d9005036004540043c5081c1d4000021200c2d00c0d4180150741e100003503503a403030005a910918014003580052a030740e203000c002050380158000200201c0780500c2e01c5401d19078641924000045001b2400e2002c1250443d030458544a5100541814541410044401c45014086 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 581923282 1250 581922032 581922037
    0x51e01051608030f01091a01032d02040e180a061d06070c0b130b0c03130b0a0c12020f07060504111c232a0607080c010609200706020f 59
    0x86400c001c011003000142c071294013210340104080b801c00e010a0715140f541003910f094040c240c40c1016101c1002c1d800c0e80c089140700c0003c030300d81280110310480b00c4c0202d007002034109005440c1d1075440640801d410300031b200780030340b10051490301404421803d5035480004101034942240c84c0100f4414072294140140242c62180c1e08a80381d1b0301c010251450070148142005110500900011012501152641a01640c800d01158083d5900c0e03c92a4041e02e000c60040e90007090702e14008200000700c1d00030b0300600e1b580452a114582c1075001030046100360700030f08248084590007400310001184464101580050047c09021703800e10722040420150303050704484040c1c4110f0001500c0402500a1140352183e4102c00d648020300c40b200c02c241c1d00d0700001e002c01e101c089200d0761100a030b1203e640ea94040d082009004a9441d03902d4038202c20341e40c10071300003902e09500e002c000007007400c03190003881e00312040b048a06c2d0318020348026032200f83d0085c00090702c0b0142d080c0108800d25180c0c500 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 581924532 1250 581923282 581923327
    0xf06030b0d08041403060105120714060f03180c150a0c15020f090901081603020105030a0608010c0c0209150102070b0f27031002070510020703170103080c0d0504051e0105 75
    0x4007800d814149814140b1b44001030340f005000b039a10301c2d0780550903000818800c040c0c9181c1142d880c2e403034050100040c2d06000344020005569400414800800b1000d040710f0450101c040595451482801c1081b80007108152a00446001000030003100c920404425a015100300c00790030500d0b125010040498009050302c01c2d400c2d0700000c130101c092504024060050840d80c00070300040c0841885601c0f02c1d01c1c80c7c84000c0c14032030084041034a10f80d180d04100d0150500728020007208a40420007028403548150681c00b810b204000700306a0400d0921180c40814103800400596181c10200c051a81c440c0c6024444100c051040180c1e508051115540e2140c0c3d000b03220400441c124200750034005807070980f01440c1e104003d820001840450b02d450b9030f001183d40180c85250b42d09050320008400c4d007002200b07a085c0d20010080050240141400c647d10004440c01509035003416501403085015a503070144503000180079401035040040d80e1010103251450400707040256450740c1e2441d081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 581925782 1250 581924532 581924549
    0x2c090c0c1c110d20010605030703080a12021315050307080601080603031b070303111501060302090d02120604061d030d0504082803051315050903090d14010c05040f06030b0d0804 78
    0x8202c41d030942d4075118010132407140705008101c050726040019545c3c0d081844010110100802c00500c1c0b503010351003080d03580030403400c00c1d0340d030304201c540b0382c82e921301c680c001c400440c0b01c1d5040540160780310b04140d070300c40c00554581808903100d1701c0c0103460b03d42000340b40e942d141c8410840300305d201d940c005401610514050041100781e00794078015189003a01003200841c1e6000c69101c010f042e14492043d07044441a0030016030302c4040308046030b010170140c40040d4022119040e010034100000510758442c60241d03400700180518443c501030240880322200001c2d520a02c0010701125603030b480b0a4010f84900082c9141c10703044412421010b4021503003020b219070600c145900c254140c011558080a510510562005290741d280700702c0074800b60904150b40e403980047e0070100200101c1d0001c510007859007401700510311782500300f44020300843c0310a50030710840c808518010010b1ba070a0b50340040d100c01c4401d080c074104400801c4403011741c507440600144090086913516009102912048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 581927032 1250 581925782 581925797
    0xd0e03190c02090702031c05040302120c060a11040605072312030403021216030309051213050f04050108060c070606030209010f240203192c090c0c1c110d 68
    0x380100f041111000b8442415034008001a42141c0c04800c0c041110000c4504001569103603420100e14000f00c496070f80c1101c600014560b0344000c0c00062046c802c40ca00c440500001c6104080c0c0c40080c0914802c030004100107012820006142c0c03203032181102c0d01c0450306180c0000c01ca6074189403070020f000310130314030000201b80414550b050002d00c140030f00410025280030b46d44c2d0400c443c9400301c00d0000c1c0030580c0d0394030010304018003070028030140d2140c107549944424150085085a40852042070311804e1400c0d0003041605003400703401e04030b80c4038101919144d62a80c0c0041000c0c0d022a5040f22040d50310400400160740e0b002c3d03418080c007a010b8040d00041d00f0900d298401c0540203a171100c0100072018880401c6a000040b60300090030041000349000c600c9034103550b2024601503009004203c405104d80a16007003001500b00341c3c048591507525140c1300e8045140d4410b000e201c031500d4210003102001510706011600c0c0301441881c003a5101c0c0201c41c2c0b00350070000181c0300e40e400640721 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 581928282 1250 581927032 581927057
    0x2003150d171b011802121c0315320607080f0712030e06010501140d020706141006170711060f1005060a05120a020c0d030608100902060d0e0319 63
    0x140e00c0002d4101e07504000b0841d440e0002d124200081ca105030003846504c0018944030092014418080010702c88484100c2940c683c4030080c020340586940b5860174503070107000145065941c0d190500d440d25140811031003080400c2152040480b1610860f08803400300910b0740002d4800004104000c004400b040c5c846000340b60a00904491146180415081040309441c54901151240c1100c0003403e04032102070f4005850385050041d014075a030b9441c4007140c00d0050000303540000000c4007482191a801c4c0da1680300b0001e07040b050b030040c0000244500341e07810211a0b6a802c11b50009000e040502801c181e0311049490a8400c56010b10b10326560002d022000141c488070f01c01500c0304072840c50510301003180082490003120744a21194140c0008561180c145504550310011504255000100ca94401401030185841100103a02c17039007450692020051080b801410b60042c40310345420032800c040c20113442420103403086800100401d00341114800d02c0c1d8008104a0303204d20b542c100e070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 581929532 1250 581928282 581928307
    0x1f0b0703140a0309060b0d11210a080c071703070f020103141e15010f0804061803091403190b06010e12010c090909032f01050709092003150d17 63
    0x80d00c0c102405040601c0f21000025500d14080b0b400150503100c1765509c460644c4c000440700120783c9000600d01030300c400c50060003042002080d100c80c2c0003080782c50042d683c0181c030b856041c0c2e281c094035040c1c00c203004180000e0840501d80350780e40e00514000c20524214296800d84a000703844000103201140300c801480c290600055038071112041030302d8628038440c40040c00321150800b1801c01c100e8098001820030486501803094100c1c11040e80c120380c01940380c040c005140701c0c015260b080b00d0b019034196242c90006858000043c0d030321043d01140c5000d95070240394aa016024078140300350103110302c185858807224a2102c0814100100e8495500c000c0603000c1e640d940c00102c0a64144201c203404682c2100090806502c1c00e203205121071018030322164007404100d0040e002d5404c1406001c900d5510504100a6411802d0108002c0b0726100f14401c441d4400300c540d0342d00d03200030310005544031804054543c40510241841c28541010350341d10702c3c4c10140c1d2480c0a0112400310b0720340c0381c034803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 581930782 1250 581929532 581929541
    0x80403030b0102071a0706091e0b010f0b090d03051c0b1305060d0f05070e100f060c122102071a28200318061f0b0703140a030906 57
    0x41c400e0000c0c00307000381000005901006445c00580002d1400070745a0204441d6a10004525801c26101c4a41250b0065082074600003504161042407902001081c0900354178000700c21254030014030752400d0130a00034008040d41d03012055041c02011b1000d8002d403070300080c9094000308108400920449000d0401c002045800204107500345880c0800c24292075452031010029000f40b0003061200c814601540f410750b0750380080f0b0300d41d114002130010001e498604a800d4404e10100300b42c180351607110885541500d510050324041d80c45000202c40d40c001e0301c00e81503284100d03c2c81000020300f2001c901c1680d00026007103411103100c0c880c0170f60303c94106403040c1c0c00103600d0b1000b0000700a202d00401c0c008105012250318242e4a02a45403041c1e16000f000b40356500c3c3c110000d46914100f015204104c0c600c16151642e8042d04c0c0010b4246180309415200c0c15524528200001e0f08084400c2a01d41011038202d0a2004006001e03503c5290380000c4e0084900d50760740030904600514044060b46c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 581932032 1250 581930782 581930801
    0x30e01110610092d0b0d1a0603010c03020a02030a030b15040b1201080d051213140609070915060804020609032d070312081e0a23040201020a23060708040303 69
    0x1410328542c41c0300b180000741c4d81c0d4540ca5403119004078244203d03030002854503c1040c80100b02600380080c441700d41308410313483c07889140107c000f0010080304403801e9080e0b21450b16400011f0300100000303103405010307034001c8200c21005050f00c800044004214a01907200d9003040240000100c1c00d0004000320005040c0980402c00180c6060f403001d51001d0700d1400340103c0d4112442c003120000d40f007040420b11180a0760b0308401700010510300d0f2100d461301d0784010fa5588030240200f48012039088054020100d049000c844c0148901b403410804403404440503108aa01c0882080b101201d55001c2003c07a407401d404010302090b884158054200f150140c4944042c19008118100080782640c103c044d101012402c001e1100c0e580d18515103218010114403e03d042051800c1c0a030109040d071101c040605078240d002881e420b28079906150344400c48000740180e1200c01c82d00001621030040d544580c80c114228404040203820742420544115464400903c8070000c01061562501511040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 581933282 1250 581932032 581932061
    0x60705210903161d0a0e06040c0e0f15060c0304080a1a070807020a12050d0903180609030b040807170d05040201270e07090b070c090e06090307030e0111061009 70
    0x3a10b407070800f1400c4581c0c80e00381e804c0e2051140c0000d12080c100d40025041141c4e041c01d4401d540b820307203040b188100f10380c080c089403034584c00300040000202d0781c401409480b1921000d02605501c008001c140e03444500c0017a5103000a00000803d42340c10011050018859000204060822440d41c0740d42c140003000d0000704400c1e0741c02d00c5503c07500407c403114047d800c000d0904000b640e09000f51880e2052007c1440700c2440c01307003141c040c980e014005058501103400c40700311255030392034221081c2215010181c040c0c4200710100c0c001802c0b40b801084164454544940740c2000e00d5030411007900110307030341003100382c4907401c01c000c540c0d126144c1ca0207580042207181c01c1c9410820740705680e100501034011100c40034008600342c680582214802007050030340c85983c81a080c9840da86018803407007034160035800c0178141402c3c10000300340715100301c20720b4000710b007444280d4404031443c203880aa80c905000000350852000c0b4801d12070035100d03c0c0c0d28000c0d003401d01d00c0e141800003194801400241c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 581934532 1250 581933282 581933323
    0x506070b04050c0a0b09040209120f0604060b030d022503020603160207091413020609030f030414120a031404030204050f041103070510082706090c01020c0f060705210903 75
    0x2505c0444058902020040ea00183c545188001141d69401c8007444001c4034802c0d0242449084400035005100da4420134080c028490300390107140d558559401c50740301581280a4070002402d02031921200c060b540407403807045030751747d03000f00d116a401951a07041c0c0c5140c2e401035034401d44c0c04100c454010800d1080c2006801880c01d00d251004601a143c107010050b03141100741556141000d9a00700b4400030b0030380f151005183c0d0351035541c1c0d12510881c14088000080d0040c5890042c00e004030310100c25025000703d12441e03904640d14840c001c5c01c0c80e0f00030020310010002d629103114007072241c203003a2400503050a0500385510365100c54490036129511550b0305101c00e8031000da081c3c2c3c44800740e00f050b04aa80323a0440c000d03c8246051058084002c400803010403546001945a008071300c10000e1300c0381086000c004a03110582070f0780c550b07007000c8428504045d605104004001e524015005e4815802c2c154030390303074003a08035180346005c0c2d00d401190254162600340440391076821440005079 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 581935782 1250 581934532 581934539
    0x608040b06061305040513110d0203061902190309110f0f04410907032607050a06022709010302010c020d0f080a030c030b030619060506070b04050c0a 66
    0x1400514024000c50080c00b001ca010003070120018003400250100401c148079610b001100400002d61020068908464108001c90350741001c1a54640031134029000c0c008942d212100b84203002d01d85140c1400c000d6081000300c0e0040c1d10409501c0e070740c40041d503010a41114070704129041004a005c214414042420381c0306c22540d820001401c8c83d00280e90210700344105022182618202d40140c81a41c1c121298162400003100e2030310250002c03181d0290066110b940146680d54400d0100078802e20002e00309401c60308248102f90461040d42d41d103a031900403e581c403103040031130008044850940108034080f90070080403640080300f03203069451811704020380000300c180d00c06110203810b201c124050b41081d510340204c0d2882007500a081d00b40c0645891501c0a0384c0c1e4860011000000e01e000d00b808040c41c4a8010300c50001c074002c00030700c02c5440e009243d4001900742000c4844099403000000ba1540300c0350090f061160040700c10f10054542820320a08140710304805502c181000038051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 581937032 1250 581935782 581935793
    0x60501180302130906110a0908030a020304030b040f02061206030f010e0a020904030c170a03050c0301051011100f0e07080a0201120f151403010b10050a03090809040c020a0c060804 79
    0x54212030301200c6229400c3d00e0210070070000c0070480340c0a401c8500300f08902d03100800e403030300501d01850a581c8582d44203565950050b201e00401304c115005130010041080495044411281c0242c00740641008e80226580024034940c851215410240c00c18010458549030a01c10081286074040082c1720140c1203208070b523203581080600910a04444000c503041c54460310640c4a03030b985c0318100c54060103109005100e581c0140303d0100000b41088000350b9140d0704002500d04070740014003170204a01e071040c0280c81c2003481105420640c401c03500140d524125901421100b0f80364204000313010180f00c20024109442c0380c00681c500c0d0311074030004006036030000e0b1100d808004c02c480003907044101181900580784980e4411540304003d040401d0220140400b400c0d041000c9008100081048007403089801540d0a55008100240a242141c9007e6000701c506203118504032850152000c0c0003604946290450b9801a4007000d190004c01013159143c0014040c24100f08000b860305aa80c2c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 581938282 1250 581937032 581937077
    0x806010810320d0308090d05070f020607030c0c0603061802040305070b180907120e01061a0a0e0406150f08060a05041d0d0302210c070b0403020f0d080703060501 71
    0x140110a40b0000d0401d038031000c505840004014208202c070381841c04c00410f13030541504d5402c4180500c03400c508405002e04204e4149540c0301081c401034401603001c00c42030340c224060643c2070201c04c6060348006140032003507002900e2152400140f40f41080e005009210b407080540030164410001400418030008201c9d0842d461506c2c0701e696140d2003409240008180030829800400240a20880c140c102c2c0303942e002c95025950400c0700300907000d407040c00c0c0c030003500c15000405a2101d415882044240081c608500d0504105034001405000308013111140e41c00014402c400b4600c0b00902d44c4c2c003884c011081400c0313261020007400e14000066520301d1a1040c3da1266948541c0d0000841d10260f65100c4001a002501c46d0b00c4120303003025000c0c1d480b042410603200391410380d80001040400c4100e00811405650a0500c59a80d8822224180113002a0294801c0088420050804001d5050440b40d19520404a4203000e00e0280917140d80c0c3d04a030341403104840c0142d0000503100303074 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 581939532 1250 581938282 581938319
    0x90c030312060d030c12051c020a1d01090503060a050414070e0c090d08030a330e061807180509010305100c05132409050a0b0901020c100806010810 65
    0xc10003e52515840c080d41c152890b184004c0c00310203111032141480d90448003804802e80d41c030300ca050800d6020501c0c4400c07445001d140b4000b20340880c203036a04991a804c800e0b0920b00060501240140d15000024501042124900509070310b50080000700520340c01c140f5200c0501310000d041030360904819140c1e0003c020300c000b50703005001c11244021fa0b20300c0800491180c0100c1280c0d0f4078103120000c070000d0250600022080c034021400e050041401c49142c48080204d50344414029042a0407429141000761401d680a10840398501150086814040c001c0b41c0303e480c0c12081c8021718094070382d6110700e64041d600c500c044400401c08a500400c0c4081d604646010002c2d000482650030b4400c0c4c002c0c44010060280000d20104141992400d0110301c0f603c0100002030082407441c04482440d99405050b8210030004410042c500220018140c1d0110500540e01c07140000030104030b41e180c00020720000203081da01802150b50b08a106960401c840030821201941421035910180001d0745 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 581940782 1250 581939532 581939539
    0x501110601031113020a021e0f07090504020609100f030608010b10051b16060206010801020c19050c06210a0504020616140f01060e010e0412080a02070c080105090c03031206 76
    0xf681c210403035030342040200725424090b10031074841e00a008025070340c40380043d00e0283c10300542d99040c0480400513440b804540a00010320060b8240b54601d809402d01500490f000032080c0400155035072a5900458040700c01e550b03510b04640000320060a9800e190700c00b8000340d242030114221074491054001440d281e90621a681e003c410708104806505401c0d101c0d400c1c003503032218981c07580c081100141103881c158201e50042e6200c0400600b00c0c030892a81e69181e6205080410341c08502d8107071a1390b900d00400580720b48100350004a01300d540000e25001301c200080036036842a01070000007035000301291070100410b1410742e000c038005d8859200090615030b4282d601c0f504005000ca2101e045007014415136100c142207800d914083c0005000d080c415222480000c42c0010b04041c03107a2040c0d03040b0702d184201e61850035041c3e405100c0a031840403201d40811a074004100c4d012200c900030300c1d000000040c0d5151004242d41045d1000b408a48280c00420441a1110403c400550044001c0303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 581942032 1250 581940782 581940803
    0x4080c15070b090c031b0307050108060a03080a210b03120306120a0b0414120a03020a0e0d0507172406032406041503150b150c07030c050111060103 65
    0x100e840600d030058100041481009004210000303c010400301c41a000680c110b81d25400ca90345400320510580503100d4041d4004c5200700070561003080c0041d08100081e203140441c584946a1061030345c0821a80000b0448210701c0c45031040c05290310805050a030300c03042100703288010001c0d0b22070302c0a10f44c0078441030f400710210380d103035032401c0180d81d0b0343c945e00c0b0407135030607080300d103002030302c001c8211010b840040c20081c0040c51442c0104006006440341e4098900d40f401c0c0100643c00cd410400217101040460910550749407604074800700b4150040c0001c100c004c1c5030082000541e1b03904540281e660300404006941c0c6180b59280c107403a141191100503003641da02000c24a82581d0300d5074890100a0505690a44049103912038010350080da4103215400312a10242180300403031000602414498440f4090080150301070300c13045000030400d00c07190302d1b8050725021a40003c070440c40740303400850040041000d000100002490300b800c02400301d04e07040719140e41300c208c14400605154042e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 581943282 1250 581942032 581942059
    0x9050a150c0314040602011a030102040e0109050a0f09080d0c020d05090d05030706090b011a03040305030613060b031623040e090109060f020702031908031f0306020414030601060504080c 82
    0x4400c00654545030f540e0a42c3c0791551400024007030042c1500e0300b054a02c40d28180402800c042c006c40b800d0b9015401200781b942d01c3d10409000401004002d40c290580d2001c141347c02c1e0106c0e019001c0e034140982d60142c0c640ca0301240b203000711210003502e481954401c0e41030055680c0c01c44103071a00c801c41201c0300e8081400c40e003005070540c42031403c02400540f80102c51420019100c034140d050741e0340c00030b030407100c40f400200c0036245120584001d00860380600000301c0e40c0c50913a91402da15540c202020400540d02c0d5540b0646070000c1d120803036240113541040e004154454001240c15401d140141c84091090398405d04610581c021100d8650781d03000024880c050075017013070b440c2035880700c410001c000c40d02011400942048504a200307004078255030050701c0581510462507500301c040c2c0c1c1d03e0340d00c0703030711140d11601b0b844d0500c0b4450500c0c0c18800008140144040d100910441d440e10035103000c41d204041c01e00b81d05030064800d004c402d0205018001e000070380f004030800203a9190200900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 581944532 1250 581943282 581943287
    0x605030c010e03211908041509140114090f1c0f051b01060e01060806180601140c0106090c140a1206051c03081b0d0c0e130c09050a150c03 61
    0x80e40d40e52800c001d4034000380f100400c0b180c000300500a103812822256040310007044a007110280c8003c0e12460000ca08d03070f810300380c41d540a0040c02c4d01c00c1540520326400f010505081d5011410490ba0021004040150003442070154070781c6c5c807002501a000000c5c40c030b104c90840034080d01e5040204180c141c41c40c2215030088003168241030240e6505000c00305003000b074902900e014050307075207108048000001c0d038078050107025004400c014824030760b40701000ca1000031403600a104604000700c0c0040324030000e4508000b48062003d550020699908000d180c2c000d94021000541c100901d28204804000702d40003900c0f210308a44c030b04110340e80c3c1c5041d02c50000d0704403600595840021149003141640100003000d103814403039210031300c02d0b41e81d02c855034185218002e4288030308101002248030149055200501ca01020309000340e41665081c042100e218541950300c05183d0380d106541003094210990000421007150143e804a0810400c20166001401010700340000d2014440c205030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 581945782 1250 581944532 581944543
    0x30909310b06031f024f1202190b040b040f0602060702031918060c05160f0b090d0b130302011407090e07090806090c040b040608060c0714070315050702010605030c010e03 75
    0x7000149004000c08080740702144481ca9011502c82d0b0829081c2901c000c0d4100c0c80d0140b003110140c000c560a47c540325000d014148031061a01c1c840b40020b0240803c400020300050809840000046a183e90404604841040703083d000f04056510000030407801716400400c4842500280d1109200d13035240000560b00078604c0200c24044a140b0080410b2140d80101c602ca0386902440c02c84515071000d050003070114081d0702808045040700c15060210704511070081c0b00590000d064141d540c1055220040c070100305480800c1140880c41c6000e051640c24000e5418441c261101c0b0f100608201d100070b00541800d200d80c0190810381400600d07000c1c09003854100501003102503500900c0c004000715214200d00d0720340c074861450140b403902d69040034410082564202c01c02410300707071031340ca000030400d070032141080ba001ca00d1403040018084050005c0c0c0d00541c0f041e07445038170000710104508250341c8014140713011a031401c1c90412030365500091f161004030003824440465a05140401d0502 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 581947032 1250 581945782 581945827
    0x5030418151202011b0b070c05030c0a050a26041205030705100c0318050604032123060d020f01080a0902040603210c05030909310b06031f02 62
    0x10708081400100c1802c2481c1c801c005034401d80c0c0700c4000c0d044400c4038860300300031520084d01d01450240019400ca0003107042c081c000380520100d82c02c203642c1c40c946500c0c0030359018044595030080042181045100c2d2040202560507840040d480030081601d000f0364022480b034003045940c4088d2000c1442000e004450f5020f40010980341800644100f002c0505801d041c00d0000a242074040503a622801e442d2041803640700002e01199290307510200d9212106281101c1100106484040150164464585107aa40d41032039070a4005070a100c0d07040e400d004000174003a040240400c001a90751036140544a1000d013850711540c2c82c1c944421b030040402040c02500103240c0400030090000d4000e1801c0c1d0400d03000302c580f40314a030074501110f000504074030041082d4000c0c000c2502c140350981c2e0b11075011203030840b4485642813044414112441004192600d1800100b400c0c1c24841c00e004000e0b03010f0000d40040c1504030034100c103052410110706500c0c048907804030301c1d2000d0700f540319072244a5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 581948282 1250 581947032 581947061
    0x3090306020d1415010509040b12060f150f0102031207090b1204120c0b0a0903020307080315030105070201060503030d090f1a0a1a0f01080a09061109010210050405030418 75
    0x25070014084020003015500f480601080003080080e000d10328094203828207080603500c107410840c2e884244000ba24044002035488005980260701108040102c1ca2080f60f6482400700c43e8280410a0390035800030002e654003034402401c150503076980010841e4042e20b05c0045080a07581c5040c1c007114115619040088461000656440c8248011600f940110702404c8102d220702641001910344801d600001005150b0b1180003c80c49203544e4030110340c090090050307038608911131742c8040c3d0543c02100c201003d840c1c0028009127508007403060a5200c0514002007105500f03180029540e4000d10008005a607210112203040090132000c021956900c4410352558403041441540c1402c42220800066071401900440704000c9442442c1d000c00003410705098104240c004641c104401040442c215445896000028005101e840246d010b6540500d8072380888800080c244282d11800814030b41c24101407001044002c800c840c21a174170428001c5821154402134000b4000e41301c4850301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 581949532 1250 581948282 581948287
    0x3110307031401050d020a0308070c09090303050a0b091b0a02010e01020703020d0f03110403020f030a0b0117070e01030b011203091a1b15011a042c1e0406090309030602 74
    0x162181c154000285580d500301c110350540ea01c58041c4148022124006507010102c0740c001c001054070000104002800795101c04803031910b440001d02520325034441180000c0e500d0b810070885207124461101a041c0445060a1504010800341e402c500b861034500e041c004000744e4451414002d521030046212000020740d1200c2403410301030748a548580b4868041003101640d2841c05109201e80c030244415640084d090608580a1204011006003040e03050b02c0b50003502d0011842e0804c0d814024901041401910a6201d003602d0070a400b03548280018803142005100080d10384224905450504c004c40100c0c5281e401c1c02c455007031050388240720000101801b100c907500d07882d0080c940d095140e5044500141955541076487d250031300044480da407180c005012141c04064614606041008550f080980381c4425490814415490b42450343c1001c049002c001a000d44240d44201104040e8441020f041c41d245040361000340014451aa64030002007018044c0350a00c01454102c4011034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 581950782 1250 581949532 581949541
    0x1210915050a06080706050a0c1a0f010f060c02030703020f01200f2a0d020609060c150a06082e06060e1f090608190c080411010f0816031103 62
    0x400034041910b580c00d00314202603020580c0c01c000036003001140c08681c6c800d450100700d440300f00c0f61410090422182c640e0000d405100c0200140040c0d806036042c203030b80f003801c1c2d45000402e100c25a220b5020f402032040020142000d668081041022207170103030352183c1200502c4004a5800a035103900041503011400701ca0110700001842504d42204902201e121500340007050080d070501000c0005c0e00b201410303104126051201c2c41720b000c2403001d8101400c0800a80025400f60800301d0007044d80d6000d000d01c0c1c9a1502c034956040d0f08507400340c07801c00c00c2604014541d502c2d8611505c20350038041c41e110050034180000086001c954034000410844181c03602c4004251440007100c1501c10400c40610007900100c0402d07008424106489203040140380150503144580020445510303144900b11200850b01980280d1000d41119600e11045240c9403924032800c00f441c0b01650704105c01c881416040b990005034242c3c00032900541410301503c450b00442c042c2014003421190380c9004170510 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 581952032 1250 581950782 581950823
    0x1512050102091903050114061e01090b0d0c030609142703040f17120418020408010f0b0a080a02060702211c0f1103030403030e15070905040e0c012109 66
    0x3c4003501d00c03560082c0705540030300c1d404c1ea0201c40143c441e1035006d01824002540042d8581035044184018146404019a500f10f50326032a00a945002040ca4030b03521b40210f0194036214040292010220070040080000f90341c0180c0c060081100355240345260031912003ca03d031041940400c0c6400c21250340b20f4542c0750364000c400311841880302c0940e4502036000710500200300015075410307848040f803d05250814907520340c0c1c104007500e60f00f5682000b01050700c0100b0702030072020008031140800d50300c001c1c80c140650008181c0c441d95654020040780e00050741ca200072641c240740c0450b900da1040307100000034402e600b0894100381c594451403d41010003046100c0c07081c210111521404e03200c00c8200400d481d003216984041c01075030020400100060700961005070828401e034121041c0341154400e201c803840040c0c03401800b00e8400c800801807460a8041d103e100c400c40b8014250b64a50080060300f42803a1880c0c15480c5107032403d006410803040e610170000c4507000b0510b100c1d00300400512 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 581953282 1250 581952032 581952079
    0xe0303031e061527040c0f030c110318010e0a0b090405040c08010e100c0507050705091003150506130902011b050c0303160204051f1211120c0a09151205010209 70
    0x120400c1d0001c110b01c02e4240c64180305002c415070691f02e40b100038058003036046009090029040040c050907002541c0e000804002514841303001c030b040c42c3c45100546001410456a00548a2044858080a20441810405454038810150b50129a946a42c6020112840700e0303040b1740041d618210390a910200005064112074141d000200940482850111403e1142d01400341007540203000c100000d00344425110380c013250141c02d4000c1c5540b25a40d001e0186c001c50301d810a083d0f185c0c414008640340c0ba11441d24850040c540401040280341e001801078804034540300b001000e1b44582c0014407209000e002c064050080035203035280940840070300c43d200054010303402980780400048034120240c2032521a0039410161003460b41c944103a5286c406060b1104481c4a0030444540c1c01c1d5454190070031810400440242450f03618550910440411661110301f1b42030410b02c8136010030781d1440c0201c0a560031071050000040d10b0342441406440b8500606d0341002c1c4151890690403600c952 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 581954532 1250 581953282 581953327
    0x81003080a0e0a090b0a0509130812100501030c120b130e1501050306041a040305070c060503040203011410180204030c09050402030616201c0f0e0303031e0615 70
    0x4003250f1403034aa0711220221450461840d030800035000e014481807901e142c286034040101e29808034400c0a594401c0e00170b800000d4050404003d9400303001a2035100076808010b002e0070b107030401809544100c014107211421062084a581d02e0010071a6615990307112860b80c91890014001d55980e405080c2d503816241c094200031101d442c00100e600d10f0301042490086810803415940740c00d6100400c212004050405c4080c030104101c84000111803035100b200501d130700e48034680c580c94a4010b050a542a05070302c0c3c90b486801401708020700c0c00d02141c400c152013442c02101d0607030048046100007842143c00162078080101d20000e94140300d5000781d80708034429410f4810340c0c0c03103000c5124a200d20b5581e035100800d03180c440340c40b1500300007124403048030303c1074007110704502d034200c8400e00c0c3c3c00a0080b07030030002e56240c07000a0010f802070017000c0d21a00c01c1d4003c40c84c40c501110308c5007c0c80d401f4203982c070340e0080d10008201e40307555201c0810038002c01216160b5889940300580c2007401c94411 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 581955782 1250 581954532 581954539
    0x609180108070605040305120f0d050411040e2d0a060e0303070f050f0405010e0a0504020c2508031e040b0c07060306060c02062b02070318170d081003080a0e 69
    0x20300203d07502c1d00c22401d59040340ea0280c0201011000050000c821350440320030024032079020310011406840c4d9000f12400b0340d014900f0704045050000a02087c0d03108800000b080c0e40c006840f0141c5407a400c1c1c4a04100a00301c62000560000c511419040000544c0082c280300d041c00e44191440001000440c0a00b29648948000707408041c0d0075101c40c002e941300004121420b01c800c000c0340d40180815074400300d0040c10301c1c0707090b034032840060304a130464000d501c2d0701e62040641d200381e1103c800141c1d4100f00c044408205452500e40c034503643e489904208540001c0190054506080401c162400b50002d40c0c0744070f40390070800c05050f580ea20140b041c0400170f4280031000644d907005180c2400495005004645000c5500312840500742c81e010a001402050305110101c8100c244080d140d0507209503264a80c0400040c3c020f901150542c122000d540744001060004e40706c001340c0250700002d58182800680e495240301e40c040d102c00e0784054182070b00000c10416082c1d01c10400a0f200d4001c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 581957032 1250 581955782 581955793
    0x80f160210090b1e010e0f0a02071406040314090f040e0712051c0e0d0206090102070b041206140108250b04060305011707030206180310060801020a0807050307080103110609180108 79
    0x42004c1c1d10380c1030203214540c0c49100d104041140c3c94000f0309548d501c85c2071071101500e4030f10640d540c0d14240089008107890368110344280700416034011800a20301e2000c0c0800c6041c0080c1000040070460a181024031881d0fa40344038560303200003840004000c000d5241908a003032200d00b855034450980b01706070320041c102501c02804660013000c400c1a05031000d8000b490000d0075609005465100980060652007040f0000036188295401440940014603800c0b0001d111381c40c0c40c4c81503441090915405841c0440144484607000461911081d1200d501c0c90118070207032094801086182c1007608411400900815415016003006040b1600030f00180d203100c40300300700a81c807007206000095002c502000f80e81c4205c2c184503003a0746411001015a41b03015114200c00c400c403006584010341c2039402080311851960030198042d03210a20b800c101d8503500c3c02070401000a02e050000070845115101d420545889440c113503030b8100d80113000a03803080a403c0381c90907020801d10400c00c41d0301c40c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 581958282 1250 581957032 581957071
    0x210f080a0f2a030507031815030b18060105090a09063002130c020102130311090603070f03020904080d0f090c050a2303010b030313090c080f160210090b 67
    0x6140c0d0010b04802d0085404038540e505907802c0b03e095001640980412811505080701c2281c0c101c0200020000000030480c0560b4424015060718046402d480c4503e030454000c550034000c0001c017a601440034a0300d0390350303006580000380181c8420f0b00131124040c1f4005005c00c0340b00110301002e40c0380e9440e110038258034141c3e0072044031011003480001e4215000c1c00c01c5091000c051780141030440f07513900001d401d01e11a03141854005a99034130544c0c0d1182100c0514000341020b102e21a0071450680c0a006560f00b4040b08aa03e40c0d0984402030003016910001014000280155503030040280800d01c450074211901e10302a0012901c20756079401030080c0090a07181440301c100807112440e8641000c00419105900a0107107a0402c6415540f00c4886e182d031603906000030185103c852407140c0500b42041e070103004880c0101491002c0c0184c0206101006030b0700340d903241d0701611503a10481105a0240100d0921041801d546003c03420800c00d07204000c8103003080b600c80c2070780d0410046120705 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 581959532 1250 581958282 581958317
    0x71d1008030d051906080c04050c0412110a08060c0a1101060e0408090f0402031b13030803010b070c050102030a0e1c060501080a06180c060f0905090708010e0907210f080a0f 76
    0x105c0380314030a156440f0940084241c1029041260700c6040001002c1c1800da84800c0454602c400b008226051444a140c0d41c003035280c240c2018000c0e18102c8020509494811020401031080b00111800d04c00d100194060705142500000050102d40185c500141001c0c0751080d00d81d000084202c0c031507040000c1c008014140f5200352032140204440440c03c80288121900007580088403030b0004085020303000c03010401c0580114002e0540c00086030744c0d413000f070a194114200c16000705045410400100e0301d103a90000e40c0c2000c180b4100c91106640e8603126090031000b0548a00902c19403c140001413200350120f000d400140c0281d80c141700307800c10390301e4503d14018010030081c010814a14103008a80c800c41400e10b1b80900c40c188046020b071a2400a0a442011030f11000014020001480518580418a13400280e8000180141070a04012540344100c5030300381940806160744401c14400c445040e44030300c1c0d40000c0072075640d9040c2c004c010406003840110b000403503001c040101403440b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 581960782 1250 581959532 581959541
    0xc05010c080f0a110d0911030607090f0302060c010209041b1803020a090507090819021c02010804110303090a0b091516020d060e150711071d1008030d0519 68
    0x805000b070b10181d03640e401d0075400100204441c0108020081c011100c40517903a128280070360b40900704002100019104051900d60b0082100e410403102c00401c000e643d0b0015008019203904031030341e43c1c507400d11031941c50090103050501da5000d410800c95059841103134a0030b0081503640e94a28801d04007600b2034412042840c44020340110b81500d0402c451036003688040d401541918103103074101e6490140901d8254a08031180030340c00c5802a000031450600c0300d403c60359240140e81c0000032200d80000c0c100c100000c00c090801407017102c041905030380a20484803c184010121060315403114000b12180d0400c0c0140c501444054160a1001c80c420041d5a0311806485084034211a240e00348103140c40700c210105c84058903000c0070385032002c1c28007607411a0030b40ca00014000f0302c3c3c80000203182091401d000d0045c0d800a0409002e00400c0d03c660300d58510380401401029103a03010350507105240d82d0b0045610303010105402c0c0044c0400d8020318069450842c1c45025032103020b040302d04a4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 581962032 1250 581960782 581960791
    0x60a020c03070f1e0813050906102003040303081503060c19050d06150207051c030806130507180506040e010e0421090305060c030402090705070f0804060c05010c08 72
    0x55100740101c82c00521200c0044281d148030302602039001004200c0300c02e052042000898038410b0100351646c20740d03405c1070a00010141251104410300b00304001c10b000501081c00d4204000c1c1038006000e03440a01c400c110702801001d400c0301e80c1c403036481c140105001400e59540c10100c25001c549105490000340860080240e48403051400109102d01d16111200c1510141030190501100c40d082d1007512034100100705800b200a0092024a0000d08114690300468803409601c100041458490a5902030303603030707050810b032000792503102c00541080211404100b096080208012007141c0c0540d202c0c0c3c01c2183d20000208407900c8100300300d55809107014403000c1186560040106825106039140c1040c01540c03502d622140c0b101280d20096039200c1c5001c08101e07020000c0003004410000c80d5804043c490704142076040c580c3c0007802051018024170100040803d0290900c001d010103030404d40c1e400300146d50f40d00c0c0d450b071024025403140841500c45500e015036a80a050291104a214 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 581963282 1250 581962032 581962057
    0x321040201080f04050106091b080708070518040207080f0a02070e0f072111030121080f07140321010801050f01050613051216050a15030c0512070e0102060a02 70
    0x355964550f051a4080300148103131410740d200e1900098044091080d07681c01c02122400440341e030001c000141540102401c00010004038908100c1c21b15400300607107815400c96061071813078407000d10005000c1e0088400180102c0350005112103a80390560040c5200c0025400b0760300007998400c86002d082000b101c2c20019280440c002034504c0780314040303031320020b8005620b20301440c02a0720300300101c1d81002c50f900071411000006125840444202400001c0551242c1524041c00e9959040c0742c0904444460300c004045040001c000d01d01c08000000044030302120f4a407020140031002560b140308850001c461a10004070301890103000f89071151004211116842e444c2109200490740450603049a80d240c42d4404030304c5aa40c80c124540748080880203054080c40c54415403103444440c0e028902c20b0300b165030100a40c100c01c886403154110360341800180d03452505010380303c0344921504040816610020000400d8104808400351790302030f821106650707541c800c1340c1d00320b105500e1100034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 581964532 1250 581963282 581963297
    0x1223130f14040b01030905240112081e040e0412081302010c140709060f080c1002120f070f1a0f220203030d0203090601080d0e1503040203011d0321040201 68
    0x181c6082c503403c1154501810f140019500145846880c203000700f0000e50000c600f140744500d107480c0c900c103803403d0140c400c2900034220100566140c003050301c58a41901e000c81101103c2a11403a01b54040c1d0b4001c100b80703502c40f1000c0c5003500c0c1012204149464a001149869000c5100691140311040300150b06840344036a813000c90700c410164050781c5a540b2101e11580c007012407148410300804004190070740414038800d00306922079081c2100004d04d28002c0c80c0b0300040a55056002402801d420308201420b513840ba21710070000d05500c200d1002078841455903610000300105031a08042c202d542d03600071071407500c1d5120b41d024100d1082d215403000c03003c890380c2c03000c0b80365181d0015455284020203c030300d862540c01050040e604100c40d00c44a80e045207004100c00034050000085071020307442d00c2e2008001201c0021441c3c0d480300703d2440d80d00004000501191400d41c084080084050b040034400025814000c1d501d620800c1100c400b5810005048244840d5240c103500a55050b16000c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 581965782 1250 581964532 581964569
    0xf08041a1903020a0e12010f1803020c030a08040b0f0702061303050d0801052b0b01060e010f170106050702030c03060c03010f09021c0903170c0d0608191223130f 71
    0x2846c0807500140c0c0e00d542e81c44072440c171800e1034451010010b11030f0300644000040707800d01a06100e06854420b01030740041c03e040c0c0000d01080102c40a41d03104800540d240c1880700c409401c1405070040c0203401103400142100d4040d103020700d0000312440b40048846100c24a0740440b2005800e00c0b8842d0800e018950700884c0041c2d40b40c04104004440a0b40d0010190944600c0c003180000e070f004038003040104001000d11b507404404c4040d065010300b030514441f44080300d914100401445448104800030510a04540d8244181240750f18020100c1e0014103201c68070700703540d5200780300c0c2c0038081904010018aa1007103000381d5610055004007806005e03203946d4000c4c060241220110100035141c0c2e400d04059401f003443c03501034451302a45648a03544451403034104c4245410980c0300307902200e0180b101548041082c2e00490748010740500c070b14561641a20741102403400c800104075440003da18100032003000e40800c1c040b81d22090a207035558507d01450800c9030243c0488043c146404c0c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 581967032 1250 581965782 581965789
    0x610140619050c0a0f0c150206040503042106020304060b01200a06020d14040b041506030209070c060e010e0c130915181703041505010609030f08041a1903020a0e 71
    0x82c80d4403002c0c0826102c44c000707181c0c1c60f01c2a046a0030710480d001520744200b880551001e00c10154000c00c2d0740020112424142c444541da401544150601c3c2840402400301c00001e65110050450748141d0035034880c00d0618242c1c1c00f41c02101d4046000903c1d000441007040b4900720404080107130040505041030140d02c95101070b41c0120707a815007854a031503201c0c506038078107060341d80701f10b00a50388205981031074a0103c0e8490130910304620818200710f000e20260ba01c5003a840d41001c034a080405000b1210b1a0803406082e414046070169403030086c0352036042c00b01003806041c01030120f5000b00c40c20b8000301804121140160081e00f117405219104031a01201c2e1700c03168080300006087c030710300311203641ca010315030034095009106584040709100820200c2c4000d01301507410030005020940c101800100018034a200280004800a14a1003400051801c8801030001040f9200c06026900d03d204540e5020341d6210f84400f1401c07030b054000c2c5200f8801d81d00c202240d42c1c0c41806003070020040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 581968282 1250 581967032 581967037
    0x90f0b04140417031b0f0f0a0207060e0406050901090911040c0c020906030f0d1808010612140a0521070605010b040e100503120d0e0d0e0f0a15030c11061014061905 72
    0x6c1e64080f407801c1080840c60700300000500740908a81c0d00a03c807a17410108d000f400038000c4201c450240b424890309000302e65808001c103040d80c1c0001000283c581807400c009100c0703402c05940d10b810500e017020100b51203501c8056041c441380207484003200794982a003855501c142d0140447c0c01900000064400c3c00c0c41072740500b4149141d00441c500300b40e20360302c1c268211003c075440003940704c42c04006101040900e1102c2400060304c0c0e005401e0000e007d031642d036128504903c469040d00d01022116132601c1c112429556043d400034020401036031940c1580003964868000c26010718002c0780000c140c507280301c0d1540140d400217400342c0043c0f8482007103015a5040142240c0c4141c0e11030491560300c140c2007080030f45940d210768070301d44854031820900c4003603014600791178001d164002040c403c02d510001003031851092440c00140d40f45176040211007806605010200300d0140c0300620440701110a00c41d41030b90440c10340a01151030603010404140304040718002d01d41c0000c0b034078140c807134000c001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 581969532 1250 581968282 581968297
    0x111030f040314030c030408010c09080a48060e120a08070c030501020c070501030b0612180f1c030b0904020904061d0709020d0c020610090f0b04140417031b 69
    0x1312800c02c00001c02d9941560002e81080c00c00c0e0399520f5252a03032651241c032000c010848803001c0c002e20903040d00c4240e900d50040c800a060203441445506400c40444000c103201c1c1c05040c2001051a1103000041060071280724071000620b61000c52041703450314420080518000030700400280c0f14960b80c0d24441c0d0403200090742c90007552040000402c00a0000b0045c08c0c03400302c09441500e040400246c01c4548d0402144d00404052100580c4100c0c00340c0b0741600710700c1d0100d00303007034540c85500814038142041c001c0d443d050240c0070b072201791a1400c4401803e18100e40e2000c2c002d003d003440c103001c41d850301120301960000d003103000b140210300268048001084161625031205842d00c440d01d240a500b0f0748401750865000604603003c880503c03d005c030061041c4013a180608000b61100340160140c0145070042d070380d511203520036420aa01918418101401c1402210903683d408065464201c90585800d0207174800d8228013120081240e00c68102c4840c40c01d540840030b85040200e40100e030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 581970782 1250 581969532 581969573
    0x31803030f090b15090a0204210f022206091b051c05160323160e040614040b01092105070e01030f0519031709010b0a030b060111030f0403 61
    0x15070501180c04005031902c9800b00c2c4440d04080e5418509120740050000c0040303580507c14007050000701d1054445841200c0b0104034440103040c0c40c10441c500a402082c02540114591664050301910038082400500302c00c20801c04166111141e505840d440401c4542028030a590751403000d0069001d010074400002c5444009090b0b00c12140840b80d003038908104404601d0b00396545103030f00d80075100083c46010902203030003520b00170f160800380c006001201d6100c041d010113482d2034450920316480b004010000d0015607611101900700b001c00092680c0581d08240048400354060101c03e001c450410940389110640400c41e841c80d20241101164a400707481c02c0010354500300c05440340618060020221080c00340d1401914050031081c101450f0314200d03030004042508071502410301030a402c2d0b400d070169100c852480c010180040220b50000100c8004424441e0307039044c15100c0c000a0703e40c240e001a103014096524011400c40c680c540100300402d1001a03410024900480040c9 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 581972032 1250 581970782 581970791
    0x3090f1e090e0c0607060e0a05011b0e0a0302060f210a0e03090112020c0307050f01021306090609150e0904051e0102070c090207020303071208040521033105030c0c01031803030f 78
    0x2009924180a4151401c9c0d031140e4641d880700c2101c0d10150307100144181c8509113019690101404035290249600c0041d115041c080760f01100e0740d42c114122400906030300c1600304410720f0746403031a1003610103640c2010103134031700349000309120000811121441da050f100d00c00f540f000080c6100c00703548101070700c40e8507000a02a10001600402c640c280c0303c50201c001582759159961440000d009a602000800c480f000040100301d411840c41d0003983c100c95800080c42c10714910694020403071200d00d80d0050f0428041000f0b00c000448d243d1809501d02038002c885505000206003030340510040500b20344500070703082180300c42c0c40d80103042e00c0344058140c0b414400725444050420b101900340d8008220b887c010082005014484c050156008620381101200c9068440c44a80001494000341000e500560310001d80160740e4800c100401c000c0c517414540040c0f80080c0c80c0d41084041260b24800c900040d01d003503020380550a121380000d203200208803995101140901440d804031807420796034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 581973282 1250 581972032 581972051
    0x825080106080a150c05041e030b130c0603020c030901120f02031e0705040e0402040c0201060308040b0a0e03010e280b040c050f030604020603011203090f1e090e0c060706 75
    0x707000341c0d0018014000038198004060070210901c5603409080c1d075500746042c0c2c014841d160032030b00791420360340c0c06070050300040304100f000002c0b800036800180c003400e0004104030128441c6d01080003001d106200d015491a580d203401d0742a0302610700c000e421078205101c82041d07948079032106000c0c0a0900030104408018800100880c0d00a40341c5010040d43e0061040b0780203a18101d041d00b01050f80b42c9545401c4ca04282500c0390440036000901c034948510200303188906c00d4110801850f0040b80550340c4070382c2c4204a031026407081d43c00c0804249041c004409074034040c03140c59003050314840546803a80454121100380852035880c403280c0c1c1510002400800e818003c000d21484c407032003100c0d40a0307090008201d100c1c003c40c0c4196200340e1203c010030005884107010303203045a9500079030900042d068501035881403c160003d1175020303a04000080e0105141c0e82041d190f01d00c00200d1140640c4a00702074080d10b10401c0509550382c800941c880b26818440010003106000d07a02c0040d4503000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 581974532 1250 581973282 581973299
    0x10b0f120a0606020d0813080315040606030209100306141009090519140411100c14150f010f03120504090c0e040b0f0307051203090d0b07180825 64
    0x41514810189a500c0b0020f001041d01003000e40a80003c604000c00c5901d042c02d4031415001c2001401042c079203010000c00e03c008070303001d1b6014142400800900c00c250b1101c8000300250400a2114800e0b2003913404174060b00d000c7d1082c10140c036085031050b001d03031a80506122007185000c00100412012401c0045c103c0ca1511074540207142c0010780c0c0b00120440072607103050303490b0012107030403120300b076010301001500440c2810940c84041e204d005040100703190958014180041c003034600288440350300c8405001040d049180721207041c00308110f8444120900c082002401480380e10f868925081c00410348142034580048414940540350544a8404031f0a40e8410b41d19500401e00342055200c2c40c0c9018000e0611150b000da07020208120341c5000603a491102e881250f02903c90306501300002c00b01442150107841c000351510070090200d02e8068943c040c203e45000004081c07583c0c0d10714031421808054100c0f00d180d4014071501c00001c1c503602110001120b112000b1106510021301e480 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 581975782 1250 581974532 581974567
    0xa0c031d0a1e0c14150a050a110c18010305010e0a03140705011b1701240806030c04150f1a0406110f0d120515010207061b020904060b130c08010b0f 65
    0x510840e200801010b10014001711860100b4a0251070006002200520303502130103460140266240a02d800c400d00410f19080c0380114000f0750b080001640551440507044c02d041d4100c2e8441e6000700306030340da1000415280d16464500400191111b200011007090013009050803e004000004031a034954400502600c01002040d021903928100f051101c0c8a00c42d80c07500400112200070071882c0101201240c11081c40340308401d002c50000440e00c2d0313440c100042c8084102c0071704104240800901e840282900038070540703050b10610703000402c0080b181e4200d1060f450810154604003030500c14103980440c20080030f4442440703500c0300c01140d2802000242d520040383c0d10366079040040c00e5200003e460004007034944e0040c0c225010016640d00061030b00840e00a803503ca0726103850031020030500103030102c1c042d6200b9000f000b4481802129408480588422106446107042c0512400305070345030660030300040784024004210480f050001806480c800c00c03040d61600b00f004c20307140340c0721 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 581977032 1250 581975782 581975789
    0x90a060504020a210c050307050a090e01080a0213090c03020f130c080a0c2c060d0c030c030b0111101a060c0d0e06040e0c0703090803030a0c031d0a1e0c 67
    0x70710031007003030004905100d01c4c00381c0c040160b0748244405505c042019005100280c62001082800910f004602e071207020714074094030303040403000050359542c2481942d07041d50881c16441103000302c000701c40c502d925100d001c80306c07640714251104040c915002c01101480b81041e0513001940140600602a8a41704082c986900d503115200241460429501140e031a2702d064010b1000c03d42c20500c044c40b944080782c0d4002108031303450201009040210306035000d001080710b40103041c1015840c0443e0181c01000c940302240d40c00300039080c4948011509201d4942140066401101000f0007640158004440d240c1380d0030702c484440da4a11022518a6010030380c514003e410100445c01c2d000d52004041c5034966040714860f04050401d207540b030a00b2001b1307011a04541d80041c0040425001d0411007008181a01c241d0780c40c0d150001414016042a0000301c1c0040d1500c00180d41c103031121150301c1d004a050000810b80604999900d4851140070300c0340b9520382c0000c10300b20000401411000c000b9 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 581978282 1250 581977032 581977037
    0x1811040b13030506060102070b09040510030b040f05100c0e09040303021605010615140a0e010c0f061b02121206040e0712031d0f06030a060e0a0c090f060e090a060504020a 75
    0x10600e54100f4900386640a80310300e04541080c401000904000700659240c4002200c0014054a4803c0c560f408050103520003015100303050200800e0024003425000d44a002d030051701c00a24505107100115001c1440c084045583d103104c030000703400e0800b0b0180e840b91090400515090340314050701d2240c8244034040311a81c0d1200720a01081020801081c00c204450030300b260400d282a11800c018081d0030245001c1003012040000168031400c03000076095000f0107900d500c501c00341000000740c0508507800c0007041c1015503000441e480068040074030b4805840142c2410b100c4540700210b698068107150380541c0f24036205039a91400c1c401c01b0018040c0d1070b0301c0c01c0100c00a1a01070031301050403030046244c0c503414040b2280707a140d54058502d0f000c42221200d0340ca41d500c89001c8018003c0740c02070f00359148207204120b0030740780ca50705c040b4020039036840310301d03055a40310751503408000c0e00e008040000c1c80001000d07003e800d02d04040381d0440b00300340000c55542e80726001305007283c0088958000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 581979532 1250 581978282 581978317
    0x203090114100f05151e070b07080406051501051b010b130507021e0a0206031305250e160804030c150c1214070f11071403010507091811040b 62
    0x7200350f40c0c1c58a00014038007034540c481e52854141c07082c01e480c0150040b080750703416070040c090f00100c811011510701d00d920100c1e410b001d00300b81c0c1c4001c01c02201207401b100c00510740070206a400d14050740030510003d0582d115860700c45041d2800e440c030340204401111942d25501405110395800851950002c10040d002415150440780207181003106840490705008050030340900c008049000d00d6104d4060f07842c82c0e5252107111105004a1040360090220701416004171031040b00340b10500d00701c0303144003103d800300c50712600f0155159005941c40001d200b80103540300ba540d4065034000341c7c09030003800c01c0c210000721600c030040441e5582503441d0740395554442c2281c0058001c0040e0020042c1240c007040984524260905140c401500e5681880560260541d007603111b0020354003080c145100340c0b120031741d491740709800b50b0310361402440c865400d10740080c55061141000c101189c4c9010aa481000e000441c0c58004144200805030616070810000c204075103442c3c024420900d80801c901c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 581980782 1250 581979532 581979539
    0xe04050c191706100512071203050f0c0714010e01020a0609020f06040b04050a0b0c0307170405100246060f0c050901090b16061505030604050d020f010c12020309011410 74
    0x2004d02010340045101d0f000308040038008a00c001118419100041d05061107400301c0d050588250241003048002c10300000f9848054840201d6003a0440707420220b0180c07610400401035078455400daa0f10780c01030780403160340404282c094122500c91030024081e15260040c0e0701c0480d02981c4641c014281c0d2010010307040010342090003000008201c0e80c801c803820581c0010145d070300c0340314510f0040e00e44a2011480581c2040210490740180002000544074401d100d9000e501e80101e0484aa10b84103006896540d419a0f041d600546000c00d0303081c40c017007ca00c40e119500000383e42c0002d030703143c66458044560111140c81a504881d00b141c80360380d11429900001070800c0059000448003031024000c003111440708a4520b0411640320001041542e9a1119060a010180d00155042c032907402400b00380308c0046103442c0094a41c0d800d036006050900c654034213980b1040750380b0000600e2244100b0401c00c0f0b940c0610340200031100041a1514000058110094107481d400034044200b64200f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 581982032 1250 581980782 581980801
    0x509041802120d08090703030503070e210f06010b07080912030d150e16080105040e3f03060102060403051606090c09060905010b030103030c03140708090a0e04050c191706 75
    0xa45c1c400c0f4403200405060b81150b07801446408080c00311401d00c480540d4501e21507542e05402070080b1040c81c40304486045042a0681e04d8241c4208080c4070300601e400421100e9810742120040d982240c41c3c00d241000c5e1109018928105c1c001c5006140028001543d4038040d034029050640d50000b4118401420001310701408040600108000000141e41120b859080100f050448104071000100b00f80950312490400d040c508440d0210500b00c0820350103040e020140020100e1009c440341c05a6100303103481c1c1e165100075244107000d6801180080c00003881100200245410700c248054001c080d580c6010544e120000304582d003643c580418401c600c00c80c49900014180c0081c14071442d450400f150000e440180405400c204084040d030082c0f500840ca1503900c14101e41800b079407010b0a042034100752f0020780145119040d04000014a50706140c0001c1c000c3e908000503201c1025503904200505891000408074100031281c005224070b180501e4007401e070900c601404042c541181768 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 581983282 1250 581982032 581982047
    0xc13080307022707030b0a05090f0f0112050a060b18040f02010e040204140d080c0313051806030d030504240f05010e010e01061d04060b0910020d0509041802120d 71
    0x1003508060b640300030355a0f210707201d00303203550025030301c1c240090081c82c010041226068240c0050fa0049602d005002070986011039652003050566040c030610f0340c1355480351030340d001e00e81d00103003003a4400d00d42c00c0c001c2209a4040c03500c403000100f01c0f2140842c5d00c01c00310704080c400c07102690f0550000a00009550b08100c501486c05001ca800710700e40350400c49103031071401d41014002d005000502030034003003003060f800300d03201a011742c0d08803500e032402c0282c40c1c03c1506a42c0070381405155402c84014910407403c11241c00f94100034003038070b2a00d440070b504074004c00c001002950300301e188000010303902c4101d4841c6d0218400510000c9101940640141c0548006903c000317000c07144e90004200c0311400411040c15a282031400c43c03c15400520390328402d50350090300c0303940b0a00d03001c00060422420b800600d0390000a85a003581c01d400c54034166101c1000786021404079104001a0a4900d400c0e40501409510700d8103c4081c0c01003500842c40600410141c5141540482e141c010f8550f0041c15 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 581984532 1250 581983282 581983309
    0x30b060a24030b0a1d190213030c050d080f0a020a0819030e0303010b0f0c1011041502120f07020d050102120f0a0603020f01121e020a030e01090203030a080c1308030702 74
    0x341003954078900a031008030002030048907526010a280032540c0646c13040d95444003420511820b5443e000d20064185144280e403100700c4020409440015803400c02c0b91080c4001074002421900b442050301441c0002d40c8284205011401811a07000000fa164009003090000c1c811032114441402c40c3c01500700c03545100c110309190300500040100815203000c441407044035424141d1281d840c8940713240b401c1d9403401c04c401e10380e0070120020020100d2a0240048800703001181403062890314060741c45440741c66410031100c42c10040102031010a01c000c161051000e02206826201e07038403480c2c01ca0300a168030251240401e02800100078268003441d0b0404807030802046082d2856000a001900d038010683c1031050850300c0040700c0e03405912180a00c20300c40302e6810501c1d28049400d0095000024010120746001c4904600320300501c903001074103602030015480e2201115050f11a100c000340801061141001040d0f5011020440c000c001c220300780096850709980d104100c0032111300a07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 581985782 1250 581984532 581984539
    0x501050708041a1902011a060307080f09030706020309010e010605010906020c011223091b030a061a0d0804053d050f0a170c070b01030b060a24030b 65
    0x40d0804541c480c0202c40494000b02c442004510f14842c007040e9a014181c030031400ca20f9a0a40d1290b0f0b181c064000041c12030002212501e2032180c40100501c0e400240d52a400051085001a411481c2800100d401c0241602224200b082e05d81d100810f03684200c4410300b03140d442d2645551201c0090083d031000d070100b420147d44481c2040e40080d40d500000400a04229041c0e800e100c050389940e01c05044c118090700603002a484001800c01c40700400d4909480d507111344c2c40c14460f01c1c1181e05110740d41500003409842d11400355103551010742101c00c14203000140f00004082f450f0b41d01c409505030a031050500035100d0340740008021081c980400d002d0440070003010540b0446905a11000e403881403030641c103c030341c4800b4400f200e01e0b008a40c8511070a4100140d100d044075044495503509041d41c461800840d50b8550030f001c951700900c00e0040040c03201200600c0001c41400c012980048003030910100305584148044180c0744201300c900ca452200b16400c01c0c4203502d801101d02401d401e5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 581987032 1250 581985782 581985787
    0x1d01020c0a050c2403130b071805060f070f060b0a18060602010b0d030f0e22060b04030221010b03150108060f1b0f0d02032d040b01030b04030c05010609050907050105 73
    0x3458545882201e0b14034204c0c84800000065183c0300801041360380d9500b01d125056140b0303249401402200d00030f4840090720345208000070b0146400e80444400480000006060204a44e035403500900041011503031180c513000e91141c03644078800305000415035120254080804521114200c0d210f41d04401d0071a41800508601500c51010705001c50b9410715000e40b51103001c80c42250b5181c04002e01507480b9441c0b030340e104d0400550f0704408000c250005c8040108981e02d280040c55403140384002034104000030030480307401440905000c0c0b0503000c0000403810105072030009081041540b40c840e260785800c4018400c0c1c0100700301d9617500038900c140d00c240320300b841c40440280500b0139007040301005c00040c1c18601d011038241074600b80c010160080d500c90810356910882002440088000b0003020081211031141c0c0e507900501450701300746401080e034210b484000403820000c20650900c0200982c0f01c00140c000d11607100107188040f07000425003050040e0a09200060340400c1c1042002d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 581988282 1250 581987032 581987059
    0x403200a02010807050307021e06060f0315060f18010e040c0501081005060a0e0301110408010e07180c0e1c020103200301090e07030c0909060f090b06041d01020c0a050c 74
    0x806400b5130004040d0038078946969604404030f29020142c92902c1110b501a10361010700640059242c0c000c00d0300b00c420751403d01507130083c903581e103400d451a0340c2514001307004103030141000a085500c81101512100e681402c4002c2108280c0082e0300c003084103000c1d442080103004000c00c646001e82400d203030180c054148a410b2100d240303030300d01804e480fa8100003000c0c0012070240c05100d02c41d4078068004d000c0700451056420903500140b040e45202e5003021028540c02c032022a2410503600f940701d40c070414641410100000303041004124040c41813028600d4010307075170503111243d00c4101d101c08555200103440014107442c02800c48000d00b464150711303681d001e0040c409030380c10740b0b08604001819651a6540034071b0080c180d44040c0c00d10702c5e40d01e000310715200250040c4010501818042c0400208035140c4401c0361941003024041d5040040481c0b050b2410380c10030340058255800002240c103954403201c0c01c81e030084107c1000342e4005500c1c8801c0080a0101c94504d640840340801d59400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 581989532 1250 581988282 581988287
    0x3020d140f151006020d08070c2607060b040519020c01060b073f05030714030c0901080f04020604120524010e06040605031b0411030403200a0201 64
    0x500018041040d10500d060300c0003082152000920412040340c40c81c0d5461500a9070485040d21001500d4100760008100c1034000a22108030380300c5039030340d00c5d4a60b4440604440410003c0c03000c480000e82ca20b0389540c1c0100195980a0fa518080c4c040c903520440c03854108112032182c1080750050741800101b10510342e60710817510003103c00b500056036401800d00804e005000e107070002410304001043c10802d124065401d222583c100701000303100c07004160b0b80c410015041e92a0003c4401c8042445103800d442580559049201410405402011080d0003e0b49402c00c40b2407922200021a40138160769021071351303540100301c0c80317031006c003900707043c3c02244843c8100c1c0a40500c8034803031031405041050800032442a20000d102c18003004401c0b014040d4140300a2258a440381c07880804281603142c24400c07041110801001070034a50b00710380640b1100106001d503d90702696a441480907103180200952040f4400d50300d204070503840c2100c403280990308200c001c03d954000250440140d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 581990782 1250 581989532 581989549
    0x3060e01050f120114040c080f120c030c0a06020c0c090f04060b030a050303090109020f2d0307030c170105070c0f031d1305010e06100e0f0f0909150a05010302 70
    0x10001d8480d5140c0b180030758041407901203151040c2d0f002d58a4030100f043c0081d80100414000e500c138042502c00240c2d207000130b07562030103440041412504011036002090035800c00400721000903006690401081c4111a410549144000c2c0c071030300d80005145000c1c03101406170100030740d811140c2c008542001e0001000b690301c001c0004040e40e5660440558607a8108000140b07294010700b00d0b0742e01e2074101c0780c0d28003170709482008078010040e4019140349850558030074002410358480c80022a9009840b03003c3c00d00440d4070303958160041c1c100202c042000d0b8a025009000401d1150102d0f03116901403508640006259100300424003e0300b00010303010b095003414841c0c0520b00122400d02c80e007442c0d461049484a10b0340d000c20302102a808114064104604031750030b04036170001346ea48040c1030181a004514860780028080542041c080c504404100000503000d0103440c9203102400104648440c00d691804d07159004012071740002e00704041c0b40f44d00080e569000c0c0280d5146034046440c42 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 581992032 1250 581990782 581990789
    0xd0f060f020a20010b0d1103100209091906080a050321010305031e1312060605041b2703051c020703021305130501050a0c080c0c190501110301061e03060e01 69
    0x100c3e007000f40308214409400a2807910001055000211254a00340340140101400303203000340a80615500305c102a4030030b4920070f0030042c10b240d4042c0e560340c244012951241000411a95840710003040d455010003000000c60b100300e004540d01c4400300e907031100500d036905602e004420b2a400500c0094404010368480c2005c070301e089056403046c0c19903c14140100600c00c0d015000a0100250341c04115481da04400c1c05a0410406141c40d001840195038420007491420035251b200340544a2180705103404188085054000288803203030342e254a0403880c0d1040e100b55120301541a400c40052612482e4442c03140010890b05243d5404175026500803030707140b035a0950302e10016aa44e10401b442c007020307a5001d4002c21451511440310401007100095003000102c6401c00140110320402c01c1350b0905e51244001c00c0d801c510215141c001c1600001e0440e41c3d9525100c003100000b010201450107401c0729140c4511035400c010888031403411242d0644105401c0c01e400b0001d46000e241c1c400d054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 581993282 1250 581992032 581992067
    0x50c09060f0d03170703020d0b0a0b040b07020d050f0304151704060b0102030d0c050a1b08070209091609060501121b030e1501030c052e0e0d020d0f060f020a 69
    0xb5907002c1e0a00b5500c4154440e03103020f01c07580110401500030350550042c04500402c400400101805905100000f0141d006000001000700402d12500e142d000150420505c0101214004a03007a52018240020f048480f40e5944c00810103008800d903480300700100b1070300303440c0c81990445201040140003074040c0025291a680d0084505241d1003441110f0190881c150300f802503844201000302a6804040d80f000011030702085a2101d0800d41c24200210b50803080782403e0003610b40800840e00406400144207204090f44102001030110b0420014600810005a20341c03808002400740b5120034900e4144524040501480c0b0a00c42c8202c07050046500c0c000600e01e20340313103030186440f89a804c04a402c25904000104100304c004c0074506aa10658020240c81c44440c02e94a101c00c00301d0301171081c40c204041d1000c860f40b144400005040380140101c42c090000d0b00840c809240a4405030742724680c010040e400c0c844030703016065030b0f402e0985046260607820f0340010000040c500304070701e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 581994532 1250 581993282 581993299
    0x504140a050a031b05030c0a03021006030807110f190e0601030902090a0e121b0c0321030604060b04030f05010e0309010f050d150e0a0f061401080604060f080307050c09060f 76
    0x504138581d0b41c21410240c2c8081103d9456007900795243c0d48008a143c21001031203043c0341c0c0d0925010318001c0200700e0f0303800402581044103540e100c3c00061001d075203640e0014101d5902e4211ba6072202d000c00c503072405080c81c1d240801d007444031031003d1f4440140164103040c2018940801030b141d56441e50703405003124100041410411001c035003016070080741780250b01000300d072640940c19224041c41080c2821700c2118500380c0e10206040d11801b05041100000925081c0100c8481c03918000303550018000340001441d6880303448040841d00030307030409e640d01101c0030f00220410009100380c070b1480f13140340c0095081200c40000201000006162042004800b00b03451040c02c0c095000719900c400c1d039008400303109442c1c04511b81640400c4a0b8200a2405d1052640d9103a4061084c4c80655004490248031424010010740b0311403406005141c000390b5400001540554221600002e0b0034200302542e83d410300c07420032914151007050100d103c2d03d04881804440c0d50740c40e0041c564200d041c1ca603840c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 581995782 1250 581994532 581994557
    0x460510050906030402010c050607091e0b030420060706020405011814010c03030b12010905070e0c181801030c050a05090f0604090c0801050702100515010c1401110403060504140a050a03 81
    0xb9060009514010041c1c2700b080d05101a80c0c3e000340149090f1603ea403102c201c5110740711a0804514803604c10b50004203002c0001c05c000c80e4007141c81d21003856907144508080d01003179001c5a01580301b00c20640390a94041001c1c4a5517900a00414420310a503241e40d00c40c070700b417582440400e0070312190541401401c156031010140039400071060201d00800a0b0005400c10380744601030300156a045410f802004400303d1680c01403c9158014810207022508140040d40740742502c070805550241e0246008271010700b448485000c80d4040c40c030918085c0361041c074103418001c182c142508154411100380303040050641e080704410341e0040d4100d502141110f038a081440711010590440406942080100315440c0d40000d03410316803125401c07082081d503480c4270030400210a00a0744d0350015048441c080040f545480e001c0904014402c0001100600125440c9203a80180d000311012521001040240045030740c0080c00168510007130140d80405a64882e1201115800141406038605201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 581997032 1250 581995782 581995787
    0xe0a140321120610020d1b06020a110c0f130903050c070603060608070503071d12150402030d05041d09150a0f05060a060c0246051005090603040201 65
    0x441d0008045154110031000030003100a6010020915840c00d040d8089015418130080382030030080554041c0070203040f4080c040361401c7c2c1c0750080200f619544940c80001c9807552004203c451141d0300ca131901503c14680d00c03410310042e02e84c4d2074030445032100185016104da55148541400e0f01d07000180240c80ca19054695028840c910a098401c411000c9480d90f015031140e03055416030303100e000041d51020030803111031200326450703800240450040c15800d40f00401c0b420340c44600902e9041c00e2078808a400d4600001c01d617441038220081c005020030740c1014040081c00c0102403420928050a081222103c02104040b401d141c0b05003100003401d8080174000c400b82c3e010136503481d4100d0304244441d0409041604a04a4003520703202c01310340e071490170070312010481d03d06840d96003c00c0480d400300541551031280310180c0041c1c00f0007610245100404441d03000340b980802c0c2c0c0c4500440f8528038814100b41d044940203015203450b95040e150494156111540d08541895495444e407004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 581998282 1250 581997032 581997043
    0x40b0f2d030106182403090b09071701050103050d0c05010b1804060e0705130c030b03010903200606011b020414042d02091303021501240e0a1403 64
    0x1280181101408000802240c54001c0d0304079010782d03441004900084148610603503491180c0020b21000388004a80c000101c0d1743c180450445090002c0c00e90095240c40604001c2110303240095085440c01740b2010001c0080d0940184924008120540c10f40d85d8a6555040800005040c0070001181c101041400d410000c00f00034060036508500b0700c1101103000c0715170240c0e0126000b509100d0080b940c0c1000040031740441e032005202c01500104010b200004140030303139820b070415440300c1140b450703038030240100c81a1700c2c801c0e61016108500c4019800c80f40c103400c030710360045800c075400340101680e0204d4900520b00e8a48201300700c40c40a03100040040c0080201c0e801201080c408000c03e202004841c0d1400340e0340e41d800b1600c604003554040390f0b00d42003a40000d604c0b01c05400400c004c601440031a0409074824011240001d041c0c580111140000b6400301d0100d04410320a582d62717004800c85401c941110b4288100c21000403000100321190901640140c2c8007402c3c150300d15a0f404210 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 581999532 1250 581998282 581998327
    0x9031e1011090a06020c01170a060e0103050a0b160e1011010c031e0204080619090206220e010e040213110d0b181e071e020c15040b0f 59
    0x2003250101c5440051030a802070310105203c0c01c410000051042d002007555412480141d507039849034860ba24514200c9480900004900c5541c0c1c0e901140720110400018040c50043c0d005144c0340d803107841d044202980092100007648002c10310002e8032508990840c1035032108840c000b143c50a000021601c03030b40c803859400354641c01d208110404503015449104401d90120007440c00c901066100800d9100c0c41c85824800e0384200009a903488152882c041c205c0d201030804901e00c580c0b500040c40319041813000e02d241400340f203414070302001d40603c2140100b04c0c1011405c0e0940c5841c4a6a0324010020b10181c00b0b43c0d9101c1440f003e00041e5445203042a4040316156200d01c50111080000c200107070b405070103a2070424000b12020034550903244a4001100138030781c541c1d00300201800041c40a80000103000d02580c00d003601c00d03d415171004c4402400d60060030801c000c44100900c005100302c41c9400d01c1c2c4104020f0280d408002c04036031200c02d0391604651380e0348001c3c401e103a41494021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 582000782 1250 581999532 581999563
    0xa020f030106080726090d030501080c04110c0706050a09270e0a05120901081506041502070b040605124c03080301180b0604050904150e03040603060602010209031e 72
    0x8800e601016617410b107040c0510310000c00c5a088154500301035040710000e0003029070a6201c0080c81c4050b00d065040000001820581c0c00e0a00c0380300703072207545845a01c2d000600441e1001c030399003007400d0384054050003c00d40a603101202100880404901e110207942d12106541c59480d0b07a20040001c00490302c80302c0d40300049408450240388010308540100c544a40001c69843c007042a444034403064401121001700303028642480c0c50b030800c542c10140d96400e0150300a03544002504100c003070141c0028011034072603540e00c0e15450004d0481e600003e000c14081080e80c088261004498949034905181c440054502c0810b5507110840100c0104072191801c00041c001200300840300c0c014504981c0d4407080c2c410301d4440561301130251440034181e250003034014071040005103818080c0c546c015010f01903070080d00c0311800440c8240c81c10126800615400060100944c81d0702d845130b0300081105100071800d040b181000240c54900400c180d1001521029140c51811801d01060380d1342d14101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 582002032 1250 582000782 582000827
    0x307170705041706011d06010216090218060c0a080d09051f0e070b0a120212090a0308060f060910030b03030d060906060807020a0b0907121103060a020f0301060807 72
    0x800e00421640c042d000312540984200f6a4031610000010301c0740c1603400188440400c11460280c60710781c4a00104898114440c201c1010907600d0030b0030301000031300048100580d484415090310703090051003a04071406205c00304045da6042002280720101194060b2101d60307030300f10b04c01826002d8000114003034001e01444040407040600c1c0d10a20030605080d0500384600c0c0016940380d6164440c030705c03c3d003500350000c00c03074000b401780700b40d40c5044091030b08440181000401554246030000445a41c1d1007540a802104140360b0080c03032103170344000202d81114840740300602107480ea01490500d140915050b110a134801406600044801180a0308403030315001c0540d6500050b041900c0360611151402a000c102d82c5c1c42601d2891043c03d858004100d500e21907030300c0c4105290020407040c040e005031200880c00500c6491180301d80d074099a0f181c00b001c200d0804040c10900050305c6c1c50089481040034980d044103400907a81140c0e898108101241d46402d42030795291014000742c0d00002d0780 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 582003282 1250 582002032 582002041
    0x1020d0c02031e0703080c090402071a06010917120c0c0d08070b060f1e1807032403030e1c080304080c011d0c04090807141f1b05030717 60
    0x10180c41d00c010300c91280c501040f03000710ba42e640352040000150015011030000384a005606c1e006080048002d03000501e0701c10940c1341d40c0480d5140a80010300d02c0c00d40014016550382c811802c0300900359010203518403042c042c523000d58405040038400c1c2046008a00b8440d06101840042007440c4040e0503409003807114503001e01c0980c4107100c11a000302e05000458918107020150036140d909c087c00b80440c0f07050703003064110301c5001d907161240d00118083c6920b80c4d44054094050144180d5280410f5003039103e040c0700311000c800e44458407003a521060400110b640b0442d401c24901c801e4a8600f4040e842416140c807204c1030f1800503011000020501c000c20034030800804104000034000c201c8522192100490391550310000e212541c0645402c00349850590f206982082c030503910140341c8051a5034103500f40c0004403103502542c12075000d542c030075405c1503011500c41d186020208803d81e020005c803003104440c034247c44200417021001030718180c0144c1541003010498603404005281 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 582004532 1250 582003282 582003287
    0x240307150906110109052a0406091a041104030611040902030411040501050609150c030912010608121306030f020403020612011a0c0a0b130f110f060408100e01020d0c 73
    0x2010301c180300008040f912401c45801c01807003280003155100c4041d221340200c80360f050111080071909904801c1c008000000300d5a0b59100c0c4900070310f810240170646590130008850500f03481c1172958000c1d030030005802c0140d00580120b80560394461000030b080301140e5801841c03070040360000001c0c20300c00410305c4280001c01c0c48001c4c0c0350030102d400b4446603885206008441c0290005150400551144005c0807a0a88c002e000074a990200f26410315448100144070858441c00c00ba03680c0e55201c00501843e40c060102803020105e884a00d403802d40a084114a94040b0b480b40900300359450040c00010303001030b01164001c6030020107040e1075850a415600f07a0300000c1c81400f004005256002152030024410340d035824444e44050207a0501c1611080344d00100140120a0014055003031400528100100545a40600b070180000c500038000d000780c002d05149981d10074641880100002440003813181c9150410f05400716140d021541d80501a0241d140e07241022418400f03004612a0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 582005782 1250 582004532 582004547
    0xb0307051605030424390b0105190602120a0c0804180c0e01020304090f061d0108100203190e07030204020307030e1209030c0108041b03121724030715 66
    0x320015030410790366101d448a96543c007411040407001c2400c1c0c0120711001c0003c1040948145010303003101e01b050425400b400380071040b040c030440360b0540c0a40140501e041c2800d0750b070050128240c42031081800d000020750b9032440c500e4180200f03000022a00e505521821011017555401705044c0c3c0c547d6211551001029540010010118508680403402c6442007610301d02c983d0041e0055407800d401d00c407158000d001a140405c1440f0745640c40060340b40c94132110030125914400c0555070b15410020940e0400c1010304810034040d0062050200b03507100d0f250b418045080c2d035030000a20311410403000d4104001e80d400030b58814408001c011640350590000e1803410030702d10903100e0403004104801081e004000203550142c0c00004c010000394010806680c01c24000c00c1d0001900c040749016400305001900103e4603010700140c241c14a176040f81d0013141e1380804001042c0c25151140ca040c03c07542c06101c10440071051002140d02948042c0a500c0141100b568694032495440d0800b600300ca = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 582007032 1250 582005782 582005789
    0x12030412080703021b01080703020c12030103050d0809030906250b040302010203060a0e040f170705030c100606030e0628060905060901080a08091e0607050a0308010807030b010b03070516050304 85
    0x1030040ca4400d0303815404482c078217200c10300140c583e601103807100039040b170081d04042100391051066240120701c207000c02010314000c1d0f2199004264501070100018611a0054080300d03490317005200810041c0d48520540d0f50f111000d040300880441c40e44110700f029080400081c100051010902041c0355041d00214801c1c00c0a8804140550b56403034608010700040301d024101102c00c028400002e100f0607003640812403e00c03a258207207035030303901d4050840e07000941580c1c0c0f80c0e02801c01100308922078020140100b12a040401824107815403c0d9140c28004040399000e4004c0d40c0038a03480171088440b80300f03600c00080b0402c00c841d1103001810090809943e101d101312140400001e00e8100004c80b6480381d035000d070840342082600b50a0220040ea1b040350700350382420403141d441c0c043d01c402000c1c00440d802035008095561403814040e2007070380c0c180c1001c20180c0100e0130600102d003802040781d0448040c505107694035680c13508221198011440301c150007541c1940c07160213201002001c1c1c41507 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 582008282 1250 582007032 582007037
    0x70f03030b030c0f030a140703050d0c050601050d03020316061e09110306060303160c051005120928020d06020c06040b0c09090c0a0c060c020d030b0303040608010512030412080703 79
    0xf2000d01904210802801000040d0f040e841691030100080c400304000002c00202d06c04c480140c0e4580d40c0e510b0030300303c2d440036500000b03d103424584103108080041e42e00504003070700c040040007020f8400a445c0d2007007400fa000b0810941c1482001c00031994058080440d02d5103984005002a5801002030900c1c00c0b0281c9e00707002d4550b4002d10070700d00490820300400d4004d0045151000004030310b140f8062150342500c1007190200d0005e03164454040b19a0000324559600381c1d80c2a01c0d515910410201900d510515132024804080c01184034143d40321000d64682c414040e0341141c130004100c01d169020091a16001140080788254001101405035209030403110f40c0f03560b2124581c01070301a802c40246c1c840002404141c0009018000b48000f10740da05d4400d0f0075000c01c1e02c4010548034284240c030016401480f0080320140c1c14450b05e00c00703c2085010354541881d2680c000c0454806000b820b200d8000d00050100684c03041046400501c44448206440241030402010b281c1100400350301 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 582009532 1250 582008282 582008293
    0x204080109020111032d0409020f030a18080d1a120a03091a03040f2f240901030b0117010e0106080603010507090e06062818140d020105070f03030b03 66
    0x101038001000b918503d00d542c211034502003004448030136615004d207001206c01c08040001084950f200c0c00207211858052101e10359034100a40200b00315000500d02500c102d4000f54410b0004022030200c0e00fa548a128020442800030712a04008400c00c000c0a40d200d0030b00d800241d29104003040e0790100500907160040682d5803841120340096400520110034081040000c0000d1502c2144004141c061400c11003010f190f0715600703001881d11030740c0b00c0302e403910803861000328500f41036980600c0389100381000700b03051070083c01c0c7d81c5401442d01e003a06154880008001ca07034403444940c2000c50384415a55000e507528a8101c81c032034002c0c050040011030b4034001809600301401254058a85a03540003038051822180480941018004603885201004010501891a030040d03003515207440e00010f070407055400c05481025200d82610f94030395900000c0228143c1000c400304a910f040d10f43ca2512419440100c41910603070400070208000442040203050f41f40d4050022000144c0c00c941 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 582010782 1250 582009532 582009557
    0x105010f0f030c0c02090a0609051315180f0c09050a0209061903020c030f03061c0302150406021905090a0506130b0d02090409052404022107050402040801090201 71
    0x129803400e00318125000c2910903498401c107620950180e29040070394070b8004142d040640c00202c0910040e201c440c082c540b04c20080c03000203464400c580e04a2401c43c441c4c60b0411030755482149080c000769540661075964040c1000c800c45000e0100c2140d940026010314600c02da140210b1200701c00e00030f01440c140303031900240c00e15025108031450500c0041c10f007410b05400c4103440100c0700c8545114010580c0030f1183c140d1182c401c00180030030340c050390b44284e207038604076091200c3e62050582c0380c00709911146211000c25001304280c00c0c1111031500e02c610366550750030704001038464142d0740c8500380340c0041200f0b5a42ea000000c2c05080d0411a01e024410b0390b10b03000c100c0c0e180111300607000b000740e2000d01000107a44400061410380c1000c0c10142c100300341a40042c0072218910300540b06500280c000d20150030b46101e040b9200c5800a4800c0306c0d50500d500496450b1041b500e00742c840402442102200440030050500100002481955160b0701e810607207020f0320381a1012800b0031030918814 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 582012032 1250 582010782 582010787
    0xd02070506010623072013060305100506090c0a210c11010507020c040209010e030709020306240a030218090103050309030111160809060c100203100e040b240a15020105010501 77
    0x786007003404c44190a0400303041c0e40f18030007151001c840414002104107202055511110107041d86640c21040018240b032550070309900305801159412502c0b40b400082202c1596404c0c3c040d43c12080b0510b803c0c0e111080780c10191141051100340030340742c190452924000d03500e1a000900d0b4203100780c3c0d9006090000105c01c5090b140140d80710340242c0c00200c012140c0f41426030251a031641c051404010300c145e031101190030300060f0340040201c140c0000801c201c0c0e0520025080440320016840f80c00c200d060003100c80580102c4800c40101600013984901807e83e4100c0d458071000014064412543d483c42c000365241c0c070511046002c1d50070600041c1d4104603803016070f01c0410780019600d0606010b039560140980c00f00c1e0405d640040f0500c5520405402000b501584c164100001a501c0c14046170144401c806036000d135814442c500200b100049000348410f80040001c0a080b20035400303a0341100c1103149415800da040f109984000410024450600e03003034020b1038000b0080760341c964004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 582013282 1250 582012032 582012077
    0x31204080a0314060d020108270c1f0207090b0d06020a1e03090209010e090f250e04020d1401020d0905100c020703230106090f0c17060d06110d020705060106 69
    0x151355002180b400300a000d54060f00c0c1c6103a03c07141000b800005642044410311054119142c500d03c983c1c80b00800030914144107070714248500d100403200f4409144200025a00c041600614480588411000b601d64595401da00d001c1940032100f0f40d101d4428410062168581c4030712980b5455021405e030345c0e8640648240d0441b503401410b2404140c0c00d0031504403600b200a880080d040c13184100e0401101c00901101d002da00300000c0d6030980c7d0081585030318081c03507590005151004098207001c0140c3e58445a07d0550741d02c280c00046a09030710314100d00a00400319010700c2107040600c0c05040103408104802c4403003a0960800910b0302c0c00104076520704040c04000c0c0a100385210f1100c103982009a0820b65490354000414240d80346e034100c000f03a8040d02c401d04000d41d2943d80c50341038603410050840d03000e104050305580710301d4100001030b982c0c02d090101500295a40302c80d1422040780c0c4080300d145240c0d5540c1951340c3e096502e8083d40c2c82d0700034031590001a0b101c007140003600b04c0e24900c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 582014388 1106 582013282 582013291
    0x61a0303130e07090b04050904021212040302190e061203090a060c060f1103151801030c05030607090303170601020a0203062a270102031204080a0314 66
    0x703060b04020030282c0340b01d051186104c414882a5083d109803403c440c400c840d0350300c0c1511940007050300602411810b621600034030000032440c41c1e150f03000700101d910030746450408001440600c010400b8a01a05041074a60030100700e0b10700d400c0e29502d100e1842c0c0002e4074a48407000000030900700d000d50088000c0f40642980c4014007000780304108000900314070510071710b04180e15905140c4001400c0208920b05104190141d442d11140c410f00004502c070480510b507101c1c1007541e10204030b849014428032460300000c05052003160340200320381d4140c031080224518a011f54101c4280140254118401e2580040140e43c0030011180681c0c210b43c003154440079405007646043e00405610a9081300802c590552503071039024005404003203c50005c014200100101e00714452000c0c01c0030f9881c000f40c20300c020301c04550001c10207400c0944080100903901034054003084012503 = true := by decide +kernel

theorem cover : BRFrame.Cov 581834532 582014388 := by
  have h0 := BRFrame.cov_init 581834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 581834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 581834532 ≤ n) (h2 : n < 582014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
