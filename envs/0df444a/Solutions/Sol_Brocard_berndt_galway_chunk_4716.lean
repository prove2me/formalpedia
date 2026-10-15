-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4716
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:30:24.579398+00:00
-- url     : https://prove2.me/submissions/fbe57fc6-6439-475d-8bb3-3a155bbaf35f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 848021582 ≤ n < 848201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 848022832 1250 848021582 848021593
    0x20d1a03100606050a0c061104030803040c0b031b0903011805061f15050702011e050c06101a0a181203020615130b220e07081506040506011101090602040602 69
    0x441c80e1004070750701845108086081401340c5080f075400f50800904640c007800380400c0c0010b07032504019043d0301c207401c229070241022060005000040c076610700a4980c10700c0e00e5155090180c1ca11300b07426205c100e40b0341d002e9800244c1500381e440039003024452685000d81d02e069420585000d03601c0c1c44c2c0446400115421200d084140038940e40180360444010000b241d1060440381000c82e82c03648032110603418003082c0440d000c3d00e01c0c0e001e5240603e02d003850303844c00d403a010114040340c01e011010340b05074048244520144507240e004407402c010203a5511107a5a40d1a00300c40a03a0b414844030a1a901f030040c1ca072001809141080440842e1403081d403d44400c0e07920f004002e0a0a4402101c542c0c1100080c20190715003201c036030220707490b507030000c10b0715004c0c4240348100301040c03095034155581107481e04134040e4055004c0101c00007410310300300645180b000d00c407440300303014100900041c40ac94458003c501c02c2d03406600d2036044640040c00038000c95100f170801707130042e41c06842481e0052181c7e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 848024082 1250 848022832 848022853
    0x702010902090f0705130e01090606021b0621090105041101030504050703030305270f070609031a0c1c0c180b04180e07290c0a060f020d1a03 62
    0x180310301111190300600040890701e0780300000e19922401020f10007402010807040c82e900d4280d829a50081c1481000c1100039810f0041003020707540903078429429940000804014035811019100c2150019990035880b800c45500c12412110f00c0c5048000504d074030828007280c00c0040d01312034803890003101e00d8000400d401004504070795040b9405400394000c0758041c00000c5c8203400c640c0e04440c001101c1a581583e103034140d05e905030070f501015180d40c01442045240503090118200408003030514030080e030b1642d00c94003c0440c403040340882a4100000042c2410707011001e84100308806030701040a40c8030441180002c0c80071408a5012600282080c007d8401c4150b546003a40d41504000703007003c0c6001c1e02c4c1c2112010701600341d103410340c440340116450601000204000c00050341d407501125001c500c041034100c01c20441c00750955081001440144002076581c0c1400c3c0e02c8080022900c7d18080000000e000e24894401c2079403c110041400d00160300000e04001811810769541092 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 848025332 1250 848024082 848024087
    0x906030201230306012012070b0a0507020a0303090602041a090a0b0c1b12151b07080412031205011e120b011a040b04060525021516050102190807 64
    0x9900b503005000e040300300005416940700d1040f400825400720054800c1ca460220035909140c508429a0340c50b44021030315105200c1907504003504404000c108020608141a009482b86184a405024545c132120102d0400c040e650494000f0a02c0441e0002100003c162840d89a4000c0011030321941c0301c0713040800c0c20802d850803103440e59020401084101c2050020007090020040e60541c010b0480d84542c20641040c170003441c0915000344a400c06181c21a1a0a44840c010b041c80030889014084240081e1080c4101d50039114183c1032565071100300c1c6000c480440e003400381c3d018050309150000640a210038403540558204c60170015071940c51741d0101c000300d840e40c10058003c0c0060700c01080b0f6906c4a50480840780540c1a01501c0d06496036110342c10f590055001c1400200e00044904800105500100d80c401000c10002c08482c21500003c1280d240c0b034410715810040000d24000070240e5610b810b01c078943c080c00a645a4602d5251441010804840350300031900300000075841b2403 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 848026582 1250 848025332 848025377
    0x41b0603050a14070801061202090a060804020102070911090d11120c100c0b01090e101b080c12010b0a030e0f10060b03090a08090f0d0b19020a021510030c0906030201 73
    0x4601e0f640d11605030301c0d24130111035028400b400238014070741c2001044515156554a180580000d89074031040c0e092900c00246405802d5000b00c10503460103642e000840425011651820421182c220b00c120303143c02c00b048140e030b084410951060f2a13079070800c0600f81c041803a11602c0c43c01c40d400d203148400075000b41c41c0448000c5c0d0051450101c1001404291300f1540552591025001100c91054a01c0b601000311012208030b1481c0d501e52038181900180e011910960000404c0016030400b40100003a0200700030600880041000104000307000c60b11942c0174400105d221001c40c0d00c00c4c440b0410240d00d9002d54610403402c03030b0410b5404030f510070b10b040480340102150130007050100c0450b22090010380126160740d512401c3c05010075030310b50b219402d1114440c061915001c0505166000f050303490303074010310700c11039600500207408580d40104000840820070040e000103503485510200500080d904001c0c40a2031000020507408156409401036a20071303200c1d090500020170304072000b030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 848027832 1250 848026582 848026591
    0x10e2805090a0c170601091508060106090f05041116030e0a09020d06050d080f070c0e19060503060c070f0c081f0b06040b0f0a0e09070f080c0c1203041b0603050a14 72
    0x364442ca00400c211f005a500c5000310342030400109004503120b4040c00e0610303c0c203900103000940308440600040810215003402410110b5040100d04881800541c40d80107014011005410b007900b0b0406050090200b2200c000004101040e0b140d1143c0e4840020342115115856251030102c01103414202140d046e42d0300c980004000d424444100207031005644030348030888000c00700c10400a0342c6400380450b10300620600181d05030300040d18071040304541c420342c0203a1280d03000300244240d203000c840484903440d400401a1a0a45981c02e2003000001240d02c0340c00700344154160b4002070042c02119604007202500305100c0f000e41c85e410021240114007480e4480d50f0204048030918450a0040140a52a0500c1022036982d4800103600c000304540380342c08501c4d01010745107000c2d8070001541e0b0040b0407680c1181464100c20701a90340741004405560926400404201170015101d13079040d105000c60551038526481e034400070090b050951b001c580403800c009581c0c1c040711914941a00c075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 848029082 1250 848027832 848027879
    0x1802030601030b1005060d060e072d020a080304050105070207081218030a0212010e010c17060f15130501082a031305060a0b18010e2805090a0c 63
    0x2070790039511041c00c50f01000e0140005048440c40c0000d4035203864010b0300c0b01510203280000e02c10b180c00804521044000c1c010001c2202c00c03803803e07a000744c000c90001d014045807101104540c512420503440d100c20b400300a040c40d04084100820403005401052250b41c0c20307401d44180301c0e680e030b03001996100d080805e4119004d0a22503140c6c02042401031440038600181210400506a00071a210720562103a0100c5039444540c9280007040034010791a81500616041700c400070115042c3d1017050010340450300c10011046884c40703642d241c0044003441c07017405d0340c00d40d03992030100c0c0402e000e003d15108560110b502880041e03441c40021440400c50321518035100940340ca180150001680020301d622007201903a82201c010a0081240724402c0d0304e80040090341d80460720801a01c1d200c040510100351081c02c005010311a800d508103034004030f80140c07480c42c4280051ba0903080326060b40d1403456481c5044204045100001883d801c118016102c104032162218102a048220001000a0b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 848030332 1250 848029082 848029093
    0x911030d0516060207020121090b0c0901021002090d0c0f050a06050c0a061104150305010e060307050102070e0a14160e03160611280c12110d24090501180203 69
    0x100700c064000b080000d06c14940743d00c00041c240b1844940201302184000c40360303510b80c840c41c10041d002502c01e82061000e503d1a0424134a400001d6907600d880c20071010301e17500428681840d8581d180701e0000c840d44401449111620f4036165500300e40180b00399881540024000580e03180176100f00c8144144c80b4024140da050a9150fa134003412500e031110240d45410003001424134641d41060382c018089540216240d450060540501a40644414440d0f00700310010003950b0303000903410003150b1900109200550b07450150200a24151103032041e942c08400c00c01205135142d5500c0702c15401c0070f8a41c961040380d44014541c3c2c031800c0d50081907000302d814400b40b21803070080c071080e403041640404070768240070829802160141e442c002c540804811454003400c220b80e540d03902c0d02404003800306540c5c101c3c181c1c03988803104400346143c600030000030f0494414003031410384140d0702c00900c0c41408030354089041c1410080c1079190041c0c5842d464040e42c06861035409484881d0143c0080c014070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 848031582 1250 848030332 848030377
    0xc010806130506010c1202010204080708060601050318160b0327191401021602090c0f1b0a0b09071701020c0705040b010c0f210e0d06021308010911030d05 68
    0x181800f501440c184404034a04200082030070005080100c600e9001680301c038540901903117040c603281c10810030390b00840104441642d01205036580000c103c0700d03100148000d440e5035030403c42c070381604043d244103005003c64032400130700c0118015103c40b1840340c0101d21075903140c1020b02039a181e103075440c0c210f000455900c0c1c0076840c0980b40c441c050183c0d1190703040d840e40380608a0784014551f004c4d00300104440702c25460b00c8181280d0200003c64441c0c60a22040c2d585070407403040e003901e5603883c401da0101c030b0401c0d41e0030069880c02035400f5a51100604000e00500d80d175007040e00c500c200039407001056043d00801030003580e22009403c00244071a0381020100300207040c0300a80c082c1002a801e4040c4042100454000c44180c0900020760f04200f4101940e8942c2c1c401d5144201030080040c030700c544035110b07410394070002c2e40c1012006850303c0400c2040f6014941d2a4403085e115801c0510807800d0207a4148060110802102201c41d69402c070141a149801100c100c541818810516070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 848032832 1250 848031582 848031619
    0xc050a0204230f01080d18050415230406080307080f0d020c060106110c1008070809030c031309060603090206040e04050307060c02030307120522060e070305030a020c010806 76
    0x100b0340c0403400c1c0290612084200450148010b00b11140d55240441c5401008103801c1030200b602c072201c8a1504068100600b10161030030155442101e00032955003601c044400c48000114001e42001c042c0301110340a00461090f240c1e000d241035038030841c601880021700030f800200311039019511850041c1088004000420030303410000e218601c01c2c0d0200040e511240c41030180c14007a1000391070384011261440882c901c0c01400380c609501802d1907409030b4019941040000394040c9091501c04820b40c0c0c4c0301c00803030950040071a0b40c8890320002c100c09041c20225803602003502e444038020015141e4074803084065450b42c14029421030002c00050000440c00c01c0b00b00c1c3d00c2405502140e160550a5a6100885420303c40000050b040481408142c43c0e02c1454511543c0c0301d008103000c10b003091004504603694181481d11030400010f5a48104041504244011103c035800e40e0862650ba0034455101e901004c0b5420060041d100b00615560007a10020300410029001c000c0100300141078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 848034082 1250 848032832 848032841
    0x801051f030e01061e06020c0a0e0109051503034b03090708060411180603030f07021f020a140601080604080c030d0c030b0f0628090b0403030302030103030f0c050a0204 74
    0x304082e5502c40030007003402203411240100c1c0000044404801034a0302800a080440422100b482001c2d0035204005100300068800d055809410001034591100c8240c0000d4810b100d6200d81c15010100b07400030401907122645124210100f60500085802031001803c408070128480301510f01c5115000f99610740400785038441c000c0811078030b107261101e9007240341400446048a10b94018540441642411a01000c580c80781e01458084d50070310030006a1039014649942ca0320900c0850004250740c4c400548611034200480100864000190003e4407056046000d82d100d41801c80300034103417107001440c58121040107026040503183d41c1c1d0380c003c1b41c1d07202d2010000780f88410320080808240c544150700c44240c65442c00035842c84500140090700161550301e6100d5402403044c8a0340300c50070200c14003d071056480c1c808000e11076200640f46050250006040c03010041804001c041d010381c000c6060b0ba02a49a00c0d03d602c442847c115458102000c0042882d08009005c03401030506420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 848035332 1250 848034082 848034101
    0x20d1a0a1706181207061e0e150601120f0203011a0304170d060305031303030e030c061b0304080a050109210f120e30030f190902040c02030a0801051f03 67
    0xd40e160380e001c07280d10031010380045c0070640300d01741da640f5101a0307661010780c140481e4940e20828810380c010343c401c05854030181a0200300400c40b410029210b0707131044441c0b07104800d00c00307810030403601c1c203080c0300c4000d4009014000304c2d0201c400c03840d40340340d0340c40c411ba80c070a075444441800d4044a04006901c19000154a010040d48942010000074001d0014040320700403038107280c840c1850350400614a8424110840c0260000c074021142e40d100ca50450301442245440c0c4500d0f003d03c040e400e855803049500001031400f50310750702002c000e41074202c080c901e4040e0701c110000d4804181c0d41480d00c0701600024021a100c50320546025010f01040008007000100014030101c080041c90300740002c100d14104201e02c410011010203c85006024120f2241c8021904619000d00f11384520600a010600c142c0052134858103035600305d4221404113a8003030010b001da11040702e4040d550b500060402404150000004a400d0420f0051400c80501d0003040007010080000154000c00c4140c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 848036582 1250 848035332 848035381
    0x61802150a0201150303020a02010e0105030705040501270b04030308060a060e01030509070e070203222907080f210408190315030305070c121101080901020d1a0a1706 73
    0x400d0314002c5440074004c402180650081d01a0000c1c6200052550742c40d00710b1141032080038418040c03440d80c09401c4d58142e55081c00c05810298200005003001c0d08400030320604080001004944018004050800c480c465101c2c900795407030303020800002070402e0103043c000030981224030310306601c01c2e0802c40e0000310302c0c2c003540d00242d118402c5c6148010304a0341080541d00005414190b203d440c5608041c00d44014010080c0900f0f00345458002c80d09140c110200b0600ca1940c450510080002c0303e1603243d001040b25a0303003031602e10071000e580101c41c5101039080004015540c4420401d0918810360b8800034051030311640c818401382c3c0320b40401e0030b03008040c0c0d1112104400301d0713591080d1001c0d500907100c07552251001d03c1c0620542d0940d4006010707144c0000007030070005d50a51402c012804e801d00f00400156904410a030081c0176120000c0c0c441e9062621100300c2d180414480446000700f41c540c1854551100c0c15a044456040d454200c5940204001200c640e040700c41a9a03200d000d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 848037832 1250 848036582 848036591
    0xe060d021c03020f0d020105010f12020604081f1a10140f030f04140d0c17090409120908010902130209010314070909050f370f020304061802150a0201 66
    0x49000310115003031118102e015a100b00e8101440c520100204041c1c0314092009200035810425213000502c1030341305460224480310312000440d602d80e020385020303041c85c03001c8031280035034009803c1c00c0002c0c0a250000c018505104140041c9003031203050303401a000307014170044154407101110030103203815140c11004028010300c400c18102e40f00450040d2203400801c0301d40c0c180b9003040800c541801c80300801d80d80c0401a46154207811110140b101c6410040c2c8003400400344012440c1d5104034180c556209142020490400900d08000c40800c0c0c0303141d4469111946600d00c2a0803101110030181d44088007843c1c050041312a50004d20107644189008074030f0844800e01190000710954a00011070102c01c400d0060311018480c440c0c0c411583c960342115818a41e00c59554111201d0450901c40c40a040003540c103060003103900306c06103c0743d408100c0028032001c110025042580c04031801800d001540c1301c0c0050350b400040446030001c00c1e04012100940901106a111407150820755495 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 848039082 1250 848037832 848037859
    0xf090720031606020322020d0b0a06090c0816020303100909060f090f1704030819030603121107090b060f03100e04080409051305100b1305010f17070e060d02 69
    0x226000b2440103105100c09602d80c18000d00d4503000d003030041490b015050fa0401c880e030160795010082c07241160851610401521440080006011150815040c050520359200e05203507008450620481c404048581c4900031404101c1c1c80384015155003004203680c3c00c091014004c1a4000100c0b071f4826500002c0c0e00c5a03c21509003950a400700558032420048850401d111080318144c0d0042d0000810520302390855070340150f14000e2500c3d090f0811a003054007c20382d4002d520100185421204505c0f5200903000c00034254031318000040c40600030004001100041d034092807440e86001004036060240702d40340050640c20080500341c98a8403000001000020920140d00030b40c01b6504040d92076044c00b40714030903250094401e00242107091040e4000c900046080d007964400100c000c6000b0f403080c00064100040754013008120b40c0350000024100216400800440f6242c0080800340340c031810183d919111284074081090038808001911352502410940c041032004120b01001d05a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 848040332 1250 848039082 848039107
    0x1121240d0b01080a021822062a020c030637051614030708040b09030714160b070f061806020a090807050a1a07030e1305060f09072003 59
    0xa03806a0343e103400002c0160b05605102e130f00d4044607058150201034509159404041800c0614100000e5010b00c41401d000c00c001c681000d0745c40301d2034503100c514071011104803c001e10503034880e49000d44601000b80059050204030640b081e414000b240400344d91203090100c0303600c0b20302d0140741503280082010030704094500c20f00b80506010b0b0b100844400301820050400e03020070034030440041c401e004000b1030942c0610035540c42540869844030782c0d2a14800c06d4914064404010710349820411510748035940000c98144190720940e0100c1100c1e41d0302a003d58074498198050b2052445c41018004287c0d1a040100400c0200103080d0703100d000d80d210a0102d0b0013212900000030300515080001c0c007810003c1c64003900044030070350441850b0100c05030148519a01e04040742002090311401c8c140912405800640040d00c500d200c400c003401503500500b41111a02d01c10201d82140b60110b080c69001c0c24416403440d156000300064010004070381414411502d10140300800c00d801d176001c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 848041582 1250 848040332 848040353
    0x2010306031a010801110306030607030c02071211090c040b0a0c1b080f0106090507050d05100506070f030311030705030609060d0c0f09050c0a021f020408011121240d 73
    0x30384540b8180b440e5410403444c5030175038000034060481036100f4030030b0040e10360300405c02d980c0000080c20001550304130110280d051004e580c2c004d091400c4410b1021040c0b1890351607440050104172529038042c0c1c1d0b65100c142d007078000c2c3c0c0114040c5080034403d2070906406100b8900074580280e010000c80c4011b000c004a11900750b801002142d080344120496102090003040083c060000080c00b5a140000c07004080d40649000c03110400d03260400f1a5171004204441d002800000d851181e032010a03082001d1405034051003180020700d003000843c0c1d0031080cac4007564040c1c0b401d55203444c074689402e8204a01c40002804596108400b04c042e000001c4c0652250b0700100481000c0d0785c0740e03e01e06000c3d141103030b0004001e40380021040115480040d40400c08100350b01e090182e40781b80003a06603c0f24024010f507000b40405610300b81008828404180c083c100140301c150012518414030044002072040c10345041000c0710700240000c0b4007000982200516030009030001d07900c518141c81e01d05151 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 848042832 1250 848041582 848041613
    0xf1e130923061006020c101b121b03051207020c0d051006060207050604150c080a020c040f2a0c050a0f14030a0503150d060e011406030106140d0201030603 68
    0xc480a500340412003007070102c40c0c0c0c42403c04400301403040c9004d00207900c0764001c252143c0310342030b461141200a0701810035600813215032004000040050300d06040c1440580d55540c010480160000701c019158042d41102e00e5850380c2c819017819844010090064405000c180039809003c0300c4210030b80790810790079001c41c090002804880100c4407010121452a0050340c11900034150074402502c60200700d80440300991354002d41800886021a0000c1501800516131000012001c2000398000380340003905004440030403101c804208614200c8140c001c4078102c0010440b0000c041c5a0800ba06d131000344a50b05080910070219a1074a00f4081c05032001c4502800740b98486060090f804000e05413511000015454118202c80c00340050000a1030b04810341c4d2600c00203070660311050070400105030b0040090241c401c01c621001d020b052842211008200b005000468900e414003414007140c0800d5000740c010381d10303501408415403401d6002d9040c580c42c2e40002000644503088200700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 848044082 1250 848042832 848042873
    0x50d15090f02090105012604050c0909010f1a0f01140f0408061909051507090509011503050a0b150f040b0a02070303081003230f0d0c020f1e1309 64
    0x81100741d104001c416081030300150304000b14a0210703481800d15500f00750642102403440c000716078485c41e0240c40c1600154110b5008000304042c00f4000c6815089001800e2104c88144080910110003103c203aa85c062080e45c010082035000d83c042d40100d10900c0b010300b003400074514100080c4501d44150b80203900901d02c60f0f200f10708004551098081248004d15500070602000c150358030f4440d581c03201454030404052282002c121600c1c09105040010a0003078000b0b0005d69503401040c0180c2c911842840219003001d0018000004502c2205815480200300d0340d240d440307992014030366401806c031094003044204000320701d81069a000d405505c18541c01003030b1060075482c000346051800f804601030020048000d00c001102070120026492418000e030140220004503a850b01200303a00c0340d40740b40210107404052584c8030000c0018513000350b0340c010460f10300900384411080020506a040b840f42200011103141500c034942c5960160000401c00c1c0d440d64480701c004601e0a000140d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 848045332 1250 848044082 848044103
    0x708042a0306060b0a080105362403030a1818021e07080703031a131d0f070603050c040e0108010c0801051008060111070801090b060325050d1509 64
    0xb001200d0083ca000b50009080090500480d1040540742c14010b000c0c00380300d0150030b002000c076116500d40440200c5a0303880c0c0c00e0346d60030324400e110300d401d0b07825030f091050318440040c013a5528000c2c180306d410fa050050029450900720305421100c1042c1405615141160ac1c0e10000d0ba4030744441c2c05040c0031000510050351b035005e00646001c41055000c55107200310f000d202900100d00450180c59100ba01800c01107590800100c0340603c041d60500441e84c409903000e99a82c4680705984408014402d8440e0100c54a0591030307455603074243c0c09898140b69208030000c0c89940c1c400e8010b00c0c1c1040b41192403505140e00c510320402e005000742c110340d6607699100c050282050b4041046401420191a55101c20007070040061500d032008040300d043c0510025113506025003080310000400e07804000704074540c410b140603c07140105070f810f58032034814226000b16104181c204070850074607455000d03568600d00414030001442110060790f4840c100103c0c10008501401001c008074440c41c040c10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 848046582 1250 848045332 848045339
    0x1602300309071e080c040b010c0f0f150b030a020f010c14150c0705030a0822030c0515010501021902010309060617010f1e020c0703050a030807030606080403080708042a 74
    0x164200c3c03003000080ca001900b44010444420017241c046411035042e107002c47c24044440050300d045503201c1c0018104124011002d06018401603c085143d218003c0700c10303030030380b00c01004060f100040002070740b6400c1903a201e070040c942031414140c41101130408210702c035000e07200e6605150f0000400649074102c030030118240030f1020515070307000021082d00307401e02501c0e898650340c3e402a25420011b0007500c0c0003084c03c09039210318803103524003010403210004044d80b40040c00e0341100902103035580720b0000c40800074200c0c03003501c50607140d042c1d00900041c0388400c0c0001d030a07500824141d062569801c0d01da0b0106001d4051a40500f900070b411140000da1560704901f111890103c140441d0303c3c1a0290300c05c408000742c0349507241841ca0015032114090002e079428040c95510042940c819015144100340d0408400c5200340300700e0302d04006241d91824207448240c0200c0b401000542010000354960303009040e981e40150054922080d06200074040041140740d42c01999545807000a041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 848047832 1250 848046582 848046599
    0x122b091217010303051b070f08030909130506131106030f041a011401050705120c01061805090a030c11090103030509040c1e0509030a1514160230030907 67
    0x3660079407024000354030940c9191801010f50184d003c140315038800e480003440c8010f0040180340040d00540d82c00a1849a480005a0f80c0c0d91001248600468a01c4005100c1c404146031304158243c00c180504480d81c1e40038042c55140981407811140340ca2124141c5007280c83e10740180d4171518401c411703aa0030b4105820304114825210039400101040300c401401180c5480c820b07050503440a00300a621b030500f0745440c0b418001c0c0f803034500c2c20150012810381200001500510f086030030040308104496002c018140980f80111030000e038a41c4168a44000280715050841d903003401500100e004494490004220340c4003a84150006100030903c012940f0f002e1261a54035122030606e090400315940034107441600208018060110104040c8281d4a003070101c2c0c2c0000c1e030b121407c5e125844084503a000108070032850461392a1940000581580440041140814198004210082c1050680422000580821740203800300800e00b50036407a440024501900b02c0c2c0c0040d00c122070038210503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 848049082 1250 848047832 848047847
    0x40308090a091a010f120905060115110705010c0c0e242b0503120916060507151509020406020307020f01090501080a15120f0b09122b0912 61
    0x4640d080c0c0c82c0100f40802c1d040146001d49110000382041860b00e0003880c1d0a880740d0a110552542c410705110303d402c20800085072050584042c9041000e10100d0050104d482504403040c50081e9480b03d802071003590300444004040611540710310f103006844044010b2041025142403105031020605201c0605407a9010300c0024400e40380b03800d2000c05540b4001c910008a804141d40c941c1815591090003000c0c0100c55018110000043c46820b140c806070760340c0c0d528140c0d91300d6408106180030840341d01c140101c07080c1070740025042d040c1c0128040e00740018031080d40481d4040c0010000014107801e40e0014000510343d603000745403900e030240140090013000015030b03130420880210034849681c001131200e4000d10071281c0001c0a505c05640444010300c0c1c0d4002d10b41180d0840c0d02c1d002000260806100e203684191515901b540302c0801c0720769502540e03a103101c10681d0602180d00d4405003121845954051003401d021032104010300c1404980c07070480e003940c3c0d40e581012940c0755660407500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 848050332 1250 848049082 848049089
    0x70c060b13060905190b0d02061605010e07030b1b04060f02010905120409150503070b0d0204031b1d06010905131103070309140c010503390c100b0a050d08040b040308090a 75
    0x10248046c14008000a40045911000074031804001c203080180004022003074505650110007004604c2080e41070aa40c0e65041c0f108642682e0600002000f800e2500c0e5010800411100d0540c00e01c0e04182007511540ca51100da50308640d0798007082400304508100b84a019801c40e04c410340c1e51801c0136810410b55403918050104020140410480c81d03d0020701d16041b100001c002a445004038403a001c0644991342c0042c2410081c0d10074050b10000ca11643c804485520f07990740303060341c405140b09400200c2143ea081c08100c803510b0400c185d06100c0900c06400407440400070342e00c0010580b0480940086d90b402000030740d10018813003040307880d4503071280304500d40005040c400c1c0881c000030a10701c001059117070b039414404003854841041550481880d0503142d080f555020f40c0102d940c02d5600300b88203920052003945040c01005040d803082c48050300e07000d0100407219040200340a085a0889012140301c0c500b003100080b1250100d0251018521031200ca66031111040d081100f00382e210742 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 848051582 1250 848050332 848050381
    0xe040e03070209130501020a0801060f030e0c150421020a0501020f060621030307020a050c15191b03020a1106040b0909040201110a080c01050708070c060b13060905 72
    0x2000041402400001e541807581d045070701030b40c940d4803007602040729001d41c00010800d6001080d50541c564200800c24113881d4a9a50f01c02a40c20074103045080e10300140031004240c000e0900040d030742c100641102c0e4245211500145003d0b40c0390300301e46d410410000d0141d80c100591165030214a40050150020b2009100404420060716080d03600c412014198910507242109008d5003051900e21044048d034000040da52030780703000600070351103841006080b01c0e640500d1400009901d852404c3c55804944900b1301410040c1c004001880b00105680c007105000150780c152420480c0c070700300103000c207104e0750282440c1030786032a102d15000317084400c3c24400c00e03040c0020f0000740d4a160644001060403550100b007600c550005072003074142c0c4204803a46014210064041c0305c1242c004210b65000070780200541c2d515018100d8665070140d0b0040d000804128000020850b650026880c40c80007c11040203000c01c480c004048580d075a000341d182c1e80c2c86408100c8404040e0150100107221310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 848052832 1250 848051582 848051591
    0x60b0a171c020303160c020a0803090a05040218010302030613062c011202010c060b03060c130b042d05030a060903031a03071719050102040f1707170c031501060e04 72
    0x844001c0e481e030000031700c0c5c1d46402d200d0340c0b02e03005814400c2d42600074450b006080007240644802550383c0340d91100b1005c90150311699000503141c1428401c036091500600e000078900d28481004402951019040591201c10650103a086890300c1c4240401420400d1408000603100d4002c169061049082348842807405030040200005d02003510300c0c03080d4246480052141c207460003c000301810740d04143c051003030300100001d01010ba1700400002501d040381c00c11540e510101c0c910030744640d0045d0b180d0618220301c0c00a82c44040018100003681d21090911103e8551020900c1c00c520320109540164a60601e801416054441c4540d11070b0f0700d820074100e16050001180e580c0c00544180c4502900170b400d81014484103005484194140e03003c048855142420018042c1d04035000c1d6080220340b800380001d0301d4040c1d650704880038801c40082c201080c5400f05001c0c1c5151300d102289118000d00400719280d50701030121008118205107112029410150b00400300b001c8a072200c0d010342d250 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 848054082 1250 848052832 848052883
    0x20316030302280b01060e0f150d2c060f011203080415060819061b1202160212010f052a0a02070f0602010f180f0f060b0a17 55
    0x4680900d403c028941000905540c0704082801400e01e0b881c0900034151400c00450266800038285035440d000320b81c600d0700848803400300101e090004810541c000d80400480e030752904560828400f004215554420148001c08000444800ca42903e4042c0d00007070100a10300030401541e81c05010400301e030f280300d4112590060807000001c0e1015044070002141044114a285c0181c800790811400b03442038104409114400c40c00581030844080b0309003d00c0c15034988020640301030051940d034407000c8940309448450003e5002c418028030345d113030380414040542c41e49100c00c104108039500008a6010303403541402110f030050107092000708000c900040d01d207156620b5041280c043c8010b16034404c40354200360726240381e80c3d100c1160401c5140000804a030194004160701405d040140603009028000c50b0079500042d01c01407400101400d200041003600c240148290f128850018904803640002040a10203500c00500c110241d050f40682a40c14000d4503500c80c8030750b00c9003122180 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 848055332 1250 848054082 848054087
    0x8150c0417161721041502061e0708010b0a2f06060109060c11030c0306040b0108060c09150307140d0f06051c0b150a0905090d0f020d21050906040203160303 69
    0x50f05a5030900040340c00d103004c0a03c000202201d000703003081c01d14460421044440a500c59000b25190076424a02130b088884e58036540100510070074540c3d803604110382c240035604150b504594101810461010742204120300c194080e41d840c0140041f8880c0800e5031074030303c40e24240c4014012410040721003c10006150000141c0031001d0b4481ca01c2d000542265011a14090800710301c20781c1840384c3c1040c0000d000310300b06507034180c40d809815103141e03550740c28040081c1d100302888140c120b070810041007203901e454405150001483c0c54560b038001440d0994501540120440c01605507840d5442c8440c82c01038401c46009100c00d607427810901411042c0d080340e03030745010406440344901c6000621102c0302c003402c02c0744010000f00b46010044d1182c1e1030031b000b0a0216203003030f03240c41500035102004d4013a041c5159500420382c0240a1010821070444084403091560429456070f001d41004141d204d000b500c1c8102001c000070042403402c1c4c01003510b001c400b4044141040b9090005001091303 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 848056582 1250 848055332 848055343
    0x307020f102c060a1a03010c05070201090f0501091701020c010905160608010509180a081c0b030a0f1410180614010305060402040c0c0209041a1008150c04171617 71
    0x680307400000c1d0300040c031502c00c0c4005c420620386983c194a040401104a070300540a42107843c000c0c1da400480c161114100ca803045c0060081d203005c203001d10410440f0b0103c03201180d41440e03c001c005420800200c0d003071400c0d180341d400112100d070003009581c1d540c0200c000944000b00742600d084c4406524100210300c510002a02030003a40f20300340c442020300381040000100040e03016840355541d00740310311070301c0c500200b0b019921000d900748803490000d4500010941c252a4010164400111440c2c0c3c64000328444115081194040c0300030312132a60f100e520503060700d9191544844001103551400d4000c60340210346101001550744014008601c0001c0c60a0744a941990000b4182119060036950070406400081d40700000e2020042001100b005807201c100040403010300c2a2180c02d2100d00040c0360b402142003d130f2180c46100d203001d0000765800e4225001d02c9003140b07840e03125400038250400034094000180c0c06824070084e02d45005041ca402040390750000d5130120f813140020f680300c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 848057832 1250 848056582 848056591
    0x302061b0f03060f0d052b05030f06040b0a0506070b0f0601030603031d0a09020f21090a03140d0c020625051206040b0a062c030c01050307020f102c06 66
    0x500021142d403400382c541c0c00301c40d543c20f1340080403114580d81200111905031f20707032900410320301483c50007545504d002d50156030264412030150300742075481d041440020072940e019039030300c030342402c41c000f0b256180c52004140780c6008414040e403600e00180c6180761006e0140100707042501d080c9003000400d50005901ca100c5845050b240b842c1c04095001513001e207950f81005481074800291241031900c45c5004084610350b030b0143e00c1c0e5101007000302c80c40f2503104a079400055040345000d030700007901c5200d841200d0702019504504003110800303800102c0d820070311442d001d03070b02501c1803142030500203084842d40710441826401100c0b2442c0018803e0050454551900341503c0109540355035036040300d400c0725800b9200b0440c1558640005010615401a00c607011140442d460b03011001c04c82c0e0800d08000180040401443c42d400440b070b40c0c0c3c4000c1000d821801000c00400115900380650b800c2c1d668040c0d07011451605c1148846c110760108001c4007007040c070510b0441440300c4c0108088da400b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 848059082 1250 848057832 848057839
    0x3160f0b03070e0a1706072c040e030a0e01080c0901020318040b030d090618081e0f011a010e19140409020402130603060b0301060c0b04030c0f0302061b0f0306 70
    0x81e51192081598525103090b50f41d40c2c081103680d40800e18041c48403c11040c0003c0034100c64031500d0392007040e5004004c0c5280d00a00d110322000410b40d074002c040c800c0462440107880092206100c02c1290300b50341040c2c80709070008030f24940c00e841c00e60340003500a803c00d00021090b861f01d0403020000c0c1d903034425008088143d042e1803a04c00d0490f0b4656105140e1040302500361420007100703079030007410741c0c440d17001c1c4101007201c1d40c800c06441051031504000340e4000c40010401c011501084000c100c1c0c0140340c100b00361044005001e0441c000307010303546a402c00d851462103100340303210000d410703003040b90b2056018503181381d00c550500c03030a01020400c40b01e400c010707200404041c0000c80c2c0a0402c0040194100d0f00000f4050480240e600380b003000c545060360b0030002c1d03a442d140c15200305e00c000e201d00e800007152121903502140340d040403150030030b01c2400d110a500e8000da6403035003070302d65540c81a40541c1040e010440c1d443d084038124070420840480b81c1c0d150901c21000140c09000c0500400c0c003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 848060332 1250 848059082 848059087
    0x219020613030e01030b1f110304081f02071e0201090b070b0612030d150e070906050304120318123e01020f0f0a0908011e09051005070e03160f0b 64
    0x10942d01a901c095031048003d0041c40c00c1500307100c14000c070204460481c7c80003a8a201030321a1080c0044261001c2d2800640500303018169004120088414245002c507817582c00c1000d8000104c12014008036014070444280f217002c210300000d00b03800110360010014003030030451800001d9400300c40507480381d0102d03100324482041552651650041c2c0c03030306060071381ca040325200001282c41507403400c941501405c0c1e01c00d42c0c0d031184102d405218910400d004940144081400a000403001070840761440c54006260340c00c1c0031464402090304201036074480c000d025200c10b480d44c040509452200d581150308200036020910400d440807214051450206889142045480a4048450110903440825111829810002c086503c03003c05440442d00c65200012010410b009042800d00c2710724045809010754054000a08a000800c85240c0151740e007a08100200c3e2041500030402c42d6142491b04103800c0a040c60302140481c022071405107144204111242d05c0309800c2a1000b1006064 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 848061582 1250 848060332 848060357
    0x1524060d0f18060b0307032d06110309150f0622090c0e07020f060105100314010f260705120709050103210e150c07090f021902061303 59
    0x40051030a250989a814200040200d0b18064400b8101c0000e0040b00e042098a52000130565501e02a10005082586080100001d9118000551040d03120300010700300f06d40306666040125070140d68a4000b402c00030040c044042400c109400d40096207002140c09801c040b00b039446e084c0300090106d41316034a82c1c8030328504c5c1000c45407400c0748141d480c0d40500085d1a2882c10385c42a9819006904d00c00c0780000019803840d100190781d040d1001d41c20050b010f01e908100500c03913001030014108090541303c1030315185640c41000c05c28000c01c0095512113015041000f20040c40c451000d2040d071600c0c4249402410032800b0541804950044030860302003024052458241100f61740400d40252030080004148204c0d01d14045c061000a12001e410072410041038800188080410b504038a5512010700d030f0200d02e2009004900301c1030100e4207100c0d40d8a1110003541e058810f600304440c2c000c58010000500c414006598a2b0a030011303202c1c1e072a04c0b0501489660402401808000d1540e51301d5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 848062832 1250 848061582 848061607
    0xc0c0314010906180b0906040c03031d061903050106020c060d021e0c0607030b011706010f140a030e010f060302060a050706020409240608060a050d06020c0d02152406 73
    0x400c142c1c2d8404401e228074a464402d4045441282c481030b141c912070708001940d112030105001d4070807680403080400b55810344d10100d03690304241c00c034407142000100140f40700ba51032030040d107000402c200181e2052110814010306480c010380c0024103661007105c42070340075510720065418200c0c50100060302c4807100031600c2982c000043c4039040c130f40c1e0001400c140b0508042601d030f1048040342c40c140300028000d00111840200030910400868a00000ca50150b2150032401e40c00d05151400c1407041c0104200050789601c060010000301c2c0e560400c1c0218403c00f80582260403080310400c01c200ba10396004200c00c1c0c450321801c41c003080400209042009030950644014000c081c004212115030082031501207048419104040b0f511100d0000d0b00c2032140c0343d1548205405003c0c007118034900300c24408915218501221a99020300030020410701c02c024082c0c81700782a500804881c0300e031507421000b03035102808160000c0e02020000000c1503d030100c0c10349621098503520303078a03680380c610f4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 848064082 1250 848062832 848062841
    0xa06030222060b090f0d020102011d21030405030405060d02040e0403080a0e06040c051306030b090606091803091e0901030b011406030112080a0903121e0c0c031401 72
    0xd51081c00307000d0a040c4034010400c030714500060148104a01516080901e02502908005581c0152001960b05e41030030001ca041d82c400b4810b000100307001811100c01c00c1481040c142d11140c545c0803500c540410203c000650300d000c40c547c40d0305450350802d038844070f860b8800d60040741e000b9400081c0001c032000c550390403030f802805400b60000b000d00302031400400200c02992100702715418a00540d903c0d110100e10f1320700580d440280e90030010f244c032042c002c04c141c1c514503080c4025641c20b030000111b4846030071648900c0405010b024a40780c0740c410407260740350291011124150041040040100010858041010445080c4070584088a00003a043d10307a01c03a4641250044000004210041d002e141c1a1070200c00b8a010144504080c008280002d05c901c00e07030311080070388000c040340100b001003a8400342c2c0d2800060054485d20f9140c003592035234002d6000138909940c241008130107803c01301007045481c6090810301981e5211038100c6185408003606411b1415006011106c00350700 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 848065332 1250 848064082 848064089
    0x6071a1308040305010501240f0e0112020c060406051303020d0c020a0819140d020c0f0414010b07031b0b070f121a0f0f1309020d15200a02070605030a06 67
    0x403481d588035103904d041800b0301004c2c8180f034920440000c41c1222101580d01c603000345003050340c4000e0f10981c01001151485101d02040c1d060008291802954001900082c0000540403008055504040c5040f401b12003005045081d120684c0300b010001a50119034400005075034a060300600c001e50002076601203030380d40a072055220315541880b810078440b25000c0c0c054040e60030003001000013502c032516000d0041c503420058200e507540044c05e14000c0740c240a03049015100103102e60340b083c01c410f621a000c0c0c006141c25000070684e40201603016001685821500c041d02da0380940030703a22941000b80261401d4284002c42c0c101104007403245507948208a81c9030024801c500011032f28040703040e00d280c0703254042c030131060001c003003410060b5011224079030243c142c1449a05001c8240c004055404080740d0090441c42250302140001100351700c0d40100031000103074401080540e9240b821314040000e40424140440390100f500070130088101e5120303080441da40d56031108108000c0c1602e80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 848066582 1250 848065332 848065343
    0x1a0313080906280f080c0a08040c050d03080a0e070e07030504111f180b070f1a010f08010c0212030a0c021c03061a070203070528032006071a13 63
    0x52180360164506810062400c050320f480300166044082100c4e082422900c0306c906080c10081e81d48518403a0901c2170348070380100202d1380203c0c1c8900001d080c6405000c0f040e80000d83c2e0760140110400b061007100c00001d202c10040c56581e2802011550788400285010245959900000e00f0310403c60f4480300308010040003c01d001c2c01108101443d01c503401150b0001880b000e8902032160320400b500015103150752074040c00d1203c259165450b010088108071600700c2026941c0002d42040c1d40d00134040d0100c1803c001c80c06003805c1546007100c2c812119441103520484990121945403001ca903004803103c0350100d034024000348180d283c07208021401c209528a094071030b40031a0306a0040080d00c0104403280c0c0340c51462040741c2510b0081c000080d5154000107020030051415a04e0414801c0346091010040c096042e00c02c3c0d10302c0000d43c02500ca0440d002108194422444054910383d18101d80c024181000c5407903903100301903494174992903e19200c1c0445c14510062004407881a40b10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 848067832 1250 848066582 848066617
    0x81e0709111b031c050108060126060f07120504020a06080a09170310050907141c0515030106060314010b070501020415020a050114190f060b0408071a0313080906 71
    0x41d0354203a500c0c0e00c4022000c103140d0f1002c44c0300c00a002103006150481e044400280441d90801c60a011001003854030090b242a41812000c8526414031110384941c4810315000c074a0310f8000c601402c90020407490013039076441c210400005a80d0b41c41d04d03400b80c444503e0849191360300d403917505000b40302d07050025104009121019401140b00b0005600c14904100924411586d81051208140081c0c0b03000022982d00d90342c0c3c1d9020f500c401c003d030000600760011101c110038020894412943c05480884401590158034411410240100c0b402040d40340b130200680f0081440c0701c2d01c40c1e4418041c440000300c00182c400c0c01e120094040d2781c00340c000d0340100850605141c80181d540c8040c4407084401c0e50a0040c5048082002e034241c1d0301c94260503160190013020000690008e10515825040550f40c0d035501044160a01d006800a02500750040404070304042001d2500d0700b004411a014100810402170000203518000031a81d03803002d4403688801103400080c885014560003441c154103003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 848069082 1250 848067832 848067877
    0xb0d0c090815101d07030b13060303050946030503040b0c01110708030f04141207030e0f01050901080c0f0f1206041514060d0e07081e070911 62
    0x902d0403182c01101d076019030742d042c40d80d00c00808000211191130340d485000e2030f60005a15174080e4009590291005040012609002603400c04451841c0c02c150001680424003003000d040046002285a6003810362a510038184611612030840b41594800c030102a4a4480c258070031900c8220007a540c0b01d4281ea4440d9203e040480031600454090070456080200300103a2449103412a034400390414009032855071150f02d50321803c4d002400c1221801c515503041e401150007440b400d50f4a000c0318400d29518030329810028203500e04010f00c6446201d00340781c001100e07a004000c44c0c01002c0b080c24142151742c1d610342c030000103024121814000e01e10000d405108110054000c103d0040000000340b00358844405100483c4d50140240d01ca85404041c10f110807011312201c0f8540480c002d0007130380351469020460003500c000001c03460b403e9010320000e112200c0103001405d00c00080d00c40da007154825042c81d941d5915142d20424071083d650b500102c482d411080102c82088211044a090310f251 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 848070332 1250 848069082 848069113
    0x60a0c0b011e0b04050102030304031d09090f0d0e030c0d0c0b03091f050411060c010f020705070e070f0906080a3312050604060e0c13061409010b0d0c0908 68
    0x4690042c02007a00e018507000c20034101040655040d0f48040c1d004500796503c1d1344d4162080d0800208403d040c0800541e0b055407940c503550f9252240c50010054410b2a9032800841e1528203c565490148040d0704518001d6440000c3c0041c3d1001c81140d8904c11410542402504000320b41c10900c0d460070004100107801c50b0000314040755640e11208a4a50034440060000b103420640f4002c1645c0950b40004816141c9000a42546200380c400000c00c01594403904c012030380086022112500010302c04c100d541e22880e142c40e0300000b01e04208034410000013000748852600d001e208184924440481c20a805d41d61011080060001c245541024101d0032207540c4144000101d4560180c0e11001c03c114948072581d641032942b04006084d246c68990b5075001030710416082d4000307403080c1c0c0306118007941c5000348400b04440740140021060700f0020b0880143c00641c03031070740c010b03d031703c40040102039116412039120300d5092a0014002c00240c5044528942661203405236218500507a030b815017 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 848071582 1250 848070332 848070359
    0x5040503100b0d0f0201030f140901050f0c070303091a0109020d2004180f180c0503060408180f0303030a0c11120f0f070506010e04120903050c060a0c0b01 68
    0x150210101c540d01c441522070102a60030740342e16590096032004248000581500201c142284141404100c1e80411030120003112a0f00d20500d0901001030184015880c2c02c3c8142508031003640100b03000c40c0b40c43d8034070303003000c0c82020f0300201056590350300c82051100318404844407030100d040b1401d0559407a085000079411510f040041d1030b03c0c2160441e551101c1c03403c81c41004c4120401c603414149400202c0c4405800002c07840b60043d22180010880c10300b5200c0c20ba1a0b05440e07402c85000d41a901b40450030f1626074100b0340c0030740c0c440380c00c6c0804035455500782c07a800388201c0400c496503519040440d00c2c102191034101c0e0944004003c3c0541c10b170440d080307500c11400503541c0f800004401608907965400101e9041e109d079004000d98040e50004c84018594074112108140c074010f80d603510035140003c01d0740f020010841000c00d0001b0003144c0c410061303840c490740c900303004401c1c159203540d9200d1055485040c0309590000d12030b451309018000c400847c64001c40e40300815a9146004e02510 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 848072832 1250 848071582 848071589
    0x31504060b0a1d03071502030c031308190308060609060705011e0e0313060809030f07030c030806091009180c1410080106020309270a0b040b030102041827030504 71
    0xa0f141c0601c00c000e08103a140100300300e02d4010010510185050246d01c0b1803802c0c44000d50031804100041584010300300010442c80d0f221040b90b2500a00c0e004685040580380170b0090a5840f10105043c0466401803403540c0100e01101c00a94815240340001e14921450000030004c0d428600b054a0348519145c1c90508400c003100107101c660b01d240c0c0740640344e100300c00b42c142c03001c000bd020510451348594003c581c800e0720318003106c1c41d0a064444020041e00042003c400103817850342e11504065201315072640100e42500e10f8501802c011412950240c041d000d00078400d6078502c407004e48030400303445581a20740c00c4141510384507200c2e08110410181710000c1c0c2d01038840b8900f03880c40b6074070401c01d5a04948560f8040c41c01e00320080c0070031031950680703505e000703041340d40060001d062031003910301c0c0c0d000fa20020030000f24480b150080c40305035110020001d1280e44140000c014900c0600550000f90410000005400710340c000000000c501122014010100310b141d24010990050000c1003034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 848074082 1250 848072832 848072837
    0x61214010510050612090f19120f0203160c0f0e0108070617010e191d010b040b0a030f14030f0c10180f142a06090f0105031504060b0a 59
    0x481e40ca800c080e4001c140340d4820030303804c5441040a60759481c0c0e091515500000c40c5419120040ca8000c5190b10341604006541404d180d411a403408000520800f10300e20701190422140380c00c08920003035102d00400c3c004010b40c8240b201d0703110802a00040c140042c01a600811a11988a04030024059000d0040b9542d5220351600400c45900800800d501d5100c60700031400c10f41c1c00c1c00c0c0240e9000c040a8494a02c9064005c002c40c1041c505005014a0a10b244081560025501c44040c203481124030624043e52801c055000c040d140c007203092003580e07002910810000d0f04c91410015880d00344840d00700b82c0c00041504c9403066a000c000308011850702040352140b2441c004079104503120780490060200345130100d600002c0c3e01000000586014902003401c6000c2e1484090801401039500d80000701d040192081150041c2c106041c100c03000d852450400020102091140f01c44e440340505000c000f00c0010100c0189110f10792125030050300500000d41d4070810f11a50341c00c1084002c01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 848075332 1250 848074082 848074091
    0x190612020310090f080d1808030702190c0b0f0f0417120f0a110c0d0b180f06012105030d09061b020a0221060f06040e0619020a0306121401 61
    0x840e14081c06421601c98000e10884d00c000b0b12a50741c1e0200b80d0020710310510550f124214540304101c5542d255090780d0017554170343d640f07242ca030070000d05094106c00a15449460030004070089101c08688900766000d0b119459903441e0120303200c42803401081f11071428030380000b80224000d844007036018051070010086907079412003809a0a81030103403248100300b09006004102c10f00384034407415001540d010064501815205c00400c2401ca101300007a18041c2051003803060458404851501e500340d030f400940900302250b42401d4440708184504842500311102ca41c08d0001101c00c001c05140d442421295942400a0080042c14030356100307941151806800c0c0f501d400000d2007000015010f0342c0544440e0b051a4200801340131205129150f40050540d00308040c1c030b08010542c060950384554102c1454148104803e66407a451071103d01e400100500c142418075980000300c59000c004c01503220031040c0e50071030051034150302c04000000d044c15104284850000c1c0c1000d1242910001d10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 848076582 1250 848075332 848075353
    0xa0c06020a030f03320709270b1c110907050a020628090c030537060f0204060c03030c08010b0f1303020a06020f01050a051501081906120203 62
    0x1d031203000d005000342c08078000b50201e014040c03290b4409400d83d1100d000c1d01c41040c1c0c3c03210903443c500d0307001e280c84104084038005101d0b2558000d0b03909030040642e00c078501030b1105c010500703100b8060f1036040410020b456081481203942c45450005c40c01c015410001000c0b110350400030307030080070ba821260003040503c1c0412281c9200b10101c070b002440e5a00149151f1b25982c8654543c2210000e1002071120301c91820803014560b0b0017000341690040400d150001c0c2103092039818084030302c1234040702c16410301c0c072101c2c407080400020350610a48003107020b9800c800d0400b000901141b80c051089584002804925141c100b60311f40c403c14020356042081507801c0a05540d500001c1c003408074020303800d1100c40500044c8000409a0101d51204021903950300d40c0451110780d100d0f0032003800b41e0031240070007440c030340244a02944040300c00c00a000900b011107020844070310001d00a030404c8901000941d2150260b03400a00c8903500d000100441e6990740e48450340d103303103090124803038000e141145 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 848077832 1250 848076582 848076587
    0x11010206010608010e1009230a06050904030521040b01240206131505091f020304030c021509030d020303010906091a060915030a090b0108060f0403080a090b090a0c06 73
    0x381601c1c0182c840007116400c0c000214000e18008000c2218010b4281b03004c146400076005480c0500c400c680140d2060085a007001c50300880213100c03401c00c42c40e00c07808200a98422442c141c0190b00f42c200180e4495080b20101280000302d03c114040118801c03c0c070041001619886040b0b4114404c204c03442034418a00d144245031203107529005a01c1351020491034061030002004880c41403920211040a040100d02130707c80890300410b058000240c4544040000b055030800901c42e02411461440c199402074450903401802038001e540c1d02e0f001120280140781210100c00f0020103c43d8884400c5100039a82e50003400f900c00424184440050802858000c01c041c1412441030800035042d60400d10002c0c3e04140680c982c440104120390032204010002507001c0c0030200740210311600f890404944e8040c040e8171400c4a640f04204001842e110400103a030025030503e45100907840d00315a20018000001010700710b0140801444201c00c1e001a2041c0304c1d038031801540c4107040d82c51005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 848079082 1250 848077832 848077843
    0x1f02030412110304030f140616090303050a05040306090507081c0206060d050307150203010816120f050f0d0e0a08010501060915090b160203210d020f0d050c07110102 73
    0x40500c0724048007019468001c040c1d6200706020340003207a04060b9a51150b0380159048202a03a5407001600c91180c3d086c000e2011039448810080100302e540d4106400a10b150380d1840702400b0040003041410945119004a074000c40c7c00000074080d04185041c00d94072801da520030391103107101d5500b030003961680700700f8411a202501d4015110036035490b0140104030601800482c3c03940010402000000c2c40803140f60044105044016240d606001c1000c4c58400c0081540b032181048260811080b4001e0340320607140c9078000d2220350b8100f80e5103042031034400403100c0100c0300e0150018002006500036540c2d00c50150884601e030f0b2072030ba5405030301e00301c130001e000f03c4000580106040c81205140041030448645c03074540762016503900c03085001c05802c1054941cac49001c1c2994000251302d0700300050006880c003e00100c40a49100d400030b002482484184d5810540105404c0381040c420402d980c92101c140d0828003a6180641c1c1d410810342c48003800b00c81940c1c40c141d074030300725500c0040d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 848080332 1250 848079082 848079091
    0xc210e01050f0c07030503090a0506010303020f0c04050f0117121c0605060a0504030f05150f01090509070609060f0e100c1509111e19060f2102090105040905091f0203 73
    0x11514030300802604c01b02c8003503000805400c110710038688841d00148003000140c2c021070190340508200300341c4041c40741c00e00c018510814880e41c1480c0c28080c01400703811600d4110381500b84198002a82e081c800c50504203140091200d912001c1620300140500091810071901c0b00c0108002503a103036420030040c0d0082d00070020000303800740414400a0410000c10800303030b00a0f030840e030241c1840301d00e2145100c1c0c1200d500c558410754000401400ea036602406800ca51013502500f050b90810400030403c0381c0d01d00c100c408100c00e110980003003a0180742e02a4044101902003500f05049207405000b4605828040700c4c10306604950107200c90840c81910783c1140c1c45100d000220310410100100c0e03d003100712126076413120080030b0034240e4403880c03003548203149000c64402c11450706201400c2c816000d800542840215510007007401c4109140003414555500010f07102c0c1625001200c3c24040c40d00300140f05490314041c04482000001c1509000442d03072600b204c18106240070b50b00fa40003c3d41e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 848081582 1250 848080332 848080351
    0x30e0a0504150b07030c080d060311010507120503100b0c0d020708030a0c03032d05100501020a03051603050f03100e0115050313170d020d0506220c210e01050f 70
    0xb101840740489072030013040018003a14015002620039103c842040e8410703000c25001c16624007080041028248181098110034244a4117120217038849207100c44440f0144010041e000000607440311700c40c0d030000050441c1c85603160f00c840c445c800c0e9550b5840100f4000e00548511107000a02500c00022112050095641d258022665903000e5014108400005903592182e252110f040c41c2c000c890409403521b4200c01140604016500c0045039000350800c50440d0000001c107400b10390002c084909a614074a15070340c00d00c0b0541000c441c64003039040300618407003000041c0442c2001c0b1080350429124944541201643c2e01c10000c1039071640c44036040c020a0003400020740b08409880e01c07008440c02514400d24800745807905662503800742da002100e407640400c4c0041c180205205243d4000f40540f04024000c0b14007020b16505091340d403c04070700b961034140040701944243c1c090340d400d0001c104c0940c5039120600d10b450103082020b001140765841c0c200091441402190b00c0da000d00010f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 848082832 1250 848081582 848081621
    0x6051309031205090a060906091407050d0209130b07121b120f1e15051e1e06070b0a0b0a03020a150c08070b060111010504020a30030e0a0504 62
    0x2080070b2001d882c0c002e00d13103000c50003107100c6000442c40600035940c1e02c92240100240d20040c902d0a40e02c0310603034160715101588441d0040c86151184000b458086030105c03010b072003039580c4d000e205070001404a00102414224000d0080c040d4100070541c9601d801c604040c0f003a003010b03000089240450240c00300c001084018240312541d000ea11081c0e1200b4003100c045203081d448100d50840c50400001d14074282d540b04000e40880c0201c0c4c042c42e000e043c08032a4400660101400b84800c1801225030710300c074061741480001c3c000c0540d54400c16056025120340e444507407500740614071400c121054010941000c003800c400b443c003885041c0c15664010008803209080804d80a1003007840316401003803060704000741c400b290320a030180569500c1540a211140703003940004040725280a070848550b0304000034003006a440b90002800e0300c503400720003c4103001c0582a151369580248950448422075000002850342c8040b603840c2100e000c1c0d601c09001e0740d490003030004540455407544c8000c3e109 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 848084082 1250 848082832 848082857
    0xa0233070510110d1d06010e06030307050d02010903030c11061602010b06030112050d0c080409020906120a0504050115180b01030b15030103020f09130201110f010f0605130903 77
    0x58201920480d07014100710b03001c0114030035a1108440146820006140001c140882e203070300c0e64050f551444400041e08071049407440a16540c801040c018070a100300b042d400104a81c40070000d982c030350342e04401201c5030145515006802032012803c2500000d080080b40304e41c00f8004d0042c140c000078144000c041360b86c3c4098044001701c03e005204402c40d503c2d1503610896607150741c0554064085c801d01c40364074411528109152901d04d01444060002108061011a514405980403184005000759480500400241642c45142904015080c00b2000d1200070f50240c0c1c0080d1003188608000c101d04130110b18200300d5079201744540d80d4098016043c030ba00c404002e421042420a0604010804d0044500065000141141c81e0031304100c01000400661810001035051030f40282c451841500b010038240d5000c0060240c00f0f4140407120342e80590b2081d0410802130030300e800c1d02c006c00102c3d00c4c9240600113042030b071107528411005450700300c07030410f4144100c030640c07039154540d1088d0340390 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 848085332 1250 848084082 848084179
    0xe0a06060215090c0411090a0f06020304120305090a0b030414030f09041a0a03150c050415050c07170a1709030d1d0315090607020a0803060112020702120a02 69
    0x400030f0a09003d8020121404000d4541d4002c1d400145c0220f003042d912480c3d28018440f21801c40c0d03100380c0c0f040340308032003c20280f40c000c412281a680c0221800030501498202a215071040a1072141c1000c2650340008040907100042c44c0900e20902d01c004d101e9070780054440d640e000305842e5101c44d0798104000d440303902d40703030380080190141d610a011080224000103a00114250700c1515603140b1076001c94034482c0107200301d4540d85200e0900a09040c10706d5002e0a00201480d810400c0c0000080c69100d12041004110020040e040c0c0d121080814aa0b100707444020f000e02c1129a08000d08440c4150300c4a40140d8040b21030240040c1a42d2880c1cbc034080303510492440300c8195911008960f00c1c9070303850074803007104501414521081e070b500b0300700000c5180c4180100342600b150040e120800c00540c41c40d040702d03001002441c00b818415017070210305009204442c0001e40c082c01c40c0310b4100103410302050350840c2500071903105100c554503148900760140e0341101281e0140c001d1070f0344400102c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 848086582 1250 848085332 848085373
    0x6040b0405010b2208030d020c0d0822030e0a0b0901020c0102212d031012170f130e010503070f08030d0f090f05161d06040c0201090206030106090e0a060602 69
    0xc1c0e428488070300017603803011854116440041e902d000c1c2d0340c00041207030210004005031101d5410034580a44280742182d105500c0090f12001c800c1c28141103020728090511800c07248040c044010b0441d82c42541c4d074044140c0d280d200c912140d0241c081d11603034160941c00031070a0842d0070b03000c3c040e4680140c6100c1105820764005244003246400300d0441c1c908160000c0d45034507860f0101c1d0200b03a41e034142070b50021003000c0e45c0d52164a28041d4000030600050032010a03224001100100035240c0041c014000702c01d01034448100302d00c2e00a4200001e0154410600c01d048580650543c0d5100ba2100340301903603152503028461099000300300b00d2070039815a034401d04100015840018900d00140d0300d10144440701c44040d90958000c00c141c00e159514002108000c04003642e10814062241c0200000c0b00c000400e0103100315a2554169580c50003900004001907006100650765a140c020103807281603140190301d00c41038807000040f15021184a424190350b1150001c08101c4040500300c01c0c12b9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 848087832 1250 848086582 848086627
    0x1020304031205160b15040516032c0304030b150a0e0907050909060f01171005040c0e0f070909180f02150406030603021c0c17011b0806040b0405010b 66
    0x420400303034052601c958481c1c43c101d031081000c42c2a50810010005080400050341ca116500e400c0501506031100d4103640127003029810041448064400740301342e0442420030302c00342054261070701c1e090420040002c00540344104120f40c80d43c1c560f003401c403010001707044a50b50030603104030042c410494031300c84c07a5030b04c0a80241110390168440c004110459801d5917415401d50141050002d1426244001c3c0d016000d06401a0750f040061400180d940c601900c020744126a1200480d0034400041c0440c4050074050b50300c01c516091254406000c1d140448180000940d034940225407000940a5190314289070307040074240000d42d07160510310904440c4100d9100b441c00b0b954244981e500d2700508020302c42500d00040f150320714014401030703440c444154161251403020150001d02da480800041e261281c94800d004808803d42c0d50050890910b82c50360b2800c6008582040c6601c4400b8074890141905e0911801280400307020a5410038018100c0c1e1038002c0c810848403071421f81545119 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 848089082 1250 848087832 848087837
    0xa0b03060a05060d081e041d0901090c0b07020d060c1e02070501080109020a03091515050d080d020a1209111302180402031302040e03130f210804050306090a051b010203040312 77
    0x4046c00e54a41904641c4283d0044146106440c8003c05048440810710f40c002c6105009226886840d900c000454102e4010707001482400303ea6041503455103200d40c8822070380a2820000b00b1440742000d003240721105400c42903182c4203200d01c03a1940c404034190f022520180c45501859007405108070181d004245400105992100c10002052511802c3c0c04002e03101c0e500010482c4004019480086c250381009004015202980001a000d44115002d403014400010b07110349100d1402c4500700d00c40c1d5140104142008404e0301481f0401c0d021086400007290140b50048822810f1003c0c0d0040395241000714810900103201420079400440d071001c101c0c00030310104002039000804881013401010504e520100b484002115000d0001d4090124014800045803a1040c1001c0702e005034940403448050180c0004c0400c59280b0565001d00300007419100546000d8071300c943e40300c070070110603181d502c684d49800307034102e13803104000300115010780c080c0d450705003991a044812900070b40c0f01800c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 848090332 1250 848089082 848089117
    0x604030f0f14031c2004090b010e0d05160501030903081605041203170c09030a0f0f140d08070e010c020f03030c060c0316082202030f03030a0b03060a05060d08 70
    0x908000d000810004c4130000410510740722060b0500708840840f1488145592090003484070011480140d404030713044240e0108101c1ca0840c0100d6840a4402c00d098002c084112003500f00310021030400b4000a903c80040082e603911001107040e03902c00300d40680800c200c2c6000c6840410860304d510b1020704641400c601d010796941d48807183c40312800c41500014801000751027402c05144920b608580354030b1a036420b210310080069201c2c103070740400400c1021a07203840c008010ba1070b82c4560b00d00d600301174904c0c841018024200e40b0f410310030045400007105980050032190013011001100c5006a45960340141a6800d01c043c0d47c05401d540c0303a042c80180010815810308014243c8210805000742c2d842c2e05040c0c4010300c840350380b460f084060003903c400708050201d01e0381242032210801c0000c255000740d1400031900b00060356a40d07003103074000041040350041d50f6411004000109400301c6590740d40381c0100804a40050303c1e40ca0f400004403441c440401c0a00000e0082e20781403009120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 848091582 1250 848090332 848090363
    0x90105041811220803030405150a0e010c050a0215010810021602060d150f0b030c092d1302070f0b100806070c0204050f0709180f050112110604030f0f 66
    0x2c080e008003211040f8485600c40c000300d4554000b800800806241c4001e500758285907440d07940f22010184a600e21511403030024130901c1c1a600048201900c01000f000000361a07140200306030b02c07040d60000588540c0807002c4c050180100c2c0e13141203c42002c050994000b07900718503406540301110b009620144030120001680d1010014945842019000106440c0307a40d000050018960720180d440000345008008540925003206d80c042e07420640c1580d03589041d40003c50000c5215a58400340c0d00002c4650b00d1011001610010b0342c00895100007911b50f0401c0349816032242d0b031801812070f00e10b040c130000090680200d09400170382c18068080441d4440034510310f810012038052002416008035030301982064880d5541000310032018010500d072a0401500c00111440703011204c0b0040500c69101100c02c3c1d000e622500d5020704140318a594a5060a1741049503203015a2068062a880c0841b444c1000484e011a540705840341030941843e15203030010001c0a00665401c500e195900 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 848092832 1250 848091582 848091611
    0x14180601050d0e010f0518190c0e0411030f010603080f0a09030f080a080a0c1d1207080106051306211e150e0705060d0e0c03070b120c0901050418 64
    0x581c410040b000c000200729440001e9441a202c001e48000304010070f402c4021f504074004a000400e284100303410340030903421498499407040182c0d00102c4250000c0b02400300b0410813819130007441c03108404851070303028002c02c3c89080b69450310000700103250400482022001b110050f01e00305285082410700f4aa503030b182c3c00d4034241c44410032204541c1c00101620720302d800070301858104524100402012000d4180501000070100d0400108620700341c62801903540d0881e40080a69040185c1d800c04da03440c41c0090103824280100d40c49414a55584080100107108a07000c40f10100780c2c1c0710b036007990464124498856a081912025400900081111540210050b03254481c0000400000b440301820088440440603a41c0030b0b00442070400040d961308041d604602124a000110542a91001882e04800c0104150140070b82400010460071f0030010b81242c142410f03012407207540f40781400d5240c0c0b090301c002c80d020540a101c1800081e100481c1e078002c03107628000001c0c5640100100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 848094082 1250 848092832 848092841
    0x6110a2003011b0f05040e040209040510020a0903031704080405090a0b0a35120a02030702030a2105090604090b06070605330904110a0e040b040b0114180601050d 71
    0x42c1c110590f40f1041d510f0b019074071840c42512143c240c0f4043e030074a81808800c90f41520040c0020703101c2c1e44010040780c24030509000c517450700c1492140455440d01e2b000000703440130341d50717100540104122380c2d05041540d80f460700b81441160b01c4114645004c0c10003081101d01e000c06480b0440c000c2e911448000942c46001036a4003800c02c12110312904034283c03204141138644d403c4c06050030340140708480000d6000160280c030306503034035103550b8a80a241008a107907008a03100079506204010081c024801c1e60705105480740860403400e00b40c06070803181078580c0e1007100c030b407190040020082000b01416a82c02682c40200017001546425155114001a5a01941d80b202003080100c1402c80500307840d140c1409029645250b00030100c08400051a002c0000344080c09140300c0005d0a025682d1b040356200140c80b0803182101203081c242400b0a285008460032a64403603524008108240c80c10280c801e510801002d2800e2000f500c180c40000701030107007805051240911007001e907070030b80f07005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 848095332 1250 848094082 848094101
    0x1802120f010e01021902010e0a02060a0302070b2a040305060402011b051605100e0a03060f11030702010b03100b0913060e100e060f0402090411010203120a020703030606110a200301 79
    0x140c1c64807914602900208140d088178025a0b1402c0c0c40c1501c1200f010512040f4150101c0d400d9440e6231140100354007a11814100034003481e40700c0d080028800c07170380112081121080070941c000c1d8081a00c0051948114080070742298001400a00150710071002c2c202c0c8092044000003407070324299a201d1610f0105a05055540100c0d10140703c1c60904030003000c2500590302d4400190710380b20700419061092400003400c0d1648030120300c417003000240c1003c00c4800301c8010465a0b0700d442e0100900030070715000014440c0c055000c0c500701c420041d010701209118010440079203500c42406130710403045006012940283c960700b450040d2031040c0010480e10310103020103c0d4841406040c182010700091204a03104000024400940c661011441d0301075407200e81c07010310450510040c2c0c99400780641600b07104086004100c602180d0b9006842118401d45081c400c0310303162070099520111039480e82c1115882609828045200c100a0080f07980c02c904254121000788004a400c0d10703071045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 848096582 1250 848095332 848095361
    0x715050a11041508061012050402030a0b010816090b0901050d11040608031b060705031909061a12010e030d0f090c030503130806010312121823011802120f01 69
    0xf0440c4819400c0348065902c20012035176003e0700c2c20841c07000340040400524041c10310707944100041c115101006888903071500804604529a501c243c801d503902c00e00401014082051750001030580c11a0103200030140b401480b0610300e0703080200b400a503000101003564001788000006416032114825000a046200055640c5500304a260b42010401420f1030361170354003460410888590000a030fa4100b9001a81d178016440c86c0e074400c6000d400394100182041e40340081c40702d2100c040c4c00d607000003800c00743c8403814880d00b000d010908071004142060740c01e030400c00071140ca0500d268003080845003866000151100745846080c60700d09290001c907699840081c01d80702c09005160840018086403004010f2581541d43e415141541c0c17804880078001c800c00315108400345c1e500506210a1a49a40300900595003011a403048043e4070400340340a0340c80a05080304018012500340801100100054800c42c0c1c0c207011054110b596a028140600b08144002e94000e0003840c0b803121540 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 848097832 1250 848096582 848096609
    0x3190507050a1713110307090c090f0506130501030e0312010b0a0e0a06050a05130801020a020703060f090b0103080901020c130b090708060108190b0a0308040f0b0715050a1104 77
    0x10ba0001e05555501e480307201c102c076600810000340000c1030800c402d80b182d0150081080202c140d011030320300304e00c6412918030780e030901244280c013580c04001001120001c01810b08540e07590340521295100c1d81300c181c6080540403100b40400c0d40207800442c04e150180084910300401d08000740c400e8074082e0409080140001609039a00d54000e80d9180345001c112115080e10b0b251140141481c4103a02c149402d0100100720358030700c0403d40c4c4045000b800404000d65948800c008001e480c2e2000c0d0208480c0146484544020741d2528401e940c0f9095002d03001c2d94069003035031a032001c50341100c2d205504503c6142207041950301c41e05100c03c46101000e2000c01c40340c08a40401100c903d000b09603004000210381046580da9020300d60b96001112805503038403a01c003c1c060a00a81a41c490840e00440c00000020030044202d009104507818004a40b44047d100c00007a0603e00c0341e0000584130703481c9555040c0145456a000039007100315568005030018a041030843d441d0000d60080c0e100101a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 848099082 1250 848097832 848097847
    0x8210f0406080a060f0b22350705030c040218030d2c1f170c04030506012405030c090a0306020a121424090f1017120319050705 56
    0x1801190040c01e404a0300307015041c104444440f440c040c028800401c0039120740403c141400200c1d1f000060210780d61081c0b03014030014101540092071541c580d41c0c1aa60303840d04510188040350100c25a40c00070701800e454074005041001070b4100141e900c0031501c07038602001d1039541c100700c1450b42c0b00c020307100e1440c501e01c2049501c01004c2c030295001c0e0b100034003000410341a590b0310b082d101000e15400c0c0c40d00600c5810981210100c400d4210009100300106c14401080c464002500859104208072007050380c99a060326802441049400aa4444590741e8004540140044e552104016000ca8108a080c3c070005403d0800e551041c1c80710307540042d90042e0b441d03021512125500c069401402840520500c01c607003a200201442c094440351a407981c03e0841d200505409440d00070078000407410078212440400d01c058910094004200700c1c0068491034241c03064101403038002c05841103140020f1f03060100e6000902c00190741310b801c090000d4a10302842803900404442c2c0d941038a42c0032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 848100332 1250 848099082 848099101
    0x140f0303190305191109151303030809070f0b03040f390b120103061d010f02030a0507090303080c0a030e03070b0604060603110301120809031c09060908210f040608 72
    0x540f01c4503402440c00c2c411245c091204040c00c44104002c15101204c081d42c4154101c41c49000d525410800340c00040000414140d1000c001406200300f0005c1e031b41c030700e0b507102d00c02203200c0054424010010030a00025000c241807400c003003a11400b828104909190828038040c50003007505081024a40c039510341e10340c034100380e14400f02900985602e90301d41400021410406d11051000901c500e4542c18507402080c000500d6040034082c0000074807072801074020b080040c1d0000c44200c0707052482e041c002740b0f1980c4606005412681c0607100c44a00e84c9400b0f0030b1555640c440548103082c581c541d424030400c041d0800090200c1405961380034030701e090100810081d40c446170302c00000c041c100b41d0003008142040341103d0455050f82622468569540790221390380c0586240c00f41c0c58000c00800c40503a00c1c405514075803040c0170360f590300810383d2140d00c291110782050142c1c50155100c0c0100d280c419404000c0b00702c00d40c0c480b404a9013441c800841c035944031340c8907810031030000e1154418005041c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 848101582 1250 848100332 848100361
    0xe430305060f010b0a0e0f042705011a33030702010e01110903101a0a0e0703060b19081008071701061d041e02030105180c010306140f0303190305 64
    0x200d000d0503030b00d0f010100030020700d401c0201d00424420b42d1f80c20400c0240f6640c41d40031120080401c0782022568105200382c1d0341107c2500000d4a0b2035081400e101d0303a450107481c603162001c0000780011540d045020003610380c150203800055500070141c41c40020691072001842c441c020503030020030003101c000c03900c0c0d00752000c550000341c46090030b0016048070340c1c01023002c030300b081020350002810b0184002c58a00702d02d04108403541040c501c007400311300c2e0f40114104038030940060314144512075460050303488500c50304d800310450365020502100340c0c1d8030605900fa0000c02d0203003071076501d688480100e4182078990740b050310301c050021f409001a007028001d400040412240341502c20601c454080103940004000801c5c00c0800038904000309410288412101c1d0007600800091805200e5501400c4107070384460340d140700d00c0c541001700d50321074020042591040c8a064480030581c0050000c1e00403040324042d40b60106200e15180c43d130b014010b0000344480c3d076401040741d0808007664484070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 848102832 1250 848101582 848101589
    0xc0d0c0206010b0d1509020301030c05120a02060715020c010f05071103041802090111070f0306061e1403010b192615060a030506040c0302040e430305060f01 69
    0x190009801000141010340a81e20450320b541341c08541014610400e034400d0750340d0303000074850b184007000200c180449580d0001c16111b040e144118195060400c00f13545000c3c5460081d8059800c010317020018003510103d500c5408802d00140c184203e4500301802d4aa6010072003508550b504100304c2c0b05a486914114048020000f4514140c280800740303440c000c02c020140c1e809900040d8840ca01d03445840c00c030160071000c13029107000c0350300d07170103100c040050b14401622400c1c104000443e5840d25104042c0200080c070810305100c0e0318241583c82019a54031055505d03550750410220f40d40c8900203640d0585080818440c80c060034031602c0c0440b070720210741140c0c1c220301032160490181d0340058072417107800c90500080015603c00b0001500c04545401c000e1560081d102840100030b05d010302c50003500c1c0300300c80500c1810000010a580d5a214001446480c0103030b0801d11940c2211300c2040701d004611450140020143c076240c069408400e03481143c06501203001c0003004220307a107029014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 848104082 1250 848102832 848102837
    0x6010309030210091b0807090c031109120127020913030207060c1110020c0307090e070b07080405030304271a010e0a03150e010e010e03030f100e0c0d0c 67
    0x40c14403510000c1d0b840c0d007211035200345103540384400c1e41808441d40d200c0c0c0c510307482140d42d54602515100156202e40c181d200e5821814141111860340340d000303000e42c803401e14492075568106401e6608228000c0340006c10b0b03003506d560714a140381e10060600190911070016490749011740d1045c3c81805580360b001454a002e000202e00b074800025400315254089800500c1c00c0d01107018030b42050130a002228105030303442079174051610328141c2c020880900f0000c0440541d0009962000c4940c2966140b0405815035000300205001c0d60310128058041c0c140110803071401c00761602c000c07038603543c0550000030951103107184400c20200b0b902080d40c07209482c00e6081c4184503500c100611200001007045040c84a120a0035031a030300d0f004840070085401c00e0201000c203400d001c84200502c105511035a103035003003120149030404140600c04c04401031800542c03440d640d51416080d14140030304016002100c1d100001001c995968040e8003641307030251130b107941d0791010100104481c84449d00d80107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 848105332 1250 848104082 848104091
    0x2007090209130c05040e04030e0303160501230c280c0203060106030b100e0105090a030b07021203041203050c120f06090901090b0609070c020a1d070513050103110c190506060103 78
    0x1144c1c8841654111854002144a99140d505d000e40da0300e600030300900d800d03100101e041c8188042050001c05810301840c000c0000100f640204603070180d1201c10f115040300b001c408207858845c410010700c01342030649400c2084081103074000c0c43d440e440100340030001e03004600c01000d61a045c4400d41c010311440c1002c1160b140c40b080030541030182c0c0d0761310505020309102002d6999010740200c2d481220001d0a07046034030780781d140a41c7c201d136040e254900180710303014910300006010f01c11607000e95002042c042d14045088000c40141c20010b1410701009810300001c0201c45006003507500a03040f40303440d9000d42c5008000c0c00785401d402844100b00780e06103c02c140200c1c142c001503d801031b1082d2041c3c031b002d58075401c0c29102a200c03500025000100d4503400180c0f0750f408101ca804209000a9001072a20f0b007075000c48090140c06000d02810040140c10403080d8029800300744c403080203c49007400d10032140809828403881c0501042d01044044854041200501007568402805d080401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 848106582 1250 848105332 848105351
    0xb07022b0209160219170a0e2107050303180d140a0c05040b0f180a200d1a03060705070501060b0a0206090c040221060406030f080a02010f0b0907200709020913 70
    0x1081b1102408414100c1c5400520704201501c24848070b01199400740081d40b00350100d04c80c025018011611402d91400750190208081c600402118034400308100740015420286040280141c60540d00301ea9901d490710500140d004144421080203004442d0420300034030b81024401a22802e081040c440c178585403020080d60707500700202000c0e1a50300e4a641c0c0a950b2103032164010500e000841d4040f100d85220154185051401009408a101001e004418080c1d1480340b0100404d60600c3d815000040082c0540d1700c0b036000703043c6450092001291071696440c079040c866000030380810058000c44104000501d0400c100f52160300150f500318601198010b54148500c0004280c50141040101007090390f40ca54001e04061504544480e200400500c0c25086c0c540c40758402c41c000d075082c04407080141680e44105000720b00f010b00320502c15582c900d01112a880d060f0350200d00c4403002842c54503111020000324000c0e080c604030050b81c681c029810403404018515802600b80c3c204070175034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 848107832 1250 848106582 848106593
    0x30304030c09051503010e0c0f040e030708300106260a02090111101521110619050c070b0f040501050f041802130b07022b0209160219 59
    0x440072280c003682d0004a5850340950f04040c0122845000c2c0e2641c00d00c4011142078102141c840f1107080100c13031814010a442040c4410b80307040f205c1903403440c0c1040c46080c001c100d401c0010032009041c2d20540313150500d01c2c255148803d03000d40010044d254103000510102d40c05c00e07030f5030088105054000005c10040d21a071103868100900084007076801040b40d03051070f4025018001920070b800241c84101601c81604402002c04000c0548180140280002c100b400c1305652025500c00342e4002c40315140540707400c10340740c81240910340c010f002040075107406048000c01404100d502d50301c003a511954481c54034a446115000542c00c0e1808001e80240d0303450000c1220119002820000d454945d0845000307120f01959204900d0260040704210b02c1d001c069008140c544404119003112035210701d2000e605000d8202e0094005041046c1c02c52008c1d510030b00f00350928440404107900450541c0418510b800984503486c000e000c0d810640c8840740c0601600401a008840041c10074909031a80c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 848109082 1250 848107832 848107853
    0xe0c0301031e26040803071103060124080c07080a02010501081002180f0d0503030c03070201110711092505071208040b0a0c050d0c0c02030601090b0604050427030210050603030403 79
    0x55010203c40240101d000d0140c40c0203490080101d2025a0707199195410504035141c080002c051180c001c1000118103141604140c446481400e41489c503601524401511500340242c238140c546a01400420001413a44008181200e0b540e070010034294545050705140c2600040041c841034018041c01544007008090a660488100c1c2c0440240700802c0c04954494140c50000d0000d010010421003219083d00c000e501800096000f00141c148014146030940140c100051814422550140003480c150340701a82001403103100d000490207014200800058054541001c10b1020401e803040c009031020b21a00c03a0b03d942010340031031801e40c1e03696108030380050000820564458840346080c0c40382003601d82150082e1020004c1181484000c1c14000015400728440c3c40f0392000803c1303c00203030042071391010024060a003407030b00340310030800034000c1c400002c3c20411400304d041c400e001c0006600e40e041c50190b000703444149040c0503220180c0d84011310050296100700410000165591304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 848110332 1250 848109082 848109113
    0x606140f0d0b03010507020f21040b091f020c0109050d050d050c150408070b160815010c020a031a1003020d1203090506010f080106081f150e0c0301031e 67
    0x3295036034036000e110080040220040440d015841c000c00c1142c01a0001040301801a000e0200d40464140401e039442019900060180c104d100f4403003000407140c00000340407111401402815612181840d00b018400b8800d0300c14010b030720904642446507002800d1001814080d1076401244060361190341e03841c0903d034540070401800145a02940b00148541d4080c1c2c1c3e05017580a181d8101b500b00500b44e42c00c416000e079040c070011004680c1507d580f5600c080c1024494aa54070346588003003000c1854241a500c1c1810712807031440c00001695045c0110000c0c51048200e00e00c0748450b0100345001481c014098101d205021030240090f070390740405503c502e948907002c24001c28501400324090030140b04020414498200003040d1400c608003500b040e14440002042002d03628185035035110300b1200c0030301400c00204480c0004a5064003d65090400c80d4002e108080d500c0c5060708107010110350f4400340c010044014004c01106820402e04240001c12030700b04032110362a06c440c49001d150 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 848111582 1250 848110332 848110357
    0x3010b0d02090c21040312020310140109080106090609150b03041e080a0206041101021506060c010e0604050a050c04060308090f04111201050906010f120e03040b0c010f060614 77
    0x2800640f20b04900c00884120400551040d181d000e801d007000f003038648003942c0c11404520003030000300f54031a0503c00d680c03103210300481d290206031900628900441d408071105041007401030780455401800d010b68402041403e2000420705c1c5411108811150401600100403040074001c000030714402c01500d800035000103101007800b03e482081c555500c0c2e080710081c20407202296114030f0603000f10f00103105500034134000b541d000c051801261105901d80309182c00024640220b0300310f0400364007a0804100c01000056404e4214412314a099812181201c0a0384600e40c002e04114051081c2d4900e1281034070203002003415035a99181a000f110300150003503c00840010711950f030380d00700c42018415030880e203542c1c180d40c641034510500240141030186603844081402c5502c42c42046450b14901d0f40c1e0205044807030b04112000d0404258001560321042c08040b42075501c0740010200720008000029a0440e072110300170546c0c00551140c2c0a103c0001c0500c08240c01c050101c4e0414800078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 848112832 1250 848111582 848111599
    0xa0f17030a022107120f12060f03061a030a08070302120906032e140306060303030c27060a050c102708130f030201021b0a030204050402060910021b03010b0d02 70
    0x10043c006078010b6503c00390a01420004084141d41c10510044800032180d43d00741195403540e50000646e0064400c84004400c0e0380307000c00115085601c10300100c2003c00c2c0307940f1004800c10010b40b0b072141c80001039131340c00740000e1000c0c1099010095821681d5a1340d0aa90410001c400011228000105207050003a80209003949109900030207031400402c102c4404a850b4407000a600e020211510705400381c400e036004201d039480d0010035284282d4645003568500210b1418001d00103001000c02d8210501040944155036518800745c216902d09030303100c3d40c40c0d204039070005203851001d6000c0c0f001185000340f40c0d6040000b0800020034000c003c80701c0702c3c070010f0510b00300c6000c0c0b0840d40c10341000305a00602080b41c01c040c00b600c2040760300036400c680080860a081d089400030088d4820350050011100f00018145034210341d41c003d0009141a00300f0a1701c0c0045036110503008000001600b004540c81280c81c44c002c2c01141c00d04d42035000304050102e45008c5801d10505000281c402c4003030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 848114082 1250 848112832 848112883
    0x901030b070323100f080d0c0c0f060503060a0501030911150c10020408010605010f080a0f0f0203070c0c1706240d1b0b070b0601030b06090a0f17030a02 67
    0x2a086418254940728030000e071541e4030340070301101440036150303048030001d44c5000050090040d0102810340c0e988802402c55006810002d4480d8070000704101d49180d6040c80010f1030410308106400109850340b2a02d070349240a0003040080e0b03103290801c1e4185481c12210101081e9a000d0321040705006507518408400680c4020b04030b03005c1e0041c50b072003501c1500003000b10b4840f940c018104403540c10f0003d1007110780780d03c019038910602c10110070002e044030340094100104c640169410011a10000902c180741241120680c3e1007194504c0220b004000c040081050f01c0880e10000c0c00c3c0000702d9500b401000c54410b03200c110281c111214101c185a5618000c14081428060304400820300d202d1490f540c500702208121028021034100c8030700c0c0c2c0019003c0e101030304441440358428418140396440c1c000560042c8100c491864018400344828070b03094403948045805410348150074074501d440e00d00403821400b6411804130094200303001c11b981258000404468440c4a00700260801d40e6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 848115332 1250 848114082 848114087
    0xc04110c0f0c03150708041502040308041d090d05090d140604052503020a0902131701200c0a0b071b03090608070c030509100903050a0305031e01050901030b07 70
    0x900c140924050080c1e0103403020041000507010344114090b82036519201c40410450045a811079562021a40c000e0010700004c000103601008440c5a00006090503240c0e03d403003130640c010342c2041140c00200510300d14031080040d01c1540c0300031644010482400500c078000d046002c0c07600c94901176007034010729904201403524980d081030755420440340720385080e0030160364460401140c1320b00401c07134180d01d503101c4003562104e0b019650042c221000d55841c0004a0000350b0201900365042410044003040c00c1c0a030030742111070703080084008100b101903040700d035501c25004200740d13052032002c200c002a17000001c01c2c80049e254125249803800e590340501a1490181c00c5499518105503c0b465000c060300010b41c0c6c025030350070b40e50706051a5101c41c5c0544d566081c5920103004107000340400c15051400c0e96010035002c400d8940080c60550300e03601c84d840c002030780a044010590205c01c11408443d003d001c00612a5803100d1301034075524010100c1d81c804018000070b00b4002c00480000c0700a070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 848116582 1250 848115332 848115337
    0x1060503030c1c020705031e03090409030f020706020a0215070f1203090c05010203120c09121b04180c0e040204140403080411010306031a0a180c0306110c0c0411 71
    0x240a410769a441c450340310440d44580c154100005a10940743d0300d4032040744009103900c2074030340c05001002c00a904103400b105404144981071602e00c801c00034482c154a03140079090549100e6150300d00807805089000c0c1c01c1400540184007194403060307251015a491020160349a140240016611505c41c1070400c1c3c1c8604007003025019500d180420f40c031060381a07020f24209400f815070b038a1910b8880780126160300c9809030342c004152040c00400d0310782c003a030700042c0700d076200003010b501c0741200c55188141800c05010b50000005143c00001e0110b0911f405903120b03954408100d450500c5081e43e6941000c4001d00a02132101404400541103454561011226001000c2c405403945810729004050340c80c01c840440b1943c8445916044c554000e005040c1a29402001511041030b03c19a00c45500e80c010040186103460741c098070303000100880e001d06410300079941419981c1c10750600708141d600404c038a8102c3c11081000e00c48120340403943c0c4000410898002c1440c2081d14540303c41c60 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 848117832 1250 848116582 848116589
    0x902071412070b1501050912011803110d08011a03090c0a030f0201030c140d110d11030117031323060a020307030215131e060615180311010e030106 65
    0x3031150110658080d50003801405030070b44079240c1900c00c1d645603400c4404d000003491000e4042902440203034101e140541c0c2406046c02c0e804000140464440c2e0200b00d0f02c801440300394081104c041c030342041d000c410b029040d880300c42820543c03025454210303540d0760300404109200c461040803011039403040041c000d03628080e80003001c602c0001e0700c17802d00070503103401044101e01082c07804003138038202800303154400c1e081071000d1012401c142c881a4010003804003c1d03481c03061080e0130000e1802c80d0709507204003040005008401034503507041110926001c019001c0c0c4544030340c0148800c4002d40e00410300c0e42e082d01c5100050721110030300e040568061200c0002569407084000c5811080254000003416006010b0b80c00c44542640c0340101d2043c1800c00d40360b21a1040324203d403000490103840c0203060851030804c8050100780d80c4e0301ca410485030141c1040a40007080f100a0800a910900060300c0b1aa03225400b421a86555246107100e0780060415061062601e1081103030f0750b00b907020710010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 848119082 1250 848117832 848117873
    0x206120c0f0403030e280b09040f0c08101410110f01090b070e040516030e0f15010e090d02251d04020406080f0619180506010e011d01090207 62
    0x380c43d00d900c0c001c2c0405440c051080d00511030f80c040c8079461420300d192a0000c503412400298a542840500e1f190707540301c401c0281d0025203810741108040700f82e20403140d00503035540d02c03907000c2d0030101e10400888805500c0354110b42d08404611809a0ba454081c440c00c02c07260600f80c0f295849640030303e0030170851060410041d460003210001340519211400c1c880c0203141d6500c2c001c0d0001100700011070318156020000050038641c2609414003940c822040c1280410845a02c0e0302c00c65200d03442d140c50b0083c00d0622222940c0100300310060305200341e030070203048006405460300d00400250754031513031150482d507006c420744002d001203034100d040f07030103803032034152300c1d001030700003001150081c507013520101c0c0a06d141c118000350800c4082000100201044081c048503100d10b05040c0c030180300502c1200c4240d541d5090500080840c8549400030b612a41c0a420070b90325014030301903124416032182c03e22544105ca0a071007040c840c041306054841580b03005031030320700c0381c21f0811a807041452010031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 848120332 1250 848119082 848119087
    0x513080a0516051e121f0606020d14090120010e07050a0b04030b0133020a0311030c0a0b040614010f090b010212040306020306040b1c060510030206120c0f 68
    0x80c00000b040c12084030440c052440d200c1c55a550502168115030840140740c1e03503903c1e110010620f46040c4165142e80d545049a00003d641c0c8000ba90303d00da01e480440400d96110b808125480d01840303c0c0e200e50a00741440c4c401d00e890440f807988180700d2901c12504120301c51803504014101c5000d03166211141c14000c0221400b505c14083d900c0381c8900410788035840f0200c000441035000360884003034030f900041c0d6a60b42c2c1d01e441e03110030003e48501031500c0c02d50456074003a0090400750380058038001c40c0c1e07030007408040420b040c09440c5030f4100e01c8840054004200015034014009005c0360540d03403045030b007800355555041c014010320b008000c1c1013060122000025850110712510010744101d0942080007116250059944801c1c1500c0c10850345000c2c4030800204040354003842d8410170140000c01e0340e00070b40d13000540028035500d5082d100e5407024044018042d89205281d440b0f02110f0000b4542420b540000c1c081d400341d10500582c0003c000001204100c50303d0075107030b103000c03981c00700d54 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 848121582 1250 848120332 848120353
    0xb0c010e060114150c0106080d0305010311090c0328060303020f070803070506181f0507140708030f0c1b071a121b04120837051308 58
    0x5010380108401001244900000410b1000704040c007424105070090a0020040780903004d9140d0ba00000e0784050207560315000081d1112040c801065510810b07a0000352543c10742c40c112019148500f80240940459070401c4040c1c1044412a5000141d4060b600701303c83d80c4080007882c0c0c11001c0b0b5028501402c007a4000101900000c441d2440140321050790748081d15068400e030789026070900a40070740d0000d0081140322420a401c003195180d070301f084d00c07100d41d04000400088078071140d5485640707540e00c04201680e68400440e0b1001c100a0303040c18509405c948403c3e40901025084404005d085004112002e000b0b0003202c03c1c0c3d91103100743c400c0b040c00403d003043c2c42d06150701c28100c012140e101c2d00e4840340c454000303c8090311800c400907505030700d6a80c05e072550b040740044a03405c880d00400002c9100010310426040292259158035903610350710403842403400e08681b0200210070358001c900c00f000e4820190380301d81456450019210480320400c052147c41e55031000c0050302a00c2c5854 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 848122832 1250 848121582 848121607
    0xa06050d110a0e0c07062007120e01020c090402091f08070837080409020408070906060503070210090f170a0e0a050109030201051c0e0a0b0105010f090509060a0b 71
    0x14071850021505850031940d1900b0320010700004460500c48202c0401c0b111001940c0d6034022003a41e10a10422003242c11740366a14503103980456802da40b9000d403000f44007100c6603c145c080341e103000c00384090300114112402044034480d0150000b0b00c10030341640090a0f00b400e4264807003450b146402e103250795035900d149181c0c071102640942d00c028001d0301181e0011380704136048040c12030361075042e03002c0d40781a01c1ca02034512a4a05000c6030046420800007035024030b54000340024003039030000343c86402d141c451000100e40965201409101040c0104990b11340c0205050503039505522011584070b101741340c40c06540401c8200140150b0009425407400790405014041c4039030142c4584241e020b0182c2003185820b458810140018000030f02440103500c00e40c0540048801954040e003041540303100c440581d945200041e010307600c00d08105d0700348000c1c1030845004100a0820200c42c899591004200107007902951b801a0825004100c07603031120f22500f00188400003d850b00c424448280 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 848124082 1250 848122832 848122853
    0x6030e031921020906120a0e0105240a0e0610120f140a0605032d060412080117060103020d05150a02040f05090c0304030c030215010e040b070507050c090a06050d 71
    0x2c500c605560200b601d44103030380c1807080b5000803900a28040c20240d001c40885440307500217012036011034603444046c0112800340078560245440e0404940d24a5818492070802c0104075422440341c20001c00c00c228150f1484007007904150103880c803141500610f50140c800380342650100c00c40b2440e004a8082c4440f0740d5000f800441503440401800307460b03e015520a0720194020654180c005e00c88010940800401250849240f690403c0f40041c882c00401e0030f102049806480b21002a0180c80f2141c1d0701810581c05001c0601d00310302c540d84000354142c1c0d2288140002030103042c4c0c0c5603100c401e000d020460b41030917028140605500c1c0c60625850f002a420500c55041304c45c51411002c1824a0711000b0380c0e1145904030003150440d96540c03011240d6201d030100550950003903aa0804004240d03682d0b4601901c0c0c4840c9140f00c904052070319843c8400000d104204108044c4500c000256000c107811034005012181500320307858440000e0700a041caa442907600c417460080180070845030008 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 848125332 1250 848124082 848124107
    0x3070f090203070f0507020a09051e090d080906070914062710030b061c060506030705130905040203030a231605060c040e13080405040c033306030e0319 67
    0x741e2620b6018070032000e817918020004025441002200e041c0500315141d8402580040400c1d40719000642000540c0050031080e13450f0b0001d074004101b91070007141c0141032550001d0102c0018100c81c40c1c624401880c150080c0581143c424605040c480260b50300030036194004000078501100d207401c2004041c02c00a014007041c02118a8400525814020300c6044865940a8901841c00095101300c6103a0b440c445070714101d242d0340340c1010036140c480c000076500c140d01c2a2030f0343c1c0c0ea039907424038940200d44443e80148049400c0100700001610007005680a68681d41001d8075900115100e180f141c0c1c0c1c0c40755040700394034808038400284181400c04410442c0c0a4402e440c03d1f0303211403000f10018400c50042e007040c8005580400e83e41440031a031064040d0040d0442c5042a131140006401d81314a00ea9140000e03880c3c25100d095a040362614221151030401d0384040bc400c1000c9003175000038948a94000e00da0303950040740005e03001b48200d424001034107050300c00403245030401405003410400f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 848126582 1250 848125332 848125337
    0x140103110c010c0e040c090501050309030d0903091e03021c0203010f0e0a0c0b0309060c0705010f020d060815150409030306152a03020307060203041115212403070f09020307 76
    0xd00075052414075200b03045100e00540d9440e02c91604207230042d80c2c00e5202820068551208004e0a03078111040c0c03182400c0d0a01c0bc0e41c489e1029464026444080c0012400c99109840819410801030b65110701e1007041000840c49030060392650f0000074014003800a00341c01d540d0810107400304007240031807000c007458404c070a680300140d141c0b40038411a0004681226040c0d2080300818883c0c0b400101400c04940300703000106011030302051072400d907085800c2c504000b548442060200301028002d081c441a0000305004507840c1109002e00c5210a0b4000d5501441d03a41d107990007414841d42051000d002c09030071107071140002000c01840400ba070803580e031041f52204100c4044c01c10001040310030325010b0b8025030400e5a0703510f41500a41c009002280c900800c1c040c0f4504030f80700e902044a2440003021075540b01c07500700e503140c001043c04a19a00c005540c079000c02405214030180003500162480c03803215080d0b80f91001c22302c1c1600e1500888801c021503040000c50f40401d07002184a4101e99 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 848127832 1250 848126582 848126597
    0x1211090106020304050117060f012102120a0608010c0f120917030402010818100c05040504230912120a090f1b0b12150f1306050a0b03010807140103110c010c 69
    0x504000091f006d040c0c841aa00480e44020305402e0740c40740d284161514171800315501011041d240410882c0e10540f4090603143e20342c41007140e1144c02d84a00f84c010002da000078050311044010082092700412002020320071145c11f11a11341906034051a0540d600022140c0c0b4002c050b44c050495400440342240000c91072000a0198500c2000303c0b1952a0003100425001000005072000f401344010280b0811800f400001000d41c1c46020b003000c04407010540300403005107004001c09410303006040c25080e070b1210b071121507a00000310807039140605282034100c807074540c08600c502500c60a04064220082003010000b030240c101e040c91242c1541c2600e01c0101540c50640f11194041c00c03000c50b100003444c10000d84001e07040001c4416411006024841c1c01710084001007203103270014402c0240f03d40c0c508003403003541040605080501003400da89411580b4102d09660385a0041c06429010408002468216406038001409140340364075000e4031018900c05032402010030048441c00140d44 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 848129082 1250 848127832 848127857
    0xe01051b07031b060f1103160f0c152415030605061206030a02030f010608070519061b0b0c03190b0a14030705030a0516080f060112110901060203040501 67
    0x4410481da041a415100c40906488035201c0b010030700da511109072a05522040c00b80c076910040d02c620302c0c000c80b840104c0303901c2c0d0a0040409800381442480c010900841d01c400f210400d0f00714592528a55200120b503c184030300491040140541001303240d041c10160b071503071000101552100054484081030441151806441241a10814400c05400c03440030071002070600c41204500740c9c8008007174100d415480207030f03020034075240350091031b0724447e55503440501424009100760401003604451078040c0b2040480080d040c69083d11940c002e0000d614440c0280b200060450075045812804a945900e040c8140c8480340c0d0040707079045440311f4489107111038501d15118100e4410005030946200608000301100d00822500f002503143c032400708005456074042000301c904520070760180152039800890729003400001c0d00444966004a040c80380c039040f00041440c1140e1008032642042e01040c104040322443d0b060071180c11076a48400407642680000092084503002e83c2c441a0b038016 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 848130332 1250 848129082 848129131
    0xf060201060305120306091305031204031206050906060301090507141606380303040905041202010c09030308040b06011b0b070206010b1e0c03160f05060c21090c040e0105 75
    0xc02c586461f40f2901003408070b40074624540442801c0f502c541c007220b1901c1045110707907010354000c41e0110001006170502924007500d501909000340b405a50020311401c019002400394001405080202503450000613021841034a90444e0000d040140c50b0b070300c091003800000c000281170010f0f110f89041040d801e040719008000e000e0b9900000e03209010300c04c03503451000c0880700420000c070350510050002041007030750b500c5410b000c0c61140d5200e011803e407100c000790075542c054401005100600004002007034220702981d90099006568040a641c0d040040c2c1d039003000b1100419010b11004002c1d0100402400003600614041d0200c0b60640c4e6a50241d8405115080400100002030304404050108000180c05103a03006802d81c1e04080058013140903504a020065400445000c500003d1140c00d01c060b980010b034a107400362600c0a001c4d101040e2031581c80030704c0112420307800094030700d1105001815081070000c01c140211078100940d00d001e07010903101942d0700707802041d03007146080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 848131582 1250 848130332 848130337
    0x204090f080a030510120f21030f060905010833130c05120a0f021809060f0703020a05030610020c0613091d070e0a0612030c1e2a0f06020106030512 65
    0x71004083c0c460400425941c00c87c0d58440b07002c0498003611011403a080d285080300c24001c0340354059500007403580d2014582c00540703446a20040081389494014844a400461071508041598026054604c07021180e03034001001c0000c001285103c0d50b060224221201d204a1803480c06150070301e448607160010440780d21040005911744e9400031401c00005400840005981800202000c1c0c6200491903281100c80040340e248010360814401c104850b1113903800207400a0326481c0850610b07411071005065131201a0440c3d1048100a82020300d0b680f0070410f00416400240c4041d40350006450f01e0001c80e40c0b240591100380342011550440c800300c00004003000c0b50008020150706142c84036104903610701402114415841b80804101291001c2040d21628820b98448241000e5400c0400f80100c0d00c400303000e0080c664031241c00c003003403581800341811110f010480d011544500c22100c00c0482e1a407140c0422002404c001644580660214003200d001c2d605480320400303120315404a52 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 848132832 1250 848131582 848131589
    0x2010509060f13031e0c0b0f0c091516060204050f030a020310020a0c06060321080402130c0c051902031905030d1a280b070305070f0204090f080a030510 67
    0x28558880000e04405541c4241e030f0f42c0500034204a10400e40b580c402d1026528000312044c04140300400103801c008896101940c400740c801481622402e0503036808060b031080642d070341d22a0718120100c00041300c0d01002c541c003011508184038401100e501e00745001c1d4216104043c0f01d020b00d0219444181030100b4900d00b9164001e002e0100710304810500c20007900440010070030014101d05107030004090341314a4020310b010f041d0111007203903000003881240a80b084d4140402c0050810301c4010784940c10b60b50b02e4030840c0c06020510031f40400003110303900a4150050041d00c140c204c5c840700305982801da0480310b4000d40a4070714442c42c4d0f881d02d01c4510111400105a07030300402030503510070902d92002c1d604601503500b483c3c1d0004400d00080c4001d03011141c441c0319000d0880e407041200313105c0c8040e40081c03140e03d4136281420000d4801070401c0c009c8282c090428003016400f5401c541c0c0c0d03a485040c0596010850704480103090900d120140c12508006020926010205404109102002089 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 848134082 1250 848132832 848132851
    0x902030708011517040b100b0c1f0e03070605061504030b310b0c0708070b0601020d23070219060c05150f04120212030901090c090b0901030f1506090209010201050906 73
    0x2d0b05d5550b42c44034042c10042c2172101c0d103042d41c500400c652881c0c0f0014001c1d1484803008020b07203049070415070041814005080c068915000d8000090700303000c07003512512504884001107a0780d4640100342d6400112070400c040c06c03000507011042040480240d0f020740380000100800040000c0341e850a691090145981429210400400038142100f019400101c9080301800d040195a81100e90341110740100d5052000754100300d01035034100a4002d29440d945000e06101d07000149442e02d00c041e01106608503100001c800c41035499107002d80800c030a01c031414802d05640c8103001010707030303102d80401c4882e40074202040072440c042060460150f5400c035071520315510f0b503076a5050740c00b42000340751055004055a2562510b01070015602c2903010310004200c02103d8039200c02102a280c002c50502d51a10055803601e80716030141c10305490340502d00c4811a03105040c480001c5200b01d0700c0021071800e24402140340d0840d500500b880070310a8000380420b4540f0a41e80741c451404440e070144 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 848135332 1250 848134082 848134127
    0xe09010203061f230324061c1104060306061206081504050c103f050c07050304080a0201031b120b01090512150c0f031b0409020307080115 61
    0x39904640812203804620304041c105001401c030846031300e00c035102d50303019000b40c040104949900795606444030300c00c003408954284625007001545500070128001040801038480482d1028a030f40030354402d60580300d0303003615180d0f00d00004020b03050a01070240060592508030380409514000c06040c0c0d10044094650b681c078003491400c0c0418010810350f0b01d48a8881d41d07801039100c41c210004008141c1d42c5604181012140100142d19001480f11501480f1020301020880102f69200c03d8004102c011900352035107405034106004501002d00680800900012807010008035180030700d04c01e803014010f00d0790194440080700061850000490313241415000c644105620a07008007005040c40413000d901d41c004114055642074070200725070b0188001c1380c02400c24401d035a5104602c004400e00e8000303061403c05071404050280b0f00000c1444416070040440341e01613401520350072408540b2440d15140042407001c0070312682003416a51f58080e6030840c46040054035104100742c170780d00d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 848136582 1250 848135332 848135359
    0x9120a0e0603060a0b070506040201030c17010e15181506090f010c15140906060303070507060e0301020d0f09200604030314070b01030b150a060c060e01060f06090e0901020306 77
    0x45582c1c0700801c000d503c6030100c0d00124585030030b80044c0603104d0040c0010a0a4603103840054122580f142140003072001c12405402500c0c042c9000c0781c10f4170101c6c51220000d032a1941b0b0391587c1815100310366800b0308207006048048e6040c04080d846420600000282d940049051140c0c62041d241e0540e0402d0142c1c801e010654001c2c005031a1052140c0206484180b440f20104221a250480220003089030070a01100f59000c210140d00800300b02c014502c1e0210f16540c007035484105108400a0100042c04c095281c0c0d400c0d4103a07003606c05858410b1240200928540000741020401145c49461910340c05109140000f18881c06540c0907045503c4d0609545040e20704001c0740c881249550703020040c16001940c0c036049035001b144113101100d070381c0c03c20035498208a82d88800d20b03401000395400404c40340c0c1d130003240c0c52612a00030034000f030a40b00c102005400f500840e00900d800488401d80000c00c1035000121b4411141c003036443c80b10316141d46008500f07070b00c030030f035000d80d4008210080780 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 848137832 1250 848136582 848136589
    0x6020a020303090c220518010c0c0201030609050108210c010624020106062a0c12020108160507060506012708160f03060e07080111030406060b070510020a110a0b09120a0e 75
    0x35034200251040116610329011f00150a41d241400030400061446d4a01d10855030903020b400050250560203102542c103029010f551101c240c1100d2289400d04081c006101e810382c8210391000c61b442d0000d1081a48803043e031180c6c0d083c0020b0440403d40c0340c8408900091041c8903c3c0f0079a035060347c6002034040382290800240c07140c18802010042040c11603030000e0b2000c60b0001c01002042510f50005007980005007610800030041c1c1d182704407507400b0700c0e07406500900305e030071907039000c1c50015298441c500103c2d14442c07070800d10b50000c801503c0300400459440503440c2100c42020488500d6010f520707160710350608920170701504210040081c0005819500114000c884680c2101c00c110b81d255545825a0210883c0040e00e81000040c4010b10085000e024041e041c2199800d180440c0381da07819503221448841e801d2002d0b404210302d52130308e01c11005031080814007412074050001d0307810b2503e00c007003064030706135400c0c0709001d5207100d18928401900ca00f2541521042d10300c0d074098003030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 848139082 1250 848137832 848137841
    0x5160c020d030f020313090c030c0216060810051c02030c0301090201090b0a0c150b010f090303020607031e1103100806040209040b04060f020408031308070f12020d06020a020303090c22 81
    0xf078055002c144201910114802c0104004041034800811040171160020b4101c80e80c00e4665803c41d08813800c50403505140150142c100c07580d44c90411200e81c0e0310610589003044581085da0301c00ba901207020700d46403500d03807002440346c022010741d0780107005031040500300c03464031034024042035060804010400c42c08001d000d481c80e85040c070803d50300c625a2040c04180713541120f101c507156078180c10000c07964481c6800030350303000ca41400f03900f85007107403006555844000c183c0f20070143c81e0b003c0410380070341c8807924481c0c2d400007030000d0003a404118914245900115107242444945140005650500044081c041c1d41c01402a48407500c0b2a00c400b90400301c0103009a4081d52074052046079400d00d4401040107013a170401843d10384108550314520754005500c09a41d69101402c103000050b1200c0d0100121401078441041d020041e101182400c0c00d0098050049840031134640051500800150b200340b00501c140c035101c5210b01c04002c4551840c070014400f02d1100a03046064031001e500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 848140332 1250 848139082 848139107
    0x11120706270621140a0e01060302041b1b0b010501080c19090305060f07080a180605070503010e010605491a0102061e04020a031505160c020d03 63
    0x41c1051140031480c00d24660025400302001449000c2c0c04458959022000c40000a43c1d101c1031260a04042100508140107024207450710b50325501ca10017030000354842002194058010b01015112190202400b0090050740010460350ba01542c40d1003125400e22880d60790001d00d00f4266401c2c1001103c03410700003400ba00e1417100811072480703000c1000b10000b58901d82d5a41e007010007421440c0190803c080545a20410b11410091090443e040301400313522068403034001520030326019403140d40145030b80015240f6460202405421a0300030b00070350607640b2201154000340d980b0602100d035403241251039882c001060090005a14040100310480d4824146130402c91440c401203200303440240d611b80c1141c80e900c9100100400c1000c45041041f0b0090002d44800e103480c0701842d1085c0c0082c0800010441c40300002000c541d52600c1d200091a0801c001d0500b1003141c00c81c900051006940b4501042102001811302a110384001001580d010b803090700310002558080c0e5404450b800d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 848141582 1250 848140332 848140367
    0x507080409021e0a090312140d050103120801080706140903100b010809010e03190207081b0a05060f0702090402060d090303050604050f01060f051e07060911120706 72
    0x10045110800900040d0082000042c0d5400b07409072508440703211040c0a120010082c01080800e9401096107801c0b6500091124000300000304d0171105400300317220400c070320070300402c1c0c80e0082c1c01168441c0741642e100b0021000032800ca8041921070580034030948405a01c180340a022051040d80c01000d844205c10280d030400c2480b40c00a03040845070382194000590320300300c20070380d503a11442e800e8101032201c0082016683c004031184d120f108020045440040b84440141054401c01006000341481e0050301c9a0420f292031115040000c91240c51103040c0001012605140c0300003141c0484000c510400e29101d455403d10901680003131083e80c1c00041404240c9003008107004d6a4851803003540d00046903c0d0010810003200d801a0090320107444480060094036080282d4017012520760600c01e4072030040d004600c1c03040c12080d20071058030102080b520100728068001e000c0c810b1042005034401c03103c1c9001c2c1b04810f40b41c4000d400c0b543c0c3c0a81020041c007806241884030708000701 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 848142832 1250 848141582 848141587
    0x3031503070f0e04170f0f091906090e0a050c090d050c10031d1504082b0f2f0c1002280c02030a0b0c0c1f060801270305 53
    0xe5240e50018402c42d44105184507550302080208880e01d00c149401e03800c0240c500b420310148003850600e50141c0c40141200b13200004440d8100d5070365805040800020b640e41205140d10f83c00700601c800158444c0381c1c032040003440850700d45103a40c01440e2040042000307032428100c00704100302945c6000b2a095829000b4080031800c02d0b1a103040c80395031400641c40208100c4130501d560841a01c40c00c40341981c907000300b1184018003002c1a880c64200c0d402155454503aa0740241b407508041c0d01c822000c400303070003500500409501c5600465030180809404001e003000160b1054101a08008030648160880030540000088071000c0c00b8600611812900300203840108201283d00c030044540000d0711100502e012247e031001100090382d01d0745002d18215856602103130f0f030707041d01081c0141480c04100001d0051400801510141100c040c01c444000203885a036245545e031002002c02e1403418070b0300100d01c02005002e8078001107001c1e04070b040100d2210300004040c0c49000710440800c01c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 848144082 1250 848142832 848142839
    0x221062404050a0e01050306010605250f2108070f03180507050906100e0405070c0506070804050c060c0624060a090501021e0a060e030f0d0b0a0e090303150307 70
    0x40e00944a80c03080e100c408569141d08007801c11010019540c481084505140c005005a441c04904981181d41500340141c03200724421488100c051402501a0f04800140c200c0050000c48042c1b20740c11802410503806072035880100c0c8600c02c0e010002c0304080351280c40800c40061040f46180000002403400044090b090306505001c408140c005498a9000003400d0069103001d51617150040b00441d44100043c848c038001030701101e424070707001c0d104941d1100005c50301405944222a00c0358008150f6200e4a0b14480c0541b46000c03c2d102034400e4400c00240d42a241007013022510448400001003c8aa4800000070750305004c801c02484103101c004800801ca85900b40500b80e00812511001441382c04c1400081c40c20700400d10480704c140380038564031203075a00030a6101006400c1300020400d51480c503c0285144a04090380d101214000360304c80310780d01c041d8130200071100b04603032007500340d41c2d0355183c11041c1609071160780d6280c00401c0483c040884541c5130500c0341c000075050b80c500c41c0c2c1c1c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 848145332 1250 848144082 848144119
    0x2a0b1906051503010e07182c280507021905120a050705010c0315060e040b12030903060a02131203020705031b0918101536022106 57
    0x120050700a11920b03000c001805101600342400307600003154908402e8480443c1c90f41d03c2a440248038125a6003450b030101541c1054003e03424a040602080000350b900382103a4010020560400310422100320044031039950015010311030184000c1d900419091b8000d4050340302070030f4090320845440c803035406509036015500010306219407464850544508003410001d0039109403002c06820186080d400e04081e001e5040004282e0301a441c1c203410924400000c90014048407020641c01200301885d04042c000003c0200b040401c25005c0c0c4031562074442e84602640902466031400c081107032402e000031003403520080740d030500a1049420075956080031030304040090102d1540e541080405190504004001c540c11496640c803106042008102d01c544070101c2542c40301103a81c49500d80c09420100e5101c03e0b01501070001c509466400c10381808400300c452180d400000b41c6500ba607410244000c1c8262071005c1003030401c036203c984c0d049000201c2c0b41d000404c2c2035484219403e040301080c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 848146582 1250 848145332 848145349
    0x140d06030b07021b09010303030c201b0a03150b150315010f0e1e0406030213020a091a03010509130f030f0e03030705030904020a020c102a0b190605 65
    0x180a0a103081903818100d20081c18420040003005031303403914a9042a8580398000c070541125014a0700054900025200726140c828903510300304519003052441c5150324021540c0408030481d050900c10440308201403100320511440003502092075030b48040070401e6035402c84040c4042c0145072034481205120301049540090381e03041158004615080210358010080f03403040307105030400007001d401d25000a0000002c082d499454903c03245403c510341d0b101c98026101440e4000c104400c41e40285030020005d410007010345001507040240054003080e4152001250a248001c480c80c503801d001c140407041c00090b040b100512114075000003c07480211245515521030342e50404141e0342d07144000c01306503540f4071407481380d0010032245000600000031204c90103c1502d0260302c85e44001c0702607041c208540d00d01a004403200450a02c05944403492020310881160070186a809a51a0022000280c0f000801c0c00ca40030b0041921030b907034903546000c2d440140d900400c2c10340e1aa00440c042c0c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 848147832 1250 848146582 848146589
    0x906151507110a090b09060628201507051c020c03070b010b090405060910030201030b0604090c0f0207060309030f1d0a12060b0414060d050304030b25020d0f140d06 72
    0x2030340c0e05d03503815109181c2410301541110f801c444480c01c10260300010202140000320600184408690401c0098011501e0710049841c85032030724050b641c1d034400d0319195002d00385ca0103410202c1100003550795009405840c0c000320000b403080350301c00c3c01d16544002903109103520780c064031081c0045400140c2c4800c039180609000400c1c503403900761100510080e204081d0115100d800c40c3d104128070008868501ca080742d409280221b080c640540118000d03204c2c640119074103508040584076102d41040c18200035200039400c586001d96114000c0781140c41665009001880c28240085a00d1041c0d15400d10008800c5840000108100014072510b469600102420303011402010078405036100e24280c0f80d46c1560705004046000d900c403a03540f9401021a44500c03160800b00c0c003441410400d586c007644e40084115054241a40544840c60401c580f204149510b20524480700d0320120342c04ca00c10515072074601c500402c00d40d045d226140118003140c07091100f4030040b0b03c207003414080c42e03008 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 848149082 1250 848147832 848147849
    0x40c09020a0c031d0105030619090509070501090812030c09301509071502030c03030a05010e01081605130b4f0906020408060405060906151507110a 65
    0xe03072100b880e002d8130038281101c4445140c4885028082543d03003003021290b010300c04440b010003000c1d03401d0507c4d0700300440f50000300d211850f201c100000714000081d04029a13000362a100c101d180d03942c00050f80d50350020a0b00c649040f0030b00100b440c0c80c222001601d003201d0010001e01c0362500f104101000d42e030900030b031002c030a00c600100311815a81030211901c076030a403820081d174030724028406075900e045274880c1902c1c034000700102d285250300c00e10584e0350032420003040e030741e80341030034155040940070a0081e9480404580700001e9090b80001d8409840e003605a809900e107480d03c0c0401500b00e02c0407140c0f03a045a101c41c0c840105035101c0400c41c00400365401d03103404241055600880000c48a100d01c0b600307401c44885004404601c3c0c178070b40241048040d001ca0300d014503151401c041d002d01c2d444036455104e0076080c4010050041a410b11901c2150101c0710540d0b01c0b84411007203102500d0b58140c00c0003c0001d1700d090201c8820080a2040c010f0b14140c402c0c1c240a80458410300c4240d110014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 848150332 1250 848149082 848149097
    0x8031b0c060a0b0a1215091502030702071d040209040201020c12070f0504020901120c09090c020c4e120d0605030a031202071131050f0f040c09020a 65
    0x2c1640d0707a01c242801000d0648000c01e05a083c202c1e0864070850310303c000f500c108542c0e103406817503030141c1d0040103029a0010f078510000100d0000e41c0080d40007556407030054000c1c041c000c01e00064a82c036500700a1001a0556100e8885401788600c4250280c01641180500003d02010383c0b1903826440301c0e88569001042050714007100384005011a4000031700c0f0f5030041010502c10307039201d544c4800d845003080000503140d510080589218a45911440c00329081c0680305507125000b041c40d441c01d90083d5002030b01c641c81c4248210001f00028014104c000001d01c0481e01581c00c02e5000904c0b43c8004115401e040711400100d203000ba100182c4602ca200c0006c02c2d040741900c0d402100020001500145201c541e0fa640250810222484251026a0103c1c5400911804035051340907040098400340c09002c2c400e82500c9956044040d28085104000c441a140c1c01c1501c24139100707010342810907405880740390b45240700700b102400540d41003044440110b0b484980d4401040350034140c0c0c1724241b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 848151582 1250 848150332 848150341
    0x40f02181939051c09110f0a0b0a0311030f010501020730031806020c01030605090f0c09061b0a150203090d050c0a06141b041208031b0c06 61
    0x1074424410b20041101610300030148400e20140980400c000709007145400000e05181c201d0300750041600301001300f10382107078905038407016502104209004d400254102e1500d01d003800b18003a81c070071b02c2c1e9400181c000c104101c0341540c44041c101142e035030f00e0086070300301114601c2c0c51541c00c203441011121110b1401040f1543e010020390b40101050403132081c2c94a0403201080b400045040c0c001c80800300000860101071190500c01100c080c40b50091007943c2c1c0702d42d0000d64440314002c0841c0807a140070313404505450300201040c490f082800750600b0507583c14000d848a60042804150003040500c012a00c0040203142614149642c1d40180f141450504164500b12540c01e2141c050510402c1803021988010410703030070040b01030a0a60f51412140d02640c17038050316490107042d140c500800c0c2c14680304e017441003d014402c0c1c0f40c240c450105500d20700c08a148118070601556004528500c0001003200000e1680800d40034101d10a0644e505500c0c2e60a9000303582d5010284c00960410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 848152832 1250 848151582 848151631
    0x1205072111010315030807050c01110c09060607020f13050402041503120c0212070806090d09050a0611010204051503160206010f030803090c0316030c050102010212040f0218 76
    0x1a48503004049040d026068445075841001420400c0c101600e40005076900320102c108a0700569001c0d07410340d80e4071154207040c1d840343d0440711b08600080c52140d101007000c1c800140081d0300000181080300a8580b641001116802081c2c03c90b00700029420352035042e0f5402c6101507811118807000b02d0790746002c0c4100400c4400c4103445021045020301c050001c00c01c41c00d01c00e503843d2038509000b032480529000207000c02810410042452107498000719081902040701070061228504440b4200b000074400c6c1e0b860b24950060a4100c10302c9107040180c10302c201e815001c045808000103140c5501e070350120314042101e9035003145840d80082880030000c0c0301c41c081c000d01d600c14800307020b09505020881080c000c091101422a0034007002007019560103201214410300024200c803100600ba001100608085100a868404000c0310005441d4010300071582e108001401d090003995482d80d9102d00981090300c180d80102c205501c5208003030502c14950b0261300040e1121030501500400c0303 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 848154082 1250 848152832 848152859
    0x60c15180d050c2802060c0c100903152a0302042c06030f0304050f0307050301060303090e0f070c0201031e0501060504050a06020109051203041b0b0a080604020703020a021306120507 80
    0x9602c0000011021010003410410100200c075904850f8a5540ca14010070545801c2d40410323205ea00a4226100b03d04031034100684a08807840741d040702d560000701c2e501c5841181c000d24013000304561103c080c802c188644165a04802849040050800c1c1c0c590f440000c3d5500b5081c00c03a5400c1962038040d0125801000b0095405141180203051036483c01d00380c0c41c1c80c0d0040340700b03040c01016503414007041a03400344228409844040c00070043c0079a07034180240740240714414119001c00d80d4002c40e01c40b080380c0c42c08520032070707460312856481031059004400510f0889281101040243c030f910040c062035014690082c40f0a41d54261604d003010b0810030350340c095034001425a80751442d64400142c0204401d40c0001003400003075101ea84a0518102c0c00401101062503e10001030209441078018068002070902c1d07615500c883d078402c403d0004030b200d51000500035a01407101c3c1c00051500100050220b044401c0100e000c43e5600502c40c031941408a00f2500f03504400800d11029003038420 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 848155332 1250 848154082 848154103
    0x8030c0405010305061903060b0f06032401020a1707020109031a060a060302040305070b091903030c0c0e1e0a0e010c170a02040308040330050c0705060c15180d050c 72
    0x50b6450125404c0d0b22540a81b0034a105c010400ea07103035a0311104a40d03408924203850000a811150f03071b0319260b803112000c02003820050400901803c201406c0e035100151803a0314941c0440c00c2045100540c4050700281c03c0031008030b040203400940440010400e100d503400c0c1e003045040718485401c0101c2081421055500725008151041c0410000301e00001448011034401c50111036468085401260251100d4030b004503085400385800010168801c2c80c404605000c0d03035520010396110042d1101030f0310162403905120391035581107106030341d503d10003a0b0440700c0c4040c0081d02c1e400700d041c03081c2034034041100c041c0402d50801a0b03007080300c0700b00c00c0c680d030040d006881145418255a80c01c02c282c0514000584503c9802800c0180c1c4201c01d82c9280c002076038503400d0280742c01405002800b079400340750060060300824100141900b094001d9842400d5200702816008801e0804841c01b0722000301b21010000398403c17094002c0106000d0b24003480e10035522a1340e2100c1c01c0803d2440c0046149 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 848156582 1250 848155332 848155339
    0xc03070611102301030503030a0b0a030c09023403090f06200c040501030c1412030901031541010f0c150e060105010e0301150e1308030c040501030506 66
    0x1c00725041440c0c041444628030840250000d41107075144114921903140c0c0000055140c5844000b0080c020300002840c0301d0f807008401446030f680100d0500082140c42d00c8024942184035206105022440e0060f00c40c1440000c0d040344c94048104031800700c0c080d415175003072903904842d2040003856403000055000d0b001c02c80c182503680d07141600051004503415058408586844018040c550040c801c0880d10800100705015958480c00c1114507201e151058116100302244070416500303040b01402d01c0c45800c1d802440c1040056401075002e001c01c521440c80880c14940301003071100700700f2480f41100c00380140e03001b90780e2803440e0000714100780c040b10030f524000c09403007440103a80c0c01200e4646410107842c0920700d040b0245803101000d400e0500780c011650506500901000c00080c0c40c50498900341c1c1c81615103000041410b080310b500354011100400801c00a001420134401081d4000a022010420111007a1203004060f0003c1d101c540024800080403c919a45405802c0d00203c048 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 848157832 1250 848156582 848156597
    0x30318390305250905012c0f041113091101111c03020f0c100b010f0f050d05060102030f0a02100b0f01051804060f0b0c06180703081c020403050c030706 67
    0x58640560312400080f2043c0480452403c0458184038420450020641c03034106010550310341c003020200a01138200c620000c1440301c004c0110000d8411114043c88001140b0042602d03241c4400e103d0320180b40c14581c1107040204990743e1426180718148030f00780150409482404464001007035013000c640072454590100640200840340300469074a13280d00c900300141c1e0703900300c4895180107008603008040e840c06050714800c5001203d41004903403100903620070702201c810100a40700004035115242c0026000d003c214100b41c801d0344599001101401280d003401e1402c9842c002982c0f01c01c00381c1006030041c0e401010698801d018038110350741c0440e0721501c00d00e000d90008005012302a6210601010790710451400c0c1c40d40e9200320007a2492944030030980740c54242042c2140c1c4000c0c0004a50701c41c40c8001120700400a4900042c07840220142910901e507480c0c54046800114410b04100224020b410581c400303440240b0085109401800d0203c095078101030912030f4070780c407c3d421b20066 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 848159082 1250 848157832 848157839
    0x20405060d05030a0c0c09091a0708070f05090a03081b010b040902130b01090f09060e0f01050a2c130618020108180f0106090e120405010c03031839 65
    0x210944440304050705d003407026000c050401951040f034641c405090345152541801c14800e005c02000303848000300d034400d21207072500302044407841411650b10001410030080303c0ca000d4800c074000e107802034004001c84a0f503900c0361690122944420510b24a481c010010b281003000d00f0b010f0310640b40012141041140c0c1341c0d4020800d03050403420700741d4119039a5160424035030301400c0700001131708900301071100061311f80302c403080103100c940903d0f0104200e27100050030144100343c1c0d1038140c0c3c4000d06001c4540749061003504503031101c000800503503460301c0501000328946810040c4540c038a1111001ca02000d803c01c501100c056242007030300108000d13100310160341c0005203290080303940e820b645005c0600182003070070b245254002d44441d5082000000d1100304a800070f8032040d1845c01039a0607504041d40210561290703214290204201e203020380c02090080c2d0010440251303c9008030b00241540e952082090301c9211000c07618002040000d01039803940601101e07842e050000c01855030b04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 848160332 1250 848159082 848159093
    0x2030c1506040e06150a080111041505040909031e0e010905060f0c010e030a0e0105030f16110f01450f0b0a141024111009020405060d 59
    0x280242149251031203000801c03802e441e00d5000f0035010700307031805440050401240480101d03140d003c066200d1040000c02051310f040600c22111580b1045041a181c580b402d02d40421070404040c1c04003d1010a00001606503024010340301201d1090740c40101815110108030300c941c2c0c00d1640d0004103c030000c0200d0407030740c00a2000c025a5811104151140003003038000c03510f8403d9020001c0706509000c070420050000201801071a4019260f80300e440e1010030046406000884011680b40f0920340410400c48140071051843d0000303207850018140c03c04080d40c64410702010400b030980d518550824402102450300710700851b8035620f404d00703100240c0d6000810f1010380400011102c0d0420410030010160f001901c21136208641404034a0044050401404100010001c4141802c0003900402000f2209420b03141407042a035642c0c002e40210310205442c980103481405452500601c500c9003c1141003801c4600e040b020032004482d2042c00242c0301b0103000c607401510300c080241c00041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 848161582 1250 848160332 848160343
    0x80a092a0e010e24060d09060609060603020309101a150a110f031b03210a0e010207020619210b030c0d050a0b07030f0f050405010507090503070b070204090501020c06070f02030c 78
    0xb03850418081c4d80700d4000103805481214003201500381342181e45c03810003c0c2604940100d9103940e004204840d030301c800540036807004940607855504005e92048800c4c20b15404083c20600c1140030100a41710369022844503900e50403801d45000e0007143c0d9030566a4492015020098018054200c81601d003070220768038003a2214031500c1d0340c51005862049901001602d00d0903e21100281103009070401d2600008000c5e00c4100d900750030407544c1c1128501c14000c0b94442e82c0e010340020b00d451400c0b031501c030b03400c0481d0345a1420455641e0410035014040070b2045c0b611f001c0020000742d202c01c0c24040620344078107081c50b01c0c0034030f0103c2074100200b071000c11040c1c20b00e6044000c1068943da1030004030020701812800090040c58400755145001d01c1f68031507440f55200d08003c20058640200603120403a035031140e0750341035011b418140021248840640007141c409040400c00b18001d5407041d09a8000200a046551104040080980d0b1000c409a040c1031305001441c50810000d1403d602c80 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 848162832 1250 848161582 848161621
    0x230a170703060b1c0f02030c13060503010b0712030209221d0d030b0a080d03050a06060c0b01030201050d0207020a031b05190b030402010905120d1d01080a092a0e010e 73
    0x24402d8a0710020b40c400c3c1d04031210805901070110746d41d00e410b000c00b01554210327031f08990301401c41400100c3c40720300802c02c51781a1850b10404509004040da101102500c110007404105034003403045000326215220540103030240c2c2e11804081c80b80e025049000ca0b003c43c41c140341d1900c200d401782c0300300c05030106640007909801c0ca4007207107285074075000c1034580403103611000e5148034201039002c01d5a032560143e4001c0b02d035070600b802210b5032040112101212540701900144880c001040158021402800300000c210005800d000c250780010b1418105544103a80f04029086940720340009500544045c00080f10303000300700d1000d1404080803d286001e441c0307615030000b000c1012340e80181e1b071410041c200201000e079510090a18540c44c1c1d005181e9a80118030304108610b05d800154082c1644401d06a54060f01c507130302d07a003464028298142d000e4422503240c40e132043e10801100104000206100c101d00502031600d2481544564140d00c034101802c0f00340c042c4611054013190b0303e00003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 848164082 1250 848162832 848162857
    0x60f0c0f120203070216030506071d060a11010f06081c020321130b010618050312160c1a07140114040f03021006080115080a03020d230a170703060b 65
    0x413541d44000c00e038a8840c4a0001480d8000305482c000100800017070260f114040039039030b081414004031024030f00ca08002007219441074003844144001c6204030b6040501c00803030f10002c548402c88600000c1141c0040e0003001d5103401c906400e618214444401880349441072004514198401040800803101c134600c3d0304808034044041100b4076050f856004481da000b0100f04400c0d659542e0162101402c851a8540c00c080304000045501d0045191080811075464082c90400d54002e0b10110010000c0c045503048040c1001103031402915814112105039980c07082d5680a20781003c0c681c0900f0041c80309042da040c103600e4126155001c1d00d4a402079030101d032a00ca140801e1a0603418420990020100d00d40ba0120000310444150040c3e291807421002240d0f106844541e51a101d0840200140241e4411103596450502c00d0081d02e113040000c0d84018080041c2d802c178011180d01200e0b507940094580801715013181c0302000315982108081c1400c0103014a00f280c100e00324001c04000d101e0703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 848165332 1250 848164082 848164087
    0x50a06140d0b03030310210c0605090a08070303050405090c041401030e0c1806010e010201110405060f07080d050a0e0c0a03110402120108071e060815041404060f0c0f1202 75
    0x4400035034200c1001d0b120000e040e070b030f200e00d8410300c4249140402d1060281c5032100c501418840901035603190900c5401c42c06003242e070b1b428032409650a82c0490491900030407507441c0042c0c600c2c420700041010318429501c984e901c900c0d21081007555480509111000d00c0208400c00410300c4405480014100c203003000310742c04c03d0031000302d82030150940e030113034024080141c0c04041d1080c64844a210714000d80b00e05103010380340d400480c201d601c0404001403260b0f080000344541d21300301d405008105500300f41c56161040d10b51b00d100d403a0700300d03103011030000352520b0038407140c1509405024000401800181701c0003100d600000c01c0100b061001030403424566205007215107842d01110304a20323100400544550791080000d645240c680320f2540c07441442034510605110b002c0c00030048a280d56510019500c806000c1d54071840510001c560041c0e603000c80c1140400d19184071842280640e4000440d01101c4910a00b070b40c5107940182c04020345415815a103541098400c0d000300785801c401078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 848166582 1250 848165332 848165347
    0x60108090a32100515010c0b060319050601060906050702030303040615091109030d02030a170601020a15050405120310090504080706020f03160914060a0e040c0306080106050a0614 79
    0x24645448040d00b4405540604044449402c000803c224400e42e407000c100815903850420245007a0784006150000703900b180100f021402c02038100350800402015100214521440d41300342e018000030450f426002840104034042c1c008509030020001c42c01c0040c6805c1d6182d0020340c9078400200000e21480d9590703140305650244408020150183c02c504210340c0c4107480c0148082d41148090318424864144e021411903c0801541c1228000f82c4500c183e0b40c40c2e10011882c2240f006140c0350441c403030450306c2e50114100c004007041000e003d031000030703d50030181032541c107006040d2005003024030b0070006c0c08403040c1c0e80d11100c001c030707004103000107600e40315443c0004641c400c2000141c4914000300b01e84807000070480003180903405042800c004040c0080003501e404d070781d51140c05040242c42c201c0d103826042400017080d205a5910f0180b0020f103441001030116103054115000007035540c402407003400800d12a0001400080710807250140c41d00100402414886901d00c1c4640740124006 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 848167832 1250 848166582 848166623
    0x81c05040b1308012414101d03010911011106070905010c1406070f170f06060d0b1e1801240c0b15040c031a100e0604030506010e060108090a 62
    0x248003420061009011580102c5c1d00321020844104046001c0404c2c1e92000449098546055008520143c0710014010300c0c80015500200c945c40121b1556180b848943c140d43d0317087c4100d2048a10641d0750310560412200010400950780c1c0c010081746e0b00c960180207000e600103080d0350440b002441e100b00352001610b02540d407076a04a0f00d0b90324030710410080c0029550131048500319100e9981e9907034488034110316458141141a182c0818080c4880041005800c04070000c22490700d1241000ca56820080d02280c44c844000ca920b07002d01024103100e49107454000e03c0310b298000180c1904d0340c203504050250040000101d14081600a40c02005850074000c8128011040d0050303540400c510303107281a80d440c668010700c0c140c030a83c82e142c0380c007001c01d0003032044071000d200786161540014002d80074000c240102003010014002d401c88140000c1e6500e6006001441c800c60103040703107514112155002c2031014102e941402005010440000d4001560800c2a0340007107440c02da1041003400b2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 848169082 1250 848167832 848167867
    0x8060d061a130609050610090b07170d06031e0201080f1314210a0503040b090304230915060f07060219020d090504021c15150207081c05040b 62
    0x9168002c00c22065004003280d40d80d02481c100c50620606200c10f039600c0c01000042101401c1d002c0215050f2a03052201481e460041c0401d41e00c14411218106810f20b644a140d8000000c601d0046849860034401c100072108005000a40700c420a025011070f540042e10f20007006080514400380b020000c2d20103c60840310450b0141c0003904522a4005011f2883e15014240f003e281807040c1200c900c0501c170310040c201c1c0d8440700307a81d0f1890b0550f01c0b10760710a415000d025224400b0b03844181b0000c50b034000c50900301c0790340b21f95810600a071001c05900b884401c0c800100f00c408000710010340e40005884150844206c0f400d00c0718411b0380c404040c60a00003c0c00303042000701188840104142c585500000c1010f1109030039101c108216503914204000d0740705500400c0c00d4104c0311f0b00c8030100c80000360454502c0344481003003981083d450304580c0d901019000c9a5000580c003950040120100034403880d2400000848020a4440d060301c000e00035101d107209004914030000360504142103080407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 848170332 1250 848169082 848169131
    0x3120c07080c16050303042312030f0a120c0c020d030306030b041514091b0103020d020f040e0714070b0402010c021917061909031704060903080708060d06 68
    0x1180c8500107100580c0d59401d0700c0c0041403000720280342c0807a00b49800800d98080341c401c8800300c8c20400001144907003128100c24920b4105000101001252805001600c1030a600203da0398813007174041c80c0240300341d400082c0c0700c40191801980f40c91465001e5038400310b103034060b105103190201e1454110001c000950002c0d01c4d2000701e50621003008003021110102c108900021b01180620310202a1120307002c1e0788602c203580c00740c00342c148040a1140709203032103e4141001400c205000040300b040e40d200090004825000080c140141075800038a99002811450a4505d2025606044071640b00e103420140000801e40d00103411603108407052422140c2c05402000d00540b000340c006902d22090050340210001d03401c45c40420600041e1042c4901b40d500450300e600024040680e000f001e02503401d0f000c00000b0b811440924800c607501d98081c5100301000103188541e814000c040b0b002c058151000c01a0b00c00a1203c0e40e07680e201c0b201021034100800040050074181d41c8200b101205a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 848171582 1250 848170332 848170343
    0x1801050f1303020f0f0a03021903050709021e120703091110020c040501090c021e0c09010605070209070309031e0504090c0809010c0f17070c061d010c090803120c07 72
    0x28000581c1e2101140c038004680c82690a004000000350401c03040c101006204c94008156140c10405482c00075208100d404140208103c4c15442c1d444850404050b500403074000ca0f000546060300c4098007100c441001d1001003224180b13580f0400c8a820010302804030760401d0b40b01c07108941440001000c041c203589008100c41c2c10810078810280d1210074a42105100d1880c2400000b4a0f035074600690980401d0f55010300120880601100d0041c1c440700000c0c3e883e03100300102201c280e101c0f0780c1094043c00058036402d031901c800d441000083c0030020800010141001c07a108000398000f50418820729440b000048441d00629040707909000341c0d030000303038507a04106a941c0300e29000403030030f03010300c1d09240241301e9400d100e501641c0c04403007102c0c900300040101c003201d40d00d030740708180c0c503500250030307140204041e290780d15080203460710751000400da01092080989562801d1080d4150260b05050001400e8074268240b6128040c0c82e2005c41c0085d016000140c2800c41c6800b16012150302c00d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 848172832 1250 848171582 848171587
    0x504050607050d060e010608150f030d0804060e0a0f05070b090a150c05070b0403020a0902191116090212240f18040b04050d021c0c020d060c050a030b0402040b1801050f 74
    0x6007c001d040140070340f4000c40261305d0080c0b01d01c0d5420701703d44a80403d000500103040d4104240411241a0001082030f1a8a5625020b16242d801c0c240847c00702c89020b030755040200610781c10800e080000c83d51200c031030070b2030030022410662145c1000c1070480b821100300581841c10810103540c540c200e550000c2c00d5000300e40000c42c00718000c802400507a802600c05107031540e00c0d0001c0008910440c1c3e581105c069002064681640c424a40c1502103a400030039a0030a03901c040f440d827508613803900603640c800d0300440e2254907464888035141e400390760805018028021012129801561842c085001d4400c15100c2400d07600c1d00080c07007094440100c00f50b01c4610341410035aa402606880480c4c40740150104006054030002d4501c201004040071410740302441c80b002d440b1518418800c80c0c00280d04003c07103010541c103200340560500642c41c2d540c0e660a040400600f25010140164807841c4144070900260b0308004c20740712070400b1841d0364025440d204006075881e0090794200b50054400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 848174082 1250 848172832 848172839
    0xe0f041406091c1119230a060f0b090c0a030e030f0c010e0a03050d090606091416020a0b0a0c02191208220f110a06030501030203100504050607050d060e01 68
    0x500a40c20400b8881490380341d442000f4201c5100440060440496020902c1d03528030440140354400c0d2507129010202070240b603d21080b0001d140800a05483e4020f241c0034010720460f4000e52002c001d885d5020000c2580d40c500180c000c0f80e0141c40b04240020115100403224004c4d071009003240c48000c00c4075200c80403a03a094400e0350040b80040003a5003003050040b40c00c40d000414160782507150315a45d040115034000f000003051911426514283c890030002030620780da22500c0400c3c95100c01c031280610b031101080030f000a085186804542c0800046000302e04031075407043d040358589601180c1d103e54103070100e1401300c4c0c1c20041d14a01303410982c010100b10005900042c608496241c0a081d0758602c98240780000300008050092424624098006490780140200d054410107174440b4501441011a07011041a004007020a03034038001481507240400c0f14080055a4010500c030314600359881c42c0d20340700c0c00340c506000d0001c04501141000380f1030b0400d40141584030640a210741e034 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 848175332 1250 848174082 848174101
    0x41112070503070902040f0b0c010213140f220209040b06030903070501060b07031b051e100f020a020d08070c0506190e070803090d030e030f030c0d02070e0f041406 72
    0x1254400c0320700c20f103d00f00700060800d42500940c2c049a00c640d40306480e051070018500c107694411020440555400c10280c1c06220740022500050404000342c142003007264000d10904440c0c03c0c150600c52034049403060001220f8441091040728101390140e1584054000310f000350841c103103a66803040001c030420030440d01c00000b070004240100000d002c0c3c20b545210300c141d18070603200301800003020244800c072481102d41c150703000203101c1e000710f611352260081015080c0340c800040c071500c0c1c1c00c00c00d611a4589054000d0520381000c400d403c5140016030340700030703681d06003a8403020240302520b00020000b5014091070038407240c112080d0f80c4245089000c00c8440c061400b40d11100030b20f40104035115800009490094070014001145800002130030005100e08210b03040307081181d04d01101c401c9840c140008030341d615240740215140c0c8084240581081d07640d0030300c0411584910070400101c0e0302c40805030741080d4010195441600d65061104102c507200761102c1a5202e480280a014003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 848176582 1250 848175332 848175343
    0x918090f0d0314060d03110703080c01060506090a051203040e0a090201090608040b07110f01020d020703023702040905030a020a030807022a180f0415050f0708041112 73
    0xc41100c29903a45000c00718040d07048450360074011428842c2d2100142c0281003d00b041c2c031809000f81416004040c92803c0c1928012480c0c02c00c5407010310114020806200034014480548022210b45007003000c0d240221b00a110140b143c02d1068038240803006a148050084030b02030540d12185400c1d51800000603000f0b082800c5040740010001c100011b80244600d88042c09203a00003800c125540707558400300c54403a0b208100b4086030181010003241030209100400320721a00420160f1504810304001c0d05000300d500c4240c11280200c2c1000c805e100320011203843c013040385e0048030740440007400031a0040c5a0440000e06d07604c00000c2410f0216000210082198403a9542d00d01d0380e0756080c1d007284c0350040301e025460921000700c15030045801e0300040810300103020340030072504406429000741845064078100342c244036480611051180b030381b040702c1203003041440610030390405244994001000800020070030070b03600049420080348800d03d101c1780c54010034a440112900c8070b415140d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 848177832 1250 848176582 848176603
    0x4180f0c180509032a0a0b0a0b0102071206020304050c270619060c1110050a0f030b06030a2f0a1706091801060f12030e09090d0302091809 61
    0x14041e0780010340c840c61207400307082e00c6552201d000c2e40c20311000c45040b1481500c1c4401d000c80e813850060b100030090208000e0900068041d948003003150810800250850311801204c60464100f007109202400c541c4035030b680c520303030310030001a642d40c0d4a0414a0610340104542d941c0088100d01c0c00c1c18288041c291182540300b01c2101021030b40300d100810540c888070692440c1d10708083e1034100a524002c002480649016103040b0144030b1141000500c41a0120000e9010900c04035a40001c158000980c0507803c0c1c0c7c2e41404c01c8032820800000300c0303d010041c1031141c02074036007140a8003d6224502d40c0400058612120031001002d0a0061076400042c07c45001a00d0141a6110040d90140c030398051000541000d20781d4980183c4090040c2e00e041030209599203603840000c0d4011521284401001c5102c0c00607100c0c40b60b171034020034404a18081c175106080403024070449010220f40b45d2032182c25401d00590741e20f03000d00402c41c2159100e9044c0ca0102402041081040c4c02003000b5184 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 848179082 1250 848177832 848177849
    0x1005010305060f090a2012040b22150f0606031e110912190c0513050417030601170406140907030f08130e0414120c0c04180f0c 56
    0x1107036142018804207860040c0e01c540e02c0310341c3e200403804c1ea0070307546c1c48511800701c9400c9008443c22118a020010ba0151600262011a6008001c28440c0c4807101d20380103110381c103008810a0300144840d42035104124041c01c0d2220030400d00c50800c141b40d00800610070000c80074000243d59610180040070001741010369019a0510f07203500e041203124020714030808506260034044081c041c000c1c12100c24a4000d400d00c1006041004921440c130142c00861103a12100c42031410401400300c0300c10449181100e2a08210611001481d13015108105104110703070942c403542d5403c0101d896106940f003041c00182104144828090a038010a0180c800c1200c0b043c00c82c0c441c5481a81c1c2d801961102900e601b00c003040280c00a0302410090807400c84036201450f130240c489695855012099808840c0e035514822174083d42d040900a50040d0001c241e06541440c0403100d40e10b4462114a011a100d10380d50001018200107005a03a044641c208a413401e0030308441c40d001c4803501c95401101d14 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 848180332 1250 848179082 848179091
    0x9010516300203040b0f0f0715091a0402011b0305040504141f03050a03180e16030510060f0c150c0518031227100e01171005010f120510050103 63
    0xb40000110340460394054042c52501c45100c030440b80c1d03600020f0b00c0d004801030400c1848040b48412400d281d95103100303000000c0008203071921001c0303a00204081141d07804110100000360fa00441482c0c41145030790480e41240d1650325048030303a441107401c410350091408041c0c680302400301c000c00d0701c6a480032441d403143d80c0024a091070401c0b581c1c44000e0007944280d58103030010b8400e21002000721050a0b040d000d1584480ca0b017110740004039400551032170391144203841c3c50782c0340c003500d07402a170040c07042c42609007403480041003040c5550188051204180f401c204100d1100300710b01200e0b554078804c2058500b406c40051180e0f20000c07030880d54500746103010304245800300c0c0030049090402046c5180c000300300440700605280030800103259110081a402c1500d50100c0904941e1043d40e0303a0107410440c10024200d12000452105c402c803e1004125009080d5140c00007500c00c2400d1801451005c1d00040307400c2c0170201400e0801504082c144600220f400c03001c2030036100c00b600c0600 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 848181582 1250 848180332 848180423
    0x100e030405151c0f0b040f050603190312020412050f012307120e07050a080c030303070509190f090c02030307020c011206050301020310092009010516 66
    0xa64a0146016095100390342c4801018012081001000011904204207100810340700303094003164200310301c1c45900f9850700c40d1811940361904c00e1902104d0300709420800380c04c02002090ba2001d50441c1b0b410340081c1001d080c414140251503040614003220015541c45444051240a4101c4520119004d204112645d52404810b0140c1241100c101401c03903240e15074030100d0090a80040c2001050254103002c081354840b4a02412462031007680080c58024a0f03c003c1c401c0b070000c203030302520b0b00c0d41022046030f80d1541c011041b603030044250718120791255909030010701d580c80750316000300c50342d030b00800c001564020703402c02407045800e881343c01c02ca01035519100b44c2e101d01c8119124030058001c4d81a0360000d43c01800d051040070201240010180e45682c0031900320791050350302f00c951184d412420040600640220750070301042100080b072a502e182c5400c5284e000700f84241e070502c0f6011801c003100a80c0c0034560004550004288010420945101c0c880c5c5c010034070015520f241c0b11400003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 848182832 1250 848181582 848181611
    0x13060206060607030c030804030903061d06061002030418060e04150b0406060807120e0d03051609050102191502040b090a0608010f0303080a0b100207080d0305060612040302070e0910 80
    0xc41d0039a1305038031508804583c5540885803c0780051007202400704c0d06101001040381ea1050b401084809800415110b030a081c0c02d41c170b0b201e0010030481c483c0140d0031107130755801e5022054504507501038000940412031071512401800c141d810000705299644200720600100d40071503820f4006a190400c980300ca0742c020f220649a06004a40118030141e011032503507803088222245000c080304c00014124030703c80791541003101454032540069100e03014132000303813841e80513540f01d0f482d541010107080c2d15080010352210010032034040511a102c035040305000030048062900c030031a903801c541e00c41d10303040340f10803c2e080700242c24002da07205000418a14000d110442c107a811a83c01424001c0c82c3d99070444032020000d024255294565004c407000341c880707100c07030b544941164014002403810421a64030f4404054030600c109030400092000380d88648040314014600c0304100c1c3c101c0d50b03e50900341c0c588211680f040644403031100400101078808030306404150b40f803031000d00c0724024501c1c56 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 848184082 1250 848182832 848182837
    0xa030f08070c060e0906090402030f0f010605011206080718060302030d200a0305030a090212070f0302010f080c0a03020c150103060e070b04050f0108060114041d090d0e130908130602060606 83
    0x189400405140104a01f480c0c074401555106200508a541c4600c1c8040c0e09401c09001c00d094100c9a91507103010f002c40c3d81c01041180c05070006070400c202d1545415442507844440d40314080c3d1030150550a0000a14181c001c4400f440c2c001d81112190014080700914010001c8402c5218a03c0e59074100414080450150075441d0581e40b5a411615160107034401080d08941c00c903404802d9140743c031000b40040c0031601c000d0880518215906245000250038208200b048008000d000420420641042030961301d41074003502e4016202d0004902e018603101d04131091012051302940000100310480c1c01010440f1840f0040d039100c5540c5582c2c07428203002c1e900420f544001043d401912a5105882540e03002e40149018640c150048424880c0307544150041f4040c1d030b0f078802c1640908001211001d82104001c0d0041440c45d1108900410007090020254482c2110700f030be2024544207500403444168025420070741d04c00f400c40404850f44079601c202d81c054080c0074001151880c281d011b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 848185332 1250 848184082 848184107
    0x100501120309030b060d020901090902120703050703080708040321120e030324120312062e03020904110d140106050409020c03361002100b0a030f08070c06 68
    0x31000c180b28119075a04000303c00003032030789401000020b000b601507907035405040c1c000c004101000542c203042e401031201404130103100b42860b511088003000040d40020300c03801281d0704851000d46951075490100b2441c0302e9035102a24800c030140342c400b02c00c403d04810314001001511100c0c1200041041c8e00d081d545c1002e8100000c2e0020320000d100e145603840c01d04000340d101c40b40d01300340f883d648000856607500e0715045070465002080408540c07094550321500440c0498021129041010603403644201c650300701d0040850250100b0722981c002d4050b544000d00007081409a9030000211860320781065140b080c40509004100030024505070a843c140c400300e543d4546080e0800560001030341c041001088a03110810016107079141a80c00651142e41c2e12141e25600700240b4604009800700d0f046d56032041190aa4420700190001030388182c500d03035020042074040c400c1002800c01500e45d40043d042010858420301000103141c020810507100781c640041ca50f807038010445480c00640d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 848186582 1250 848185332 848185337
    0x11b03140a15051201090203010c020d080c040e0411120d0210050f060603060d0c0504020a0804060e010605100e030718022812020c01020d09080904060506160b0402211005011203 78
    0x40602c19814071020002d50405104c0010803481101e501090131280260000d00043e0046001808000d81c40103400750488907200744541020308000200c884508050720041440152100c60300960310340922001e40c0104110960300d05208004010b521842071030385036000e461820000078141c140343c1c0c95480c001d1801420b064155a07543c0c00b03100c070341c0510000583d0340c07003118000061155103d00041c00107151503512088141814501241503803600c3c00342140f1641403440a01164644001d00c0c00c0c00403080c5000d5880341c00781d4000c00d040980d140c1081090584540085050b0310b82074005001d2503180c2948040d090381c1e0720313030019403001c0381e4041c000006000e20056060a0450b1b000f800a041d1090700042c41d041040c0000c100b1101a03007822901c0c03031404500c041451906104002c0145401c0e80c00a180140140e1040001074007658001c000701005c1c1c02003020340d00c0396240a00e002a07024040c0c00801e26a01c0d01940c3c8000c4402c4042803d0300f064004a200c0a0003042401c03000d5064 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 848187832 1250 848186582 848186621
    0x106151b0c0509091011040f1202100806150f07121106011a04080d0c060c03090b040204090302010e060a05060a060903080a0809010b0406032a0e07050a02011b03140a 73
    0x5040007000c00c4013812a010300c1c800c80d02502c6a66a4600c1001d40c0e142210f182503035100c2c50082d195100300d409502610086856442c0200543c644810944040e07500c0c0c0307000811952500e000407a40301510040e01c031984000300303412094250120003002c0481c001c105a2081c140c2000007119109e00164000d030b02d540144004001d5210403000c0d86080110001c0a50b00f800e0301ca0300d04c2c52404941c0c5461030002041c09a4403802e011040c401c83c1000e450515040c40f91500540700c1d02484000030300000d0080d50380f4812071051510031b512010403422440309030303900b508160460402819042ea0007500c00c0602c0c00000a00c00c0c0a07441d540103c990007402c0781d0410440607400e0303601c548000c102d503c565482d2403211130b41c2d503134603c600b401451180442c4645100c043c403403004146120340c441d46040d50202c100740f040081c01d884a552001091030030b16619035440400301e002d400a904040c01c00020010303000e403001c0e0940c01400d40c0703410044032192280c0c0c585110710140d441d80d072680007609841 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 848189082 1250 848187832 848187839
    0xe0a090f060e0712110a0b0306030c01050903100c0c0b0601030c14031f08010603060e01050108150a0b04050c0403151b0e01110a05060612010b1f0c02030106151b0c 72
    0x1503801202c055140c01e02580d118980c0c0d66032046002d00d541e0012602510040c0c0c0c0e042040c500215440007801c04a07641504520306107011a81d21a09c1d0710050b4144440410186150350b0f04100d4101082c00c645000c0c03020301e1b07000e100649447c6081300d045a111600100140441d44a0320500005003c590f980e111206d800150340074155001404003074995910f41e40e508400d842c9609080f0080c024400000360040c503505210045460340d01c9440c584e6410800104418400051514103007041c0e041c4150b026280c1c405158010450513601070b0300300f400d0208101045100c10f0151003142d0181d1118003800d5503000c030b0101110031140510810504e20140e02c10030700d01c503080701c0d5100e241c181001710a220700028404d10f464030840c0d00f1a41c0b680103d003007259509003003406161800110300288031000985000406103201d000411041c03d4500342c40c2e5400c01c0c8a10280148a40c010300200080741c0c450035a5040c00c40054592404074a0320216111180c0104151000181e04080e200800703d05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 848190332 1250 848189082 848189093
    0x1b010801180207050109050607090509060607080a0519031d01051e090a020301090506060f0d050d121b08040201090b0f030103140a1b06120504030806010e0a0f0e010e0a090f 76
    0x5480303024040c0756828000000010030134860518007501070b40041105107840d01c401003051043d604100e0040a401041c4a416250031040ea54000e5010015580b00c0d941103504640500070743c114022203465181400c58500d8055200251b605400098042c030b40000f4042c7c9800e070f800a41e42c207441c00001414015009030000710a07504a1045001d0351080042a00040d0a440d040c020641c2c0701e03040711040c800c4624110304043d0b407452050f101541c01c40f03001e4580700d44445091000c58240300001203000009000b0380d200c01c2202091580700001c002c14000d004115642c1254224080f500180c80814000d4406059a41e026101010305141d03a017582c0e200c005800a510500a281c4941030002c40014403a00203110094914860100709a20384403009000890003c41d0f204031524003014880481e510140306644501c0a0070071141e0484080c1c00305607480150ba1100b244010350040c081807120300b180b440d604880b0381442d40c41003a100e080d2020704482e00c22800404d0700182d5900f1000245 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 848191582 1250 848190332 848190359
    0x1120e0c0d0213020406120b0a08150901110c0a050601080f0709020d0b0603190516120509070f0801200c1504171612021606180b1204051b010801 64
    0x20b202600849111110002440580e08180c005070003103585540d400384414014421304501c0141141d56903031091405800700c1c0c81d500c515000054a0403404001002c0c3c003000d41211348210400711955035150200100207803500c000301021203442c000e12000040155002818120b12a240f00c068502c01d450100303070000940c40480500d4025840b00304400c020707650240650f100740780240100320b810501880702030880d1001040c04940d518030480701c2c0d104982c00800d010105008660000baa511441410303031400d10161300c140c0083c5d00e00d14000c142804103400c9190b4621a501c5003541c10000031209441c0f50240d0f110b0803405521035040040d5000d80304210b540c016000d824034a00710b52401180d540182d00000e21480c0282007015014100020343c00c6402c442c5146101a19400c07143d20446c562180c0544151401c0060030b02c072200c0c4660071641070900030055400c05a540c2e0110300d41e28065030704100c6081d1024003443c1c6501c422408020640404808140e44200c130070781c241021400e600 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 848192832 1250 848191582 848191609
    0x3050306060a09230a09050f01050405040212010f0e0d08160e0a0f1d060402131a0c010608010e07121a130b090606130b030a0213020c06130201120e0c 66
    0xc90981e81c0068020560050340a21880100e2007030351307804160303003031002810356917111080440c43c0400b0420100f07078141c4544d040d47c0d011540891191194000208140e0f0800d01c2400b80354a021806080e040745544000c0d02d50700c810301590101500910292070410f4200e9440c40304050010b4a0041d20b0701c50359038480c40c0a00240420303404c80d10742c80203001d500704540080c091100414000000a664040c9a95000904482c103501e40680e4004611707021a052051070308040403011052440054a000c1d1070039038425100803c851545d80001c0c0c0c4c040d0009030000c40c0580100c00011641c0c1000d481d24100c1181c002e01c0d00803041034a0014210010390081121007035548401c03121001a0071521a0303405103840740c000744000e08126003009000c1d104c2612413000300703103031500100712500d0104090180580484007a20341d00841031045003e4440e0240b96a900d0140500700039403240d04c03228110311782d4000e83e10460f0050002d03411300111282c1d808002d1391030388030f80b01100d07a524040041e91540c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 848194082 1250 848192832 848192837
    0x1180809090601090b03040b0912090d260705060f0f060a140a091a03010b040618020f22150512010b09040603060f06240c14150705071a0403050306060a 67
    0x41340d50b90701c000500c0d41055900701ca15881c894241700b4210400c1008401c8130401d9a0403915200c003c100150800865600042202c0d07100340800100d030049401444c0720030a9040c101e80d80d030074139250464481d502101d04022034202080030600081207514044c1c41613202404400b20035080c408200d0200e4609040c1552103600b807840402c010800d40504000001c051141400403030118081509448048099030301851800c1c0382004070051090056803c80c004490040c1c0d01c4407240d0203a441e034440d0000c64011001c0046890b600780c003080c46020100c9440350001d00030303507101000844151042c0300c0ca80030220391b99401444551078500c002c0401900007440020039035a00d40e191030544000c860f02840710ba0b0b655804202c1c01c2e42070303805080703060101100c1981c1c045c07003203102901a0303098000c003170507614200011000729041000100707840701c04640c01e20035074030301560010311590150108550300d41c42c80111042107003901c010903001e02e5140d1601c030b003580d44080c180640e540201e07a080d803c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 848195332 1250 848194082 848194097
    0x6060d090f0818030f0616050d0c09082407030506030102160302160e2205071a041403060601020d080c090d0f0506070809030a120902100305040501180809090601 71
    0x180ca001c101d000c0761846020160740750001d010007009103440070041c0e030303000e0340008903152a031150200e012503121034040107401a0035000041100c0c240035450345024114a414040102c43c0c0d0000305030011500b2582c00c45041ca842d40701030000c01c1a960f5400c094058503400403070041806034221f50792201d400750005040900c40c03410708800007208401900941c100c22034410401c0300581c0054040c2054920004036802d240810120170942c42142204402d81d64410380200101840400300800001d030b14801c0804168070b0742c080d140d10511500780d4a10712100c0b2803001c6d040c08101c00d446094160041c0409402042d01512030040091034132210150400c210700c0c56903101903202081500903041c1d88100549842c1c0185440da001d06070009003c4444208885010700004540703440c199440c02141100da808081d10107003003c0e12000b0f50080c01c404550400a0b40340d40b142e880f03580640700a00440350303140820140c440c1c01c81170150100e002000a0f030603900f000441030740c000b80d040c9840d44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 848196582 1250 848195332 848195351
    0xd0c06050c0d1406030d030c020a0f020111070305070f05010f05030604050408040906060206060411310906080d020c15040e0606160305071505010e0a23010b09040515060306060d 78
    0x142110f8410005000f204680f50a128081c20200200e05400b1043e0500700102c0c0d1109a000c4d45d034051401d0018043c034040030301601103902c85e0809001c40c1d0b40580440c0c0d862030f1a4a0003070707210039450048800c030301e4000c0c600040d207600c1458510600040e60301c59600c5c41d22081e0078080603200041c01503681500c00c00c8001841942c2d41f24060080440c4c1d8050246400c00b20100b1098a940041030702c00004180008580341c0742e000c0d420f0a28144000741d00c021401c14540290700c81c0c07407550000c40030f540741602c000b4440001042c00007015a8607400e40c1d11a0b140c25040103001060071101e04020241032005001ba407403851a0b090700312100802c40d5040520007826501801070f0800c007100014000715440e03040040c0c1c46e480e200c002203081001d00c117543c1003512110f481c040040c20700340c40680340e0f9021410307001d0232840ca20780000c0500074102c0c19a110302c040007245d81700100a038006c1e0b1402c000120034541e034041c0252040780050903207207580c540070100000c0e5080601e0791042c01d980d4a41d80c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 848197832 1250 848196582 848196607
    0x14072a080d020c0106050d082a1507180614160210051323040c030207020a06050319110d0c180617060409051e0c09190e0d0c06050c 58
    0x70011460388000c00b60780d800ca00b0307071841d0a48105500046c00385034071032045c0001035a00c5040d994407140c4084400c9062440800f00160020003c60b01c0311340d4081c000621086a214032511807003514241c58003030000c04550000d00c0b0481c800c1c814040043c4e03e01c07210070f1403548038400400d06a9000c4184a07149462600000c2141ca08c1100b00c40c04900005502581001c8051942004100c41c1203201600c000801d000405c2086010380d03144141d5a0b6400445100c0c0650b050b41c0c501c80d0040e190000c081e4550b90007821940c829118524845521300700350612000c1401042d6901400d815242d0038100010800303805005000914001e0081608445086052403148480102403550700c0c6107412034403000c2c2411901c0040c0500c2d0203142001020b0780803840c001024000c00d01d80c901d046a2186906091030f05210801845039480464030b0b0603c00f02811452140d00318080c102c0c410400044c00d418203682e17904602c0035103030100da514424400840d0b420781c40f543d800401009201e10741100725460 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 848199082 1250 848197832 848197837
    0xa0209180c04060b040e0709030807020f0d14060f0c070519050f030310030c050108070f0e030106180b040b040603052104050904050d020705191202060705160914072a08 74
    0x2044c055540400d0404c026101c500440b40c00c05581c1c1811101c80d030454581030203600c51808041c0c021100c2c10300441003500c4498545851980146030308a040c0072030b00c0c9160316017005076080b4605000810115040300018012203c900d5800001010140c04403c0c070303d60040316050b810b0b174080c013514440030f400e044144001e6214000c2c2000400c095811894250150051034210398100500c8200300107986402444640c60b455407420107603204010440000c0c054060303a0060b03d80007000d4641000021083d80116580e41001c807005d10041000e801032108032045440302408076488800300003c404440c10f40000b120110440c10381c502030301c4401040312004182c40448040d8401043d100895a0500c2075030054030044501100c100b20300e2010131511140d5004d11420390080c4e074981c00840d0703580022142c01381e5110050b00c10740c0301d480d114601d8156840c498020a11b0410241144008a140d6864401c50f074588174000200b120000b0380110240071000d4140c40b007030118032440800c804074007 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 848200332 1250 848199082 848199089
    0x4050406111603090f030c050108061f02150a05040309150e03161509051513080109110909010b010219060b0a032603090a0803130803040c0303110a0209180c0406 71
    0x1040c88003528640144080e056500401c0d10440d90001400040c8001d000303c0c7c201d40d070904c0e000c405034440a001a14082403030b4080c3e04e02c0d0b0410740f01303041080e4000c50106003880c15081d9400c0700f5624001540e0a40e00e0440b40100064207c0806100328181040141c8e1341c1e00f11480e010300c041548001092034009a00900a1800e0300c20300100b043c4e104094040c0c01203082860508081441d2201143d0130000d600750701c0c403100d007022880b8015900403501e04002440490001c0c054901942032203801000c0205001e801100c42030300084d00f10205020782120380b03030182c0c001d001c0000280d00b1403840b08102e01c01140d4040c2c9844044809984800a000203540914000141b40b04000c00011000810140e0300141500c140308000d120f61003c10350051445e00310246035036030342d10480c0c44c49121401d01002410301c2c0c070100c1408107000d4100706550950b44251905200103a0f16085195601d5004000035404480c3d0000503545451414807032205e49500411107000103103070400502601c03d00c0e003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 848201438 1106 848200332 848200357
    0x5060f0c03130801180321020c030a030c0201060f0609030b0c0c0703080409061413090203010216050307170a090e0c070c0308070215030c07020405040611 68
    0x1400c840a4162400549903645054820b44907404034901500e0525031800c10026003d0b80550a00c0301c9098040e11900c15030328510b400c00c3c41c60385011340c02000e05074003845095040c4a0402c05840108a130b520045503103d6103d8009013101c600380d004c4080098145d00030820740307402c000c0c0d40f01030b40c2d00045107400c299546400d1304400d100340c00c440f844501c10b0900c00001c0c0b20414001d002a41e0450700c0c140002a031301c403550800e603005803013496070000c005480801c0c29441c660000616a102500160405902c1004c0c00501e003031080c0295019000061010304000f01c180b032484d09402c400e0302150806101110003440c1c1d42d01802200d44188600c40030400d03401d8000140c0c0c110f1540144003140715a12031424064039088000201d003d50104100800d805c0040b10540b0300c43c00c0e2250203a82495459020800903140c0030303005840c13880da14800800c4050f030000c018040f110046 = true := by decide +kernel

theorem cover : BRFrame.Cov 848021582 848201438 := by
  have h0 := BRFrame.cov_init 848021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 848021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 848021582 ≤ n) (h2 : n < 848201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
