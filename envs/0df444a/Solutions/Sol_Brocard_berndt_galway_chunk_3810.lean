-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3810
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:45:14.700687+00:00
-- url     : https://prove2.me/submissions/87a9eeea-e3b6-424b-b566-d52b83eb7052

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 685071942 ≤ n < 685251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 685073192 1250 685071942 685071973
    0xb0a0f020c0a12020d14091306060c021203041202040203190603031706030c1003150801180507050a050a0302120109060504030c060516050a050c0c0a1d150a0314 71
    0xc11144090000034010b00000b03091169410944801c40025036005003645c0190701d81000b82ca80000120440c156203503103602c0045101c1540b6840c40000306c0b4500321010642c5600304100038a0f440c000e407044582d00c03a407907201d40e0703491085008515015488651100041c40d16130002c56100c0304201401902c1800d03010142e00369032250704214003061004c030302e00015039500081107620100031401420010044c002240802d00f80382e0f48207007010384070350388c400e0b84103c2c2a1540005181140c002c011801c0407071050303440c04c596072030121128003e841c030010f22441c1400354030054a07401094045218690303400c020031003109090140031552910030304d0000c500715109943c0301e00e0203529100e03140f030014948041107600090400c24070a0020031314204490f40103003a070f02000402d040890340d030020940180d01d04059446140d600503408080410300a640e20300042c094910701041801c3c1c1d481d0001c800240041c110310031500003207019001c0020a80c1004202d03c00d011113002c1d11111020316424 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 685074442 1250 685073192 685073197
    0x16080a0c0c0b07200a0b061e0d080a032f070302190c0314010905060a0237030b0d050a1101030b130903140901120c110f0106180c08040b0a0f02 63
    0xa800800c00d00d516013048080600561114450660701a1054070225039400e040100003a000e9401a1501c02002c1c06181d05003140c548910f40040400040c3c2201e440c0a101c203900420316a000603007084040782036403030303546070910000000000f000402d041001e901001a0001d0303200307a0440c451900240b8007095443c81c0150287e000303d07425a60fa03030850421000100c08400b02050750303890081030303034080780d00411515007003c04001c000d43d4516082c4c1c020444242c08880e0005d00c16900c2c0e028504031010b11940c440b1103a49a2401d20401d96054100404e01320800c0d40580141c0010102200050046c1c00c150855901410000362800350307140450030034065101024030003580c4a03d82e50034560010459045164200e42552509024a0000b8800f4a0411035840f196855548103201280a4680501002c1c83d1108441484581d00c4035640070305040c0c07188105010b0014001c0301c0c9000c0f1801094280c06036a201c0c44490b894581e00e40040e0f08000303044991240d41e9400540034901d09000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 685075692 1250 685074442 685074451
    0x3061801060305010609150e090603101109040c0f300f090303150614030c0702030604050304060e09011a0c0a060e0d090b0c0601270f06030b16080a0c0c0b 68
    0x2c0001d0258100000030780000e610741c2020114154100c81040d04550001a07003d418105407000c1e80583c48401c080792512062403984e144450914869200086100c806003980742c0c000c49081c007090812401c16520444842d00180c0003400b60075540c008510840806425141c1180c60030044e9400648080f04071140030011114890312100200c06060303140c015a40c0c0042c164481014440c944200902140c1c078228140030944004030000d4030ba0b0588505840700d00f41c002c1e0984409150500d0b110351250312900403a808140340c40c41c0682982032081301d23141a110011041c2e12002c0000c0504685d0707801c40101c0750046d00c10841900c0005207140950300c814041c08004040780c60600700007411170056a08024681d410502c400d001020380040c40d9811542040c02201e070440e10084110342284010010107104d070700300f001d012000502540a41c0c01c0b00d006142a0020f912441c0c01d950315102c00d2000000040d8074074004c00c000110075801a0003e0b025070410300301180465480d960022012607 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 685076942 1250 685075692 685075697
    0x51c05010611010e010b0a061409060f1c060b030403050c0f070b04060e0108040c090b0607140d0305070201090309050108180f0105090c1c0308100306151404200306180106 75
    0x81d0b55060003209000c0d41810315200780c000d0002c0e038819404958400002d109640c1040064040c000400d9807407030458440c10340180002d513603404190806465984040280d0881c1a000010094003452501c182c3c01505d10190b40a403450310742d501c00700c9444d00701045985040c015118242d291040400030f6034001c08000c0811904c4034604040501440b85d02c40d03006041c070941030200400108803000d05000d4948200002640d801d900020640c0340c068030340010400380b1300030002d001d409400601103100c8181540c0600203691004012800e8551905000b008585000c1c030922041d03014000c1c1c65400230b500305041c0400000c3c190414075000d4400d94001c5140d41d5207003440043c25050080c180381040a50b101401111010104203040b40003903c058208101d14001c5501003c41103584001907030408010302c00310040011503500a00248106181910403c0301c1000c00d08140c040e041c0718081400b444c640c00c884031b03001c3c0500c3c3d41c001040941d02110002a00451880300080d843c040c0181e0f6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 685078192 1250 685076942 685076957
    0x40302064606080a0f120e030307260f03150102031c02090f150403201e010206010e13030302071103070608010602070b032404060509150f060c0c01051c050106 70
    0x20381c1c01e2030407107000390003030240d03a001580d40b00080754145140f416000d80c046406904001e4124044400c0940611020752500001460405000503841817a6a0041441199040c810030600c1062144902e0502d110219800d00010324520843c622905145030180152407410350506851801c03404c1c080c94102089078003041000050074044202d0140c80c006542d08012200c106079201d40a0046100080c07500382600315a41190b10790310703111010001c001d01030200010203000801928240000f03d07071300501c40c1c01d0000030f80041e0031010b81d004568020a90400143c41c0c0c60440180d0b0000c502602d550036a003001e0302040d01d080088200810b400c1c0d0f5110302550410800070b003854200d5104403440f840c14014000000030100300c0501c00c20400070780d50b406044a50206003c0c1c40740c0d41c441350f800301e803007010440ea2503188006101010030440c0d0404405582108114680c010f440e003c00c45503102c042d600644c3c2d40500014000c0d00d000080d010950346d8044007030310559800341c10440004441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 685079442 1250 685078192 685078321
    0x7080f0114030a0b0c0403050c0405070c023607020d03060302100e0a050a1217280c0510050703110408060708130b07020a0605070809120d06080f0c150304030206 71
    0x20b0042c68461542210180302f1402c1640c1c00410003643d200019103e0081848695800d03d985408505080200881455072041d9078030481180d04040f41d548026002e040b10030081c7e01e11034480c410607298010322518038104032241c01c803440c0ca031160965030031080c10303a00030801d03a441e07072001c200804c10000303444107102c1c880c501442020794034810800d8086090110001104c064120603041002d4400201c4102c41072040486508000b4071010f0001d024001c142c04081c2c405402180c4039408a8030140149903400c00d0107902032240d803007200860780000010544946c8a09001d507004040c0d0a4400907800703031600ca0030040740b0290358042c00350380290381070700800c00c8034050164400b0103030600b040c5918022880c8c0385ca4001100c4801648000042c0d01c40400c1440d40c49403024007440030440c0c1c62245100c10142ea9006035514807442101082c1240c5241400c1c201200e00c2168141d02500c55a03c6600d8500c90b81450704d94001700e038902a20b074040d0060568403030301c20a24900390a8010b440300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 685080692 1250 685079442 685079453
    0x140c010e03130503031305060d0f05040c050906030a0b0a0506030307140c190b120702031317100905030d0203100504020f070b090c030d0809100603051507080f0114030a0b0c0403 78
    0x158002d40c080e400911501030b2045201d1500d90444400b520502e5030349c152548120010700180210488452915007404184040c110f00f002c191281654102800e4541400705a66811401d0004280c502c1007000180e22440c2c035081150455000740072642480d5013695848621a203900911050ba40002101c02041c501510f030500c0124150300350a5415043c501065014030071581030325441e03101c040220342c0e058400c000311591401218610b820054481e00440f0440c01d620304544007610540641d480350000d14406d162a0171340c017800540c82e00d4031420200010f0b400040181280c0328140030005819152400200015031010034030540e42c09240c0f620b070700b1001010323100310425800f1188601068a00044015401c541800c20803500ea54540c4843d140c0a0210781d05600749081c82e6000003004000120032901002c0c8000000090b5200e100c100e400c00000c65000000303e00c0c08004000918039860592202c0b034014054601c446181c0c0c43d4a0b554541c15150702c00001400201002400f1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 685081942 1250 685080692 685080727
    0x120a08010e010308070f03090b03010920090306161b11030f0c060a03090c03050a03020f060f070f0f4a090114030f070612060608070f140c010e03 64
    0x781001210710315504545905801d4011008001e246a400140840505000d64a030200401040044c15602d40c2c440101802400280c183c0400400c8120b401d040c95900758400d42d04800d501034001c2000765600c1342c2007640c1c419821920340910000c0d4200421031450748c42c0746100c01e801188210a581e1110051502d0040b200c4c843c8941034000c5c85501003240c3c0c0303240803140c408946150104c0c00c9030700f038140741d80445400d502c020050b21500550b40200341d0081029100c1c078032050159203495880000041404108031203910024421007244210030f4051003039207108096a20f0240715600065003550800000700050327454020446404081c15204d241410702c0940d5141e20ba0b2500e002d00e50080760600c0c9060080c0984945850741a6810351010070840200d08160400c44100c565a510060705481d0f0b15521402006d04000380070030030078000c1c00703d280159035684e14002c1d000c902c007800f100c000c1c0c8a50b05c80030071a04100300c1d801c0c080c41e0074084d024940c82c0c46005140c0e02c03143c486030307106040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 685083192 1250 685081942 685081949
    0x706020333030706050f0c070e0f01050105070c06080703180b06032103060904061b0507021503066901080a020d0b21010c02030313020105090f03120a0801 68
    0x808560070020450348020506100300c4809003400c0b03490b544039000d500380e14002c20b460010144560000041c082c6501012030340100a01041d001c596603d41300116400c4c420564003901c200741303d64040004a1007803400a0f030042c001c0c40d001454500c40f44002c05070014601e001e880da801c001d810312000d440d043c060803005908c8000842d0b641514049190b510b0b00008000d288510101ca0008050144c40d8010303511a40c405018240140480d42c0084d1aa4019040607405482c0181500c03241e85605801c0340d0240200903c15801ca62480c00b60340d8076036038085000b070040420340d0b400005042c05080d90320a50814601c8403020b040103043c10455113120050000d42483d1a2041d0070b4060360812102c0b6041510590003581d109040707c0083d000d4940c1044d540c0d08144110020081c00034801e5800c0110407416000f4014104041000c80c1d0b03a0000399002130040480182d001700641c011402064a40c2c0c000e4401c6c0c4400501c1400030741003003240d60303050000501c0068954507a0b5070004146024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 685084442 1250 685083192 685083271
    0xf171b010507020705090603030d1506090605090f040207060e0304080a02150304020d140109051002190908060601030b0d020a060804140f0a030804150606030609060609030809060f07060203 83
    0x3900d81003100940d5078446100317450007410348402003019a101441203075224407501000f070115100004100240012a10440300000c4101201060852103642212048807004103003024035803000c030400000b903016040480c1e00540c0c900c1c06940d002e0702440030b80014404400901a11181c5005100101d0810310840749280010020000140d8490b5040003c05403c141c44509a02400b081c080c010b02c1c0129010301288200b003140318040807250001c0c001245440d0140c040805921800c4e00e4200342c0b40245100c5802010008106500ca640195214a002449440f03110000c1d00460303c030984580016002401c0b4500300024004030b4181203544940c04002048003614080e802038862401c0e1034010200080c0d0f00100e8244026260228500008840308210040d52402c01034020540c5d4850b1545240c1483c00005110b80581420000c4980203400c0a04c2d04a58034100072301c07030b03000e840c00702080c10090041d000440e03d10b201071445480f0700300d500040c0080b143c4014060071a0147c070b00c0c85 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 685085692 1250 685084442 685084451
    0x516150b040b0d030c0201050c0a050d0f080709141311030f0903070305120a0605041806150b0301090b0d1205070c051c060b0406050d1b05010216030b040f171b01 71
    0x315840c0d1001600c00144c1500d090b00400e60980300403121482004000b968504c2900740d0003003408408070f0300d940024100d84410502400c1210f041d0392400040711100046000380a041051074416000304035100e030700071301640d084680e1285403800c40322381000031420a04080304000c0400d14100341160050320680055091041d07650340104184a0448060544960341000c44c6d0f000b1179a4000c8005041c00034801d0111100000c818a01208455402d84a550600b0b404214103a6900f01941c10348071425202403642c1e0a0100c064003805984401a8204141e0080d035000305a5584200500841c04d07500c0d180d4400b614240009124083d4000714454a036060b541c2c9902c0000d05c0c0341c5c11181364020004503402039180c0009008110982c041c50b001240003a038881007140200303ca4841802c80c3d403034250095140c10049940b0584800b0380e0203a610241020b2010404500c0484c1e8014420780703c0c1c41c00b003e030591fa0354501e5440c1402100316540c1c0400c01b0011090424a240001c1c0d500302c00800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 685086942 1250 685085692 685085711
    0x2070c090606090810020f040317091003200c0f15041101080105010f110a05010501080c09010e06011b06150315051f0513111612020601240516150b04 66
    0x9441c2d64401d9440f05d1032640c00150411240e101c1400d5400454015001650b90036070010101d40c1a405112002d119144000c45544441d000f8401d01849030030003441d110b50031800d4540340c0d170340d40d0094028007910b106002030b001218000704254600c8031001d01030343c1c01d20704051624150000c6034850450500c0195401801240d030f0011050804241a02c0c151000154008015007044003062001d0065401d041c004220300d1400908421012816039450050b41c0c2d80340e040c0c08034110305680c0d0b2030000c0d84401d6019204049130460384140e6008000014001890782c006820010780c5903c201c0303240b8020581500488294031038141d01210660514500c85134000c030084030040e15016a6108010504c1408100c901ca035000b8201d680e0003405032560707804180c28900103007030340c1c1130100c8038808041040f0401a00c040b43c01c60483c1c40040140500f0782e00421042d1103034520200c00406c00034248424800010708403049200c0b0b0340940c020032480c854031030080007540d45c110b09443c05141040003a6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 685088192 1250 685086942 685086959
    0x303090b0c030906031806010e1005040608070302210613030801080c22020d18050f0a2001140a030e1c120e032b0b0f0d020904020f0402070c09060609 66
    0x341d0b1900f00440c0e09540e40c1d990b040c1d107a10b20290109400226101e403e00204070030100d00e0405000e9810042d00100c0c550340e0300c04000644d0b03c203001c0c8074480c0d04001401c00041c03e00702305640b4078a03d04004101c0003440200406d1500c401104ca0740200e0a90000800500d038000041300c0c05451071380c024000c54044500401c603082c0300944800100586505043c2c00340c0000c2c1d065540551a072001030090010719620002590708200042d22607014051104660380c00020311848407a50000340d02c204100079048000e80d07040000740c0345050004440d203078425040811700601442602e5240052000c000080152030b000301d410ba02c080e000c441383e00c1c100303286800454030b40001810141c00301e91421000a45030843c0161515038102c4e11858606c40c800c1b2149d14006240090400310821000c4c01480800100b000700c1a11070340c000c002c210a18002d4202006203030351040c00544038440820388030010500702d90003c130041c1d490300c648039418401450540542c0005080e1890507420040c02c04422 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 685089442 1250 685088192 685088197
    0xc13020a1716140309150709090c08010302120a030c08070204090f0f0b161b0503130b07030201051003020913031403071d06030c030f0928020f12031608160501060303090b0c03 77
    0x2180d80b80301c004000203581d14486c00c1804003034410900d01742b0047c3d0700c806000d8194042804100d1241d100e0344101000d400c2c00054080f440340d0140e51b800b04c0100181c440ca40b05d0b0780b0400042c0d8200c0d480321108000700d21141411102c0b54451300e0341d2001907182c0e0410403240c20000e04540342c8079012690481b000c9074040c02d824901d18808408407044117192600ca80356200c0c0c8600d00380c00090100340040c1c200d00c0740000c0d00015000350020b000da1b42e1030314040546a401c501000754401c00c4200428010b20340d0011940c5210b02c40e080001000d40d003001042c140b81c004840c41800078a070b09005c4124410000c00030b91038030206442c3c580c01c43c20900c84501460000902a026004c0410006051110300b00049600c070340000c00905034940345080c101c03007820028801607000d0141849410800d0034980c2c118001045148003442c24101026511000140e405400b511592024000000c6904903c050a143e040c4100c0c0009000c500d1483c01410342c1220b58040640301c0c509200c2c59080384408002c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 685090692 1250 685089442 685089463
    0x110a0e0a050310020d06030b090601051005040b030106113a080603100903270906060c0201021213030b010b091008091b01110a12030b030c13020a1716140309 69
    0xc000d600c603030000d04c1420007003546c0e60000d410401c012080c007a10000c0895441d040c0c80d810b660100c0c48032503442040d45d86100798852840000c01c10001000418801c0c00780b5010300c145c030407c0c3c0300c4848500b001d40389081007004c2c84440180d4506950114280c9511304068840c01506250300e0307a2610400182d15136400b11000c0d070304191140e9a1504052180d039000318210350111a454402098495190306d03095240955540a481c100b030106030f02d0301030760404021950590040a03201100e03100c1844d80d8101b07140100d0340460030b9001000042d55025164080d00300c0d8000140c40308090001c020060002224004c10700c08a4005e1010540011480340703506900540d002c0b000e10740900c0101e4600c041c10442c2c440b14050814000104031301d4080c0c8424104035035800307100024402081540701c080f070740300e03403944008102080410b54000d90058440398045040c48444d40c00d04980b40041c03002c00720b03070030103500180310780209031203070071400300030020100b400001d055203031804016aa40b00e4869 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 685091942 1250 685090692 685090723
    0xb03070b180411160c14030a02010f0e060417060f0408070807150e060f1602100522050709050a0915180c12111905010f02070504110a0e0a0503 63
    0x7000907290341c44540107948280300020419568a4040c1c5144070091203105044525a680070b80004071420f07400c4142c3e6420000901030b00c83c103442da9005640c400d08407408003080c480f078843e500c203c40d0f640c0c80183c00103181d0b040065142280310a4014248007008064400f100d40400500002c00d0310601a900c800e50b2000751642d8900a4bc203118189084c583e6000c3c810384d09207198201c0000010940a000c0c0034007800680403500d4400813a0f00103070102d111840140d0114003800164403031900300c20340110741d084e102d080c0c4051038983c468042140d10000d039020303482007004010058452051992200504004111641c0183c1d1032107d040510002c0c0d40400d6150b45100520780c101450600500385d10069032080b031a510b1280c54880d6120110564190030103100340811414121960070070500c0e1540300412681c00c10005403100f03900d0b0f00c600b200318401c0140c0841d542d1250f200323018111018203c41034071980d011000070041c8400c3c0a080d8041c10020004000a4400007100c00c02103526a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 685093192 1250 685091942 685091977
    0xb04140d0c05030105010323070308030712060503060412080c07031b03020102120406061419090905030c061911070b010612020d050f040605090f0705100314070e040b03070b 76
    0x1030400300704180c01d542100b907040d4078260001003000400300c13a00c545c0600100384000d81c02403d000310b989074042448041e15140081000a00140c0304212101c1341411030040050050b807114080307890800111011074498506100b5088540d412401107070303000e46640c60340791034040b03a60350007814901d003155030401050720811030ba41058001c0d01602d00c00041508003d50034503080c140711018000c184615440b24184003121222410400c05074a0801ca082d008618207c1c90b01d120500100301649060712640401e224486106105014841c082c844481d100c440385011450454101d032009981d84840e400200802c0340000c91000120f811110507080c41c0750006102c41907040644203800c454031200b460542004036010040d07010701e00550050b40c0800c916035071000b11303541d0342d41760000f5140c0c00d511000c8100b0581c40e0150b40035500104038600071401030b0a85c0804c411508050303848030003003a03c004004809007090701c51000c80c000100c0050002c14904184031a1600c5454a0050488500c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 685094442 1250 685093192 685093219
    0x219060210020f0d0c120e0c0d0b0c07080a0302040608010b12190e03070b040b01061b06090f120c0b1f17010204120b0a0f0504030806060921160b0414 66
    0x2800e05840c4e0700d00303000105014156102d800149803800c4807071a803200d44d00d0803c014540b5140060031010400001d04014200c04041d1101d403031041c070080c103080c640f06080000b2400140010040c2089490948000d40c45e00c0c1000000b80c80600b050304500c0000806010188403a0a259202d54001080003c079041150300415044090078002c51081910300c80001d04804201140302d40c0e41c0303da40102c101c209543d803201d40449041042c0f101000d008001c416a1402058560f441501d038a0710810121006043ca40d650300300c0c1100154818012881d55006a41807109100c0c00715480f00c00e03058803980340d00c45240d04041c114400c0c001e6120b80c2c84e00203c050740518003541180c02514481d15213543d00101480c00828903007003290109110b90401d003401300200c1d1640515406079506d40c4400340c0a40e1001d051101642210b01441d034000b80c50201c2416100642c1c01214160a07034001030704245680d8503d030a103101305130b071107039800340703410070080080442d2031401c9640c1c0c404c222407200200c42c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 685095692 1250 685094442 685094467
    0xa02030403140a020d02100e150703020702091003020f03060603030d0c0210020301270912050708130605030a0c0c0209010b030712020406020a0212030a0e011808120304021906021002 80
    0x402c09003000c10510015007855041d800040340c034402c821540c00c44543c42032100c071400c240e8040c1d03882100c0c0c0390710925000b01031030050b00500b580454903140c010305008058001406401c0140e44c406010b4060290074002e5050102240403650f005400905603800c0c0100402d99030704c11881d011180f1a0f03940102410030780b0a200c44200078806100075502d0396111400e03c5502424441045594907042c041e18010494a02410003815000404e54140518940307040e1916400300f24200c0709907004005201001c020051001c01400096882c1c0d80c81307180140c081812600c1c0e948011090150704c2c500f03800107030b6985584034152008998a95104d442d48041540e10301801a2034040c02d50006c1404188a580080e150f110076000300c409070000315104030740c2c0c0c1e101d02c02c2484950008501550810041d401070807004403034001880c00010481d52170686900303281462a100070411000002e00c0198640600841e00740038110701c00348982d078541880a9034540b65010303c0422641c01140000e40041c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 685096942 1250 685095692 685095707
    0x5070c0b01360c02060906010f030b0c0d0e0f0c0402040f09180c240302030c030a05040311010608031806040b030103140307020a0e04061104080a020112060302030d21140a02030403 79
    0x1c10741401410418040402c5015100305a601c00040c86000700280040800007032080c12504044c001480f043e045445c0d140c8084001070090342140030800c00300c5c0300d140561207581020300c5104041d0040c54043d611f01070030f1450400398540f20314014041840214100c201c20012501c7c0000d0029049a4088810018100320400603141040d4403100003210008820004100282c0f1920302246441040d016000c0307020580380070184d260188009101d0030440c1d441207822600074108402034143c086a19801c0d9901a04010321342c0e04042102c505065403604040501c902c202c856900303181c10702540844074001480090000150b51119005080b0107000312149140c021740117219298030342003184004002034808941c55071511111010903540d40d4103590135512035101800303034444550011681546a840d003c1209a0740d07070710010051303504020300108440c458031141a640702d401200152691143d00c41e111580c10800d604590040c1ca4050070743c020400302c0010784907295401d040f201134 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 685098192 1250 685096942 685097009
    0x601090b0c0a02060c03040e0702151602070e010b0405130606020d14070c0323070630062c040b04061a0405010b0921070306021c0f020a0305070c0b01 66
    0x13000000300900204c01c08070003030055031400100d280a50b100d010741240d0342c3c211070304280c4014070008082070114554001e241e5566910748101d6004076151941206a0b000c2a4031540300c000c00014200080d040c12041c2c1440c2c1010140c00f0401c0030300d00a406034a441201084804010f200d2046000355200b02090740c00036600030b1a0000450386a107030060350819201900510048130f200e0316104140001103d00c2650801c1da22a0580300860841c1080c0d4107150780900d0840360000c0345520489824801d0200406481c244c882c1c00d8114050070400c40036a1a10b201419907240c0108800315142e818482c1e0442d900640000700200424040c09030280308040280d401428100000340e18031140000d00361108080b03805c0458103034100b8541143c80c0d010b4690b54900d0b00144000c001152441c0c3c00352200b0310404a00c1c414400e5114568821940e07240940e4121a6001c04e40044465040c42500d0b030001042c1000c0d0003020703d0340c860303410030300e01440f079000d00e41c0e40810a40701e503490000556490 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 685099442 1250 685098192 685098199
    0x6131b1203030915050405070302040e01020c1614011e0c06090b091612050a060908120403080702070905010501020c1003110a05070203010b0a05010f0e030a0b0f0405060a02030601090b0c0a02 84
    0x140388092800602401c4010000c0e50950542164009002c980b4860f1300d000c1d41c1d008000708481031844c4c0c01d02000c2d14054070780c98015503007807003603501104062110080701041e0f4120499914100603080c1ca1414001d410107040207000c8501b020310310080103030710489290904101c2a488c94901e0000040c1c1b00c012801098010860140314640708001181c8022031844035018a2160306d440408200398004038024005900940008000c500c0f140c0c4185200350240d04c140b482d20450072021041008207039000c07800189030b51b0400c10b4940c1e05100c140042c140d010014002d95240000007507440440b881c2071813007140e424010001f40c83c0039505c6101407440398000207446190f007840103400c6030829102a4000e508140c012091441e082c540716085d03600503164114061101803045440b9419501ca01d030701403080b4a100780128000d4072906118442d402c1c1a11003c0c41c191a12505041000d484480000d006006015560307030084002800e40711a20200c6407030314000d210301403400021100117900b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 685100692 1250 685099442 685099469
    0x13091e18080a030e06070e030d200304060c12020118020f0d060f060314030f031b25060c0206010b0915090901080102071e02011b29160206131b 63
    0x1403d80641101e81045181e405031181980c0754803055900700703611500182d15070000300c0e1300c91419009041c11000c2800c0e45075486c8072070041500366844e50384203810440103d00e0360340600c0e0030840cc0390b042c1c052071080c17480284641c15041600303440e108403104000344244510840c003140d607101c4e04403030710010781c1010050100360144480b040c02404140000e0b604040c0f0704181401180001040741e4070f10f4185040245960780b0118240c0c07008075800c9180c100d40400700403801c11208203403205440c1341907604104c10a10207620341402102c1142206006540081c00100310003803020050703640e000001d0320304422400780d492003a8400d01c03c0d0901c280d400007408001140201055001d0f00c421031191b2006014030211312480072541c18217040082c0043c03a00040142070040703483c0500312082c0f040140c1c22000200400341c0c00c0d40060b18900d0f807a00c04102c010050141110946a1070a890310300180c2100e041c103132800b801507400c0f028054980b00e04400c000c4100c000b88042e0340010070f0400076200707 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 685101942 1250 685100692 685100707
    0xc0603240905090c091006050304050709060b0d060e16031a120a03030c11030a031503082d0403020117060307031e0302070609150309080d0f0213091e1808 68
    0x50090000352806800c92240c2c044004c038504001a4241c06081d0320b280402d0b0341131900d001140c041d0300c0100201d800740220440001c641d2030074080c0501400344910300039150000d5035070610444800f548603444c2c684400703052104640a56522440707101251401180c4950042c03560b2902c1d60342422850340042d40c0c480126040c19011904003038191190360b0502c074201c0c0e4050215510081203401c1401074000704032340d283c07090103075005c40550341c0c0c3c20703a070350310540d80c0c075250f000103500480841074880354806540340700800c81c0d0203490807000400034424101030468000070680404440012009003200c80402ca0641e41001920000d6900c0410000a40350303030340039200740340f81c0c41c041100541329140300450564011800d2a041c0c3d82e18405010400100c03040840240051990136500c50f00c0400903800c107650280601204142d19081c0980c2c0c17000074040c854410162544501455860070b0044040ca42c141c4803503002003a41074101040c0f0b61200d440007066050707600001813071500001990b2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 685103192 1250 685101942 685101959
    0xa0b0d17091305010305010b0f01021b040906111b061009090206040504061e09053643031401020c0a1a06010c0c17030903010c0509030610030c060324 66
    0x70f42c10f030380c4194001d02c02412202c09020a42c1041d49006015070071105010601114008a50401950040c80460302c03201c0d5072203c00440700e030415585034680c40041c00340a141c20b0350031a180c0e8080850001d1045141214040389030036400c0c0920340c45141c440001c0700c195598001940c0c040d0000400420050340d440c41c144040c5001c1d82204000d010b44100c00182c40c1d0440d10410307106500f00d0b840c0100e041d429060038072505a0a0f21154010b220880f0355001002c010896031130420903100c46e03031010303500c41c0a804070252548400c04c2c01b81c2803030b28800e01644036404070190459a01c440c183d0030381004104480d000e401000c4d110b02c214420f100700e0000744040101ca08110a18410100710280c81e9a001160403040c0101c003e0f0492410402c00c1102450606041d61410b2003c41620b013405880000039003556101d0503c0c100140e0049001d41d01458103004481d04800702080b104100381c076540c0e450800042600c00c000502d961040d007108581d001c052003010843c0c05000d682545600c45010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 685104442 1250 685103192 685103201
    0x30702040f02070c2c07121b03060b030105060702103f0b031b0f130213360216050d090605070f021e0a09050604050a0b0d170913 57
    0x1991010884800001c48150035014002003103e50043d2603a9aa2a178640c142040c4014007107000f00b090350580741e2160b050701e1240022950003108443c03880700140000405440c0641c11060b080380c000c01c010803071a41c034981107075841c0c2ea06880a2448620030081564626070300191942c0701c1a00d0640e01d040950405841850750003401300c00c080d941d0002c00140e045034015101c45400d0781c0090074201030000ba007264103090300d030b008100000031b1203944080b4207009081d4044100c680d40100d404080c6408100140000d070032482c0302600c00f40a118082d4031a4010701103007460b07100f904550a0481101a0126080d10580004446044e0914504a03a441c03125503c0000081c1800320301285140c490400c80b40780756000790f1030301c1c070500d125002c210300588007941d044188880d40074041d07002d84900070890000c22020700d0006561804909000a0b1200203064a45072880e02d88207060507910710030010f030941e4224520f454142181c03403440f0794510138030b4000c65101e0301a000f001d102402d00d401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 685105692 1250 685104442 685104457
    0x72d080703031805011209080f12040614040209010303030203041b0303050c0609031c0b030307050a080a0206090309060d2c010f11181003090f030c0317040c0512030702040f02 77
    0x39401c0c0080100400c8000f805a02d000c1d140c00149445030410303079060340e500100010707809410345c545091801800b61102c2e40c4400c1d0b841d040101c11408002c10b100c403a20980c3c00e1200c20000401440c40c00d540004c2e000e030814003005041c903901001003000d00c2021500c200d100da00b045855000c554076820050300542003089a40d41c00c0c4643c8000521a2501006580080d441d195800d080000741c003038000003030f014003642d0b60340521081c40f84501185c010001240c10307034000c1d001c07070f41e45d100b0094000b4101000100001e030158410881080aa1035003001c40e07890b00c1c0390750b400141d07480180400340c0c508101c08062580d10051811903103a035050640c05401c51170b00103182008001440e00c1e001d01c5500850100400b444e11211500481b403d2565420034901c019240004045d81030703503692405840802c6041c2d00148009003e202090303041401100e402c21903a580c00c17900c0c070341513548a06e000030f2401102c0c06010748820000c6000401c005481d5800d13030041c403d1064a14140c00b5030025000300741b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 685106942 1250 685105692 685105697
    0x50301050c0403260a031e050a090507080d080f1e09010606090e011a0c12070c060f05032505130e15011b02060310090203101401050a02072d08070303 66
    0xf00c0c4d40c84142d05651080c25074083d803e9145041c04d0128409400904620080b060240c0074030720300c4d03030203251240310b500d100b52960000040d01c0546410030381e00e80301351504542c166a0001802038071298005410950007a1400749558041d91400741c04030000d09400b48140000c1c2c041401c4c4802d00c081034000c54141d59084d50303461019aa90045407429450078451344125040301420b0b02c0d40c54030034038014106d03903090fa411a81400c416505014080d8001002518046001042803120036400134401080500e41e00e0414151300300105203400100554101241e444010503100e009680640181c403546184100c030100b100b075139001d180500c0745007156484040c030b40c15840121250b0041d402e403500e2601b40403950480e03460580c2030043d02d40c400303042d40c041e000e09c840d00061965141d00085120b120312000c941b030010f18000d0320b084816020b80255046c00814000503454035400540e41045034032000f940c00700320910041d800200504424984d100c040308140205001c41c1c0000d000c01200e200382d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 685108192 1250 685106942 685106963
    0x30309030e0f0d230a030e1311031504061a0d18030804030f140703030b030705060c031c09020603070207210c05060a09050915011202030405060f040606050301050c0403 74
    0x881c2046000400490a1584000b04011220200e84070442c80e1022210202c8503482806a0a8840385002404007040b00004c4d06004034801e1400c00c2c1805402d2019120300900c8802c03141c0f0011041c0740030061408448440001004101e950b071500310900074407206040d111142421a000803203603020200c81d100076030404007903404004c070030f1ba090b50f22640c05640b01c1d0360b0340c1c98179030317085a80c51400c10000c01000103180707900c14551008170080428170320075200043d54201400606040000650119104200c24880036104040100c21600c0745449103030300424034051018003200800144901a4104d030000c000c1081080c0c0000380300d0151100f1312134042c0840c40107080f030b078211041018000c240c031441080801540c00c00c0d10107800b0b8201c4505103e10100d80305d07000300315420801c642e14102c58809c41d18104403940c101100361005203112606500e1442e00d40c031041d83c1c95030003421405102c4440c03400035080c0f000c550300503030281200600034031060400c0903018010f60081d00061300c10045230b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 685109442 1250 685108192 685108217
    0x901061d0d0302030a052b020c01151412240103020a0b090a06030c0c050a0605061002031e0304030c0605010e061201020304050718090b01170705121b060d0903030903 73
    0x200700d5100300c1c1da03416401036183c214412021101c0c0d0308034070f004159140f80302440008101d02030642d001c00b0707801983d0058072042c1d200003480c00d6410615408120031001c500c01e0020005411000640c80000d5400c0800e100322044084d00d8450302d001005401c4d070443c0c420307079030358081c0a5000e81200c1c000c4070200c1041e0749442c80400c1078418080d200343d101e007140302c040003c035001342c12181d03403d0140d00340b220a004c00c54460b5418082e56810486095545a041140038a003c0b40c0c902000c2d54944015070621001c140c030380c80700344110181000c51140201c005170070180705110070b4081070f902c0309081c030103541d44840d1281c0d07114003a40c1c802c5c4960310707481081c5403000051003500d03c60354002c401400315501c0c007100c2c20b50007818100107044454071a050440455084403045000b013130551202d016402154030f4642c10100640c114a01c03901301143d40001c01c160004e40007604180c2e648104810640c0c0780c00150b150f12032640c3e9038128a00b411118018942c041d404061020300a40b681209102c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 685110692 1250 685109442 685109449
    0x3160503160e1302010e0d0c06080718090209060c0304171b0607150f020c060609070503010e010e0603161d0603010524060405091303030e0d050d1a0901061d 69
    0x4550268402d041d20860025046031a01c0c2601d220050040c148421400150008100c100c17901d0b07841500e540c8024002001030592010205600080d030380741060f041811045100105445440340910280c0c020032910388698030b28040741c2d440d0341d8001c1103030741d51507950220b0500800031420246180c020543c40d41009150844400d0140400418407440d14201756207803c40d10f045241000021661140d1880798440c15100800207001e14100501c01482d00c40e04100755010010004410400140010080d886210b000b0505407140700d00084020380d2100c0100c1d10f0300d1900310b064140c0e02a00c038800100c106064002104020811900b25216031710003091509031001503800702d600b403681410312041d595010b100d00010420040c611860540d031070300014803015007511032901103c0b01d451b90303508142d0140310380c1d4020314090f009080c030f44005070b00c00381c868003c0000d4256001d403183c0d4080503a008440c0c102421a030001c203c1880c650f1500380c0100748114a44813500401c03009045030042c1d24 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 685111942 1250 685110692 685110733
    0x8041515051003060905010b0403110f01020604020d1b0902030a1d0309130e01020307020106170c180a0f05070305071202030c07061112040501320a02130503160503 72
    0x140041a904150345000203014268521401a104044c1c3d04e040c04107414a00d03000c1c1d980200010318082ea02da50031342c102181d0460005100b9031103070341e914603a130340c41c1c0e6004901154000c0e012210200c804800e0300300b451202e01941130002c0c00d280807100104d482c020650285000c2d006480341041280301040c2c3d0156a85c90b0408403101aa0060152031142e1910041c80150381c1d041180105001032034005d541c1c20381c0c10a6412101503511110240084c03080d418000f00d18150340002824004000c0c0c010441c0351301034500705d62441d0600000200b507210300d5040010b50900b00d400420282c40c0c4514001c00400060b1641c80000d9619034800d00004021b0007035074000c800c0c0031141071610401c1e9a48400411a00a000b5001e010078031003440b51818040401e88034900480020403040e510840e404070380442e1424641102c001e0091183e114005400300d150f006540c610010b0f500d45c20703014a64109200c542c4255414441e4111125207000900c0c400c0080b01d40035030480e4040d800c000c00e0310308204c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 685113192 1250 685111942 685111961
    0x90604141501090f060f03060606030c090f12080c061609060513150201111201050916080a050c1312290a11070b040b04020906010801081504050715080415 68
    0x303101d40d80042c40180800d901c22802901d0041c00000c203070756036030384003411200298000d440c9543c1d251010000381f40c160050003c00061403400c1e5420509147e410340b07100b01c090003010071500500302c100040050020454289560038002c50302c403840d01040300c031410014411000001004000c0004229004806645070340120390865072409040c011202340c1088003030740c0031381159280c507040350089000c00c0080090440800100980e50f0401050210416000d443c0e8004060252508180300d0350010060f608a1843d0b0004640c3d92120500d015081c026100781d00050f400c086070008017082841040c00c03d041c0301d0003111801114203d00354661142c0e05601850241c2c0c100300140c00002d15901811105c4043c180507414009640c44094907039100700d170101e034104400001c0c001035103440c0e082940d1142003442d00041542c1888001c5445a241c2c070900780400402002160401409000c00b501901055202c280e07500d0ba0018020400300080c0c2c1c2c240d0b5243c0e14803601d0760800469000d1241c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 685114442 1250 685113192 685113223
    0xc04051909050709050421050a0806060a11121b0303060904140307151d070503100b0d02100201240b0405010f02010f090c050a090b0d0f0c0b0309060414 67
    0x52000804224050501c401d0304480c180140180404c620449201c2d86020754000c3d1502d410007000680113240558209400d00d09011003480803641882e80102400e0f0700c1001554401d880310328110040e109049003040080007409040c290106400081c4060031404030743d850036918000c048400d103500c074481500d100390403044c528006004070b02000d06141900c80c0103070440340750003240d407503841c021001c0c14000a403440c2c07034510001201040340031518a0049603405080c54500c1c0000099941c6a003414252800c5c1c0c4038503410303406540300d0000c0100b158000d00180505401c03c80003e000301a080c4008140e14003580c03003240050798002c1c034001500d155500051809013030a0040d2880e0403c8403980d001c540d01c55040c01700d80b809500519014510a030302d040b9034982014200040701d001134000c080c40d40c0c500700407141c0607a150b0007040403854003c40410107580031400d081c82004529007110b5080c09002040c031170070000010394644a540a0228902c4101c09600402d40b0b80300d1f4081c07034569 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 685115692 1250 685114442 685114471
    0x510080f01140d15020c01230f09160e0708160917010609090507170a0c140409020301090312050c0f03040f02011103041707060f05071b050a090504060b2205060f0904050c030c0405 79
    0x7a42c2007603400c9d20781c03c150390104851020304a480c1c0c91180d00074540150000302f034a8401e00c00c0c041d07000160340340c0120480c00d03d0030681c15030601c0108030b41418455038080341d0046201c0710740c0c0842035110b81d01a01c90131009021003507a900f441e686ea078489110b01058440d0300c080c0320b01103460100300d0400060740180318080951414442241d412076105030a644a46e8030448030005903424412082400d200340c4444014500035109c07402205c070010802d01410a040044c0601c0b1904041180c6d40a60b011f100c01c9801d9126000481c0c080442240141d5540b000007000701d0310b140719071021302c4444200030803602d050f40c907003204468403244c2d00551000315034144880400100100210044081c0001c404450160f960001881c060447e41c4603005d0759a90b001408280610342c040d160000800713490140b240b018a07458040060070085990000c5951034012a80340d03907517580360001d0140c0050504216050a06000b516808507000580c401d1195600c40600c0b800e00e0302078184100c610960284 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 685116942 1250 685115692 685115701
    0x60d1109030f240411210d050a141e03010e0114031606120b210613021c03030209040603080405090907061211070203160510080f01140d15020c0123 65
    0x890502d014004503a940c0c1060b0b03800011b9101c12201d1900d0b00c0b0819041c1d008400c00058150070090180241420068200945117046801c052010a015400d08403190f51fa400b081c0400000c001a10712007000401c008000200e1054121149058420402084800300c02c548200369580881c0203500048481d01d101c108043c80c0641da40708501082201d01103040d906040001e005240d11380d030150380c18128280c801c91000c000300501588403101580c580c21945281c3c0000e48032040854003000e035201a00800390415110360107485007060050301c288803603510303131425074856040b034040e160040149800007001740200040002c211a01506c548452507907188010b40a010500b022003580d0300100804401610304009007141c19100081005100b03040004108208118a42010401540c43e060000c00030065400e0360441d00300b1a8108626000c490200c2c0301139050820180c114503951840d007840c102d1540080c450442080000c0041842a142c0c2001a01c1d0b08400404400344400016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 685118192 1250 685116942 685117003
    0x708010e0c090315150901050a0e09250501030507020c090a1107020a0e0a060f0305032d0d15060c0302030904090f23060c09030c010c02060d1109030f 66
    0x21604000c0340900e0034607012441000c0f82ca01a034002030318031008400d41c02c100d1014400d510310280b0800856446c0ca081d450100040c002c0c3d51540200610802c1c15408682103080801a240c02d03002d0135000f101c1441403101c6440400e042a1250b01e01290400c40024403952010a85200302c880040c02244651994103018008142036415550700c3e0000304440d0000d0307a61349002c00020030300580411290b14080340200c0c25104107078000d00300345651100900c0020008029118680c5041445c282d10340a0590103162203d6000800c00b03240100103168102c6d4190380e008003120602d1002944101c40c0d91348012905801040400340040e041400032000700d1a10f03800c1940e01c0d41c011800c6010380c3e40c40b80c0394004440c105410703810301e6080003000076000d10b00910805a01c8041d003020281007c000f100440d4607003c904961074100a100c40080301150798a00650b14202c4030204100114501c144610200394003007840030b4401c3c41602d40030320344400002107140200c1c00c107090a40e1300700740c0304510 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 685119442 1250 685118192 685118219
    0xa3b0a150c081e0403120c170d0209060406030c021c0e06030a020c060c0c06011211060304020301110307020703051b100f450302091303110712020108010e070801 71
    0x1112151000c1003c40c100e6240800c07054204a14a0301866440341740d842c0c00409010442640000e0001c40b40707081c00483c02c2c0d5801d0100b41942800c0f845e58803004031006000902c43d089507587e10000118012480b88e6251b800440e07a6103239a022a0141100001c82500406900812000050700c00b01d400381c450504401035030300035800c0d01015080c0300301c03162a6030034100304540034680e01c05c0c0032403c0d28140000308189401001c4801c96039007800c1481d100c6502c0854000512400340b440000070404544003580903851403422454030b55100d041020780251a10160b11003503030548100c11941c500c40403601d81516030800000c180c00d1540d0b81311072065409039100026841481017a00c2158020880e011a040130390600444400401002440c2d8030805110200108501040c9803020b100507140c0c18005c40e0040e6010552511400781032400316451205910000c90390b010703680700044ca15519030214030030541300b44c1b1078140c2030781c07120b1903103100c06400c81c1d4010015070542d0040080e00b00c3d4144 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 685120692 1250 685119442 685119467
    0x5061605010209040606020a03090e0907060311130303030f0b061c180c030803010303123305120c09010602031201061b02040c02060109060f05150a3b0a15 68
    0x903003801c03c03500020b001c4a803158880d40c0507800c40005001055400181200682010710303003404103040c0400b1095454180d40204028541d50f45c2c051420b6488850940ea1800501418841150f40385c2ca0000c001e84440705100241d0703410006a403a1070300d02071055401c4601c4102342d810807004646c545501606940520341b0300e01903400008000f0480e0964010051800340300e045641e07501d5890020f225100c2148041d02a5280903516003000c6020003001c3c8400041e0144401407602d40320110b1000c00856110302c0e44104c0c030310400b4080980200d0803203843d0034201c80301510f50780da038802a40c07284607030740600180c1030900005010072406079101c003807004c100ea03080008500080c5c0c0458201c81160b03a4040c007507449000108401c0400c0d000301c0d0b024180080ca00511a490240880d0400c4c0c070048101410780404202c41ca0400d01c20100340744403e0300070405107100d00000c0b03032560408248511164444414056600035410032044501c12a00d41e44801c0b0403400c521f07034080740c0181c007148 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 685121942 1250 685120692 685120703
    0xe060904181109070e0303070b15131e02040b031305010b120c0406050f131a04020f040614030c03060d03120f1a0d0c051002010902030d2106050616 65
    0x281c58490900101501d500c0940320b02000402d00408008025400d800105003008200c55101466070741d07240882641c403016170081c2886541d03110060380b0b130895144141156004104960558410781c5c06800c6840000117200c20103594098800000d4182c0c4900d00410315007036410400700b00042c4010007040c000e40d0107a130002445108840000d282c082d24049020099841040b007039116181c244030b443c1c0104011039000a06162080208503030b03522141080d110203070b844103d40350712120303d01740f00414880140211341d54002e0320160440743d0410701802c00001c042c5a21500000d2020702180c1c080c241030011103055070340e0716040202c9200b80c0c0804508002c9048030218123007800e0302a080042110113804100201d0529184040c28040e01c00c4501c10050f01c82c14001050788902e142e81130b103109036411040554130394004d0703000d440c040e10000c0d0580718210000b03060907806403041c0c0c64036005804038402103a0f403070389010942d407039405402d9021004102c03049282c00c040780055111885403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 685123192 1250 685121942 685121951
    0x2090a0315021c0902040e061b070c030b040507030317280f09050d031a10030506030a0b07050306090114010f0e04060f03050321040506010e070c0503190207150e060904 74
    0x503680c010b90160182e03228000f42d07126880402140b80c24040d4074041300f90b03800204030340d02e00b00b1109600074144039007042c80300a00140c10424408401036600141d5000010458103060525100b80d803081548070507000100e00190540609941441e564007908800c90281841c42c0707884000d105100d020009000c06d90f07038802441040303549600400242c10301510180c41800200100541035a0500c4075428a164011a00a030681d580d205007040c1f5a43d945030000b4550b5508002c05e241954049000e03101c191000c040180701039016009512440d4103a0f240000303a41c0e205025400301d0000280c0c4c50100b000302ca5800021449020076985c3e00800030302c0490890303a590042d074600100ca400507103164000141c0b48020304a9107148170005240098080700500e8240c440545514040c029401e040800e000419400e600c511a040181c640010559a031043c0b10070041c184c0c0c005140d8080e0140c001d10b00d00080c51139900c0240150080180c8481070304004900c2001000d600c040304180d03019585 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 685124442 1250 685123192 685123207
    0x40f0e0604030903020102010b01020106120611071707031403062211040305100b0d0803070e0609060409091202011a01050702061e0a08061f260c0d050a02090a031502 73
    0x8200d0540282c0c00ba4640c00d00302400c50000a00b520b4400a00c2c41c10b580c10440308000d06100c00c2c0e60602e456800100020b40840d0740c8000300444e100d05000a0000100319180e030345000d02d000c2c01400c816120351203c7c0c102002c443c081a50b5400111030740d0754884080003062021900601c10f52101c40081400018100c9420816000d103402c5078106440710340c096412603140f4001d600c1443c04460003210110300000c40e41e5102c0849100c0201044c0401040340c01060590319040e00f510703c1580d0041c442a2601d8840c0c07140002030000e0101a5000074100382403d26550040c441c0804100703c007041000c0c51440e074001500c2c0c950040b081260445803c00c0200b00300d0340078030903820560f00e06036503990351840711700c100401c00c080c007510340c40c8100b00610340403c4a50b1014090752501d01e1504100307064854800001801d072110f040c1c0301400d500800104820464100001c026030043c10f0b408015079107a1203100b100300d000b40e0b103505412008142d420700100e290700a00e48102405840d015140290 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 685125692 1250 685124442 685124471
    0x4080714120c011e06051023030a0c02060a05040203060a24080304061214060409060e010509030c0f010905210403050f1b03030a0903062324010c080405040f 69
    0x31048082241d80d6403080d000d1444028560500d000160a080a0291728201400074907404042c0c5580e00501c24020700ca004130130117405d921012034651152403078603480c1c295070b0780c00607020b1026200c00502840000400d12921407246901558015004000c02d640300c11171030004105245011806d402015148900f900490501001800918000d0742d11039160003000b401c1b540d00f021440800c24107060b8940070421140220300d601920445011a19000328281070008103009040e44109500304400c00c940210004000c00c50500d084003194021800040d815080744e101e403000900c160070020b0a031207031802014004607813074440b0451603d00b5a6950f150392900008a03403258542d00118038420240c501c1c21102070b142e82c2c044e0065481d05412500051900505000040005a5801162084024600b1030b034914420f01c411042d568240901c00c200d0190f002c1c081455007481c070705040d80e070750b511030f0000c0000b07182c1c02075990381014140020080540000f150030241c150784c83c00175206903130 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 685126942 1250 685125692 685125697
    0x11a03061e311406040803041e0204020c070503070f0b1603021c02010903021908092209080306040b060c0714063702060114121014011d0408071412 65
    0x1542110300e0550b140700d14052126403840a4944907a801131000c100100c1d050508695120b98884841450750f0258444000100c40079040650401d101040500000c41e0004000301900c40c110102d80b0810703640d20740119071a030240035074000580248803032014180010890f03085035102c0d00550314203502402c020a24140f0310802000142e4440b0101c00905406000e2880d000c44e141a441e0206070040d160f0b03074a07510850b031010703004103d05100c00010151050800110180c03411040c000d406079810104615081541c2c0c052089141220120003403a24000f100d981d080490302602d20b040c80d09011040c0f000d2100c044039000401000048620440b54940520503c0c806018400c00c0c03040c200054005541d420114056501890051107406540040070000501c2100c0c0c2c008882c80c2c03240494100020084c101d20300c5428280010509007102c80701034142d40c0c001c40e20401400f06182082000c8009460151250804002030000308511203ca4120842070300100d640070010710a50150030f5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 685128192 1250 685126942 685127011
    0x80d020c030711010503070c02100e030313050406080a170f090402030a060e060a051f0504180603050f19080714070311040c091a0a0207090204030302011a03061e 71
    0x107400000d404000c0000f041070841c003c16081c82c20900303500c1e25090241445100040c064425084403421421080c4a0800e10322140b0010f403e0720784170020002c0d0081d518049000d01d0344202c0c00c1c100c0109807504006400e000c155000010104400008100c1d040301c6d500115032040040f038100440c00300d0340c80d40d00081d40101080f21000070000d140c400c08011040300602214482c61000604122540d60001100003400706c2504e003444200700c810042d2200d1140368809041c02004c900403040f203c0582d40301600b103e0041040e81d0f050b10341d40220640781c8032402c22410a898000311003002180c2508040d14031641710300e1820594540010503a4680007203a402211821116940c501250806000d4801c00825505003032428a050803c8040446c80c1c001607007001000c00714100085c0c81c420402d40c0020415010f08664898903801c0080c0600310501d40d1100c0240706003403114403814001007903403182401c4880d01c48142559042880319500150484955a00000b004400c44200d01c015402c01e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 685129442 1250 685128192 685128217
    0x20f0d050904050a1424030a061b0207081c0314040f0201091203020304050607030507020a0b0705070b040b2710050c0f150f09011401150809010c02030d09080d02 71
    0x1252071080420080d1480209440425810304001000001c08611a190083c280c40702513040541011540f000d0b80c050308031300940c1885030305640300034042c407a4001d5401c0d804e43d004048001e94800010381c1d56a08601c90b5400c2c0342e10000030114180c0920f407050320041c006180101e411600000440c40300c401c00c0e1010b40304144085005400c568100019000174218444041c05c01d40c01510080d4480c00381340725242c020f26000500208242c410030403140705540c001d02000c0140d4452501c00c000ea003144004903400d205e070000100b10a442003041d1400c5030020b850440c54180494a12580301c404140c2c3c81d25840c10018118442d86d5038801c01c82c0c500440ba0b6a061389894142c21894544110b485000301c003900884007040600b840300803043c3d84007981100214194450a87d900e00400042c0c00c00c2400030340e00400441c1240441c8003440740a0681e07a41e40300345466444204d030072181c0402c9001d0141e40104540307a07a8800da50006180341e40150a50350406501154100603a44031000c510f49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 685130692 1250 685129442 685129447
    0x7080d0506010e0405040b071e0e22021201030b060402090a26031603140c19050c0301110c0609060f13061107030905010801060906170c16061a030616030b01020f0d05 73
    0x2142032740b0440c00c214081001c5840c50011181d0072010b482401d0003480ca40c0a102e0703070b403103100c10302ca84406540d19640c54403004564a4044444d00d4036240801c0c04126511002e03070300410700c1450b040c02a1411080d0003840304d0b0740a45010b0514230581d404443d413071140311100884021716401803014080403882910074404900c420f203001441c001c00c0203400c080011092181c4030803070400040012902007080010703c0111090b080c0149040c1c1c101c034100c3d0b410360030f001c2c1040c0108414009045c1d5119000e0450710280c40742846561502d0040b601030302c002014400140c1603642902a030403078103008460004600f8010301c3c0c09003c0da0300811059001c03c2c0c0d6034104220f5940c0c03255417903006044500d0710203030503803c01c4002021000011401e8030a060400003080384a44d80d0720859031a82c1da5102201040e103a01c0c43c00d80003030402c010340c81030056915100076400d0305010801c5442a681c1e00301c0181c03111140c500940081200c2c60340c8604511884c404041c0d15402040b600b511443d05450b1b654 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 685131942 1250 685130692 685130701
    0x114041209080a0816030c050303090a0606050d0201020a02270c040e09150105010c060e1f0f020c03070b0a1107050609010f0b0112050c0913150b07080d0506010e0405040b 75
    0x7040c40549034045502d99222003064004510301c030707054402071845182685200704407414222800030610501a010740000001e000d040600011300804c010700c181c0782409139554840400034103144406c0041d0161b002004950014540302403415000316402d02001c04000481444000061045541d908401c60014051001d001c1700c40d012640554032740b00078003000d01c0030904202c5140c018800c44e414044092651070030060246c0002d0b8039841c0c1942119228207241c1d44014000d4043d102e003000080c81c25003406440a694000c40b020016814015480d2007840c8e510900c0e2000018240e2032815502c07d4134101e4085504000c1c04003600403002400b5038204580c8080c210303802406d507050928941130758040303282d030402c03034154003c800071900051541c1c518180700030300e105456002c0e03403003018040c003000100e07010307440410f42c02e541a4240c5001e41d1100503105044c854000d0140002009028800719508507130481030340180d040c94400d9452170000302003001e8130070545048034840705000410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 685133192 1250 685131942 685131947
    0xd0609020c1009051c091d1005010e01050913021216180501080105130605030d030e060f0c0301032009070306051e0901061b05070f0608010b030108100e01140412 71
    0x20181040c1aaa0422a10743ca6503102950b8410350141c0900c684a003800c1503a4030b0340039241c280c00900c900104e004036049a1603010a580e903007250040c00c5810340907004111940310300070f00368034200180c640601e01a00003042100503c0b40703411460032913400b00b240403a52000c1140712030240300402c61601070068049009000d04d05420032250391140e00e1042001680c2c3d0007003840341100c00503034126031085d03042002c0350090b007116002030b07406101d54411a03407410b0341a0700c60044c0e841e01e0000e64000340c0b1107580310010880300342d400303c1444c80180f0040c8080340400c0784001c200c1c401101c0b0b000c0c0011825002c110488001c0322101d0204e60344034820005804d04030808a21106c003141d1014250440800042c01c00d038040c09101c041002002c08480302c4001d604403c2d0600d90002d044844241c0d0390030650044081c0e030b0145100040e000000001c00f1001c90f8280da042e80c4451b4041c064420902d02280d004141c1700a0091603592201c1781c82c0f2041003007980080c0160b00440b07804403c002c461402 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 685134442 1250 685133192 685133203
    0xf0d141608180a0e130f02010210150602070806131e0c030c0e0f240102121605010c0801120b0402130e010f0e030a05090d0c0b21150303071104020d0609020c 69
    0x1130444d040c100c0e04204a140c100303201d211040d81e11050740340b0340075650700042703251036a0001221003203440d03c46079460058034141d82400711030042d4200c0d00120348855015481d00c0003900c015045560101850300041d5020100701207020501c19490000c4009845000d0303103000d035500c1034507182602042400000d844078800c9910251541c180c140c9802d1002601940041c1d0386100b0308000c0032000702401daa07100b48200c1c0802c0e22041512619865401104401600180d000b1a0990700c1c001d81070f0000d41c040d10f0401d0403164803040501c4040d80c5601c40c030b905108014012a448501b1840e20040c9170380324030a821030710382108000250544026800703021030f00c09400d5024258000d00070210781c40d5206046071030941d015221003000220030b184c4a03448443ca508400c00140c0003045000c804601c079800d0b00303070322201040e5006464460341d99074500c0561030103e00d038050b0402c00007500420410004040390000140c401441c00440302c100100311140768020384030082d000180c010451008211 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 685135692 1250 685134442 685134449
    0x2e090b0d030e0d020a050a0b091011120a02030d06090906050606090d15140f16090e0a020a0e03010c02030720030616030207050613050f0d141608180a 66
    0x8203440c18a026407009400000206103191295038048600e40c2103440b160311100080c14003030b103941d85071500e03004200c9554020b40c078403d0152041001c000c2085104800942610584401030325034080d1b0300782038042c10380c0141c40030b60661008000020305100a40714150050015000001e4001c1841c503140060b1600074180707911581041c824100701d5540d0865140b10303103034007484050000c2900ca030100084d1160000c103400d0307030b51000c08002054480d40802407162805426200d202c03811144c041d9510042c901612400d1802000080c00c00030250380140081070050800d04179501060000900390b0782c00c4c90b050001a0400700e1100c0c1005407419a04c2e28070320361a40c1c40b1089000400200c3c1d1f0310b000c01401d007101500d0312031640f21464001c1d412960829042000d58a1900d0080700126003603212080854183c441d520b0100340d41d020200b942c40c4246c400b940c40900104100c40040c106402400000035030001464201001400b11002400c0c162010020740640a8141c000c00001d04000e90 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 685136942 1250 685135692 685135699
    0x4120f020f0607030b01090e010e0402091e0414010914011b081e060d0c0807260a0b07021203090c09061203040504020a0507080c0105041b0311092e090b 67
    0x40c0c5079040ca8070042256640112145030000d00c00d084100100c40d94092503200c03075180742404002081819500b20414810f46c025203400c21240c40707004490000310309010301c01a00d0998880440c0c00185210030500010500800208952407141c50f00c0654900c1207440090580d03680d2100141c0d41086980d101d2094240c0c10f01ca4100d203818580a0220480e1007544034240c040d200003d12103642d107844120310759401c0005181101c1e100c50410f42e4071040e50040994201500078007490042c0c0d00240c100f1200005400350038002c5180c2e0700c0d0400130390050040415400f411040c100090302e0440610310519030b2400030859030390381c1d00501100321000b8104900030624002c9072803004400004590865809072001681c4614072a41103445010340c21004001440010705198031102c1500504d001d07a010b80b80104400e01004900b16419441d444028081154030b445c5118526202c016681d01004000110b864848010501c0c06c0c2c0a40f9040c6201c0c0d075a180500511030018a0301c1140c080c901c059 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 685138192 1250 685136942 685136953
    0x105040e070504020703030e030a05090f0a1211040612230f070e060d020607050f06060405010f0b0c010b0d1a0c12010504150509090d110a020904080708070b04120f02 73
    0x8459041d21a62180219401140c00051640070540700c0d500c5500c0c00101039054075294a440a0014501ea00640b4002c0c410b0a03142020030680c50040c200d08102e0b07054542005142c0490764070101c20f100e426082a5006a5032000010148105468001c8092040d00614902ca5906801e0101701d40201c1d15114103a1124001c240450000a20764054800daa00c0c0409030f541d90200203840c80c0da14a40094000201080d81020410001400005240403000380d90b029501c180c24801150000d02c0750a840082c141c604100000d04e900081040c40751800010609076803003008101c50300502c1404a845504543e550410160500211604003c2c070382e00c078038a00707011602d00019100041c00740e0b52049076241016000d0583d24251100140006040c00020f1314290300b1040d1903000007090314011821030160040801d02c0880c01c8841158018102c2c8015140c54589550715085400e08491100041180c8404140b448040d14851031042000350301110500c00000c01ca0440c00740c0940035236015 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 685139442 1250 685138192 685138211
    0x60b0309060606070606031205030f07031a011125050907020f0304090e03090a18060501050c031222081902010b1f030f0e07030c0b130329091005010504 67
    0x71036956045842110607640302c00240c240781c1c1c018886540014154400048001c403140c1d0004051480f841f141c14801c046c0d1b0341d4080f0700340c00750f80c2c40703400d02c40c3d1001d00c511028683d5030148100c104900403110807034200000b2143c00c941c1c00407a004c422100c5080c07241c0104103e00d0044c111076440b20386031019285041c1c070703c014940e0324041c500400b000540c032900c03604403018040041e030380c00c010010114081141c0d104512410180380a8400c0812810f0440129240d4024402c940c0c925107004000c501e400c844404c400c1e028200903103c04299194041824020b21303511080d150070074003902d400740e1340b064000c582d1120300c1c48262558040d07905020000100340d90f0201c540e200c074840854424101c040c181011001840113942c2d40b052070703140000034039000c0c10014001054a1003491850b00c4141c607860300724150700400f49444600c4407581c6013400022848042c420b8215002d00000742e91071059846c036180ca43c0304407050581c551201403142140046801180d005050a483c10031003c4403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 685140692 1250 685139442 685139461
    0x3071101090e1506070812040c06020a0b0f13050a050d020709050606070303091e0501090b010608013c0b12010e060a170c0a080609060a0b06180406030206160204060b03 74
    0x500404840404410f000d030780f50070f5102d070011121429031000c0c0042e0340b58607514240c02446810b075015160240d80080205005000180e00b001c6c054110082c0002030342d85220a04060a005241d50211107151105d035000800410190400d24840d40181801a240101c000c0ca0b00c4482c4e448903101038148011b103c40d5403a10011140d20582514010494462a003080046840102ca0003c1140b2280c544c0600340813043d132114030743d80d110b105c3e0240b06991754030f0b04840c44e65082c06100d21341603012545100d0522024502509424040303140202400c400c0b080443c604955440180d05000000714290002c04900c1458003408008100000ca42003500218000c0200c0d800741c2120032a0f0300690f40c0345400704114401038060028840e07a01d01d92a070390b0094440c00240c4405255128200204207402264000c8154587c0b0141080b401c001a049640312100b0742c01c4102900169203810210243c1c03916001410703030340c4404240300340305c0c0018818081284d145070322091190006000f4000c013183d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 685141942 1250 685140692 685140719
    0xc010906030b030111030a0c080a090525030f06060503013c0b0a240e010228200a0e01030b01090e030409020d0f0e160e090f010e0307110109 62
    0x1405440c000926401050100c4d00410112082c0c2124080210400c000342d48250800d08203801540c0d940101900c803500f416080d0341030084010711980241c0030301c07040e20b026242400c3c01040d2000b004049240e03281c035102e643c4201040700340d0382292200c42c00d00040c20240501e503c1c0c20441d0710704940742c00840c04c5c0c00500c0d401e02c2ca20071980c00f281c00300c00361460801d5008000c1502006010044030f80e0388022140b102c05007907040400742403040c06c00180b01d50248180382a04d003010b0f0050a442d00d00041004950700011036a1110000380b8840b603804101c3e40900d1002c4e4841042000030040912800c011140c8259032022050740003040041c800181d2404210b03046610419002c60302c050074041440c01d40c09a50004500c140c0301141102a0103884e0700701c050049210f410405c8104511003001d42c56000424071002041c19840c030412616800d204425031006085080e00c0010240ea841982500c1034907070400100d610100b49a014080c1c0c0c510441c1c900300c000d081001c10b141c41c0554614042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 685143192 1250 685141942 685141949
    0x17090d060203190212010510140301090c050d021306080c0a05120405070e0901050103020103060504050106020c19080d080109110405130c02071a03040506071d040e0703050f03041401020c0109 84
    0x195004000b040d400d83c600307a070001c0c0b9010400c0003551a402c01c9000a21405000d03c58903200711940f0103541c210070f00681c0440034183c41111120b20f180c0c2810f0700b50010f0030907510307410101b100401a0034400e6809201810103075503c604000903140c64140000e058038400b4000c40c240c40000c014924030071f0b82000c01c4071001504114240c036039a4417400d00c00c1c01d1040f240d01070105403064800b0800d000f40194840d90680c2d100362000c0044a80b07500c24401150b000340101000340c0c1c800701080c49585825101c0d10003401c400c5681c1d102d02501d890f0320754101620184d942020035200c40c01400400d039180901c0d015507444000140c02c2c607150100040e03003400305008903a003c507910345580b0440d600c20300620000d0a0312200d1558078240100181c0b0b150f07401150295418000e5002280c4004c3c4102c8608800c0111410360301c03190700000d02040004c203609500d0515600c6011000400200c085c40818038030f905442c0a1512186016200407010300300c48807460441d00181c07060035407a81c0200a03202075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 685144442 1250 685143192 685143203
    0x60e091011042c01030302030409050a060f06210f0b1f02150718060c02030c090c0a050f040f0b0c060703060b0d05040302190503041a0f03060907021f0917090d 70
    0x82010710010b8200002003d0a801080c80048008000e141d0000018001c46040724801c110701d580b414003042c12902d681c041d0000f8240980800c00aa910418100b2400b1180c48401d0828036802d60050080350940e5103100421a143c446007000c6107400c101d4404000e5445604001d81844407500031f4407507019100c402d9606a80c000850607061240f0042c4041016481700107010369150700700908410070100307040780f00380300714198404503041880c032443c09042c0400c542d13410200032040544454120580d041000a0107202c0040d51504141c0680d006101d281005070381c45000aa20390b0410800138803c0080c1800c00d4010025985810f0403518607100a0f0030019064a540c0341c22802c080c06007003030507030101181c048241489008801130045a545d10591503201c1c103a0000186c0900429000c040d0032a03051002421a083c170011090380805030f807058589485000d08070441c0001d216290002c401d0b40c66886108115400e800c5014450102c42003608001003140020951040100000c08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 685145692 1250 685144442 685144469
    0x3080412050f0607020a0209010803120a020d0209090f01030b0f090705010e01030b100f020d02010b0a050f01110714030106170c10030e0f03031b09060706020a050d060e09101104 78
    0x40c41018400b4201c924001c4055030b0403410030110003946d800311a4007c3e03205802450000440120010803100201d40e229040c4203030703075100b003e9000250003142e1003002c030580800003214103a95910742e2a102c0c500ea01103490b495410b6040894030414001d0030038400381500e0b414880a09400100001116002d01c4e220800d0607810004030040c020112821303810004410503a0385c640c0c2c014511442030791442d42210a250036011040f800c3e20030041c070300d80e00040e08000038000360a101c0d00c60843d000301810085002c4824010051078292541d1003403800c041e42400034801c0d8036080c0a010010008031043c0541c1e0204005001d44680f40040860f20807400310541007801d6020b0340020260800580644401001c441000ca840c1d5200f104e0030724010700c4509040719484520003c0e115500405088581894125a1000000e40c002200780b005d12206208200d810390383d0b401600040c0843c001751103490f0810f8041146408030200e010341100e8202a01821104a160151400c0300e00b90120081d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 685146942 1250 685145692 685145729
    0xa051803071b03121e05160f0f1a01080c0108100501110f030a020c010207240513090501032301050c090618041508060f040c090f18061a0604030804 65
    0x41c1c503401d1a0344001c203201300c1c0e01402c020b02e6420079080c418401d160812851850702c10702d02201d951190202c0e42d0f5440042044a01c0401c056001e90014103100740c00c5d00050f0a615151480110000c0350115043c0c8462401481812004c0c444070040882c2030800c500b00e420010340c40f80c0000064021981006490f02841d00013070400c0210f0443c45c541d03030701540e03134441920300f009441d00d00701c2c1c90460140c41240800540003160460000020401035107080c1c40104000e0111110743c0811145c00c50034441c1e0001103900b40081c41494025440303020048000d910366949a40820070301c2070701e05000d925100411070203000c0c40040b584031190843e00540e0390100e4005c0220340048000149802c1440c2608003c00403454440540680d05208106c5229669080314905a17840032a001030400300428000c01039100103810048201c1c00d510000b0440388078044004070380220b440070540340b41e602c0d00000012030b401c1080401c40c1d2402510b000e0b00d00f505548614503117200c1d0f4070031024908187d82e0040d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 685148192 1250 685146942 685146983
    0x804060c031b0303380405090304031403040512030324040621060e0d051804091505010f08070f03080a03111201030203281b050a0603050a05180307 65
    0x592a6800d00c0e4403031441410b0301c1c02c005008140028000300c04405440fa2410380c0c510001103900c4104262984d051050101c1c414040a003902901c0d40c2d0756444244000702c001112a403050071101d1074000115180c6103000204440150000e5201d0b909420070018000700c4109601d80c241c180e0420198003800111a60200b001024a940101c908041c008211100303c0c0c503001c44038150341e000700300c14412002c0c0310b03011640700d04c2e1b07400612012420400401884018100185003005002000024500106d441d0814507182c029180f1940c0b5541d080144016003690000a0181805100070101039040818034081000140006400500e000c074a00030340600c01e400140105001c8030449842c0c2060071244121900c085c0402c0348203000d400c44528089001c1140903903508440c0c610700c141d054040d151984001008249001d2011402c00c006c04c040c3c507030003152801001c00e03981c00a4a490901140c40032540090607442440000424580401c4800010b5809042d040f42600d9105403030414207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 685149442 1250 685148192 685148207
    0x1506021e070b1c0e01142a0313030f030b01050412080c03160605060301020702090f0403020106150c0302011505061b010b040f020316080105030d0e03011d1e01090804060c03 76
    0x4851076600000c1d8008000710316915620025401d99414000f010945105609075003c03501042d0010807800c0003d60780b001c0b1f420b111010b030000752849120b003102e000002070a951044a00d58001c50003548181c1c00c0540c480080c0b07101c070360180313420050f1700c2803500020030720b08c22441001c260050f601102024030070254100d500e840850070840b5916502d20703a004540e28101b40701602c1191900c00080d181b805d041c0201c580080d8014100074460755074415003e0171102c050001d0301103650710400801c1c80c40d190220305900d0282611803082050442c075009094801c62007240d09008900c480801c0f0030344510040e40c6814a5901c174141d89000d180f0003050041051080141d482802c0044a04140c6420f07401140a9600c0e03c401c09841402035005a520300002e00c94160103912000d001600c5a1140b000c000704101c0080000c0b8403106400040d0300040c4020045040d9a0000500c054141890008010203000c4810003800092013a4940310703800d0145105140074005140668420544280c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 685150692 1250 685149442 685149449
    0xf02091008100e010602190302010f090b060a0b0c0307080a11032a0604170c100e06071e0e090c04030204050412110c03060a0c050c0f010207061506021e07 68
    0x100314054110600080c4000002d48110b00c0c0840380b20b10104610b4070321200c2505a4800b0340040405150300d01f19080d003c12a2003055086540e1002d070641c0b903110368022102607600860b44181203041c0310701005400c403095031140850107410083c03040c842c0700100991b40038039042040d076500d4148051080e52509005041e000d01c50000080440c840040c124241d070403541d221403034810307901c00c58121f183d032142d090380c01030013228404005a00e0a8940401003030814004070a85465250003180c50083d600490103461154101401308000158000001c880d0a003000310111450710381d582000d04002000d01300b00b40510078030800103d944c046881120000d41e4003802c10881c80c039041c1810114140c02e41c10500c001041114250310b01d040000e2000c0c6400001000741600791944002c00c801000607126010070b200040c07040c80356102062000c610201e80b000009a600c50107071410b081210781508101d140300c0548501804119400284421482c03d0201214442c0c580100141c3c0b0340134042d030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 685151942 1250 685150692 685150699
    0x2120130061812260402220b0a060215101a0c0705090702030909181513081c060902070f0303020307110f0106140307031101080a0b040501030b1f050f040f0209 70
    0x5203c80306290710042d00c140e8540000401502402611820700260b1010345020398032800e4480e0341c8183c8030007000b181841300b075201000600c034020301d00803507010615540080b015800c4181039006a4412009640d84902030a502451241c01c040203001c00c2003914405903421900820305200700d10702009100080e210041c44a44685084440256a58070104005000308804000b25007500d02c0c00030140070085c100400740c1409590113000082682000305980038000449800e0b80104400000522194000b00200c141000c1e40c0400740060b502d40380d2111030451300c10800000406c0b54045c1020940381e051030056a030781c40d940002c4583c500044007820081c0103884c4054100340e01540f101d02142d0a42c680350201c04e002d02c0c10507458003110311020300030b15103100114010750f12600e041c80d0300c140001d00000740d42800e600401e04954003600102c07038030042002881a12001c580c0c46041c447c0070907500103529820640880c400020074000c070307401151560b500207800ca41c207405031a103005018 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 685153192 1250 685151942 685151963
    0xa0309050111030412020f0c13060e04050102041a07080f161502090f010503160c1e030e2d01181a0d0c050a1707050d021201300618 58
    0x191412260f03500c1038a04864070424441041c0d01140085071410035505041c0141807040903040a010a80d031120150311700c0c04d5a210000b25250b0b1481000c580070798059000107131198280060a038510303c40300d1154100520a00414002428580444104800d00c11400d91603100420b1441000c400307003540240442c014111110b290303480307680a0503a02004694884021864000564035032105580c8918849001d00b403403188030340180300c080c10707040c82082e48140106102044002e03201c0311240c100c001a1803012081030a142513210151a0544100d8400c07001d00165910780d0040c2e00e0180e000c3c14041e0350303600f00f1400350b409072404000706560249c0c2c103c4007110350741e421034941c040c0d40742003501031074210a000c80d5032244003030721030902c284e48030b012515400b030100c40c2080307000901000400400b000201c80381704440c0003800303002806200b181d41c19410240440b035130200306031031b01d444007541480c1c11620060010742e070b5100e0707a000350700000c50146100c07940d01074080b000c4000d403025114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 685154442 1250 685153192 685153211
    0x221040312052a0f0705060f06010f05041d15100201050604180519080d0c0309020f01030c140c0a050307050312160c03050c0705031b040609020307080403050a03090501 74
    0x4002103000418201008000580d19101a040b40f102c0340b0300c2c1410350078903000c21880b10612100042c04d854403600704842c1094103550381c00d0700d046011200c52041104200030f2100650704403010040440e56800c1c881c0c18030303045c003101d141400c0030503845200b40003030500424181089aa103003402c1c0e0002610003000d40782c1d4850041d01914054864a0107030f4a80031071201c0d010110001c0c80405036104001c0c3c0b20010880fa070002030444989420703101000c08000c0c0c4250304c0014810050024801c1d20b011403c50700307070f00400000e124144d00d100c0c1071608100c540c03900c007644848401d42c40b143e50303044541c480078103862240c913126842c00c000f0000d1000040410a100300000500140450580d810b91507a40d190f4003c0c03440f6041426480110b032101c0d40600009010b90082c1c010469a201114621540c07400080c2c9481c0850000d80d4a00b841c14001d035981d03042c1030003801d002d814901c0c019403560800110050035032100400c094208140407520300c1030309102f90071003011907400c40020301c2461803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 685155692 1250 685154442 685154447
    0x706150503030f12010e1b03041b030b0406050604090c17100606050c0d23090607050a2105070b01050d0206130f060f020c030a1104060b1614160902210403 68
    0x100d001130f02110301c0103000045250040a0700c1d0301c80c110000c07082003041546c151421031504040c2040380c801003c5202c1c210303d83d8101ca8440c0080d40252429003044c246400c104048910140c02c03180503a00340000000810f20a448003421207010200f10b0300d03099a5030711000d041c4561840442c41540c01c3c039200254aa5001c0e000d00034084c1a02c081e2090307000400ba068980310315944aa1011920400d24841c0c4051144007134007000d24064411881c0045680d00c85051221905044400001480e0032107111110841003808403980d81c01c11610f09100d50b00c0b807101601d014030071720740320b400c01c07012080454035840e0075030710002031030010349010580b2252440d0164409000d40c45c001011010b201c000d0038400070380c0700300c44007016021f0100c009007a1141d4006044044945070015151382d4001500c035117010003450a1040b0b41140c222005840c5001d01054010143d044900e50065004909c505806552941158945180166034003400e8400c9416076600b558200ba020580344200000d164 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 685156942 1250 685155692 685155697
    0xc0706090503030402011413092d0c090f0b04031203090b09010507080a02030c0d0e1e0a110307080d080601180806060108160c02060d0b0a0b0c060f06060706150503030f 74
    0x181700b40c03034107a035084a6a03400704440c000c0c02d401028405451004002c00c400319405030419880101080c200c101442c52880070110380040f01ea0302460340c8400e2128035560009140e4040d00043c01c411003503620b041c590090a0255000103020900c02c0740341d0500140c000c1d403105203019400f0900c40907525000c2200390082c0003c07201c100100b00d01d100000e1000a00b4402c0320301c101c25682909052000040003d00101898018003d140c0324212a188680103a6844c0c510502c990030000c11300c0c021146004401030040008031800b940c031144091259280104a084041d1518546481c55554000040780d90034440d00b0380d8600709180582c08501c5410200740c1d80e1061070280c90b0728486450f040b00f001880031000c0300c008009414a00c120740145840b5000b402203030031f52100401d2a0004500080075044a50302c101d40c40301c0b0003c5c442d45288402d111160b0b20000060b50110540b51260200360b951050340e0004000e02d5036024502e44004103443c1032409801d0180481b0b40712a51800d40082c1039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 685158192 1250 685156942 685156951
    0x90613090f210507110a030611310b07060b0d08041d1017120c010905100504050601050609131b0e090402061204170703050403140a0201170c070609050303 68
    0x3070940d11406410b20b15064101d42c000a40d07165860040d03c1c0d01c0311032590000e400119446030010038000701045060190445082e440a030315030741d80e08159000000b180955000c3e03010f1070280f500c4541c520820908a004a800f9104942e40e50702c02031410900501660701103e43c0000707404410018894203038040d02c156401c40e0f801038840c4910300d200760141c403c01c03525802d550505a0050089400044040c6001c10006080350401790400b4041000c503041000c50b00303416907542042c0320520008228188d4003081006041010341015101d1a0704c07100305015040c0201030014800c1d0140d2611841981c00000080d03007040b4220040030012103403208154820000b4202d038a020000e8501102000d019a500a004915011007501036000e0050020403d03a1042440041c032a42d440c0c024005101252007980c441d5074031401c510b81000c90411034601c0004039800311802c0740041c3d030000142c64145007c482c80700501d540b1100901030911810b100144980d08100c044001c1100c00030155008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 685159442 1250 685158192 685158203
    0x110a06091a06040e0c120c06070b0f0f07120b150c0601140315060d020a26060709060806010e06090d0609020f061204060b040b091e0703060b0702090613090f 69
    0xb0780300c1d102000191400c08205aa264021900c2d00340b09103098030540803000807130300c151400740744000009031040c1c01c20780091700e0703894000c010400c80320b42d40124650f103c20700000c8071070207090a4800510501c52172443c44455640c440c10401d440e580c50900c455402400c0b021203954028500703055803600c40c2849010041e01d041e04c03890209240c0410312545200410320880c100f03070340390310400c1000d00704040c3c141c0c2c1103505900042400f0004140007148e900f0b2101514143d4401140c078946001001816102088040a03091204650103241140c0200742464085040e25800c800214244559910700303600c80c44070090b20b41040b90b940c01000b80f40d4001c503030b05449001180c05201180c481d1014004461000390000740010304c00ea8811441030401030400949018a070000c50003000701a1940807410813281c0c4412102400800d8541d804896480c1c03d000d00c51a11190b245103001e4071100034410003002000800f035441d002e82c509540c441000d030030712202c40b103810040c08120b20000251907 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 685160692 1250 685159442 685159493
    0xf14011205031905091f050f0306280303080f04030f200322120b180c060706020318070510050c031201060c1a06091302180f060406140d03110a0609 65
    0xe565803c2c9601d8161046c640e1141854a20511400e2803560310050202c0c1d80841c82e24038580d0182509240c1d454000c04091190010a0540c20041d00303040e00101a00b1002000e0020440060703407158140d8801081424820154203161140b00000500800300c90032b9848007003102c101c090800748820000c007514643c002c07101c80d101c0c3c5090240d0480c0700c40281c206060345000c9600100c4d4280340b403550044000945407070b03a030803c0c0011101e510030700040d50718540110038800305c1010039074003c80e1071218070010480c1901e40008100110204a2105d05020000c90b07000300b081810700032140511a0982c0002c0150b03110314016290f507070700704c00070b885174849201c000c0c00c881c0a41d04818013610000300319000d03903501d5811540d95503003165000ca0300b241c00c00703408540f03c4040da40407a003d0666a246411030745801d10a0204407042644411a1011410010480c0391500100b001c0250b03050314000c256444403005603490039038501401420949809044424040a000b04040c080c0000c45120b0303 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 685161942 1250 685160692 685160719
    0x1060905060c0c011103040e0a05010e13020a150203070c08150c0f0d0c0e03010c03050a3213020603041b0e04110f0a17100f1401120503190509 63
    0x115006105841c040c65020484021040d8001d2600c1060074041740c00f00c03443d161300d8501d441001c01d42030300c146002c0b0352a00010710034103003018121a07008404155008003018640c0014506640910869104103031001c1190140c6100340100c801c41a000501400305695039030035180d490744c4254907103049080d04d0010800c0e80400c0012944000000ca00e503d082041299401008008d0041a8001d01048421802d030a88086c012001405030a440c006041e2620310001001e403941403014070ba469a500e2400ca81c001c0c620a9a50070703410441d41141c2c0700d50f9803902c6a503ca0348400c0000395102a0200c200020002458a075129070000f12202081c00740da2451200c43c40c000585000300619545001000c19040c0a078201142c0760000700080c51f125a20003184060759084020a540c5800c03503440390225090303a00079000c00c2d102c007034805c220254902510051840c0d040c000c2c01015000301c0310200900000f00199440c46e05000c12500070f603074013098003a009c1d80c042560140110703d030319410b5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 685163192 1250 685161942 685161949
    0x30e121603050111130312021615030b09011a0304020609030708340b0d0b0402180f090609010302091003150c0e010804080f0c07030507030506010e0a02130b0306030c10020601060905 80
    0x118550017091300302102c85821541c40520007178441c440306003184075406101019160408060008040785950ba05094113038010040c251410121b031280103903449001003100c541c0b27001c061007014a002c0d05645e00c940341c0344002007544c49122403180c0e05200301c00001c15040008200403007c3c4444110207445400b05000f04c1d03200350032400b080041c08aa221040007041721030b10042001551101d40095003400e9003000900b00d030030000100035110700000c1307144c0081c14903010b03d0b12042c008a8140e00d45c0d103042d90004408220501009000d0300103800070400d0300e41a924032a0145034041c0e401c00024454942100040141070034000025210300d0b8280030b55405028664000d07030b003040b02c480c94016990044d4141d544a44070ac07030310a1184000010214609100b0000a076201d800030f407a0552400824161282014001120540c8100b1400d443c01e41c400d241c540c01c559034119450386030303590000041c0c20b000d00070100c65004515260503029040d40440c11905840c501e40320390300040d44500c00d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 685164442 1250 685163192 685163197
    0x5070506040c061e0210020d021201030305090102010c050f031b0d0204091a0103050405060406021605030c060114090108030a0311040b16050f0f1506220605101704030e121603050111 80
    0x1e079015801940c500c0072031007883c1d0008d20726202505400340c0fa080c1d00c07200042c0e04103070982c010b03000101d012600c04915031342030061500d400150302c2c0550402c544c2c0c0404503020f11002d00350f01090745601810504150120b4103590700b40c08200411921242e440c40c030200a0b04080c0c00c03228402071100c40300c0314658064842c060150b0f07040700089c5007641c0c40c1d945d410000c0d4040034031030403032420400d0488001f40003080103100c000800f074064810b5525002350040341484201180c1d210360b15940050141550020554440700c24034580420f00345c1051003805003500c1127400c150012800040ca11100c00070b4414840186031240c421103001c4440d10407110385851008081d1000303500213500002002107810011504035000034041c0f000745005192111144840003900780f60203490b0b5608100707514041019030003030007040c14491540e5032541c81003560f085005000906000e8a0b0720860b165032181154954100068011551200c50014040c0b02031240d0f0701c402c4a881d030800310040d14143d4607505 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 685165692 1250 685164442 685164497
    0x80c0901030b0a200f070b0a0c0503191e0c270306050606040504090318060c0b04140703170408060c0403020913030c0f0b0906060102010501180c05070506040c06 71
    0x40780b0b0390350348030701c4030b020090710002c0c503c4c001c00b484c80c0c0300041074801103600510304036150841c11651a034140c9441042c40c20001c1c07402481c0c5180c2220040700c0c6800c08100d07a03221105480e124004078040d02e866000304001e10380c400f01c001210503140c1c0329919540c400d02c0300d403e9684481005032440d4442c07000ea9400815880c0510017201410070014800f500300a4002d07000802c2282010348a002180440350451801d0f0001960000b014a6000d61401c1850103013019141034111212180c035098400da0014000030b06108481d01c85100c451002d018101c0915030207283d06200d00c0a103402c100d030542050140407032500411000c240014203a8040710210396002c2c203103504558410800202c2c61055400c280c0c14407a40c0340b40c050018102c0041411001d20883d00525030707041004100385444802000603055a05d4080140680e401c084031207005880c0c008800301700540242030490301030248900003041485203000344003c024054048400751180355480c6101689901044503040d842040c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 685166942 1250 685165692 685165703
    0x624170601051c020c0a030c1a0408090d1a0106050a020c010305100e09070b13090c111005090a080c0f06061509040c0e0d050d080a20161209080c090103 67
    0x410f58415002c640d00d43d8800072000710303005091540c82c13000c250800118800441c0060341846c002810405540c11096402c800c54202040c24617069a070042c051003091800340c03060107050b0f010700c100200c1b590540e0150740d03007070031030031803941e450601529503004440001c015000300b07800722003594400d1013585d1181c441c4039100050580b625110794540c10001e80400840d003e506000314007007001718010401d0b045040c1209401074a041003d10898180095181c108403000b036074181041c9000991060414401000003041c7e22140415071803e0031550b0010303d58140880c98900400022405000682c40b15050311742960f40c1c0d20030040100301e1140c5000b00e101c0140300b241c049080ca540321021711942c504003500f00604442c00680c0c0c0c00344102c000c4030390b0362080b407011081c00d41c0900000d40004a000b001c0c013020706a4103010129a81d50003001d00d00e01d00200b0381d030300004da9400200c445580c200e001602c01d050140002031a158160003440301038410112000c0040c01c1403070140341203030b402c00f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 685168192 1250 685166942 685166947
    0x11d06040302090a021b0a020a05040614120c030a05061008060915070203070c1509061103090f0d020909070e0f0103030503150109090c050909090307080913062417060105 75
    0x15420030074420800340c540c0c40314981c01c2c0001c04d0b10409a6505580400300c6d40018a0600840e10401040b07a40b40d4004d5400f4a0400d00b0411000d15040114500d00f0411a480052245a000d0f05440d20f0b42140303451f941449480940001d110000c42c2d0140105800c0c4134043c26580c84080080e034510040d40e840782d0a0723016074843c0c401c0d580c12003200c640242aa02c11340e85044615141c0c1e244c0040c803504264402001010b0141403140c200e03809000a14050805240284403450140c0e180d000b42ea800034000c0846661030342e55941d07603c0305800110350080c4440340a05064010641d1f48115004040003c0400310119401d4080c8000d841e0480e0b038169916840d5943da14070603403035a145440c1d514140140740102140000550060380d0601300341e50b88440c2c403800b1010400011100140c40350000390010440d413008107040c00103c1d90300d03550a4a1401c45002e003403d20300c004146a5020300e00801c080c1d0150105900740804109249003140d0315481851910b8440140082044d9140d80c08074004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 685169442 1250 685168192 685168199
    0x90b011d130302150414012a03021804060b03010806090312011a1605011a0a08150403051b151501080103021201060b13050a0602030a0225080a060902011d0604 70
    0x3210116501c442c801c0c4103850942d006071001030072540301564100c030554010900c541103c90244030366a40700d0001d90745951a660700310030f4003c200340b0b1100c84804150b0009551401d1081501d5400c1c110200a0300c2041415a5005084c050b074000f8090403456014000124010902c00005d940201d02354030704107012a40f07032038030081c0048a42500c4c4c40000c5024000e04400a0f2060030107481c40b40910004075040740030364070b140c1d010414411440c5c8904000754050066040004000c44000b6003070004800b0340d103503407d0607521390140001c0c40034201104031389402d80200216108000245440c40c00105407a42040e8510340b00d94030000500141455004201615000e07400500711581c2400004840d61902c0094a80d03501162135042d640085900c200241c1c18201000c40050103d44080c6080c81c4c00e081c402900e0307024800f102c00520858003408001010100c0229005140c20b404a80c80c0158038a82680905003203881640410701c881ca038030388003008244c1c4910248400805080c030b040d04 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 685170692 1250 685169442 685169461
    0x602040e09032107091815080313091d031b0d0e0303030a09080d090f0b0604052202010e0a0603141015050f0705121309021c020a180603090b011d 64
    0xc020244d00803c00c483d9000624104003031580400c8080f000c0d80800c10440d01d2034034280a0803c1e41c0030103200e034002c205c040e0b1462446030484003519030f00c0310007049440d2a2402d140c080306568032181c61a010000c5c2d03001d1020f03c5500c5040203107010506855603450fa1800030b40d00300a68444c2180c154204000054641c0110360083e84854407419240342010104d165170740c11038103d16000c862048146911a050240403c18207900c1001250180f10f6845c002038240b4000140080841c50810649200000c582c00340c1d91050040001030314035810140ea4400c002d000d0803044502c0801083c114010079410584603010105854401c01e1540e00342d9070107801102d05901604040a040d4814000c00e4000f03074045c80030103c003032502c0c40d00e1610740000d440ca49121034500e501c9178100ca403040290440e810030000b080340c003403500006e00589400c1e505005640b0808064000405281c0907980801d071641c041d803100318010302414101000707a8940041a150b01202801903200f0040341c00001c98030032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 685171942 1250 685170692 685170757
    0x3060c0a0831030306032306010e041a0c1e09010e04140c070602090904080a170103050a0809030a05100510090608030f091201050915060907091502010605030a0602040e0903 76
    0x5101c4d10b00022aa81c0d00d0700c540d405000740d00a281044e1480d60146028081c1c108040d40c050f1103100443c030300906140d034031841000c0100c294a0f44003054400003e540b9402c1030255140580039514045040150b144001350340d0380708000315800b048090601600d1400c062003821811070030305020084940b00c0c40c04004054120040483c0c1d810b40030469501207489010f4058040c0e84034505180d1508420341d00580240500e4403c1041e007040c1d82c0041020980004020401e29040803225980d5088000443d051402070303603000e0107521801c42e07568030300c43d0b00380e10281c0300749807110303020040382e0311192151300380c0b4058811400142d005011041c01540380c1c60040c0342ca81c0008140d110304815808102e42074810445003035059401844100110341d504240f05a0b1140088900c40e105251101d0080c140301618000d004010040a4031001014001d5000802800c0700601300c90301d95036946400c101031350007802254840c401351800320740c0ea0352001060b41c21400d00c6251b40c15108120702c44804482e07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 685173192 1250 685171942 685172041
    0x6110d090e13061b03051b0d0209012604030f0201020403050318030c100f090f0e0a0b012601051e0622051e030d110d1101090203060c0a08 61
    0xa04502e040440015910300c40c0400c1440c070880d40e514038000401c00502141d9000b4000d50152009400c82c0440e500e0380c20071210380540c2c006006071121010030040b588000050300c0790400802c00e201030800c024809448030b01c614481d0340c0e00e403000c800f070203412030030b0380960312004105078410300c100c000000c8000008815400c0290480c0d02c0219480000b07007440740030f40324000118249800001c1410340c00000500948030310391850030140d24044081e40c9180005200d4001107940b00301080f09a0300c254182241040c0001c020800419021415140c1080038407900e1b01c81e030708190061030307004244140c200f203228008000c00c1c1003541e808048070130a644032600e503061403851880403990340c1c0d174042540d242106101d103072620708544005161410884459010a004810440b01d47c0301da00051020b5032101140341c030f230054141101a06000d40100c010003136041c0603001c1040041000c18025010760380450b03440000079210640e07680b00090302c0401c0520041c03c5168124080ba200040700c041c00e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 685174442 1250 685173192 685173211
    0xa05010c021507031706040b09010506070f080a0f020f06130b10150305070f020a020a09090507030b0705070c14011403180115050f03031204140f031306110d090e 71
    0x2c41540488001142d02a4001300c01182035004400c01c250b0120600c268485ca040d142009004504400156603040502c5007a03c82c1c400020740d030381081400c12a030706540d58018411a180c07102c146c0b019255070800c000752030062007140103d200c0150001900c46c000c01000d4840100700c0090b407150324060500400c845038052550f440002c1d02d81c4400001c10720300c0c005990008190600740e800504401d80d8018110445d0b10401440c00035a807442140012620b50100c00a4902c106180c040d0801c80c940d40003601c1d042c1030b0004c009100d5040002460380c82e1085001c119a55114190848000d8802020303a00145030b6a1411020049080c01560030200b21012807040786142207445096824130014030b0302c04c03040b480d001c0090b800c080e290700c490381904a010b9810b0803c09101c2502a000003000a409603440e850514413282080c1f1000c2d440e8003841d0103032642e5062480c0000a440100d116040c00990101100300d000039000c120080403e0700c40d514100c245240807010318000380c024109044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 685175692 1250 685174442 685174459
    0x10501030e0a05101b020f0c09090a02091e0619440706210c050405030316051b0d0323040306200703020a0f0611121503010b0a05010c02 60
    0x11560400a522800c115801c001c6618038601c5480701703da14154141800707640c8961109228200081201e0800781030503210700078159240c0300d0b903514100039040c0c040d420425800c107000010390b07109640c40318400740c44400151900d4440603c02c2c0d114403070260015811b810b242c20310042a01d90081d02245200a0b6002540400d0103800003411428a10710103030100d11102e0b5060603402440003a00030101d6041ca9176030007014a000007411072160f00007800207503541c41c5401c095030040f002d0320040c00029003103030b4861081403142c00c052102040c1c1034601d8070440c0b03941180d24070310b00707400820060050040e07048044980e505403030b091080b040100300484038184e2002840c3d80307080a08021401039134042080e5580035500301008000840040d120f02c010050500441c0d000034058401607031100700345e1955402e50408800030305000c15142811100000e1b0380380e444100c08c2059011703a002500744000c0780c55203010103080300d403031041ca20741000c3c40c500c0c200a1580030319060342205002130b28190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 685176942 1250 685175692 685175713
    0xf080f04031202161b1d0604570305041103060c090f1206010303051c0219030c03090c09180803070915020c0303070602030a09120306080c0117010501030e 68
    0x2c240d0300070361250003131004070502d01000d000f04e141c030101c06014820310300d907002e60030019000c00301c03500d100d41c1840c03403202d03440428060f0329aa44440c1e06c1c1030340c4001400c124200000c440700e81d0329450745400c0800c9042e841c82c0c4d60300e610f60498903099072030b402d005185c207401444061b07000e424000c1066428104203000504c050b201400706030b2040802c40c08141d5259141c81c20003450703402c5000c95901078020804807192610002901c0e6041d01c1c3c01d41001900c40080302a089000880030a030040542e00225080790081c078440400c80c0c0c1c000e42501c081c02100f140070021421200b450502900300c203c0c800b400c02810300da0b688000b1600c2840c202c800c0c8007c90603103c041003a070007601c183d0006081443c041100403001d624908030345446101503c1c0d0b445065001942e20300824001400b10f50740040440e4040125a000c00525a0700400c80000c2d41b8181c80060020200c0d882101c0040c007032108540e6903903110302801e1603c0210701080d000079034246401100103128040e21200c1905c943c000c2359 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 685178192 1250 685176942 685176977
    0xd110928111e0a03060b070b0103060e0a060c05040f0b090f060c0a02030303010b04080706050c03030f13021f1d0a0b0c03250302070905060d030f1e0305010e070f080f0403 75
    0x2e00c4440c11001c8070350380e0341030582801002ca5040e503028040c0001d00348088000a038000201c141141d07000310303001c0b032100380310050142000040d400007440c880c03900000013081500100584210b603501800740400c5560341042d4000d900c41d01d44443e0b40300d410010003000504d0580040e00000450a04541e40e050055010a2455000b138121729010071004c0303403c00c40d80c1010044070703000d010245411424003428603000d0b642c0f404060610455080c1003000509400fa104860380490394008044484d1294411141e8402900d003407003030303000600c00c031100009403000c0b01d6510502e0a0040e1003d0f00300743c40c020045955402c000696461404108140007100403089414040180300d841400c507111020320f806450703c01c3c2503000814541c203141c2000300b996500c082103031016805080803001c01050600440b90051205201110b00706000c0c001502c0d9507241d800390381600c1c0c2070040d50780750380c0380c94806840c4103c85045800028180e0b60004a5020910a403103402034880c0c1043c2c0404910341805 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 685179442 1250 685178192 685178227
    0x1006150c050709110d0c030e030f0913111b0601062012030106020f0f0d1e140a18050306090303180109021e0f01090b0306060c0c0d11092811 62
    0x314444c1c510110315244149014801c12440303068a04040100f09002141180c60340101c0c030110144403004940d04120b40c80f041e400c0e441010302d8400404c880c0314030342000c10745074201d1100070000c10440c4407414007400c00021210705844d0652985921440101c4000d040c2c003101c0c0b04400e03424091140c40740f00e43c4c010f1402440c040d1189801800c101d00d0716410403481d0014101c41e07001c81c3d501c80b8140059498004242200c0c5c1006110441d00f10032500506580303c00c4c5000c2d80c00110040050080e00d0682c0c840c0040310059100c01614901d06d03503850406544074800d0f100101d25400800100e048006510120409010510004202041d041d0000744044840a00402ca15440c81300031403010700d001c9148411360407007401d000d02c400341000300400182c0002031050340606030000d04c201c00002c003081501e100e0340005003112040485803500740a40d500600307250740903074100d4001c100402803228580b03000301c41e0365251000c03242050401c2009412282140d0102d1a802c00491601118282c003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 685180692 1250 685179442 685179461
    0x150b0903012c0f15010b0c0c090a0e07082a0312040603090c050118030b19110406080f0403020d0c0f020d06050609010501050f0d2a080601021006150c050709 69
    0x6900c080c100c001c030b003420110841107a060070340068039104028414050b2403410340d8071103500161140444501c0c03505d0100ca1100d06030340100d41e4000c2105080950700b02c00c0414540c5800e40b41825030f1900a44e60343e29000103580c00d00e64155048a4410720742890701d61442030000e0840d545848200c800c0b540aa02c9a00158006529041120144418142c2d002d00810081c48d0555407148140300044032008180070003004240b400002c2845100c0c0581041c407407014041040020f200b401c001001180d000d0f20840c80852180400a0310910003040303920300c40d5804d50090413100912001c01c4502c00d22001049825400c844d6081d80903842d40e18003040c01501c40c01e00003445050180820071f00400580c0028108181009074081240301c4200381e528142c0001ca011507443c08000800a2038110021111603403555446c0c40418241e01101da54001e0790b081c0c007a81c1d9450191400c0c030701950b07000e0207100985a41441d680d40361a00c00c12010080f180207000388e4110315110082c10050301c04691 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 685181942 1250 685180692 685180751
    0xf0405060f1e040b0909060406090501020906040f0906090902010801090504021c03030207200d0825080d0c03110f07031e180b0309070b03040303090209040b0a050604150b090301 78
    0x1055043c2014800c080b88803e080b12100c0c624a041c02140e55038044c000c100600d8252540f44106c20000c094054400e104801440035031510303104d00c1c2c40324100c2c110344610700c0c000d4244440018421224450426225010b9460002030703801e11a080028010240c01245c10050a4a03103002e80c500c1d4041e0070881d9071180d640941c1e46c51680c01c00d00c840060000c0e042c01d614241d4a035002b159590310000c0740b009a0702044960f00c900c40700703280302110078041c03200341c2e0031111510160f020085918000e08241110900c20001103000800450454445141c22056442c0030804448001da001000d0881c0510074a0454403485031042500314074170000715050302061050108491601c1d440c0fa42d030000d40301e42c51031982589040303240d40360346001c944281000300c64004081414144260041d0a10326005451040107080519241215140441c1d90f0f06200b40b9050129240e403503d8062002100311500e40c3c5d450342807e000c1850003583c408a5200d90640d03894001c4560030507400a030824404108 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 685183192 1250 685181942 685181989
    0x1808010603081803010c2c0a060314070804230a0606150212070203070e100b03070503160e090105040c090302120105010819031e0c05011802011b020f0405060f 70
    0x40f51030740018040048850f1003a4140a0003030300003540300000620391701182403002c091541e0240c0100d000641d028205420400000c004100e081d00f5030401001e1300c500c0544265241d40313860044440000c142c074002c042d25110402080c5900d4600030b030038903400c0c03800c069400051256031000c0440703030940e0040031510250b8850300030094040c8410300381b2401c80f20185180130059030021b500e94070baa01640660b0300b045070102d0210078402464501502e03441c14115924102002c014269410842d0400c0c941401c0c540122000742c412901c1c4486541c01808111450b42400c04100c06001000c5440041103c80c030000809640c6900742001c10141c036130000a925418003441904250020000540c1200da004811002a9120451100302d00303404030201d0382720b0942842203030040306028000d0040d600707111038a444280714031b8a0b043d40a1003600c40700704030303204032564828042000304069070001001502c0421401d15411803540800700903d034001040007400000c205100113041c0b20384500c0c28 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 685184442 1250 685183192 685183207
    0xd02070c0e160e0109031a09150406020414060702241603122d0f09020a080c0f0a080706180e07170906153f070902160201180801060308 60
    0x10083d1262050002c1c40d003c1c11030342c00d40c2c481ca06801d6100a0440b800b9000c5000240204020720001e00e015803803049408042c2414202440070f504640901c3d002c95a0200031003640746481c4080351440c2d83d024141c04c8400c1704040c481d0b02c4c02d004c42080a14040c00400442038408201a50061550310a80300c08011203004107403034080f0740440d0aa03000203056030005507441036107161340c041e030360180c1c00011960070400048803028000c0c0d0040203410404c030310401304001c100070038001405c3c00b00340c5103041500d200104011902c900340c8a150302c04e4014400c18400b503132140b0031201540103003a0400c094647d443c41ca8150030403003100c80b50001021004002d910803880003803180c10038803000c000c0400d4245920340c134075030a01e810001c500c5400030301452040040042540c40000c181c0780258080d1000c1052802890216076254901d00c0c020450049041c2c1524801d8900003400400844c0501c179450f030043d10465242c0014500b0710110b5000092081024000c4901035842498500e80b510503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 685185692 1250 685184442 685184447
    0x90108070f0c05030a090e0a0506211207080d0f05040201080105040b01093303020f16060905010507091706091c02102d0b011d0a0e091b0d03050d02070c0e16 69
    0x40c00c40d230704041c02c050900000f80c2e241d61302c60003441044284481c524100c81e4180d0f103025401040c10b0080c0c08045034003000e004820014120441c03000c2c0c4d09010402003145941c0803601c01312030080c0419800300c014011410160300144000798107040140025448a032903507c1c95003542c0f9412303440d11656003103500c1041903021000303c031401401c06504002070052182000d00843d203010a8001c8514080390610225070850720344107412800030046810503080040068516010304005a15400d401c1025100c001039040e1080200101070800c40004807100c005821030751001c2c0c4210300c280c0030203000311921440f65071640301c02183e580f2140442211181420704054401404043c60000000038070f981100a1080d00c00c01107003864010741d52200014000d07119074105204001c600c41c10062011000250607145094908014209244080820002d0003901c800200021020700415282a00f13640240400c24410781030300d52a0364540319140180e6a040b103000075124442c80c0c00c07880094 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 685186942 1250 685185692 685185719
    0x15090f0711030a080703051b0c2a0307030609080714010615030203011d060a090c0203040509101a03070c120507140f12070c0302040204060809070506090108070f0c05030a09 76
    0x11451005141480e0310301c60080e184c4040281490241502c42c0b000525032000f0380884c0f40710041d000307a0507884904107441555a107180e00348013686003c0a00804080c1030004100d07440f503c200031f0051000701e06550307410000e8051000d0413102c80d88107001c40c05c0000c40d000d0100d110080c02c0c00000a04a00c0c1c026600c0f40324000312414403d25204000501038880c0e242048900008032104014007a1100070224942e892240d200c54101e902d050800e090595011004100b250b60440e800c03044e5407100e1007451001c1c100c62154110701ca014200060421620790081d50340b140a80c2810940c0b2041234990003094010052180001400000e12104100803a0760410311803075094001c2c019480b9040343d4540c0d42103005104286180042080010020000c118401455002c0c02c19500c840d40c030311000d8007420060314103e2650144070b401184904241044d200021f9050b0340300c9155841e405807e566640450043c1e500b0011400200d4010610800c01803108030b44a940c0c50703d44a281102e42d00d03008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 685188192 1250 685186942 685186967
    0x30506011706040504242004080a030807110312090105090c0306010b0702060705030412150b09070c06091a10081b10120501181815020315090f07 64
    0xd03203080039a8612048510303255200c04143d4001400c0e84541c00c112640e06c881307601c041c215069001c20a4180c1425410844030004103160040e01e6001d0001e00408500480c040c0203810750164000c64040382c401d08025400810504140e09440700c1281d1417411940810081601040b00c6030501c0100700e030900c41c02d41e00c00c80d2940506080030382071b000a03407900d5040c4200c03a070091022a11209654800c4201ca41a942c05422a66510740e203090720a4106917175030303050b0f404140c865070740032034114540195000110018041607031590741e0602078031100205142a00c070156a850340100042c035126080256514030103070740c074591400407609403450080790402800c581000044040a64030b02d0000b403410001281c1c000e1110155460481301400c00310310f02c1c005641080000145400c1105062600125880061000c031010140c00500aa000400100038031231004003c00780b02450760145030001c9001c0b19018011003140300040105030140d50584880c0c00d41401d101951f0f4001009041c02e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 685189442 1250 685188192 685188197
    0x302060403090e04171b010510030308010b0703080a20070c03021c0222020c06010e0103120e0108152412060901051f09050619080f01051005180d050d03050601 70
    0x6503e440c2d941c049028461841c14a103420b00462108201c138612034400c54203130074046c02045146841040c201460f51580b0003030700400c3c42c440020840345000302c03c030350040b901521514119202c0c00b4102000741400e0320303104003440c089801c0b0300760b8090740001404d0081c06221000302807030031030040040715a0300604264071034118200000c01070712520b41711800004942c1c80c900c2c68054448160010744103200d4000001d0240600101c0c2552210651a0503240147c441141e10545150150f551207581d412050205030b042c00001d81010340781c88052807062000e0004c69482d0312400140082044c050107202d10001c0100d40054141c086451982e40081c040380c141034a9490507011075049540004d171041c40d1281204180304145c010303203d81000381400f52180360f603920f44200c28410040208902c00c0042c035000003040c2c1c03030b400b04104030307040c1d501c000d16020324580c0000c0140c509034000101c41d0600240f45446a400f0383d03524410200c250301a00180410f401d528000078110f503002080b0506 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 685190692 1250 685189442 685189469
    0xf0c02030a0903061505040207050a050d03020a080c09010314130312181403041a0304050c04050405060a15050402040b120a0603030c0f03020a24061403030706110c0109030206040309 80
    0x9080b503100100c03a089981015002880c242480000141000160040f03500700f4000504a020800c001424040c118003070801e4400720300040310101c090b48a911068400201200082104042000018140800d050400142104141c4a003107030416048070703c00800e01e0403000b502c0c00d1541050341e4030610003560200f0000309103024440c0542ca0100350020b802004034841280c8650002c00840f00034203041d140d030480c2000341080040d01988101d60454070381c0543e8520260f03504050082c6c60103254010090040703503403140008001880340c190603446817040c81c0700028082c2c640d840103202410007604625070350280c0710104d85480c5000307008006100c0c60700d0010804a6032060103251060340c0818485209001410100d180c80342a09020300221000c12600c1c0c1d400c5038007070340b04a982d090102d080c0502507039248800685810601001c2d0950410042c00d4001000ea41c03001c080038449120050404001082003403c450980504601683c001c9090200b819004402d1500038100100c60301d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 685191942 1250 685190692 685190707
    0x415031d011527090320011a0405060a060503151c140f0a02040209042714030a020a2604030c030501271716210f05030103200d060f0c0203 61
    0x5140f0f0410501503410790b644a00c01000c151040710200600401c4508061500c007052032254003c0a04680c19180c020700c2078410207060906008540c45044010f00c1040c0d0f030f61074180c080d0391942c0020304841d107074111030401440d66a102000a200c0305880004400c20071401d10b041c08012641445990180c0e1001403c0060442c000074140e00d6a0b60507200540c0307030a07890000c00c01a001d107099039922910034440c0ba600b10310402d55400c4c250b82c01440c06150403001c1d5981c1c01d480b0310442da00d00c40143c00c2541c0308800f091052001840072840342d1848840c21302d01d13002c1c44003580c000703030811621144180c600b081484400d00a01c1c081030329042e00350b02e409549203010110340910417001800310783e420425100d0103142c00280d803010501000c1f00c0c8003241c3c0501d4047d00300c1010011030404442940d003008031240c0b10b00904413202d0103d172210341c40c42c1d0841e280c00388103800c1c2d101d4a071600c40b206008040300d43c841d410010f880501c03400e00441d44562044800042d00c6804401c4000c640c02480b404 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 685193192 1250 685191942 685191989
    0x3030f0c120c1c090315050a0c0306290c0307080c01201902070e01090c09140d0807060603120c050f0a05034501180b0415031d0115 58
    0x342d1111243d8078181c0c5a00318401050b180d481036a4006094002101500901040359401c40780c400e03400c43c00c0c1045407104024041e000c50701d05003e409250149400c00500a00c400e91440808030000c0c213400d800c0002d8428030500d55400031104558010300402c1c6d41030072030350900820325030741d503050070481071035601d0f0500c2d2180780a03040c0044061800d4020001c2d00303178000d125090282016060b80d00c001c0d81c480c40c8000142104500243c00a00c030100000b400d00102c0d00c000c9600b02c00108545071002c03d07911080681d41050310700341c0d003c0d03540303260000c00140c2d0300700940440441c0e0340340e903a030202003414030328281515170031980060b4100703c4a100000b034000c01150b52081d000c59580c80718078a000360900841d1100c00e80405802c028a150f02c5182c074422540690b450380c00d03179074031440000035030301c3d1900d8010500c219000340d00309000612801c03440d203240b070ba500046442c00140103000d403443c1600ca41c0241210f060350703035034800e090f4007641242003c080103080c110741c80111109049000c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 685194442 1250 685193192 685193203
    0x2105130206030601110f0606190807330c060b0111060a0e071a0c0c3c062205060f070f0305070f080903010612050d0e040b03030f0c120c 60
    0x744a041c0000000c3c2c0182c0c020f819250400209000f1107108103204001c01d40d8403602502c00320310400041c100d0400f4000b6001e5900c0540d10300030080c205103481c000b00c800e140c4c1151141c038044603046d14074030258000581c071140e0304010250f035102503c0e1141e0501c2001c88a044280b641080f400e0900542046800101c0756007100c0f0103000000c108560385401070402d52590800d0341080d9116a540030340f01100700c085c001c1c5c80c011070103807049040389404001c0c2e0764420f49004074a400e441048114017034266160400845204d01406c04070401010004817981e12802c8200c0c1040901501c4c2e8070781e00c02e8001c941000d0081620302901d0101040344640742c03070146610003080340c1c0c810b0102404051003801a0750341164068004030110080d442c00001e26044641864000e40ca0b080000440c0340c0c0c1c1d62a04c10341d03240c210000e003085455600e0102e5040c042010340c0f036001601c81101042d903440800080031130b000480e101c15101d4a01044190501300000030280c149801070200200801021a1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 685195692 1250 685194442 685194481
    0x20415141b010b1315050901081005040302010b0604120b0109110702213406050714010e1b01321c0501030b040b1b030601030e07050604062105 63
    0x81c003206044a884980e07001d0502c00e607031103420400c015207804211005401c203007044058007424075401500ca0b024000d0b00310b03091051000d02d43c81004110280303026940019081030181c40045142c10800011503015070195003c0e45a47d0060201070b801c1c001200c13000c40c09045000e0007800310741c0752801305885600032113402038403490a1642c403080803c4041c0d06008068840d8055505134034282054151603013803900511841480302c200001038034105e80300e810a82e00c182d02c4850074400d85072221008000098000c140c0ca65035148914032800b000c20040e01440d44801e6a484001d0350080010000e8403040031540b0404410107030808901403094200004002856030a500d40340300010b2003071422503032104550034524010020003480078003070400c0d102e240a5001e010b07041e114501c000401c0f581100040100722406d10100302558400e0304080300c0b03007034044200c692540c0c4a400151881d403107a0b02030408106843d6444031502c641d4400240d034010414401c0049142034407000c0e0b102c59003030340c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 685196942 1250 685195692 685195717
    0xf0501030c020114190603150914120d0203040204150315060806010311011b0b0103080909060306060d030e030c04050108010609060f080d0e1201140a240e07050f030a02041514 77
    0x608040700f26520346c0950b004640028065039002088001d20000740960341003a01c07800e641401e2030007001c1c1d0000e140752148510700152842c05c00c10380032100083d00060700c226400344d00c42401071482c5000c415800c0295014094030625000b12580c14800c84d070341030380000d1040e0000c00040002c40e80740548444402000c2c00d1502c4050061002a51a204e01071001001c0c459071000100503c150038018020404c0141d6640005890307100400d50b9a000032150707903500a41030440000024071800800c044607030090200c5240240000020701a214240c01800c1d20342c0d5100e004010609060049100405c0340d4045224890b05143c00329440320402003c030014440e84140703170550b80d105e03852001d00006c00e0400800511020b000428000390007510503445140c10300c0d441000491040900c10300b244110440d1000041c0f92940031004030000070304080078480c2c18043c01c805088542d00940c85420030b80784c0141e9860074098400d164603c80d0000804005640b400451142d52100803610940002e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 685198192 1250 685196942 685196971
    0x9030c02121612020103050604090b0a09080904110d111c1512030e0a0f0821070501020a090e0a05010620070902040b04030b06120307021005070203070f0501030c020114 74
    0x500160b00c1c00070341c01010b03200c0010b25000011441200f03201004030520036a0244032640350704003040107444207090003906204c51000400d02d248406d80c03040319490b01c2035290500300310350500042d08940c0c00d803840d151507010005510f00c00740c08034829850614808032003d82000c00101d00e00031400381070103290804079a640d42c481340b5030700e0f502c0307540005018041e0070fa0111003491400a100240085003140141d040d080081580c1a110300e0290980350148014101600324134524a0710700c448040003404008104140008a0420700041100403810303107074038409070301d1700c400c0710b0000000030052494507250400500c40983d1014040101107802e81c1048083c05000b5030b03950800c8916400a801c4520010f000a201841080500308807401003600c292030740e0b2100248103508000f0220440c2617001041150b0040c90004042c003000550b03450074908080c1c05502280c070b0308805800c500d29107940c1c002d04001c1c66901d03018016100220748020311401440306440250b040d0003410039041c26500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 685199442 1250 685198192 685198219
    0x3031b03021c18032303042a03081e07020d06060503061501020703032a21020c061204030912030c1205090109060e010215010902030703060e09060606030a1803110c0409030c02 77
    0x1104090410f501d19842d000d5890510f89060031240d03480718103078807210f2040448d849411004a002c40c04498008031010301e458000225148820b090440c02c115000050060501589900c0a0f40920901c101400108a800d09041500d400402040030302010204a4250b015076400304040c002c90354141011801098071850f44a09074485046410341c501c055802e41c011f01c01c00010020314190880e00e820040340010b5030403070320703199a0011240c019104011090004c1801030049078494042e15000011544070128241e005041000a5001070700b90b04c3c5510900200e0030400030a0075407820214544103a07000040e002c50000d101e200184100b11225072481d034000d00003500d01550840d02c990305580c40f10765900080d0415580180000c0c82e04001186840c42a180d440c0900703521401011551f0310001005600c1c1e000800c40f0200a49490501c1c81400c04010b00c90013261080d02c1c0c100c891900c540c21240760100f411740491243e800c15400401098001c41540031080d01614245480b90a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 685200692 1250 685199442 685199477
    0x70f0b0d0902010e1002010518030f030c0a0212070b040507050604140405280603140f150a020d05010e0f0a060b070201030f15080a17030f060d03031b03021c1803 71
    0x4e4601d184d400496110b403a142055040d44458864810004c0d0014850410150390342c0e64001c3d82e281090a10301040490a00801003025100800d0b4610403036028019100126003150440c010480d80259008180401c106042c040c0c5d03009000d0540c2d030981000d141509000741c0e5031622424034055581c40d40864010300a1400c6111500f00041805040c04d0b0143d1003a8010300d42840180c80c1d01c80f804030501c84200001c12018808540c4e032004004140e480b1040d5514148081c0906c000340303508214408500c041070060307a0003040700e800e50080f980340c6081d00d007034141d500604080c0b1151900390288201c0340c0071810b481a9580a280004210800810910007080b4811500402d003240310b400081700e890000304d007803001d8811183c0083d0802c52140c000fa05000648811001100001c000b640e00d003021201d0101c0c190084c500816941e00d440d003020743c051010803c0c0d000080c4c0018030411003100c403050f07210150043c8001080110842a01041c81c80c80004006041114524240d04042e9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 685201942 1250 685200692 685200707
    0xb06040b041d100c0f0810030204060b0406030b10050f1b010906061802071101320903071a04050609061e031008150402060d060801020d0e070f0b0d090201 68
    0x980141c42088014080040c100a661030841c40441c03620075503100c5002100d2038011a050540b142d16210002140c4403002c0e19400c00061648020000004000000d80c6d40c50280c100203000412002c2d40c2c03a410701c3c000405940400040a000f8808c14420300421640401107074071280002100716200d600f50725145000700407554200e10190b08040e00c036000c4c014a42d0080c000c49400118401880890b4041c2c00143d00901030098205030f6041c41a0f04594000c202080c2c1013000020781000c010b160107441c01070000700006441c9400310100f5008e2890904025810262828805501d025444079060902500c01d80c09414001e260201c2d16a1494654009851203090700c00b00c1c2c2480c0b03600244519909030401c840200900703a14200c0003d81c800042000b5000d1010041d076070905650700d4081c458650320510302c20a04564401d400140c842c4c082c80509501c22403188040b8030500a52540d519017411030b01700c03405403040c0360400c0011401140c1140d2000356000720220700d890260006850301c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 685203192 1250 685201942 685201961
    0x3050d05040b15010c23100213090b1504060813050303090a0b100f17070512030a1709100c051b0616080f04060b0301060b1b1b13091704080d14160b0604 67
    0x207500219107488808941281270040c0c40b200002042201c4803002002023001d1840319161242c0c00400050040c9c911404802d5840710b4500c2a23007024001d5642d405145070702c1107410340c3c660f8200c103036048100300d0042c40c81e64000c40503550b103949071814a560040070003124407071546102a00ca5818407158410700c12280249030080580910090302400540c496128410120000b83c490307404226040014254034040d034000300c0201410850f03008144000c040300030045041c040c00740300c12014004c0043c1d0059911000c2e1000d0107603824084802e080380a02041c1e42410b100101d0300b000000740c401510301c1e5000d9008913010238200894000320340100820f8001c0c41101500043c0780c040400d0741c88414400300005000c88880a107020003807080303140e091700c2640c0d20040d124803504100e152a045000c80502404009092154000c01c40d811a486076105020982100034520482078111000000d400351100a02c1d25180003540060405080e09400a0158142c0400725400d9103881e4080180d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 685204442 1250 685203192 685203223
    0x4051c0204020a090e0109230a0b1e040509013e040e070f03090209271504050d021f240807050f01230703050d05040b15010c23 56
    0x20364209110003000c0c011507008180c5080d0114000103410b5106108080035001c10312307001d81c5048450b00c0c249044a4024044505281e02c820301562150b079a15013014203090b16810000501326070009210035110000d100c441c842e45080c0c80c040a0805c01e80214400050b600302072905a2071501d0490610440701e0345c1101c0078000444c021130b00e0004a5640c50080c062034030b03902e14003081e10300d044047d2082104000e4004101e5000303e00c40016030347c0310b00c00c1d60080010b2100c1541c8036101c1c40d4035000d20200c80d883c00b5120794050005112003401201888078551010b130030030f000384072074a90900100a200c0c1c8106680d03400a401100d00041150403000e075841c5081d020155604d410583e228000e009591156620000348409036014408161914200c0c1621440c5298445140c0c0d1454000c5107081e02030117030401560030940040c0c400d1034032484c4680c1902605007440d6000345080100d1a903030038140040d1800c0301c1c012510410b1006110140103088448500c48030790024106025100001c3c035 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 685205692 1250 685204442 685204447
    0xa18151d07050c011503020a081f050612060408040906080742090e0703020a0c020f0a0e1305011b0806090604111204140a210c1401050709091104051c020402 69
    0x182c0b0002c4081002c21a1f0003280c8058900382c43e206190f1715101c4040c04101c0d8801b40c040e1745652035282d600032650003c4d00410b0441d001c40c400039041c3c04c01e8800c450460b65034100103401d20540d0090310850005d0700c62100145082400c0c05003450559500f880004410302c0b41000a284c07904614040e64010583d15407601c2d4480c800c064050101d8580303014003030190282900140c0fa03140319100703890301c83c18681d840302142c8402d6000c1c050028a291849034100d941c2d1640425001c10007140b00b80a4000014030340f104c4030711818014211810103084d4529910300c6111150010303441541c554018800300c03008181e503107a40700020000d0154080d80d101548000c50310300d1401d1015009203202c0c81c01a254070f490301e8078401c2c82075100ca510150040818803030207500c1c500b4980b203044c242e48060040c02c091103070400301c2c0c881000c140d1080c00000c030310341c0d124001c0180c036a03400a1210b0046c0f280450070b00580710b804443c11513038001e5000d446e001e4080d01d080d2014444601d0070051300c09070007131f200310b6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 685206942 1250 685205692 685205711
    0x402160605070305070e030d11120f03041709010e1306150c02011d0d150608030721080f0109090f29010803030403080c0307030b0a18151d07050c01 65
    0x1405000102c61078404a407811001a8113940240080c42503074034001c0203401013080104040c0d68101c00c520b182080c0348151321014403c1000b410060420120805415440b03103060b1400845400c821040e601449505006015092b6040110b2203240303074017200ca14120441c1410580000d012583c412028085041000d0304610380000342e800c00503001b80c3c0c6240000307044c00a2401c0000c10848559084203510302d891012881b01328401d15020f0042303001041440d900c026051640d00926425a0700600c0501154155003543c1050641400c2d107081c50101403070910b03203000c0010030503c1400c20844d15050171004101d0524100b14140d44c1c485075810300484c6004041844000400042d0b002d0312001d400071074003120000c00e6900c41c40c1d150751a2001a51903000140c07042d0006824403040c5511000e0500d40d9a40c1d019045000c1c00792902a0340e161041c252901080d18500354031003510111b000c0b030500982614240402d15000340b1100c90f456034480d4082160b00b4800d21038054510b5180038400d2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 685208192 1250 685206942 685206953
    0x19060b0405012606041805060705311809020306182109060702010306030b0702060906071119030e060c01020c1014061203040b0c061b0403021e040216 66
    0x40c01511000c0c0c0e03402c2441c1214029046095000880101c500006107001503d94640750700320f24485003034075040042414007a0f03652450404141e4905001c40d0b008100015078142447c0030310a25004118600f0607906508252130341c8160500403108181d03002d100304118001d19800c00800d903a401b800b1038402d443c0183e0710f510103c901c0c60600089e07002d991039400401c2810039001e0340c0b80d07008040d06403400c0c0300d4004020990740310850881c181a111f07040040400c00c00311115114aaa0b41c000d000300b85403031140d807403d00100800300c0013806400c2c18602d00407017000940310a20b401604001640c40c550b0b040660301115041840fa038844400150b00d6010350064001d80050344110084841c0c00001d00003040649001a0301d00c5501c0651030005a518541414003540c0b94401ca4180e9141945491040544c1d6004480e0f54003e50304c10000d0100c951102c1980a0b803042c071001c3e17803d040c142564002890504240d18400b6440e10200406506aa0f254100e41125068a840e05405074841c03070403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 685209442 1250 685208192 685208197
    0xa0c0b071e08060f06030403120b0f06070f0614090c130b0a0602030406030e01050f0c1b012c0a170f090a060309121806030f090b0108010b0907110d0819060b 69
    0xc450181100381c0c0c2135001402e1001c1924000d03a495140e449840c9600e14280700204031740c0200541c0070100e001d01f00c00301d8480000404115006041d00f03007580c1d00c0c40c2810700943c3c444070700c01e444c419202c0d0f00f0440c03405008500c00e081047d00b1078080c04074140e452403075006040c2c0c003031010354419554030002403080d0300080180200c603215181401114900c1c107c65080342e00c100e80302500a1000c100044800d88013000030300c03801c10b22402c0747c000044141046400c40f0304404204140144545542c08032140c4800840305c081e03c00340092101d11010350b1034001041c01c072035240c000081d01080d18508170041005a5815180184c9412005c1e55038200017406841000d5068880d060f1100200b00f62030710400d55070300703100350803143c81c480b080c80c100c0110018205000a441d10035640c808000004001d404058003c10310000085000a991001c00135582340240070741e0280303c48403e1905844101161307104020f0050b0411020741e540c1d211000c002000c0f840039040034103140000204801898501 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 685210692 1250 685209442 685209451
    0x905070207031205160320120306040b040b1528030504030e0607030e12012705070b160605060a091b090503010b03060a050a090b01030308010315020a0c0b071e08 71
    0x21050300714403d0750000d548600c207842d09030b003185030101e04c0c3c0c0380802d010704806618950546000c8240a092150480c100320b0903448074003042c01c00200307100a501d4140509148100308850070482c7c01400400284813610919000721041300200b81d10742d030006003000d0f030420081c00d0341851030402c035a070310010000c03c070485003200400e80d07500705c0300103174189441070311017440c2e05459640705140d94204000b14a030300750305c80410664907644001a900d40d02040c954a83c035002144400b0000a45812400c4c100c1940100b14401024031510403c8112040e0024a40d60800800075a80e220240070a04009158010178403050814040380b0000c6104480900c80c0006a41c0b03032406d0989610070907084c0d0b40c0080380160b065110340007241e50a452648503030b406c0040c00e0340014644106590b0455040003da00541c0402e855000410902110103d01c1c4041408010114075050940d10302800c2c89039505001391022003480300154034203010b50003510644401e1031010f940b0304006900240085d00449 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 685211942 1250 685210692 685210703
    0x50a020603070f120603050a020112060f0605071401050f010b030c091e030c0a1505181005041802040b070305030402010c060e010902130e120d1e051806010f1e090507020703 76
    0x4003e03c6204c5031086130192035011002c0e050302d060a0f00111440e041d800314001c0e1180e0b8440d000592203011801500040000d074594a803608043d00f807800b4101c60364035160b10303640d0402d020001d241300714290181c10746040d04039080d107036115010f4250030f40c041d0984464201c4c1e60030380481c8542441c0c112155800c0022022520500f5500d030a100c103140f514440c0501b0b000742c030368001e403040d4000c90143c1018550412002110b80c442800940c8401d840311f08800407641c0000d06000da5800d0746031a031b000b811501020b5107044c0c0b9040d54405148140d00c8003030b04010010010404580c410900084901d030030400900000c02403900c280c2c001e181d078043c200d220320007010045601587c1070140300121081d20001d40940310701c0c114203400990040041c0e8045d581c0c1c1c2c410003101450f82e2182500c3e000400d080000300c51508605c010f10900b04119550340540c4a10010403c400381c061001c000e9484100c040b01802c5051444070200300080c0e08403840545c1013208003c0e12680c0081d000d411240030f85c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 685213192 1250 685211942 685211957
    0x5060405070c02060f071113050420061b0313080606030f0f0721051506120a0f03030b0604090603050c0f060307090302060f040801051303022104050409050a020603070f 74
    0x294060740c40340e0042c54000c0d0401d80a0105814010f070304000f078080580030301070030540011000c002940c46008003503580c050554460030f0105000c808540b01e410310101d01583e542c0120032a0004400e40101402c3da14400c060042c4003d411744280140c4548503e18119040003d40f100e1080c3e480b0f60341103e880d070203840740c40c0c9984406400014812040b04044000e081c90504000078040c01c801540c6000b2004203840c0c11500004004204400741503000604c0155141003c0f410082001d8954003400c1a0b0ba0004003510007003020030400640041d414100042c03650390741001f065540c05103611a0700100e00d8214004180f090102c1e0a140804046030b01454201451007000800d0105880740400035045100520050500b00010a40c4204400005091542c0c5180c05425217000316007141120204400d504101501081815100e22440862403004001041030007558003c0c0d00c0f403a03114540340d0940009001c001d1141e10807164000d40800e98034a0006006400e8540f0b170070240000070600d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 685214442 1250 685213192 685213201
    0x11517041212150512070e040812011409070f1b0503031006110a0809030a020a06021b2713020904120815090106030b12010c02160807150c080408030d05060405 70
    0x9910411090b411502c1d030065143d4204424000c50200d000c031301c61518400c114002c00c0d0003080d020040d03c114031850348190340301031140d2000070003101171f40710780b50100002d90340011560b12190305c142d002d810340c5442d81c05a0721022040391100700d10f030807150114010301341710070038088040001d5108800c411000c060056030b0700c00880302140c581d21b5100c403903005051804005401400208101300d0000c04a81605016400040040c4101e600c0240941e02c101490601003014a4684080030340c100c4140501e81c810005044851041e44581400d4101d1f410000c2e40070380302c05207007401854020307014a901c1e25152a01035000010b170002c10000c19105400a2070025140c2c55844070b28401805044503640fa01c6400c0d00986034903400144d00600a031802080c0700400d02c03400c0c0c0208543d034014001400d480b08209001c080980000c820b0381c01c140c0c400e000002c0700300d107c0c208000d80f602e041c100380c41407820440d400e030240740c0154481d800000340d002c41010321504224080c4504a9041045848 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 685215692 1250 685214442 685214477
    0x9032015060a1202011202070b01150206070c030531170601080f1c1e0201020405040f02032406120108011b0203070b01050105030907050301020f0c15040b0115170412 73
    0xd980c03103000068410403c00350015481580c51481500421001500300002c650762074401744000d0700004942d1080d00301c1883d95942c100160750f080992820803100f88002d546001f40f407807086003200f0341d8001e18081c15440344241c000080300e01e13000e06c2c03a146424030f444510086d4902103214202d9058464803002040314000441c5107040052590300511700059074030080130204200c04811810b00000314a44950392282c2001c0150790321607940016615810482040f08941680114040c0f2600c180100080481016400340103804c41c1c80881c4031503a0110000f4409220380003c012041c001d002c000100f45205410510f000800100a84214186450103d030780c1e020b008809408035201100400c42940580001e42e00b004418007521041a20741300800d003641d018004e81020010006204e00c4119414010b21030001c21810005523b03041c20740b10903034021018004d44220a800404d10a00e1502030440d9810100207050010458a8242050200e0840d480c0042e008546ea407030803a150040c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 685216942 1250 685215692 685215709
    0x5010c05030907061404170c0108010b250f0f060c02060601052a160602150622020f25020901090c1b0f06021c110f0306040903201506 59
    0x440c2030003041000d2600c0411a411180e0000c5410664030070032002c00d440d15004022191f03036185600a0500031504400102080300503845080103000c2484100143d2100310b5a0003040c0c54220f80c02c921070407070342c101f040d0a540a854000d00134500d00a0800c20030900c1d4019119080142d000c0d00c01990ba0034005507800d120b2007401c0755400c82c42e0034844c0700c45041c0700c02608511844000f20b0303500103903010702c10180d07010b0754110030f015038450182c2c014480c1e0381003500fa500074001d640f404e01c14185d100002902c00b449544c0c4119094000c10201003c1c03ca2209840c10042c0302d400c500c00544000d841c480d1442408542603000300c0d10040040744076540c50090348416240f41d0b680507401d0300d100c070f01380034100a0000100e86114680c0801c0c000301d49540045c0c08004084891b515030342020ba041314088401d0510700c0d064801052246003d10003500064946c042c40641d03022582a21a150440318185d004030301003040c11044007240f5515800140590042c1540340f450f40141c0c6842e0200706400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 685218192 1250 685216942 685216951
    0x160e090c030402042c030c01150e19180c05123c03030a0b1309121d03010f15050f0f0409080c010e0307111c0204110903031605010c0503 60
    0x180e41000070074010705080e030000140c00a5120340212540301109010260845407181d2070090380041641c8030203175001c0c4a0800d00c8034000c85880300c62480c0038000c6008150040108041601071070150101c0b89503600080c40e040440108482c040720280742c0401140c40b0381c06420f00480f4039245821541500140e07a05080508180e06200400340b100e00c020658800e000612000f545038030b5807482c0e402f041000c4c0d0f00689441d600400c901a114043c003a01d00440401c2d0b070591801c000f503140105800821000040f40186030018a501c0c032142962951190103104980542c030701040340750400702a0b0f04c0194014000c280b880c2801e0764490810500c540c0025000764002031221039a0091300e481d50103124918400c2d0b020b01d040400d642180c41c2150740002440d041e5800004024007009441c0c1d0101100c1d5104448600070700c076400d40606800141c401c0f000740035a6445800c584003880507000d568407541e0040c202d036a6081d040c8600f80050010031400c440c55800d003500082d909001e41e081c0c9105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 685219442 1250 685218192 685218211
    0x1060804200121050405060903190806061b07030b010b04060519030e07030c06080f010e0a42050a0605120403090339060f0c0515160e09 60
    0x140c444001c0314036104003149202906000040b035800f2480800d81034069890b1000e1100000c4603c4d144c100b09091840007400750703820360000c001042d40d9105500d0400b86140b1240703070200880d030740c0d41d000c5940740c400c0e41030a11664090011020181b240014200c0a980c4140c078400d0303603a43e0b95285c5c0c401e9070180340200c03004070343c0c1400349000103081584880c403010158a000f207103059030744111070304040154009894050361208144039044d00181c10b13680045407980400095858443c3c0c0d0824100041c3c0301701c08030b80e1039044544200304107140c86458a1403e0070b50b0070412850410714007205a000940c560801c0c080940025907151030581c440823525680c440ca03290103a0400e0700324441070000c1c411800c2c0f080c071500200208026400000e02c503106004c00c92440e5038807644100d00000b0361054014a0800b0007020b0000b00ea00c41048160440e150404140fa032101c0c0c42d0080c1031030308c64012150b850700c4c62810002007a40340d007502c103104915911411002c030354401c10702c60025000c0b41c00c40d20 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 685220692 1250 685219442 685219463
    0x60c011d1b01030f06030210020f010c020c1c0507030b010807050f061602060c190609060e010c120c110a0303090c0602060f04080a050c16140a120308090708010f0603030801060804 79
    0x260b9400390304500020414008000b078080d4480d80001d07040140c51a10000682c044d289603a500ca40034401c890640c40c2c2c6000600d4103601d400000340c10004d01c07150060348900805103810403c642041044040c42c2d1000c0c1c100e0003036071101940c81d5680c3d000e1180070711901301d0741c6030071100e03080850448610400d0000d001c100807686400340005940800007a4240b4031440301401504101030360047c0500740b00d1040440d941c50a4200b41081c1c0340c1d41c0c0c420010b136907d000c5001143e140c1002c03101c28840394040c8045007010004900340c4107000342416842d07030360240e142008101685540400c11040c4504400401d164407500304036074900b8111900120501c8000200340829040c3c0d0150030001510720740146050780d5109254107101401e56200550114503e080c80140040030424014880175528003a0302c81c030b0f00142000c50000f220000e41403081080c0800c0341803c05000c2c01d0b0250000380c009000104061840c1c1c002048140f00640c00202e9080011074068402c800c0b05000f141c10054012 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 685221942 1250 685220692 685220743
    0x4050c0409030c0c2418170a0c03080901141305090601120504080304030f020607022e15090b120307150e0f0723030c041a180906010b0f0324060c011d 66
    0x3841d02e4100360140600c50904007132300203500050048059031007100401d844590580c005401050389200c04041c2d00000c1c040c52151300c00007141501220000c07508880552195001610440b00d6112040c0c1c1d024281020403060040c07000086000e00d120f0350b40c0300964014440300702d80b84c18040c1c41a4005030424900d80d600003002201010044d01d614225403d2011211074290403074060149201d824218440200094031240c0728540d64900155520303050b110100c03400c0c0c0e80324804d280c00145000f42c85041200179186039031045c000c5a41c010308480b03100c0c5640b00e41a694032264840c40d0b00521608404001c3c1c2c0c5a03004400c0c61092000d802040340c2100f050800c0081c12007050040440003c0b0714801c10310307940318104200311401110f0900000d08211000d0742c1010b4050b0001e4514010802140c144042000c04407540100810811205003038086669070f4090841420b040c2e2044000c6203000d40d501c0c0651081c42c08602e64212050b031749a124803520b07200c40c4455022105807020f1040607 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 685223192 1250 685221942 685221959
    0x207110402040609031104150611072405030c040509090604060e07120206030901111309180305041e0909110f03070b0a0e040f020d0b1804050c0409030c0c2418 70
    0x1c603107030a1b000b040890007404110f051908034600368481800039004140b0910311100038003100c00501100300554514030301c0e03584800c101103688007a18017003000010026020034208002c1d5005007000804114003424141420341e034500342581d05507a07241c40d100b154040444000381e103808071281d450300740460401035001c001c0c480e0001054030303d542d501c0340440c030b203140c9506004240303080414580e66060b41c00c01105004a4030583c180410310784030f466070728000c2a00401520304a4004030141524405641500128001c940e40040240c81c1040300c2402040034280120300d100b0001e89030700d503402484000301955031500b80306d40c501c0a042080ac5204152003178410f805000c1000d00b01040d1400d000540c5000c991140389401e0f504c5564500c20405031901411a9960074004444c05a207801c01c0c0d143c035a00d440006204500c00d0799140806000c15000e01004c500094200390716007141699084420410886100c003040a0040311380242c4107903014940c41d2b800c81016100d0440c0c1c00e802e24006 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 685224442 1250 685223192 685223213
    0x108030721050702091029070809130f06090c170712380303070c06081e0a0606080612100b0a0803030c090307060c020319061e020711040204060903 65
    0x7002c0160800000c005a100c0c0070740280103071514140a034110b80b800c00c905007138024804082626211002111803900340c4441510f034201d402c602d9156481403d200014120000c00101c03079034040c02d02614a80710340450b072010044401c180d001388000440c0041c11150503415031041015211200c2c082030a4500c150308401d4610540c0380f0024001e009104004944000ca000d901c1c2d4481401001303040c1c0c401210141521a00290000d50a007a680da40f01044809507000d002e00300180c103070009110392424076031000315003580e440701e4600d0305051070481c02810081c00b07000081000300000c1000c071304008a100d0b040440d1800500754280700a02240090b1950810440d07011440040c0030031080000e10045008480130b403c90340c8d4445101007810b041c00d419600640074440b2819031480581c5011900540011340b044c018503410f02549410001007151120704180e01107440c01181c000c0d04180e00819071240181c2c03034001c0d510050800c1005a120758024039002441001c0100000b4800864 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 685225692 1250 685224442 685224503
    0x603020d1109090a1d0709050907060311121e0103050102130b040b0d09020f040e030301080f0c0109061b05030412020103060f150503090109020d11120d090521060901021201080307 79
    0x4000c0103038410040c0715241006d9a001000e401d586c0c1c00506c41c00e204200118030082209080c04d010725641d0716018070b5180144d010302e0030008903241c000382440120580000141d030b40322804c0c2c0910f50f104d00b0306074000d420440a200401c075201102289000052080c1c404917030300516072a2030280c5034185c2102500d42c2600c226045400300c6d14003003035a950341c020407500c000e409000b035499624080c005880d01d2a20034492046421035240101d459900401380c105482190416007c0d00d081140000b02030014840c01800900000c0b4000c544100340080601026000f40d8061104a403a11000c092543c8148038039101685444032400206014101035548208030100026048001c2e13004580706007001401140c82c406103544850940c50041110119083c144005041c0c0d00e0700c10201500008150141500c80c141152048003140418588200035800080941d869400c15024290103900100d4607001a10100c400104020000000740c0b111250081c07031751202c2d0b0311081d6240004804280 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 685226942 1250 685225692 685225721
    0xc02010905010603030806030624010e03190302100c110d030c17090706030f05060d03031a130e01050c120c030a090f030c12090515220603020d1109090a 67
    0x12011004281c080c401c000007580030740c0300c5401c2850b0060805050107002400c000c01131a89078621040340700d012840403da44001e0801d07aa4002e40c2800180c500070180b09404103a864083d500b0303040590200d0044101c0303034004001d101d6041e000313a0907610703903d083d2000b21950340040500b40120b80b094100883e14180c5041100b00a806410181700390102201d04090a034000e0200308101641445849061240c0341c80810190404500080310400390200180826840d8800d17000300745451000301c0290100104000d0120001c8102e50010f03143c80d960242c050752916000442101c42c58003141c070b5071074814031000081d40d160350306002980c0001d0000742c05541c0d580064030000e0260202950198000d8407901d01c45101c40c0b42103a900c0759101007171000c1140e182020400c9480301c48010220241108015803110700b9040241406003011071926107003001a10b001500c0b03a01580107140d400d00c2c2100900030743d0180303101c00c1c010748105081e454005140200054900917184d102290203442003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 685228192 1250 685226942 685226951
    0x1406070204092d03080f1905040201110a0c14180115180b09031002090d0b09161e05030d050d05090c1e090105030d050403020603150d08091002060115030c0201 70
    0x3c491880c007542034030039000429007641008042c5030300224556409119100403241500d080759503000383c491104c10340c00c19680c82300042421680980c000c0300c50081011700f100d080000b0303414042c18050080c49200c03461000d000d4001d82c0c034100346900c50356070654039805000c0c90b46414100105a80b030403011008102101540303110355104026007100910b5440d80303658841d8043d00425003041018080c01c3c3c1c13800d02c104810219510b80950015072a03410000c240c01ea59182c006442c01d12800784e40314071011281c51408a9980a5180c021104c0504e13802e00c1140d04e500d8000b81a50703045003400d404003040c0c0c02d2085414800403a0056680481d221080d203114501101c085000b88404c140f0b02d2920341d802c061004145e04201401500601c4228010140300b842100c3c09001c1c2d11580c0000303409080c1c000009081c1c0c034422814400c111070040c12000110540c0d0418046a4100780c07030300c920030f40966603800700291001800394161030892810400d0494030072400c0c0c00030282444604259500d9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 685229442 1250 685228192 685228223
    0x1104180b10110a15060815191e09050718050609040f030e041103061e130504081c090210031a270f090705010504140105090d051c09140607020409 64
    0xc0c0500d100c028507003200104505040c411071604020301e104180f0108102c00d02003000d8130500d610602e9448540400000740101101103103840744008520131140241400c0300cac5401c0010000d201021103004416540c0d03c42d007c4000d0809850060301e96560060710320011070b012820313115002544c14801e0601c1e040c2040300c030300424203a9025421030091940c01004106d4107007004500e00c00c03203200c1145400924014540007440d03203d4040c80341d10800356900f000074200098407049800b011445400e4408180c1d420100802030715022108900070320b0110980079007d4024090b05e80400ca40d48080d1000c000300609000c110343d10f900c2d910136448510300007e418076211088d183e0007903440c0c4405003910701d000c54000b0314002c0d26034800c81c100101000300700031043c3d15030001c0900c00c100b40317401076640c09104009000e400c080c82c0302410760f01892404480604043c090300000b88013a03212003a01ca981c038404070360240f030754a03c0c46030080b0f41040841c0041c0703090f0f41311482440c882c07500100d18814 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 685230692 1250 685229442 685229453
    0x12030b0306071106070507150c030e0f0708100501050f0904021f0e09010b03070906030e0a14060f1b2224030509070f030809010c061104180b10110a 65
    0x1096074603101180051901c3c1006480600010b94440000d080885c90011196201903600c108100c964200d1581c0310380c0066580e01c240c02403c50000180103d030280e100211906854544611a8030161f11400406420120f40f82c01010304841d4001d00203042c850300c203424004080ca00800403a40800640102e100300411400c0340c03814040c4036034411606008600c1400302d031906c1a00494034140c81401008400c0364020f11030700545503646404a104141c500342246000a0b6840003880a5603455030b1000005002441c41c0c480d03d02d801c4ca85e0360640b00c41b0360004e12400c01040b0781c00003440402048600c00d50f807018050310480d5080c010300913182c3c0c400f030396114500b6030701c548000c00e0140c004c811219135150140c3c0341c12200c40800b801c0706500c0c2c01e0710503e0100052000510014021452440c168010001e00c2642034100d4410f000089070481c20b05481d91043c06a0f51030341a041040e20301d125114401e90788000405040c00b0b03c1c0544407501034445a000384400086480390744140c000254 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 685231942 1250 685230692 685230703
    0xd0f02010c020a0b04031502030f01060c080f040e07023a0e120c190e06012d020102040501030c091d0408041805100509090c0108090c090115020f0604030c12030b03 72
    0x1139a14000ca46540c210310b8200b610a042044c10300505005005120411003149140c50449149050001c001e20715881d00c4131150048000c902401540410001600b2702c2840100d40f1484007682a903204042200d1001c402c1c465041401e40180030301400500d9640c0121840c0c540d030066424051803100325030700040c01c0f6040901c01812240c10880782210310381041620401c1a000000c80021078609100304031000280042c20241080303240760300c1080340c511032081c0d10404650250045031004030088080c1c0030b54442c3c0318030b6002038645107454449500c99040c00054a0800a0142007007036040c4003200b00543c09041611000c108220004030507940210314501c0807201140400c4502d807020300407100c5c0b110f5074000e60040180004115001501084500c032070002420030402c2a1900440c1600d40402c03080b00980208540d800881e0300c406025070511210707401d07800c460b120740d030b6454100d03269803064030b00402081010a020700050442c0d0340b040f501002518000400b540034000091405 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 685233192 1250 685231942 685231949
    0x61c111912030801120506070305060d0506070c05071e170309130b0103150608061315060c020a0902120406091707031e020102030c0a030e070f080313050102010603020d0f02010c020a 80
    0x80700000344410140c2001c0b100b401060030906800c01c088281d1a555118080241241308150b82c880c00076005c0d41d1680c5400102c0c0760060119600382c540808054074104e00407405482c98032400100281c180c044c960041500c00c0b0880310380c8501440d000320300c036640c084805a2401c5000034030141031179032101d0281c084440c0d4482c0c0e02181c2d890410001404a40038064084e41994184005201e40b907003141c20a500010165030a444c500c0300340d010040100f00c0c801e500d81102864001c00a00c10782c0c010b051071000b0b40202c41050203196181c030110120301c00c03e22420900407080d030000e40808d8280d80804105d50091005041710004141d8402036648030342c84c01c8020491290b840d800c3c41d0302411a002c2041d0090000f1447e40c28400c00342c01c0b150268100401c10103496829401e060202405070b60000d02c4195800c1c240d45403030750340171074994100ca225039001089894000800758814001c050440780c002e060000728100030303110403542007554281039061020300e00070100103845180c0c80d039004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 685234442 1250 685233192 685233209
    0x40c0308070b0106030f1503031d130b031506012307080406050301091a0105030a110412050c090906040309030b070509030601150210051e1b030901050f061c1119 71
    0x6070b60400a003e4121019410040c1b400c40c80d024048012403c44030800c2c040e80c0d05420002c090030541e44a01441d5008003811790380107480c2407480c104110041e0000844d1502c201d060b1840c9034045810b0030700b212030850300a4001030070041c001c0c005244005802095030306054105281c03504e56141c1304400d502a50100340010340000040014003194070510300e800c624001c0c00044041c070880000c099000160003020500e0b60f030179203200307621740b041c04407802014070140d80004404a8240390380c443d039107081c0c0e0340d009802180000300c03004001328800780300700e41c0b64542d80b00d094115150002d140800614000602004108502e02e43e0380400c001c90003800300351411080079a030108024106200b5080e45110f450606043c042403800c10300b8180c0480c0342c046060342c0240c2e103000107410f1020600f40c07080311194002060210781c0806410007441454200500701864846a0a10152a03031481c000305210040040000c00a021404403216680000304081c003a101d442046105d040c400f64460a00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 685235692 1250 685234442 685234463
    0x81204081b070f0b1c0c05040317041d040305070f0c0306050f01090c0207271b050c280b180d020703060c0e152208060a050903090d0308040c030807 65
    0x703108400f0049800740a00100c80d40c20090701041d50382da10b0a110355012a15a04d03001e030714500340c0c403400c00da0f0300464011106c403001c86c1710b00d00d1141c5039510a0240001d03213075240d11440d08201a20b034072280155456940c1500e460165103607001000400b15044400c3c10200c07a000011030943e000d5a401112803680303180c02949400004421101002520010b540148804105d110803072506810342100c16000c1c883c400744e0100006000b07014140c00080491891210190415400006001d40d074203044101c420721111100103901c01c00da46852190002c0c01d0440b108001403505a506804c01b101109501884450021240c2407540c3d04a2940059110300d00070401c2c00311a00602120000074241221059000070100701c554941d003c4c08015040d0000310481d0b4070b0100c02e01110740c3c90b105140800c50a455152582d01c80501396541c4c01c080e82000041550500003104990424000804007140c003942994150b65900008105841a070480f500000101e03a140004010311841440040c2c03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 685236942 1250 685235692 685235699
    0x121060906020d0c020f0d120e01140103050705031606120f0e0c0f0f010f050711030a060c0206070f20070909030203070203060c030907140d0c0303030c090e04081204081b07 76
    0x6044802000c904c00866000c600808544003000c10015040112440c050b002030f03524100401c06082c0f0512a07000c0d41d880c02e03128179048034040c000541a80c0c810303003c2ea2491a525400c0540e680c10114500030340c090f0000d0200081c50260f0840c89000e0308025000c50a81698080707070048580903200946190004440310b003040c540821324403030100c0112000c28101648200082014115440346000d00c00c00050716000c3c00b454402024079401c00500b12400340740d1507d0f000001e882101d100e08007622400700865038290059116034108001642e07807040c1041c1c8a041e020006004810210340c6000315600403803186140d0103400c51072402a0001c69960320544103041c40d011004100c920490340c117000f40a192540894640700b2107031051a88000318500100040b0020030700c21009000f6400b01d1000030416416800180707003440203031124403240fa80d5000f1518441e404403801802c040040000c1c0021503040881940c000d4004e01411741422044164440e0000c1001c40000c0141d0007100b081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 685238192 1250 685236942 685236967
    0x2031015170c0607020307030b040804050406150c0213020c0304170f030a080708042405010603150b040e09070b1b1009050607030902030f0d050301081c0503012106090602 75
    0x40d000300401c14400040c59000c4200c03546560b01c2d0200c542c451000010101c0545d40c04200b2800a141c012001d00c4603814503282107140c1c1d034010310445024600300000010034050144080b0b906464a8807407040e09010355080100010045010410803a0b0034000083c2400c030400213070029100040e02e603110881003008491500e01c80108035034003075000304225050942e22a90030f41e040011420980201c0c1c8440c540f0300c1c3d554034a4840211041148007400140c10300541200b0704036182c42e01c04001089000c9446140103c80d80500c81c640b84042104103c200110840e1507030140320203096070002503c4800e4840d0951140441403040e002e1035140142c401c1c01070001d40050b000e012810461250107079035903902e82d13000400402c00e1580c1e4140000c25910103101c041c0c510485a000e444000000103405841e9070070030700403c0c106125002542c0c030000c1c0004c403905909010780d22083e046a11302446081941d01c2c42551701400c09030043e403000060b00d50f000d0003007264480d040260b254100030541 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 685239442 1250 685238192 685238231
    0xd020703110306160c05010612120816020d081f0f140d111e1f02011b02070e07140a0f021b0a0b09010e03071e080106150813020310 58
    0x19070b100b0f0b00a0400d0002c55180481d008080c1c1c0303003e00340301c4008156030a000c2d00400d2158000107200c0e041c1440e440410401c0007141c80c201c00d9035141d507000c640b504140303128209420941c400150384920640ca075810b002d2a90b0700c0e409031425020915400740362440303080031481079100b030f2142d100c02e0105114100356014411845001603600303042808403615900b00b4585022045401500a8000c121462055004190400b03601400d040c40204500154000c000324140d0044011352814164070541c44407513281c24258030786540104031460a03c4001d5030500c002514180502108984e44060000450080e01d040202502c130464121442d04010f4104204846841c00002140800324800da56118a04050700c8410750315507180d16000c40180e9005401c0708100354107124040001074014040c00150090300f501e1700500c1d68050713448031800d090303800c64042c50030300040310040e104440344151516a40304416461882220200e1340100b41040c007501000c20800c0d4648140310303102c0c4918040c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 685240692 1250 685239442 685239473
    0x80601051908011d06150a090b0402160308090c010521070c0c0b191b080306030102040b04350c241309150b09192714041113020c0d020703 61
    0x403d207601c0803080000485210710350084401c422782c1d03401a010b56441d99419550705000c00210401c100c0450b0a01606900382101c0002283c46000d800382c4055204d0010340743c04140742020881982c50413100e407050010b0081c046003c0188081180d00440c084018040041400f0241140d40e01c151605c00c04449800c2c69541c400d014201c403d140e034580e0284010546d8503088141c858403900c03220300090180c0b04070f90100608200c0410003043c003188517850100421518000c0303c010005c60ec02104030040c16100e043e5a0743c001e0794201400e800c00c14050300038807500410121000f0b1058805c0280c81d0810304005194840000c014441d40542d072250a12005c1c28000b03000d540c43c030305214507589100e840c1c0018010720030006a42d8034060759064110140440765203107810140f845226940001041000c54104c60030305007884c1c3c070300b402404894041d0360010101c0004085c0003084c824240c198071340c00415a94204240c80198070140316000c205030380366000e071041c2451420580b61a229010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 685241942 1250 685240692 685240711
    0x152a0703030605040e10050901020c0709060503010b01030b150c030d020a050a02070608100b1c090b0403021504020d111801081e032b1506030b01030510080601051908011d06 76
    0x440c17104038400170303546000d00041070020546946064000d401390103024031a890384d1040e0080442c1044407508404140d92003680200908588000110207480c59001d00f65003040160844c440310158140051914030f00304022607180c20300101188089900402e28a40050740c0407500b4120707503a040c04000c0c0240341b140703010081d0b07091100c9060910a032912610000071000180b50a000c6a00c2080c00a20020803100f00200d43d254104264111401c4800710018001c41614042034450034500500560f0050112102400700782c0e22698049040181a030344070030b070540f09420114802902c01c3c0a000307040c0140c0402d00000d41c648400c0e401030001c0100c10340050080c00c05040708896081d501544110b80e44403005008006240200f00c0f12422144102c5440d4020450303982541060003240f5081c1c0e0204030a50b0346003079680d02c0320308030b01440d4100e40144004215901d8010007081481d980c80103d01c1007590384009060031100c5030380482e84840c9000903245c007130580501520b0350040440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 685243192 1250 685241942 685241951
    0x510030b030d090803090d06150b13060f02070e0a090b04050709200901030518060a021201060e0112020a03110d2301150c0f2301110903152a070303060504 68
    0x2460648034006e140e03019000b480c070703d2420f405002c80c03600617600340d0071000c1c90813401a407504031020150303014101c44650900f800c417001800c148100c8500d903096003a640944201401c00e400400c0260014011a0a0760340380d03d400c41c0814000c40350940158420300041002c41d25000c0c1e00000e070b078180c00d66000a400080703654104090350b0403c85103400002d2800064650750300c0204100c4003488414034000c0e00c550401c000f0725048a5004103c6243e01100c0601c4582e0390300d03001c807000c86502d011180010f8002088241441950b0090700100c00705081c081a60350a504d02c0300a075030003106034000020303100d1621031180100011a10300308540c0c40d601300e9481d810400001104101d41c41110100318203001c40105001040d406414003961201e60003104030705101c0390251032610740c0000382c81c0f5468904030844c1c1042c200b045880034080034010b44815081441032050300e0600510b110700328910181c0d600c20078540051315010300f0740c1c3c611220751284038a04000b002c0700d5058210f1802240b52 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 685244442 1250 685243192 685243199
    0xf0f0e0115050406030807080901020f0a05060609060901121b090207110a0906081506040f0509061501020d0e040203090106031a0103060f0506150a030e0f0c030f060c031305070510030b030d09 84
    0x190807c0b02c080742c0d04000c685584204040040345004201d40700c44655014803403022080240c0030075803d0044004450b0401251201000c100c00380700280f152403404824810000e0000e403801d0b18020198415000c6d580080da529210041a0390000c4011520303448102040d810600e4103190100141c240b5a004000550030409180c2e984c808402c8182ca01a650500141565980d60040d040c082020a418441420b1804200790b9039001501c41c00c0d030080c85c80c0c103041e0180d480040c810b400c90384142c0d18100301141c140305200c020350020788003074901d549495000c00400c0a00e250700110001000344440c1c503600d11704100d811104100c1e1142d203410f04140c2402441d90b01e00c139071071300c1d03500c0340c0400300d036582004d06007d030010205814a40420f0240d582442c1925101040c1a40d28040c2981550058002c1c402c0241e241e240c12141c2d0301d608030040c80411681e00345004000c440c80d1007401196002600c0e000012030303501c0d44005903400a034495040290a040030b100c014400003160501e040703007604 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 685245692 1250 685244442 685244453
    0x23130f05030a0206070c051e01110105090706030e0f07080c030f0d021b130614180907060507030908030412140d121e11070203190804090f0f0e011505040603 69
    0x9041c00183c4541342c085001024041034210110007400002c00354004158004c1c03001c1509803008400a01045402c03102e8040e402c07060017458843c0030400c0151000a007016003d034028000100780c920548140070b1103000c8a141041800c0107004120020300b404800e017401c00d0319010741000d2800a58010040c111a8a078000607082245014045c28000c01501e40012500703440c503800241842a007000030000700b08a080d9540c10400d035040d00c01e05008924000b17807901803c8203640711903240e804007404101481c414000303480c009201740385c07203144c855903003084600e140c1240c0c11490022241401e900208102d08200d01d04085800c1c003c0d1028003d4200041c205d14914511108243e40315000b00245044969181481e0101c0c4401007280c03001041c07649060b0b800c1012b0403402482990344002070b240c5620045080345034000e5045180c1030a02d032408028090b255504c0c411340b42c440d00310760031000c5513004469011519030000580c48039080203a643d404c1e8198080c0d40101d1400300d00b403002c04c9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 685246942 1250 685245692 685245703
    0x60903050d0f0309060f0902040b0a0e061302070206040303271508091218120102040e150307170d0807050405010e0114120f09010b0301050114040504020123130f0503 73
    0x10311410500c0e18002c141c00240e024240c0785400600b564505a551303502255140d01c4040c22074000d0310104071000800c41449884030751400365500405402001030b0003490420241003c0092280c40981021900d03404036200c0c1c3c0050f00b003140441c5400c914610300210020b41c07040000c0c004555010070303500c1c05110401c14115a90003c00f007101030f034000303011050b017005400d400078004080309070b0300d07400c64403810124001050042d1042c3c0d03400030038511107403050090720141c5104c0a09500d0302e44448040207051080305603d29014000e00000051140c0114140c040b40101c5901a00c0c0d046c4448170000d0062000500c02420b005d411b220520103079074040e155403ca04001e00741082000800e81d001d4280f030150300460300428603404100b00303140400d0032445020f8003221009001008141040600780c03203090243c81100c0201c401703100b04516068008640090040c10030038000e80340b080c100803503000301010200301904001002c8000e110090003d000a04130310100c11403407400e2030300081e00c0d031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 685248192 1250 685246942 685246963
    0x3091528090e04170d02040f090903390804150c05071703040312020106060f021f050a1506031508010605030c0d080f1c0b0402181e040e030309010606090305 69
    0x300034000008041104c006071103400307450401041501d8075411980e040280d8458010030f407104010b0400007401c0f044034060000300325455156080c032482103159201e07110050b0300302405030060070554203144115424400049900900c00666200c0c18805108036152104117404100107e85040c100410340104503181668103030303502d2290003651402054514025030704042c2604800308104000035070154054811a01c080e04d4224419904000581c2c4807031040a6208140071480c042c0f0030b00d420a0303800260301c820302040002d0000e03503502607180103a40c01d42024000c81e56401b40d4001d840190b011150042076140001d0052a04180219032184c40080b121070140b1159a105010844a0416524051003000d8602e84038006421010b84981e5040d0919031040c0c90010907036000d0501e4000c84a05170404405241c1e01d0300280144048140c0461a55654060310250400183d489004245e01241c032000150388030b044c041c1d50242120385942c8050280068400f08000051021510300c20f00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 685249442 1250 685248192 685248209
    0x20307060f0c0204021204030e0306040b01050f2e030e030f070f080c0a1104050106110606010e28140423061804030c050105220f050309152809 63
    0x3072034401d802550200010071000f58080d00101c1c031701403c034200e00712451245000b83d5410051500b81d2080c140c481e0710998010307140c94000380051186051090704c048400b20b000c0c0071502c08082040e041c1d07181c60106007800489800805007450700c15418014280d00c40e071504051850134643e49540106440b51207002000c1003040e5041201780001101518041c80b4808155001c1a41c0362a080d961100002e041174404c3c0e00c1c200c00441d000307114064900d40212684000c1580c0d488000c0156161410040c0030307030f44640462041561003060343c2081b1300e150000400503891609094101d443d0903540080c1e207000314036146001070f038040807828100300b900d1410f4501f68640c0740c032000706081c01d91001d4050340901840e411f100400d68001c2208107c81c0c0070f1002040301c6d485d01c08a191000c0c01c0200c440707481141c0f803558500440c8928100c001d540340301d201102e2609500b48086104211044003081c0c80e8440452202c008441011750b0000ca0a58607034031002c4407042c132002030b01c18070480c00344055 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 685250692 1250 685249442 685249457
    0x20309011409090117011104031a190e010c0905030102120c030417070f0501150609062006040c0509010e04031407060f24060c0c0314070f0f0303081302030706 70
    0xd85941c0c02c5440d41e410181c003010f0301d0b40c1c498003250f03101036400c0c800c41c080750310b06040b80460640300d5081d601038980c0b1522818a10821440384510028041c1500c080384242c00c4030803010407680e1060240882d6400004900603581540103000d1a2041c1d0059000c0d900400201c0d2140d00804440780d841000e40144503141d4442d0b091462244001032440c0c0700c0343c540081c410b020b1021005040c1c1c0711070b10400082c021154080c2c20804045503034031840c80810036005060009038061220a01d01440b11000c850844900c030350320754901802a2402c1d1070300341e800e88040c0540d06014840c6400340041d41801212400d0955006000e9462510310141002c070200f401da080081c0f60f0031209072210100c509000201441d80090004141205c0ca000c0ea0704440c1000982507004203082400c094004040106103450741d00c0300c0300345c410361051400540c0691400464a03d03c890041000741c450070450740805820340c0350160040401608400600c0030200b91800166000a054403c0d42c01c0c41c504500f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 685251798 1106 685250692 685250717
    0xa140c01080402120c1504030209010b160609080715140a0911090603070e010f09061a190201110408010203061e0315070c2003010f0c02030901 63
    0x902207449100007a000d4a8104224590140c0348401e44100c80c426030001020217007050140d00f4120001300b024000e5041401d4428003400c01d00030001d2070301c1ca4521200b614902c40103001000130391501e075900d0030404054182e846c55a80103210fa01c05450079155000a003c009075a180d030600d80340009100c410160003401203043d0002c02c0111640060b80c188036a40c00020401c0b5058070551400242c0000c0650907180200f08000840b034841c0e0502c12410140c2c0d41c44c9d446403071500b80007030f1032580068040044808607100c56510040340c1d2100b030001c0c2c3c094543c424144154410110740006c803413a041d001588580000c0701d030a0f140f1980b484c5032004c208030000f04e142c1c043c0d101c0741d08060741c0c202515240340c0002c050309028404080c0c0b983c542d9000c0140568000000c1800300c1e801c1e01c00d08003401007048100e40098103020b2003ca030340000b5903d0203121902c5040100082c00319 = true := by decide +kernel

theorem cover : BRFrame.Cov 685071942 685251798 := by
  have h0 := BRFrame.cov_init 685071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 685071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 685071942 ≤ n) (h2 : n < 685251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
