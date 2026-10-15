-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:33:31.93138+00:00
-- url     : https://prove2.me/submissions/344e5f24-98b9-4312-8975-1e29f583c56e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 906834532 ≤ n < 907014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 906835782 1250 906834532 906834569
    0xf08030a080112230105011d091e0c1c060b0f030a08031315140c0a200f06010f0f080102090d031206090510030303050c1218010905010603200901 64
    0x204000c0950f00031122800003c400020601030004241c103c20705101c0000340e59403611085640b072042c2d24a0600051007071408001d0a0310000c5070301481e4080040c0e81b070841086074006103040a80100300e4990201010785803040d1024110020425207101b40740030055001c0000c2042080c210041d0203d41c158400c160380c50015150102542d0003842180703c000f078880c40c42da03070948401100700741d940e00b0540d2024044520140200c070107400c20200d004883c50303741102ea00a10120094404002c1c41c45014203d1840c03102c1004104140c6100704280c2d21b8a58450130404500304082c07161010b84940c4102c0804d4540d0180b003203d51040d4007c00d00d41e15024243c3e019240101401004086155078060000d81d0121a009031441901150017807442e180c00c624025007100d1001d00158840d100a00c0f0040300e8903521000d140c2c000b14413080411700000881f13a1280500500c0c40300414a5013030120001c20080d0a4404008800340042803100c284405414082800424401c01610007e5800083c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 906837032 1250 906835782 906835799
    0x807080c0106090221070305101412030a030b01020f030a021902040f050705250c050607050a140a1103060f0402060f0d051311030729040509100f08030a0801 69
    0x10200c4400c10000420200d6848001c64100d8024168030841820120511803420040241403540f101050500700114188103e0200c400d01003400342410850901c240303030941d0f5035042c0568580020017400c8966032184000c0080190400d10b005070301502c02c0384200c40d16154044280c420440c9030f540200200b60440400060580ca00c4100ba81c0007655945141c0c04d240c2d2030300030984a092152a07087c0d80d140e6140040782c2031036048540c05000c4445001c0e420024087c0605001140d400304d804540303c013020305003203080103510100281108001e1040ea250041c0100f900000c80d0300844042e82040c101501b4107850707480884103c0d407130004d04030000b40140f40003000703048a4000d11a443d410700c00310031040412100140c6040d41c82c0c3c0d0007540d4000810603035409150010f6410b03000361450a00e400310303030301041c80c80300d61444200300350b03a03000106669414291401404010012000c0d403c00c480904013001d86806256007101e0510340200c1c030070100000710b500008196845001a07803a1103640c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 906838282 1250 906837032 906837037
    0xa110406170d030b0402090301021b1b06030f1f06080601080a050c160c1203081504020c0a030309110d0b07020f01020406050417030d290d2f0307270207080708 70
    0x11303194019420b04c1100003a440034406002c0032000041c03101c4400318526901850110604c071511907601d10b07001c070115551680410b40c0d40100c2095a500066240d1194801450000d035251350103181c4a12000608158084c6078940030341e001b0b895440300b0303886a622070400c1e14012581080d40400070003506010316516040b407551035004404c1507060719258002c1d101d011496180a6002881a00034014a1401500c0c0c02c0f411003401c40342103140c500b102605549881c501c1ca030240902d90798401c3c0344140b00030020724051a02006103800b00c640518a000e11140313409071040c02c014410440d211000c0300e030500c203c2e010b440041d122681803600d005800d40c0030544104000d00d450005028403002c24401d030040d16034a40961503c88000820001041002030300c154200d4401c040c02c503031500206100c1505010180d105010190b1442c0c990801360486100040041350548242400001c60b07019880d802580c180100d080980c154100084260590040b144043d0009a040200c1000510007900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 906839532 1250 906838282 906838301
    0xe07080c0901180f0906140301090506011a070503070f0b0601020609061302041409071a04060801090f0b1003050703060905040816050f0304060f0f020109110613080a110406170d03 79
    0x80f000d050a44445000c041d040c0f85611010402e51208410703c1804202c5005151002e4190700802c244009a101c00740d035000f041c03048101410400307008034180810101101c404c20f8014040700d50f1040c480c64032841400c00381c0341c00c0e1039030312825003c14455840031401d14001c0f4240c000519164541c0310081b80c503683c0000c0100c0e40705648800a1544800707504200348111040d0010344030051070000a9400c3c03500d1148903005c446010007003841501d130071200d1141910300764407000900701c0c8601c920400501c1031624850384a950a480b034030210364141c119500c05e4a195605010003981c461810007550010344000707140b014240030b04002110017011030071007503002c1c1c02101ca00c0d4800000307060031a8820342009002031a8250062141504440e5543c0c0d030030110300c020056005151161841c460310b0800e014824a40011700c840c7c07100030411404043c0155400341c941010715858402c1a52219018590155003044800100d60b03540c80404800c11a20801425000242c00c2007100284000c0b607 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 906840782 1250 906839532 906839567
    0x81017010207020a090603020a06050a0504120602090d060606120605090f0a0605091f1a07060b01030b031002090a0909120c0501110a0807020705060f0711040b090c040e07080c0901 79
    0x7070000940e0f60b1100000003807100701d45c00100103003140144111589507412000500904000321242541d005081760708a03944942d850706031111600d0020040d10032091559031003410203030620140300055200d1400c43e2070b181c84030564941e256001c10b095030020701c074045d80720841c4000200c401c08401e4045500a003064000129251600001170003001c066a64010601c0341c04801c20241c00070400e10b6010b4a103500c04a040040100c100092600c1040c0d401401c00c1d03114000310301d1a9009030050200245c1c000e00b030303e95491a541c047c200941103101002d10a01d1100c00000795181c40d4810344013844d402c42c8111809074898002903036030510b241c00448181d0b50701c1c48184820700b03022000d000011420f50302c860440c180503d00900d0605540c0240307105280400581c121800c92604039501039600004030890b841103200080c000701300700d4001c1c50700000c0039030420a104844e50000c000366050135202c030003d9110304074100c41100c000c981150032407034208519496580510301ca0100160b125 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 906842032 1250 906840782 906840787
    0x312042c040305270a060f030f020307020c0112180f15021804051e0612030c0a0627030e1203210601020d02120f0306011e0f0f0810170102 61
    0x518603036089950032901030307001810124808108603c290000c0100c410304000b03202c0c0d12010704c1c2c00511112610b01c40e08040c403003140a0080b40f0340c02900004007d0346580b204540341d00d030845002c2d44aa0721201d0107400682d446030381400d01ca0051085850003008003055401c240041e5540c00261000b0500546190240c03041d03280d290713101070005001c0364500c0b058840070007142100b403000b82d4101402c00c80b000d00013407240312a030454031080240d20550072070701e0750800ea5600c120b0504502c54114141d82900498084a003440100c0d00301c14104044040a2804141040c4c080388404418040007000101100d840011620f0481401c54175600341c40141da25004c000c421030700302003041c1c1c00c0b905030302d124203810481c1c6503805110181c1850070b0ba0010f0000310703c2e448480d882070310804058114420002c804104264417074002d06006d04450b4104404408680c08058403002c03d106008000400658054010a00c1003249a0290703900e0300071001c00c1745c2010b440800303503038500310031015542d402d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 906843282 1250 906842032 906842099
    0x909030403060204090f18050606040209060d060b0403050d140306130f14040b060103020405060d0e01090c080a0c3303181104050c0702010c031d0a06080a0b031204 72
    0x103d10040c070042444070000250201850079000c152100845d404403140c100d40720340404640041082130380040200c400682da01417230030010f102da0188000301c2440e1450494040741c02922000180140c9002c4c400312a171200320040216020001c03c05084004070b024000b1900c1400c0040c000c1c00390313842d881004240300c04106191400c480000d180d9420194005040c00180551084500e82040c0c00386000d41c6400d00703240100742603204001d41c18999950300d500700e91300300c4002e622901c140d55000c8240c141040c0d032031254640c1c842c40040191008050030170002250301142000c48044001640d001d11844482c104061701340004403032038800c1c0368844800200c0480c002202140c5588910071810818442c0018001151802000d410002030204500c0000d032b0380001d42c02075241d50521381503104403034281c030401450031000b04c41d40e0000020800490040c1d041003006200300c0c8503400170400991f010701010b031b540c010f0800c2c103101044104803d0011000c0d0340108226055013a041400d040c50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 906844532 1250 906843282 906843293
    0x7051216060807050d1a120c1c0c12030c110d0f03260901020409061421101b0e0306012304270521040501050315100f0f08150909030403 60
    0xc00004040e118889002c01d200713185003003807d00c901071820b40020308054407104003141e403203800c3c5002006404a01d403104030400958101c3c500240c440b840080000041d81c0c90302030001c494060301152081034281500c911420205091140960029400b034888141038605031035150044440c202c2082511490107911500c890103540540b80d0304000603034591400c47ca50048a4464000c50b1051202840070704441d81c0d24a0501b0700903080213614014007501c510301c946071162607020b19268030700b00340300301c5400c0003002001c132001d8200b80c4503004620182c2c0e04068581d4400d01444c0c4458a000008024444c40082c0402e03c80d00003400016031000248190482d494002c0540002c6541d045c02100c1041014003043c840d41d03000d41c1c3d00e1340000071029030101084c0902d00400d41003100c04000220405101200c4225034440071b09a9116111242c80c0184003a801d02e0540000c00c0c03400c00e040d80403c4c0318091040c481c0c080f00c5042902070b00c0341000c0082245c0c0152900016100911011003c5507 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 906845782 1250 906844532 906844541
    0x90a080a0e0409140f0313151806080f07050a02060f06040b030304031b08070f05040b0d0f0b090105090d0801090c050403121d1c0303051b04030507051216060807050d 73
    0x18080c18440c44c81104000c130f01e0f0b26040c400007649105810510402500c69605100c0200707030b410120104044140e04002140d0040302400001074010408000281e07484d0020310450240030030209500c4581e80d005c0c402e880d02e124800f20b01005034046c400184075290800381e07a03500000014000300c5e0ba40030000c0043c1c65a00035030400d4891080b090520290f101660550800400d8070b400131f0200c003481c1850480d01c00d681403180342e004688030360366011aa51560716100240c0d62110030a414800c0324105241b81d01401c6404410035807814020070721155002980d0002c0c8081c5948000c0c80340c0c00d0807500c101401422120b9418801c080c0804400504264185100c00c0309541c1c44030240d042d42e01c410242d10001d03004441c01100945041e00e0050b1a07032104000982c0c150070003003015214020440c10011300179022a0b4500c1000c03801204104010551b9030444004903002140ca9203042c0040e52101e8400c54040d51034903400360200103560207520b00340da111085040507428044400200c80c2a40d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 906847032 1250 906845782 906845801
    0x1109060703022b080a0c02100203040602071b050d020409080c190618030503010e1503100204090501050603010e060d030e1011160b030a1d07030c05090f090a080a0e04 73
    0x503000b1805841403215481240c182c1c083d5941c180a8051000702c40c044d00030b6602612004010741c4441ca110485802040b211012500d0400c00715524580741c200780c8029040700f40c045030043c4c0750714465003d10290b041d00c841a544001c00c0000c0d200c1850b800c200007401081411a070014042c4422650180d05000c0c0c00b8009c01c18080900a4000b58a00402200c3c030409800311b40c41000c1c0c8140c1e000c40c2d44441030300d040d103012640c0300d95180c6829200c5104107105040032035044c40b4810403081c081d04d40f50041c0040b24013160062041e40d8a07001000724030b0000b40540c200082019001503141c5c0703000c070160f00c1e0150280c100394105013824008500c0d9903020b00070701c0300030624400b00c203078a20b001000b0b0309020b48c03000f25503014541d062060250f454807020b01440d51040e00c0d03200340c60100b080707642c0400c2030011680c120b076142680c0b4540070015275811301c07440317101e804a840080c02d83d08801e40c9040c0300d254040042c11001c24a80e4800318190820400c84081080500c2544904d40340c6100e1007004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 906848282 1250 906847032 906847037
    0x30b0a141b0d060b070f12020f03122703180d08090409030c0c09091104020a0807180807080c03061308090907110d02010e011b090b030a0e1203040302070b0a080a1109060703 76
    0x70300307990b041c4080b081c501d80307c100045500c10a1001d0b220080402a14081d1a000728030403400d0f10b80980b0703007109041d10301400d00c650406d07192000146c02c0000040c480c40013103d8401c040030060704201700328040d000e44003a2921000b00f024032640c0c60103900c0700320441d21034140182c8008045d101c101d01102590001002c83d07990761900400d1211007070611000c000c007100c09502e0040010001080400068000b000340070303415040c6001c1c1d10141c0450005810441e0444020950f0761450715500c552910000d4000e010320030200e401d200c01c8900704401280c00000052078885040d060112540c00103200600b085a40001028640014400104054566400490f0890313031002c0301405c40f00085810b841907400072071558403103904100184211452151030545955804c4a118007510010b40441c0003030142c1445070a0002c92080510301440c001d908850a40d0344a490080c1c281c03044403583d4002c03c510f1000039140c601150010b040c811421718129040c070314030324007051f400d41040d0001c501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 906849532 1250 906848282 906848303
    0x806040f15021c0902060906070f0b0106020d1d190b09030c010e10080402210d021c0509090603100e010605040b03060106171f030b0a141b0d060b07 65
    0x1841180850034025400280307007140f811141c2c6440302000d0b44510301030200561503181e41020342d40c985054603172115000d4841c1e6510042440c0c020004081c4e10012503e425500001140c150f00c00126404901c0c0280c0b140d0042c50342c50428160380750181344420780e02c0020364108003200301c2024810402468420300460b1031300d01c0d8000b00350030540102001c0c0e040008556030600385540300248618031131850300385031000741c980c1d001003080d80701c0541380001015207442c8041c403002800500680340d0011a400d565848003d070a08076244507a0ba240c0a000907000c0c0414021460400c0259412910060480380c1680301146c4200545100c0345501280380d6680008101a046c14000c048900c0030440203414a981814030142031841401880e09440090741e001400c440c07a101c407001c0e0b846000140203007503d66203141000e13007510116421110700d801c0200300401d541c940d580641c01085440d07000e204201400c00300d00e640703070042c0038000c44194540e04002000c0200400906445001c1e511204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 906850782 1250 906849532 906849563
    0xa0f241b0e10050a0309080f041701020304030509120a02121f060302030a0305090a090f1a0303192313030c0f0b0913020f1b0106080f070915080604 65
    0x850031a00001260148103410403460040c0c0e8540700b509115030400e00708503440e40801c24040340100a00c190007880e504001a00b8000c020302d18018208440e403025210194940602c600750a0b4001a02d004020640510001619103002e815041e02e0b0b03071800d011070300400c90b20b40008e040e40450505a64142d00b2645c50010b06085d144648000da5a500400744090b914540c0030aa030350706958400340c1003090124803441150380b03420300c41c0300804c0c0d8000c06005884500010034014000360400842110242c1c03280700701c904021080e9a507068440c000c80020314103420054464505118088030308241c0205041041030055001e40300d00d91012880444003415450458410046600418062070480004010055090080782c5511400344c03030055110f40d0003054600030b40a004c0e00c440c239640000c40c5000490211400340b5144040103802804800d664000160b00d4003004200c4c4206508800b07024040040a45c0018089500801d10320b0300f810798070a0560705040301070b203045608143c07000103a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 906852032 1250 906850782 906850811
    0x503010b0f130b031e0606090105010914010e120706031b020f07090b060d050403030902190602030a110a021207151e1809020412170c0a0f24 62
    0xc50400d0040d628640286a0750000a010100e000c10781d50205480303194a800503202408900003000d0040a0030b19108002241320f0f480f21000c5403141d00802402000295540c0f00311003103011128408049160111501c00446041641c1c1c0701c050340001251900c0349c520481009800b006100daa903000031007404000702100201d00c040c04c5881154052414200d6039400840c19504503a001c100006401c05004042085030160100d1425618500400c12040c19016040100076038130868503115002c42e9080604007d02441c0180740c0141d1091082c105594080c0620308100240c000884054015590024140c0b000740900c40300d050f0042c0c070041082e50a5503803045108206e606140c500300300c0980c0c50146400c8110000e0007004042503d800503000728445803030180c0f00d455402c1d5a0307251030306108401c20004450841d0489001070486504250140035a0300d200022406844c684400c1d499101c2c182210072019150a031441c07000e22907114a0075081800d21004c0c080102c0d0710070094212 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 906853282 1250 906852032 906852041
    0x203060f0a0f2625150e03060702011401060c0218070504060f0302160b06220c09080a0b0403030914010903200105100320060414273d050301 62
    0xb0220304500c120000359114002181601c0d06048034000c0c1403036121891070484d4030903503591080850f40c50040d109010154003e9030229402000e82c2160001d448031241242240c0903541030589184101c00188109032107032016640440c0018243d00c44040f001c000103c40410a44055020540021341000802d8000301c2c002c0344030360941400c6080940c0044801c04149440c44024401600c010001d802a91900452440c441c00b0600c00008040241c1c0403030002d1058100081c0480c14000d00018862030001c3c054000d00c0c0e001c20029456101ca54064000c2c021103d002c4500900c103c850180c017900900c10351124500941d5403002d41000780b90710740f085405400811002e64104800c00c0030301c01940b1400b0781160b60100c003007081c1010b801404031000c01441100e40d070100c1c000030005a24410342c040c0803040807044440036208007501c0ca0784492009808a0070303456206450000d010608074100322901e030440d081240c00d490005000070a03012494034400c1145c1007450009000a00b0240b08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 906854532 1250 906853282 906853319
    0xf0d0807110601050d080c01090b072c060c01020c0d0f120b010203031302120114240a06050d060905010e040512030712090f050f03190503040c0501030203060f0a0f 72
    0x500100c501e207800d01d0241c890b00140581401500106a81000c010804c4201c03885d80083d10001c01601c80702c0d161081e0005400c4e10100c00140145415000b903031003900440301e4004c001c40080501c9802e03101440541d810000c2d4240b260755081c03007101100c080501c16080c0880d01655000800000c03560040d109003043e05500e29406e01d850321152440e40c00100b180d40080361008171102c03006180c40040e0f464100b11440326102c0d42841c10b07420201d5200f0000f203014801a1322200b040b060145180082140803c927038903404071440004000ca41c0c0241c0003072040311810f502c01b081a50310343d1100300a6520a80c0140788041e007050170003042c0300060142905a9a0301001f0300d2460804c004000c081183c483d201c10182c960710380c4048204100c4005c042682d66218043d22502440c00c06c1c0d2940f83c0c0c104d10410f40510140c2e1802c0c40c0064030901c226407203941d102c51503c01c0b8070304110044001b50801001c0c550400348594003009a41e0701e1040100042050001d64200d00d401c0111886084444c1384 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 906855782 1250 906854532 906854537
    0x8070306061403041e140102040801051303090519240219031d060c060421080702030a2a05010222140f13020f0405100c0b04150e0f0d0807 61
    0x6501000b5658004110ba400980020350201035290043c400da56451201350010084003150100348281181900a041221841402001160b4901054104510b801140100000c031070b07400c14061440c0c5030390401c12400805c90460000360300c80c06032400c101404484e04019203440044031100c01e40c108500c0700c1c80849074082c0000d01c0c80a0b80c0c0940700c0841d02040d401d020401d41c0302044545c503600140c0d11103000080489206090500340741d00d01f140841da8091394141c44505c0280340303c1c01008000d0089485a0046203040c0950508031041d40c2003c0e0040c01c01d82c003040c401c1413071000221034040014050400140c1e1071102c81076908100742c3d280d40005084601c81400c21050300c2210040781d84183c1034030841a4a5020800180d007c02200340d96801c0720b20210700198010f4001010344141c4030161000840c2d8204100c007a20403401e43d410092146040c4800280000c101c203000201c652241400810b801090613906410a00d02c0c1da001850b9178044007410310034a6010280380c1d004201350 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 906857032 1250 906855782 906855797
    0xf2205040b18030712120e01090818030708030f0904020405030a150c110307060b030a05030301060c02040c0507120c030306050a120c0618171e0f0c0418140c0d030807030606 76
    0x550f0345800300001e04c20003501b88213100d4402c10144a1581041c6070110781140200968140c41c5031400858120202d400c02101d600d640381802c0c4d0900161302420364003000025400c0146181020985500a50031503410540900000400385c90400100300414032034802440480c0e841c5a582084404501540c0c040080c090100880c2c2640401240e42c2c540d003020f00800c1c106072031004607203000740c50040103005200000c0000b800d281e03c021100e40d0780b44221070611600241d0740080300c43d401184030103420401515840080d945c080d14007015164800e01300801d082c1da0390340004143c011154442848125501d00d19801c01c0341d40384402d006003c0900702409141d803416100d10705450580901c8030050302101c84d5003c0034108205032400c148100d002d075040e0383e00680a2a40724260503000600324801c24410206501d4140110945010407c4100031051007503216400da0450512203d0050f002e410015206902c0341c0855813001c9010307440d550360b18146500d006040310215440803003040b001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 906858282 1250 906857032 906857047
    0x203061003061d04050708060f251b020d020909010e0f06090c010c03030b0a0b070605330f030a0c0e0112151e0e01150b07020f2205040b1803 62
    0x280255400d580c181211a04915551351800b58039080700c0e80c000e40140d01c240c200304600f0b43d415070412440b415007100034250303d8440480e4901e0044d02d03d41140003003608482008075010f0200310007824580020310071040e19075540c020684d100410364000e070269444454410340740350100401055800034900526541c682408a282c444011010060400c01c040102c641454469000400803100040c0445400d80e41ca400750f843c0d55000600c2183e41c2800e050015041c4003c03500801b242c0c1440301401c01110641c41102c81080e85600303070059000307800704141c100e19207040040c14010b910850300b0012681c10041703001d03103a08050f07100101b44820802140b000504c400d50600d040b0b00500b01c0030070031a8000c3e20b0341c59014075240c45201c040780307440f1a81d05072030415040080c9285444102e00b00c119212407075050544034091010f900901c050241c00b116060010f01601c80c0380d14400c81d02c1e20b1942c02983c420940d40e054406468102d0440140108035480c00c06c01c5030300311840c3c0000d6142410 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 906859532 1250 906858282 906858299
    0x1d07080601050d060915080c24070c0807091409120f040e010906080f240a0621030f1b11011b052a0d020f0604090e070f0b1303080d0902040906020306100306 69
    0xc4510340030100c0c0c22030040c0c00d0902711030b1040d0b428860303111003490b0003507031030f00072190742d4407070038825240d01906251440303104041c0100014041e01881018107403510038101c50114560101e0800001c0740d208010009038a01c00440c0e4a001e001100e10202c2e0585c07801c0341d03492412402060000700c0390400c4444994122002d00d020f50a00b07654050480f403031341c90010801c02000c43d41d01c8101c0352401180a04929524012262102c070b2081e10b8441e40d81c040aa4100d80b00d540303000c2d0307000c0c20410f08103001c80407886948111942c0c6005162036074801e003200d00d86144c03050400004035503d034048000001c0c5503104042100328105600150021180c019002521002c0d500002070301070340351141d00f040a0b4030b80008030703005011124800e02a07110030400c00c03541da00f4284502d60841d901c02c05e0201e20001240c1c1124441503c0551960002d800d41c6c450102e1580001440c0e891144ea82400c20f0058032540141c03003407140110001602c81c030b00b680510000d10b50b1001ca0744105480c244081c0704412 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 906860782 1250 906859532 906859549
    0x50417160f0501080a0e1f0b09070905030c0d380105090609271c030612051f020903190501050709082a09010f03020a1d07080601050d060915080c 64
    0x7030014102040c0c100d03031115601d08259180c0d5010900280072007c050001c1142c0e0072040d0380b6541a2890307440303070390795100844844206020b11a4190040d803030343c100340c1c98030151070004940203580034040c550200341040b04030204102c0d5042d0b00c480c10529600c1000c00180b240b030041006a40070b510900d4400d0000f158400c00a0080c401501d4014840c801c0c45107200c107000c0d00c0100c09045907292400c0c0406510318100c3c00603d03000113401c100e00419080e240c407a5100c041680000244040c0156004500203004144044031100368284a00c1809a50800c5200034428003c0041800c4c000641020f9080da40020b040c1014444650020060040d00103511644401c03900c82e40b0a440030081c400c54000803010701515445000380340085171038800000d011084920840e110543e40380d40c2d207102003001001e01c02c0c002c400300708600080e0205000d500919031000c2c0514015141007050148130b001ca0703207550443d00b601c9589402c811400381d84188180c002e060524014070030010f450700016102c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 906862032 1250 906860782 906860791
    0x60305061f050702220e0102120429040605070801050607020123090603040b01090606020609100518011d0d0207140409030329180103110d03050417160f050108 70
    0x40c0c09401d1594501c584243e4021682c02419075803482c4002ca4000300380d40c0c03180c9000309054079000241e954180c0506c06c0b90044004124061401e039a103440b08001d0b81160789000070b0040d024214000e407000c1010003136214030b00c00d100c005814200f641d030060851b40141c21460040004000e020058ac0c0c00024914400e0110241c00c000f83c103886555960703901034040c51540080010042c0030821100c004c41c0c605880794180c0030041e0b0369076800c0480c0d458005844e030312a145c00c041c41c003115480c0b103508144da03c04030701c004071151168038210785401c40c5c48440f480c2d070134000c82201100b1031240c24400c20516260501c01020316904019582d480e03500317070010342481036681c0d048801c100350180d040405160025802000143c07486070303d1048081c2c642418034800c000e801c1d64248441100480030f810b0f250003840084a00e050f110902850403c0d0000070750074001c0900c40040c14030030b16004c81038400b0f00c00e00600320b008068050941c469030150404213019949140600690340e0010f56903512 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 906863282 1250 906862032 906862069
    0xb0906090f1f0810050c0f03040b0903040b0c030a0201110c151003050d091a041a0d090618030e0303070b0f071407080307180f0b0714160f06030506 65
    0x580310900c2001c4908070401c2141c42c29401d0442c0040d8100c00403030754000d403440010003440b007540c480c64000d003244680c80160060f0031080c40490f01242500a50702c0d40310700290100c81ca006d17100c0c54025299005460f021790746030b10000366110599828054501400c0e0741c1c0c04841d0500c0714030b02181e40c80700100e880300910381640328005210b0362070800f0032038002c40d00402920b14140c0100070042c40400e8500800c40101c181a00c8a102103100100700c804130703040541c00c0d40307001801c91954555175000008840c19182ca48407844080b421511642d5906401140c804400d0051494064050140c03100d2203403007500184120f43c0424001009194400b42c0494245004d94a521050b1031180d0343c115856045000414a4010820302200950103020103450b05000a52156410007041c0880c2c0508a0304500d560810042030800c1d1001d410445d11130480300341c100011139415403030101c03c00e422103490100b40000b00b292050303601e01607000c1d10341c501d000e025610f03019004ca840079180d078000000c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 906864532 1250 906863282 906863311
    0x90807021008010e0a0924020301170a020120010b0909010c090b0c03030103020405040512030a0f05090d0f050306060403020640051003091506240c1401061d07030b090609 75
    0x1c010745070205840e07030303c2c07e4000d02000d4481e0202d00c3d00203410900464000e4071407280c40b07801642d40007a811030b00543c142d40d011600240c8003296422001800a102220764039050070a0096554200755840750308148000141c0c400a020010300c59100c42e0301c10881c104e410003902c80f04c00408030840f815071b601a2000305403600e441c0341c0b46182a8031409038100215010042c000344403134a030804c8009032480c210034003d03500c45618242d1208420142c0d00c0100f10729405400701d0307034042c0340030315840310b0014400350030103a130786d0045046540f000141c09800014202210107100d0143c1d901c4844140000000301034005121044040a030540103032440340164a061142c5135202e600150000d0f9402508042041c41d0746041d00302400740d42c0500e101111301c0b070819103209a854010410b8004403942e40100b003610329225030b00d10740006d4840210075500c2d0000400c582c042801d5082d40588038009180107440c1991006040b03502c8884954825402a8284607a903030310700c0b030100c0e00301e0b4907d5880354 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 906865782 1250 906864532 906864551
    0xc033b0303120c0c07170307110a0518061903080a1209081b060702030c03091302070501050708040c0914011503060e1815162001090807021008010e0a 66
    0x92841c040d1000b00402d030ba030040100940f4401c0180500b1095213944126070100b61204040042400b100c80700b072042d94014032900b0003089482c00320105032500501140607113600c900101c0d0091000100c1008280319140910030542000080707a42400c0c22001c50300035460035951015124401c1d0540e602c01c200d26441d0780a80c4c80021352240408550041000c2e80d1400c00343e00c0884128030201c0e6a407113034003415001039a0300b80048111759000e0a20b4010f50310386850fa904102e1034462460480400300c1d400e01400000070801d2003006e000c1c50154683e0304c814030b07061278002d4030180c3c590460300800e0308050768904921000d0088506484141a8500c00c1c5c020342a8104c00401e100d81c8811420704d124001d00040316010821100c0021005c000e903103038000000c1d1050741b403100039100d181205464455a01070349100301052214864a921345004101036500f003582529016102560f5490340028028110300e4030115403071000c032140c00c10642540c0340c0440ba009000c0e000b80300701c103032075140e44860 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 906867032 1250 906865782 906865789
    0x11060309210f03010e0105010201361e05010203390f160305090f030303010e010506090604090c08250c03030b1801030803060301050112150225030c033b 67
    0x1d901c440030b40c540d403a0b03e0390713074469554500100c00c0c41468055440c00d07403142a140c1e40c40f07500441c445031407100100c0c0348103c031100c00e4440b645d01e441035a5141c09003500d14606020020300240c80e0740114000760b01c03410007081c808500c209018609000070030410441410404107070241c115040802909502c440c1038142e44030030f43c40390785c02990859521a621344201500000075201c0800140e517410504030a01c1c09261713032407200780110405506000010801e40c64003400a064400e009071809041580e44c00c0038805a510741c104000100d04400f080101076504207560300d081850f040001518001511406403044c12022400f40825403030fa4944800c0d61076070070465003010035000289141d90b94908200300350340c0003501c102d4840d5081800004000c00d2001144a034250048101c42d011189084154000c0d40004000d240040030522040c94546240c0c0b00c05000328085d85410f0901040c62400600c550503500500315016012900b0303420901d50003204044042d01880d401c0741555148000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 906868282 1250 906867032 906867037
    0x170f070504120605041e02060f07140607020d02160e0601030c02010b12060604060801110f03090a0209070509090a150b13030506040f060506030118030c0327031106030921 75
    0x2000b0941c0c8a00004420004103a100078401d9005500040c0100018100303020010003c84020798400c20600c5840e80b000350040060a105104a110b4000018a1040c13941029411204a00982c100301c0c11408035136014068a41c110000540c0481c006045c8500c13400301107005400740c0d0416a031402c0404002d03001f50700403000392000134070884103103115031606076881d00d0464449000b10300b000070021328174030140101d5140400e06000c0340d00780b103207880c031450320b41d0002041c15000d0f208101c0120f0168403086255070064102e6170b01c00d50345840b4a000e006600d40043c102d5509186401c41024280c01c4000c448001d0700d41c4e004201c0c0c3d60303440e800b109105504d00e030f400151450003282e051008000c540410101e040f840790701d0a0056540f4007003058221504135207100415420403900c000080d00c0380c03420305032483c40b84c180024100001c40b420800710050407501c1561036820344082c8240081c0c1c0003181d260010488000b403030b501c1c02110341034039031054800440440300800d0036900e50b40f41c00b000703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 906869532 1250 906868282 906868289
    0x2503020a0518130f0606021e0601060f0302040b270d030f0c05070305060109021e0f090f0420031806060f150c0604051b010201090224070803090601060f170f070504 72
    0x1004e00160b0018810040101164441c1602501c100f568410444414104809041402c440038005031b80c80c2503000d07100104101d520300c0402d5420003000c10103050001c040d00a4104000b5810540c1d0f0380d1141c100f17440003402d40183d12a07102c2daa80640080d51218003030310740c4980c51900788840d890600d07010b40703881e0190700300a0580c040c0318004101d0071b07031a82c017a041151004081400300340c4c100001c6d412601c0342070020440c2c804100b105200c2418810111000c1c404083c0c800100c03001c5035400f01c030b24507801c4101380c2c840c0301c800000d0111401c0c980925086408503030300641158106078001804c007400200030903015807000c038144410240c1d58420b4400e040d100b84142c8215141c9490416181d60400707075a40083c40100300b029015510501c030388034405a02800181202c801150640391740b0030000000703170004000700103600000d040070b0003441c01000150010079180d4101500a0440c04482c84400c013000b9580c0b0581c0504070224107019004041c2914003500740d201c1020450301d5116541 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 906870782 1250 906869532 906869569
    0x2511010207060c02060f0c040504020310081f05010b120f061c121707080411041808090a0501020a0b070f020c100210050f130305212503020a0518 64
    0xe401c10500c44583c10401a0320400e5090340e03032950300e074060f40134407803810b84881654042c140302c14001c0e400d1640c0199000049040c84000c090b80d1b400c401884c00c0710411600741c101c10f5400882c00540b041d405460301420540f05024206115903500e8496100c004002c400c4e102082c1e004903001c1d4803812103c0c0c40c00440b915014003515401c0c03c12640c00740c1908284000103410386407641104076803401840c020251592030b01c0c220380b12511800140045034070070f16442540d8410300e0400d030352082543c500c003d00c110760392501ca400560800031070305010f0344400d0541d0011030103940060481d4801c260b000410341084540d050b43c2c400101e140540300440142c202d8049070180c1400e9400140d802d00381c046c41340d01404140d55401e0741801121007945d00228203004030f11f1500010307000c0c802402040c01c50310b18a0010b80f5900070540c0c00b000f4140c500500c8024507520714016260300e55000844420035050561030403003101c0f00100700f8807610514055816100c003520401e50707180e5810b10142d54030344 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 906872032 1250 906870782 906870787
    0x73809030111040806060f09040803063111031501051b070902190309050d11010b03030a0314070503010b031302060c0a03270e0c0309030c1516050325110102 69
    0x315640000d56105004e4407078148291000182d891601d03034800910404064400d4065440315580c00c8041c1e040a8138060748505003107051039040301481c0e01d1220401c07040042e0190142e5512548049500c500d0440c00c1021007003040080c1c0312640140080c03003040a2030402ea4858940142400d1410b400c00300c00414066a2000102210190060309a40c1054141d1509221650b03005070112640c1e032800a08581080409410b010301540459803000c01c0b0200102e5034200240000e411a402008060b01280d6602411503c140781c2c1840b243e40709886040492540d41007824105181c00010410f40c4030000d40350305103085450b0310f0709a641344141041111240f02081c036000d040d4501015000c001e0b0001481e1000c118400148034104a680300038169803141c03143c008080030307030f44000e00c2c002d00c0c3d01c41000302c50044041040b0488000000361400b8103641018218001c510b58151020010000184103100b50301c039968428558603010148000f06640c01c80400b079a003000040e12182d15540301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 906873282 1250 906872032 906872051
    0x31e03010302130902010207261213060206010609030f030519030504150b01050f0702030703141005013201030f020c0105041202011806230403030b01020738090301 72
    0x500a14140d9100b141e100a081007108550350490301c800b04041d0060307004601c01c04c00c009101c440705a0200c614219909d43d042c501c0000380c603148183c00e076000c3c5171000041050f01000041e80c0c0b10058882803020b40350720751502c0401420300b8080d000290a03000400c03c51000c0601520031101031064001d1a4803a05400101c068000c240456041c0c0d103a441c440310103400c0b0031452085104101c416108e03181070110320340484100ba02714442c100c0c0c00d807280f44000b0010030520341e0000880500703c0000c0c085180d0000d4a0400d0341e2040e8000d03860981c0000d01049119a140201803c00303141441d034040390556240120081c015a02003041c10510010f034507d4070140c103411081c461401400643c40e411054142242221420328102e000c4480d0a1070340c2001400507000f50f9222803190041d005d48203128004504c1c0803070161402c0300402e554200060301944c05200c46001000340003004441900561204100103441d90f9082d600089200c610030103000c142e4003500e005180c054005c0041540 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 906874532 1250 906873282 906873337
    0xa0b0a14061b0c1002010e210c03220602010c0e09040c09020a0e010306150c1e061b1b12030c260601141e1b06040302061605130608040503 61
    0x8594854060b050002c0c03018101401405001d11247c42e07a0001c001040e07400c010314164101307481441006550801c030300c04403084204064540d0008030040d164440700c2c00d109889a0b07450580c090750075641001d1100c3c1c9440d8002c0340340d4280340010f03a0615019a00c5182c403140a030610340102040e1403002c56071000960303028210303026000d001c0c0c0302088020340302c44003903860860540103d4001000c60400c4000140740f040384580b411712481e07a918450610341d940d078050314403000310703401401e07100822400400c0e4071903c0d00c000d90000112182001002d625580807011810b0b075038030309064484c3c0c00c021060384181c16084031000eaa1a46205807103407507081e0b19402c94141e40c410300003038040b4411100d800b4075200b02c03010040c0701007203040c2e0321a20103845416030b004408200904134001585200c964400c3c07042a105900c1380e809030282d0310b048a00110341c5c81104001c101000744c1400420091060a0300001c161545410720034002da8440c0782840c0f40d40f051480000700c040c00b05441c08003185 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 906875782 1250 906874532 906874543
    0x913031704031107080609070b0c101e0605090601020c0105210103061d12040612063809010503040b040215070305030a0b0105160b061c0311060a0b0a14061b 69
    0x20b0724200303844d03000e583d41c2c05150b990f02081e00c2c00c0b040b030380040d541000041c81200007401840409000c1e01c143ca00960a4142200d0041c046180c1c0e8030710003218404000c140344200c4001e800200c5020f82242080c0c80000d41c0d0300e003d10152030502030005801103a10303510b0500302440c0b40601c0c100e403005603140d16016026000c40340c2d2812180d141400128034440300030420b1850300721401d6609040c1072900c10304544070122081003080d055078813980480c40d0610000d420300782204407042450494406040104030a0103500d0400210505028518a40e80e0041c1100d81080e04052181c1041c0c455000003903c00d507521015165131040012840b04040c1c008001d144680d801510804c0140b55807001901d041c0f240050f21110008020903400018940ec0c40058201001600c50b0590000c6414020f6113980c0d0000254040354130700d45006000343c0300b000400c1d40b00034052010310581c2b4800c004107102840c18049d078040ca000c0050160100d80300c0c0c4003655641c0103030b40b08241c111020f8010711501d40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 906877032 1250 906875782 906875807
    0x1d12010902031b090703110d050c0720010e040b1c1b080a080307230a0e1504050a03080703020c180609070c0b010b1303020303040602160e0402091303170403 69
    0x9010b01c111412000300743c848a1044540c0280500d6569580c1000450007420058400e034040503041c4107807018200c7c1d5118442c0300b0780c2541e071629520441800d15206031032101a9401441101101c0b030919039038000304804038054141e03004992a5000d50000b01e1451028400e0856003100c3c070b102e8800d0045813000d0036100d10b00300d81203d88a581710303820a611541941c2e0060103d00c0100040707601144900c4d415100c1c1001c10400015510540035403d4107913210300c2c82d0760006000292980701d5446c0420750007a04040c030000305480c0625190100d106044284400344c03070b9145c08600d02c020b040c02445500c603c04002001100c0c1708603c140c3c400044c91041c1e07a01070082d040b040005150a010300c0130019400c1d00700d010b944d07250303282003410100ca6020161407420443d07001d10000058904202400180c0840d80250001c4c0040e941002402c48490b4000c01e04400d00d801480702581700d4020854100038100d00980f240c01ca00d08040c0d80702021407196100c100c0d1100200018982d001c1c270f410449 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 906878282 1250 906877032 906877039
    0x3060503010221010f05032d2505190909050a080706090b132613030b01050906031902061602091008011107031b060e030c010e0c010512071d12010902 66
    0x156625a2072040055505006d41c50309a171105000d041401d128140442001d1001d9803041c403a05120f650103030138600c0c203011443d0b280140e0354607003d02c04e100e0768508001e0442542c1003802c5042004914602e210940301d1800500d584006480034000240182c0d0034268101d00448e0b03070781d00d140c40e2010050045050645032a007182020800e208010103000f94590b4000318821884142000c0080182c01c40c4a42e82c80522010042178852400c0c459103440218010186240c0c25032408052013480b0b134004103014800d0304018814692060884a0b0410f03554054504030b840704c0a4441c00c1500d60030614000e94041186810010884040704044040d103200d903009200c20303003401102c0300ca28000d0407001404240040154425141c08524001c09540540b030045140718900c580c2c0707401c551281d1350442c0c46035107a000440741d00404020a0300014000c2c42c183c0c1c9802c0030030854112001015089008019040301400b81a804010008820700d00007001d400f620a460816540200180c4504030700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 906879532 1250 906878282 906878347
    0xb0105010509130b01110d0914010509031c030b04090b040c0e0606090d391d010605130503030d092018070504030605070908060f090319030605030102 66
    0x649500c100705a41c20000d0140c54008091605002d19000d440d1440109041000102400c00d4000d030400c00110840810f4488140d83c90a009444111b049400d0745a414844108202e2146440004442c692202c05030b09021114101c0c0f201100030b029a078501c16801810407030301000703126064405600403803080046154a56440448100b0320004030703007059000c401408005800d0520b10488500c01e840740ea034a24515640c5070285034030011010b0704010f010324100d40d0040d40464807076844043c0440b0040401e00e54083c99010341c0381403050140604104020a0501201c11b141031000080c010040a90f902d030110b4851403030042420718810350390120074405c1840c21100011120051302005080100780044007000b0703254404000d0b02801c10000c04000010102d1414403c80340200d5642e6214200c46117090405440d000c801f80241d132254003202c0a11244c050008201d034001070362840800d115200341d4206400401641d0f108a4040d400050440f5009120030342503441d101222201c0c40303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 906880782 1250 906879532 906879539
    0x91603140d031512020d06060b0715090503040911120403020606040f021c0510080d0302071101110d08060105040e0a150e1918061409061305071203020f060705070b01 73
    0x406480c4540482c00d5446032880c0c013844080c41d803a0a4091450004d885074a4182580c0d40e07100c11130705e540d07000c2c0b11199004560b01041008181001580039600300c41480300713001a85595869110318400c0c00505a514800300840300c103040c0588040c00030303000340030a5a250504000c0d44490b011110b8510481c61305100764040c1e46144241c034119260f1b9404c00e0301e11101c1e101500010840a000501c000440c004001054041000700311035191343d0380e07009a00caa00c1c61601f0303910541c141601a042c0b0050041d01140c0d44e0001a100085000034504a16991556401070303546204036001111050085001c10102220340d801134144101003039004d6000564a412a60a481003030344c085043c024110108041103c0741e0308566401c0b9801996006450340d40c3d9103034400c4130112900254450345d5002041020b030010312120368003803001065641503c0660b41e9903034440d4020b010780e40607401100b281c281454800c00034040303823105040454159060225000d451900f11020032a00840c5540010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 906882032 1250 906880782 906880787
    0x6081b030f0a08040e0c071209060909060e190e0f1606081014012d030f05090a060915060308190207270923010e030a08060108091603140d 61
    0xa110b50740240207035082c1801c2c0034420b0354401000c1c1071102c03156030034003551000c510148405004103c481d101d5550603031404a010344802141d911896a541c6401d208001d210100c9900c0740e806003070070b9081240358180ea42c02600804455004106030b00ca06c541c94000448005000180500e04110740010079685120807105443c0854078590025124002041801011000108a850f050400092420074428201555000f5507010102c640044441010441d01131141100384e800f8101c060100385013544100f60b4444402e10024060756403901d105041c000f02a40d422034000600d003050005a0f034a09101e40182c100034444d000d0442c4003811509110300010301141150b039520080c0160a070320304444684240e003180c0c0d4000c50b945407a0f0500011b03943e89510301c0c942000198400c404c0203042003607402c48001610740c1c6550750003040400c212642043d0b103e94003804c24a8034050369030314003031000c0c10715030b0b9001c44d2049a6070b070706004410005805000c641d0303444103000b100c2494010503400c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 906883282 1250 906882032 906882043
    0x6190c1205060a030b18060a1a091e041a0907030c14130504060c110102091c14120c011103090a110d1a0a05130c030210090f0b040801050f0403091806081b030f 70
    0x4020040200c2918072702c40e00f4007600080c1d0010b0303000c00c03040c1c00c032104c1040c11400c1e000c101c80480d0700c0b10074540c1410005240c61001a04108204010081c1d54150b603117000d0038100d68024840c0c0e1015014050045590f041c48000781c9106154040c001c9003003600c1e0400c0540041c3c4441800f00da10800c0c4104880030500c26038030310400040814690842080c051070306002c9402050b00c0c1980041481160074904020044074441201c48441e65503425560040c21141210140b501d0340c001003041c402031050008080c1c5801c7d412001401d000380480d000103105041c8518000e0442c81d01c95440405007100340961840b40351588c0007403205030b44101d442e076815444214002c1106c0f02169090001d1308101a0715a035801c11800c0c030301000ca456503119115103d10354010201c111000405100602c0c0c2809550b400c04c041450280540c1880e030740240803030302540255103240401d48041361489415400110084c45c218050f1480c0c841c425508415080c0c06d802541c1c001e1003040c1a030380f41020300090 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 906884532 1250 906883282 906883301
    0x50c06070f0609060e0a0309060909090309170321011805040807030804020406091107050d020706120b03030d0204120b100b0906031003020306070206190c1205060a030b18060a 77
    0x4815440803940e541d07140145180f142c01e4030455aa00101140c60320100200380b8014000e44644144070b180c482d00030000701c402e07004280018244107003400041d411156850a0700e181f00e41d9a61981c6d0b01c040b10700d05e98001c40c0e0045003034103028501e10719007101c100c0c080f40c147c03042868401c440e10103480c0c081c0d040e220142c400400700001040004c011911070282d1a80240c4010008212659504040700c140c07050b0fa22105204000000c0060402c9000c0150811400007400900035140c9072107400b0f05141e5507a44801e401d6070321101e09201e2643c0c06c1c800c81d010a5981002191219242c4417148640303101000f0464040d950440442c805d10b4070340e803128084985210805207021054020301115070409050201184c0d08018084010b80c1c0c180409031080141c2c0c3e00400c41e030314000c240002d00c3d259901c141e000007442c100d50400b00070360080b584035000140100c00714168030340002084541a02e58805407800c14010240103e0b015030616225545070803804807681c0782c443d800103d044416011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 906885782 1250 906884532 906884543
    0x2120a0516030314090304140f03070b0703050c0304170d020f0322030c03060c0906170708282013120c0e04060c30020f090301060f03050c0607 63
    0x301d489081021407a030814480e100349000303e6500c0341038400314400e442c140c43c070b03171103075040850203020008200240052481003240c41100c2415444040307920380b4070a000e1281ca0440003e080c1341810b0240d0104c400c20021002100ea64580d42c00303619490111000088a481c0900d403070b6240341910015a0180c00403001000e5031420180f07100d0040401c110401101d101cbc0c80114001011813040410500114022440490011003130030b4002d10645181d08100148058284028109007025074041d900c00c10340e0074070074540e03101e0803c400520322402400b00e01580c0d02c80079150343e4504a4000310b0060201c40044102c40044200c1e0350381c54000c8552140082c8040e9008101314a070340103a402585000d600d0161010740c0301c10141ca01c200040b541034600320740710030b0540185c5600005c0300c14503400f211003851511140d01c5186c411070840603001010380e42c01042e00001c105502c81100c124181c0207008016055440740824030079035903031105482d940103200a04d03c0d1400c0c29011900d590b40e100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 906887032 1250 906885782 906885787
    0x6140d0b010504050601020a0219060306080f0304050f01030f09050f010518031c060b030f0105030c090105010e0909121b071215020a0e06160c1707170f070f0602120a05 74
    0x142c140401410b0041c82d09045205081084001d6110170901200740420f66004110340780c10300700050265440e41c1e10090540d03112489000015002005482c00e40d142269603405442140004030301500309403a119080ca4a0008100e0401000040740c0c1d20780100100240700c0caa0314412000710820080000300030355042000301940501000d03074000c0ca4140c8903507000940356203480ca0740300c2d1a002150f02030080d00f100c0d001400980b80410090300d9045045880081e5503050400007080300660481d0503005001d40e50115003040c0c01400143d411902d1400020f88844086d4040d071a0004801c0b801c3c40d040c0641314012980071113050354500d80715001580030744111381050402c00203521100510007000802c4196401d01d40d02d01e401882251103440103074811100c18108581d1b000c0c2a07a00074540c2ca40c580c0303c240505d90307021403d001143c0c0d2000001e05030241464001d810140c1c1282c0c602800d0080e00703000f00c3ca408210a65100350341f4503a085075822489228400001d100322900b100c04142d05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 906888282 1250 906887032 906887039
    0x50c0c010507060e0f030d11090609042a050d06080a0b06010f0909050703020a03240b0d181b21080a020a0c0e071706090c070317040606140d0b01 64
    0x10401440b001d841030b8000101c4803440c0c8002c03414050043c40942585e080001e0050b81000f00d40240701c174881c50600c016241600e0f40d00010000c2c8101405140160703240c0e2804c419100ca21003030140c55880049015043c6040c1c800010100c0c5d02c8145410b98840c6002e00c040f880000000d038120b00c0c07551001c039103807003511040c00641d22103100071400400c00040c50404250b81000d401218000c2c80c0c01d4030050780f69280c495015060b11040c0d04040d072500040c1c150140000c0d0008001030454040001031030f9a2040034021001400c4a2070440030034440c600c02000401125001ca4a110f0f200c07208039141d240e031141c9151100031040501014050f40d04540c0b800841c107600004c00300d83e0a54012148008103599400401c0641680460b104402e01010864140e4025410b00c0c2c4040040244015614010000400189000c1c0c010400742401044041c00c040c0180304241d080c2d0701d04d91808000349007038503216001d08414060340c2a0189030010329191424404c004011035984042d080449030708 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 906889532 1250 906888282 906888287
    0x50a0c052109270622240b1303030e040f05040c0312170a0209040b030a05011a010528140d0501150c0302030a0c05072303010b010f02070e04080d0203010603020d0c050c0c01 76
    0x810600845c0940e0b1150801d1070201ea10704c55402c8150100c00c5455481540c2504495190207940c06544071081c100070780c04c50800f1182e40041520b07894201024454440310104004180300900c1d107034064508010710092143d01c151701302c2260300c1800ca801c441d05007100125503001c01940381001101c900e00200ea0810400d802401000c1d40c040c0c40050660700c4440042e00e860f01e03000007504c503a5543c5a101080801d4140314080065013807c0c0a807400035808440b114040d021140d6200f69041b40e00740c0c4d000d0b180b24100040000440403803071500d030000100034500420081c4038200290342c4102150102d540908002006541c26030040c5042c4481c000d019121064651002c40301d40c0100700b00810350780c44c003d01850b40e1400c6980c1c2001002e80c140c00341800c4440c00780825060000000251806940c009143ea083d40d400c01c1040510741c80d603103003860039801181c0c0c1c0005024001700020942da0743c15409011400800c45c01402040c0d00e409040d00c8a00c90b03500182019040707800c0c40c884550 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 906890782 1250 906889532 906889549
    0x3020702130203070c0b0105012f10020f040f080106051815060a0215010b040f18090215070302251a13030b010302090f07050a0c0521092706 62
    0x14000742800c0c405408050205080342d2085860320b000ca02c03204140814000300f81c0e00507000d44400c0c2441c1c2c082c100f05818410180007299070810700c0ea800c11050384590041407181082c011407810301551079511074100c00000d9081030054001d0508106070014a10405010700011038402400d01c00c000f524217455104089070050002074540d507500d400b40b075562102001040c020150703901903e0407420500328421684410792006442540c01d00c828010500c0c511030050840d2901c10761050310000c174095680c040c08880380d01a50040c004800c0704100000b100003030400070300c00d40c250384485032010040b0a11401004001511005100090091648140d40d140c09081106c00c0b071403d00390086038003082642c05820459005280c480100114140f1000182c0c01000c144001e40c45854456402005402481c14450411000d04045002d01000744110403050700001b42d10110400198511907403540800d0a0501070300080c44840118025605240000c680c03000140209440d01000c028001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 906892032 1250 906890782 906890797
    0x612122c0d020118060306140904020f060c0a0c0b0a03050f2505070606092a0c02090601050c0615130903141809070f030c0905010f1107170304080c030c01050301060302 74
    0x500c0607014241300c840d076030710000400060f074000c1851030801c500c3c3c2a4130008031a01d580a04215028400180c2e42c0c0b519035100740c0400e4848945070004046514503080c5541d002074406d400c0110702203803a1541d40020906103626840603c0b040d11b0344400070201260031145000c005031414401c802e4a201c00030050a0303d880d51500c64186451034a80364100c452641c8505200d9940d9560301c018004030528100c081d0303001c420004403007084100050080781c011403000707201c0c10503a800141e540e0300941c2034500f030382c6000040764002d1908030001031287d00140056840b41d02d114100510301e043c00e0007140d482c103038540c1d00d0029030500b1640d00d916941180042e042030403201000e215050300d0755200c0510500e03450ba0313880883c42440c040502180c0340700c1e60304c508100380302c8000d029a036013042c224051101c907441c041e080407004074181420311200d904240d190100c03a42e07111701840300c004007a00a80c0c51140540f544d644507403082594560320040160301140c000e100400c02c0c2c501980c06007100c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 906893282 1250 906892032 906892037
    0x80f180d0305090c060c010915020906190201020417100605030627070306140709060c02090106111e0109030e030312010e18030301060c140c06030c07060612122c0d0201 74
    0x2203004c0380019055080b0400604032030303564885107401e1103840b1445508072403419404514002401010403414481c641c81400c003804201d10340400141f00b54125030040018003014412802c0c40071449881d460884511b0282c64240100883c8511780444c00741e0268400400305440103400240710005988408500c02290140ca6000400700e00c15010711b40010b8840080d551031480e0058000d404003820343c021400b0070411030a004016140c85504905490f020706211481460440070240382010440401040c0c503690207002c80c1c2d20708150028800703284a81c695208904000017819640e001748681b01085404200040106403101c02d01ca43c0c0113046503044140241c400c4035594031b154001c0c1d00c40d40005645055901c11701c44503102035250342d0b064030085c24590346c106000441a02000d8016a1121800a084001c05c140d035070008000b4403030380701700e20000c01c20b506084842144480d035450100e1281c13240d0904800310140c94a581460104500941c032414600344680d50a460340700720705 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 906894532 1250 906893282 906893293
    0x5010f030f14010e0906012c040f481412010204030c090f09031d0109050a090e0610060c080f0d050a06061b03091208090a06080f180d030509 62
    0x10030102ca03462540c080c04940051040714200418902c0c64000164409403981600d0208034144c0c008103042d26000229035800b9801c070b40c40d43e040a85040ca884c203030050a04420b804d600c00c00241c00131500c180c001d1007612030f041e0701d40c90114101e4000c020141c400f101e44c1600c6020310038884c01c1c6d01e03550581e44c0040c00c00c510755490b81c61030b107089030310580040d1000c3c1d2600c0c80410240805004446802d500c0e04030a012902c078550703011b040000312101d011a110102c425140646c1d20598048005040c02400d0403841d50340e0f010040000c100c6403014607414041c49002a483d8440303c00c0c194100c40c43c607565402d0311752560326800d03a41d400099828000040800400501000354000c442c02103da400d400100d00c0d1030070304050404155294410b00f640583c0310b8440200c1e4015640c00229940080028060040d070702c1c0c800c21510602d108140d11800c100004210258007a10551045080b1280034025850707115800301c1050052010f104241c0c002d0444002c06803280d003056130841c0140c2c0440b071 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 906895782 1250 906894532 906894551
    0x11d1803160f0204150305030a08090f0a0305030f100f06110102070609060e160f0506070c0506131d1005010e031006060c030210020c03220312032405010f030f 70
    0x2180805000082d100b041040c5415000e51403d03200341411205480102200b9518503503da40c0c50380a001400070a100c051030010368074407428400c1410480910b8255401d654080c0380140043e00b0907900e40b8600018100019001d00b00380220005039022685810780d510f03e4032004841c01e40c2c0769004001c2c10354003032003c100014494041c0c244428401d80003c1940312900c886d080c0381a03402001e604aa01c0c0444c030401510b070400320810305030b4905070342040e40e40c245400c180f0003526596001c19041040050a1404001e444400c0000c2d0740e07000e9808000021003c58000d00d40307006a8000710040d040c0e041c00c000540c007480301044241c0000e02560340142c1d1034140c0704111041903001d4000f2070b040d00001400c050741070188280000b0311032011824110b034645030702c5c1d40707018554041d0440c0400d10310003da002043c0c00b11000859101d40140c902e55408207000300a030144450a26145000040000003204015143c4054801c180d461030004104c103c0d04401074142e1445000c0d140755075150700e5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 906897032 1250 906895782 906895807
    0x1a150702041d0c031c0c03051c0c260a0906090c0603020a0e0306040506070806060f03240103330e01091505011106400b011d1803 57
    0x140c2c8450041070320200d031100780d0324210f400c210881c810036200e42c2000304400301442e600840484031000e2450515040b400301c1c03070b00f070f10707180b04a120200301c83c00c15980000f4440126040030342c80009554401043c500d00c010313105c1d801c0352280404203000c07403183c0c0001c501020561000e00214018440465814410f488120fa460130344d170400b0300007a80018006804a40010030f65403401001d40c0108007624007600c40c00e4803840007a226104100c0803202158540c0c5c0c03003000f41c901c2c00712003000c02542e80c10000d1240c07040f064081114000081510002d0aa540c02803040c2076548083c051000000e104c0250b1f80e50380070008180d800030810440c01c001c1121b010554185010300ba030f61100003542400500c400b00d45e01c01540c032372410020503a00d0000c1d12100405c040c1c0d00416a1451400c2c8084076450304200c5210107010311188440040d48004803102e141003480b2440c3c080c508080721030742c0759048201021009166449540e592402183d00f000c0d001300030800107c6d9610030f980c24a402405003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 906898282 1250 906897032 906897041
    0x2d0d0b060f07060b01030b0d1505061210050718080319020f01020a0302032e03082805030601030c0e01050a1b05030417070e010303120903112e1a15070204 68
    0x9403203d80ea500d00340304455030140b0070321200301d20450b40c00c0d881c4410751b5540c00c074419461200310300183d00c80c00131895944820048a40e008403034000c1da00301e500100110401003100311880b00001e0807042c40c101e0b40001d006c0180f01035802c040040d51603d00c2d4104c82c135001441c18421102144540315454010407400e00c090921403582d80e801607a2402c000e43e0040f0311000700121140140c80c05114030564040360030704603044030361212040340c8451494103889100c1e41046002da100301e90900c0d1108500e40e00400462094509881c10020048580f00c111602241000c0c500d000c5041084034414050013080303400300340c00c5419100c0401e10303550703a107542c1140c000b60300540d076240001e800c40704100014000480640307031490300818036601d1030310000c104001068402c0030850b6038115010901d0b02c524400c810b420304a40c1180d010700d284a03429103100329261b00c2c00404a107401850500c1b41003600034095900b044101d000d040801c1c0d0130400c00007071143c00300329128040420482d00161501e014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 906899532 1250 906898282 906898297
    0x4140a0804080c090615071e02040207060903031a0a050f04060b04170d050306011407050114042f100503101707030606090504031718060c2d0d0b060f 66
    0x20303100307881e0f1000911080e1000079100a100382c86908201d10210386031029941340681000300602e96440d180d140d0303081c44030786102c041c0d0482d00000b0070f0020f01450760411072031284259000c0140c44981d02540c60904140648180d00150f41c4004101910380001da920004100501c0002c005030707244289080d036481948204030100540e075420003001014003420400c0710060030120300d503141040c0024190342c49c0001d0013a044d0700110f200d00c2800707003d50203075062144030051420039007000d040040d480d00c6d02041c0201c81401801c4005202301c541007000d013000030040c00110031002c11000581e0207400013400a01240010840011100780e8062070384003184116000d407401390304605020090740c0d01d9030840006a0b05100600000075803005041a0600c44031100c60540e40300c002003042024100d04044017180b25060078810007000301001010407000c0c0c2c243c80064580d03040840c81d80c02c40d048140110243c3c00340030110564045420078540c0c54001000307140740640c01200c02000c0e410054 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 906900782 1250 906899532 906899549
    0x203060a0e270105060f010203040612020d0b030d020a02040f09030e040f0e19060c0509030a02040e0c03070605190c0f0609030905120d0207051507021c0c080a03080f0f04140a0804 79
    0x405011080c10b1070007006c0e00c0d640003071028628042c100303103014203041c01c07070b60f0425410b0341d0020b0300b0484503400d81d010514002004041d286c5c06098440700a6440310700940991280b0714002701203820820600c243e03255154191661103228036000b003048014100641d4580100f500c90b802205189018044c1f01c0d00d280368481001c00030102c6c4e04010044504270b503d0f03001404410022200103503000550f120307900783c0c1280c003ca60214099009410000304010a5805100d240d00102e0581d812001902401c5003416514140ca18803550031955500d85180240a00320f01c3c03003494000c5543d54000740d0a450090903c012601c0d6504040380c0ca40ea1600700d0300083e90492034401c000c440e8140f000d80c0040800b2651020f9031410781103420610f210711b200c001c0c46606541400c1c00642202d200f1400e0b9290800c80d00b590166417030802540310361b20034600318000380361003002407101d40203030365207900801d1900b000c82c0c0c80b1382d03e44d5a00c40341c0034945401c01000c0e2042140303010005403484004c10141c214103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 906902032 1250 906900782 906900791
    0xf040504030c05011103040f0f0510050114011e0c022103030403030b0112091e110303210a0c1407080d0906021306090e0f0601180b03060a0501030203060a0e2701 71
    0x282403c5003110001e51141c96840010001d02c008a12424410340042e038200a440e6110038151820510b85035111900d401c00d5400d1070000034620181ca0004030302c2010a0300c81400300c0e13181d481d61001a00c1c1c2040c906010800c0d400301c8038090300305468000d0b81903011000b0380b0366500000040500e550000c88044000a45030109125103503405022112040c030b085405101c1c0101c103644032401c00644c0c403070070100841c0d49400380041c8161441d81c0140a41f011302901c0c0e9a40c43d5840407100e080752900b014881030242d10110303c2c0200903114118000307842d9030340d940c504080103800e00d40b5544101000d455508003030010003140460b9104004640303209403001603441c06d20303901030410701a450b0321000c1800340040f42000030303034981400749500c48400003002c1c15942e141c0e40141c0b94111840341903904041d4072400400d21180b42c9008502038036049031045045991000118144d03c800c60701160071078400c070410003104100190f41600705000300c00c1c059030900000d5105041440c0591030220b036030b466 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 906903282 1250 906902032 906902057
    0xf090b040e0616050d02070c0315050c0c0d05090109031208090d050f0702061308031b120304050a0f06181505011a04031209090c03050a0501050301150e060f04050403 73
    0x392107480005001e0901030001403a0038200300d8604109200d418082c860300003005100c06069a0480320310340c0d402105151969103d0411204e02da030b620808601d02803078200841c00c000d103010284c40710051080000d0041c41c06121040301d281d0001520981800403032500480010b40e03000282c80440c034a65200800d615014490510740320709088a00b007402010001c8486000714441220001d54050750340d955038990001015580100701e60240300709010120310100761644200103821036041c9241100c40b0b50100d032a66100900c0309640042c51a4443c1d2404e0b000a9001044074029901464001680b0800d0800c5e0303540c80011342e001181c004030411642100c00c0900e2044602410b9002980b0809004c1c0d01120701d071922640c000604940348041c01c0d0300b00a03216452308005008001401d100000d0b4290016001c0c1070300b50340d44001c0d603007040d0011419060500c24402e084550030300312000c1c54506400070081450150400c2e42201da8901072401544541c05403500451007070343ca4040e0b0109 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 906904532 1250 906903282 906903289
    0x3060c1d040606020a06111b0d0e03060f0a1a100e0a090b2404081504020108250e0303040506120415060b18120d03150509010b0a0e06040f090b 63
    0x2005904a00c81ca01e04441800002c1c0e0005000340680c0d400200090791880040445100d405000700911115001e1f03649203070980d401003400c004080702da440d0450f03444807900401d81c41c2c450845960201c5071745403000a1350350019070401d15a0780040b86a00407001b0a400210f03c00740e102c20455004180e0351860380401d800c00000c1c07140104000142000031840c8403002075034141490134104500d03580301082100125141c0c040f034006100d03040883d0318210260480c01c070460400c586c240d000c209484000fa00311a460f900013003281c039100032040d005901c041070a54410442008050301032005000211700d0361036200c001d04c0d003030400102500c0203191900e0032403052402c1c9265800500d041035001c1101e4402c0b00140c9518442c0c10300d082d14005c1c0900302080e081c0c42556103a1b42248104400c050850790164404110040308000c403d40c1e01c2d89440510403241020301c904500c20604101e030181843c40b0f882910800d01005003164a0907039110850b503401c0340250480282181c0e42c50b0641031915 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 906905782 1250 906904532 906904577
    0x120f070c021e0a0f08060703020a02031c0506090f0f060603130f060203010f150e041e14040308070309021e0303090d0501050906100b090d08040503010609050627041b03060c 76
    0x120740182034031340c1381410702081d141c0f01d003d448801410f8000c650f400c529402402610b42c10070016100d1075054405441c2c00015200076034030036014210f52404260002c40d904c0855100341803c4c40615010340b1003000303001c51684002c0c04541c1006c4100041c4000940020490652502500b0090780325410031078800c0b5402e078035a0000401a030080130310104290000074100901d5400c40307001a101c0c60040507005494100020003141da403070040c070700c58a40c00c0c61700040d00a07402540c80070410365030803200358104e40c14a40c02a41c400180024249444040e1014070107040340542901c0c28060881c005c114024515a011136031a51140e017082129901040034580c4004d40310744031884546041d0b0100224443c01040b94000c201580d5030300c0c1031000c000225070040c14090000c12060b60749420000c01040251001341c410103080c421458001c5a5052480030000680503480454855640d81c2e4280451400045200469942d002000c14440d110782011444c064030303003042e03400d00c582c00000c246 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 906907032 1250 906905782 906905789
    0x1e0c15071a040c0b0310090603050d140306060d0902150703080103173103051903090909021c1103030a171021020f040c031d03120f070c021e0a 63
    0x803400e5000704804507007000700060456000c00090b41c0d17603858045400035025007517000b10704107070300380303040003041000c0094a13201c440b000e179492001286a40d141d014643c4019500740b83c2c4403e0610400e120303401d940d4003800303045d84001c0403007840410a030072285007034024980a03004549600010000c0c045000708043c00d881d00c0e140c000e4030b042d006c0034207142d114031844901c064041c1e4400e01100442d030390081c00e80145821104981e000a0889204481031003409011800500d40c10300c001000340c41800380641c03443d4010300f0640403003078810307035042d41c0c1c58203207402c0d00c503034041d05601d0f10961070030310040c58030904940d1403040401111000105420003d03102040080400204005141d00903200840441d1718000d40c10180c036250000032000c030102c0c41d0140c3e12034a0035000c100041e4050340807610b002007000780b81070701045400c082a1a0b0040030f250036024003102d4009500700c81c111500315030010940c2045507609081e60086002c000c855038812001c4208060115054070381409808002c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 906908282 1250 906907032 906907073
    0x115030605030303070f0201090b010b0a021002250c030b0a020901030c020a050c04150b040f05090903041202090a0906090507032d0212031b010f0c09081e0c1507 71
    0xe454580403d940c2d1200178091401c00c555401d9401c0c0640c0300390861014150081032861072561940c0c080c00302c2d42d0041a031480075100700d200d01d8400c40074a00903641510424200420030407851501032459001c0d0810484021841840201c000b4007001440307401407448280040e101c401500024044074a40076650003954400b12100c1d00181c00010140d00040003920f010036071460b22a07420002c0c90303198010701100d043c0030401241420102210004031481164188826110b01c504540c8900c0340380220080424580d24140150078035070005a081440000c0005c2c403a4120788429040380c1c4000d40407541900f14a40070010f104034050421800480541013540a00031790912a46140c440c1e0002030280f20038940482c00d070030007802a1001d803031400010401030319201c56010700800c020300004111504e043c0c0030585941c840c000c01800e5404060042c0807142c1c1c10a928500e0030128052400c8600c2414020302d0951903001000e40300d00c07160f0742a552a4086031400c030103c0b40000c2e079a82e40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 906909532 1250 906908282 906908291
    0x1302040801061d0a0b04020f0c0a120c0302030703081302040905010515061813020d0903020a0506070f0f120f06090207020a05100e09090a0c0b0d0516050a1103090315011503 76
    0x281d0303140400300a50413901026000850420b1480072030060700071401c44200280020800d07102002c008680709442500c210a211300104100c00155014004d0510150050348203000d0180020f01400005801800070300d88200da496280c0d000505a82070354a04403040d035191070602207004450700754480000b5044908600b40041c03001800c00410820714280c0c4100d80000b8006c1c06101181c1c110358504040850900198407207040203550394076113503021215071154600240c40540b00d61030045001a080d555520b0002456104640080310303405020009961400c42420100ca14030a43c401031042020140e10f80340c01d40100f00201c4402d40c401401202211010700800342d01140e002040001101c02801c15141e075503086e45815180403004002c08010240031030600d1044001d06040305142d01d0902c40b0b41c0d98079503400365044013a520000458024050449124050080e1100c0040e80c44104c1c0d0622000c40002440e04600c250024030040c1c811006000c03a0700d40d003c0342d074200c07402800d0030302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 906910782 1250 906909532 906909569
    0x507061b020c041505060d0b03060a020f16050f06070f0306090b0603130c12030801170a03090509060415120c0807081207020f09040506090615011b030e130204080106 73
    0x3901c50603842c0c1d14511aa0381e4082100020798a100c40002a01c80905000c2d00d49880c006c050004203035442c2054820700c01d4a000452104240c001c44074008071401e2902d080041411403003a0820316140225514050310f007440c9456041000817134030808103642c88000346007450501030b00300e0381c2300d070003c40317605041c50001e655584400045070703004012003200781d2504801c1c0c20540050800b41e0028003280c81007070480014998000070fa2030590703c150340ea22544007915548203683d5581e0020050105174840e0701009030f0310300300504a6000b40701810100345050159041d1846a03d942c21103004071a03081c9042e001d101d5000000c0d4041d080c0b4038000c0013107e0800300e14642e58100300d0384d039500d2070034001204802c5481b2030303d0f41d02d46a0805440d500c65030425103412a00c0700c004a505074610b100301d0703000270f1070356411842d0b983e800300060b11050140e00345100c8030f000080c00024203070240400c0da5070f1141a910340303017680b500d0001181c200607200c80c00d0100d01c900351a00ca90091803017010300c0b00b41e40e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 906912032 1250 906910782 906910787
    0x60a0605090612120a0c02060f031f120b0406110403051606090303080114040209092a04050a09020d02071a01170624040b1903110904120c051c0507061b 67
    0x245146440741c566074881e8803040041ba600b401c8480000d4010320045001e4182c506494084c41c06074002c0081880c0041a8103e003030b580d16554480d000a000c038000c1c00e000400c00c2c1820340c030380080c0100000f00c0d0707481d520010034080d944079074403c946a82c445450703002e0350302408411030054891490280045031450318000c12154041c054802d0100c0a50000c0c5c0144c5d94070b5040743c104500140c04140e807443c01454030b240c03400c03000078820095903d00038003c18130200e500855040e9000100300c18445c070708046600d0000c1d00180350280041d03500304109c00114003803080c603215103050302c0e40b05c1e089903060040446d0202c0d640d0a800f10540e02400c107010044250805901c007851004500c00d04454107980060040c0c01041506508180680000d14030590701c0c03130208087c2c03409001c0d140d484030013110a100d48580f0446000e02061a40d0040d6403605210b101c48100a070702401c111502e50901d40001ea880716160b20711714020900000d2542d04006140c041c03107503d40b8007482c4042c00d96040ca1400b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 906913282 1250 906912032 906912043
    0x260a020102070e090c0a030602030f0a060312200114070f020d1e05130602011b020a05030d0209150301060e0a1203091a270a1e091d060a0605090612 65
    0x5a0740c00281c004000b801c24281004451203175980100240105543c900b0f04070029401906c07e04c181d0104040042d4160540303005510499520a0307000d0401c20502908030f50041d0300300d948030032200d003100a140a400f8240103020050401404103a1a030428940290074030320902094402d40d046100c031000f0303070f9070030604121b06004c1d40b10340042e003004410004c130b0b4117108841c4c5518403000d41030804070340b00340d05600c0380c180c03107008100a691106c640c2c402a40d0f2003000d0000100b00b64002c0004e407800e241107402400c0da07a00d003d010f4019000d001c1c4c030612a40c0c1c009810030700014218007240707051072034460901c1000300220028076101c442e0719180240002ca441c06403030aa20403d140b5a200c911120003111420b020342055a00303c09904041d8604519103140c80b03030700c5000c040c000820305c80704240170540a00311020340400041c0c03030418007034090a88801110104c40400a000551500034440075104511a000003e4507504020401c00c0406010301568094451030204000c1c06c60002003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 906914532 1250 906913282 906913289
    0x307060f09060c081006050c0309040b01030207050a151d0a0b04030905030106260106080a0f020d02090a0e07080c0609040b190b0a02060702030a0527060301260a02010207 75
    0x404552030400021420103071045000c0200501d1410012004165000103040d004629403100700380d0040d40e03014200c56070b020b1158007000ca50010003484050746456401803d01100604016013032007480d88910b800d00c88401801c1d1150656690074240020702446440510007004000c0011041c0c13090304196075401c403840c02020340b2103c00204081c1070207100d4030802400014000c0c001c107030b01d50f1030610600ca55549449062400a01d0403900e81c40c040c06102c0580700346500505e000721a5440c0c51112205400050342c02c094100380175000360310342c0003901d8400c031511003012030755107d01d44c0842c3c13a00c020342d03210381c1ca150082100321b201c0d6a5124101c403000c410481d030102e9440c99a00000301610641350b6010140100468001140780e405009424002c15030b4082d50042d83c0c0c0e00344c0980c2c403803290b00f8800001803410880e840802c0c03214890f550035404104050150601c400c008074034590700070b0700003881190039003441c2802600c06000214501104030301401e4960380350340c0041c2da0341d0b2680c00b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 906915782 1250 906914532 906914543
    0x803040f140a05010e121b160b0406023313120207050306310f082a0d0504140f03061e1609050607110a030303060920041203050f1c0605060313112e030c0804050307 72
    0x18080b51000703b0f8040c0409a07581c00c403011194007051143d0180d540c040512515020f40902130014800b4460f030500007021540305412a0b0003e00070120010760441840740448a4810510380c0b80c2c0403818a101610046049902140311b070b4600d180400942000d030421500c899112180b01d00c0000c2d0b1240544080701e08100914011540100004034600c5d260320000740c25102c0c440c1000a11401c9020f1003a41c0c407889503995206881d48a03c88950003c06c440d40004900640030030405400c003400145030850042d0003441007400d1060000d00300740000d0384103400090301ca80b0305112a050301e00c10550120b1107801c090501704961810f0302c1312402644540b807800e400d000c500c841854010b0044540384490140c00b44d9035654040d03403000c0c0003028840700d0240f0341d00d0540c0120f210f0410b413003140e0007001c0d2514030724411895a580c0c0e82203101e1303210080c1d4101070075401006101e5614070b0040d502c914000340c10445014040401030480761100e0751001003089140911003ca64003000301c0750f1068202 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 906917032 1250 906915782 906915883
    0x4020705070612020d0f09060e031e0702010c060e0d02071d0604021810110115080309090402030c27100f030803040f140a05010e121b160b040602 64
    0x303c01100090240c0000054024181a84642014801d5008106140c4038000400000c0c8005c0070080c0d590103025144606d03002400010046001e04401803c03d403841403401d00405082c9645101c169081c40801d00c030303103a0082104842c40c81d0184645c80140801c0080ea40070040410810210203002801d154051030740040d0406d0326003c2000b4154031000302802003040c050404000500c220139250a81185519103486480c5000c0310000031022280180025801c3c20069010170244c0140604220391600c0b4084071010700352910049600c034122040c8800c1300600360308440075400c201c014100010890380c1c040500401350030650341c00950b80c01c028280d0f12a681c8d840c2c00d12400c13107510405400602800c00700c0510850004054104030700ca07030020300c006e000305c422455072446142240391604a06000141c1060402c104c1c03040c2e0741d807403a01218200409454408007501154000503030764007002900703000068042000840e02c07446c10300c0c1055400181030000200348039141445480c103600c0c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 906918282 1250 906917032 906917057
    0xd0302072d02010818120c1e100b0429040915020d0b040501030503030711030903010f0f0b0d080306040b01091806050a15080403120b03070806070207120b04030c031404150905040207050706 83
    0x100315000034144041c19412034128640b940790303a2400201e0441e25050b04050041580d80bc007070140c10130304c0408030710054a4590140100710300030384030010300b600710307958100d100c011070240c951141c5504044000181e035204e80c22503503420b0b1120240401c2c041c504150041000610000c01c03603a104400d8a07120354100c0360004a141140300d952451507141d8244001e0038100c031280d90003074108601c0c01c2e0040005c00c04240902104030a00306c0040c168200600c0060300a080942101c81c9000c4140341c201115502c0b0f503003901c13006000189640029682c0d0702e080c4100d081ca242d01d80301500e42d028818404400e00f030382c000c20400004000074204101c80903004042c04598210030071750030000301980c0e001515007650740d40d242d1044442c50014400c050001400c800110f2a01c0165a042095034071a603645450540701c850082408508005128204068a0b005038025002030505011300701d60040351103030002e207200459040240700c3c501c100600b030b00140c00007a4a10480302c460910340c210260 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 906919532 1250 906918282 906918307
    0x40803070b10090c020c090a0b010c06020d0209060d0b0405060607050a260a030c0206011a04030821010902070203070b12061e060c0309031204080d0302072d0201081812 74
    0x402c1d0740070340c408a0503d01004c411320340206812041e0301e030685440b05103a50b201c03407050a450b110281c9074040380405850f03002182050b002400c0320010050090301e070100700c130003184040d8409961000300382e43c0c1d14940782036480c0030300038030307800500403542981403d20a84446494411a1b20003c0c4000340450803050021a01c5200071000060480c2451303c035012204040c009c1c2000c000d488006010340c4001250440c051002011030106421040e0704160442e03030307100002d9001845409241c0c884031920402c003820101003038064086a1000361306d43c036480c4189803410410f0303080b400c26007600b4021512804160501294058006c88803a13824101c0c00010303000368007918a0380c075002800042c480ea544100003008040280d015000c0301c030800a8042440c0507030059000d86240754102004084960707100350040c0c11028010041503020b00a05400c0c0b614400704136840b0450b14412912080556802c0460194468a100d180300100000d40071440e441300502451081d005001084c4c061402e00c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 906920782 1250 906919532 906919561
    0x501060b071703041b0605071203060f090207141905010c081e0604090602030702010c0e0603010302060714011b030b13060b0316021c08011e1a090303130f061103040803070b 76
    0x17804018160785516164014502e81c008101680c1e201003035001080d11a100313108031003c55280c0488004003504005a0304069402103900362041d01e03040c80d0021128006205450180b140c03040e0395000d0ba94203103443d500f903800342100602802034010030400358440001d903401500301e070440744420b680e442074000341c0180386480015007158170220030000415015032205d19041d4481d100c1c1d45c41d1f84882401c0200e244001d01000350004014050400018a900320b41c840d500704680020408003844080c108d102260031051900003510380c9000c0c04141003605050240c40b01042c828000d080c00c00d03240b28102d10000d00303181d203401104840a18030703e2091000c000d220041d41200d01d1115940e4200030403100081c0101e00c0b0020300800c11190038040356501701c003120002480c1c41c1028181810307100302600500343e520b8050100f00901c185010940d903000e4003811051569062041c208040103280f1400100040300561003000103103c2d10f000041550340959100c039600006039a0010301c801034070f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 906922032 1250 906920782 906920813
    0x10060528120b04060302030d180e0405010f0506100c110420030a06120507030219050402070605010e13080f0304020d02190302013c030608070e040501060b07170304 72
    0x2480252610211980001c1c1e00755014200a02840300b6024a02003004903143ca2000a60503407205002d2881da501500c10014820100f14006400e560ba42c0002500706078110303411240c0380d41d51a0302e442c10900c680703c0c058203c002030780d410712403050b81c020141181c2c4048802500505a164030707801c00755a560440304100442100b41c0380503002c8035094031003076041940c2600b4080c1c10450302003059680843d004169603001002006400e265400740403e0703101d00c00801109804d2008085015100c9000400703c480c410f081c0007800398509042d90b010054041c0c18408500c0b00150f541d4082441c00c0706031160a10b591b4085980d9843e2403000a4140e40c0f1001c0007508211141404019040035803100001c6038000c3c0c90780b65070032401000c4012040c50b8000841302c100328209007001c1102c2041607410241540b4280000c04c292202c0415241840c3c2c0d51018011400d558208020040c003801084002c0900c00c2c595403c081c1d850356800c0107001e448804404840000c40081e00b0b1015031203035003010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 906923282 1250 906922032 906922087
    0x1090515160819021309050604151802040e09061608010501210209040617010b040209090c030415320108030a050c0709180b060901030b06100909061412010203100605 73
    0xc903400403000112407010780c4106c08002c0d240c0780000e095410b15009100103230140b00b80d018812030505081000d07441048058059041d400e100106a2420700c14005003d03a90510040034641303410410f507146684940c1190007000803090042050342d80265426181c0f03041441c074078002c40111407441000f801269644d1780d0150505000144941d0f03d0300303c2650a0746004000c0c41312201900a001c00d0388518034559401a07400300000e5035103151100035541140c882d0000b9281004000c49540aa03142c045940054020070b000708100d100c84407801c4140448440c0b0790740829031401d0000b545a025660402c000d004000902e9041242d09005201c06441c104400304841001d0341c0741405500b441003812901180203801144c024508600b0480c101c0e03034405c1028035141c1d40c02e0144065524500c035068140b2207485404143e06402d400b40d20042d01030a1144034004140408202d10041880c0c0114000c0c0d2040040c0206400c08001c0c08042c5c83d410300304180d991101d8055100300b1032028461041 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 906924532 1250 906923282 906923287
    0x11e1a0901060f11061014011b0c15020a1101200607080106030b0f09011503020c01110d14220321050114030f0a0b090c0a0303020109051516081902 65
    0x5200e5007150f03a0b41c088030305564521a13020811892641d8644098070001c885514016040003200030205000024480625020101e103440507165030115010003411a42418224401d200303000c400600400034450600c02481c2c505c1c100d4550850021403400260704000302460581d5414400312601000680d03030381d003100d00b1860b0050005102038400e0080b24006400d080181045161004e030700d079000c00c0c00408044c996440c1c204c10ba0f820314a450014014507800b4006641c24040c288100354040d50082280c1e5558000f054414044580f8900c0050041c0210418003410903208004904c0c0d1616004001042c0141414207660006601038902140701c3d121000540c038983c1600014100c414a00c82c07001d004060300100350b161a0036604800e40e61f03001d60b01100109281101c8650040600000e69020a030101c010880c3c42601c0d800582c0540e441c1e00d444c40401004000036034580d000119048210304040700324001c80841d01e840c00301005044804030700c50b0700001d01c000312141c665020031507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 906925782 1250 906924532 906924539
    0xc0f0807020d0219091b080a0e010e030406050c011d03030f150a080a0b01060807050f0706093905090a0902010306080f0c121207020d11040501170c03011e1a0901 71
    0x40c49014030380a00d035192401c006d90300094441e03100940401c0e8225440e0281c3e1582e800056100034a9807051801c2150340b034010944c42c1840a00c001c00c00380039560f80b40c030b03030720049006900e09442c1c6081301891808d640303000c04d049103080031098940009101504180079250201072041480c194800c0c2075102515400c0043c0c10300f0b00180e5024080d02c1890010201c1e070340c8480596014508441003408910304002003104004000006e04e00540700f914001a00c1c122030b11000204404032031941c119a40003034045440b1070329220140b070704401e69491490b121b42080080340c18104080c2503419907580715081c0004581c042d030003010150078490304480c209044040c03070320380d2035005095090161003040440e69200c076010401c00e01d0001c10202d4186000f0a503800e20498076150881038891800d18100d10240750745901485008004188000240381d030b0101c0803505100058181038403a0785040c40c00c2c610308402c0c0a6454440301c0703038000021002e503921a01007204020a90140e40100040d0011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 906927032 1250 906925782 906925819
    0x1b021908061303021e10020301030305090a0906050a140d0f030f2606120f0d020a021f170a181b0e0702071e21030f0c0f0807020d02 58
    0x5012508040e080340c000d51185200c032441c1e02c440d0b240140051304410044005d01d0020380c807506103444004226001c865080c43c2d8141240c000f80c00450003d60f000502240d64501404007101601c00c1c80000c1250b0b519290014441c50482d215802c1c9602e2003100c503251075619040142d480c150408019001e003a460b143c0100403001d650050800b1610300150100207081080c0840039001d110740c2250380035100c110400884042280d80d0b0320003441908008159401e040c0041200c10609070000c1220701040c0c410031600c80e100300d06904105001001d101e035801e42c0f1000400707540c01204100c10482d100e41402d413000c3d1881b8403240b0100b01c0c072a801c08040040d003480c50071400b910504980b0807580c030b503900306400400a0300c0000042c3c1c080d11090040f551f112215101544041c14503a030000d44e10611521424190a40958050740c610143d6060640007480c4602100a034540082c2c1710700d0702e960342541070144000c090180c40e0301203181c0d403c54641580040c01c05800810300b01629940d01401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 906928282 1250 906927032 906927079
    0x2a020c01090614040909050a05100608060f16080703060504021812060618060102010213080c01090b0a200c0603040b0a06080a0305190c0804170622031b02 68
    0x6640081d504000000c0c90310701c248102007141c50f030011543e02d0185068161400340000e614146c0e81d50140ca111032000540130030031000208111400414001d01c0e12000c54200b81000304803e01d0619802c0802a90541c40c10820300000b00300d0600010a4443c840110010300080c1c001640040c0300203000c0842c45152420015400c80c2210b65044ca00784060429844401c241c600641140c100d0030322904c000c0c0d0369a42244d2104040c070006062003280300000450f0201a03014404a4019080b45100c65074000e0b4804050a1040030540c40e080f44000001d00100212091010320350000b201c0c0d148100c1d00340b0030002e0180b4010500d980b40d0505040c580055001992954101d902c0c02c10300040860012910001c0070790940c50b16030038105c05040d00a4000c103620b00060801482d0382c11080092000e00140014000c00201014800e1507450038502d4224003821700c081441c100c48004903a001c002d81640e1002d58540340c00c00944050100c2070392940d91161000354820381d038081c012080c2a00354117 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 906929532 1250 906928282 906928303
    0xc0804030c15061e05040e06040b130b010603020a030f0515060c07080111040512070b030703090206070c08010510060c0c0302041e0c0f0801050409020109170a052b18092a02 76
    0x81041c5203560f244200001c032840007c0c802d4a903003040b000580441c1c1640e44450740042246002043c0600b555200d080108098210340b0100b5800310b03180342200e0345846003407400d00050204010313034201a07280f03021a1346410b40d041d01c61400002e8180b020304040c0b000c000200344190090001003c80e451440340c035001b9004c0d8601031421640c036011480b0300010045c0880e03c102101a180d5107419070210007401d100791040e0307000281080001e00084903070002200900c42d900001070f0a0502411003000e00c8885d034041300800014298410102d0310300310403181201d40c1241c00060704c00711b4248034000000c9102c040455586080c441100c1c2d203070045c000c42001901c607034455200d6a02c40080004542c014200030f0700081110310144032020605042078100308041040740c031039070090381d0f5076482d000d01c600710300c0718409a10241980f10501f10ba4194030120b40c0d404e2030380314051b040611139130703507001441030400140d2510300b60440c2203410808030480008270181440544460480690307941440032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 906930782 1250 906929532 906929579
    0x131e02010e031606080402010e10090321020303010b0c01180503091f210204090218030c040c080403080a110d0e0705010503010f0603020304170327010c0804030c1506 73
    0x2030900451802140300001043c480c1038a001060a2a9084521001c000c1c0103c0c10310100410100e029940d0601007141c07428180c0d16a88624190701e8003030a081d0b118807000c000711081d100c0c2d801c0c401e5000f0040c0c0341500c22403151162216800070350343d4013400318483c41d12540104010700300f060001c080010450f03148150f50288800b641081c10b4501c008801009000144041512048150500840400d8948100030142c01c140c4ca400801d0202da00c403000d03608400600180c01c50745401c081c440102c41120456082190311f4200c0c0c4003410500c0d00420041c2000345e441c1c0002d112080544c400c280310700148280c60f8446014020140c020300171703401018003501c24131000244e150301c42e404880c140e418131441500821310b0488150040c6d0406001141c00107859440d103200c44414401841c8181d610a0400d40e0703040f00c42c0480903012491000149850341001c90241c00142c02c2405150800d505207891100d40d20325007064110030341418940d6039030a043c01f00000c0c2034040d125181180d140d001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 906932032 1250 906930782 906930797
    0x21b1b010c020d030c03020f070902070501151505030a1103160e10140f090402070f2a030b1e070201050603010c020703120f1b1505011e0509131e0201 66
    0x15a80c0c1c0500c1107009501011900c55440002c3c410544814094428011100800ea070102c110b0308101c4650005214142e0214044052003424010b2160b80002c0b0080c41c40f505040416a554001000e403a5000303029000021889400f0550301450261148000315070701e03414100d400c004089400500f03100081e2481c840f403202890300d02c2210f400b0400c0303a180d454082800b180b4a49141c0c001041481812009200e102460b4440e4001401118807030720035001c00650500c3c04c4003008454000e010320f8525a03044e26020441e0740d1682206523030b04101c0030501582c030501c10042d0b2501c4420700704280248070050004c050f8054001324003440b0100c00a2140c0710511000300e0340d48280f271001400000794040302403a0300d8020901620400d100b89042403c200ca02104115200c1c6200e50454151401150381044659144151405003c4c20342c4c60802004149420641500c254094070b40300340e0005010400e04040140c07405100b0703900c440135080141c1e00105400390303d800301800b170303000c10b590 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 906933282 1250 906932032 906932083
    0x501031103071d1206040503070303050c0a08241804060c0507080f0307020f0a0308010608070f0c0303050903040909150f140a0c0203070804080607030e010b0f040f021b 74
    0x1460a80344240310310f6a82000240c04440031540c21440e0f12541c580048801821046034907051120034481c0d801180255524550b40c900241241e500521443c4a860b0900c10404166844442150400c0d00b007180e070aa000008541c41da5803005550150394016841720008032016201c040c81d81c452401002c0c20070000d1180201500d16200390000100054000c001221641d80b01801454110020340704507400b8051400701140340448888054000c07076040d030010401e00740e00000040d4000303a00c8c40c100c4031a00f000f040141501d421400001c05064580e400651040d01c2003080d40e00400903070f80b060016041c141048141caa825110fa000c40900b4051400990f4507070b402070030400000c40f0720840d12a075034807070605d0080540c0d09044045000c03c001d6040130030303500005440074081c400082d0855060140d0301404071107080704460301d00d9043c000c107030400f80e580078155510400241c4001c030303044c00003041d91002840350441c40c6041c81074610380300c001442c0000390b980d00140c1e85441c00c0e440e10b82 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 906934532 1250 906933282 906933311
    0xf260f0405011103280905070308030a05012102065e031b050907030204060e01020c0102070b13030f08071506140609040b0d03021b04090b01270903030204050103 71
    0x120b031034845e100e482030340c02080b50210031259094081c012000040040495886034200030301c0f0351061f07418100202c00c0c0301a10b5a0391044500418103602c40a8065641224942c058429598040c1c49072030701103205064082009140510311503164200c1042e00c8240400d0340204a050002d00040740100e4404c100b003101440079002101100c0c91200c0f030304c81c955900e01c030750075603280d405510700006d1080009964a4890249004600d41e4a016841d241030030030040c6000005031200d4115031122007040003598000ca003640070b40c0c000560440c0c0c2e038000e001c0085229011a03100501301c4442001e100c1c1441076403005405403a10800681e9503040e0702c40c52140a03114907016290038122142c0c1020118504500185102c60340540f0100f2500600300018510754544123080d40035801c45040000040c480c0640845000f1007201c08110030340054580584004050080d0458551162143c00c20b00020519940b1245c00c3c00109000c01c060320311740100039400c2485464003003070410f60800707280007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 906935782 1250 906934532 906934537
    0x6090801050c1605030d0203070c1104020304120f0309080f0c07050631050d050703020102010e0a0b31081e0703050913020910050405100f0f260f04050111 68
    0xa1408002c541041541400380304908080c100c21911813004000345040811140044c51242c4002c0d100c1e514000814140000345000c00c07071600b0321540c8108200000034607040405418103d0f03500d00307855000e008203030950091003100c102401004000c28640702c0508403000502c108003000f015107600c00e40c1d66092140c3e070700460380501040100e04070b80c1c2c44502c0117102d00c1d007050020034101d010180d40e01c0001c10f020200c4500240c0e181c1d000040188155602409450442c5d0700b61030041c44003440c1c4c0d8580a1070080301402000c0c5400350f500c100b88158030800412503c00f40d40122040d950b00462511034100d50240c9900b421030303040900f048041054001c29100d002c1d4164841a1070041d1030402c00400c040280003e010159087c84019440e8640c5031101d40742603040e41342c0e541e0f201d041400f0884140c03540b00d142c008100d1800d044906050340300004184080142c10104264084100444451001d85200c0c940e845561340c104001c011901035114000c0780954001c01c03404060082d03200e500d1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 906937032 1250 906935782 906935791
    0x1030603081c0f060620060105060708180907020f06010602070501090b0d1515140f3f0f09010c0f11010209060c01020406120501051f12050c03010609080105 69
    0x1100034001d00b880800221000b28044520110006500025861400c00c0316042d801800000c2c0c81200d01200340900b84210718078065000d401880340d0342c500700c0080e10600c00d682000b00440008a41100307031a624103018086c6480090000b03000c2e02e804240255078040c0012070490740d00c030314000000d034a400401c00c1d2050701d0b41a900c1350340c018104000180c3c07035484201301a081340e6584100d041810b01c1000400050280481c04400012030314000610110354123844030713118031080009882000c0c5140032980400f040c819101024400d00341c07005000389084801c20381d0204043e42c2010102d4072808003612980042180c0b4020f611010812404c07076000d410f005001c103070340304001d4810500034414094000040c900240c50315031004080b803450742040c86020300381da40114081c0034980e04034190751000c040640c03040209626000c005180114014a58600d82800b480007607000c911494001c40501e880e82418859810880c0d4512860380c024410340300090111300c07000c1101101801518042c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 906938282 1250 906937032 906937043
    0xf040b0c0703080609071b0303152c0705070f08040302040507030e07060810051905040b10120207060b0415090e01020705150604150f0501230307080606040503010906050901060501030603 82
    0x1584d0b50142030041d080c90103040b900600c202c145a18190900040d40c4824442c860355011804512840d022000c907405900090407451001c248100320700100b0507503008900c10907c0c45800c68803501400e8485200b0188040e0003131356005030b1213090106d600001c0c41264401d840400850340e42402c12012034071256110782070f40d00085410451a4802c00d00290002c515050480240703540f42c00040329403004110244c58025221000c001c907180922450407525400e41da566840f03400d10a00820001d40a1015002e0aa0210310350040c007241b64400d41c1c40c040302400800c945156103a401913041503a1007801801420300010714080c00e018029200d92540c488003c122007192200040c1c09001c2c002c0c00c1d2a00701e659160454220740f5500c3c900310003444801d0844980760309080006202c54102105803500746d005400b0440700c03024040880e5806100d80c6407140042c0c441c4000100c80e48290783c0190342c150f003081050f20030311002e607202c035005420200003041051359a10064050b1a55444050030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 906939532 1250 906938282 906938297
    0x60f1d1602030d0c080115020a020607120e040f0506040c0e0f130b0a0329010f06030b030705120d030b1e1c020415060f080105060a050708120f040b0c0703 68
    0x10351080820540050a034640192070030005803072070f4801110704072060880014110001004200345200d810300e080c60b5588041e221410705600070980c0c5204080300100650490880040c4c204d1143d034600b40c281000038800d0090741055280b51002d00000e8036240e2246180010b41003650b0f0040605d1a06c070440a00310f420492041400c11182a00c07160340580707266283e250298003580c07041c0c507620141d44502100710f982c650241d1191482c908020800c440c403284900180244100c0d0395160048500300c1c5008220219641e0100341007074025804507402007800a40d41d035047c1004a00301da15071542e0b0340d040142c0075081c810030191520084114903100440d40d11107400307003041070184400699101c1080702a4140da8041800c88900045010001c240c0302014401d007603003c3d4460719110900c1c80c00d070700305504140004003184245018501441000180d44c41002a8102500e00c80702d54000e2a07610351410080d034420900007180c0032900444d0f110001890f03100c0000075070310a50781560300d004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 906940782 1250 906939532 906939541
    0x2010605011d010903020d080717030702150603030d060807090f020f09091e010803030618040c050907090f080609011508070603090c05032b0306050105092809060f1d 73
    0x10b40c1d6500a29941080001800400543c03070711884440340c1841565100e13940c0c1c0903824941003124012922002340c3c001041806415580000c0d1100e42007120009480240c0f03071071001a145101d11512041a14100840020500c2000c64a003084500b46275080c484062100c521208920950780050010101800405140e05043d01080e034000c1280304031210003c60718080000340802648049200e90000040180303c1c2455014040008143c80d9404118280740d40c034610552600d000d0f0702d00440003800003803015442480c42c00000c142050711910060b4980c2d00064030744100f191000708035800d04080c0c1e50480800c414040849800101038010503003041b6003100640208442502e410b1030888010480780e40030300c0380030490014000341000c0f010000b580c403c0701c0b9500300121424035103441402c10031a42c01504581114a04a5041d4845d006100300404850300d0011307242811022000b02040380030302075005c2d809440000f40c50882540d41c0741c419491240d0340e0017178030707540000c041c0c0800c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 906942032 1250 906940782 906940817
    0xe030d14030606160b060f090402100806220902032103130203010615050711090c09061315020a03020f0d0504050f181e010b0903030a050a0306030507090e0d0201060501 74
    0x40d40c002c4001014146010011009040062000e4509840d66801d00040c800e80d0b15140307010600c144000d0324581c200e071405030000380190802e035010380180000c04000401a030743d00c0c00500e02142032007034409020100d400c002e000610281404030301074844d0012303000c003002d920480310f100c69072030300340641c550780c0e90700c000d12620007004070b04030380664807002d01040011040c9005400f142555580a031100100d081c03141c0c00c00d0b00b11303043d240250031804c148032982038800b04541c110001650300c5a40c900b0300781a000340d0741d0b545510200e80034240341031010400382c2c00b04400001c207000c0ea080750751001c01c1032401501e40c10703451501404100c0820003040b40d07041c44544130b4129403004101300580c501c054500c0c0714405044401061100c4100c04201003880180d0805003d00100c0d0403070703800c046c94400881d40d680b007115000c50a011000c20030301c060310b100b0382000003d1503006041da0350041d9034000500280042c484a001580151481010325a105104180032a81d05030340e407889503400c8030000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 906943282 1250 906942032 906942037
    0x3030f09100504031a160c0314071401020c060f10060e091e0702010b0102011a0307030807020a03150b040f180318120f02120d1205060a090c030605010e030d14 70
    0x20741c03041c80b5081c000040420a041d0b444031541420340c3e14007403140b6115a400940a0420803203405120404250b240404c1d81300954802c0b1030010600c032591903d003402e00b1111b00c0141c90040d5521340c000104484d50810100741c05d80901000081d0078030b5030b00d0b0803150269041c03e501484000a017010b0b00848186042c0001e550000910002d110000c503061407015114802100d0400140c0e4544101c10041d590910a0410690700d001d454050140f8074000280c803481d003844054810300004c1412415541d550111070001d65000508500c403040349001c94002c0d01d1100c078154800e510f80050035944030b41d14000c01d00540707400b003030b42a104401d5980560f21506000300048811003200ba000c998990310410007103070240106a10007a18419104102c42620452511038440d0001403c840d070107a0826480506941521000302e00c55807024080343d075002c043c0e071002506504000c4009070301c0790580d0052041c0c074001c0c1c1c1d81070f003401c00c031009060780c40c401051500000b820842a00210f202d20902 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 906944532 1250 906943282 906943309
    0x506150d060e1501080a03170c1b0a021c03080a09030203041205060109050106020309090115120f0e06060102060c091c0c0303020f152e09061d0603030f09 68
    0x4550400391180012680081c1464040b80e00a6406240d91100c4008441c0104109001814044c000e55401041002c0d004000101d2050032340201c0c110041c0c00b400c0c0d600c420903090824203507200b0550390702c4d40c480403000164022021004075202555108071107010254054460341003640b40d641c8260000c015036103080d0110300060102080354610080a010b8079805000184040d50402182d035048030411b1f07020341c0955100304003414481c0ca4200703c450440c0c040c00d841c0440050039039000d1741c0000b0020b400780809442c107a08005121a2030307105002c1d02d00c0070707011590550345560045e03039600026a80141d461400b401108a20f10b880c21000803034a4010f5407a1140311010345d02d80d400410b150300120050b0308884285072400c2c00030014030748900748003c42c946140c200f550100380c4071b440c0060303107400d414201c0d110b50454900c040c541e440213000614041202590325011040342030694003509020600c480c02040d01858000181c0d1048118042d1403850804a50100100802030300c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 906945782 1250 906944532 906944539
    0x1f0f140a080f180303011415070302071a0c0715031406090a0f0b0a080102120f010f050402030403051e0405040b010903080904150305011b03241e12050109031803050615 74
    0xd1610a4405013030001d580240740342030000300481a41c00030407610210140c0040c81c1900140203000109038006a0002102da000c8003803114640700359002c00080c410118000c4d85807007039600004002d00d500f41000310075401d40d40c1c104250306c041d4010307070310384403040d01c04135800316403a0003103010403d40b94000c02401e4845100000c3c40903205012030b19040803588201e04e665404a005c180c000030243c0d80561140342c2c16410442c035814150069015000c0b4001c190007503502100090030035000c1c50840d0501c034488003029115a036004081d8081e54814007a0314040d90500049407400c1d4042c8040030142d82c1d01c8031482e410051400c0510004041c150b0004d1010422100000007080c028170600441400221843c040400e00ca81c020302030303075641011030051030300e07443c5c68040360f6480c481507500340c802c041c0004100d8010071984002800303150b0040b980201c0e110003c0c0d400c0020540c01841e01d80c0c42501c03801c081807020242c1095200c4580710207451074014000040410350305640541e2902b030002c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 906947032 1250 906945782 906945811
    0xa03200102160b010f080f0607030207080c0109230106050112020a17070504090506010e06030411010201060b1b0f01020f04031104020f0f0d24060e1f0f140a080f 71
    0x1c40302d05404000700a0303440050410050052000042520014020b40c4004000302910419200e98030803001b1708034001c066003c18038404014070a002ca0703461541da44028042001d9a00340707500c008082940184000c09940e0840b400e255040c0a8002110016140c00c22159484000d0341d02a610800c810703003c0103a15500501011030340c13005280503000b590346154580e800c01700e214044403c0074000300d06202e12401d08001a540752002c81760300903800078031a0700003d18040103038050700c40c54000c903c840f40085503440415000504000e48030100700708498102c49032900b028200c1c42444c1d0304201244080206001040462a0400041d84050401171071308c1c5425080380d00907008040c0310720a1050000700300034801d2881c094481480d8001480b07000d01026070f8140f2070810704034841c4c0350600403074039400141079981040d03410700c2d0724000400305a81a00c01d07400402000301c1190b100d000c101b4110482003440c0e000020b6880b120020340b41c0300342944944807180c0c00082e0080c903060f01c40d03991 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 906948282 1250 906947032 906947047
    0x20c121902030a1406070f02210d1b020c0a0509130b04030e0306011206050a0c0e120c270f0c03011719030e0a170a080a0507060218010e030a03200102 66
    0x8140d442a80104c41d019000a0922000c0148000b248105503000c6601100c000382c0d0228010702c0c1101d07501641c40d182580c40d0305078a4038401a00c0c4456042e0341400011118417000da401142d00329040300d0846880041e40c1d103840401000490680310b0f010007185143c6c3c44c00029203100500c0c0e030024001c2c10500b204082c0c101c002450500700343c009840700c10b11114154104103682c080c0075002203000d03005001c0d5641c04c1d90000c0c00600401000351040d10034400c10519500140712040b0500005031142c0001c000d00000780074a003499006403940003503600001a9403107002c0b08854029030480105038656442c007072001e080342e1000450b020850107225115030780c2c041c2e1620b4403030090784603407100985184142e0420914084c0c5078031005401c0380442e1440c541440200da0350b0300c0c05600250070750f12110007040c203c0705405001c0c00141418400591420801c3d6410101d80e03900e18240e031545100323100310041c50380b52468201c0c010082005080c040c0c400762415403070320019007802030005091841c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 906949532 1250 906948282 906948293
    0x113103060207050f1603030906170c090109050301150305070e0408190905180103110f2b02090108031c1406090c0c010603140c040207121b060c030b01020c121902030a 73
    0x5141d404e81e1507403460345c0420800c164003e4001001015a400c00007403c841001151040032001400341c1da6110b03002800c00c085a0103088040041d1501500030400d080720100c1c5102565458001980e06110300000040d0208030030220303d120341e43c00705449050001106000080d220310500e40401c6c02006c0c0e40c0400c050726049441100090f0601c0029544d500d0b40c01e00820070310400c41c980b07000e15007854580340c241c0c03038910704058104640342d03450028090a110011118981c17060003940140d45c40000550040008003400c050070311a01e01005050011858000710f803401d1030030005808210001648625021602170b622001d0084005e01e01414000584d084560340d41044800c018083c400d100c04501c10840c2c60a0014140c6045180284d030361100052000c00d80080b4041201c3d2415174103041c01459610810f0030780c40401400800c4081c007001e005000c010326420700611600305504058508441801000c2d4002c90181c84132410500d2841d2201c40c001c00700b641c041c841c1d081220000381e0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 906950782 1250 906949532 906949543
    0xb0402040504240608010503030a260702030c010606080103020f040c020f03030c040f080328050d15091802130e03091305160c0803070c02010e04113103060207050f 72
    0x70f1000c2d070703100440060002c0d00b581001c00340d0011010014101d0060000e910000300708c9500c03445030700703140c03560b00b506528a00100d4140c940c07041000d17030300400b4003421035000009001115a60402400303034079111002240c8190091201a40c1700a40b449910310300e0801c1c0c0d02000c0d20000e248150b036200c208000c8400d10716402954503101d851720000b0100034001450031668050021000030718900180e50401840c2c00030040b43c44500c3e50060741e050280b490103041100c003001413002c0b003841404000910307000085568450a501a42400581c00e00100d03204210603030190b008103000e820043ca0f018240040084104d0b1010510040112000350780d141010303680406245500070a803490400440040c126010320401d090003411106c1100090800c3c1c10f490388210b940c07070302084c810054001242e1880750682e407950018035050b0940e061203042d8004287d19808a0445522010510724800000310403010361080c005030041d040c0300051180e001004100e02400440ea80e030507110b2481802c20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 906952032 1250 906950782 906950801
    0x190f08010611152a0c101814030304120e13180803010308031812090d080706050a0b0f1909050709080f0601060f03090b0402010c150f05150a03020a090b0402040504 72
    0x1309071244c2c0c0450151010b007074446096a104924144000a0b91050b0355103038601000da5190380b92590501030082e040702001040da0001c0c0c0c0318070300c014580b148544a40c42940d054840d80580b035110070050b402181003122001c406488900744cc2d5801c0c03d4400102510400c0c2c115049076086841d02081d9101c0185028500400401d592420100c8403040100560708004440b50070280300c10700009207441c1650600b10054421554564080c54114030910600340f000b03002c14900000e1000800007640800300110003a00c84c800d444078054104000001b4449407418041021081440a61583e1308090b42105d464101004030070b417140c529030b05000c4041209640c80d80510300402c0001d43c80103e0943c45003090504000d500f01c992521b5045640040020781030000030740b95a0101700480141c2c55060800340420464440e0104c3c00c4000b03098240e0b00c0e114160401004c406941c80d0040022048950003816045094503020719500a41095a07029070320030b50034000010292118010403080 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 906953282 1250 906952032 906952051
    0xc0b06040f150620010b0d12090b2118250305010603030c15060b0d1e06060e0102120309071a12040f0b090705210a050a08190f0801061115 61
    0x113496100940556640f846980c01007640e04250b1415041c2d00c42c2030188004035080110902c51500002c0140c8848041c0d42c4000d06a01c000546101d1054250b08110071050085600c072016484155025039148400d4206104c2504070400403100d14a400c210061140e0010400c18041c50f5261229421550658010341c04200b144509504010f00c100c11070340c8002c02e60008104141c1003841c0c080b407501910810f1805e9550340ca00110350009900c02c2900c10f040a8541400a0b5031aa10028042580304144034090302c180c035808403441201d001500c1c0300c1e4900f0342c001c0c101203250039058005184c5141c5801e40c1082c04100c40400c0b0002c40988502ca24041c091629080c4058a010915420300428160707060304042000d0109985100c410b80e40c0900d0f000140c5981c4895585207410901c0c4550014842d108103941ca604000803140600b846002701038900a80b2080018155481080301c40c10344005008000140509401080d800e911420384104686c06003041c03503880e031400102034500028 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 906954532 1250 906953282 906953297
    0x200f0102120a110f22140a06320c0f03040609050d030e0105030a11040f0e060a0806161e1206080f0309040f0b06120403030c0c0b06040f1506 62
    0x70600e01905160002e00c01070301040442105207000106024601d1101c002c1c1c0300024070403102c134412000c40900500000e5000c8880d0b903684004038254010055424001e03540488006881130040d100071740c0401145040800441140140c42400041081150240e2000340702941106034204818a1241c4000300215a29814248007074a221a40d0b80454405c01c00307240d0f5140000e501c00a44100321200b802c0154981d20f4000c0c4140103408401109100c603000030400040000c0110701c05000c440510080311995181d04060205803020b0380900b214552002021869030f500411043c11503480c546880240b4440500815203003220000c02400014003c250760a03403600340f8880c600c020040e5100903d480c44448084944a00981c101c1500c0340341d85030301d445084e51281d04041c0684a00400032541c800b580c0c100d4100750784040d14260700003890501d105502c0f40c001e018484070260003c0e0171140070740e2050100809030458000c80110191185284110201a0000381c00504500c0c0c44075036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 906955782 1250 906954532 906954547
    0x3010503010510031a0709051002010209040b091b071a01090b03060a0e10020c01090b010e04110405010f090b04090210111b060304030c051f0b03010e07080607200f0102 74
    0x1829100050400024055107400403c000750340001e4a03107400441d44c0310500c0e20b940c0c419003900c0b0f00496a01892700054024070300303101b0550640c002d100901044804001580070b0f80f05118545108540080c0940c001d603802e0030300f5112300350180122900c1030081e55011861400342c0a0743c0e0b8401e920201d80d540c0c444030016024074092014607482000d4407005c0000030039005010ba613400d0b81c0402802c0a41d8005403841981c0307400c0d0031042449400400382c082d1542d44d04141040503e048406445ca01d211004803081d03468280100d034100e40040c1035201c02d442c184501c0314000c002c5c2d24543da0f0b1050b51910b021005807500f40f01c4040300b68080d00ca4410340b1072021505400e00c40d03152a00e001280142da8090801e9846109903074005800d07181004101c0320300d10704646000182c10003106c0ca4200d1030905030086132190400c0c018501c056001340903941028402030f07500c02160180301081d800c660002410740c0e20071400046c3c500354800c20441d0f40448010000c1c00e00c03e054040d962240d40005144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 906957032 1250 906955782 906955789
    0x40f0f120f030e03092e050a08011409040809060c06091c030506033d0c090b03040c061d060c0a02010f17040b0406020c03030a0e1614040207081905030105 68
    0x60804035410148038842411610755280c4c420171070003501c140070a218080c6039500c0c0c03803011400504444070103240c0a0b0041c0c03010704a50000e1a210001942c0e0790b002103100c0d1010044840b44d00c0c070180000a1740d03110341e61a800d03d174121000150708541e05000000b1400d4080000c14000d554820191005581007a0707407414084002d460241410b044c00240b00b01e6031400201e001004614800c00c4011010340541000304100c40000d01c0d0142c007440982c0c100b01411030f4004502105c50762500c0480d02e58420080509002c116005400d00b1001d600c1000045d00442e01c60ba4610554048214092646000255542c00041107250b01e03034858150f040444d60030403000e4051922905000300414511080000d140c040203000410780c3c20071902007020814607805449542101805503502e918146503801c1c018000b8440c420f03410b11810300d15041e11603c02d869103050b035000b184140618a480010b10020f0f51040000711202d603000c000b165482410814281810344580d55441d41e25494001003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 906958282 1250 906957032 906957047
    0x60423131419060b0405120c12011b090602190c0b04030605100b07020901210c1d0a05060d02040902030c0901030f0b0c1204030e150f12011418040f0f12 67
    0x203007000c8600c3c00e181400003413840000d64040b60b00458198441c40303402407001d802c0407800007d9a0304041900401600740c041900640f0080981852164407507100340d50403149034501d0301ca40005600450305840000d240264108000c074000c40c90aa1059503800403030189910907402078440f0ba949000b40400d1100c0d41c85076100a112440340d0508003002c0d50009211100c0620036034070159203000a5182580043c40324400c0c142d0005249a00c084d611b112218423201151920038a0701c860000003500351302603201d6035018100c0070f0041a00d80070b0350360a010080c41020b80c180d0b410301c24065011203965646c0c40580c065403141c013000700d984883d0300c1e00c809503450203402e1001c40744041c400320248000c0d21a403950301607014030b458001e03c490350003c21300350000c6900704443d912000407001e04c0f60300c2c814018603440000321043c0015a98507115401156240c0004941c03205104080d45424110320013510f82050080c401140071114a94400203890a0131800304c8102185184d01007529030045030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 906959532 1250 906958282 906958321
    0x1312050a02010501080114162f064507080a03110d02030a031a0d08030916051305071725020c0108010510020c04020c07050f0604231314 60
    0x21f00000003d400c0507020314000412900a00c282d2007520865540300e003101c11402c0700042030b00c81003010242072208400c006000601c0700e40c860040480d14410164070000c9980c13100c022890b250710511151102c0b1f80341e42183c4014a540350790030445003540e0034010b80009107903141c010005082c1900d8040e0400403180c61140f500c1c0c0290040b2040b098012045942c01c18642c0340000d001d00f2000507800c1000c83d40c000c85900b2802c0d001024013001551002940140000000c555115100364003e0022020b50f0003800d40207800d41ca20b16030040c000e5089a60001040e0500d807400280424400e810041d0442d07540c0f8030002e880c12000c41c42c42d0455683c40020060b440a8001c01074030000280844406104041c000c0c80c41000e4440228420311030500320300c00c01030003995206400c8514958616039070080500c11428010130000314070f012011101201c2c040020402018540f404080c5869018100c5136001091391620315109101440b5003803800b8000b000d40078a0b0700703203040c101c844809540d4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 906960782 1250 906959532 906959549
    0xc031507080903040b220b03070c150b150904090b100501090f0b19020c1c0c060203031b030702070b03190f050c0405090901020d050f160206060d06051312050a02010501 74
    0x4c0300740280007610044038050343d201400402811540e80040c0b0b80c0d90300e51383c0301c3c002503c40803051142a0b0760006404c00700740d0141d0031038031481c11101044400c50300711210342d40d80543e0544003d0301c2d01c401c8001070850003000a10014103d42e0649500301c14100c01c582e20700482d441c3d5141484150f070001105000b91102ca00c01441075810202712a020344640b60509414a0150100c01032951003002a020ba542005c0e0480ea184500313a21901c0e00c0e5100e4403c1111100500304010a40740d10000540c0c0c0f090007400d90280c1001040c0d00b10107010341c0050007050450041c03000200300128803400941c0201603c00f10740d0414240c03001035104444c3c00e510381c10140c506000500041c9000078003924169002251407010310345035180e1590092003052000c002c8070b800c100802c00c0d40300b02035510502c240350351755001c07070b01d40a441402c036110302c03048410303e0340100c03c2c01465020a040303074095a403120b80c9024880c44100135803210003075012101d11500000e00005a00c0804980c2802000e00505082 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 906962032 1250 906960782 906960787
    0x9140708040308040525081507140c0a0204020f120f040201091806051026040b0f070e04050f010503150405100c0c060f090309051e040209030c031507080903 69
    0x2500000c200500c00341002d0100100e400106050080c00d0284640707032a411040c0e40303c100b44c000c1c000d0b0741042480c4102c014070300800039a69001c944400300705100e2100381d1f888643c00107810f070142003a038004243c4403e0f02d10a15040000686441c4001c1210341c601d0100543c482065401d0060007250007030070308103400c200405000050f60464100825900b9800e201c3c01d4216a054070b040c0180302c0f07a88803030f41c4104003000d81403031950802d240340c034104440580480c44c0d800c900ea10707024507001076070300400c500b50a4002507183d040110307080750466030714940350240800c2100001d007654020303100e0701d42e811803601c0100198501042000000f440380c515030315546c40c140c1c50711502c0e020484503010006407594801d03000544a003001d0801140e020b83c04001e02d80881c08007200618542c64224007207100310902065525084142a064a8618691400e00c54100d400e020107500100c050700d0309441410503800d8140d8062100f071603200c04d083c4c010820742ca4110001400c42d107010b4101102a0400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 906963282 1250 906962032 906962041
    0x1523180406150c02090702030c150a0e031201050105090a03050a060f06050d03020a06020c070302120307030f09080d11100221071806140f071209060201060617180d02070914 76
    0x2083c00081c07441e4040305c0000140d651424160700314800c1026480441c010240a0320a881c215042e55006900d028010440f407040070504503680c1c89480200c0c00d0701203422004106940c07043d0014030503c00b0190071884415620740c0d07030600d85244150b00f21002a1582d600c514403802c42e1040100501044491000f05a81610040d44074405103801404641e00000c0000014404004000c011075014006a2203030070980c403c2c2e07450b038110003c1140094860302006400034401e08144082d16100300c09820091224181641c0c0b40702d600500c0892402502c40060310400d880c8084e0203001494500b460000981d800410043c407070003843c1c801030181031540249100c0281803051b0a485403420f00c0000b00c0101c41d45c18180e0300518000c0083c91600107000010040341c2c0156a05145150701d80b10704168403010700740d09a648a004007030000d02c0351001100b0341200a80d43d242c09c000d501070001026400810810f0510440e00d4142000d684080c82c01c01120742140302c0c601c100301001e11030303007c01e080 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 906964532 1250 906963282 906963287
    0xf070f080c0405010302160b0c0a0305060102070510030905151f050a030c0e0c0c1b010806010905130b04022104150e0c040e030909160216152318040615 67
    0x80f03000d1a8109035000c541440e00000c0a5688504260014481c0485140c440001c0d55682c1c005000280024106000703e5059400003901900341c80000788820301080003800114010400c0752010703901c5120380d406032a079019505812034010745001502040085041400e11415a1158000e5000e00d00207030003000030800900d05101070340c500810720600d42d1a00400c0140f54091104080030b90f005030403c0c65040a03407005074405001e400e0b00c4100b00ca9550000643d0202c44034401c07583c0206800c11260f8048034254815910700c44000c00040c00c0a00c980341400e2440600b500b100142c0110300280014401060b400070786255034a4000d1150324030700c0c40304945402205145901840d10360b0100004074006105460f50040c0140084042c2d190480c001280c1004c0c411039000035008900b00c09001c0d01004200400b580c0c0200090112440d8940007101e81c141107440b640c44030520119101c008900400080159242031070003511541e03288801c000480701b06174822020001d00700c050400d101e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 906965782 1250 906964532 906964537
    0xe0a0f050a0603020a05070c09060f0e0f07180f09022d04030b040204090209040609030f05090102031614071502010b2e120606021c0504050d08030a0609050f070f080c 73
    0x25031503d40503032a003030101416a1a0700940200400b070100002010070030b105143d0101d41155a92821890f945680c0c01da8000701c500f0a4941d40c1c09200007400050580d40548101c9203060241064100000d81d10346805400203240d400c0200081e80000b0903224111001c402124040600d0f030030f14455003401d10208501d4030403840b0041194200000003815590340e588400019500500b05580600d002c1c0703031000051442010440c0810031016004e15218400c03c1610000241a0000d600d80880e40c40c804d021111903500407501ca0300800544400c5030b84c140030b8000100075190003590700002000b000ba0039208200080c501800141c8042041d581107040c0d258400d04607903422040d5480c00d407508550041a800d5640c0ca0390381024000a0a9540020b65046500342c0f028401003400c0044000c03200c5210b18400c86600c0040c5550107004170700807100070340e0421803500000820a030f427042da800c140c402c01c43e00c6400340b01020b010002e8550700300d1a0b1180d908038a140212032883c003944000c6890 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 906967032 1250 906965782 906965789
    0x1208010501021525030e0105070504060c1509050a200612040615080f030a030f02071208071106040b04110102060403020303010b090f0a080c0a0b070f300e0a0f050a 72
    0x301200b40803402507072951142020030b0320005485492404844c0c2c02070050700e1110517a910030344c64840041c0541e0b1180090b2000d50303040342d807401455142c40d141c0640742c1d201074151a0075140d840100c4070014904210070b03d171710380c4104500200700b03600010b40d400c0982404070b824028101004001402c04e4100c2100741e00581c0700400140800c8a00546c010b1408540c02402e460700c1801c1e513030f030f0103444000042c001d40361a03030343c003031209007564200d4000341e00a6402c000c20030460000452403d5009090713456000105203001140d0a4405055a00e041c7e402c1d941640c890180e0390900c02401114504d501039018280000c058904096038002c0d0343c0d200c14850102c81402c04038818104e40c0c0e071a60100703442c0e10b0040084860035251820745851b40100000f05128010f054030026055407030030700b40c45101d034120348800c1302c01d41251503042c156a01e240040300c84010440645003081804401c02c01d60301015903584401c0041c080074003210811a41103101e044c2a034071410081503554042c1107058 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 906968282 1250 906967032 906967063
    0x90b01020d080a0e2d210c120d061802030405060604150305060901050106020d14030c1602060d060e1012080c0f0601120510051620010c0c120801050102 67
    0x242d55a20043c44001d1110064010b000e0041c40810400f408100081020311650561001c01d43c1c4202c40c4841d649442d012000717a030310952140046c140c0d45080019090000003c82039034410301c40070950070360941c0000d200c1d482480d5150018412100000c15540c05110504011403843c1045c0e25117a551f541c0041c80c251040303440b030b00760280b112030004d04c203001036512804482e2142480c1c1e03201130280000740100310040c1704002d10110418400d00032078040c0c080301000a4995200c0751085d0300c0b03da0010810a40364038041c042c0f400140c03100d00040c484075001e414001086401c0035041405213002405410320131500010a0000b200c01c0702e42c00700c003070381e10825aa603140c0d01220494104221444042068042d0030b00014047c56905c00d000d00c2c19100704140d5040c00001100b101c00c41740c0036a6103c0005506080c554805800b4850b20581c0f9101448807402c003407003031000e59087d10a00d4200c40009524002210200070302c6d4050380c0c020340d0321801c0c0f1885d550306120000350f40e0302061111410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 906969532 1250 906968282 906968297
    0x9080c0f010c30020f19030504031101051b010e0106140307090f0b04022a0a030e0f01090e071d03070e04020d03030608060f01081006050f01031a0319020901090b01020d 74
    0x319568003220352064000c19400c8980c0e0f4102000c000b07034480b040350060860501a40c035201542d0200d14030080d02070b903410b803140350425041d40c4500c06801182e2402c181030117400c00c50f80c05d180c240114080744951203040041440d11140740e00383e0070b40d20540e00c0030504482d07101c240c51a03550b01240c5a0250f0302100400185558119100c10107010f828041c29045440015601c960196a01710160501800d09816000c40140039030350f60b840c62495009400550003c540f030105150455981003080014504400d450f0b0302d64040c0b010280c002d40740400480d8080c00382d051403094040126104800803000b83c8cd003680b41c907e1009107804000c0009100326480020401054080d5001c107000c0d0200a08075515440c00c24108110030714280103440c0d003031254408140c0d454005025450540c3d1029007040204404600190054a04010001d90000c02d12500d00d01a49041011000c1c069600c50541c40415490060101e200c0f410b8002d003c020342004401d041c143d8000800d0452003002d0701c0e1050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 906970782 1250 906969532 906969563
    0x5010c0c030803010e072007270509060105190509061017130218280e1c0e0117150a05030109030305060f011b080f091009080c0f010c 59
    0x156034024540004003664004400400c09404018405e0b1013010161149420400300c800e103140d4021403d072203160381340d100c41014030804c1240051100850b1401c40100e881f07800c000c3c2c1010039504101e50342a820360240004100e180742c82c180d10010070701c0090201e5050350030200030503140d00d0700030072041c0104003001c07410704102d121310080241043c0c0d0100941d80d904010f600b0b80c03001ca43c20b2800340c1c0726105c07044004540d808800407081c003406140d10302418251030250701d88881444203443c4000c0d59030321101130ad101740052050600090140c1d0700007d00300c0d248030014008020310b494160421a800890001801d44040b4081d041500d48400c512145540300000302d9140b4640c200071f070154207041c0032030f0800d90075803c424000c0b4004c507410045000c40b00300440f00150301c0d80c40c820320b0321003110840011600180081140840c21841c4624002e60310001c2908200e03021802400681c2170314042081c1003007840208444a42103074860300769030b2803000080014030f01e11000307005041040b9006 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 906972032 1250 906970782 906970793
    0xc0a050f07050303010e150d0f030e040608012a081503010f061d0a110403110303040314030c060705040f090e0a151d0606010813061e09110f0102030405010c 69
    0x1508031014200105541d08010326059440f5003082c4124091241c501c40401c40700c04001c60400c0c101400a400b94442c09119102c000c021060001c0503420f00108000052680d1101d0140c1c4001d0305140001084110001040e001c100024500090701c01c034080c0280c0750940da001e0801a00200007082d01842d0741c10340e40010340105040301041c0e0071103241c1900040e4011850b41c1c440b02c40c2030b000140c00e48039524104040203990350382810400c100c03010042400040c83c43d6104003000d10010301200d0034a03481e035036000b00400c1400203500e0951b2002c2071040f9498000c110043c0d02c0380c218a803842c1442d00d420716800040126010f0100b445803100c101d105840b00c10000f4807050354115506440030004074081c00002c106404260303030300070b03013500107511100800a0014000d0f8012f964444580d51071810407144011350540c11580c842e1101800c180d0200815440c0c9120707429400b000590740542e00e003c081c50703424040a180a0a01020901d0740361b070300401650708460b02801c0494000e03030207251a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 906973282 1250 906972032 906972037
    0x7060c08121e130b070513030501050c040e13170a050c060c03060411190e0d050d0e10030e0a1407081e0c0105030c0403060902041b08040c0501050903060c0a05 70
    0x4059040c9081e030400c07003203403080d11032036901101c1d1480030001911040c207442408811024042c0040300d03800c000c200a42d00c954000c20400c0300c102002c400140e00d82d69038609590094a44150b11407012505000194040b5030642c0c01801c1c40e00310f548007500c1540e440184210070076940c401e900300030501a038414061002c944960900406540840c50400c070036820940003680c101d80198540080c8650f01c0e205c3d40c8c1110020a400920b40e2154001c41c031040718465158030b040360300081c400075031700e00040080020903141d10682e1a80319a04591106100c00540e030f5400c0001058148101c0b0104400003103500010300740c0003640c8400e40300720001100d1400c445070380410404c1c41030705e95900d0031600503039109808035900c2c0706035051582d99200446083c082074400e01c400c50800c02081001130b5030740d802407070020b10240c8007003004111494228540c80c0d42c003164801040340001003200300310400d5440c03400344c0000d0802d942400c41c1d240c0426503501004104040050300080d102110a008005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 906974532 1250 906973282 906973297
    0x406050406140a140109140609040611030708010905060906011d01021e0303010f08060105092a040308070b060603070c0308060a08030f1809130206130906150813030207060c08 77
    0x14002c8450400e540000000c1580c00010b0302520924400490a0300307550080d03112041034500c1d0940a40c407002c003000114440079108a803a10340c0d50940001040c8618065031042080da11140b01541c5882500d4060b40c1005016030305c03c600702c20400095030780003145060314200032505510304a140b20010303031400c620070402013155400301410809040300000110b05980503041d0740c01c80343d84d880344000d685450078061254460300d10340000e12031444900c0c407010244c29a01030f0100040b409802c2c880c5c50340c4030b42c109441081c0006080c0f0b003400301c100d409a0f0400e0041e0350003455807825400080050005000c000d003001101804198165a50b903902e401910b00d071001e03203986e045d03081450160350340920784425055082034500000741c40e2400800d8490114010b900b07400100c02c1d1300700111940030148140d00e00201c0c0001040d8400103100b100050212118101c440040c0e0303000141c1210002081c480c50f44a10ac160030300080e501150080c21140c5900707041c0d00c00c80c460300d480e071143e015001303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 906975782 1250 906974532 906974561
    0x230f0d12030b040216020415030209070c1b060f02210f0f0c0f06100f030807080f0d0606030c02191104050403050c0d020d090e09071e090f0b0a1d0406050406 69
    0x1a01004049148905c290b2040c070071142046545441200b2208041303680c40044c0d0710200410000308054000e07000c01e61814032900c01c0c01d4036443c41031800402c14030290443e2001900704803406803083d07010404505405030240c4030409100341040d4882c0c0f14850900b400b4142d41010070154a10304647c0d040c0c032248804981038400d211103103032803255940d00841d05035052040c01c1d100040c003200d00080300404d490304a44000e01d00900c0e0b44440f001340e8041e54030081c008070b00304225801c0c4841449480081c00003540c01046407800b500000b460071340da0100e195225109030742e0782400280c50030502c3c0740018085c0c8000c103040d652400c0c00c1e00d09004144d046012402801c551400c030070340c0804c404036652079070b031112481c403502d410400c400210222110030480e40590382c18841d103070801c100c6512a0030006a026440c2d0340b00c40303030241550b030307200749c1c00c2000d5884000070141441c1c18000000544640520102c003807070800d8070100c18038000751010781810781ea0b1003c1024011030b038010301c644c0364061 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 906977032 1250 906975782 906975787
    0xb03100f09020103050c12010e1021060e12040504201201030b0a14060d020f0a030312060e101a090d0b0f0108030a0e011b0c230f0d12030b0402 63
    0xd1103014080c046605049002030b242c44c00251240314190300795001e03c00c1b50003282c80c4580c20030354852140e42014202e10801d8000c03420000b1416012620102d000c68840003014512440f481c0c16815030700b0b8803180c207900350490403540a00100c0101617408a81040b00c01240b640c44903100d01c180100d2104a160f9400800560507103501c0d1130300b083d10b04880c03180052003199590707014400308440c544100c4ea82d090007203074080f0780185002600c0742001030005050040e00500c440000c0d00b280d58a500890114010440b510001c20261007090000d201030540344c0c00625103001d2020091149000e03203048001c0f010319a0882c0009501540d1007840050014170f50481c69050207000c540c41161141440003804002007180100030055541021560300ca1420703014000c8015103015480ba01c0e9110071546440010020880c1d1400402c002c1890342150640c00c01580d40c0c0740309002c0b010564502800c0313a600300403502d40b034080e41e000f0031540007140f90101c410600401c0700581040400c00da4854000b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 906978282 1250 906977032 906977051
    0x30612020f0d080a0f0e0f0904080d06260f010509060106120b04112205060d0b011106160914010f110328022b0503060118031220100b0310 61
    0x104802100c01580c80303a40240d0706c00402c000070590114a8181c20181c03140124002819a601804400b49030503c0803428039180c00c0f40d600711080304081c107005c4100f04540c89005074818480154148038183c0248540d00d032034140942d4903001031140c5803c00c1038010050109003103aa0003440300303200042090210310302105080c2090381120140c0d4441c88805900a61019400365105003221400b40c50035080c00241d1b0102801403e4010390316060010003640810101000d11259110f80601c40b1401506403c414004011045940010b1290b41c54409888860307038121414451039450f82ca0402460119003c0b61400c5018511031803184c4000d00d0500060111144528450000135500315030018065480e1103520000f000000301a01c0806010540001d1286000b541d01c0070040c10202045068007800c550f8141e03099105403058a40b05003034011295002983c400701c61025a40d13070b05047c10f00800b903521200c0e90400030341101d503510f001404584042c000710030310300b04041040141514 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 906979532 1250 906978282 906978287
    0x5160b01080606090c0c0601272c030a0e062113150921260106170919031101060905090f0d020604030f0c1719030612020f0d080a 57
    0x7515200e200c1c100b0b13040041c3d507089041c02502e800307028880c000c01241e407030942c00b84065081c056000c1c4a81c03440c1c085001c0448030340e000d8075001c0219812011000c49075100a401c40c89541029072032507400c2040403811040e40000c822122610882e500da568042102e000076032682c0ba40110780d440d40d0b00c00100302002e1040680510fa090140d43c0040420b00c0caa9890b00c1200c0b580c01004004940740030340d4000c0c07602c502031a00e19855050600666140c40c41a802e05114a011000c00300024248014400568803035096041c10280b000501c00c28103084000d5501d0b624001c00308219650144c804a00349880790b94031031010000b03a0000c10290351914840c00c00307030004441644061007a20040554081c1c0000c0c0310944e902181d024201c42e40b140d0368100c2d000c88880e0b424100700891040054085103184000081000e4041c1ca1160f0318000341c1004d2002135030950600c2e0501d031805c0303010004117500b0303481e250045a0480d000000a03d00f01c00291a941240e54094050328020940c509980d8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 906980782 1250 906979532 906979543
    0x3f0a270f090c02070f1a07140a080415050f040e25120b0a08030307111006062f0601120609080a170c0403151a12010605040f110a05160b0108 62
    0x800380e43c03c0e50070300360b01ca02e222134060a40703119124210b060a8280c90191800c030020703000c00d521412040100449116140d8034118100b84166078020000904000c603222034180d40091541c24102141003001911854410b4000e911802ca6012480300000b8000711800a03040d143c04a85034401e000d54854a500401c104004c80500c00114940390b03814110b031801046370012114880005d41ca59520803408844420b4518074107441d0740302d9001c1f410340c03502c040e000b50380207401e00386e0b80c0d03000c41c0b0701c0504144038500c1e0a5030400c8a01021105003513000d00007003801e605417031507d1004511000c00d450705800401c4242000b400d18240410080d443e01c1d40f2000902101401441129490321403440f06246807140e840000d000e1200c1205841043d4029003010090600d95000b00c141c9460b0344001c10203000181c464003003d659034081c00d0040b440c00303204102107030901c54010840011121071044e810b20174014500c051080c00b10304030090425207442e00100c01e03404140309081c4d5944610300b580c2c1d003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 906982032 1250 906980782 906980801
    0x140d15060f050603160513080319120509120a0c020a080d090510050d200a030e010e010e03040e0a0204080f0a020103050c07050c0d02033f0a270f09 65
    0xa2807000c0c4005960300e081d0003138a0040d1008003401c24030800401066980d588036942c9811040d009501c0040e103400144050b0aa182001141c1071a036940040002c06109007050160340d03262900041c000694800555130b590301ca4001c031159902c0680d0442521954640c6000135801000c0800c003041114000ca8a40507406041d182c00c04899207036010041d00c1c80080e8030341c0300050014419083c2d03c20864000d407512110009504d125510f40c00c1c0011070540c850002c920209466003c50341007441c0911590304140b01c024020009101810340554881c810380c85584640c09010300856102e509c140c0c1180e004014000442c0c0c00c00e1101d0046a0303c0c2c10701c0b14800d81c04646800001150340d681c3e041110399541e480700141809244200c10020079802c54001641c041c464a002043c80c2c60542451405020240310741e0072046150404108013403d41d048040c034a1070042c80799000f5550014801000900110700c0420030303505900300801d084042c0c0c2e0114064001d800c0001442d44c203507601003190b8 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 906983282 1250 906982032 906982049
    0x20708010609140a060302280902070b04140c130b0a0801021308010c051c0c020c0306150f0a0803250503030c0a030f050405031806040f062115140d1506 67
    0x12641c1d803118130002c0300c40c1d910000c0d4100445c2c46d40c554803505508d900c40308c1046d402c04d903003070026211207107002260001c0c0021610030b60400d080c04140920702106205c0d51017100d0040c07500090140104000c00c00b04030021114075128078180b00705a48404040c400307043ca0400864039140c0000e200750707440c102440b52034015440c11070300c52481c40c070034800ca680094038a0a84c420200c071401640c0010004d204141c811030084880e189240d580900071030f0b000c0d2640e2100b0742000701c3c400c4200100c20340110300785485510100400c2200721004010342e11800b05004108804001d455124041c100c0c00d02c800030024040042000403400000000e04543d48440c1d42c10003c059000c03401c2c904544042e240500a0350090086003801044040b6180031080003620384c03414140d403400ca4040f88025038000c14080707074005511044c048100790407808003020190b810b111010b04e0440400a0203c98059858100c804540e42241da03103030320108036003007603001c4840c40f4810081030345400201110300a0640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 906984532 1250 906983282 906983321
    0x20c1c03110a08040308030a0f090501320103140a1410050a0e060f100e0103050d110a0b060609040603050d0e01090501020a0314031302060f120a0c08070f020708010609 74
    0x1601e070390002c1d900101561200c0c07094075103421920744071041d070401801151169102c40394281c000034240a0001d10310320070400032640009000d200314403000740031007030401c90450091200040690310704090441e03070000d100c0c07001c0074100d18030790741010381139400502001d6000380302800d00c00001504182d03089840e1700403c400c4e11019450b8007544c1c4801419056036101002003190404882c0a0542001851410120460f50b03498a12200c160991083d1215017121045400a94001049440754204000a0003114110759104107110700c010f0712907400780c0000702c0e40c040f06031550740c0110059030308237048810340d05400100030100c1d040c112250b07000613a9a10009669400010941d020a50549542c102d42811514121058000a18105030a242141c84a0141e103a4000406030142d20704c0c1d1495440c036200303000300d0601001402114206160281d0b101601d94080d4095030002110328040e03254003480c2208a05d02410768216560075440d0060004640410b5445032840c203031808003948 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 906985782 1250 906984532 906984557
    0xb100e06060403050a0b07091e2c040f02030111030405160e1b03250207031406070504030813030b011202040f0c1e1809021b1c0c03020c1c03 62
    0x70107000724071008000740d1011481c0400a0351108004d94400720341d06d480c85030280e03118584603c408211181c0088200780d03070014480c0315500340007030f0404042c0116200c2070314000000c8445030040208003801403480c84d4000f4086560a401154047c0c50380307001c29442c2c3c2440c0c108261109030403082840c0410001800080b50301e5064480761240c00301d8203940c10b400ca080d6581c0629540007e103402c40403581e0b003141109060b04030340f0000c00700941b035004010a9096140404040c503039403c0c02c400345d52004041018140e44081141c041d25401710b04940c40310f42c02d02d40e218896040350001450141203500108a00b000b0026659503940229401d2000e0001e0080e101c01b2502000c6096000420000d1500385510040500c0320041490b40741001d00144003400c0d0050300c0400390040d41300c0540001d025007005004501c003105418105010f06060940402c0900710203203101d514070b051012081c148000c3c58020f018000e1040e0001d040c8903070740380308161010001640d800e011008507011007a1038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 906987032 1250 906985782 906985789
    0x2030f0f1302060a03150807030302030a02061003110f040b0901031202010c050903070b1b0f0102040906090c0e04050a0e1f0507020a03210605030f0c09061903020f06070b100e06 78
    0x40c8803190007400c43c2d031414580d00822009030180d9002c5008404034a41b000505960400c40000154080c1c2d02442e11620945002810600040e00c0d008880c860720500b440400c40020916612080c1102c895569140c0b9001180207480c0000070940d00c0034402c000001030018031a21721141c22416802000f24055060b400c0d07542c0c1c000d05465070340541c003141c01800b20342d60a80c01000680428103c01000e0040401607610b0100c00140310070044c1d40108082200401d2030161001412000c0400c1c8150f0100580040c4245c83c40c1c030081d0310494848011600e01105580941c24400b6000291610850b0f0740154001f1081c0c1d480d5107045051504000840751b600c08540c41c1185603040d80c81902180d214082e5600c2103007074011001100340d8450000840d42d804020003210585010042c0000d005203d0400840320310040089000769408002c2c540c034602c1001c00d00b82034070f9040764a0b04178100c424002c04d0301d07400341d00c0005050b900054188804c107000e1115800031560320400810160b5a090b091 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 906988282 1250 906987032 906987061
    0xa0e01020c010c0c09090f120c0201090e040b061315062105010806010b09030304050a060804060f050c3c0c0c040207080304260301061106010f0303270902030f0f 71
    0x6402d180c000c050500201517250003d04c5120f0103001062091200e9440b40001e0000c0c0c4040d010128082414070305c01c658028507194000c0c0f044480c00c81c558030703240d200e0b01401c034001081540b02e050740f0f04084041c000c0c16413020328400030300001088807540f0b828000d4681c9881070001090010600c0030300d540e0800c503026107816203100754007404181c0d181214180c0160048c5c101c1c90390500003800042185e45507624008002d1030076503514080e50400f0300b008170031035850900c800805800d00003041017018400c81200c0518940590062003410440388100803040c0040040071450749409a4440441511010708100c020410954010103803034410801248a5a280101821001e0000030041803c0241c2c4a03400b07880c0441f04140d440d450350801040780e000b41c11a0001c22014100b150343d440302000024090301d4407c82c150501411070314041d00c101201b05070a8005181d040160244030964240b48004040b40e0a096460782401074900104c0c13042110a6200082c141c0300003003807100480f49 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 906989532 1250 906988282 906988307
    0x6080102071101200607051908040209011202010c05010c200102090a180e1f0c090f12080c06091c030b0a1809020d060207030e030619051b0a0e01020c01 67
    0x1988000e2809240065541040c40c0c455640c0e001c9030310707a242c890740905110080c4906c2c04c0da540c0a07070311a01100c5110712032902103054020003000004104c0140c4403140600c1c1550940130f9080c4050b059440100c541a880325001400c5508045a0798603040d04900309160008200d82d0040405504540030780c01c0707000702c070002a8001d000e41410015500285403581c502d11444002081e42c07244406400d2a0071071110440d4421264a5440400d00c131040c0b080002c43c01040c9401540c00d86041003000501100b80a40410040e08003400c900b0840c4010444041003a140241d424a15003107004640750b2041d4603000d09011800030f45005080c1c03083c03050080741a4020452007419007080c403c54684441003650785440707036a401d98207002d692121510300515210f100b003da92440c6c6c500d0b006080c0e2424201050003540514203010400e0211602000501c40d14140000c95548107a8250b6908503038018000006c1d100056811400d0340c07000005030021001e07000c8610b86213541004647e601c040700c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 906990782 1250 906989532 906989543
    0x1111215031507050a0c05031206040f060506091215040b070906030e0a0312110708090a0e04151a0a0b18060921010b04060e07080601030209060a030504151104090608010207 76
    0x4024500030b0014141715501885c2c1b580b00c1c0d804a607610752a59100b18408940d401c868000c001e62880c01d03010312a420807010300c00384407040c80c02003c5261802010038461044440b2035007408070403c2042070302160f4181401028441c2001d040a208484055840e2000102e0340c2a0114005009004800c11002000b004006101c82a101200c0134014403031082c401642703402e6003119101400001e400e203640140c00c515a900c1030a01085405101d0340d0144400308070010410010401b44c181c2c2400648a8005c0804c2c0d00740b440c585405421203107000564080860407000c0342c80100031016000c280503a01a05560142100420000b80a01031445600c100e11140320651604190101c9030f4440034400003007850014540005d0650320707680c01010001c0404002c100d082a07008a02d00e41201003804c045180c481e0300e60100e1220301c64401c0344014103840d10003040c200401c00c0c07040d44960b40001c004000050b0360801c80c0e0600d50291150040c03144c10318001048951061003181e15550307100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 906992032 1250 906990782 906990823
    0xb01090c0206100510090b0f130e10030b0901020c01050f1909260906181003050432010906020d0e0601080703030e1c030c23120c0111121503 62
    0x2808008102441700348042c100041032800140361010b00c4060003801c41700385072068a402e0740480b00c40f0503900b1540281916011207050043e08540a10040c5c10703650084c10300c006598409136028003901c0f4610040810b9884c20040041801a4032035090260013070760030701525541ca40b030419040d10fa820f60058070b0381004641d08a02aa0103041c06100902c00001d482c1c10b0102000000703403207400c11103002d01c0848100c00300103510301c1c0c251002c1010000310b0802f00003506054070780c0042480d075180380c10302400d4888480c1c85101509044c2e03c0075099940000d212810b0300c4e181030b0004e504031f501c8250300a410402502c2c1e0360704001c42c032141a1651400100360040c5140c0702264031305a0504010b8000c9000302c40c0718045245141c0200710349009490741000d1460600c0c6c00b040003400090140302d10104040145500c0c540801c42c64100a10080300c50784960700480c038940140f050000d002c0c800100090011600122820b0561041c03600b18001c020300c100c02d50900d5190741a40102034242a0381 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 906993282 1250 906992032 906992039
    0x30307080c210f07031b09060c02011103130e060a0e0a0f090f050d140f16080405130608070b090d0b101203211107200a030b01090c020610 61
    0x8503005441c4070031024080c0c07410350101082c207048050b030540d03041884051000c00c2099054050007800540e000c0c800c80954004140b10000388800b66901a85040040318084082560700c101f0b02074580e81032160940380e43d000c8803112004851100d2061400311001617001a11501e08511080c0403601d403584140180e0341c9000d8102e00902c80311041100003580d4490b21030125900084000300c10b4490001811030306082000030704900006030740740e1400c071001c20140485118000580300c84640c114510038480850380751100d071130300994000315001040a8580d19841c5841e03040301045500c0307001907560040d103d18035400c00d072090803110703500300100000120000d40b01034145540b0403252030b0500c0c82d0729203803070700c01405a0a540054001580100398516813002c00000120300e0481000e0420110302940c070141c04500602e03401070040014132042c0ca01040c0c850344800034004006206600b05a140d10300688418002c4c007030350340c1c1c00345085241c07a41913000141c254000c84400a01c020550310307 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 906994532 1250 906993282 906993301
    0x21602010806030a060903050a081006140c011d03070204060e0c07021c02060d02190905030d0509040b21060f0c040b0906071a070210051015021203010807051203030708 74
    0x1c06441c0c20b8040c4940703005440461460b100d402e203924829600e050340c41c200c3d5071009040650192041003001000b80c0700700100c40d0001804003d4004800034079854081c44900d043c0104285010302c07c5480c0c4000116400d418084020545544210760420405031100466011b951040307c0290b4580400c21000000d0700e40740b030401d201940001ca980c0c15111041e404076596800102c40c2c401d0312074010600f045c6950b170140c00e000c60304102d490015403c0b8905000240e8503805410f280003413003000120306059480d41d401c4034845200c00380c48000101601600d181010080c0102070040e0b0146130007082c00c002c00c1940003401000040308503802c2c10700b043d41a16030f990181c800305512800800c0000e00207500c45403c4000500c402d065000c04d4601400d000e0300348004c004203e540341e46000e04114154036001540710a9a10344c01c00480001d00101059282c020803070205042e0881c04000002c94201c0001c3e8001607a07000e41d42902290864000c1990760b000542c1d071b000203d405540068010715 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 906995782 1250 906994532 906994547
    0x4030f1d0d170d1e0501080c01020d2a080a0807090617070512270d0512060f0d0c050102010b0411070615091d010510030b040b0406090c061d030102160201 68
    0x415024102d450528003c2240703007140d18410101986004c42c000da9000400075200e25801070500300701a0002072101d00000791103d001440200c1802640c00c001c002190021103044040c542401d10740248014a0820b030000d90040014280003901440c001003915100340f17031030003c17100583c40c1c0f140c0c1030f40345d482d900754400801424803042041c01d002d01008000e0004615000d485543ca03504200503d202004411101040c0c941e0104d62121001c6c1c0c4800b0b51050407500d00151b00c0d0039215a9403100400207101901d0702c41101d510032901c0e0fa480c402c1c02503030840e000480c0c00980082200310612824401a0f900607a1503810707100042c804107010402c4d81d000f14401c06c0c02c003c13810b1001c98540c2c0b21030742240c01904485401c540119000c600442c0240b06490300031000b142d0034a01385146a0322954140d4000748010400c000d0400402c0c2085400c0d00200b0140da0300482810803292181e50042c08800044050811551002e07050360b018203040c03084600c00b114440d1800a901065001500c854 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 906997032 1250 906995782 906995813
    0x5030903090405010b0c160b0f07020d0b091608060f044d0a0e070c050319030b011b05030405040c05070b04080703080903160b04030203090904030f1d0d 67
    0x60008000c155182c1c0c1d2544103071070103480d41d00201510b4140000c0060b26280320804152180b80d00c0400511181c281401902e140300e45c03262403290303100203d20203d103050340824001418038941e202405918180429407124404500341032414103695041102d076241410f4656015020320300000c80d0214242c00918200822281030b800c00c0d180200c0c00c102c081d03c541da00041c0c0c501a40f140d1070071001c68803190400740c1a108840b5200e4007414100c00311305481e03014040c1002d00400d1910281013060071320589040d10001d603034200201c05423403805005032152030051800a1030100e103030400c1240102007007e180381c00c00011420f01d8100410300c0700511601400009105050000030001486510b031544520b2107061219201c004903d03011306021b202500d109a036400900024000132200d901400307030280c200c075041d401512541003e90075840381100250304022150100000e0503088801200348143c69a201d4a0b880c0200301080c0002c0d0210141561200002c030045010860403120341c1c910 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 906998282 1250 906997032 906997051
    0x14120c0d080c0d020c01180803150307030203030405060306031006030c0e070c050604060b03030706050a2a020615131a0102120405030c060c011b0c060b0103020c0a0b150307090b0a080a05030a0503 86
    0x15204d18003d501401d40b040c040884021000100b0000c14030ac036280e00a2181200750300078021242540e00203a220700482c0075441c05001c01000280d20340e03404210042000100070760801c543e030388901f0000f0350100c80d0f0180351505104100403504180c0b0510031071048941090140c8110344a070750b178440160107110b80e003c0e858030041c044038001c504a803203118019030100c2c00000341030128041e00041c0c1c25800748180b09900c0080c2c410164a40c0116070b10754044000e040030f01d020311030140007030080e4815542c1d4040c207c0c5030288036820564161805603512800b41c08890007003046194000c0c2c20312582c014250560001d4015980d0307800c01c9405080c2c019051b00020842c2001050014108e000c0040342070000740e82e0381440b50078044030b44118a4110000e00e400e510f450800c18846965841ca1400106034110420010740c041500b400040d26120f00202518145aa92100c80001d001450940c500c52401c0101c00107c9072400103508a401d030f070080145040242c01e04c0140d840d40c2004169504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 906999532 1250 906998282 906998291
    0x60507151b0305011401050f0f03070c060c2c061e0d0c171e0105060714120409061e0b030703020903150910062114120c0d080c0d020c01 60
    0x306900040c40200d1141d103540c0081c0a614003146aa216404c54100a043c01010055070b412640d802c8211400c0c42c03404060303250341c0e865080c0300701d803882070040029100318034004a40c407181c2d0744802d1909010000364103041c101100f441c081c00600c8500e514140c0c0c00034042010700c8003000b500b5910f403038910401d80c1f5282032040c4c4000d00400e0b0381c03c485007003001450303400c0c034800360460401d20540c1114801c456060303400122404c12540c10b1041c01914840d910109410303040003207540b0400d110070759001c1501e0500b0714000560f9556002806910030460a12001007000080807640e03040d040100c283c1c02520600d0000d90034110752001e011b5904140e020840f0503155242013042c80818050300e0303c004424a401c0f551582001145102080c820b402e11000300510314810031a008002542500a07a20b030031649000642420b800c00ba03640c0500a00b40b160308a6088100642800e03030368502a101511174050007200c0c240022140880e00420038002e6585280c15035001c0c212608a2800004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 907000782 1250 906999532 906999551
    0xf0c0604211403030403091203050a03050c07021206070f0512130c090218090a0b030714010c05010e0319020312070c110d0f0201020c01091a1e03010f0602060f0106050715 75
    0x1007049005100030441c80d40f002051004040e03000684030700401d0801e45120700500c06a070010004c1c403078005e0b1681019107510100c2c0c029082c001c1211211603001f001441d071595010b8180d91641000c403000310100d080140403022150182d0700b146e22944400075a4445aa150075a1406c00c000449051300d00410401010681040030720081c10b10302d8030381c6404c50706c956900741000600748009140032951400c1a0540d0240e403130010340202910089000e01ca25000508012200d60103001c10240481d8280250b46600050120040240c08030761441450300f08016101680d0703074840c0d15040c0b0030442180b00011591482080c0700705180c2c0c465115a4454000000000c40c50342078114290740035541079000004568040000281c010703070a09010030490329082e54030b00040700400800a01840014003404251001c80006000c03400b0421580c2e03c0e540c40d0030421441c007426000311400b510842d40400c041d02e0000207854104c442544d81e46103031991a649035110100551044846580c480c1001c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 907002032 1250 907000782 907000793
    0x20a0b04080a180303030209030d0302251b09140903041802030615030721060f030609080d0501080601150e060702041503151e050903070f0302150a05090f0c060421 72
    0x2d074004c5001c0e54002d40c8520780b00c0d003090b003030500a0502206141c41004410140c000c80c80d10325a0243c062600303e6a000c1803420309038042d40c80305d598078442c10a1582c021032038401560000b0103849101552502640c0c3e44488503560b44503500032030135000680d900c9800f0500d00398008590242d0050685400c080c2504011505a001525a4404070340200d5207003021243e0301810034580440340805101c1c0324a44220150960250f0102400040c0c84440050901143e0700895400703d81c40314040003d036075101019a11104280948070f10f04d03441188074040588900004032448800070300003850422541d007044000c190712900210801041e040c008080f40d180000c18120070703960303a0042190764207011640341d11800f080380e00c1840c3d443c020a1040d0b060002007690b071000c5d8044c3c0c412002040905007030745171017124203015000ca04c04c86c04000507054030340c0055018801150454600d240005660340d1560304150402d5001a01404200620b0903000803e0352030700d10031034440071503800f640c80c2d5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 907003282 1250 907002032 907002077
    0x70803041e0b010b1b01200d0617060f07021c1209120503092e0e0708030c011b1106060915040f3219020415020a06050106020a0b04080a 60
    0x2213195034401103840c08000b200c050006030840700840c006c0040420102e81403107a40032402d80313000c0c10b0700089200c08807100560300400141c40b10380c2d85038a07041c911030035083ea20001103a10581a8103888c021420f07007800040da00d8803100740e1840c109001041da50781204c920b142c0c40b01000c042601e0b400c042003c02e1004c0051000d060259072156500d10300303058100d1411800c0013040454485500c4012003a1116149a14000004c0240130031090308107032035986850f085070450300c002d000c0010f108a024105500c480c64081c4c0090460301407c0766410709942908480503402c54540001001501c3e62914101d02ca60044401c03407086990300d03d031000701d0220b0b815440414455070741c40f9000030452460b00410b00354503d4141500e104259521401c040618015019805440304143c4200c0044001c0c1c0550f0090140480260034051440074005d41d6450880700c10b940c458680000401c1491021611503907664100d20404540c0d120b81da02c58000f03500c10a1140d00304212400d003480d041092146 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 907004532 1250 907003282 907003289
    0xf0c020a0203060115050d020d1e060501090506040302010f120f090506010302040501080304060203160606032405060102010e0c060904090209100f08010504020f0118030605090109050601080102070803041e0b01 92
    0x10080300c140352042c50302c1c00c281a00504542c4807049060700c207003030340441101c8103400c0c1c4480142e11200704001c20f002a1003000001000821036080d516200c0c075495001702c017280c9090fa2071a28266589046c86203501c00e07030001174001030164104603040c6e809590102130713118020710005080c080b2407180e40b0843da08400125501c3d081503004206600d0180203042c01341c1707103200c041c500e86494131001035a80d200d805040100500c82600c01014400c0561240c0015600080d41e0907040c00088038100711440052903000d00d6500d03040104006504c14400c0d03c4080c410100100301490200d03040102542140c0300f201d03031080c1c8800c041001601c683c3c0c4018024003030851940c04450924040800003c40c941000c03015a140c0030401016a80e00050b421075404d0a00b4240d1418160a0300b50240d0b140541015007003900b8203051200c840d40551051483c070317004d4002d4410b544d0b26210390b41c1c240e204045016040182c180007040110303040510441e03030030024010544c0100600c0e0f4510039000000d90 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 907005782 1250 907004532 907004537
    0xf0606060302071112061605040e131e11010e06040b0c01021c110406030c18150909060b030a0b062506110c0d08091603052118060d0f0c 60
    0x1c0b40b50403c8441c110350f2013408412140c14103581039040107156501402071198505a0784017481d600c03081d00540032980a01615030420f00c040c501515865008241090100d6007a06d00701c0f4001802101c500800c400250b07c8034813184e10048032001111520120381815500200c20880010300800240041914510403800907840f080c000101150300c4c404030508040b22170030402d14490040b000c80c110340c262405420001a68200300000304c40c550074501032600e20424809001c40c001000c1081a2078000690351076001c001c1d1210b8030442620f4152244104200c414004550b942030300c0c0d00003650106002d02110700785200f15656402c0c824041c02c070301c0c00700c0c0c1d0f1440049052003054000d030000c44d04c00ca80304520344815403202583d03541c01080c0c0d003002c1112000c041900940c060103c10320f110282d190791405282c41e410003544a852881030400e4800107991550b1501e0000c00a6449140480c025480b4009058080c000c0d654400c4180c0240300e82d648c2150b880980c0d45128020f0300c052180d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 907007032 1250 907005782 907005787
    0x9090a0911090408070f06091b0e071b0609050114040309050301060e07120506041808030a05160210090203210705070605090a050f030c060c16090605010f030203040f0606060302 78
    0x741012254402103408090041c40d208040101041050741259a141d51140c0308003002e07a9503080c104000d20f003040c0010400404806200381d0a0907030b03c1c00300305803051800340000c0c40c0c450f038070251242c0e8608112085146400c0c5040404500c080c1e110f80c284600682c0046402440078114503642c4078101c504030701040343e440d070510443c2801d21a9402a0500f07411143d210708041c507025040c0c215442c90392060644900016401d52203e0300070782507000e1041e80000420072545040a11070b0001c83d03c00d4000d9161078005000481500807888040c030040d009009a0f0703800c2204007004d80b84041c0b061380c0500c50040c400310f10701c0c0e4034204400c40c03e660300c81603500c400703641c9451801d00030f9a601070000c104003800700f91401d545007088041110700172214038054503100300c08207042080c0300458507802000400c440c030400c800411041300b02c41311f08082001d455215428102100c9a80c0102400680c0c076040c440c84c518002c0c0e00540c1c11078050301c010a15103034203070390341c4041d0340882d000140082c0d0003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 907008282 1250 907007032 907007051
    0xa09090e010203040b0f060d020a0909110409030903260304061a04050435160201020d11031b16080c10030e0d0516080c1b0405090c090601030209090a 66
    0x61140040005058000b0342c40c5090035105c2420500d805040011001c00c0d0401007130180c0d90711007080000c07680c042d055104c1c460b43e40808000400b84103030700761060801585811294607003071142c141d0300c56054486010407820754a03220b400d640c031008030800340b80410f1041180c07869607402543c401d920450000c5402c000f540c080c14801003c444210340118102010b001c0000c100400482d40015003902200b00b00b40000880412504080d8222500c04d600042210b15000704403040c0034124001e8003255103134000100100d07419075107450f01c1c0c0f4603900b06001c40d500e0b001403d528481d140400d4070880e41d00c14070b03000003505244295402042c141d40f10100c200480c3c240403252010340b12641c00d0402102030034545194480c1c1c281c40e085010021f0028600d982040310740008160b458000320025210004490440e40c1c810034401c5910311800179190f00310b070920b054011039100340910809088140c66074801c1c0040c00c6005080702d4113040d003d115025082e286c00b40100d2042d21000030100c0d15204 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 907009532 1250 907008282 907008299
    0x605060d050a0533040305090f060f120c0c060c070c0e0a050109050a150b130b07080703200d030e07181b030b010f050f12010303110c040b0a0e0405010207080a09 71
    0x10081c00e030141c803d44006607904c4100c07204c1c04503a2186e09418030655910704200004c6070400e02039959036200d40d01140e0007008400d41000361903514050b801c44c9540340c98040c4540c015009600c13410419500036400034040d038032204007030041d0b00d2140c410284c40b00d455061107050110304442c6102d400303542d940100714603070840c0191508002d0710030007086181c950b120359021120305401015048100001c1c030b510454070411156009101e00954143c0301c903003600d03156285910040c1c0c16800035200030042c5000c4070b604000d69a0200701c40d0001c0c525000d044c002500a000d442000e8070403405503040c00a610503807061240ca1032244d42d94005040384055001e0487d2101c81c0b0007a80c10103107405406640c51740c004c0920309a1004c241000c6840f00985200c030080c0d0311070b80d00002480300408000000705504103041c00c59551000043c5c0703a10752000340900c400c40d0507980b81380354000390321601081280000d600a40d000741c0540e0000d0301d8004543c5a61000c0e9004440201c00614410020440c118 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 907010782 1250 907009532 907009573
    0xf010501080c161e1209090b1305040c050312090102120405150c0304031a19050c0409180203031810020106081005090f06010603150b0310030605060d050a05 69
    0x19090030205050b04110003a21030720b0185900b94485403d00b0b0001805228510382e40e5810090035076400c074903229103850400b840310f0544200c000810303860303d00440d04203550b009000102c500a4074501213071041a03203e40141174058019100411581d202007215141400b03a0302e22010750309c1c14107559076070000c002807802482000e03400030050f041c013040c071007683d5501c1c500d003c8180e42d404054540400c84030302070540c40307140d01c0100b0405015201081c1460000b01d9188584224805c071580722074001c000a081e04c030111140001e03031004010038013041c1480d41c40100380006010303040d4141d640740c3e80800d10f540d01421052442aa0194060059140100361111b8000c0203200034001d29151142c080e50f5500204689070005865400203074400408001980204032254226000c950b0340350800750042001031a1b8a0030302000d0768000c200348030b000d02142c0c000e014140e005152030b4078507220301d001044040c2a2941c0104401120801f1410030071043c010a0700134006000d0320125034071401600d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 907012032 1250 907010782 907010789
    0x7031110050405031005041406010e1e090c0105030a27020f010f050d050402060f0714010b0607081917091b0d0317280b24030109020708041703030f01 66
    0x20040100f4840d98401003110060b6191a10003c03980d6141c51070021220040d240c09400345224400001484030f001b4824140103e01c24000305544c4a01051141042c0f08111903240040d4803183e003402040d4440e10007180d0000035141e0000d031401c041281806200d400d03040400b08038840350a014154503000b113000c0c40c503400c00d0a206450780306108020f0300d640900d1001c3d9480d5a0340f00001010764882104a07404030205540c1141d176040e076460040943c00e41417590581540c81c20030104403038100901210416038012600f14209035089481d410404210305560307040060208410003a001e10755000c0c0c2c041c1c0c0307040020300001108070b40d01c40c076010078036452540320f840b04000c201c01183d0032402005424150b40da605504d03580b00a8850072941140d100c880752001c44220b40720318076040360311012061108451051034410360f0104c1c0312000031800c40304134580320100010024101c2e141d004241c540c2c4030711160b605261791000992904141144180103c1e000003040198141c4c0c1e50f208507014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 907013282 1250 907012032 907012037
    0xa0f0b070806010c20040203130507080d051c02250b06150a03020304021801060c03080a02040608060105180d0b040b0a0c0e01050c0a050105041101020f0f0d030f020c07031110 77
    0x11032030202c000802c100283d4001400c1500c000441100740b010084609151541c064820340d07403818504003441c207804051005640501405101040340320000c00d2200e0003441a94031300f800c2803404200d80c9116041c1d1114076522981c200a07032180030480310701074258880005083c04100380d0a042c2040340d608028240c81c07141004403a8a0b8504103d10141c0d0003114151500580381d07525440030a284889040c3c0ca00100c000d40000064450740c005412100b042c425600d40c6400d480c2c1c0751340e20701030740500d0241101207100400040d07d554890030141c10003801c00f01c0708504007543c00d00450f00c5c01c031007044142c603621020000c21041c04103190180380c11001c070341c0c0100141004114010001900c28103441c0c10404001000d40e105e42c800c01c0b4100d0381c03d800030000c000074201072500000c4611002c06050150041840454584030040742003d00d8010502c0503200b50503d02130102c00800320b00070342c1a51590700744280d10b90071900b001800c026522416030781405600200c104090070500d101000c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 907014388 1106 907013282 907013297
    0xa090c020c12010606170915090a060516110c030c1e1e041b230f1603110a0203031806040e0f07121b0f0e030a0f0b07 52
    0x4a170f20766220b1401145407000040e00440701129240e0380c50300308202c1034403981041c240c6541c2c48032000c015581030118aa6900c0200c0d04e060b102120340003611600401d003243c21010105c4000c0c0c1c840c004144004070240041e41e2035411038503e50168803081c0e030420320785d48503141d4803850310300052407901407282406881241e5640f6a29203440f850821040404003450380d000000700c080c250365a002d90001105503056109640c1d41209101d000410003440207112140240c441031042d4691198440403505001342803080e07422181d41c2d1a08004051801641d00204407442d800c1c65641a107044174690b00083e00b40d005503404020010940c80c100030b00103010041440c801c071038680300e00d01c0307203401102c0340000c4600310001484d55144255030411410300841e0200c800040d0341c5415007017107583e4400b0030304080514400722080781c441a0005c08001c8054541984210649007494 = true := by decide +kernel

theorem cover : BRFrame.Cov 906834532 907014388 := by
  have h0 := BRFrame.cov_init 906834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 906834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 906834532 ≤ n) (h2 : n < 907014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
