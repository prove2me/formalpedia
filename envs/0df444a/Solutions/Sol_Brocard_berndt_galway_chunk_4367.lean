-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4367
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:23:39.920023+00:00
-- url     : https://prove2.me/submissions/583c23c8-1e8c-45c9-82c6-25d411ed6f1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 785251798 ≤ n < 785431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 785253048 1250 785251798 785251807
    0x151404120507061103120901060b030106050c0c1509040f060b0d091b0b0301360f05070809030d0e03070614010e1f0e0a153812070203070503 62
    0x144030800c4845101800340302110201c40d502c3d40100c1d4142402000b040a54105018409000001a4009804c948440000b16007030b5120a0720941e154801c0e40040080713034000a0310754414000744440c6107001c204075071000910059002040c01c0744150f86000e03100343c0d580c4581c585251400d034010ae01805040500640b5040d800032200004c0c450103000340c1e003900705605900200c40740c02d00824107541020704114116441d28080c1c410310000b86041c1c80d1062200d000c40c0200100c0703410701500101080101089410018050318210350700501008104243c45c401c021000200004460540685000000b0a0488984641d0a600440780010442401e080c01c180b41c41444442d030506a4020306070a5080c6d031950104080c42020048045240301d03000340c0208014060401080d40c00042840c010403480000280310700f0050042c1c1050007a915134a144140c0700ca501141c1c00200159100c0c80202031603500000d0b0203a002304800f0110a041110020300140c0c400d0099504e0540d000b4112501c6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 785254298 1250 785253048 785253059
    0x903132d030b181902060c0a1b03110619120e1203070e09040309090209040b18160c05070909050309030f15100506090d060e0307051f020310151404 65
    0x3048050b60051400782c2c507200c5403040351201091140702802105060412201c41d40e0910016401140120700507010b030803e100d01148002c0c03126414104c0c400344101d000c60942c58084591022f90081c0c3e40a040203200850360100340c0001004400e405090012000c030306a0049400f62581080058140c041c941c14500344d40b07151409036000d4006501e0341c0300d04c1c4410a0600810000807200900020740d001c40800c0408880e074020404580094008a0115080e002148101e414400000c1c0d020402408000300c0301c503041003404560f8804d24000c1c510506030345415681c0c906900641d00a0b69880f4600740411804200b00c039080007010701540c05000704524004c0d140c02e40d02628944800402e0000340b03e00300c83e0451101030395401080c0504105889042c44803040700301d0022284559a0b42015a603018104040d1200301d2181004000c80d90700307070035a414201c0707007140e820601174014000c1c0a481d1000a0001040d1f544c5c000302d018058890800407103400952a5401d40c041d040050003252 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 785255548 1250 785254298 785254313
    0x180305090a05091308030417031305010506010e240403060c0504060314060a141210090302070e010f12110607030f0e0904080a11010e240903132d03 65
    0x32419400c68103014042e0340e80d400e10450403000c461000030488110001c10020b40844080d503000341c000c00d800380740c084200070b0444541d803042d01d0643d00480c41030312031030812600740110b035400002860022000303146480421001c1c5a00c0c01c11403607a0710030706005c42c0c0c1242840140d50066401c0103040c0030380b603a101005421540a402081c001a051100401411a61440040c081c08000d80080c000900d05444c5903500d62010402e207900011480040d51001e41c100000c40100000540002d4503c0302881c019181c510154003001604940000400001c480c0c3c840c03501c12180140c030020751018071881d10500c12000380d030140c5e522260104051082c11351000c00180d014910751503041515030703600204404984e0461b401010100200485d0492a00c50509003401c0540d1030000714080e008600a00d080480141c1c0d503000d210800305012901101c1c1d100c1403a00808064040e5107440341c11054980d125103103000340303403081040d11020301c1c03034203120380c0c10101000d104640b14a40646a182040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 785256798 1250 785255548 785255557
    0x6091216020d12030504020a06090302031b0f0d03031b0201150b030c0409090c09060506032a16060f05061002190809060c070e0705040503150c1e0a0f030b030307020f04180305 77
    0x82c05100c00d400c010071103d00540c2e44109032f0b82c00500034003454488040c0318500c505540310351604070555405105542c0c941b0400355002c130340310b034402050201c00841071030840421401040110b81c180140d07554400d041d100c0a074140c854007048103503640d6821002c40f0f050712541d030141c01442d180a041d1710034821080b0003a81074528406060120a55650400c8010301042e100701100741aa00c2c01c4c5401c94405e000e03903404280f07144011030700307050782e1807109a0148143d0105444c43c98075110b080006140c540b241c0b5522080840f95503ca480301c4940084d80e42d040742028001110003040d020046c0a000c80584070401d600130503a6940781325403856030740c4804040c4180d130106018a008900341c00e00850940e0165040038009284902c1051001c200c0300c280604446140201040f0712001d200c0c0c5801102d000b13109040c4059a104900c81008011600d0856000c04052400000d542a65400700407107524175011078400c01c1c508880b00001d80203081c0c0003201e000e6181e40d00076500400d6004405032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 785258048 1250 785256798 785256803
    0x230a18060f030305030a0902030f0a150c1b080d090f03030902030d0e061e0c0106031a06012607020c12150a050f010605030901060f0308030906091216020d12030504 72
    0x14032030940d803505001200c80307603804010080b45090000802c5410706501c17404143d07000070100d650146081c000c403401c0449056040d10902082600001d601e0494001c0b501d20101034501000b046151800700900c0e201c1c040070040582400040006810010f034100403115a04850000004041740c40c0c003500600c01d0200890080c042c0d01c903034144090040d558290400700c080d0085203805078603000d071101c04c1c0080d280114280c10502042c0c54007182481031201070341c451501919080351003080d915111100078065410460f450b10807107031103030700b4203c00c0c2c8141d4513840309080a078462035004d9044c04040608160400000300a405103040c00040c4407104e000c014450704901d0700c41590100c1512403c0340c20040014240b00100b0855120b41b0003103034824140000011309503152031030541d045103035903c1a20100400300074408483c005128242d0041008001450280001d044442c0d182c00340000b217810b85c04d0011041c1003075442d0810605891a440081210000c6030504081c00030310003a00c05 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 785259298 1250 785258048 785258051
    0x10120603080f0c0607080402030304140406030c083a080411100801090605030f19020d050105010905061f1409010513080a0302010b01020d080c0f0d05130b1003030504230a18 76
    0x4254181d006d84c807501d01950700580039600e4241803003415007103055000000f42d002a80c80d00000041802d0540c2c44028001440c090f1850101003000101d01070713048009500110448035807d1201914150552000725981c01c0c1440c690b40c0300d0600840050500d80c0158104141014460030a50300405440c142d8543c203c0070820795441e68281035540d00000640d14190b400302d000b10b801c00c0002000b0603c0c07035100034001c400134020b80c1d45490035030700280d00c2400391a450700140095490400e401100300032000182d003d500ba5a080010306001403000f122003050340016000405901c07130310465030580707400c0403001c0c2481d81c1c4541c000d564a14076042600103520306101c40030f066101080e1907100e44000d0b44c0e500c5564884260f02e0105500500c04140214410000307da40521b060060314441e655408004006006605100e07890300002040d480f00c0c041c160800b40f00094100040d64203680c040491540b64499003020700004404603001564060421070001482c1c03a4110703581d041d4000c1c00d110 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 785260548 1250 785259298 785259301
    0xd08070303050126030414150412020306070c020d151104081e030705101107020d0803180d0c200901180c03020a0906030b010e10270510120603080f0c06 67
    0x19030101c038014603005603507217030810401045000404003460000540042007aa410b2803d584802c5031a401a03101c00d000940c0d081340b1405500d0113010440e80100300c0d0034105030804a40e8009421002c2e282001002801d6041c160381071002d60754083c0706821030f80c00820b55296100c1d200155101040c91200030b0045201e0003c20003c0d8021083d2407109038040001c09103001c6003035000014001e100018a035003d4280960030147e070302e041c0c06000007402442c605a6030300b04119041811500d0010720b419603400140d01840c038070307404480c07240c509030401d50200c1301000c1100b02d81c6220b107804281a901190303010000c2041e014244010302298013a1004100300000040d040c1c05a0003000456001300f01002000c0003414000d0308140c1c030504051621104c1c481304c0400180c1041101c1c40c80000051b0481d811003001c0b18030340d041810740414000a4680700d4a84800540c2c00e882560500003044503a01c401084000036803c0b0102031076000e001d080c2c48450f42c40e07070011950031807003980000c2d104000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 785261798 1250 785260548 785260589
    0xf060c030216122117180a08040e090a0c14060408060c040501020618070e06180a15060311040614071e02091806010b1309060b0909010f06120b0d080703030501 70
    0x100703141d03403020740764840b64007151709465850303a410802410501c1c0001c00c19402c01042034144090f4400702d100d4039241d030b1641d08080031703515200402008413102c1d83c030200041000c601d81406140403509031054042c207240041020612501a40d40065410f01c1808103102c2c0001440000d0820356000703a080303481c01c2c0e90f00840071a600c680446000c0a80d085204207100d00781d034174120740f980a6000742002d0315101c50342412051500045034500784883d520510f24403005204165071004045078601030003a440500041e08584c45144190340502482c0e04030504400140701c1a03821082d0440c0a200624820b280c00e400f82e40d404101c1284244000d1001900c5164200c0050403210907400c001c00d410b0b03081903600c0407240d004d14030992048950142c0040c1c010124025000a040e5070003100b41c5a094100a00c03400c1001a04090504408042d0a2200541c00850441401210000868000e0340c100104246d01302c440b00240078608002400750616415070071a034101c400e0307035510041055400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 785263048 1250 785261798 785261843
    0x31e021305070f080f0402010c1118090f0f0618070503030309010c090b0c0d0c020a050d0c091a150d1107030c120f0e040f06080303090d180f060c03021612 68
    0xb05d42000c44030382501d000c41c007d944510030b411405445011006510b10700c0c0d07400202d10190750344281000c0e1041204203c040102440a54161450b100003409600c00c215034580c3c4a01004001c0705480b290942200715040040043c24010b1034081c0031b80741d50b4141044441d000e0030f10800030034045a5804400290304803188120b4009107c018087e01c01c0d0180c140d412150a00b0782081070303a2102003080c0120f80d0307079503a0b40d81131011032142e0112001a0325108681c003e0b0340594902c500b41d1026200448416202c00c0e0100c1a001e42003a00182e840c418004130100038021452080441040400ea60b002c15810103040c1681c54000c001e84141202032180454031100034030421000590b10410b40399403401e01d0380101802000b00e100106001d52107541a9141d504111009151a0310000032001401d80152664040c281700c900d000042c14200f107188028803e4900c40c0c0c4041094000300442418800c0c0f00015a808c062104024415510840401c0b909803107402030352907a02036030042c040450035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 785264298 1250 785263048 785263051
    0x1905090907030b0f0a06060c0804031b0306020d06080f030703020604030c0f210314011406091203031501091401021c17150f04050f0c09131506030c050310031e021305070f08 76
    0xc1d81191404bc1180d882c50510f41142d2912a64000301e90004400180c1c1030000d03095066007032900041c11407030101c4607407070b03c1c90851000c821500100300c4580070a501196055010750142002012401d041c40c108403090741b441c1d8054400d0012400200040d01d81c1c00440541d10340d2a6403c2c0b1081c0c05040100842410038840c0d1014240031903210748550030302c02e01400351110010000180d984201101c14159802111100c1000d88075011150042d030b000071034107000d002d180d1000b1221244200010b903842081d850861340d42c60417038a03103030308051240012204002c9003440e0a14207092079001c09041060007408144030345c41c1610102400d040512030716200e0009a03a81d2030550f00d82d031510301181d40c013603085540c124200402660f10005c141c064200c0385082d880c0864126407420310b008003103904016140c810484100706000b00a140b02550a05036904102c401c0016100a074105010310525140250469050701181c40c0410007a807001d4459001a01d03140f80d203000c0b5510483d0540b80 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 785265548 1250 785264298 785264303
    0x20303091b030f010f06050a080d0c0303050a09050a0b060a0614030a0e161206050c031306151706010312030b06070605130804080a0c051905090907030b0f0a06060c 72
    0x41010701080c4041d92035260016040050280c80b40072100680c01800d480321802c07421081900c550381004981040a508030050408001622400041250082c070700a44814080c0c2016207030804601403031402d03485111030a5000c0100c6034041100e01c2c0503204a0001c803416481400b42c1240003070081e0003030203201c8182403d181700c186181ea40d121010002c140d030011183c0c682c4a0000c40d41032210740d4405440240036403210001c425421850423005460009008070722601c0140103000070481e0300c02d0302d0b00d40b45900030300c042240140e014550343d4000c0594010010111500e016901f0380302d021510314107030381c0a014071036100a01007109406941420f011a90010300130011a0080b86403540b00c0c84c0c101d824400f030001b9883c0c0640311444a82c11580140540d80c21451402d0300704412810128002c19041d1081503e440710345032400031204680c0b00b170382d006000c0c50740040c5405000780000009160f10006e50802802c1c0080301200400c411034100d05101c0c138003080030441034019001600b00a9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 785266798 1250 785265548 785265553
    0x4120218160c050f0105090714030109020a05120c090c0d052a07032d020d090e0a0c02010204030203060a050612030715020c0c150c100504120503040213020403030201051602030309 79
    0x420014100c030990011641a580c0b030080004490114000303000361b0380034001c000300404081d414050080d030100c0c11a40180d100b0781c98072049000503211500342d1012614103e0390b0f036004090a020035400c0c44040c148980e403040c60ba004200301d042d1a0b20141040c26940e000800050303a81040c409113458040400d11050343c10314140780940c000410007002c4403446440d08024580250100340044d4601503c01c0c0cc080d5000030b180c1c041c49504000b803004040003442c2c41d400651410001001015000d0b10301c020580e03e408082d0700c014001d4045900869002d0211071140c9000117095000f440c090700d10b04d110f07800c005444003048100105450308160054021440c40341103031015002940011107603006070168580020141da100e40380c403111310030b071916215552503111001070f0410700d480000441007494282400301042c5400c81c07000540f0102d0421958903104c60001420f8142195500320700c0c1070000801108140e410b411140c0101398401c913580140400940c00d0381c0301d020449401c00c065 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 785268048 1250 785266798 785266831
    0x12010807140f0d020f031e06310303020c0a050a06150f060215060f03100c0207090204030302190206040e1501030c03052511010e0f1002040312051e04120218 69
    0x40c6003a800c40d406081c0d0041c00c83d1807400b40a0b90858220035071f501708007402d070415030810041541001286040d512000960140d0100400f8410f41101c44100c000d8105540813565182e1314408002e00c07080182c0050450300704031114584040501014078130540030310290400042c00c03841d00c0341000140d95198010f403e03480f600381811041c41c440204a650300101aa525040c592001d220407403c40f903803410003007050044000064540b0120394030841030240b0400c01000440d5010603c1210204008503840010380540000799203401360381c00c0f00700a103410405021003144040344582140400713813014400102205000d07011102d046400c64801c101d51114017610069030601c44407015014141001c0300d01c0050501402c60303040900c40d0030b0310ba1125012500c016010800c14000c10a006030651a1a0641e03541d00a03444011100300213005000c20b04421820a6400c0d040e0308040024866884950754150324407503411403582a0300541101130720350190000e10030307818400c0d001c0e071510314400c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 785269298 1250 785268048 785268053
    0x6020106030c06110102120c090405070f0e0d080c06092a060418090501020d020a020106150519020c0d03030203040605060a0e01120f06060f0509071e05030a0212010807140f0d 77
    0xc40814106480d04c5550800a24000860b41e607840c0d0b024020307080c0083c1d162202e020a00c01168005003880c8140705940700c01040ca1a405180240c0c6070b142591503e40e081181d28004009010319603104c05180205d004000c108040058105125103030710000d074801d42e14100500d01013504034102076402c00400c0206001c0c26080c4140d00c40101c4040c600010402500d4960508a030056003245108076000180108204c2c1d0900529015142031480104115a802c10113480c40c816141c5440aa03a281d40c40001d040e8001c0c0644400703044041c200c003d042185e031800034000d60013214201e840b180340c00d01244907402c0010480007505e401c141320300710703590800d206d03036030760012640040b6414000c0c4101180042c245000311001004814180b18081c0d01340010080c004900522407400c001a403d42a0344e01c0c840810382029214490a000c0d603a5160f25000d00042e00c1510141c0100200b0900009890040040c1072000c480b8180040b04410341800204581c0020311800c0d154000e6a42e030b001c801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 785270548 1250 785269298 785269307
    0x1113020306060a0522030c090e010b060901200303010909031b05071707030807050601080d0507050c0405061c1101090501030c0914010c020d030806010e010507050a0f021302041e06020106030c06 85
    0x17019030b540c1c100a0010100d0243c40300351200c1d03042240c00307540300401080541c1c100d0142400b40c52403807000b4040210a04082090350007100c130142e042040840b840e010503005080c403141c0c1e600500c000c1d20303625078460303009601500050100b140025080c100d03421642807035003c0ca101032a031002c0905140307450041c200c440c0303e40755000044903010f10540000040c406400800c001c0c1c1c81000582a158580040181480e101d000c8600031700104010314000a50080b0b1140f62802c01101c0000711907c03601c0106a2031041d203c941003549000003544014806000683c04410809a0383c0003400d5440f900110140c0d550a4062008034144003014400c000c208041098542d40624042224014680000340b20303520b645801d402040e5200705001d15560310019180b0fa4600030700b03000703250180b80c1da00d0543d50154024040c0c1000d418a50741070465aa102c1e01d040350100500c802e41d11540c0ba8546460038001d18107601505000c0c1c150300060f11801801404200c0b038010048508507442d00d90b0554 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 785271798 1250 785270548 785270557
    0x3030712021b0c100206010b120703060314030c061602030703050306040f021201090632010c05010c03150504091713090507031a040506030303010b0a020f07031113020306060a05 78
    0x1125660203000100810030050685200b0401480040400a4040c82070000c580c103203441c44001c5400202c0144840101d520031540b241842411080041d03603103000480040400d41c20081005140b484030326100000000a4407018074100300365030140c1c4801d00d607030500034000084900035070000d00180c808203006001031a0701c004082c3c80400c114181c201c0000c201c1c0d100840303442010076024014003441c241c9114400c0a4183d44140300c9010810340702040280c42d0300003400300c42d00c14a60303821105910810003002e12a6000740280104001000c1c0500a0600c1501000044111071000a0f06150038020a1105a040a0406070f9188440d00d40d025030390100c0c441034000c14040e4400604910305209030f07841140240c2e03001440d401d03120100b080d9a0742c0e008005204074189018000c44d6a0080704490444624004140e9240070f40b140680c100004070f11031403050301a450002040c443c201212404014046412046c0c1c0186000c40300300700e010560340150411020302030215954010802071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 785273048 1250 785271798 785271827
    0x30616030917071e0f060b010314010906150e090402010e01020a0b04050d0806040c170709080f061e010f150504080105330d021c0f06141305030307 65
    0x200700c40c049900c841000030050b5207011006040095070b60240881401c00c21a04032107686500c66049003612040c50310742d41c04038040d01c0b50b50b0301c0400a007540c0c000c2d4410003401880000c461540d603520400b40008040d184030703c00d00038048007140c1400034070605240030603207401040d0081945031500110307410b201c1d00700751034154491001401c010807003144e0710310711461240d030040840405101005200c601d0103003003240682c3c100b019507003106420104103480809502d0b030041041d66001c00454003100140d0248201b8029007200b4112207001040c2d240c450b086c1c002d442c004010702030305500b9603c0e41c01d20403683c0f0506a2881403004000d400b65049909000d0b01d0103904160321003180130300712617080d5280362900e0a00c0c45142201d014001c00c414040701c26540e130885941c0503d0200c0c1e02070024140007841b46074001403c0742c00c4250076000d6600241c03c548010005c0c03500d864484010700c400940b147d0128103c000040c01c2e50700b02800740c045113034400c010314116210f14000380c68410741c80509 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 785274298 1250 785273048 785273051
    0x105210703240302030111090d060f020d150e1509011401031d0a03180b1b0a0506040302150609160e04090203010c05040911030c1b01090203062401030b03061603 71
    0xaa0b0044060300301e121a1048030328101c10301079103544101401c4400c11b040e40281400140b02081c0c03150346802e020812190004000b14611a0000181c0003d2240d4400107800d00c2c98240b9008035281c52401200607101000c0d0000c6441d120058001c441c2030009003030981c8050301074018407542558032174141030701c1c1c818100441e155203800ca44602d18018580c1ca861070f98000e90907203062580c0003500d60840300022001540c03a03810800b02c15843e1080007001c05001802503c05440c5090800c03248004a8003c01500c6003800c0c48e182c000c0d2a41c0c0400140d2541d40001e4000c02d15624103001414040c060001c10007203103802642c41585ea030221203d00a902595400c80303280507842c2070060803180355241d0b40300342d51582040e184500700c43c0d50307000c14015030b0340a00c02c000c0c603c80784e04211181114071049802514000c21003c90140c0101d0900a40ad03000e10700c203000d04401c42140350328030400102084000d051a03240110116034041954560540c003d60106118042a03020548110f0640c0b50 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 785275548 1250 785274298 785274311
    0xb0f0c010f020d0f0b0d0203072c0c040602071401170a09021002100c0908070308090607062a05091503060f04111209120910031d0c0406050105210703 66
    0x214030040360040408990404c0d1100800c44040959200b00d60b5070b51411140103d1086458000ca940c1d02d60a0040403017a1040070840d40800030711080101031480d501070380301d120703203840c14818009420900c80d0801500c12100040b9a40b0b04048500240c1401a520f64004100034007034030b804c1800140080040c190341c1c20308203001d07031903500007011245107640040580c4d41c0400d0600d4203e032501300e02034003080581d100c10300c9407003400b01f00f04040702c1e00110750984400681c0300144080c46842002802e0b107140541418101c0405088018402010034800c0c0812000d05000e551910a00ca0b095038030025400505086841c841c02950308180e010b052111301200c00c1020030211261007414505107100400c4406103d100403042c203500080d1440507241e0f51a10540400e00c0740a000706043c8120301d828210410340744a80e1055079040083c0c0303290000c0c0c456503d50540c89030030070f24201c5d010fa8141720707002c513041d4010700c11034201e0001081196803903e0400d036500d03001c50740078113003504142e03c4030b0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 785276798 1250 785275548 785275571
    0x1c0509010e1c0519050c040b01050909041b090905030a0f1809090b0c04050102100209180726060d0201030b0616031e02060c030c070507030c060906020c0a0b0f0c01 72
    0x225407568030070960002055082c4500f001494a99400b0302e4079004042c07011001c1c00608017013860000c58105a0300842c0340542200162018050510100d400910741003c00092013120b00705a100c1504080310f1108060700d880028007510000c06c00941aa0300401094031450b02c41c1800d03084115451030440407100c180d80982c0d00b038800c40e030b00090071907443e000c101081c0100031803119044261000d010707140ca407500f00040d403036a0422500394078072617000c81c911141c2e0300c0d0100016642d541c0c0c5044142280740001c005000122544030300c0341c0b000401006840e000042120142c00f540d001811300f86002c8890740111b0113803c800c0c51b4203410400901c02e480d888000205c500805d148203450f507100402d14013940760700d0442d21141c20000c43d409002401001100f000071640c20025041e0602d0752184142456480d211090f48018070303404000e20009103031584002070200342c4100f42d0960b11019000c2041100300d10349401070b4481c0300030410031015251144002081c3c2121058004524074032400c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 785278048 1250 785276798 785276809
    0x7022b0c08030d1b020d050307030e0105190e07031e150609200f03010302010309230d020d081e1911040f0b12041428030306081c0509010e 61
    0x250700207401a80081641c4003120000d01400c0c030003005240b110b041407807400d10000d41d02c028100c1084c1c240701000001c0380009100350891400025040000d10060400001c0c0d1007000b081201c600156071300d880c1980c54101c0011940b13508403a040001301c458000a807041c6060710065020450310003120184010840c18203008000082c0249200000c40d44807035001d5000714100c4402c101c125000800001b13541c030320314100b5030741500d40a2a001403100030700d20385441b055119104103405142200e59601110000250201042d13a4690035100725011043c01a030f06210192800545c208001d1010900c0981e071428142d4860700c080c60340039810751441103440842e104071040c80300c4030318005070500c0724501c0445041c00a180e1178207090300c1c01d021428000c1c102100600300501d400c09807030351440f008008010541e26580b20150841591060110309002c0701d8015a04801081c100a00003849540c00300d1811011000e400b100307240910760745401c0380c40364000c03c0454103112400000903401d4541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 785279298 1250 785278048 785278073
    0x3030311130f08061018020f070f110411070308160215040c0f0e0115030c27090f05090a060c03061206150e07020c010e0f090f040b01060507022b 64
    0x49105030340c02d814403030343c18180342006100982d001c10b440c4003000081e1002ea608030030304660150060315168540380d01c0d501482a10405006900380751281401e00c010801455104c0c541160200b111070105a1003520a01400360003601281061000030325201c0c540540740c0100d0010710685030840444440000c02c007009a0b800ea6480311884d03800e0081903000e403070010203050f941c1d000761220742c035204011495000c000e0400040507198442249101c3c0030300d80080c455426a1381800d010512075035002d5032002a8405c1d0780005003811020240740c0c44074800e090003a481d80000e084001d6042d141c500c0600781c0c20040038101076072040f00042d41601d800d11203440511074040822401a035141012114050f030b007181c07840f0002001840b0300741d5000134208141140030309003000d0207444d200000740004038840440d0740016000d010032a20303d41403602244644e101d010b64000c1d99032159402c680c280034601c0001e4011071020010b84c10220b06429100d40080900105030800c1380c1075032172100c0c1d841c0c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 785280548 1250 785279298 785279309
    0x91f23070906030e0303100b070512271509061c0207150509121b03040f0801140f040b040609051f0b010e030c09010b0a0207030618060b010c0c0303031113 68
    0x41c040180a00396042c0904002c2e50101d20040d4250b0034030018500100c116071041a00c0c0130760009500e010042e0070710400e000d000051410b25100c103c5101c0d6010240204040740356094035407600708005142200303e8a03090b040c860881810200800140302c481d900000303203240c4800403004003c00300c0442d400102803135031240182510340703000302503800c058410180140e81d0b01d8001d0030082c2d11001e149815501205144c0b00081200c0a0103c0890306520440c1c11540c1117009081d03020a8040054010000e80d21451201000564408d41340b4940743c41c05884c0108216481e6021401080c05a08805502c81c0500c0946100340c0440b0003450090b4519544050080d4543c12840300310343c0c0200c010300c800c040c1a409400d00042080c009071070351105020711000c544000c6840c032810b501c02c000490103154170040401114090107061050900390410841d41a401c00c50700c01e80c107510441c0c00c1daaa0561040600184074111b940a0303018141c1e0309102e034100b40092040c060888480002e1600521 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 785281798 1250 785280548 785280557
    0x2070e010303020d09080c1e06041205060702070803041811310906050906100c02060301030b0a1104060c020d0302010b15070b0a0504120e010212031806091f2307 71
    0x540c1040c01429207295a44030406d03d4100417038901a640b00d207140010080506440f0300070407000040000c19030b00a1341c104007407400c4100074800c104400091100e000b10030540803207190369690000c0c02c1e62441580504801c44200c0c8075022060203068012401c4900700100e420b003416907000d140b40c04d00803c4050384444051405c003101090758030302c102d00054072081c04284119402d000200d00708441c0603040318007426030001030b01e5185210700b111319a0070b83c0c014180c030366950b9a424007000c064000d03103006455600d070114420b003224100080f1703000c03241161a025004c0341a40c0810968110501c1c0c294199501ca04a40c911350f0b4031191000e034031011003100c06440f5843d44c10f021002c110002d142d140d07041e244c00c00b41300200d048000005030b019500e00e040b01d00d241200c80108e0030a12100c600400202e004030074040c0710039806902803006803241040f100103545040c1a5503890f50001e1400002c2d041400c04003010502680164602040c001001d08101044400b544000802241d0b00c80005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 785283048 1250 785281798 785281813
    0x1e040302101a010905040203010609050913050106032001090f06390b0c0403020a18060b030a090201230f130312020c03150c030f180a210203120106080702070e01030302 74
    0x81d038004206130040d180540b0114250b604026000c1c0020043d8001d0a106250540001e645910241a007030049544030000b84000c0e60f60341b41030b002c00000c03044080035a49601801203c04d512030791446d8226070103c9400020340d4580001a59219083e0051100303d03c90040b1b5802001a4903a2032031040301c4090b03c0030312130103c50809094540b00a40780b20090b0b03c04000030000b51761340c45602130230303500c80d400c0381c450144101c46000c0041c00c840c0d1049540c414007104104844c1000c0d0702080e0001c0c000c0c0c030341c002040a01004e14049100c1506411030484c001c3c4441462070003400c018069212020704940035464507501c3d1580b400b002c810450006038000354085017182000d0096444041f06070041007040e041c5084c4498090000408540f680016000051404400c0441c1155007011400658290b5019414010101c89a811704001102030444044200d0b5100008503a6050007000040d401642050411101d0b0b01c00580004110311552801044242124007000d000b14404c2e0014001ca = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 785284298 1250 785283048 785283101
    0x1120e0f0f0708070b040b0a020703061a1005091e0f120d090501080c1210091401050a17030d0515060a0203030a1109010206070f050c010e06010302040b04051e04030210 74
    0x2400d800790010119a00102c4081016000b43c40982d0305035005030005944a16404408072b11f06220750b03001824103420210062984070380c00820034108202912031424800d05a0010b4030030b84202e51010381c0002036081c409005140360441108030100041c44c0c409a420328200280d0460b0344148a07480b2900f204480440094002991400030f04080c02c090001346000e4142c60031502a190010702003a50761800500c0318010700e848bd00250514440802c026501d81101841c03c0009015580c000c0c03603842404580d44590700703042d104074032441c0000c41c0f900c05800f00c000007030000a0318147c03101915254111003961100094185440c1a90046450b403070f00460202c241d07150f01181c001c41810030081d5401903640816010740c480c0c56030501007601c03001c000d822581e0348035109841003594a0f120601f000c241001c0780050489008803002e20020036024100400c45e6400d0f151414030703403040c2034141c900c2a500380c8001c0d8414000d00565010030f0b044c00040c019500440d00407201c0001000302c0549 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 785285548 1250 785284298 785284303
    0x9030415020115090b0603041401060504050112330b060702030a05100b06040302130507090b130807050901050904381602060103081e1b0a0b090f060601120e0f0f 71
    0x101007200c0184000d8034005c0229055100140018200c6500c0d8240164100825080380b402400040c108124641e0f40f550301c84001360440c441100c0c880425410080342c1c1004101c144494598040c0c0c0d90b070880144281c1c28001d04a03003102c683c20031000e101000240e5010b0040c0100c1d180a00b01500c4d940d2040c078500c80840d16012415440354405000c21b0000da1184040e100701407030121300008658403045c1041e11590096400a1200940051400d1655011480c0001156005d02c100c50031b680e105c1c07080066040003400342c40c2c1c200320f0110004001c2448621a00c1c03220100007180c440c849008102c45100035881000d030107817003802905002d00e5100401c1c1030320082c2d043d840038020b9941550340f0007000e44548601d091924075108040929a80144101d03000c080a16103098030b103440c0c0c008179585031212110282c030a0600580044c05001c00481d00d461b00080040c090800f65403040c00540345d01c4040c035000054290348904040b00414208105060140000000d1171314020f181c800e9031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 785286798 1250 785285548 785285591
    0xb09030c0a090b0901082b200106080f120904020a090f1d15011d061605161a0f0307111603120201060305060c0c0114010b0310050d020f09090304150201 67
    0x60341c0162640240c01030447c1101e4014060341200050306041103030b003110f41500b500d51182c01c0740a40d81602107460b10550000040342d84c80f00548500c2007105000b6a03d90403c00c4c000070204d80700f0400f08a451900c0d07070051440d00810b090503c940c0b5182c407215002c8900e00c2e0400040220062810884280c03200320f8142e00041014000d1161421900001c100071540351804c0d00e40c202c603105a070380583d40c00f000d40d08a04002620690043d0081c00c05565451201c45198001c103e00b1101144915048030304980803141c112402e46082c21005407583d02c1d9000514140c10041c150014a245080070302007842c01065082200d00c40c5800d60030070180803000101c80c06e003036a14050040000501c041200780d0303c00d01c1900010b85902c0d80a0281d405001c01000ca90b000300618400420340b0318603031009c0c40c003800c10b038039024418070745030030921821005440c40a5404161840d1140b02e509d4941070707081d440162034041e281051760f180407490f5036a402541020143c0d4541141c03d42e004090001c06 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 785288048 1250 785286798 785286809
    0x504181b0819061b0509090705040909031d03030405030304031704091a0406210308180f070e07050307052505010c0c0201030e010b010c0215130b090108100503070b09030c0a090b0901 80
    0x4c0d080c05040380001c0d0461003055800c90284031071000054505019400369401044103070002e10003904145001041024001c40d401c0c0c05008000003400982800000c3d2000c1c2d480140096103428159240c0480d101601c07001495141c2041102042044050054400c80014200c02280c4085800708100903a003481e08490307002c005007514000d55944075002d178444d684d01030401004586684a0700356000e0705401c00c0710981d204007650b01c600082c00049000841c0c0144905088a803110035080b1080c0c0300a80d10b040c002801480b400626003128085c80300481e6a0f032019642176815035032420709440d07040c09498040b840d0301e49100706550f090b00031501e0388100c0d40d00800030200080c1c00a400c030a1414000b900441c40d131445500780c40b08890403204070340b0703415000c00003095499084080d641e024145040c001822103000c1020340407070480c10070550303034002d001d02010390424610703e505400c0100d24a07450712800b0400f58842d180c4100325000f0b0854031401042468503001440f050a01c180e101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 785289298 1250 785288048 785288081
    0x3020307150605030a08072a050f010e041a0916080403110f0d03020a020f030f1206132a030b01020d1809050c0a1403090303132301150504181b081906 66
    0x4030603241c10823903110740640382c0890f070245006a4900040700c0108541d82929040340ca462a00012400c24078600e9000c041c00701c0c2d1302c004990f114004800603e0480300103a02162842011034000303401a4181340c4465090310407600440698038045250058581030103021a0b400101c003621180d06000760844c0350300c4030000f0740c03812500300008c03486482a61039141d0300f42d803403101042c2c09941c3e030014500c200c10160024000306102000020031a00d4407090120040510215800c4680c040d00540c244000140c01070601e0511250017983c1000d0322148401d2080c280090105440c05548110746c0903507001001951281c4290001610502140d500004008070074001c00c512440c00004482e80250050700b44e58a643e002d01d409011030300015201c08002200d0303505510001d00561003400454954500300c40c00139500c03001d1108a40b0510f0203e070321f8480049454005c00c044400c100b03110401900944040756132017a805003003c002d04100e25030190988408014404980220803000c40405003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 785290548 1250 785289298 785289353
    0x230a050921060c13090e1f06050a1409040f080c070801051009110f0703051b061b0a0909090c050d030f02010509120304110a031502040503060f010303020307150605030a0807 76
    0x945154444132440340740d0902c2e849102c90a0403010511040d0754426154540d221821000168034015103014003e40740200c2e0301203000502e9014100030108022005004043c8503280c60310390103a2502e0020081d07410003810480405503460070803105002b8814040000307224103140c400c082c00701d0f2981d8454a0800e080c1aa11060a02c00b40100e03140c1840f8103990b107540e2142441c1c1030f122800340780340c031190f041d4118410f00b6018801185407032055003902c00941007407205230400c910354002c240c1b004000543e42d100a000024450f80210b0313280380102c140446007540c07500054890701d001c100c11400540c1e42c80002024603024040c4940041c00140500101d0602848880c0f890000800151400c00c8030885000c0d1601d40220601c0a140c01220b07460250194410480296002d44105c1d406845144000b40b1505c418440c128140ea034198003552800550b034480281c1c3c01c9040c00d0140c4499920a80040d450350200440c003c0148150000307030b180ca0701d40c2030030308802c1c0130705071045d151a51040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 785291798 1250 785290548 785290567
    0x27150c0304050c010f090803030703020c2b030b0a050301020a030b03190b06060904150b04140103021606090203073b060a090e101805060601230a050921060c 69
    0x9400307a02c1c0c510a00e0080b16115050134100d610380d001f5880fa5a01c3d02000052240c5550b054004002a280140803501c40020300b000b84403000d003004c0881a81006180e45400c174652203500b20403d00c400007403070b402e5180c2c1c5840c006401c81e03001400c0071b0040703a03490201c1c0049007014450309520603011102e0a05005c266110741c09407402c0200359034403440c000100c00003150340e580e10204613050020100e02016417541d81100e0194405d002e5502c441c843c4a03034001a0303602c0790003105c42000d840744580e00800051381d100310240c05103450480c0c1c5401191804210b074040c4002c0e12085940700750102c8505030000a44c82155207402690210031510352003000443c1e11002c80d80f0003143d240c0000094180c1744044000d00b070098104c0303200d40060510b004000089000d00100b161140500240c0b4210784500006450021402114006c0c05140402a04080e04a080603140214840c10b005140c0a61400020750b5041d0740e09600c614403500ba4118010343d1002c01c13403e076110354030480346890008100c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 785293048 1250 785291798 785291803
    0x1a09040506043003050103020f120705040e01020c03130e0a050606070b0709050a082401080a080702011704150608011e0f1104030b15040c140327150c030405 69
    0x10b1000c1c2002406410682d40340b0300480800b20034010b1402803028200c1d070720400a020b40030a100607441003a4041c2805080c0c60300a40b12420403003081d00801c0302034a01410f2201620035030031200c00c15542408803080c000c0061000303000380400c00000c94295420000d040b9038502e40a4141c049441c03500b0100003917030b1510011149100d810136095249940c40741e400301c419110300d070402c5070040c04011000518240004c0c4182d0403000b4601c1c1d01144011000c0e00401c14030702442407000c0d80d4046070003400818a440002c4c0250f900600d001200010702c04085140850192411100c00c140e084c01d1100001c52446140003800d8804024014004800d5a51070039120010038280700c4ea54a4000803c1d9100551000c141d510350910000d4480c0c4d036078103140c0c1c6420803c40c1c680140818044d5554a289400d114108080301e85071180403d1041062210320b0540005040500d064520b9800e00281e05c21002d4006402d20520f0017082c418684110303400443c54044e02d000400d56007403040c0300006601 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 785294298 1250 785293048 785293051
    0x20030702181503010216060e0309010926150106110c060a12090212010e060a05010f032a08031c02070b041118041b060c0510111b011a09040506 63
    0x1484a000392640740c02d042e0399441e00c070b50600386078550320000d020288902405c291400c3c0701e000d480c0030014403c00c0001c0d161644254405030707000030b010700400d11141401c580b0030b002c924400415260002c801c00034403403401c0802000c00c2203101d112401048080d0740b149100d13402c00c600300081c1c29100208001b080e0240039043e5540d0038400702e01d90010320820954016050190002c0208203800c40e808900f44c02070001c840d07815124000c8600007014800c5a00400e0f040301d403001c0d0f094460528644403912041c001c036800d500030422555000c8401e060f554564005844000f01545d43c07002013039164880c20100804403a007260040c001d0101141c54544001d078400d400c91411142e08504a0000d070800341c1020f0002e605003818000c2c00207028034401703841d80c02d82c00180c0d61a003044e1207403c00c0c1c510440c451001401580401c03400c18040301c650b0440c080b00c1464615242c10001d0072056211502111140520303035a56640100310114490518208504005e0300c08604506260711041c3d1103150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 785295548 1250 785294298 785294329
    0x114042f01031a090a02091914010309060204030b0906010603051014120c10030e07050607050c0d0203010e0a0f061b09090c090b12041110050412020a1520030702 71
    0x2618050704403d800700d000c12162840004003820500d01c1c0400790030000b500500603082c040c01c1401000501c21092100c5c0c102518503a442d96081000d0503001100900f141c10021150315800b44000800100101d114501807a400c0c4c01410140d81807110040884600800210040e1000320f410404c00d0203e00c1062085881940d14000364241c80e8099850718100a1002d0b0300904207a8004103501e5042c0e0020400890980a5441140d0b451007006454081c410000c0c00390f800a00249046151510034021071502c041d001142c24907210142e1030038001a44015581c1d070020790650741c100240341c86002400c0105143c00d165520011800030600440e5000740800c00e075807045070b2a4520b00560601c801081c94001244d9140d452864180035024103235401c907556030f41c9140780700080c50540d00860300c10350107a443c103041601e00f10410000510050041ea0051002d0002180e00d03007403201c070342c0c1202181c0d1701d074140f03010b1511044050f150001e08081c42d640c0c20074804140107a994100b890075410 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 785296798 1250 785295548 785295551
    0x7020304051810030807030842151201081903050a080406061503140a060609031202010e03030a0b040e0138040c02060403080903071a07110a14070b04031101200114042f0103 76
    0x754a507000ca2103507030411607810711030303403012a85007200b4194bd081380d81a2811482075504105448070b0440d5078040b611002030224205000041d4101c1c42000d150760710500520700070a03080d540d01c141c01289440b54000314002911078600e01c084490100003517800c19013a01042100e20b140803802045c0308a5408003d000b000240025105c0070301c00d4000ca10083d071090250790f07403420541040303c02031107084929405a410300c1d0540350350311018405c0016943c00101c2c120034041c69aa43e4907103076407800f084413407041811403052805495611445031032341c0b91a001071615040c41c2c1000303408440028002030481c4c0c41001100002624150b2203044e0f50701100101c95591a40300094a00008a4165170740a20401710382105000700045081d44034171018059500b4203840348800c4403035100f03500014104000f80d80801c0400d501c0f0b6070890411415004900708010308282c025401d48007890648004183c6481c180810310100d12103182000c500340c945080320086400c003c002a900c40d911407411305 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 785298048 1250 785296798 785296921
    0x30c070206121504060b090f010e1801120512070f0f020d0213050403080a060f0b03040602090a14010801060c03020a12020c0d050102040e070203040518100308070308 73
    0x151206015681900800b600c1d07401c0c10b2801c03184410703e0b0351950301818892410306030005000d0300381c072040313a01c0284007505540941c000304c00195075038000440c0b0241c1001200c041c000005140d405000d000e00344541e0b000d00c0c0140582482ca2034441c59800c2a84610010410a400640c4101707511001c140d220100110703560382800000e04104201d20f000e5081114840c11059003102c1d03610013803146109469903080b64071010310000460b050307030003140305032031000d1030510030016102c014544c0b080c890600545080c03003182c04108045013650044841d031400340e030312401942e00020210b0240a4620b0000c0303001d00e80e03842c000c1d92226003600c00303041c030400804000d07142c82c0300344042554640c000d80106804011072400c0d5000350302c5485041030451580000c10780d201c5c13000c070844089070300007000c600b850840c80201007003524000c1c1c562220304914410020005920380090190140262124400c03442c141d141d81d544200d03220044a24900780e00d04042408102842c03580362142100030700340c0d50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 785299298 1250 785298048 785298053
    0x209090a0509070308040b0306031006060c020d0c12120f030b0a0302040f060b1b160f031709031902010e0f031e0c03030d0603050d0216150315060801062003030c07 72
    0x3c050641d00003502d00000060049140c0f030440c6c006600405e0240d0441e24940300c0d035403803101182c02c00d00618000840118440700980b41418000001c28081d207410300003599a400c3c5004044ca51846c21240604c030b158003241c0454011a18054130105402d050000515030b0700054801e00c036a00000f03100b5a5204001414201c071540303c0006082c01500b43c556030000d184192800d0a0039182611261040440384105a01b00381c42d80021190108800041c641c01c41e41d9082850000d21001682080140110000b6036820407202c0040c10040d41c1c0d00f030110045000040039884101d820500903056803003210140c1d10009400e00c150702d002455919034242c40e004403800c1c1104183c00c0d903418400441d1500903505580c0c40181141e01c82c10442d108420601800c0e6151003403c0700c1c1d02591910804100030041c2c3d406001600c44d403040c940007400d010401a0021308910580011001942d41001401499000900d0b000303103a41460380318110321822003007541d8901c40140300c010300244c08580c0808 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 785300548 1250 785299298 785299303
    0x905011401200d0c260c010605040e03180d080f030114010309052808070533130c0b0c06010614040302031c0c080408010e12123903190209090a0509 65
    0x90402c400d00180c19042d0045c5d44111141e08907001260360b65191000c001203a181c20305c56140d040303500398003540c10005c1e90103042c02003900034104c0c1c6401030b00180d81c040c0000c140800900c9840d00d070b1a4031030b03241d50605a8448401c2060103c0d02d062500e04040312010400004105000488600110300c4a01c9040c104115450f040394008000c03c4000c01c001c4c0400501142d01210340c00c00744140845035281c00302505042122440c24081da080c0200812500c9507602200ea1060380600d5a000c6180d03a290904880d03540311503607076801d40e003040c0014059141e00560050a1000c000301d086c1c2454110340002e40c0b56050103405e803000d1030301d409104000c14050755818510035002240a51a650b80e2032546001e0501c01d950000c4600940c40f00c0081c444544003aa074110360044112152592184416003004c0b00c010705c5401c1004064020303602400d482108a42c00c0c0740507501c0f0781e8580c20701410f506164841e0306030b500ca40b94010f1010480c140c0341c100300c5607400304080380301250a45607518040d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 785301798 1250 785300548 785300573
    0x1506050d0f06050a03050a1e170306040207021305060f0102030307020d11011b020f0705180a0f240609050639161e08100908040905011401200d0c 64
    0x94004e08a11000800d00c9008184800014080c08842c11030703140009100200591041000f00444910b081c08c0460320701c4d08018603804100074200514100c410780005107501c020441035651241c43d0b02c100095424151411021540c0a00003541141031801d0060748030303101e80380540304000554400c07400880094010903e1050407040c1609052245080207407a52500d030000303004e42c030880c000066541081440d14103070703e1408040f546961140080e54002c1d00f1840e04118020342c40e42010004c000d400b030030300454608a000003035a42c03450312801400d00d01c0c442d07010601c294024014810300381c0103810001e804c3d03007804941c450303400902040401c981023035907802c450610492080300103035a20b581ca10020b0b559403000c0000c0001ca01c0030760007012a502c0c0100c44040d00103e040110b0281181c2124500c50f00c280c0c400b5007483d884038445002c84600341e003c0d007214024031030350301c0301540c00c41500c100e004c1080c1807540002949085050780e50641011750020005503404900501100f240c044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 785303048 1250 785301798 785301809
    0x80d0c230a09260f0606030d12230106020c090c03040b0402060f04030c050109050f130b04060509100905070503040b1603060b1801020f1501090905030c1f1506050d0f06 74
    0x2031032441c42c0000d84000e16908828050300c0d604c610450080162800550140f062500400030030b000305094104890341d03903050b02d03440c140b1034680c0c0c0400441002ca4154841c102248261040958074020300240340200080b1298029428a021301c075500051804503a030254105009803403945940c404611a4415188a01a2101d021030702104010b201d10031101240c0d403d03a03a4200341520b400c1000040550650322903030065400b068481c406800d40c001003401c120042c0300041c1c03aa41c40010803450306003146c2c006054400078106105112291095036081402ea103400c50540c649070340c0b002d000c1c0902610395060300c41d2102c00254040d201380c00c8100648000d40c4145d440b1000b901000b401c081c1c1e542006030140c007860440c00d0030124006883d4469994601800700c65034648a0306000515036090180e90307038002002035000e41c410410100181107001401d003842d49125000100442d184c41010340094186c040c1d0411940303501c0000d69404410002d400640d040c12035a0000040541c1d9106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 785304298 1250 785303048 785303069
    0xb070c120614060907020a0b1b07031e0c200d06020a021e420403081f120303020313020909030a031a090103030c050109080403080d0c230a09 62
    0x1040c1000074540000748128078102c8410800e844400811001150454980e401644001560804100e81d180e080f6008400a03d01c80746001d0b04503803800171355011140650204180078500b801c02282c0c55408400c694040c42e0902c010302540e590f62203202c402600001c051144030074113070400d60750104000c9006a0181c0115940c461014029489140d00304100789481d004a103625905800071440f04101640720000000d2150f448200c41d5058515000c940341000c1d0600355410b5015007003500034001c90098540c1c400e9487c248541200400d500182d521000c4090002040302d4003048800c0700300540c0c1810302580300daa0315424070f0540042800c0113540804e078001070150346000030000340704052b003c1d501030140915003695403410440040c04243c2041e503a0004001091085800380c2041d8410000461f2075000c1d519414a140c0191f041601c2c0da000014807808010100e2042d07011481c1142080000410300050305540340c00244211985039a00244541d5810f1040d482d150181c810203a5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 785305548 1250 785304298 785304329
    0x51c0204030f12170117070b030403031d150708060609030a03030507030f0b0d0b100e24031f020f0903010608010f2009060a1b110f0114040b070c 64
    0x303100000080d50388080d0b4011014544000003036110341684444c49a02c0d00300c0d414142d107050b000d81030081c001180290700b401119008112a80035500550069009070342c0880d8680030f00744645181c01004588000950020142c40c041400300308046500040506010320a0380c1c030940032800764420306070142d40c5802032000321000c050b0154402d44c0030b803909039400c200240f218186101110380042d074859110031159119000602e000b4130169010210006281c034a0b941c0740194001041d040d1001c0001400d19107451400e0030301c0b8070b80364031881002c80040075003103810780e6001c42283d1302480100d0044d80010380c0c100340c2000801102d50240d4068000c00003a551801258001d1100102d0200902d040284000001c0d404409401c0750510b82c402a610309130040c03081080c55409440e0400a110564080010810482030038a50440c0500d080641d040000c00c10028610b0300c0780d07a00c41c14800e2600104581c101c803402500c0c250703600000485d98076003550a1894036071265038060300e8201134250 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 785306798 1250 785305548 785305553
    0x21b0409021c1b0e040602181201050603150126010615020705040e01020c060a1e0e061602061b0f2a010c020a021012140c1c090210051c020403 63
    0x18481501500801100e040c4204038250707106401c00d607215180401810134045804945580c1c014100031004000d25100c401c5003201040141c460702d00d0b0030101c0e035501d4082100c0c80c1414006504540e17440380008160358101000f0100741c00c130171403071480c4d00c025000b4580011002581b01c035001d800811a5a150540714240c025030b90f0809000d01070189003481d0a2100e440b81c140261021020110040c000030360700c0205100050100f840c60a4a100e17100600040206071403140803950180f41001c1c0c0032902d800c2d01c1300a5410541c802e944210340c0203500304055403000750840d054040b076040110359550ba0f0b8030000c000318040c1355400050301725a000640f4043c5c80b0f0300480040169164000d01c40300b1500c0310166114081e10b500a1f40092000d141c4628003881071141040b6950041d01c0018103400d00a40500100d408031140c907403030360b400100c0210020720401030f56007101d0658002e200625003a4040748146209800e41002d02c20049209450b01d4810365054180c204695000c644407541c90 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 785308048 1250 785306798 785306839
    0x80415021e010c020c0402130b031302040903050a0806010807091a0d06081e030c0a03031d010c021609060308090d1e050c04180b0105090601120e010203070206070906021b040902 78
    0x100380350f0b000f43c4169401c0038014103190003502c1310101019070107031000c0d10341070350b1500951006201150000401000d0f00040e40c403440350480c041d001e50740d010b40300c441d1248068801c4002608040c144004202042345455111030850140c0341810f030071100141703424001541502030700130600ea080c1c4c1440c4021488200010750f003500c110000035808251410f0702042c544a206a032030114498101e16481e1020900a8200d907101201106c0a0a4403079503840c4480d0071070340c01520036401030300710300c5030303a0340355908602c455002d03240d001000c0050615641c0c4920305440b80c0840c0354002e02d843c240e00c2083c46042030445600201c1003c00340030080141c40c0168a0344400e5070914400c61500b140c100c983c4086410200c1480e900c002050303110b900340740c104100440010002410844102c032010300300e00c3c8500a050b403618020b8000358503420184130290500500070211410000700178030400900346e00103130107680400a841e010490056003000309001d030540c01c0d0065041600c01c4044a88441003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 785309298 1250 785308048 785308061
    0x5120c03061e0112080301141809010917090112270309030201080106030e0d11030405041103090606011b201804032a3903060f0207080415021e01 64
    0x65400200380c3c3c907844090b0000c070705101c002e40518014001408518400c441c075260f0140002e01030b458910852001562030842114020016519000380c0802c00060dc10f001c1303001d451101c00241000c49407000200318000003a03603690001d450f1a024200813440180d05d003007041c00211004030340855402c014040c4900b5100403070004000c1c60000031514400d11401c003603448400041e2044858039201103070009078640262240380010000040d643e17035a40700c2c03102c0d0701407000051034691806094040c05e0481c02030909050166540d00d02117000618000e41c2d00741c07030b80038120341401ca641c8044285820880c0e421180c001c86c11f01d035210400c070109101e0303512851180e030f20004410500f6240e00c0d03480100038895030b0030f10608400440000c0800259413134a0704414a0914107044120f0100301d00302c045800d4015140b1091420310510006004503200741000010561030060305640e2120030f44628401c0354000303099141c4c9020068801d00140203054040d012180400c0303011078400d0300a190 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 785310548 1250 785309298 785309341
    0x1005090108030c1501030c060e040e062a09011b060204030203010501170118030e280b120a1a040b01020a02030f1c08040b0403030c020a0804060507030f050c0705120c0306 75
    0x90313034590807141900c40e01050690fa846000006082d20b0308400761200410b0031001580251541d08101d4400d008014451180e1780c92055020301c1000280d800c0d10039a5444040c000c1c192080001c4640c6981003410410302d038203100e2901600443c541404802400b568100a500d5400c0600018514603400d040050000b41e00e0020820700d5421103203201c820803240300003004240344000d142311300e160a100d07000c212420001c00060360011124004504201600440c042080200310380072070541000000d54816030442d810003804108a420384100b41c0d412013010b00c25911080722090701e0344280300c2c840805502030102d07100340703c40d0b031885a00c5100560740c47c01200600265059031500c5440e416000c0c82d00100c81a80e1078695813000c4000d8102141e1010952182d00412740005422400400c01048103580300f907101d8000345002810300114043c0c2404108092021618901e40421580101c1c3c0341210031050449446c0c01d60303801c0080340494503615014001c10040c07200003000d800881d40c0d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 785311798 1250 785310548 785310553
    0x314070305030106090b12072118060e031602100c1a011a180405340f1d040c1202040b1201060807081b040e04081207050f0d051005090108030c 63
    0x10b448500c808002e020347c922907560400744e000400c240501450b886001010a64140500b50340400c2d088426505500140c00c0303030f40074604048040c08002e02c156620120b4071006180b5054002541102604054030080e22809a103035850b542140039180009004c0d504c22407681c500e8060754903641c040382007407227107054100d84240c500182039214000c4860000d00c100703031061143c00000c1072200405008002c01e02815100c1070040f503a040c4081080c0d402581000e0a50500040c014020104a0980f01060038803060035400301e003000300c020034100c41039425140040c02d10881c0310701302c0e28201211601101c80348001004100c01b01d10b034000386500035010b034500e030a80e40d03105011075800c0300444411001403040d4001c01c50200c417a80c99800c84501d402000c50801d62610b0b01d40340c074a803060718101d542410020317030040091034180102d9030119483c1000b50404071880d20580d00c4d48140c035540040d9036501d00001d007008046141c0240a4640134004050a40e101c00e140c56481e4001c41840142d131 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 785313048 1250 785311798 785311817
    0x806221a0a1b02030d05100503152202090424050106090e01080c0d120c02190311102a120e1e06070b090309090f01051810060c0314070305030106 64
    0x5950b070300e00011403207080780c1c011450881c19182c0e0700010480a001800d21030505900000c440d60100005500c2c1e081d41244a1400d040100f5458012010520a01d0280032002240c40150717484e15142070b0f01540008048103040c003886210605040c2e50484030f0b00491400c000802c2044e0f1280c1d0038016980c1c8141007015503602d07102074a81d24a1100c411607444105001e0000c0042c03007101840c9032600480c1000c140000244c3e00103400854035070800d14000e240140100b060082c0c034180038151607019521a030522000e820020b001070000511009031030010425201c02143c04015410034a800007403a50081e20383e000700402c0ca0383d8006480d8071981c883c4580119217003012489000d450300c0180705902d01125507560880c07482d001801c0790080d0000307100803102030301c51142c1c0f24442d043c0d076544100198102000c0090414984407001e032540c0ca4581003240381208011a00c098035181d0410640b00034161400300c8001a000324be1045841010400e4801c042d0844040c605840701a05c852421 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 785314298 1250 785313048 785313071
    0x10227040609050c030705070f0609082107020a2616061b020309040507050d1e060602010911040e1c0f0e0402160308040204020f0724060806221a0a 65
    0x181c4500350360542065004002040b6200c7c010001003000a1081c43c400d12424036644a20b401c0320f180c85000ea942000014854051020720503903945007050b180515000c3d410001c10080d91010090300050680c14107600c2c14100401c0d00e0317881690a003600b21656070303c5079403502d00903aa0320344250485806003040c1c481a81d80003220f61505643e05907078015802c0590010030040030380009020030003801000c001002410480e806602506410180300101d05040c014454003158201d500034000c42e40350070214000160781145040c000d030350480f0003040d001c00004d401420a0400d40c9004420a2600c2d410020282c0000e5024050714442e144c4005450f4101d043c003040c0c0c4111070310010000b854040c0d80002074081c10001e60000d0018000508202030401c1c2c002980d0b0004406a42d1541201102445030580340386c40449800441b0b01404200d1800c4800e5507124409012024100c80408007407a80301c05d202e147c4280d0b10340181c0323009508041020000c071362250507504107608508140e809981c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 785315548 1250 785314298 785314301
    0x8090c10020319110a0f24090b0a0507121d1507030507050703080f091006060201020904111813090c0e010302031908040b0a0c060203041a0f01060e0d05010227040609 73
    0x60715000300c2c000e0074105025580e0039002c0d99104400321f0301c0298026502040841032031803171051040010001800c1041810080b41c4860001e00c1c20f40741608140400141c0b0b5801403212122600c0c1070008640b82880d2100326041c410f07001c1704509240710b44482098048603803404540600360f140c038200a26103c00f8000c6509125421001c3d000c114030340007207030a0f4043c07860000e5015410109807050199801c1e5400161101a800000142e4010903410310760320301032060440e8407100380e0280d07181030782c0708152158408049594601c94902c02c40070b800036504030340081c640b4640c842081c1c854651600310700b107071a8000707000503400381c810700c107180c03141c1481265180802c0740c002408508007031410460324180c1c0c5c84008058100040e101c209800901140050350107070b44180c80b02c81c101c0b4150000c1400c01c180080c007403004049800b00402c4095000b844143c00c111003510401d01c481d00d28213100c2c3c0a8450340c0100c00b1401c030a4820f14140f00305143c92450101800c031400c0c0009640d8424540 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 785316798 1250 785315548 785315567
    0x1302090c04030f0305091206070f110a021c05031e070317040b27100209040b10140d02040b070506040b060f01081515030a050103060b0a0303020a020108090c10020319 73
    0x1003103032900120fa030700072a000d213026180c04a801402c5410441d0100c0466003880800d0707440300080341001031403049480c0c02c56410402000108001c10340400d0740c0c0c00141d54008100380703803104c4007002d080301001c2c40003d1007251100c00c1d80824040b000750540e8185c085a40c007070b1900ba0001540721000359100014503100b240180d41100711003516880741c14040010030203e080c001d542a522034285e6050550500c014010003008520050700d520410003840151401c41d40310520908200911200e040c0d046030a281080c20000c01d1143c580000103c444000d101d1500b04151902c070114074001000000103100e031080d07202d40b031204010307201c01081c042030460020026011a8003080010402d90360040800700c1c0c00703001001e0030248003100c541c00002c0c2c3d1040c0c40b0b1081306501d820061051011a000d106c1c46248151008001d03a0324544000752642e049000003030400c890600841c40781e0b4010031000494400c001e00c03000f88040500c0020b982c1c1e60000304000300f04201603d42900305809020b611 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 785318048 1250 785316798 785316803
    0xc030801210b07020709090c080715080118090609141b060f07050c0d030f0e0105030c0f07020a050415061202120f0a090501061d0f0114190e1302090c0403 68
    0x4800d80915542c0b11014a0018207480840c4194040021070f65101d016102c9050f01515940e0031041c14070040a00301030954001c1104291304001168003564802c0086045850151825041040c4050f46202406e1088400740441e0b041c04244018000041000f102106071141210607070b941a104400106100c510360640c40b00040c425074602c0090303032005210341f40c440d105035980c030300040c00000e50660082c94283d00242c2030904c829031042c0c1100305000f0320202401c0c542d043d0300e001c0d10960b00303e02c00da03447d1350f0040b00040340308011034885d150080060709004000340010b508284005005c40c0300c611900000500c4000802da180416108070b90382081c004132070f200b055036005111a900b80000d00041c005e6030303449c094000400e00a11401c00a0720340b115107848400144e40740380300f0030703c8003a1032204100204001001040c1924015000f5102d06444001c0070320400d036001016810390354010f440034900c886c00c000825000441c0c49180d14401c85038403107075403100c2c0001c462601950000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 785319298 1250 785318048 785318099
    0x10e0d0509090a0e10062d1517150315040506040f081903020306040f0b09041e050a031d09090a0b0c0408060901020408160303091206061d0703050106180329070c030801 74
    0x900120400c8c031917480e8009100e0070842120b007400307440d02032402e408036110301038250080d0340c2603c0c80c60140445603a00c0c524482c0d491450400340c5629490b148040c0c0020041d07281105680100030140d41500c401c42131503040028001840c04018002c1c0d0310803990382e0b00c034a28000d9090081c0c44940311300c20002d41c0c050443d41c181e0340c0f50366403c0322005141c00c10419003001c4001c4000081d40801c02c3d10b5130b8910a41c1c60750005148003681e042c0140c1c1180c0c049214010550401c603801f0800610402220342001410559445110ba406c41f10f1095800c07840f280e0140e0800c000c13403000150028400c8900345021281403c82c0044801c4060703440380001400141c1c2c501c0c00300108500d808081680f540600b83c0010740556401000722075290a0f04003004144035403040122050705440f5103801844182060141c41158020340603004806001c010000d001c81c0c46c242c042c0d030b02f090322000740007625110042030034100740307102403e6155200c000302c0009629400108100324290466240c1c2c074042c641 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 785320548 1250 785319298 785319389
    0x50618040615020619061715060109030f24060e0f0f010303091502010f0c0c0303110c030405122e0c0906120b19120203010e0d0509090a0e1006 63
    0x1520000c0c802c0031403248142c03503100200d00d0111f0761142c40ca030000b41070000d00028200b15140080f08034014240c2e41407007902e030320400c040303032044901d051129800480310100128000601907140c20704100d581c2e14502e4a00041180007a0315081802040b00060001c01ca90341c050236510b40c1c810034000100060100d1804000103241041d41102d00c03803960001040d000c542c40c3c070f528100c440100d006800144588407070b00034036400d8454044090007a0381a14582414444056500d10492080e0313401a101100c0195148800340b02c01d0382485038030f80001c2d0036681c031065031141250610541d0a0329a280c4401108401e000704c0300f440803900b40c0c1d107441c4d400c06042804100100040c203001e94124016004404056040c9400070000e880d6002030301c0c5903203049006045c02c4500402a41803030342d04c030416503c022604201950418013044501000030354804030144090310020180080701d100360b5211181c040320070341012054969111406500d6009064101303500c0e6110ba0404103130504910 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 785321798 1250 785320548 785320561
    0x501170717030705010c080601120c0906050901230319090c170a0506071e03060503191403040b0901110c0f10050c06010b09032a13060506180406150206 67
    0x4104004690100030b603418a08103868007800e4644040c2e5960018040b80204041c42d070300091808416113400780100000300000901034070700351241c0141c0051100c081041d01c1641e00ca0441110051030180900d820955510321146c480d41080d03880c0502d55080d14160b00302124141314640700d4682100744000100d00d001290010100c035400c4180690040304c2d43d940104804011071801a03445030345248000722080c5a0307c61181c528510881090b0904108211950700054407031038085e400c409105000c0c1032858401c0301c160704100f40d00e019020102c0e001515040541c040c03c5149000e0300d0300100000126862611450608071050703110884000c031309018206103c0100e454a01403c0140c0ba184503600000d11b030280c00d9010071070a54000803c12a2410705100010700405840640b15600d008800d80f846091003141038140502c070003c03041400d202e81500880700034070f0003510455407510224004039600c6042c00303130a4091800c4c010001403900340141c015010100c2c0e44e01400f100d45960 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 785323048 1250 785321798 785321819
    0x605060f0306101116080609070305100e0f150a06050a030510090519052406060301090e011b0e09091b0105091f021f020a0e0409020a03060609020c0105011707 70
    0x4001d04100080090112504c200402800c0c3c01504d00d042c103124041e103050303070035072504200400808082e0054030080001500020303250000081040c40407840e481401030052800c60302c01005080d511910200d510300ca00c0c980c0003280a40381440c000e016554860341030144d414514400280103502030850740c06c1007101c984c844103101e4071841c02d58512250309802e0b440c001d03c072a08141d90b1a0040300185201d40a0100744441c281d180c01700c0041c8628007480001d4142c0814443c0c084a2600c6880703100f000a000e43c0b141050344c104004031003000b0007500c00209000c800300c003007a00644803400806c080d1000020840c0a0040b2000c4c100c08508010004407515040b40e040c854100e1581e02448070a6030304040841e22100181d801040c03010303101d25466020199000448015601c1000810b454661040b01080302c1c01c010f40300415000114804112940f0b0154000b8040d54071700400480c0c8013034290024102080c0340d600030b22076070b40c80f601d2644d115062108046c07a5940515020054050603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 785324298 1250 785323048 785323069
    0x6150212180d15020307021005090a120503070c080d0911222d090308070c03020d030507170c0910050909040204090f0602030a090b0c0313060b040e07030b0402040605060f0306 77
    0x510030f5081c16810344410501a40c105460003405030b000703c2c000744020034880c03052030f9000890384002c100740620360310f9041488915a0110040000000006002a0146186008140d0b10980c115912a20200c2e28801070400c1001203a00c0110000d0350708181ca0210389aa0f0b041d20b40702c00368203520301c0c0d086a0100074101468442088104902c01030210782e04030604488041c0520000b0030804a00d15006200f110010325143c14002c4c242d503440007107540020241c0b012880f0f07040002c2c098a4040058440111141d00300c501100d02404200e4a0480c7d10301030f098441d029a0780e011071072544c2905640c540a00001590004000d60018000d840c140d0410700b000303405108800c00c03030482c82c0c40e54130690340102d600d04100358075481103108202c80c2030341c11a400141c0701c440d18154280001c1c94203098600040107800c161322075413104040e544079070181440118180848622985d24603003179118150484003039214a00e0000b0000f690b081c00011205001001c51140b13180d90b0385c503810081520203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 785325548 1250 785324298 785324303
    0x6100e0a18080a20070911041509060f0e060304060c0c0b040b0114060f031306180501050a060f050d08070c0e090105090c010e010512061306150212180d 67
    0x125441034401c14402446603031041402600340c1a6a0243ca0070003800e20304080c059000d0104001d14071120084011a44e107065a031110000715098101802ca03c00501481d080120004484010307142c186410104070800c4810903160482036075581c1c14141c400d04404a507058011b941000010000340d03581d400a030002d1400c2c2000c1007540480c1e1a4000c00c46400c071400c580b0400342c00018018404d0550051000d00c0044890600d00110b40c1e03140702031070001a001c8021514280e00c1d1b001002110b400420000c444080c11041c0c00c10309046c9980070306000e40b82e800b03580340740180109100000140c29401c0d500040c04207001801ca640d50008240d00c0300e88140c07490b24850102160f406001d0150a020700100000410b030350503c0704840e03060480f1007030301c581480003410003185d00380d0708803065405010004004203115a40d200100d00d10500c03a038120301d880c525001000c41c111402c98120404000d00d907085805801c040702000c042841018144441c0071401c14040c02c492900d022044155031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 785326798 1250 785325548 785325551
    0x31e1303050303011701060b03070917070b0a050d0b0f06071511040312020624040c0e090408030106080108151504020904060b1e070b010b0f122706100e0a 68
    0x280d40e5101d0070300310780003a04040030320aa054210b2080d0102401040040d20308820520b1560411203005040c086003481140b0145c010001305020905003030000500601c400a03a07140e880e01d00781401003c80c3d02a4840c42012458044100d5031401d14140c001c140781c1c1e02401c6185404426211004001802c0d0503003072401c1d407580d10121007046600060030040d40300e00303208a0314054010340039081440050440c0851895582c61303001541c0000969202e6607801c1c0c4d40021031002030401224607540d240764441d008400001031204014003c001541226815a01c90b10148d0322404007035100c2281c500845040c490240210300551030400b170007250b4010041c001440c0c4140c4101040998a51b640310107002c00010030a0039402030380d40300070309243c4014112145007004690310344845ca003041c064044a0354001c140e0320801a1074104070303003000c04103424541e124641311124420040d05030241c1c860200c1d02c1c040e023400d0490005585805440303034180c0c1c0e901140c1090b450203602d100041014402c1f5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 785328048 1250 785326798 785326837
    0x1902090a1e090c0903030f17220506100e01050a0602150a0605130903140a050711031e011b0309020d030e060d020a0e04050603030c030403060506010c081b0f031e 71
    0x412601c100f540c084100d80390301c642a451810090518060807600400b4415181b050364007071000032401903441243c0107440030800182c48849402c0c81c01c0900c0090a61090105010500e101c0072221002ca03450090f4030111680c031003041c00303008050b500c15a80035038031052070b90b03110a0300c12a07419401030804000082c0b166661000454108800c184002e000b80d0b20041072040c541e00140388841d01c500424280c0c40e101041d10300811030300ca6804094100700801c01c0d1030070745590612941c01c607000d8451b038a4230140104d0050b140203240b5100780217010019802c055200f54040c1c0a9108001d40081c40105100700a407000d60ba20030184074210303800345003040909030000f00b61028000d40d6102c1c1c0c0c0da40030100c04003428030040f1880071704210b1203a481401005030b00580082150281c0754803100204154580c2070058510820030780c00200071400c00f1070413002d911408120380e15000303e80c00813602c880d010141c03025100d20802225040d9000007604461611700b1840080060900000400140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 785329298 1250 785328048 785328059
    0x405030706050c0c010b0306090a0b0a0b0a18050601031a060a0201060312090611160b0c0307120c1a010339030302010c170c0a0e040b181902090a1e 65
    0x12030b802101c02d103280c05000304a4840601c1c0c00d10038410180400d0300201680c0c140241c0307031603403071301d18440c010084080d400000c3c00300e104541143c0750080300034105200c00c0303071102041502c460340410324500c6c1500d0100010300c95032007801022500346001d1881c90b1503c61003014030420382c3c0400020815592079250010000ea512502c41005103840d581c0c0b446c1050030050010140740455403110020340c0880306a0341c4055440b00100100e4807514085591540300111007429070269a03009821489800c84440d40e454002d520178a00c5031051074a5072914034940011011002c0a01000e081480c2088800071000e89102c10122004411824002401782c80d12210102002c590002c40040c0d44070310a030000c45800120b42ea030700800020f079904c1235141a042860f01e40c0106104042000000d24489035143c440b540f2080511102500c1820984885801300e40c8a0f43e003610103c201e42c2c0008803002d003007c0741d8400c1c1e0743c0f0100c008240b8420035141ca00d256103048c000107a820058103221200041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 785330548 1250 785329298 785329301
    0xf050a051b240307180e0901091202010207151a0a0b071a0405030a0e0f120c0102120705100902060c06070f03182613060c140f0303010e0405030706 65
    0x542003940e40c07104001c01050401d0100554a8402d000032100e201601541c003503007460150b0b0b40c428220300c1e10030038800145031080c1950700664000030030704052005101d0100d50640000b0982da000b0288030654244e010380072800c0713104414001c1c0c41d00e03143e80380064041c502c0d60421071081250004c8030105004100014000d004150711012070628006004020003580020242509560446099040c034080d1282c41e280e2103694444010003514000444650b6520700d0070950155014000e45074a05030707040b05e9582c4980da8003546000d03106030a90f501c5182e038210229a0219030040142008120007070492000c2c00c85054201d92148050041d12086041044024440ea00c01d030381d03028891031301c50000340071030340c04150032050b09124504080c0441c08041c01034881a6140648180300d503c10034201280703018401c500740703e40f4000c080c00110700e54080f03101d0104e14000c10a040c1c0715a00c400300b0035510812041d21100341e410034001004503840e50605d880e8050b000d102a20714010f1107903251300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 785331798 1250 785330548 785330563
    0x4052511010b041d010b0603070c260c030901110c060a0513050d080a031811060d090605100e180613060603020a09050a0e012a020a0204050f04050f06060901030f050a05 74
    0x183e20820483e51000144c0901501d491210141c0c1e000d0b141d030401c102e00901c0301085c918041e2400c0c2c1c40e10b10031f1602c090385d00642d031004100c0c11026601c0340d00000d1070a8807940050852400a02203200303030b4801c14008100c8401000c402070140346003010782d200582d09600a8030f000309550241c00400201500d5440c0c0c45001c4034030a010841d624000340b0300150440718401051240ca405010782940054420b85004001010403100142c44560751415a009000d0000e8028121030030001840254100108c8a078145c40c0051640072135581c1b402d16100c4800c403901c4001070039a000001182104000c002040f107401e015550201e4015200e4011500424255100401c0395a848003082660302c9584a042c01180300400203111101c3d0340c00080e01c0c448200c2d0041084e80300817a1038440b8a50003042074262641c1c2c09803050101e0304c0d0412000c860a00c0446041d25107001b030020300411030501043d450310400c2c00525540039a402c5407103658213050314203401c9030a4030640c2e42c4980030400800240 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 785333048 1250 785331798 785331821
    0x130b060a0206040c0b0a0c02041814011b050309060a150e010e0609070e0102060f060d1712071e050912060906010503010b1c1713030302010b04052511010b04 69
    0x400042c2061324042080c1546944205034913902130000b054400e40c00f070705040150f5012100401d42c03400ca1041100c6c51001180001d01d5192800f00c1c0881080301074112030b80e04000c02c90f098500c0380c00e100060f41c2c9444202d80b5511141c220600050418409038000b104154503a200e034040f40b0b0f103841c400d448007038082e0400030384100940c2c1001440d24151161551142c01458a440181c05400c0041d680750f20140c402c4001e00d02c4900051400e0702c6010388a11050380050103203c4c0007070702800007407071a4840d10044032001034084c000b504042c020001540007500341c45c1000308a08981a045840d03400c0301208a6110712200190301d4054030400405004104000c080c0105502d003008260031501c5a86406010f8130520b604220a46035035404004030541114004585a4101d4400e10040c4540010803041002c84036000c4103069055000d00f18120045e00d0400c4981c0f00c004a07101161000d4100e12600c41c0120102810644101d4400381d5a007800700002c15100c0d036400003d01614a9032900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 785334298 1250 785333048 785333053
    0x812040504050705270103020c160f06050301080a0303020702010e120f070515120a0e01090b040303050903030c0a030b0102010f0c0e03070b121b130620060c09130b060a02 75
    0x10301036407425100c0c6580100e01c50030418580510a40e00050490344c07110602e00501c0022280d2403642d0081d01141c010f481d116090f00e020000622182d90610f050740a41c42e0501d03c0754002282c1d02d0300840c1124140c600c3e61005050701885560210040d61161900b01c0c10004c0141154140c1d803030704140c00740300310b43d080003070009513204070b5043d480c2c01c40603400103101e840c1444c4100088000b40080310817440b456030380e0b0360b01a036404405a01410b24109001c05c15860501e1080601440440b081c1c02140f00355014003e03038403240b5450380c0e64041994698560002000080c0e6414041c1c0d1001c8004541800041810400310b280407044621180160b004507000c583e0006080c603041c026880603143c81100c160504502d0780b0840750380e01c00108000203007421003c101e001c400113207059420080065500ea11820b48503034006241020072a0307002000c03420032091000702000865100d100e403000690349030501400a0810150420002064041a40c2c0d00800d0f415621942c0017020880410f400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 785335548 1250 785334298 785334307
    0x1515130308030a0f050c04260d020f060a15210b07021b0103020c07150c080406020309010e0907140d090209161806021207170a0c05010b040c0917070812 67
    0x126070054402001103d1402850b02e030810117981e10840950b03040e68000c04880580f400394a0061023007644201554a1a1044100b440301c210782c00103042c055520700c0811380c9d1890f11901c151070159185480c1c1111020134450061020745080c3c440f9000218446015015000da6621004510981603401c00b005030840345020350403400301c245a0100c039500380b034114070381002d40c800c903600c8420f140110711000c8829401e06031658828030a400c00e00c3d40007990203a61369a609400381d541d0340b0084d000d6020441300e440c510050300d82030740864411500d035151007100e8144410402c1e40d0754000300070406e01c80e41c1e405074200503071a4000000c1c4901d08000400900e031a40d00000340c01c1b803050303c841c4100a000880d00b840541d60100e50101c09550500145c1d88480051401c558018450809000b40e070001141c030701112603015540018035030041000b002100c00c65021312060b66840c07880040401c1d01120204440002039440d445400c100c881640c0c1c405850320070407400d01d01d1251044861441c0402c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 785336798 1250 785335548 785335561
    0x9120c15051c0b0a0b12040807020f0a140a050a080312040c18050109140108030f030a0212041b091b0e271801090f020405060f030304180b09151513030803 68
    0x42481010703107095541c260600c503000c003044c0c051b950000d000400100020502c14115250070750013100142004294010054840e42d00901c4d00e12041c448502c589851800080c2c42c0c10b00004000603101400c001e1031524080c03e061104148000c3c0086501040075040000c801005400c4a400c07841440c0011038103514140c00c1c0010342d144131000458081d840f40041002c44000401c03501d04a01c088822500c981d071303c0c0c05400c000d0169407a5290001504020881000f1880d04102500e07c1031750f032170b0381c40c080d02ca5400b0703821514200c030802000c04101c1d40c078851181c040c0f40c06040282c0c1c020110004502e030416a100c007152014010740012480c2400d00141c02c8140489511000c0c00800811038440744c2d0b25240b28000303190902a001d46d0355600421003944078a101880c0614000c0c0485c0d5035903030b480c03501d00390040013400750b50101031030719103d15140d01e80b4a0030b880c01142d180020140b03011141081100310303e66080c4540040504000304190b42a030501a40b008601881c19217450f0724150 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 785338048 1250 785336798 785336809
    0xa0f080609030a0e0d0804051302030621190f060e01020720010c030528020c01020d0201090b07081807030c0303030501080102131401030f020d060609120c15051c0b 72
    0x1e8460300042e0028800d0a04039a4032907407400c950041202c03000e403c2649410400300c0c07441240c105c107400030205a000d0394401c0c250b400440c0900c0055400083c10107034083c10350b801003124804007005400681800c00312600100070025a180030700c08240d02d0700301603541c200841e51991803075041c6940204240003440340d1280e055600c0c2130915184607203c40304400091070f80340304040003024400046250f9420340202c1d610350410300c1d500105200c0d41d040c2d40c03502a41c1d03101700e020601e006100b9402100c610300e10600912340300c00d600008104180d102c805007030f98442c000412480103842521003889805104105000003180614000100d40741542402400e41e541600714403c981e00400c10742d80003000200d50901194400c034040d018840b07090340101d010f40011000741042c5400816401c0300035109070b010500b2503101e902c0d810540d5039660107405040310118405403d40c402806c04014001c0d5000040b4030140c0076180c881d1410701203400042c240d420811035143c0d42551020781e0152030419 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 785339298 1250 785338048 785338051
    0x10311090403080604110408060f0f01080304050603040f0501200a0909050f0a1d0a110a05040b010f0318020d0b04050c040519090c090e060708060f090103021009050a0f0806 76
    0x3525440c080d80352946015100e4030b0054061400784e641c03021807003a03455450098901030100f12096038010b04140400000034041510150314aa0f004000040c840a0010440d0704407a005491141540d942c0c0c0c860f010700d000315050a94081d500e541c04001080c000d11341c030303456440c6414907035a242c07500303918018031a100603007101214500c0c00040c4030707a004030141c0c116400101c280c00851303102c04140c4130343c10310743e076910b15142039116940300b120403c040784030042c0403041c00b5560680a0303039440701004103540c44150b640d40464018501e59120030312940080b40600291a21040e41204540c040360304010717403100070345201c880001031108101c1c00780000c480c140c400321800e12481c10701d0001f40c2404100f507101c1c00c100e02daa4489140400c5241c41c081c0004000d0842c0800042d1a42c90181d911400b04680c024001903281000580920b4000f40c01d0f00c00b40409048082d25038255400d202c035040c14003201034180700c0c500d400010240e4a0354280c1c0c000e4200c1210000c03140d031801c5a0f03103140020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 785340548 1250 785339298 785339333
    0x8010e06090f0c0901140a02010207050c0405070c030507050a050a0b090118171b010504050a5a230f15071e02030315010e1f031e050103 60
    0x318082400154600c001605410404000303c082c0d55404100c01a03d0b0501e0440d1400c0e0981000b10346400100d03010b5010340740c418000c0c81030306e042894020800003214401c07500c0b00080303984040f03100003081c4100082e014841c0b00d082114000c11503611403925040800350304485c900d000e00d0801c2500c800a00426443c80784a03890700000b40048c2d83c507120001c0101c4410901c0800200740d03140400c412241e030380300400800008202c5824a0f042480c1c80d003821303090644280c410350a005941001c6221014040034148003042081d64800142c2002c1d0303040d00603543c2c0c01c0601000102c404002510510203c184511080081c05e40f074600713002c5600f03481040c1010187c11201201802d480c1c007081d4000510300c02c400c00200ca41c4c038100c06590004802d00e480341d42035101d18512500903000802036010314440c1c4004e4040c080700380011a0f50326200407034140c0040441c103290b01d04030f1403442440d440301c01500300843d0040c0b203204000c240034810300d020394400351a40010400c0c0300350280078500014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 785341798 1250 785340548 785340559
    0x30d0b06070512090d0b01120c0806010e06040c090305011404050d0512130614040f030210050c0a081b0706090c08010e071a130303080703050a0227060d050708010e06 73
    0x54141c031029180e20000c0c0f40c40d00c0b4150000341491031591505d640720301055000a074804296152101d00c1100e2064600841c0e041c40d0905010403400e80000e4854100c4900d4134130419140da030002408060304061001c042841001100031002440c00c0c003848000000101c1c13007400a00c0e05092a510348400d1000c80f20a00c071040020040d0311209441c032640c4001d0486080400304503900d03211001384000c2e4002d440c0019142c4c10b00003008012075400510a020b68201c40b1490041555402190002d035840c00c1e000e001080092101030246a0851f0311113050712a4028900348000150700da648050401c42e000c580c5c0307200304000c004031002c03003501030100c020080120101c031501c0300e9034640c520300072901c0e070b0242840c1c030001d841464422194140601c801080c0850350b20302d27019128040030754048000c00d00b0321000580304e02c0a803081d1000300c41e4500d4090007001e203d03089014074804000b00942c1001c41000091a0b070174041c054907000d441c0704c0c3d40c0c01e02e41390315044010802c00d41c0641554401c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 785343048 1250 785341798 785341807
    0x70609051302030903040306021b28030f090b040f050301050f0f0c03090705061c0b0d08030a0c0e041b170411011b020904050f0d0306080d0c02060c0f030d0b06 70
    0xd80741c00c40440512a004440142d480d02c600040a2850007594401003100f400080c9035102031040b00701c20032144054104507203000a6000d11585100e07100341300208000040c08145000c070b03100b81400701d2120054107211500350380341c0b40c003000940d100e034020740c551800c441010812030400b4400c190340030800100c0105941002e07903201c0070071180a08168040d070004030100d00c01100500c044c1004260040c01950703510440b0581c111510b00e40403151107440d15218042800e800c10740c94890700701d07900c046101d15550b00ca03008031004201021485003009200740f0301304c00c03d4403144507030701c450143d058130031811051201000740400e08005403a042031044800340f00c0015009644100341003002d00b80002c004000c03070404004a201601d01940c04800c003400c0c0000e1081c0880c52881101d50346050300c41d800000f00d026002d42c0c0d02ca2081c10810744c890343c2c074089803c0c8180e01009030a440180b07270700d02d00149162520f01e00118111550060381000421104031400c91090310850241a82c02c01d042 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 785344298 1250 785343048 785343059
    0x2a09061103130b070201140a090504050c0a0f110a050f0a110d030e01140933070f0f081c02030a0c0e0906010305040213090c0302030105060a0302100f090b0c030309070609 75
    0x1620b206214032030324070a010075900116030040d0400b070a42d44116505a0300c40000382401055040355108a6015501d05000f180d500d4110303138200c941c0607181d5100c11000030398541040b0740d00c0341109010b0500d801000680d1300051414481c1d46105202c10000304107050302401d0035400c2c0f40c40c2044007482201c64080c0240006e1700140c84c1c0002c00e009082400d6440d0a4a904419501c1500b5165601c100b508400d00c0c3d16a0401408078100c591040c00c4c0101050b20040980e55480b95107806011420086203034800500345190058105204041060915140c21a41220402c021202060042d008000c02091020270f200c0d02d0341c0d640311031402c03c0c1c0d0400306d080890000000a48031504054942c2c00040541d1540d950b60a040e655000040040440c0790401081481d940c0c041240301c4c3d401c2c100481c070740e0300c0c15001503019a90028519145801080b81c1650000311620100050100c40c1100203940700c03250015240750108007015503901c2ca04a9905030400005070840800c2c40a0400103015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 785345548 1250 785344298 785344327
    0x90305030603150f180304050a151103041211060909070c0302060f04031715031b090c03090705060d0e070f0501020607140307180302120d0915080a2a09061103 70
    0x10800c0d080745d030076040d015082c00c1c141e00f188203540040d600100b071200e000804000b902d14224851a1079518940b0100701d0168841c1c41e8417a80c1300d0a0302c840740c901c0d240d00118112510403d020140200314615010054011500d002c2040722841c0120740001c00402c249601808240c2e40100071080d2400180b916036005004000085078582107040c4440000b803c0480c01c1c43c241480c09002400c0f56400601014000030090881c0c41d41c5001d155040c010900040140d03080e80e0082c0c0340c032000341600034242014400c082e00812a8061450f07240c070404091860203008030000340001001c25032005081000180c54400702821003001c1003010303000c0e1064880220280c0c2c1e00b110451510258902c86403008075628095908082d52103415540244400c20000402e611000500c0d220303168590742e030742070303000400e8641d10303800012851050002c3d55050096024000b510078400041030a11041d00d550f01c2e40c480306100b000045411124248601a0800001c0c0d0049090070000c3d45480c1002c401c500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 785346798 1250 785345548 785345551
    0xf06051e031e0a390c02150c1b0f0f01200714030f0a03080601080a0f021b011503020f06030618090a110109050907080a0f090305030603150f 62
    0x101200300100c081605040400e2880350811075072035844909051050002c0024a4a81c02c59010310116007001c24218006158031048094030001c007070140c402c03d440684000000e100d007240c0c4841c090728519000000940030341030709480d5030b004241007049492041c040c1c68210020b00d1180d40100c148105640c0c959a900c0e044003401c3c07808040380c5141075409070b4034021003200101030380111035001c030780c00b4002000088600011422542c4243d00a6802600e4080b000c3d8041c00003155400000c98a500900078035401c100c41201c0014801c848440840c100d80006207200c3c00500b42038800030144009005490900e5140e84100ca10103107158002a031504107000c469000390004070024a0303036524095402e14103d071076882480a0302d4186101e40d00c032541c03040c089a00251000c501d11655209000710020354601808000040d1918032050324071480040028103000c1d10340d0520a00d0a5a6002c1c3c3e08d1151310035214140c407070800100301403e0440c0e8943c1441ca02c002c6a04004070550804100c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 785348048 1250 785346798 785346847
    0x7230f07120905040f05060301110406020d0e01121e0501050a1404050615161a070504182009090f04050c1527010201150503070b0f0403120302040f0605 67
    0x1071200080407035007075418a64903400700354003515004540d80c42071140d4011500ca120214002c0122000c184201700b400c0c007d60203014011391201c08008a050700600e044140380c28141031a03240760001c50100c40554108400c120921b129150034541c2135070a5000c2d0601600046520000e01410320085040c03c0751101c12091150340c4a001050039a00c40308070307581d140e42103d02c1c02c5584120140031081d90000e142011501c2c8514450007401d25003140c802540503100310b03600c05103014a031038a1218413038640701c814041039642d0342c9500c10301030803c115001c1600701d00601030344610307080c02000106100200002d004c21005000c1000003207000c942e00d040c42804031001d140a8040c04480300d0303076000741c0c50f0b0b5080000d102000554000d2400107031501312807003680203100c1b21044402c0001002454880c07250550b00c801d04c01d10081c7c0c0b0000242c40f1039040180310504041d601d8541e400342c80412103000020a6000a0a001039104054484003400060800c1458000040030005240d007003071152 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 785349298 1250 785348048 785348063
    0x3061a0414031f020d1d0319050f09010e03190c050a050d02060403020607030504330203070f11040906020d0518150402010c060902041b081b0f030703060e07230f07 72
    0x11701c40d440102c0e805205017081188000d01d41403880d9808940d079a2140c44620190102603d071080028072480894801301802d060903418017002d540156400710722600d01c6540350050005074071346140781c00344a80350380b80503451125140d49410280540c0348400e8000c0c1e4041c0c1c900c1d00c0030102580310307042107404890303060700c1c00d50391442c06040c100c80500070341d04070800d4000c508032181090601c0801c0b1a00c40702c03006411404010044000707980d01c0c455280000e00481e2140890b01c0441d50082c0904421040504041401c1c000b40d80c0740320072a8005a54400f1300c81c4e80e0428054003902c0c921405c11010040c100414100e181c404000b440d40d0030080000741040340360700d85c0e4001c100298000c01c49480d805882800030b00030b0380b84000d0b010088480c0d0b02e8005807001c00000c41c039001d40c20311144548095a4504d141c0b96507010841c81e035500040c41701041c56203030072001070440d44e40e0303042c944140c050740d441058101a42c034040742e5010300998a0020700e02d0a05c614240b1903450422160911361003680d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 785350548 1250 785349298 785349307
    0x2a09140619050102030304140a0210090501020105060d050c101107030c0e0a0531150f050c03150d06020903060415060b040b030145141b0a03061a0414031f02 69
    0x1042494414200c0e4000c0d00240041208c40c0f415070400d03c0433040d144240c0003801140c0c1c4050510442e1112140040e1155011000b00036241c1041040400041d54610300700d40d0591000702550300e00b044a070300c00c0b83c032035410300c01c104140f01c4000c54185e002078a0250034807030307400d0400d4000c0c00207441c0c00d520308505110005031800c880302c1244400485030300c00d41d10f0002c440200071040c0100a4908441036160a2000007034002c3c03010421644a01c03001900e00740000805000d004000c001c805044400903420402d041d12560200425480b4078460060808030100d2408a81c1c01c4c0e1340240d12910028105020a100207506041600c0c191821072200f0702c40d40502004120341010882c2802411110038001d40c0c0c08600341d03d10150010f505c605040c40a8a0300c400005079842e4200d44a070302007131710702c1c4060b10fa0748484030013400e0142c914a004940503469260034200d11041d03002c01c0149020024041048c030400d640d16079042103088003d80140b404039100b02009409081c03c518515a0005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 785351798 1250 785350548 785350583
    0x135061b09180919080a12090503070605340e031c0221120c0c0f0105090309091302130c0207170c1503042a09140619050102030304 58
    0x7500d030451002000e00b0001c0000382e0600080700b00540d0141000c0c000c0c031011a055120f00307682c203545941d1000a540c070706030805070102d60104a00104903d9281c035194500042101000070308100c500a06000400741000101542240c441c0113401072004c10926003910100184060b040e8045100d003892105810a0b40020782480c03041d69400154422851740440540d5001850031500d00c4080d1a800070b460020851030351a0050041d0400e00000f07260000b000e00c0c00900250180346100708c200c0b00498584204242501d404071100441648003003520011454030080180c0c101c111040c00f0100072207503801040c40618009840712003076403982d0314000c200f8420004503009195912000400304022100140c66109524050307106034424a030201740e400400c0c0c1142c0c0615840b46c0c02000509811114208040791740c0320500e698111071500042071801340c01000040d01c021a0b07800c80d1894602c0c10800071141c410300036400701c4c1c840502408640d800004072a040750300180c44210001804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 785353048 1250 785351798 785351851
    0x10f030b04480605070b0a02070804030506040f0c0b1903090c09231b1c090204020406050304060c02030c15090a14031c0902060702040c0e040203013506 67
    0x1c0e00000d04010b90350550240031808040d070752101240c5074025070415641c40003280c250143c00f101601d000c281201081d05848241d0040030014428410a42030607902d40318142820380840d0284c5a07071041840c4582002241441c4038007411211203200c0c00c2c0001c040d03100c04907401241c911010f041d0307640410300500003901003440090200120601008682404181c220b17041e030281300d84000400d50104664003050150840181001e150050400c110850820f1410118418080c1d07a00d907a010500c01584a50000380050911621065a2400c141c680722045549140c802703021500144019005207101203507a49541c80035600c0311f0240c1d281c2d205201d0901c0d04c1e0351401801180300903400e085c6040c000c800781c1016420194034100702c15001c1100c009039202d141c0000d51040c4200710b504014502a4002402501d6078600740d8400c01c00d21000c078040ba070080e0020214070201c4080640c2501e5080d40e01408100204681900100b0310000c4039511400900300d070072480385d041008140fa4649 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 785354298 1250 785353048 785353103
    0x50924010618242102070302010b040b01020d0534052103010501051b010203010e07020601060e1507080c0609031909050603060d030c06050a1409061e06030705121005010f030b04 78
    0x2480c0e4000040440013407a24001c2d44048822400340d402e010407254145018840c4044007070040c0c010340000d0340400340031107081e80711001148041703680100b10220034808448003a00031046c0d080020455103142030052500715000000707031155881100104480007a03005880c110b0700c00b800d01c191a200d601c2c000703580e42c3d10540c0071103040750300c0400001810105005614091a101d800350341a0340d89030402101c1d010350114400c6d0700541d014881050351aa650003c000880c0100001403c0001c3d01034a039052800c207680301c4003164030104801d00e060390001101119400c1d00c0c20540355580c5440c01195027800010321151060804610503800d040c021003240c2c9003079a12240400c000e00e40025210014008861141741d880f1004000034200100060b000b4041c00c000381500b091b43c1c0700d40d02d20f5654048010b00c9035805000e5640005915117840442c007145110b0300340900315005458030340c5e900b1110164003080e084010290700b00085914001c005400540114440f0b030000d400715601d1300303000360 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 785355548 1250 785354298 785354327
    0x20d2c0f130f02071110020a0b180a0309180c020a11011e080108070e0106020a061a031e011407090326040905070905190905092401061824 61
    0x103040100c101614580c2c000d0001354400e600b8524202002414400e030522404081700140e0301182a41c0d000c0352010740d546510006401c0c840c03440c1c00540c2c805504055480e0340403000304030054002d000744600c02c501c01403c244002c0c4104203264500c01e00070740d550b1410310060903500c90a008840f45034410034800e0307481840e445505030b40f01c2c02c6100080c0884024030034030045000721000480d00c07200c0c480c8558100c0e01940e0041c004849d1548528004000440c654541f580750303240306030101d80341800615881c2400f034500811300ea229168032401d403800d01102494030340c803220400c480503811502d0402900e4000141070b00300100068400c0ca05803900072104200e15000c40d00143d44159900039070f102d01020b640d07940d000d50355841030240d42418444003140d81030344500c1c10b00800c0860b0344225407241e48581124400102a01d00503046246110700340303600c405020040c0b10a6401070405082d0344041c245030000795142c80c00310302d00440750745a00302000b0800702c0c441d0100d920a5080605850 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 785356798 1250 785355548 785355551
    0x70305030a050a11010510210b0a09050c0a0b1603020705210c0102060f13020607060e030702100c0206040603020c0c04060f0915050a0311060712020d2c0f13 69
    0x200070340005031071604005588800a400d60712005241d42060240c240500703d03500780c500d165802c01c00d028034004e01910752074000301100310a04000c00c80b441c510310300850154000080041b841d09042d420007544040c5c40d030085281c00c0c0100a80300011044800381c41c80740c000f48001031080e01e001c0741014180d070320135648803980c1d441c0e002d01109403244110007100039108690580501d1401a600e9400448101c2206981000002c1c0d906000b0700d01c507080c90f0b100030031103072078451719942c0c2c4011a21404840e00d601d5001051400460510403d50f40c00701c406401d08403140c106660000302c06100d54000c507420990003203040300500108020721443c443c1c0050080c0081a00c9a201c0b01210b105c07441200425070070090410131500214000806aa002a00c1190000e0864441d2001503411040035900400100015004a1000000084a003050394090f180d05090300c00d000300b80071000da451590cc044600182003510300f8410b0b506811500946030300e40984040ea001502e1540d1031181041e010313 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 785358048 1250 785356798 785356807
    0x2070c090608060f16090506220e060f01021c030f090b090a0b070504030206180102031213020a1d04240603110405010605121504180302030d0c0e15070507030503 71
    0x110003084140c400e44d86401c030031013181e4440c911224503e658407000c101040d5140014440c0f41401f41c014642c604000c10721446403139280f101c0d94492051540300010007403200007407101a190150150340b480e00c00b4030050074a0045054641d03002c5c2d10380c10180c0d040c15034130800b69010b880c0340e8100d42815a0071000d40c10103441e01d01011622415005411a030001c480c400003142140600c080c0c3d415030760081c100d03a0602c108801101608000025454154402400780c1c0800c0f02000341d8041c4651503a801c00c1c0780d107180502c10b00c002034120303820164603a1104551941020103a0030f18507486a0400f400007000408108251040018a0040c81049040074030100c184014030300540405802a0707800c100c0c03681ea426003141c0b030b070061120b20303615240f148000c02c40d005540240c00c00e00c10740081000410610100b4043c245250b400cad011000340e08041040441d5503042d01c81c8003540203003030030603102004081000840c0c015141c0c00d200ca00000104441040c01010440c4901455004e03046a58a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 785359298 1250 785358048 785358059
    0x403050f01050601350705130e15240705031b06071403180f07050108011202010915020705030304030b070305281e0207030305100b0c06130201261905040b06010302070c0906 76
    0x10f030703024608030070400c1e00354030000883c0008503184600c61042b145c12b101440c0788034030401c441e11510300d0b42c00225028016074020310ac61498000c011540c4100e000350341da042c580c2002820031405440c03600d41500150104180d40e500601000b24016800b6442c5c0e913a0340d0352014820310303000d98004004251240c14007107110303558006a13840030349000340c030760800c1c60f0b07a5403000450309400200002d000810b580c0d02004011400c0100003070700c1b14540160f544032034440001ca46590000da006030340080c443ea041c0420f1a8042c8210b90f0030000348081003407107101010b00791b41004060740341307183c0d460355400c2c040a1010081031600d2513003035100e0b402d5580301414100100a004103076505400450890400900d05444404075010360711510023610441d036030480440c030440c40110090381841152880d8290500404031204c00c1002102c40e443c20324140350220a0500d026540104000c42c0f0f00f50601020410502c000d0740e00003002d180150b0b84542c40d2601400d070310740d541d0224820303a00b8520f000c240c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 785360548 1250 785359298 785359307
    0x60c030f050f0613050c0909130f0f0b0c0c07050616020405040804090c111011070503030720010209031b01030e03070804090c0512150301061503020403050f010506013507 75
    0x34880480b0040c00c0c114462444d803040b110166840000c0e03074000c01c0000080e080648140390302550f00400308254003a10f03200c20760322004d442000c4519a202501050401c950282038903000364036600880d042c0f0b0701c1540c01076131b1008917000c1c06104d8080840c9903004004030504c49454150302800601c41d0741454904800150000d02034903c0b81e50401040b130021718800e01c44a05a00d01c1e02d00240140880c2c0102080101101d9030002c10904c41001072a0200300c041000354000e00c00c984d50301016400ea4031040b00004064a4030718078990041141003210354001501c044450f46850003d13403c1401d19006074001c000c0195000214000489e442c1c05210044010f042141e160f0a0240840035050b04103d9a1388a244134031640400b0744004104401c1e110152a208120003900004400d0345805000c0c0320021030030b4102e40080e0b000078041c010014240803100c1c0c0410340100a0140e4200440041c01c01925442403040d059040482d00b14601c00380340d4000d90350741e04000c02071454100303044c0c000e0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 785361798 1250 785360548 785360551
    0xa0b040e0304080715050d020d09120210060503060705180f030f1b040b0a0303030207050a140a03020c060f030721180212060f011e030210091a09090103060c030f050f 73
    0xd42d8018074100003180390745c04415401012059952602d0040306030000f0009420540c900424240c0c0c0740785080002d41c5440c25210400c202d500100360b410002c2410605880103900700e00d0083c0c00a0041c0100550048195048020903142d4210120320b014042400c03000b41254942d4588110b401100070900041421a80da200b03106004442080c40c50a200c140c0e07901c2e21a854202081480c2040840c3c429809052124400c9042d9030009000f0b4a82c02207640200300c403085e00d608022144802c00d86c0401c0701c16200c11040e01d1842c10004030b120380140a0000a023400d00b0300406450f40c0d060302124000d034840c046442c9004000c002441e50310220703080400c08080340100740900c491040b14100040c10781c800c0c411920b507480103a00b4550001e284a00310054041002420000031005a0f2044e0b14408801c0c665030700d03846181e180c010560b0b00154076201c9100c0c034600c100200c0e21181c031240002d41c152030b01f11001042104240c0000c5004085402042294910b060309018039030000c042c465 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 785363048 1250 785361798 785361809
    0x21b0706090f0f140906030c040f02040906080f0a0f0203120f13050f030a03031104050a0e0f0f10060507020105040803031303032409110c06040510051612050a0b040e0304 75
    0x300d440c240c0301c103000c0c0100e032018044c2c04400321040300e52282a1400e6003003a50321800141c2a5004400c3c0400400e080c0c4041c0310b0103003210360300440d00b88001da1552050000501c400c20060400f03124940b8201d468045002c0050b0019143c00214003c7d91010802e03a111000e044180c80c1d605c4160080030815504108541c10004101e8400062245054084000301040080282895150341e543c113400034650585080e90241007480009203996801603180700030a6031a01400541c9003409443c0e0070084000c01a4400403141401e00500406589120341170b5100c80c00c1080c1e82d210f0900050f6443d00450740708201d00e00c4008200111042c3c640c80d11040c851090702d003806184511000000141200b500c0590400b018034000c0018000e0303608a0381e80700501103c0385142000c0c122031036080c61000c640503555940101c2498145160070f205183d0f0180f2420780c00c6c51000500c243c003c001001d8109910455915070000c03c8190216610014895400500c108030b000d40c19501552a6001407060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 785364298 1250 785363048 785363069
    0x13020f06031504150e0f07021f020408060c0f040b03062b050c0103050118051906150e0607080909090c04060f18020307080613111c20030604021b070609 67
    0x385613081d2020009109032060102146902c3d1741e000348900c0c11520003400d01c41184030700c0801c0b202e40c1f00e9100d21301c0e04112001c04090307951801d201c2924176040d8042c1061b95562020800f42007111401d40c142c0d0141c03040551080d9403070700c0b110700203070089140c0485c020951a00300c41101d6040c8070001d221600c240300e03000780d41146c0c21000c010750403103200f449508103c041840381e10081c041c0e50781c0550360001d20740102401545544003402c0841705e041d0842c2c0e0106c005605071102158001c242800c00c542e003120b00c103207844125602d0b03008070b01540c06060b0003080e41202140c0e03040b9090101000f8000c02410070402181e5480c0d1045000c8024420007100ac0d0087c176501c8002d035114000c60b0300c1941a41c5400040e41c661109000780c14002e0800340d00c10994030300c00c038150140e61200820b61040349010400c1e08028011300a012a0b4a210184030b060400140382c522180d18402601d6004800315001030b141c0c0800824401d0001c4841000091070160801c003048541e0040800001c2c0c0300b0390f002c1d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 785365548 1250 785364298 785364311
    0x90105060d0309060f140703050306032a0105030c0c10020406112a12010c08011401030207030905040e070f03050607080105150316051909050f030a0b13020f06031504 73
    0x61080c040703240200030700002c2c2001c00c14021180101c00100314001035107070644552007055000003081e0000b00f01100010380001c1440043e1408204088100e04001c00c1e02c0c8408031181d415a103240d22094006040c0304010000441c05104c60003076401c4410341c00d0580b01480c0c04400044000d60040c003810000c41c040c0c030a0580903c50005084030310380e0b101d1490141c1d51003d0300c0010220310210a07040e502030300094420701d240d00b00707005007103491686448102d415410090f400640042c11100301c1d04043c410310442c004a0f07442041401251401e99000880c40c520009480c01c007036894202c0c0281d2200c10b10b00004011000a81038030602302640d81902c3d50f40c8810400c428414410400d0070284410b102140071403003181d01c035000410150034818501941c00001d212103180600d10307480032a081c40401c00540c02c04c1d00c00040540d40c220003428400403107a48810366808090030ad00b640f80300031801e910440d201c1400c461070f901d400506403500c07480c00036a4001003c220380c170130034059402d121 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 785366798 1250 785365548 785365561
    0x70204230c1219020702060d0e1027080d020c0c0f06070213020c0705040c1e050c0d0c020a1d1008060c030609043816090536090105 58
    0x8150391040d60280b0061640e51680c00c400c0a003030b25440c40d688040c1ea803c00004005039640401410301c108840f20104100010549040c10208010305554686041010888482541104007010301881902402c2d2010050500d68010300070200c8510b0228030016426610070030016443c0030440701110f07140407040d150320134001e440c011044001c1d04015001590f004040e0300d0703000781c071814030400205d9024a684100203010f4888015415011500540c01000301c4a8550f00c0841c001d149401c06629082d8850074051340c842d40403984070704000c4a111040115590800c108004115015150600d008201001031340c8607001d503031014040303504190006480d5004100d15102d4400464650300b540d41c0c0e85c09110002c00002c0c4101e07507588104030040742d607031502403410b00382d03400350003426034982031901001000b090050002003451000030306401020b41d01000490039158241c1741400c121080610030b60f0b01101099982d491220050041e01004036500c1c400c900c2100c900e8003d01540d101d12 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 785368048 1250 785366798 785366821
    0x40e0604380409060609050f09251806080708120714011805011e0e0303011e090207030f030f0b0f10120e0d030605011403150607020423 60
    0x3050344081c015102100c48074498a90060280c28810a4001c04078000090450382d5069040b180241d903401c09000146c441d00c90030b07501183c1e41c00c0c507400a090042645035211240011012200940710000c0b04402e641d074010002851044c1040000300c47c4106010301618035030041d50203501c205100015407480018950302d03c19546960395250610343e4031141103007507441a041046d99210300c00040707100b10441202c8103503400303031000050952600d040e0b00b03e64100c82c0e042140c59800d28001800c0305001104903411185c5900e04074007400c0003001e081b00e1204107503000b00b200510100d1400203154015a81400d4801c103540c040002ca0140e00c111403c407842011038607044107124801c41802c0c01c0030f0030000c1e40d40c0c00310300b0102204020025440c05559120103201c0464210350280c40d603030781c0c0501132040580400d007008200c00100350443ca10a00000303001844002e0080d02041e51501c07244201d80308641c0280081c010a0300103100241e040c65020000740711217140000203051b01d14407 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 785369298 1250 785368048 785368061
    0x311091b040905060414070201090308160e04090201020a140d0314070804031d0d081806040b030f100e0a09050609010c0507020d0204020409060f080c040c20150a02040e0604 76
    0x4002615051a040400700401000300400340c50b0019034401040b08a81c5102d4691b922904042c0c0c0007280021043c90020140000640005644114441c600c0c503960b8108503410320502d41500c00103900940d40c00100e10307103003c201000d80003503506c0d01a8864481302043d80702d180400e6460601c030702c12500186c1c00c090202103400d00300042c00c2d00080b0703000900c101d0b1040303004074150f003400c494061010300143e401030009000f00d90100c0c001410011020166a0006844030222003a41c145843c1c04c15030071980c80000c0004000352000d000064585c14215030020141607600c042d076421f440d007810350a0080180800640b40c070b01c19080021041c007014024010039000d10790f2480e00340b0201d5424450f00000342d4504aa10940030322000c03403030040c00d200343d900404001c0d102d08902441c19500b07a06042d51651450301450400f400305164030f4011694070514886540c2d00e4a40e540b000352070303500303043c428010f41128100e03501c03c5c0104c0d0301d03064000e001510714100030300d1540e0311114100002c4a50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 785370548 1250 785369298 785369341
    0x302060c25050f16050f12060714040807181a033f070c0609050619030f09080408160e070315030c061e05120a050718031109 55
    0x103000703021840141000d00c0011038035100c1c00403034200d00c0d1500201c42c1054040001d1811070701044004005a1800641d50301c03800300c054a400704000c070b0103803010380c4a01c1c00808150900c840c0360070050390300007402c0450b002481e058059850700358a035500004842c8840c207440940b00d0405a00c107a004002e54086c1041d000024020408d1380b00d000c01c1c2e0a480343d108100c4213a01e207064180c3c51440100c014036820310b140c00c0c0c0c400d56507815480c80c01100340c00ca81d070403403001c2014a00052100c0c1c0c403080d08840e64025082e4041c10840c0d40c58504601828001e40380042450425980204000c440405401030325101429103000301001d001000701141c4901c903403c01230580708080b94125009900030509210030f245140c2242c1c0d00c90311000390601c032580c00440000c035002030780b80c17210303000e14050a0214540c0c5070092624880b18503100e64400003400001e120ba60f5030300407403a483e00031001307950b0509500c0c583d26011039807400d00000040c0707501140b41c051400180004c03c4220b980340305c1407202c0e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 785371798 1250 785370548 785370577
    0x506071413030303112101082a0409020a08031206042304020904020a12050601062307021201060f1415120a09020a090e0f010608030c0c04021c05010f030302060c 71
    0x10725580f411000f40429441002034040100054403078440a02c08402071000190354420b025490203407198a4030080d8806902c20101710401040c55218000030118008821a8041600380460000071003800c1103901046240c44006594500c0c01500c08100744100f2003141c080160070142812850003002080a881c170450110300041c0c01072809503407880d0014000341c403400ca0716840c0c00094080c2c802c9944251080c0d44035400402c00181d010310a41ea042408012800b520700c01d0500d4154103001e0000c00030321414004400707182461095024000801d41a01196260f03a40c03034400d180c450303170190300c201d004103400a1a550002600000c81b5030011505d1000400c81d503c241411000300041e28089038001402d660000f400c4a95008a21501c55003801030722a1070b041c58003950842e052540a000306800502034162060404503050054a0702581e025a4450b014242c00c104510941403000f19a85014001305031151040d040310280c82c803070703000c98001d511000c0b2640010300032040403500c030f00c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 785373048 1250 785371798 785371837
    0xa060f0203070b19050c0712020a0804050d0321090b24130905100b03010e120f09040f02130609061119030e210c090108070e0606120405060714 63
    0x43c0e01909040e8441802c0041e00d110301382080314542030368020780703000702141800705103c01808003400c43c00c4407404031070004003e90001c0b42d07034070711441c000d40c450b1034846c8481d50110010715009000319200a035218050b908040c01c0c0008c68801407403c0c44054a86c2040c0c6c10000e100802408942600000507500d5805110780c00c804000070007079504100d61354991140d206000082080182c222003041c0304001041c0c001e03810042c5401c48200b03941009043c3c1c00424a44000080e200483c0e1030a548901e020703031b484a094008c5006000c04070300b0500510710000b510326000705503421046c1540c0683c0d6810320a103603614000c88003100c0c0140d8000c401e40141106c00b104842135070703044004070f00c01d05281e803c5803103000002d103168540d076903a126842d004481030011030b14140985403522000b00c565100650503c0001584c410340e9010300c2c0301c10740310b05000c9001a641c80c82600d07140c4030000b070f2405691a1074942507407031b064203581d84000700d203614030b01c204260700640945c1c0c4030168018002c1442c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 785374298 1250 785373048 785373053
    0x204050609041e230603060403121802131b020a03120b0103090204050a05070206090111031819080c0d05040e070c140d0e030d030c090b0c01021306030b0a060f020307 73
    0x1480600c420018003004081c003001002c0d0940100b2024241c00200f135a21142e00f2040704000c90001021548640c101d1010130000a820908035841503c803664001864407500305e130304a6400120501039400038464440307456001464000030091442200c03461102c01d134081040c0e0313030f0b01031004d00200800c4a064030034165200f075a0015500d1401450046a94001600841c040300c405031891211162140c0410481a070100100368100821000070807288059001ea10001d00000c0d002d024200b00a1500c3e82c4903480c01c100c604182030403410b003541460034500c0c004106511240c2103180b14015806240b049502440603030b030880340307201d00c07028095540a0085a40d541c1e903840480300100f01541c002c84e03690b4200200f00140d80c40751641804000e40301d00309454200b0b18070380c0700201428150701c11075041c0e10002920407a007803042c015840e80362800c000c40c0680600400305894001c2d85200240d1240e01d41c0205040344400c0d1b54818199172240f10860343d03610407aa10b103025070f004101c0c0380700 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 785375548 1250 785374298 785374301
    0x41536021305151f02010c020c0d06020d1b050703090f121101020f01110c010f0e0a080307020a0503071119030506070c030e0901120b010905102309090303010f0801020405060904 78
    0x612001c1c04840405440f01140054000040005000c1c8072074100a040316030136809100384103900d051170008144882074000040e103080c05810004203602d40209440c14040800c0e086036049400c00d0107200200c540d8408000c0c056045408141e0010340744e010002210b000100e001401e4030700d02c3c00580c4001445403103501c00c405942c0c802d24110301c580040520094807e11501a258248c40421550340040e0003849094900744d40e15aa000791405550031a10100011402c03209a4041106903c1303541345642681400c0c030480c009000b0340400903e610412500718a0b00c0000d12048402002c4c44a087c0011a1901107a0000800e40d0b0b1200d8003145000d8090000c41422900c03e150604440900b200800d044001c01c0e40610000e040310070021080218a14000d4003604a4100800ca41d20f085062069440c80303510810b03800640150782034400c05020302c0c1d8885444005800343e03c060a003120010390300c0d4024847c00301143d00c12103000c24a1681802207074115a801084181880c000004100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 785376798 1250 785375548 785375551
    0x6050a14070f150f0b1e01080615040b0901200c040b0a0b190e010507210c0609030804050610051e0102070f0f03050c0901030302060f041536021305 65
    0x48008440c0381d907240c005041070100c040c200d080750034080f50ba03041044040c01071744c0b40359130114800d48401c3c80b00c40c0da01d5403544132501e0b0342c8402d1034429607640356840450301d940d10105030100032a60018011034240b01d000010324080e031007a40da1800c111100b1512061020b0004c43c040b16130b4101542c01c003042e1503c6c0d0042015058010304035101c043e940c80d07802d241c0f94130840703526800342801d42100e8030307030740e080214694030070401c3c02c01d036250038690703600c501c50001d1400b10100c00b0340e142843c1e442e40c80d22492400880b194040f0080191203040d0034040c00700d40c01201d0482c3c0501c1a00c000810455800c08030b0411140d000e049d078101c5010300e041e40001c01103841303e03150441c41100300004840240c041d0300350041942c0d003d074020203411414001d04000c1c01c0440755018940704401080003c1e4002039640d8020009124a0342603100d610701715041011b600c41c85c042060804800105948101071070041c848501030140d446c2d8a06503600e1500030300c1e02180179510003600c98071031301e0848054002d05d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 785378048 1250 785376798 785376803
    0x3230c04080313030c060e0a06030f0609090b04020f04200903030903010612030e030a0c0b070609120f0806040b010903030c06060302090c040603140c040501030b1f03140106050a1407 80
    0x40d0906888081040ca5a080404400601411900d00300184052400703c00c0103444585050016032882002151011000b031062608140e0f44d842564034003001c0368400c80162407410320501641d100740c01c00150013101076400343d2103a401a15330440b5480c05229810380f07800524940d8985140d02c60300c1600a400000c91113800d404100074040d07141d6428031030000600b10000c042141d00f2024100107003d00d12041f0454041e074414035020f4080354002c0c2100c000c641c03200b106240e88a11070310b01100507142091009282c62016000c408c0645d0308003004d006401640c0da0341c14030365500c4200300401d03200790501d000d0100d50f640b501800444d114040102c0440e019140201e03907160780e85d012800c10030048030301044200d4041401d100c0d090b818011034a1180d80001501a241000ea03001e04192003203200b8581403561300c040b0300140d6261503c2d11155090012080c0c00340c6260000040d014114440409014401180001c10310303c1c090400d65004135425030751407000e07922104583d0780036030144406 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 785379298 1250 785378048 785378071
    0x10c09050d020117090601150e18060303070c080c031006050a0e0c0408160e06100807082d0a110403051b151b06010f03210e1c020108070323 62
    0xb44808405604d99603070052400b20300412883d8580035912031042c1c20180c0710b600b04110005030004569980100c90004800d00781d11940648444e000640b452081300c00c003c010035594407000416203c04500c0a01141044d4161901c0c500b24a044100301c1c0c03003034004d07541d003c802c0300ad040c00802407849045170b0141e19075110340d203099100d41346240350020f5101d114100850a031420f0143e004030301c640b1500720000395071003d005040c3c103c000d04034500c010032034010003881c03a00042001c0e01c1c0d140b8003006c03020507541d9124010042e400005440c9001c8480f0349081d070a20741001001041c850880d02100d03004005041164840308210006040da42030f400c0d8400c2212068489040c202030043c03030b010300d43c0d00c22090b5003442c9504950810758141e01c10040300b810740d001000401c90350744080e06c078050441d240c102c0140800d60150746941c2180403142e007294500b021021507405a8400c0480345000740ca81803401d50340c0020880565103608185036144008207030610703d401d1680030468100300c07011304 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 785380548 1250 785379298 785379317
    0x12040b030c0a031d010b030d141605031605070305060105120d140d0f0b0a0801022d0d0608070801240303050d1b0302040f08060705160c0b0703031d010c09050d0201 72
    0xc0a540381340082d001d0f081e141d40d210b0040351140b9080122254040c400d0501c07c040605021441a850042000780d00d5030728500300d079990801c5024811221038040d41085001e4280107410b01d03035500d030308a02003115184220310001c40d1620b40400100f400c00c16950041c41e0305c5203040030131140e81d146100150440b080038000c1000b403503031600551400302590180011100b0741c7e98200144425a03030f01c5504182d104001c8020742d41000d40c18004440c00c0c0d820400782181681e07031709514621a1145244007146400f9001c0b43d145808110030702150000d10080c0004c3d0080c5810320a141a00b070141100c059070440f0800010380039038058000400740500010f02d4011801c0003010051045224000207030b40094140301120b07507810481c000e4141d00e0010300c0c051502076006007141c41506113a2540a1140c0c1681003004000403001006d0000d07580d82c144c840115182c0980a46140c0c1003444e4280e40c3c4503070f00c142c02c0b8014800c1c0d008008907662014078140c50003040c000040e6008400380d040040c14074 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 785381798 1250 785380548 785380571
    0x3110c04061410030606050306041802180601121505010807030f111c1103060108040213020708130e13062f1b030f0304020432040512040b030c0a03 65
    0x455500101a40601e41c580b10500e101081810100842c3c01c07400e05203042e00900202e40d11a094a034818816900003980d100040c80703035509840d1403180250b00000e89104140e88509800c0c00a0164100380c07208250340140111683c00d4034801c500c01741c41e190b14110100714940c454514550806040d00b0002040c0c044507103134a0035100c0f401002c01c20703141d0000c1c125104280e0711042d850081036080341045030107102c0b4884c0310a40f201404c150304000038a4042415583e0790a4030a03c88262894110b69a84c1c02d0716010081d600821410b0340b89451040c0c00140c04410303901818031910b9004010241034205550b604002d141121040642004061001074004214003107461140001034440da200c0c070307112003c24500c2c2d055030103018140e0402e11a0f0f03025218100180c82c0c10590440d80440e25481800722502001038051608004003004442820800440740e503041c00759006500b9605000f0a91138150700500c103e100d100a4000f08200103004089420013800100b4418035020a440c031911 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 785383048 1250 785381798 785381801
    0xb03162313140601090b0f16031e1205100e061e0d0809030115080330040308101401050904021b0a1a010e1603050709030b0108070e0f040f03110c04 65
    0x40040400d00d1060005203c038540e040f40e2060000c0041e01002450710340113406c041c49074002c1c90405050580007404840c2014003c1054074000300e21002031100780c4485141c0103100b0000380944452142c074010105103202009040c984c243c81a03104a103444c0c0d01c444042c48502c0040031424140c000c0f00120080c2507603184061010040d000308641a00c81c1440d10804d42151044031500400c0c041d0320034100a101f1000c01a90314803004100b034403c800e200c03000c0000c5504c8045d102c0490380001c034400c200815400c915a00d01848000c110519565141da18480c400c0039000d0885000c20402d001c104941d01d000d400511501c41e4214001c0c215086014150b860f003401100d0840315001c1000801004a14020701c0c0c50041882c7c062510031410507090716644130643b0142c8204140d25800001d03800e5010f000500f0081d5440380c0149076540c4e482085503110f00017406a180c5807168000414118442c0c0311000d8000d980054440140700090741c3d0039508001920451174560113413001c41c00349545c5a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 785384298 1250 785383048 785383061
    0x503060f151305040f0204030506040f050109080a031a01080601021e030408030403061b030b10050a050c060a0606180f09021b0a03031505030312071b050f010b03162313 74
    0x111802c4200c1c01c0070100f10030344040d906140e01c400d10500007080441c43c0014a00d410541190740d0030341c44420360030240c0c0035000001020b0040d54000940d4680107070b0540c4040c5104090840000c000b4104000450302d01c40701795442070060f031201c5a1190b41200001400d10150f21900c00c60746090f90329600c1ca4210f4001d0b60040e15296902c12640c0100c2d1180c00f10541c00700241c1c5410070050101c04009070783d0082c8030400303404200c0301140c01501540240c048840040080040b194146000a64000a4001030080c60300144030404851047c204040411040d1031f00740203044089400c0c014000000e420402414400c0c006c5582d0600c4c0700b0900f0300c80c407816075020b66804154181e9040c0709901514141e8403c5001e079000304605c800c01610701da18142c20040794500b4403003440c0b00c2420041c1c4e202007c407003d00a4001d00504100149056124101481003035041d160181805d1401c48a414501e00c83d00358202001e20031907211403026078060301c59890091064411f2004e061050703084805 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 785385548 1250 785384298 785384317
    0x10503070c1a06120d08070e0414040b2a03131106030106030e1618200c07170304050612100e010b030f010b09030c040b030319020303010e1302010503060f15 69
    0x141030050112034180141340030154010350000748100c04051500070008580100303520f0400480c8000707a030f0303ea9201e400400d21800c60440003242401c0c1400c028000e40c82c1920345000c1c56800c0c2c0050900704207800d405005200420081a0651ba00e0340d0204c42c4070103c1d403008503502c01103540500403070f0340e40c0c8020b503010f0240c0b80c3c0c00051003c1415401441c180210000c6182e1034900502045040480300e000501c0358038000c4003160410a240e21000245404080c200e000d003004140502480d1740040c49804403961080c40d50480c604202140e6144c2c07145014090700044100400592024908042d5401900d41c0301d21042499031140510009a02a0082c0f940300c0800030034400c0e50b00c0c6040c1280d015040e40c0314a18a4a00550000303565000051607117402940c8450078087e103580d091064848014240c0c460304680c4411080080d12540700f402100c01c8090590042615100000c86213116190f040e115185107444610030064800e5009034815803084920280a196102840160600d403c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 785386798 1250 785385548 785385593
    0x708190204092a09060e0402240406111e030304140f1b01023903010209271e0403030b2128150902030f240a09050705010503070c 57
    0x5030078080c1c1007910743c907a44035001e41d50505c041070140c6104120b005400643c11030742071040e402c9500c2c4522980c10f5140511505130408100025000d41002050341501ea5600a94014a0300d8087c4507030103030310161046040d64800c1c40054002202061604130342c052400c01c41750801862180c00c0e2a014012000c01c0814040784600440d55804210303d50384410552000084a41100c036407401d12090562060b220607415811107025450039411180b0b0140c02900e541c5803c0ca0343c4998804078115244280e03115041e00f0001884020303110764550100c0c8416600c2d02c5941c840707440807400740c0344500e02c3c640e0180c20148110400d024840300d08a81801c1e1102038045c2c00c1e46800e0080032040461401c82108001d41c04c9a80050790080c040701c0b0031080700c2c0000601180341d00100b0b18181500440c10350500c604050201d1a2a410094540861040700c522185640d101a11029241076240003812640480014001c96014101865010b192454107804503451521112160070103c0760314075405 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 785388048 1250 785386798 785386853
    0x70515090a060501231507020d0b09190f06020304060b0306040c08010515181e0103060906061a03060108070221040513090201051603090b040e0a0b03070819020409 72
    0x100b428002e10780100001200c1503080c13080304081451920001c00d92034803900440c48080d41c071007088801d840745550041c0109580341c0721441e10300700c041c10540e07140c8420710560491800ca00f110b0040c100446a02240d41c101c202d54980d1000d000e5000580708030b450586842c00d0700300e039032000c2001c14030075805014040942860328103400e00311800039100c950300000a00d4252003544810203002a60040380f20b80050560f262056041c581c3e03070000e801130310101e0b07400000090000c0c1d9080141b0303042c014602040255640c1e440c1c3c5d501000f00040440040f5401d00000c0c0750340d80101c40b420341c0700c0d0082c016202504800c102840c603800344201800044400410148018180612421102d51582c5000c228890346500083c1841c00390341701040d0303e44010f400c4e400800d40700d6841132000388001c1e071090f5117840c0c869000c900d880c0f204640407260b140c5040d0b405000c07840e00054010456101d9009080c180c1d1803144050b2403507850004c240e8202c0d88803070003a0300052030382a50014071038814169000e803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 785389298 1250 785388048 785388053
    0x9120109110a05060406050c0106091b0206070f08040213090210270e04080a0302040819060b0109051f050f130608010602010c1e0c0b0103110f09040b0c070515090a 72
    0x402054841e55400399801d15014030250b00c1e030000700c600b03a5069050140d200c007480c9096501400058001d2141541416584941c00180c00403040136840c0a4003983d80590f9105070403283c0003840031600e800030350403074040780c05410f0010031100a801c40003004aa0200d5a4000c9021308170300c5445000000e07030158001968550044111035406c10f40348407004110b1900348445205900988003070401000000d07d40c1ca42402a812035000f082078000740c8022101c41d42a5082c0ca48013080c00340c44490410080c00865846078400a00742c84c0d00420550744800e00702800744603400d00144010034040c0400c0915a03c0862602509400e2903541c1600c07503081c2007802c0286900010b0740040c041d0780c144002c4041c030030b803c008544034144201c050a020391242080c1203c0040710404040c3c101c4150800220138001341403800700c90450241c03140181100c1910a00c0091541101e024206804950110300000001f000a15446004030f007150744101404111a102407c1a241c10040c1d50140c00340341b08 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 785390548 1250 785389298 785389313
    0x30b040f0c2606090a1d0d050406110c010c260c0601050f100507060504020d0b090c2b260c03041806032001051b01051008070f0603090809120109 64
    0x3850242015400c2c00b0304000d0046404d440740039181800e026100c483c0d40c0081050200c02c0d2800b0140c4204035008150741c4800035160398020b00912000a02580b01d0b110405000078490020101c1a95054056852030f04d503403181c3c0e5060101041c031110803080300340540a00c08040c210b442c403104041e02003940342ca010400014801d02d10325005414482188107040d40000940c0d640c20b03005880450156030341e20004842d59903440f0010400d210310401c0c42203007500017a0ba40034105090741c2540014919000003524104c0c540d46158141801605000c000b0340508098401c80c034603142030019180044000c04041c0c0c11130301480000c4d600214007009030700010b55800554014140080062500b992034440c417140702e4044100040d180c2c1540403071280d20030300403101004d84a80f0340c0c8107039169904035103000e030030143c400c903061915803c004101403101190841c1150381d504a40111585031080c1507000d02140003041d220080184944086620f44503081c02e042c20b4118000a0b00074403600d000305 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 785391798 1250 785390548 785390597
    0x71d07020106030b0a2307030f1406060d0f1d0a1a0c0403110d080a020c130509031605011b0903021f0206060f0604030c15080718030201030b040f0c 65
    0x28116070400c02c0410206003104d540d690002d017039060101d82d240c0940502d5104800081c02c407011040d9142c200040c4c6549a804486001407074441440805901c42c0078509081c402d072605944848200b0880919603980e0707108204507c0032607804074040310800e480f80b0340d4810400e860b80850b0040180e10003000211259040b200e2840f1030411064140440d0b032980900132030000810b0a0740322034034400d00d9034031030b0207404555520026031955400d54200094466418480311801541a00110091640c0c2401000c0c440e10304240110305014014000c0400c540350004c0c280d80704d541c0c941c507010780c0640a201c031500007001a00d4260351a4a1441031040a1080744042c6010300c5200255499161340492142d4100000b02c0386a0200c4160340c002940307a03c1181d02c000d10b60100c28000140642c40d0751868882d07010135442c2e1078030960720000700359a43c0302d050003210050b81004505200540c040d91000d59201c001134000266281c1e4a00c0000c1110011280c21001c18107944100300c181c4c85044225 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 785393048 1250 785391798 785391811
    0x60a1d19031e0504031e0f08091c110123031f09150302010f03290102060702060f22121e030204030804120f17030a0516051218071d 58
    0x490321800001d400500c0380c0994040284051b058904621900c15058005a8250f402081040c0035444510704400658003c0b445d0301e0281061100c901c000007640141440500d412a02e081101e54601c001121410411003116141170000080c02007020310b4040a188a00d00c00950042d2041c1140800c2003c124103910148006040c02040340e0304000440041044941c20b08005c05080d0150100f5805414004a55111806100400b00e02009100301c4618080000e80a80d034894540b0a02281c887d0300c1184c24062070308100b8046000380400b40320400095421f0315070100294181c5ea61084100340c864415000038100380b000c0145050401c0c034010f00c18890342811840c292550340c86006901413480356441c1648100c2d0500f00b8091200e00c001150380d0b1003c540301540741942140c1e000794200351440d100440c500f200203200c03160504000101c0c1805503c1361414041e0520900041e41001030004c031514818001750b4111480c10041e60b000360000400e0722281850307002d140100b540300200381 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 785394298 1250 785393048 785393087
    0x807080408070b0c0a110a05030a0501052d071d0a0312110727020f041508100b0415110f1f0b0109030206130b07030302090906040905060a1d1903 64
    0x1140c42a1000178140d0700c281d80420b2226003031002100180141c00a036101035054000c51415004200040d486030b403042d06400b0302d0300b40c861086069000c03851a26070420380c480c00702c0307030114600f41d01449101006000420103030b0040595400440c0c0b08010b1035004a6056480c1e1100002050304040c18182580e0a440141106840c100323520007d0741c0304220103003420200009407410007038103804440300c42280e220341035655661030000c0454a82a411903400140d80e07400840e40c509107000700324089510b180c4400d03043c2402d1010700742410b50300601040034041d842002466242040c40451100144d84004d09480c0407050f04160106c80a03100290700e076490f18611901c10f03070b0086110426070750151100c644660714440400300d6008180c0200c00c10110210346013081540c5500181a01e20081c0c4069180d500c40e20144020346000d001c0051a6801420014440c007070aa07006180d0001c06410008422a0081c03100c4d003040740c130b03008446604a40d00210b109040d084072601d0001c0c110b5048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 785395548 1250 785394298 785394307
    0x6010c0503030a11041a09130b090105101709030307020d110703122007032003100209150c0d080105190b0f2802100c0909050c070807080408070b 64
    0x1121500c0748801040d03031801c1581c4600181301d20f8200e0055070040c000c940080000c004903001d480340c590300041c7d24144107a800031116601d0030303158040c407092000e028010900c9642001c003001031000c0f0341d802c50010407109511001103500448a1140620181c0c1d0185541c1d0810110003410b0080b864240c3d41802100b04003418900360018482080300e1b04000307864402180080304a480160503022101d040024500c0b6a158003c041000011688590b4892026450007902c41a00c03110030181c0c40da064001c0380c9020200107854004041428004040079411600c0e0500444a5000400300c00c2540d4424034408035a16084100e09002d08401c491145221080000c00c4406460902071840d0b18000880c0e1004541d61540517184002c02d04520030b58942200d00400c0d80307410501e04840c0040c890340c03500008004d240e20902c0a00e004540d030b0350780200c1c100f80d1110050403000c0c0c0301c1e040342c182c100300d51000b080280700038109951045450964a624000c860b40c50103002d070300130306003942d400c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 785396798 1250 785395548 785395553
    0x120e0303010308030a0212160801060305090d0c1704090f14012405040e0106110d051303110d020306010b18030303070e040507031103010929031f09080f0301030b06010c 74
    0x1080d641140e500c101da550752075840c5a4034002a001d0040d8100c1b0307841a90003440340e0850a010b498601507001da07950f400e127a030b80d5403044040e654150781c00905e6400c070688040344a0b04c48c44100c4d6020380600080030031840c4001c0d080500e070703100e544030080c215030320403814495807030034014140090001240e00840d541444050003d030103a561340c0309071140310301044001650081d401d40d030082000c025000020740e902c800180410800c2034413491a405030717a0803072a809000b4419500d008203290b0030000312600719910b80006403100c82c000d40d8005444220300006940030410b550103400e80d02c4071503844082d071a0715402e0f488803490030035110b0b1300b09100700081607620124400074000210342c049060740b68118150001c0c900e0304000b02d0000000400880c900d121a00881c068000c50003295210381c030196108010030320301030210341c0d160304107526001d042400c40100c0810709115030700010303a484180d5610761036079010782d02e80c80f800e8001000400034000e4600d4a6944180c0a080018504180d079 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 785398048 1250 785396798 785396803
    0x7140901120203030f0a0e031e0d0f141e030c0703020f030913020d0b2d04060308030414070f080c011101020310053c090c0712120207060207030e01120e 67
    0x5c618183e2010710200b66034240314461040c03c2039409000c0c0a442c0b1901006100c511407264402c03c81040303109486200c0f241520a160f0441039102c0d554441031a00d038200c1482500354042542c4a031040ca1480b203480c09070755608015402303101c2200803544d69500278039000c0c1c103108080202204a8009214024030303500e40c1091302c000c19124190050351401102021f84c020415080c1c0d86030418031048100040c101c89903050300c00480411143d0000540311000c000a480541c04010a00042032000c1400941028408040c1c1444081951303091511000c0340140c143c1076601c0711401e60300c91904e800b080d5802000129201b901e180082d0f15600c0c0030154080745500034417507207020304245100e4010f4208000c020007818008000f6440c0321565a40200b118a844040503c1c41499140d002c10038045903102122515684503e0310545440c52a009440711099202c68101061302000f010f000034400348003e11318103109494981e000c074100c200040c440c51090044007076607860b1081e03440440b10300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 785399298 1250 785398048 785398057
    0x15081203090309010c0f080307080f06060f0d0209030712080405090123120c0325060e2211030a09050d2102030c0405150d140f0123030714090112020303 67
    0x2805c05092008107464424003080070400b0150030303e1404070520451036801406a8010300700b0040032441d540f15803040141030700c1141075070440b111080046070024109c5401902c1022001025108180c0c0e4612081e0b040c141c03c071804654102c000982401145003070358105015248494000806001118480da005034400c07104911528080341c100c40c0f5807104101d580741001d40035080d0744121100c1441810b00c4412000c0c0c040400e2540040841d41500c42d4400e0110b440c0001d00d4041c01c0c1c0c440c0748004030140040001265625140c00b070703035480c42c2c124000550040940c6080080c0001c00d030f050090a04941c01e075404100008440c1d80c02c6683c1800c02c10450309556048010f90f21780f20004101034070700c501e0380400c0e0090405645441600c9000c8050440c0000c3c8840074419640000c8401f60100301c2241c0f071141512030200180b2481c0c96558030711044021102014051550020002e0b2805140c0c4e846402d5000408180141d48e042890380a40104482c41059820240d20350000c1d0f128040e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 785400548 1250 785399298 785399317
    0x1f0305150f2701150611100b0d02060d0603080f210c040612060509090102070b1003030c0611160c06031107121818050709210222150812030903 63
    0x5070000c658081940a5002c000100c1d81300c48031900c0f03103a903050050f2603c022101d0312a900c1c01440c0080d490940c0901802451031401041142e600c5080d0307003001042c0d0804007420000c40c0d9035590104c0003c911b40000c0884000c04d1124544030403441014a00300c080e000420002c0080c054244541003101c2403d4030f0554400b07060001c410b02a10080500510140d030000d9803114119052001005040d401419424050040499140c0c0d4074003070018600e00c18030000300007070040c40c2e03008003080c455802002d0510003030681c05c3c600b040e10000c0410401110b04103448455545400300817140d0184030b06441080d00518142c244081c4d51112400503941c50000c0080c803c0447d0320b00b00000400301c03214090040307041c00b1001001000002001000c00320b6005010400340d007008288000d90031445044840c079041d04031716411180d402d10500f40031030504030760b40034001d42410a17421480d00501e003440009280c400d00003460266482d1501c0000c1401510f40402041170080042c0c1c003100b19005e802 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 785401798 1250 785400548 785400601
    0x2031b1f050c2503030606021b041104080d110d0e01050d05220303020a0206071b0f052a0901050405060913150608030d0605060f090103051f0305150f 66
    0x107032400149841403180d000c507540ca0400078403c1c2c00030121000c02c103081c1d2034001d070f400304100c50b2603038801d0b42c0e1400070f01081400042c4040c100c0d00b17180b600e5004807c4050120078407031308050703075040c031140b92441070315411340072820f506480d2600e4002000110100e800e2841d2640c4200c00c41e0700042e000c0e00c0307032020181e00d2580b070354001341c201080c04020000120b07400071b1540c404031550400030025000100c0b01001401200c0c0819900c500c00d90a603010078501c1c964040441046548128180014650840d454000c0000c81d0341942c0b00d01340b00900196a40c207801244030500d80400c41c005a05800030384c4940d203040b0900c802da840e0600300170ba00100c0e4180d034001d45032042c01d26135410781529039038400d601c2c140f04003c981d207800071002e4002c0074410103003800440c0e10742d4100103850003030010380c2c0d00c400030034400c00406601c20741080341c00001d000d01800c0034039000e0303034622540c10060308161441c1d4401e011000128010521107584241e500d41030032401d05001702c80c48070a41c082c5c21545202c5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 785403048 1250 785401798 785401801
    0x6031e35030c07050a080703020d030b1305040c05030715030b03010614100c021e041a06031519090903080c09030307020114161110210203040c09090302031b1f05 71
    0x1490b081040b83c10180d004800c6a07000915403a02401e1a030050400700d0040c01614002500580030340110700340310000400c40e01c0c4050742c0321948002040700400c182c2d05c90440403000203c40d00e05104d0301d0b0103400345c2810450342d251480406000c4d10741032800c40b0b020740c1c5000420450034101c100c03420a8843d0407a0a041c4010300c01030122514650090040d610010103103c03465411004000c030340d86180227807005d01400100310a00c6e440d80070100142d0340c00031000c00001700103c1800304403503000f100041c035290702216108008119200240c20608807036035a0100306c2c081c190880c850503401141e54030f10310f20780703030004020a031240101c0384000d0500c05501080b00d08240036034191803510324000b08031090600ca038281080001d40c00100640100c8440c0740c0004030602c0b4061000d01082d45c901d000412440c4007804000030340c00107005545041c200300002c50b10012034010800054001d41c000c50b150403140c180032a01c541902c1091480d0f81c41101d00c10110b400740034807040f4180000c28002003d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 785404298 1250 785403048 785403061
    0x2041e0c021b101205010b030a11070b0f1b040f21030507110616230a050604020d03090b0c011a0f100e0f04020a260f041506031e3503 59
    0x10b40b801d0341d040c013024a0501001007804802030018501c9450010000e101c2c2c800e942842400342c0c0718000018000e0f907907000c00030303d02e1011649015000300343c09550351001441240080f41c55002074008843c06048000104054168110200c000c010030400d840404a280e980250040c460b4000044c459550503280415541d202020f0740c1c08520744d507007502804090781c5022900318642c015401c00501182e00c041845500020756010090743c824020000c6403240d808118209003c0c00707084080061050340440c0c8a403000d009002d04646003000070500c14102c84070909940010502103000d00c001e0302111103c1d68601c014a4a030f1092420000407881003030011802000e100302c41c0e00d412500000d141c0b140b031680b0218062102c0e000c2c40925980d00e400200350420079906541c901108500400840e000c03c00103a403c1c9140c8420301c20000703515680c2e0b5521140008600069004170651000d2801442410b040c00c200d03e030030442d04004056580c0042440a10041d0b4074003109450120010310b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 785405548 1250 785404298 785404307
    0x60a05010e2d0d0302010c020d0201111b0c0d0c0f080604080a0e040e0718140103050d14090405151207080d0f11070305031c1e0c030902041e0c021b10 66
    0x5000300140110000b400a8100071780606142030405c00148509c08146c0740f001c0c418445d56461614002035189400b803055180302040d26207112640302400b802500300d010303542d101c410442c4a0312420081c0102441c00005840d0301c0e465502c9040190480010000044d114104880e665960b40c28961034804164010500401400d02c800819229070303500130030b407191030190700003041c4100b490030b00c0041c0102d159400c010768280b200615590144080b10794950040c03406020010304802010305001441c0c0c00581030f18025101010b400c07014840c40600c0f424013480c1350700400c1492000301121440c2440c42d0766075004034000b4004008100c0040d28581d0b104070950159013840c14101c51a80303460f41841504c82c0d1200740d030f40d40900201054019203001d0b9000d03c440740d43d650703482c2c0c602108801c40420f0280c0007460b400001c140d501e990100050780c0c0c0784036480106090309400c1000d40d00054000c01141c0c0c0e523140340c40955105119045110880e03915501508006861401c01c00c00209801d40c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 785406798 1250 785405548 785405629
    0xc071a10082103191803270315180c0902030402011409012307021504060908070b160c051906080619030213021308060702160b0a20010f05060a05010e 66
    0x84102c1400302c08905065112a42c284031403071300124485501f1130a6a1180c207900300e03100051210710000360100c0400c009a220462160f1070040c420351400b1159148551407003190070006080e54003000b44415564071842c02c00d1210780040740b551070300f04503e0028105410b51400a82d448801c5041070711035500138019500120b1340684030078400079492501ea40c4540103405600002411641c3c00076118000150070f004540c2000310091601015a81000b143c416801080c0ca0800f002200003c035501d41d1901c484901c0f95026a00c0211428480010a1a00064100791241d8504403803030520480703610600d0202d95048500c032030080e50301d84009002e400765101092031690200310020300c079a408515188a07288130b07401e807001d81040c8601280300c1400c901408040c0401402010040303405600140c591b607600c00300209920019400c00c17800d5840440c00010010707120700600066003000b00b440005000d00342886003002c14100c0101e03000001c1003082804451201401c0c1c43c440303290003050f8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 785408048 1250 785406798 785406821
    0x10111207030608030a0c02090f070c08030907170633010318061401060e0a03080d0e160602070f05040506010e06070c260d0e01080c071a1008210319 65
    0x241e480d1188035170082d1080e00316403020313809820540c00182c5005034407161a0b205134030b15100c507500d80d41d290301c458030290001000800c05128852010071445108807400d135611491030000e0800e0b1510500a0500181503011000c100b5400c9940c41207980c44080880e4440a013031a0001d14003000e00c0004455520526000c0e1109241660102c221100c1d00c0550b8140d450507101e1809a071140740070300015490510000d061644180001d0328112415000090071020000444900058140c260f00508003141d011501617480f461041094503d1a4034820007050212020000e5181c0440040c0086003500c10040c840c0500240e40b104021500c0032040152840c0e404c805041c130001c820070032204401c655134111600c50002d010b00c4803441030607080026138040e521000b103030315001d44017001a00620fa0440e12030003543c4101410300c00e180301072481503800704008000b035441c1c000502c6c1440e284003100110401d0380781e16410b4040802c81100e401001c02a2101101401c1c4044080140b2030030500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 785409298 1250 785408048 785408053
    0xf03040803010509070c08041a0702030d0e030c01030b100804080c0d0206040b0a0b0d080f04081504060e06010b120a0f0c020d030b0f150a0311030103050f10111207030608 75
    0x502003030180c5440518161101a81c0210703031600d0707a000a40f614052a640184104420003050002034500458009041414a017003403d1108030350000e0302b004a010b08000000707049491800c1c561a040051056448080c202005000c170741201041c1d03a00b010350f0350340e03051201000c041000c100074170741283d41c1c0a00000555000d44030340304009495080903141590b140112001244807018140706403112480010101106402c2e03642c2e40400daa0820598a038080c1402d000000d00c5400034070821044c0c502840070041140f91a1900d0390498034803260381e00d0701d94003140c014070445040d0740444911000b500b070f81428661390241c4220280140c0504411103030b041c034019002250b00014a032602c04003a40b0300b4409028404184038062501601281c0c3c00200308540742d040b030014030020520580715250204840f80400c202e000c85520030303802120540e112034444540c1d16814001c03400003000c0300034184120b6028800c98289802564036090f800700d242c5000c20000e80c02075201c180100164010b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 785410548 1250 785409298 785409301
    0xc050d090905070302042301120e06100801020717070213091124041a090301050408220e2d13060b03012a171603181113020f03 56
    0x200504421080c810306000509240104000303901a00949050718004003000318900004503881c05501800b00f0b945041c0800514640c80384005801101d00d00c042c1c00004040d00e09000c10040b900030a60381c410592640306002182c00903a80c50540b81183c2442c450458544400e80000340b03001c14461081d101c41b030324080c85c042c20070488980c0301c1001a011a0100e00c1180c080c1100d4211074808a00c01912400c200300070b200340c0d2244540d9071007101c0c02000031801c003000c20010a00b107400590b030603204248007180d14400c9000c401c804e0401004a002042c801a00d407101e40e4214280c094911407120048400c003e440c040b20141c413440d5401d8032028844075091061025900134a80c00c0180d9003641403c162503180c1c1414010341441340d020940380c40d40e507502514408141d101014064040015a014080701c5c048560446801128540303090311150788500720180883e82100b070800c1d507618210010b60041442101c4441c400001600c000c2070554072120210000d201d000c0c94079504500120 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 785411798 1250 785410548 785410573
    0x807081c0207270f0507020c03010b06030a02070303090f23030703020703030f261501050f0301050d150f0b040506040903200f0303010b07050628020a0c02060c250303021203070c05 79
    0xc000c42c6c000d00c15a000e5034440c00d82c84090501341d07a68440801d070001c1c02000407801e446e0095000384900ea0003481c1c005200c0003c0d644e941001c520406007610300201410401000c55010f0354210010000030004510349401554040d4031580c041c4005024041003286510b50907011f040e0880380c1d0000440040400c420040c600c0240c0c0741f054403420b840c00242c40081c642c650042088500e00c0400c0320000c1e04617840c041c1000f1684804410449086540c070044200303101da02e005601400c0c02410021030740b094402e050100307c8400401031403142e0f04084294022a0b040031080841e45800341c411611101c0341c60324180f505441c0c40c070354080b0784000000060f4001404001c0c1000600c00c40645405407540702600c414403084c00301c0c080c07c521040c1801102e2200980c0140035505841c10070391301102040e00054030303681000707841c0c0c51250810700c150900b8030540440c0040c01c162511220250a003103450080d0f0b121300d9548260100b6000101144041d070003038101c6a440c13684070b001c5450001100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 785413048 1250 785411798 785411801
    0xa06051c1d0303100608330d080c06010e0a050f07030f0209100e0306090105010803030c070606050a14040b0405090c09060414010b0c0705030109030e22060807081c0207270f 76
    0x248503200c0081e8100c4081402c2101c01168040c80c614240080d43c400302c0c602c00c180f003100c284945010723482100030f548280080c4065000d84456400c04000e005039601d890008820814006d2a0340f40141c9800c00b04207140080c8824183c10088030b00d00003418012a000080092040180c015030000c00602e1701c403043daa000002c1c05190400781c05407a459143d00348494241d42082c042d040c40380c0c206000107181464000d0260922034040c10020400380c0daa1008554a006150820b1110548000001505040034029501003040c00c4c0c07001c01107803900504007034851415051043c071400c40d210110366582d40c2ca402a410f410a02c07140300801d541d46000722051a8801ca1200696008081001440303143c10321408080070341549942e1250140c003410400215035060000c031691a1000c0a40035100c95446417030050300c0304100408a0f80d0801072182d01e013200b002080c242c10a01110000300041c0c0c00300d6035070215002c007040b500b0380c500e040f944100f0b000c100700340006a15282c0b03030382d80588000a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 785414298 1250 785413048 785413081
    0x507081321051204060c02100918020c1e120d060b030703091b05060706050a0f0906060f050f1c05190503091219031d060c0c0a06051c1d0303 62
    0x1a40484402480107141c40740140114805d48001c0f54a110030f100150804240a0303100700b28a14282c1c44140d181d038143c003800c03540814100d89040d40030981032460401000f4440380411884603840781184501d51061341ca036600c44860945410201d403640e21086030383c01c08005050f45606803900c0703140c01031000b0b000b40211501070710403d54040e44441080c512004e141c6c2640c0c005484107150070803a4482c1e001804000c1c1c0100900ca5030f515040001060a106420b400c0b8880c0340b011807000e1a0150046100306550842880b8050400d07105100340d54070400401e00c1c0301c001940101c1c1004604101d4107081040041c0c248030390103041410300300040400200f65401c0b080f286061174800c07131034034179036501c041c0f111500c0103000c040c000c08003090150b01040d00090b00e10480d0b00c86c0c02c14600200701260403031074611400b58040e01c4c901e0018502580c105002d4547d524281e410020b2041004008004036940c00c0c94a03036a80c10700614120010390101410301841007101d40c0c0f8280401542d511006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 785415548 1250 785414298 785414303
    0x130c050111071d1b1c05151809010e03120406150b0f030901060b070f0209040c121a0a110d050c04090212060102060c09010e040b122506030c0507081321 67
    0x402d000c0301d2900c01c02c04c0251009409071507010340200c070001da40d66004000203003500c0c0d00501c410b00c1000c0c45a861041556003540c48800a04180c10940003550035592038500540c60ba81041c4088102c5e00745030401a50301a030410804511000032140111802d04c0b50b800102d1046130000f001c440e0703948800300660291810700000c0007440e54030449101e240c003d01c00000c2c40c5508190a06d8090303d030070402c15400c640a0180e1135134060b40c408000070020700c03110007143d01000c1180200d01308140100c40da507020004a80520603003564681908052049000400200daa07400100c3c04040100c0d0503100940152074086694250140940d1071000e8200e850314018840c4a00081c20000b001d0240c1d51501d4068451002d284a21030400002c7c0401c60603281c0c03c80001203542c001881704000008560303c008004625108050312410300f100c1c50368004030306050400700b1030500160b0010464401c2a008440a0b854080040d0031400008042d40710001401c0011a005e84211452031001140c62 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 785416798 1250 785415548 785415571
    0x8070503130317030c030403050d2d0e06160c15020d1a04110313150f140702030a020a080a0c050f0609010b010c0510021b060717130c050111071d 64
    0x10100f0001c0200348001c64420b4041e030004c1c40850700081c0950701a0540c0d00704684081001884112548888803c0300d001100c00c1000045913240c0ba103c0d4400c404a800c8164081c4c41d46140c940c500440d40c1ca090080b0380d00300b00b004450001840f1016035045410704824070159554031000340410060301c101c84080402d02410810568145458450400040c0c02c1e09150350941d0b0302c400d0704002851842030150b4a5001944410181d0300c81c51180c42c1e00c800c04d14000045415444104600d21200182480159070080004600ca143c00040707800d6050780c02500bc642d00c4246080071240c15105140040040c8218441c10410308030102d0000e00c9400044000c1100804160044540d41503426010781290404851608107a549800034039180c0074651001d0341903452200443d00d050310484a000016851b044405221881c42c0d4440fa00055031020380704100f5840d44400104640c54401e85050112070301c1c00305810b0f01b09100d0703000101000c4020701c00a28107840c03c0300700e03203004440710385155 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 785418048 1250 785416798 785416823
    0x106030f0b011d06061e1b1507021911120618010c0e09040f15020909070c03050306042012100602070303081f0b03072f0a020d080705031303 62
    0x100768a004000300f00074182d031448042d445003428404c4a41c4515042c1e0701d000003e900e03041c60300e01da010060035605211015001e0544607840d289041030200400581c0c240004410320600f1540000c0410300d101401303003003954500d03051070017050a0030481040b9070480300e14403801d58454004500e803071103508920394181302c00701e290b00c00c54203c0f0010204600450100c102c12441801c1481200e40e21500c42d41401d05581c44545410b601000381403844921203800140e40310003818100134803900040c0300e041c04908050507540c060700501008250b14001c959600510180210202c0e01102c4011103241b0715985840328030100074010001c07030b10b5583c1c0b000410301c009a4184002503074021039070581d60307a55694403001c0240b02c01030022103094107601c0c15228003103180580500258064009600c03001000509200007043e811042e045042c40b8004031510401c1070800410710705482c41d411078070b0344410010342c0f4244403640174a160143c031603c0081402110300d403003000450250b034001c40341da241c01c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 785419298 1250 785418048 785418059
    0x804060f02190509040b190b0d06050303070503130f030c05121c1112030717190204170105071106070e030a0b011d09061e09100507020102041806030b071107080106030f0b01 76
    0x690807018010500700360800d000c00004403080d020f022740090342c4402041056a4034006031542c0c120300000d5038250000503601515a03155403c110007040003aa14404c1280303141c0f00c3e6101c84a070b03881601e024001607450ba25949200b80883c8040948805444034410a9801c00070804403102c4080030051282050790f440d200c690505a9115100565407030482206040c882412444041d2070650b181a607040a14220016800904040c1c40c40041c01c50002300c0b400355090949401a04207800d00507400111003d4150105045500c440d150810391100109040441e1421029a4001d0000c0b00403000100703145665000c11181030ba08480220116280e030500c00340c07200400d031000c1003010740c4020480030560648458641c801304240c10703180306861412a0800752001252500b0060358002024492040c00c090501540040340c00100716442c15581d4200070103c01400c0ba40901c00c2a01d208a0441d500300128405004104001e0101235640e282851010981400444000301c860001040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 785420548 1250 785419298 785419309
    0x5040609060e04020d021203040b071e021e06090a0e0403080106021209010f0936060f0e0c070c03050703050d0e030619060b04060909110a0804060f02190509040b 71
    0x1580c044070303002c40b12520380c0d908100e903003454604101d0b000040807844030042c0b9028000350004100c000200c1d5030f600f03110f29101c4120308500d40c4a0081000b6003000c2c00241c0c54000401e20032000b00e411881d0202029000100c25000d103004165002d40b503610007040d010380e0070390b650740600e120752030321101c0e0390300c451003a40c5074284c8000c15168000305120082d0b4a44c407841503000e0180b13040c00c4c403503422512562410443c0da001040032148036000e1a035420018801d00001c041604403420070000a42000d801848641603403164450704840c0901088003800785104a23a0380c603038081c078060304e100e039030386405030b19940644005e9a043c09001d0001e607005000d04058401030a00502030400c0c0d558034622030700c130800c2e00e40e4002100c0380e58503000b2800c800381c0c80007031010b071145440b8848403030f2801c00e100064402c0446500041d800a204c03c44489401440580c0c100d070f0b101c200840e50180100d442c000034001c140e8040000503c1e80c012f0717183c0c65000b0000708221001540d040c03003601e001005002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 785421798 1250 785420548 785420561
    0x106090c0c0f170d05040614100b1b010b030106030b09010f1404140c030601081608160b18041802040531031211040510090501120207080c0a030905040609 68
    0x600320780403608040c001801d2100070754a50000d40c220a804d044d074500c90031040781c0013164200c4000340e03280003852107441c001141d55405108943c43c980440c4c20039800303400e18050043e01c11030503c52840d0760348000000b900503200c2d000d4050000c1140681d2401c100720111010383d00740c0c00325403800003803113940f8010780074841c88543c1d0180303e0b031415203c4d541c0e980626014580700c044c0f01d00507241e0743c2030299010b1003558005d040040080c443d840da4000401e950182c40e03442948180d02c214210b41841c40800e2581c000c54cd9424440b9440f080c0300780e501c9011001004135242d0180c9401070912000141e00c042140713480c025242040b05a54164816031100d940b603032408182c011f51451803c0a440e0360814a410314401d1074101c2c100c00c0b041442406a40e500c14480c15886400716042c4038034100742040072180000d516003e5001d525060000c2c00f13a07940800122111074001940344140540c00003242d2403030320700000300e030750448407410700a0500d2034501859205900306000007c81400c28043c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 785423048 1250 785421798 785421803
    0x3120c090e13061a0a050d1e0816051c020c0102070e06150d05040b16140703050418050a0e03070506063a12110606040f06090204080106090c0c 63
    0x5020345003070003540107031210001c1c034040100c01c040004000080c0d030f42c000c0d11140000c001800d024203880e1420080c112030540c00060150306a80e900c0000704014110b0741007806e42050500d41606241c2c100740311175100d031000c1c03480c07200c2001c203492040040016860070741201c212940c000008610208030b0b00c1d000304064250041c1d220602c1445000651240150001801000a41c581642c000c900e03000e60444208028a59950b50802c8240540b103002284d1001c90091030715103101d904a0301920210092a40000780c00000c50203a080502810444010b000311210030400c1e010000c007403038090301c001c650f21100182020010304894900000352582c0b240d0100c05003005075155414070105484180789501c00c24114070460900e010030500e0141021110b10815a05207510b0618100f682030014075501001422a10384404050120f01d4980025007210042a81c841050098010380501c1d0021120f9034800200060000c905500103c01c441000da400e00401c0910b41040e04d48038050b0002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 785424298 1250 785423048 785423057
    0xf0312072010030c0302040911030603011404120f0203121302100503090c01112401170303040b040b060f040c05070b010b030c0405010f020102190903051e030f0702030705100c03120c 80
    0x10190502a8112441320b0000d490f00500b4580da480e54281544d44c58800c40c000302d9800800d0000c3c030304080c0980c84541d03e04a040c0c0e00341c1d0a2035a66081c0242c200f4000c0c10030001d0224605140620034821900001d698800a03d41e6082c103054405012002001c00c170311030184921201d0140e03005805407480b81080704064500c2100300c90055500c4805500041141e019403584840c00c1210b081120111510981c0f0010266040a41004001c4811020240c1c154002d008101c0054081680645e00503408005075417a85c440da0080749084914242c803c0d03000f802c0012840c5141d6000c809042c40e50b0140ca0a41116685d910f84180d0078802561000c030450f03400c110611455001e0740c0c17881d400d41d9161000601d480300c080e84209400c0285140c600018240040800074004c08000500000040d051084410000c0c1420f9543e40c2c85241e2030016a024082210b50556805010f2080103010203080029032890080000340a101d9441781240460848414000700c0000d03403003118070345011303a01d8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 785425548 1250 785424298 785424319
    0x50c09190c0c0c090b030a0204050405010506190f060e0d0c0824040f03080405030c0718060e061008060f04021908240108041718030601050301090b0f060f03120720 72
    0x41503000780c1750480209415201c0d40481c10016222803290360b128030b02410001605003061020048400c0000c810003c2d4150803c070280301d00b2201042c414203c40701410900d240b010030310041072900d01d0154002d070010382b0703059000984a01c045454015402d80400b958903031481142142b403846029603002d469501c408642100290140c0c0b840f80e0041d01801c1260304121842d19102e1a281c500e410400e401c2c2d516440c40400b104a40c003901e4060704180e5074050140ca0004003007241c0e0080b21807124100314080010071095242d4881c070f40f03d0030b40c01500a5507a11a40e900d900c0c03a003908020840e0010f1300c03410010b4001c201c0266441e0303000756031002c8500c0f80340d000300044510700b402a20980c2c419800e81020001d070520100205803065aa50001c0f56541d0840101810460140c0c0702030702076410030102d000000e500407e00396002404100c5c001c4981c850b035021500342640ca024145c1c052140f80203441a031440e500c00742c84800d20400034600b03a05115040000303000c0504003415003055480c0b5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 785426798 1250 785425548 785425559
    0x602180a17030f0c0118030306080c01050c150403030b062703030c030a0f0909060e1e060d080d140c070b15010f0c2406032102030a050304050c09190c0c0c 68
    0x134040b1600140010480340060150481120111a000c4010a598803020402c15006002c401c40121090916500f0150104007858554a0340b803464003150100d00d000a007014000d41c0154000900580426107a81c20800341d804850400b15160034518a4490308056500d400002c980c0c541040030301450401340c1c103d000340c5003409102c0031001404882407001c45c4076406842240000e00b8003d0014482d414262000b0024900b05501c0300c00b6424000100041520b4032101130045541c00716080c1d980d841c030522021300414a40400408890003601440f840c408171002421089005d181e8280c1643c903580040b20340d8445103206540469200800c00902c18003401604414a000703603030502c0140e600568107128800c60001e0210b943c3d07a603a80c10300030b204491403401d80c0103650078110101102000b40281d80d034000e800c031100810400000080c00c2100a200044031003402600d24111418040c0d164116104000b541d440034038545003d0906952040c000b032910f00fa04506e80860840c10007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 785428048 1250 785426798 785426827
    0x20a0f030b03161a0403050a030c06242108030124020309030a0f081201260f03040911130b0d0b1903023a0201020123010608070c0602180a1703 63
    0xc01003130401e4802031000101240c0144600002c84e4802c5d0780c0c0d0081054a440d14104030703040c10030700d001295160901900040d84040e464015104040a903619030414088003101201d001c0c1d00043c010400880005070001c0841140c0ea40640c11011020300c01074000c50483c0ea900400b4815645a84422245004120700c0c5011038030080c0555440303840c20110142015500c6001ea006511004082400103482e8400e008405440c00d46a0041c004201e03101d4403403656805030f40107803212990750340d58071400444203004541070041000c101440040e0307a4090141181c1044424180042c1040c08860355032514101c12840c1c031080560421455056400348541010070031001c03a05d0381400c481004e421610b911002e11300080c0010445549060b91000a00351951143e0041140040d948600c988260490720281510a14502840b0581d9103200071078400100a8003e08112702c00205445102c1010728a4078003103100761500c2e164141d40d5624900103442c3d290b1051015002401386484001c0007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 785429298 1250 785428048 785428079
    0x15050f24061305031515040c05030a23130203281112070e01030210020d050a05160210050c1501050a18090219080f0a080702010e13020a0f030b0316 65
    0x1810340c20003001e40c0f10404039241052422800d030007943c40a0030040360141c15041c1c0030b6560015102401445114036015242d80005005040d40a40740d01600316652542580c10302251100030680c8000d003464821080100d0342c0c89001c2c0d01900600030440300c008a40719520f49800104a0208403012003030301e50780d008450b0038040d50740c401c081500d07407134901008100c40005000c54101c00419035245104120780c00010020f00000e640001c48160b070026044000d591440d504e0303080c180e0383d0780c85241242c00004160742000758400e4404440e90305540e8008003070901e40c2001003c85201070201c13407041c44c05100034412540e1000f00301e0405d2100c10782000e520a03500885c29404030b091503d507400286241c92031200c0c0d032040c074400501042002c80410000c6015441380700500350050850701c50000c41e101c0d202000c0c0c14028454050b01d0360352916078410910700e08001d0115101c981d0f502005010060b9400707010000b90030f00300004843c0c0780125204036001440240c0d8224549404102d841d40ea06 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 785430548 1250 785429298 785429317
    0x3040f03030f0c051b0316060f051803070e040201110105150d030e040c0f0801060311190521070906020601080703140f0a0b041e0b070e030a15050f2406 67
    0x1c03a40e914800044c4c0822a00c0758044515107000200c3d1014818103180101d503100c00608095611130800c0b841e03400500301d10308204645002551400c10340740084002c680c000486030075104655000500f07645036825980030b54800d9036581080860381032040d0aa82090300d076000c09100482100c21a0703d030100d454026188a8104a00b07844103080014003180d1103418040c0c0840d19180541155660081d280b03405480d490400300442e40b5403450100c0c2d240542c90052940f8000441d882a0313940c02881070f82c0114013480d1205078125800303040c00c400100141c500d440400c0d00c0c2200403425a0001c11094161050b10005007a028a181c460040003815083d03082154040e07215034007a200d405103d007440c464001d110301a40740c01e140c0341000140303681440e4003a164003545000070000b9a04540c050700007100d460b00a08000c02240000c0c02d2003038165006041175a54418084520f9940e00f0291007a15000c401c142940d441520b1041e05502080845015401b205040d203018503024025102024 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 785431654 1106 785430548 785430557
    0x20d110307020d020f061b01060b0c120a110706020a03090614120603071e03061805210714160801020405030a0204052a1b03040f03030f 60
    0x903000c0003d12801005003103c00359669a40d1500c06018003c00055540701c0148008056074266260380300f46500700080060308403105000c3d01d81104010001e003a515a610006043c564881c40b040c1c003c1c0001c14a490b0401071040102c00098441c907001480480701c1410042d11040c1261702c643c081007885140f8a03a680c2421040d903880449400c68400b19407507100c00a410100190001c10280d149051940071501303080d01c806088a0040c0f85c00c111085252400050300e51022602030001d0b27100011a07a1400984003405c1220030321801c469062520550307418452142041d01c1003010340c4440200c5548000c0484490001e0210400840c80e10307140c41d0100b41c507074001d44006072046035150005640d10940c01d01a80701d10b50001200e800115507032070781a8480e000b403120004032110110001c1000d601c00000c84040c2d80351280340203002451a60103d400100ba07510385820031 = true := by decide +kernel

theorem cover : BRFrame.Cov 785251798 785431654 := by
  have h0 := BRFrame.cov_init 785251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 785251798 ≤ n) (h2 : n < 785431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
