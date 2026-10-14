-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3096
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:38:49.244035+00:00
-- url     : https://prove2.me/submissions/8a38694b-6fe4-40f1-90d8-fa255821b6f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 556654676 ≤ n < 556834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 556655926 1250 556654676 556654691
    0x201081b0f030c040f0e060315150406060305270d050c1203010608040c05010815040506040603080c07031b150809102c0d02030a050703091a03060405090c13 69
    0x80d000411a03104105140c615922070800503035081041d070092080c01c107911031007940096500c08220a07140b04e180c0040290452006052a940305004c00074110500940c0c40305007020155035610800340546415900040d441ca003421000e000040994440c407841c4a0b104043e001400e800140c0d451041c0c4189031071a00c825040d1002890400a118070722142d80c0040b001141d60f80d400941075200d180600d01413202d507603880c07005550f0140c00340d4030803884005004254580e402d00ea044a40c1048000d40009413450740c1e82c0391051b03560032030840000180c0108008200740b0410b0014945680e00c030100c0c140f600c42c5060503103000000e002c000c100c18071080e400001c050501c18845c0800e006844901488102000d0000c500044000f02c00c3c4031104030310048121042e000043c0f41000410203800840c03030950303039000c142d80d0b40c0c0069808900b08814504081020f00c40000e030312860349110380328107440b410854204004e0311002852030440b42e00c08283e40032640d80302c5100722080d002004e00029070b0b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 556657176 1250 556655926 556655971
    0x160512010204090603150b010f08060d030507020405390304030c0609060f02040927020118030611030411060a0c03080a0f060815071b0b07051909080c030a020108 71
    0x82c0200d50190400e42d15144000091210303035010030034906d0303030a4410421101c0f01001520000109400c0c0000600701c00006241410090b00000d01c042c000d0038034034107202071035002400317464041394a008007444450130543e0010070100071040d02802a04c00f40040040d01d510b05805000080000c1c007000000c548c0c01c4207100032032f40302d00780c56504401d041c40010103c01c03805019511521070402a28030b041d00c8400e510204005c2007003c01c941125500720485c5a03001100c003061004203100213281d00c08000800600c842c1f03c0c40b600c60142c8860a900e0385402d050203010b1241030004d40c0d0058100308440c03255240c0c000680000c595150906039aa80c40c0c81c00a10f0050846001c3c85141524104000c20cd401e000681c0d80f40305030b41c507624040140c0c0c98a80c05c07548031f54000780c8074104000310700e03c040001e41e040040c0c1e584200e05140130b90400c2006681c1c040c4840189000001003030b000e40003400f40c0ca4040c465040c07213003070070341c000c051841c21170380003e03c8120000d2810b441c000c0b400e54980b00c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 556658426 1250 556657176 556657181
    0x31806040512010902010f0306050904200616151a40050a02040305031602040209090112050f06090a140c0a061707140a050306030f061008010b0316051201 68
    0x25040140c0005144510242d00c580280102c11041c2d0108a0b821108200700d480307402178105649014201103407588542e6544020143d11401c3d03030f920300c2c4850140194603190100500350000048030120b90041d100d0070035008802502245040c4142441c52a0301003010b07207000d0260314401030315040072030401d04e071519420801c8010b03180120407000d4000f62248020702500362500320b0850003002207880310810720003207128a110003070158100f801800748120b04000b00e5004540040e10262a082020001540c08103090f0400c5040b601d007408014180201044400080c032030f480000c2c511410030400e081d90351a22824018007a00d0b84042c40b0309908400d104030008100d0152400d10580c0c2c54a8024101400070352000070050044030000b922107105242243c860074609491515000c00c100085900354001030009030035104000b828100704008215648c4212080280140580e0034998941e09590f42421050b200340d0140d01000d1180720b0121030081115011030300da43c40c06031400c9500c1d01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 556659676 1250 556658426 556658429
    0xb07020a0c060302040501090f0302011e0315030b0a1b08010510090b04060e1e06030711160803031f0b0d020a1206060302070c15080606030a060305030f13080f03180604 74
    0x1c1e01c010800080035038140e000b030070996000342c030b03544001c90700c88101d001d05109921000c0e0000d18103056040c0342d02514120034200d20300030f203000702d07410f1044d2a005100c02800d900c125901c000407401c00c00711010510076954542001190700c0300010a4402c01407980106000c0c4078441d4009944441c20790703001d03950000003803208042040d15076643e254094002c071061050346000b0382c10318040719203150410f035101030303241c0000b8109400c544400600f1200c0300f800418030080e9118944036584003594a18201d001010414011039480c68141c0d080b104800c1d160704550449649410284805504402501d10441c11450010303101ca0070703000121004540c00c171894400900d090300c0402c0859242c0c0090130304d075004a400b20b403071564444c5440c40d800b030041450700c001072f988004940c440c41d002c0001c640100e40c4513404a9031984030781381c07103041d6400749140c160740010000b0031080c121034201007400103022400c00b40541c600360312409a140d21510381e011a1018108125440c01d541d00c105860 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 556660926 1250 556659676 556659683
    0x21e06070c150207062a06021c050103020f0303040503150402041d06040501200702040c14040b070c060507050a121b06050f061f11070306020304080a1b02010c0b07020a 74
    0x909155031030108a06051a0040020041c002c105001c1031701c80c002c884051007141414141a20021420164420a80800d034111206c0d07408200301ca400500e80c070301c4442a160360000010b0a549984108195400c0c1400103d0080d00148000c200c0c55a0119914141a601c20005642a6180e02c0001d005206084c5c800d2405011071022890078440040c04034820351040008028a400ca41c4440c982ca2004c204d0385883c8410801c41000141040e4010810310007079428071100351408110000c44c20b403c20703000075144810220316072051004215003038000340114101310f460101d40d03440d0641c036076100c104003800320f00ca418565008548500310700e03403825509070358000729a941c5140c5038001d030109880c101c0101505401281c403518240c11541307150784407091080080204490150340a00c0d94a0314852140926040040402c1060006520983c030403400ca03956104030550140481c503900130f84d8807106c2a064403800045c6d03040512000070a41005c4454003564404074100e00d06107410b60f004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 556662176 1250 556660926 556660943
    0x30103030c030807080124020f0628050903031317040e09010b030d02190602040b0a020c0102070f0b0405060f160503091e1305060604030f03020c09070c021e0607 71
    0x141036200d034403046500e02ca80d43d100d4464980b080110740004081c020315106203d5003240382c010800411001483c0f202d01d005135604890180103c07401c1880440e03000f2030060b0250181c442d061111107008442e04a01c0c0707000c001505000340c80b00d41d00d020041101900082c5a161034041c0b1169491a0058611141c1d40c00e80d119111840b0782c100700700540b011200356003400308010080c500803502e0340300e0b403500740e00500e0b051240400d40d20080f04581e409403400d507420400480d02001c502c004154010843e0000d0260301d011000082c90910141c1c440f05030008425414000715012008544c1159030865055132604102440d11043d03100d09280c036503d00910a980004010010014001c540021541980144080c0104205841032004c0050b40b011080c1e00034103431000310782e003d69045800079201324102a181d990b00500d45a2020040c2c01682c03140e0080141c0c0d2a00682d0290301807054606400c4c281902d0303000c9085130b00a003507400307140d01403003240602545405040d104402c3d0001c400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 556663426 1250 556662176 556662179
    0x1b050f1c0213090209030a12090f03050f0d080702030315010323040c05010e03060613330603060303051606110f090307060c080414131a040c030e0312150301020301 72
    0x90360000d502551040101800011000032290031501c03d988240c03401a0240c11442c50a540c0c0c03030f002034034120522050003000032001c1000d100341a401e2024501c640024200c040444120071301d803000c003211074810051003e003004240795000c002e80703400c44c07072248400218854040050b40078001c0c43c46200b21985940030b0340d540e26000700d21031500803030103903544410791138407103004407110110050310030b80583c42131020032101e0a050406043c0c4050582c400601d0754820b2041c0c1110b0714072000e070f651220b80c2d25000d0418400c0c11a01c020f006009909040012602e1a640a02280903400440b401005006c41c0141030010035044144001017106080d40c2d01c032001c250050698001349640c5010b445424404038095016460f5081d249422040c05030500c3e01c0d0007407002c1178441e81000aa0040700500c6d10b46620700e01e50250b1320020b0303e660780b019401d220980a101c101c40e82010000300b0103003009950405c403d4003200300c1e02901c82c20361090065541341340c1d001402034501400143c01d580700000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 556664676 1250 556663426 556663477
    0x8070c1721131202030a0204180501050a0911010c03031b02070306150e01030818030a06020405032401060f050708040902030f0a0203010e0106030b030c030106080c131b050f 76
    0x3108107001ca20001120003100c6600c00340c5020780140c0c406403102c0520100240700e1140b82d40281c120040c4014101c0d00c2c0c2561550204013070350b46940f0b0000c1c40c040144106020018280582d0740d101d11300c05d000700325031110f40c0c035800ea031540b03005981410300503000c07201d8051500c82c1d00440303849948201c0501c030001c1c000000030759a103003a200030382d41903251030a03030700070801d80a1410003140d8050702200c1180c0d095440d012110790000083c0d500303a03442c0c1101d0050a40b014400c0c0301583e802440d005031514034000034103081c42140c01104020040070074a8501c1c07845901c400c0343c1550b03498507010f441a00c40d45400d13101d500c901c0303101038003050005c617001540221a4005520401070395103130395001c3e220400200e00780e000c20700454038800120f000600c00c2034400d91140d03c0c2d0070402030440303600c80d0000b030220303086651540101000e50405030030300015051031680c0d201c00c02c074408010840f610641c0c40446640d20028007850402000040742e500940100c0c0c00c0e1109031401c101e20210000641c103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 556665926 1250 556664676 556664683
    0x170403031b0e0a0602011526011404020901080a030c0303020901030902120a060e070803090f06040e0f0103260d0b0105091801050316051e1903030521011208070c17 72
    0x94019114603500c3c0c0c0041256881800342112820010f52510020381c1404005543d03294046558180c881c94418441c071019424021124006841107290040d410b0500510a820005030006949a417120542d0000294481d0b060f03131245030540350040e250309030700d00101c002c2c127140400a9480402052001d01c02000880c213070150501c03030a0200001894565402d0711014030788101b140a400c28042c428035820400741c107048002e070081040b49031513150640e41c0703802270082d02e48103098102c61005000308440080000b24400c074082140c005c40300006911030b01da11070a9910003d0320380340c8080c852164021400d9415085004040007208411016801c041c20001d1003050300c01d10401c26800e80c9681c6400380c020583c1c1000d0105201d8410301d0f2020b0228039401884181c000b03c4c9070303407000e4202c80003000d001c0295210b565500c0c0d480c2a040041e840701070460780e44500038507901c00108084000007a400c00e44590101c08251038078010704201c1640845030348000c60310031803141401030181010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 556667176 1250 556665926 556665947
    0x10091103160c021305100e0108030a0e0102210903010216200a030308070509030a05010e070f090b0f01080a0905060a0e1009240b0307090507080901020a170403031b 72
    0x505001c080807030400c1c1291984000c50003c0d40000c0c00c0b05501024041c5a04415402034015040c0f41445507140303805402c1d140c1c02d030702c604219080841d452002300d40c8020110000c18007480200200c103000c16241e00345102c4040d100c004844002542c00160702c6c00e4041d140c100c42c074640840400000781c24803d900c080c906540c40b08602c01c10248060b1440e0200f007090075a074140d0344400076541c400006403119800400b82c19418401c07100c40780d0000c0c42c2401004407209560740a080310078500710002d203541c41907820802c1d070700f030400da4150310948980306814070402c03091800074280d49590958400510f24140c02070640d000303220030003507184856040f2392410f014107422a0380200d9078003901d50440b45103040007080b07840041800e001c02d4032042200d6940401ca41ba00181207402040028035000e1607a000341446c03500e49040065140d001a0369a9110301000029407816a00010082112070303028006c22101c12080c012905141c0301c0d6001d901c0303020300d0641800c20500c10340805000341052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 556668426 1250 556667176 556667191
    0x130603120816050703020f0703031d012105040804030f0803060925031509090c0e1807060302070f050a050a0203010e011503080c1f020307090504020f07020910091103 73
    0x24542900321440c8240c46541c89500412160142001100d00c121066402040c4c02d60840c80f480c00c0c64803008405000e41002180729803101e030441c40c6c00d9004a04001c3d280c4d41d656043c0030350004044a0b001003032074088180c03200000c0019059407203180100217406241c00240003a11170072480b00411030b0130380040d4000e41040321400200c1e41d81c0e110481c0c03c0354412032840c0c0210040509040c9950098010040148901045d101c1154880a0308021202c246905446407203a4480820003014204102500841d0000741118103101e0682c1c825911602803107240b041640c006020014041076142c5c0c4030180b5070200645d100c0e40c1d00341c1003150740e5040c1d4510682c400d52820554a24000052060340c81d54172801211403481450341c1c480403807507009085001c8940c00fa000412181c00b8200340040b4500141500040c1c503403c100b0703c01407103401d0903008580503610402100089180030000d071205198101c9448049564088044400c1040c80c0e015181d46030404c50500d02d42169140994410000e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 556669676 1250 556668426 556668443
    0x1a03030f13170127150902040b06070c0504110406050301060f030b041415012c030102070804080a0b07170c0a02010e0303070309031103070f0209040c05030a0b161812030e130603 78
    0x200a681c0c13040b040c2c103030304001c01220350f480e407070103590a40382c001090441c0002c20000d9020f58010125506500065081342c05658000341480750b483c040c4110404454641b070440d0600b4100302c0d001d8001d201c103024413010310001583c6042114801d42104544000140003800080c20540e00c0f1540f02100386c8a010540280d2145c0c0156940700b005010b90682c5031540b15034034005203208660b012208403800c60f400d550200f00030790100e0030080051000704407400041c19164140e0070f20700100003025100f8070802400c0c495130301241480380d400c607030410800f54655650786500001680140f6001c1090f40c25404044200092300c4d80543c0030f088840d0081c0c4031103031410348001c4c98a0301c903c2a160028a0489a0541440541015407025600a110785402d804054869000915151000400310f031410110303000c100701983e1a44034030000720320300e05140c101c80052030b030014a108181d010390b00d6202070441802050610440008501c60405001d1070764508a006a4201526442c001550b2414 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 556670926 1250 556669676 556669721
    0x1a01030b161b0206130308071e030e120c090f07020705011e05160609200f030736020403060b01180b0313051b03011a03030f131701 58
    0x301d415444020540e1580d0b400585041c9942c15000d103540981c0d0030ba82000083c0078180310488000c400070301450041030095156001d03464100d16049145403100a0800152101d400081e04020702480310b401c00c844518109200c6070b001c5103041107207000640d2010540040c0404440c61411aa01a03030041c0d0035070b04810b031150010346400d00b881c0e40040c010070341007020404d030500c40c1c006444a88080d056041603013000381c45582c03d0318042102a00c24141502c030701c048005d90201700e0300182a041e01e910b00030560b8000001d071a030030755125403030b282c0c1901d4086803840c1c84c2a10010f2080c2100341c130408002d82007e00060001e41140c001180d006281c00c1c155000344d0702400b40c104400c856a03100c0172030a4100300031005513410181c40b000319501e1101111001075424400c00400c3d801c003101010851003410105400d46040e510150b003505400c40ca181c1e4291004421180344c035100b00040355071104c2c1c0a1407085c02800950010705600742ca0700c9034828120043d008041e00b148080400100034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 556672176 1250 556670926 556670941
    0x184308010501230306031e03040807170627030a030902100201050c030718030c140103050a060b0d0231080601060206060d0618020301020a03020d0f060b07140a1a01030b 74
    0xe24200480f003280003a0380e089850301e9410304011640f01e40007030141c41084004540310140c80c15a07255400040e040400d051201d000c042040340001c000c220010581400e0b000100c1c0d81350b0701c0c00780854000702103c217420948004040d1106460710040e00450f5511000b0580040c002e20b4000350403845081101000d0000c0c130300c14040e26025400010031149162030b0040f00742c4070710b0b401c0a00c405642044800000105603008444401840c4094102c0401000400010f003142c4000b0b2001e510740b80f41090500540d4040070a031038445070b411314016592100d1010704010b540d07002500e00900b4880d421070f25000741588440384c080320204411284540d0300c0708401c0ea214181250f4540c0c001e61101a46804261190401c18142c1140d4072000d510070195000300c0d0990f80142c2c00200420380004500c08855500d100708100200244000c000e0141001c00300b07000d0344901600a8492000e00c051591f440341c2c184600405954444490134645116441d46110480c0910050398030644c45000550340c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 556673426 1250 556672176 556672187
    0xa0f0509060408030f19110d0c0f05090f0112060906030302100e061303180e09070602061501080c040b03010806060a05010807201018060506184308010501 68
    0xb5a5002004030b007103a8908000d0280400014000b0f1180b0b0fa4800243c2030002144c4200064615201e480700d0341c94075000001f8066803980d002c080204800d2107406a1119804019140605002c42d03d804440305000300480d2000c22094442c00805d11340307107001407070350019881502103a200b9025146c6845070541510300b21071408026403c0c0390040f0000030844103c034030000302d0080c0321303084c403000c0441d41c02104210070005400c00811302c00403006005c0e20010400c643c40061500d40300400c40c0746000c080c0140750381034942c4040c1c103021105022035421400c48040c0d9000c0d080d04501c2d00d8896030b40340c460941d02d00c015181c003806070450201c040380c04c0d40302e031003600d11a01d1180c48854880b0582d107840e1026008149451402e4007660b0f039000c1c0c94010364081e43d030400e8200ca19100c6140d1701418074104550001c0d20b52442548400c14222007200a049025407090402c8240c0b003034040001c0010500161848901c0841d0303c102c0e500103004091600e0f410b144a00c59500e28035075a8942e40107560 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 556674676 1250 556673426 556673431
    0x41103061c0b0402041e0e0618030c03041a16060f1d0a1119180606020102090d1203020f03010608150f03031b0c12060103050c04091211150a0f050906 66
    0x11041d40701c000f4016050a4000303030112502c030a10110301c00910f408050440302028289145a080340c41880301d5840b08a15100e0040c1c0c8a202035440d021410325610b070307648101d1190f0007584c40034000d05800400c4000648840303101e003480002c0710042c2880c01c40b0040198000010026180480d42d1100c240f0b00720b040607211075004010850b4a02c0c0703440e41519084500e44240d806000b27049950750509030704c101740c030046c070303608000e10300b075540101340c42e4180c94154100b0350440e841807221003010b5540b05100c440c00d98100c510389920044143c011000380c803c4059500c100f040010000402d20b510441080c402c414107188160361035078400c10010303140594190560f0640c41403156400e284490103121607a83c400c20f0494411440ba400883e1401c8598107003258660040001007080c000144452808002c0c01c07941005644041d998500300c084003100b0070010002c00c0160030070101810400942100f000308080c0b0002d14101c0c541001401050101d05156030a00012407809100000c1460 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 556675926 1250 556674676 556674683
    0xb0f03160e0a140f061203181318030c0f06020a2106050102030406110f0f0a020306090a0201021504030e040510060f090308070210090b210108030a09091109041103061c 74
    0x141252261010225400005800c8035804694420302070071200d000c000601c1c000000054200f04088103400702702d0f00d10f070901510303082a8203200c11000090303120310b00070202c5541400c0655030b1940e00e0401c01e4901003000b0f002440d0520015081100c103030481e2094030b4040880824400020304000b50b03900741d0b4503510595016a00a010910506016105000b2400320000480321401c1d503a100b801c5c9004080d00040c40c0c2c0d034010107030080c00e60405000b01c1d41e21045440041c1304101d070f1a80000d65569003044201c20000c40d000100d000c06208050649001400520900c100d052030401e42c12200c0c0705204520100ba9001302000e080c03070107105550120b81d00038082c1c5085c40d01c2a020300c020803102ca01d2803020001a4003000c1002e4903400041c0a100080c0ca800d507003452042d0310361782ca909170182c0061046900c10b0000105481d4010750041c2900c50003400401c500030700c00300401c420702455001c0c5500c1820700c111880f000003020060345c0302e024104d6034600c1010101c5d0000c80d2028a860025 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 556677176 1250 556675926 556675961
    0x2402070f0b010b07150b0d051c080c040f0510030b09040510061502120901090b030c09100e0f011d030a051b0a06140708070c081014060a03060b0f03160e0a 68
    0xc05e01e40185521042200b90060724248880c00140c2c1d5060905040c21f540410321400d00302030b002101e500445495211b460216170904d82810490713040b412009500c55581315080c000b682a040d0791007500310b280d02240c040c19a140034101880c1c03481d1112034101c60507020b2841c016000821284c00c01481d880c2c000c49070007400308401d0140890300320394015203006044c1316400c0c0c0d0004a031000354004500c030b40d0510150070749810104c81044414050481640c007082841c130140501c1d541e5603510301030b40380c0007400e00d80804215156030310540d1a141c1c3d0081e5250043e1728892040c040007142c000039014501400c14080b000c084200006055940521000100c0c0350100d070010b41d0b9804000c000d054001c150340350802c03030903555440008002c0d812124294000d02604800303111180a09841169400c2ea601824600100454043d0b401c030710003d040203488010301c2606803075526002c1d801e20750203001d99000550809140d0500d800d42c2c8541200d10040e080015002d07038071840341c0f100307906084612 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 556678426 1250 556677176 556677203
    0x60d0c0807171311041b21020f090d05120408010b0111070e01030f050c090406020423090a09020d02061305030601060905150c0102160501052208072402070f0b010b07 73
    0xb040c130208136100c29250096594515900425070759a490f010040300740ea141007250944020064240803143c007400c101a00601101800d01c440d6001c0e90b50758401618035000742441030031b0007413409840c0e01c5003c8180a0006001c03c1c6400103400c0b000c1c11000a8031a1562485480b00b4142d035004caa12608928000d040b0041c8000789080c4204d000d528010303002c030740d51100c2600010701580401c0e1070880307000b980024100481e0b18412008244503031110076000d40202c1c4003000c20b2800100900300c0b0700c40395903490100308550301d8202e451305442d00904856150729039003900703040c464001d014452203803103107000025a2134840c85020050ba41d005d0f02e00c0e03030010350129201080390000016480103540034004100e00c41034424031070000da8001c400201d402d04089440c1000d5108070150310b00002107a03001600880c0b002030894a040d031348052070a420340260000904030042c9112030710b07070355400040d458040c4031644104e950150300030b10080d810390740d8035000155207215140c4002d10f8825070140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 556679676 1250 556678426 556678433
    0x51203030a180b0f101509050f0a180b09010803030c16060b030d0903121125032004050c070201080604090c151d010f050d050402060d0c08071713 64
    0xc0030302c0c0091120354601078207580d40f2009081001c44902420070001d80810610034501141c01006100042c07911048503201c5200400241150290707500820340705005030382c540c0f106aa02c45c01444440c00105c0314684003807040c4007800f41c00d98450f2007050a840082040c9002000301e0f8010700008030050304c0d0041040c026540c549115105171040c40e9580e1015800d610241b00ca005074484a5848007080c1d07041d49030034030201d00c1c0d4048003001c10401c14041000c100d0001130f02c0c10041e411150303002a452229070680700c5200e45400040c4040c04001d503014400c22201e5000322900300444052005070b40d00301c80c00c080c501030051302a000902d108042095828190301c2650068088d01c80000360681340e48a051480100c10480310018014020441c079926901c442c81c05260b000f407810b44500400f50800174803c0c0a0511012615a503820100d070443d5036910807100300001d000000d203c0c9144000001c0c01203c0100d80e264041100150040352000c40324500e0303071060120300d516064851a40d00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 556680926 1250 556679676 556679681
    0xe1501031e090c0f08060f0709120b18070308040609060e010c0b1005040c05070b0606070201020a170409060605090f09280207020303190f0504031205030403020114010306060609051203030a 83
    0x420070307543e4143d09003010400340c44030389000010300785400060100781810446606018002800b45080003200d1105000c100c00c099001c0414541000440303c41351600c92500d110b0301201ea60a509610800342c0c0003041040c850301510461f44651076288045640e824241c483c000c081100d03500150b40d1b41b01000004101040c0309822001c440c850741100ca0301c030f9000c1012109160300060100d03201060b40004c000703e03840c0c01039100405603242030030141142e0020b5902c03c1e50304d50040c165404054804801c2652100707403002040c010406000160b0740704000382a0740d100d01d0240d40503414100d078410950405500042c01344040300c1181e156620b4009483e42110724080441301040c0d001c000590142e0740400c0500440c7c4c031800341c1d607454003090784405850010608054002d022052000b040403070312202640442e640c0604104c2d540365100c0c94101e00400c1c0c0f2450b03041c09000c03418004024407284d13074071130001d4617410303211201116201c208000928160300d001d1a060f90041002038005481c54 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 556682176 1250 556680926 556680941
    0x5010602030a031a281205100e120301090510090203041709030c180a0e0d050d1122050111070f050f21010207060b01030b030c09070203130e1501031e 66
    0x10404004d8942119000683c140309008140580c4401d42c00e04a074144201c414240c0144804030740c88002500e01e950b00f83e155101c2500c20f209039542c46641d200103d106000c005140d1856220311350b50b2303603190350243c0000d042c02d0b260070080b00840540807070031440e54801c880c0500d4000b0852101401c41c0200c0d61030a9200000c00ca4060044181c1028581c68210350042c0441c07400c3c0c01d080892a1210005085800710580492241d1121550f0550580c000045803031800004802040c3e000c4000c070301120901c85c8038180d200300340d5074070b0046084800b441e43c4031064580c00da866254070303034112020b00e80c3c03a01c40d0f0080040500b44d0303d5080000b4030303110741c08028150000d0801d004d41c441411741d45049003080b603841000307a50002010303c00c1102910501e805641c0900b0100b22580c9000c0c08a40c1c0c803031155104c680a504250041807400f0b0082050f11402d100c0144c8902c019501c4079040700c004c07141a01e881c1c8290521944859440d0b01a0003149200d24401c2c6154442600e515103100260144 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 556683426 1250 556682176 556682201
    0x150c0519050d020c070311060307080a0c0918090b01142d031603060c03060311220c200d050a1209020616030809010e030a0c02030102090a14090a05010602030a03 71
    0x40000311900702c0c150010b403c00d0f206450203050164a5401c2c0f4205191440340305a201d004204108001c19800c41e40a9401104201c2e0005084c000c81c0c6c000e403000b800d0740e000000d0000310022281c0007000f2a40004400c24810304189101d640d03180002845030403503940e441d920118980903035011441012580d094405440e880c0480f0104000200703003025444091100c2045d40e4403030038000d00031a4020040d0602462a04114503440c54541c0d0440050b0410168850a80b00c0000c8a41c0380d4601c2401915030502c00f0104807110711a8000351a0b035080355402c45441851584181c0c12890104696000d5001601e815181407515101141c01c1c2c0ca030114070740c4d2001d60350014500545c840c6800760000702040d12010303101d0759103418003070100c400081050003903a041c8807a034002c5071404426955142c0b10350511302e01d0040c0a10000e0701a001300098940c100614860026825100001c2401503180645041d01c0351340b0750030100010303240300f4024a809030740108416070000d88a5030008420605 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 556684676 1250 556683426 556683437
    0x61207030f03020304031b06050702093d090e150603070306060f0509010b07030c0219080109061d070f050607062408121c021e040b07150c0519 63
    0x88035600e104030796040400541c0168008030b130900c108403481c084691f0301c20f8004454030196262100c01040c500c20008001e01410000001c6549035241c1109040c01082c10140d52802890f8a1312808a100140c0c0040d181060311500c0080c10300e1591140544c42c0310b007040030300510f40c200c01c03010948107400ba107125010311414100001192140c80f07060080c02ca095009007005192404219443c18182c109645010003003207180c00081d0003540d9240103981c10340307a40300741c204c400e201d414080304c007a40607460702c2d400d06024004004050f4080c1166003001110444909103070381c117083d45d03920503010f2a40c101c586503505110603d4240c02a140b02d9214a5011400c20016440d101c1c41e00d07443d0103001140e5504c00414004d03400240410002e6803a4010b0290414108960010000400701030740c80701c030f60340082c0301d040c03180046c20103002c00c40c460b02201d5030b5199104030f50619940305040075110a4082840d424034200240140c070400044c030b9907600c1c00d19504400e9000000e8001044170140319 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 556685926 1250 556684676 556684679
    0xd0f0203100203100e1611031e040e07110d0509130207061e020f091c080408060f061c02040c09030209090c040e011407110304050406121b050306061207 67
    0x25010099120700d05080c460168584c10010b482c400707200941e401910781d02194104005600c060140c603101900e400f40340031f0381c25044410119003140f10309800c0c001010408200100d56941a6004004482c80740020315401d40d0b40380c504540b2074a25003030001540e0021103030000107034420000f41421540040c2850865004002d1079000c991120904a40c0da5880d03e4a907803230303458549402d11070410003070030940c0f03048090030a0700c0c014841c600c0344603c610710503145a80a02254040300e8103884d40880559035175505c809819903580022904030810b016000c0c0001e00508044100414170605a83c0c00c204440241d420480030b00001001e020802c00d05200000c003580e070381c202c0580142c2c1e4010180c00107411880074001512003040e098a1607071705003150301c0644002c01c000140c1c031a500c1d1030046000d2035880c90290840c4266807116070f0090510001040e000041c1c000754000c50f200395811340300014410f0a404071894580301c2d940d4141c00107400240c032800c003100300344903140e01038042d035406a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 556687176 1250 556685926 556685929
    0x314070c06181d0f070f200a02030303011415090108060402070f0b010e0a0b1807080910020a0503012105060103150609020301090b040b01111903110d020d03290d0f02 73
    0x80b010381c0d00b803c0070341d0000403d02c070444040185440e000300207440e02595056800d0b001804101103001c4c92041408080e40400300c0c03034818010720500e640c1c014113803030382c3c1d5035115242c07010001401c141030700c1031000c10719001140c8050000c6600100060b140da500c02d03070750b0300c0800c4025006a1000d56219008044000001d900c555445002e4031924043c03940f2401d0045a050403a0889402d240c000e900c4081d139000a80300042c003c50b40842e09103044442aa01c07440541d0802c1041c00b006501381d4004902c4091807a08103003d18160b42a100282c14601154145140b075148032800180941e08018014408941d10720030103080d144040d00302107030030780d0b45003d0320301242c0c001d9002140581c0c1d101881441450240a003105402003480c250000308110341285407900c12003104e010078071404010610426008200c520f04c13124820f019a4688111030b54065124040203070381c003001030710b01094103a140c14080b182c04203101540d1040a0000c030035400f80070101c1048041a10031100903400e81005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 556688426 1250 556687176 556687199
    0x50a02070e061f08090115030b040b0a2703083607080a0302160e06130e10090b0a0f020a0926010903180b030403080c220807030314070c0618 62
    0x119961359410540349081d035405401c4130241d044803803640c80d80ca00d0400200d400b440301b40b43c1282d0069402042600e840261100900b044400341ca11008250100416860158401205140243c07100509030ba2150051041840c0c0103404468080d03100a0031100c0c1d403444034414007100c0240b02140c84041d150445503140c291031601c1140140c3c424071500000e030307211043d400002c0c54400d580c150035003461000607a10041401030284116682d8100c0c080703c030010004450400b0300900108074102103801c01041e451001c88281200c0b41c11315080c074601348200d10032203180c074041d60b40c0c030010b103070400d111900180f020803c030407101d007003400540451140a01c43c05d040d261007622004013403003e8015100e4045a598002e80400d1814010040070a0b000409284e0009103203100c1d5a9030034910000f031044010913000030200141200c2d020038903580c00a800750503240a40c480d042240006000450305103d5000000c1000008407410030003d8041c03071444049032942446d1800468a402c1e01101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 556689676 1250 556688426 556688479
    0x12032706090d020f0c011e030222030506060909070b0a1101020a0522050f0603060d060c021f060b0d09030203190f09080303041a06011112070302010c050a02070e06 72
    0x69582122480c1c0682e142c0420220000005103009459403440f07101c000307404005c030325003041c00802ca12101511800c7c0301e581281d01c030358801c1050700040300d0820450103910070940803c940301d01c91f041c04100e42d464405100d500c61011040204503032410110a052543c10040200707007403001107808030486410030300207040540309540e1940d40302d00c000c01d02d43c1d1a103c01150b4945c51b00b44691400e04c00c03526410b9100708484020f0b81c00340c0d6030351160004196202002280a40b026240c0710301d1001c1701c5d80c04241c944094100240d4200800c2e082c0111a04841a903c42e910b401801044469046400f0360418005a8044c2c010740e802d10f100051001010a144001e14000400c1c101445c2d14268210390510050b1000c04021400c44c6420381d555940207600d10520000510184e002900a80c0f1070341209996030204001e84019696449040f440c50708015000c50140d401d01001028407403003141926005041030703006108252904c007036040341041c060304641d040b180100701c101e000c3d42030b00712100c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 556690926 1250 556689676 556689691
    0xf131d0f222a170c060408030409090312180b01050a0e04060e0703201305010e070e033309011103181912080c03060f0105030a060512071712032706 65
    0x20080300d4904103c1d040c034504003e481d100390350500c824852a4800400d4038142c030f805500004100615080a40e00c4240c90410385070b4003030a000c11030210072407401007044a00d2003000c031030380c0036602d61f81080204d201da8080d00500c0d980300400100400d00d20380003c61801030040030f03942125140d8481207460255100c0b640008052034600d86010301305a2629604114031080030816941040000c0281d03810140c42002004110007046135140e80c18060140c0d000d0302d0402d0075294107628010100b80c0c0020b40041544142c502c2c00041c550981805072140c00c200e42041503245540d14004242110b00d10611a81f842c440d44035450107000540b891480000e014680e00320b100a44860024280b01c002030649140c8e04080c0103200c490b8684000e01d031040142400d103c1d4580c1d0311544000000d0030658000d5901c0481214409180003010488a080d203041c09842c00b11400311387d840958507012a0150b806810741000002e52092440c04144440a151802090082c01c101c152900d080410b94551 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 556692176 1250 556690926 556690949
    0x20304060806030109020d081c0c030f060504060303080105011107030807030302030f060301090201080a020c0c06040303030209130903080a0f290a06020c060f131d0f222a 75
    0x40c44115004008558400002c4009100e8100b80d540070035001c03070804800925403800071900c10810026884480c0540384070a07020400410001c5004000d01960300c4021354462070b1190104440c103142c01100103403509502e13005c07040d034a000d00448a010108007541154004d018010000440c10401003000300c2c0a56030240c4c407818298040c4602032030203411180b0036031410000c0320050740c11440721a8001f954400050315605044042404e12118a02c015840030f00001d011003003541607400341c941c8000684001850380400c9001808071021100082c4c0860115800900342c49036070740049040c120140e03008070740b403c032a0f265115034814144104800815019020040307081c408903c00c001e0890744003c6c40e20000100126407544980900301030229000541d04644c581202410720041c228000040050329101b0b1104000d01026180c1001e44056100421140f03269031451201c1c42001c0c04100c212000c0799a2142942e1075068402e01c10300750304000c551360f40810111040000c1c070842220 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 556693426 1250 556692176 556692179
    0x20a0507020f120d0f0507021c05070605130513020c150a0c0302090d1214070b040b010e06030d03050402011b0b0103022812030924020c12030906031f06020304 70
    0x10030001c2d4001d044080e003d00a41141c0d0000301c040012405081901400c100d40b049010400464940c03281c1140a90000e0111840c00300c01482d40030103100a50242003511001c40d100c5000b21001d11071440012201c0620340024441d62030300c00c0c40895001c0d4003000051901045400380d50410390742c4030300035031507115082c00c2040844290103150a4802c4a14045150403010000034a24194504010740000703000c01081c2252806412111071040304101d01c10340700c80052904060243d0b0032101205c40200c8500001903070076141c2070150180d82d0003000340020450b8400d04034003e20000703009034100320441005003091102c820341c20400a006a850b040c0540c11130040c09080500524006d4011140fa01004130907400b294004043e07078181ca0211281c402141000c880e41405500038000488081040903261075032203002846000e000e800350340c0001124002c10079020b1840f0070307040c03070390b0420009010700d890140000c580c04183e4410b900e0010707108842c1c02c8010742c1b2035000040581d100180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 556694676 1250 556693426 556693429
    0x16020109120e011202092d030109230705060d05100902041805220f06110d020901031401030b1602011e051b13150201021909060f092303030409020a050702 68
    0x302c0d204c00c1c241d03c00d00f075103041c0280004c2849190076580d40c4007000c812416000c5008020020b280c01e18070014001d1080700300b60304094100155a802510320b403c42203d05105001d030100d825001c40350300030b10480c14119904800005400000e00d0808a1001e50001269031482d80c40507001522030100403023600c1d0180d003440380840741d018040350f00c011402d4007011111240c1000101025600403501c04840c40f0a25012002d17043c0794159514000011440e4509944039a0182201c100e090341d01303002001969180b007000344420f001c090601c40b40f2100080004c1105a9000030116203440000f55030400d1421542d41d00b400007021041180d00d0340b0a01489042c03124041d012500d0003840d080c54001700041071410034255105150566480743e03407240d41c4900039030545400100b00321640b4032a00c111407005219801d10f006213004203e03a00d618507000c9200701e44050a4602070140303860200104541a04da2816841d500c0b40d2600c01003001292041a0740040c0c8075000b05902c41c50b40f40c1c2c09510 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 556695926 1250 556694676 556694687
    0x3070c06060f0f08011806020903160303051206040b0117062107170f0a121b05010504050f0a020105041a09150903192604050a180c1716020109120e01 66
    0x384240e1340d0740c1c14000e82d0b01e07a440c250940d21178460381c0101c1c0165070b40e40d0a000302e03083c041c3c00a000f8608024250700081819006401803007000d8038207c81031800d03079a82040000710340400300500e0000350012000c01c11140000600c07904402c008240a580b0311f8050354540c0c0008490014100d6504445410031503400324103402d59021191101910408101c810b405a607141306040103000c3c65504110081311138051000c2183c0c4510003800065010424100340d4042d240685040340e80e0320421546a8000c400840c8403c1c540e41e05948282c80e040c43c0c00b840c071070690030780c1e06449400681044204841d5030361048841101d180000d0294039401d00c9802c15050102000000b52002d20540c000000183c01c0a240c2d00003d410395041c00b4a1552002c940446010395001030f5000964402e01040c0f1a4080701c00e00b86100c3c5001d401d214a00715510111f5000201001000d000a50400480c0c9032240c2854240c842c02a90702c0009a07c14490700c9000e0301c1c210000c0028017062a000c01c54a0b0f03941e108 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 556697176 1250 556695926 556695929
    0x30a0302010f0c09180c030605210c0411120402060f0a12050739020613081b0d080a020c0613030b131e02031203010b040e0a05071403070c06060f0f 65
    0x1030800d1001c15141260b5580841c0c034088170010382660311101048200d00a87c406005010003900165641c09c03090a440078520400f0851182c03072143d2455400b840c03034030b40144512442d011003803038184614038104030b0583d40013038401c03a441201440200c010440d2440906980300c1a80d99507400c0b03403020070500e012201c1c0901180c040080b14007120700300b42c514035065811902002c8821918800d0601e40c100c0d0040103c400a42c062000100140c0b003902204d440410340e002182a80c040c03135034903c50122003112204280307030819082130728000403400314800380c603807440303180180c4840f031062000103081641300c03100704c14104050440500c2071068040640d81e0003041a0500d41000e4a56203030108044554043c140220a64030301c0c000231501d05121a942d9071211400c902d4507542c40e600d005650b60010700031601d01c0c41d65600080c030b4200007800b03554002c04070341d03c030750705010780e46441807065900040c00785007031000c88550040060240d202d0341c0000c022464044000c02d003030170358622145255 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 556698426 1250 556697176 556697201
    0x10051603050717061908010f0e0a0c030605070c0606030c060e0301141b0f040e0703050702121c090206160b060a140d0501140106030507090504140420030a0302010f 72
    0x6290811080d242c128103018007122107440503c015035107182c001002401030f8a5801520955988001584601500284031100403c881807040c1952101c0d81c6980e4141c03800042c100128040040006c01c6041d401507402c0540d1340ba01000f107068544410055641c2c0c1c2e8807c4401030741e002070421106900c447c500c1d1030700a0460007407214685000e07180060500c0507142000d500c881c2007030964040316201c1155065080d2071150ba464954030b84c0307020205c1c4011076100c0042400c0500182203248040780110754031a0081003541021149042c4090800c120072569000c02d540340700034800369035070700c0241c00f04407035015030034545400074601750301c1c2d01502624540c043c0200035424004503441030000c01020800742c1d1501c01a04c05803c100380908109136a585808007604004542c0c543e06802c403902c04c00550321907030b068070768a070140300c2102c820102c11008030310048045000034140864200e007201400a0003001c062100c000079003800d242600883c0943c0d0b48420303041c04250701c1d0245a40c244003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 556699676 1250 556698426 556698431
    0x31403150a1403010f4b0e07050303030405250513021e0313030c1109010e04050610061d0a0b030a09020109080a1e03020f0619050a05010515070501060810051603 71
    0x40520b02015410b80a51038040051745c482c4070040c946103454441d0390030501b01260590036403094001d2001032404c041404214090580040f07250300780081181c0c0142d901c08020a6403c80f800003000c045015628a1a84100004000a0140d072591154400c4000032400103039180303403808080c8000b1280d0000c005604400703008004907001c624001190607605400c2518241220f45000e0f0700b007444628426034405079020010030003d80c40398130b95124a1141c0100c490a0310351007001500480140309080002d00d002c400d081c1417900d0a40f1414040700050320642145880d542402201d800451301e8028240d03580104005643e44209140000d02205016042240142c2c40d501200001e0100221203803000100500806108000b60451340c95888241c5c0c206007881895500c80440c010409194181440702060384070b180c5101e41812204020207034061500401d0075002940c0041c00250b03840c1d5610388c0e000030101c0080c0550701c5c02c48140c2c00002202c0c50203115060214545004001c101803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 556700926 1250 556699676 556699691
    0x601090b0901230d1409030705030a0c020102031c0c0e010908100203040f0516061d010c030e01170f01091107030210020306060c010c030b030d0c031403150a1403010f 73
    0x30314404981c0c40d100e0a103020050764035100d90b26a4000c21403081c41440c1c602c00036240d2400031642d030090f0207102c4035681c106015203404c00d041e5584c0c06401800340068004210f201c0005004112882e1250301c180156030501e81d02412910300042c4440d04842a680c494180100e2071f5031108500110420909050751582c0c2003103061560750b0903844400790819400000714050101d100d119408591b48081101c0d02c5504092142109102a1003240013045035034252442100f00c100d5000031110301039441480300d01d140c1c0ca08a400c0035011075501e06028100015100304045100d07094812842003182d2600c55240000c60b204842402e046802015020311408001940c040780c9006401d441900150b01c0f6180c1100280c41441343c40c217503086940c83c04541d510942e8060b000a8820074007103040c0c5039800d0300c400c03050380d98001c1e10600600145107140d00b0b0001070183c034055500846d660650441d4508500c1c0072800c885d0090f0000c5180140c41d0803008100c0c60240500021790510500900085 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 556702176 1250 556700926 556700939
    0x903070c060810212f0604185006090f0a1803030e070608040c180b040c03050709080601080309060c0a171308122b020d0914060408070210021c090806060109 69
    0x1107994800a42c0d8152121344180d1100020308100c00c010104204c000342400040c04c0c2404921092683e00c07210809d566601420100c448000a210b0b40c00509104180e6880c0c0c1503914212400400601049030340700040410b542d20081c502510a03c692000152031003100c11103403420600c0c0d880002040076204c10040083c84042c0001c04503410504541637400460382e4030009001881101038005280800010b002981900002d0069446807146544c0640f01c04000392034440034003803405280d00c01c0103c5605820a8002000b60102680541c0c06c43c0c3c010780d4610070107450030f000320700c0c0f903020101d9100000200c242d0980010701d0b4540092a902c00004180e40c428010b034038000e4003c51690101c000c03200f180d00c2c60780142c000d20380c2c4110b5448038290b0f440b00041c44040000d9402c000003458004000c203000030b096008541007148a42008625820401084a06c03000901103000300c004c40c0c41c040d00755400c0e8034010030258482a030000d0400034542d18022000304030a0400604a0040110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 556703426 1250 556702176 556702199
    0x80105010e15120f0a0b010509061e0f0d0c03080c0d09061403040203100624020307080306122107060f1b03050a140903070c060810212f0604 62
    0x102c140580311105042c07008021a0300b444118641c00b4610702428020004120300541c10702d0585108840102e16901c5103010310140000c1c0000107200c503041c2120f050700a00d030000074100071080040c00107000038815611005117401a500881c0d036450b000c20b8a200041d03040c040203500b403001c0d10b030080815180c0340000382030980110300c0200302a4000b002c00c055403001d200701c034500d5104010500c0841d56504800d1180c0b100d0700b0184428030745d000c41c125403d0b4404002c41e40c00540206179181540c0768001009000a10302d03c525102c0c0c8a13061010900968511844105140245d28103441c0c0826040c624255444011400442440c0c9441224000e1010740c4030380d00000e1514001071a6a0b40c2410400102040890521880c050500300301410038004001d05e80503108401c04049103917500c00955611f20192070705600740b03001500900c840300da000b0206083d00254072829140c5d91780e130303100c0081e020040d02c0c903103150340b90003c1140c800040c070301c0c40b130b00d20741405032009840c1a2070410000e50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 556704676 1250 556703426 556703461
    0x1a0a08131e03030906020c0a1b0b03060f03010905100b0103140c0711041d0f01140601050d020703050f0703030510060e01361508090a0c15120213080105010e 69
    0x1032810041c20942418031a0380104c9a403a8025421540e8070b00c181d403000d94440440074200ca0070200328900c4c1c983c001030703501064126060f0314451811500c4d0340702041042811030703501d02d81665170b070b011603c04500100f2403c50481504100000c0104152000500344c4260b012950904007441c03051052401c0c8071002c540445070018081d040c0c0c1e030417580014006c7e0800f01c40390b0140c0d400c1135482c92640040402c4008603081c18800800001c05100010401d02c0c00c11212140490018003c88407103410707540041071401d11034035280e881c0420341c00c4002c0494002c0303003054000940e03c00812001c54883c08120300904060306110f1200704116000070201e000e04038440740c0a0150821807800740c2411004050041c0841d42c0000c052600c0e9201c0448040110400d17400190984020800c0145c010400c00700c444d40200454180313074202510f049420504040728400c01c17a0790304000c08440031701e2016040c40c0c6c4500d14649034003864401c0150075124182c02030080c40f0050340a100c0e0000e190003003541c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 556705926 1250 556704676 556704713
    0xa05060c22030f0305130b04140f0f0a050112091505161403340203031017211201140f19090e07030807050606010f0503071403101a0a0813 61
    0x40d60380d290122040024446c90780b10400c006c0c80810042070299007a0612000920241e40c01c0c089405480100040c8080208819402007499081808594070480d400710502c0c041040120302400c4955802e5404d0701d40542e181220707952403003130061020389607075030310350211032858581c000d802183c2521425100241c288031540c107114850041e100c0390503220884c00c000c403450f80e01c070509007040040d4a962048900d03e00d82c5400c00c1c40421100d801c4200c00b8020300c0008010700c0c2e642d8411154044030725241041c030755448810301c0b150801c2a9510541d50213000920b0740c5551480d880d0052040407912030080307600c91449203075200c4240003244409400c0712982c14000c50075802c1380051314104800340d040038001d14400500345041c880001100c9000780400c3c1d030b82100c80403400b803048400e400305558140004585c4140103200c40f1340c2314007440d000205445001c20241e036a46034801451040039130440c941401160f1200b002d03420041046d44502c008414904010143e540c3e841841c50300e14001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 556707176 1250 556705926 556705937
    0x1d0103020c070e150a0906050a0e01060207030803070c020909070e150108150f0d080304050d0504121b1707030b090109022202040504020c03090405010b09010f110a05060c22030f03 79
    0x140003043d91400c140413070340d400f512141032643c84112440203803182e4050a030280b60860300020390b4418404001e030403507070541d0240003010305540c2c03449034a62024044400b080b0300c00c2d042074003594454801c40d00840c0040000e01000703162808241840c400209480320458149900c0c20307160b604244595403140321000520102c01c0b52900103414000148002c81d00144201d11580030400e2040007540250702401c212075141c00581c00841c0c1a1085014058039240b1032901d5500207001000342508027094101421111511498010700045400941d1035155111040400611280902e000e030006800170003406803105580115802e12402d0144a0001090851448402407d6410345000e840000d10940d60381c0d001d10301090782c0b80c0021207003603c5103182c580000f650031041e504480110720181c44030104440c0c215401c5d00c03141da034844941c0c00341c0524004000022007d0080c14401c44e00101c80c192141244528000001e1a411105202c0369240c0c1061000c240414104646c103940361601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 556708426 1250 556707176 556707181
    0x216120f061d0d0e04060609050d0533090a02010206011e05031e06070c0b06040c02010207020d210f050d02090f18150904080703030e030f04061d0103020c070e 70
    0xc001e081e120404110450120014207644801180111000c3c00c0d40c1c2e00c1800302090340c1c08100880b0603e11520011940e104810031107410720004109200703008900b0f4841b285034823503860f40400ea141c165185144032441444454000041c19160001075400042403030666950001c0e65461040c060314205101c050b264046a007450301440000c2c20001d41504c000740e523500450042c440c0c0000380718156015160024492078031036051030640982000350307010a07895590a00005005000800382195003c000501c0940c807030031141d400302481010358654032540021585d5807103c000c80c40400708030b001405251510360000c20744040511450006a48200070800240100c10303010700c29822400359084410180d0b101d144d083d01c11185030702030780084511078042011800080750010220802440018082407103a44400b1038515407a00724bc0c07804103d0360810f4810342180d0b1144002400302d404031942d610795051004410320007070a00707505042d002c60703d142c1c42d51214001c20001c0a0720400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 556709676 1250 556708426 556708433
    0x111b010629092808060f07030b030a110604090501031109062710120515013516090507030b09040803040b1b07030504090605010207052407080a0f0216120f 68
    0x1c3d00c051100100b06483e09080c1d072404402d031145021a80041c22954a20002d00414040c3c040c09090300da000300504202c404964510008021007800140c010304203000c04540181c0074816180614002d51601d64820b8885041003503120000b01514090b4100c0360030707154071040304d880940e0100d04600319404c10355240400a10400c4a540c881e0991070180181c40081c0000403c10302d0f244800c90341ca607400c0e80c0e220700407a42402d54465110321808110140912510f240c04500100c00380d0810544458544820001c03007620100e1700180c410317036a542d0500803034581601c0b07411006001601c502e080741c0360a40b104100350100902c040c0c03400418200107103c2c0704090107014158441498110380b40c01031030800500e2904a4000d080d481c1740780c0b83c0003040035800001c8110032200300502d948902020705400040c54000d1030407000480e6414881500080c459401070400d00305103554240c010b03002880000d00d48000c0246001d0345051602040c445180340c80400d115003500902c0c5600341c00302d2840e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 556710926 1250 556709676 556709719
    0x510090809130911190902070507080f030a0e0a14090403031103070c02120601030c2706031a0f160f0c050a11101809111b01062909 58
    0x5281d035001e681481405607801040e0b1140b1022402461400b042415110500c208840a4030804502850800301004201c90a40082240a110b141030f62009580c1d070340480e140c500400c0c0c801c140d40d00301041440c28160f101f41030031940c0b41c0469100a65074030309081141000500203a040c025041d0500080616020381c124950104003142000e54a10f04501c0041000240e43c0342241b00300c030041214a88401d000441505807a0441702e072015091409480e01e914503042000e010340b1900e201404117441a5510460300114010014000405c0310043e1255500000400350f66041d02c11380d042c01f40c41c0000c002d030b04207a1151814801415034544070103079124094448010800c3c4192092001000500a407034040a041035400d03020040c603041041d00c07107120128040c1e0b0a101240b0041010f006a600b00e0015241c024591070318201a400d45150080455030032403a050707444400401c9404014400c40600300000c01c0250030203c0b85003840407451088649040c401c1e030310846000420742405 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 556712176 1250 556710926 556710937
    0x10f030905010e060705190503060906091017010507030501080d2705060d02072306071409060a02010c020f0313090b060909010312030534050c191e05100908 69
    0x400c503076245c030b050640101540c1c85041c40030140300d0b40c0e06801d0b401e00d000d40152802018001c0c01c0500c1e82d0f407050240034590600412a94000031580300c0041d07494122040812b07260814000071030300d0302c1c0031100907068540c1070340160440d80c07003120440b514541c002010704122055425002d90398114880d0300d61460401c0d0807655022900145100900c000c55000308030452080340861620840d00030f60420085500d003080b4002d812010000b210148200c180740204050003c0c1c180c203000310440031401d650000030411026030340d280d250151442d01000003070440500d5200540c038100b107440d0304900c1c1080d03600c15000c1070350300e03440740c00c902e641e80354156101074030094010744996a41c0d090172030182543d0902000805d188c80041081010154884a00e110440205081046141c03061140800c8154601d0080181c2480000300008045c03140d035001840c403100300c000f006c0103070030700a440300000c41c0d0000a006d074440e1140c000400c00b0451100900360800002010070160501403a10f1240c2e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 556713426 1250 556712176 556712201
    0x1012090516090e0c0406030b010b090607120c1b050109030308060f0319060506150306010e03010b030f0706180602070b0307030e121b070e010b090406031b061409010f03090501 77
    0x22000c0855502c03900d601941980a81034100d520703000044062004843c140d000c050520131080005001c1002c24000900c100340303024051519001454a54080240350310600600040d500301c07140d400e102d04040c1c80c0101e494540c2202c0b058038603013800a84030308060b100003010702030038000280c0745036558030410300265000740603511811003488140786828420b0324102d51161a01c0040756207810701014510303054024009103440c548800005580d0b4400407a203841c2c0c190340b0344c14401041e840078840803010781d281d40010441d0303904002c0050440000540007009401d04110108601750b8001031a000303c5a40b4030401da581d49510302e045000e060101d40c1001f1500c02c100c4042d0018100c60028580c05245281a0052044c0410b06646a0303107640f046294a00e034100c01031001c450f0100041560a100500c001102a541e40c1c400ba082c1581c04009140407080728000c2100c0c90300100c450401c02c00702d034009494003140c1400640401c40c8a0000010556500146420850300b5407100b00c90103032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 556714676 1250 556713426 556713463
    0x9021807020d0f1404060305090a02040908130e2e08011505120f07180209121e070317070311030d050105100302070b06040509070e0c09090610120905 66
    0x800032006503455099060040003e4200070305540194130a440300650090a802903a180a28152080f4080d000203086407050340182ca0043d8016a01c41c400c2c00c0c1c1085c850146140c8500300e03021003104001090348000c5280400c0c400304840c1d100c2038141800c4040030000c2c01584044001c40d8000184001d403c540c4680d86003065407040308182c1c1c1c681c0421100212100400c0d80f0402d140309841e034004d980507042e5540009000e000c0143e046103a0030020817000fa00509090b00003000503050841070354510110303000074261654078441c0301d040c403803110100f00081282a02d15916045451340003007c0d031401140c08600f100401d8880c848011030408440200c80d1919446ca0b5480020300080c45264824802c0481400203140240240c03842c0c950040002405981c138076080c807001e01001484070103140a00e8170081088200c1d170038518041c6105041da81c0d150340c08601440007010003c0c011906c5041130b407801c3c0b00442d5101c113860b250410302c0341003c0f0700d8121a2400b54a132a80d05080d2540404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 556715926 1250 556714676 556714681
    0x207020316150c121101021317100902060f070318090c0915020705010e04020d020a170c16120c060507050703090b031006180e0a1a040b0310090218 65
    0x400c1c40c5810080d141c0110032824016140d05094888002c500d80007044461410030002040740540c1c204100c5004881c000340c83c00040716441d2020440682100c4024039421113210b000c0501040941d500800b154000c000011181d000501903018000c448418070360001640b0342090303c5075880ca01141c155040c4110019114140c0002030502150000c00040740024000f8840d00c0c0c0581a10600c0c4150b005441d10b1410301c401100c0999804009a40180ccc08100e11544070015200034403004444d80d94601d0524410440001c2036500640850300318034060007a11501070700300e02c042d040f140d48512000d031404150501070751b400400000260140b40f60404000c98550840c0080549601c240d4460358010384906500760340b40016110409040f456800522080380681d05480c00000a03134140d01d500d81d650071003182c2c0381da0210f5134131114035126008000003104d81141400d05000c1114284010103400e00480c0e990603010345003030300711511000000259118a00058034154103025107080d10b2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 556717176 1250 556715926 556715953
    0x160c0b04081210050f030604120e030c09161d0609040f090507060504140102061b07030903080c100b01110d031d010f022503020a080304170703120501050604052202070203 75
    0x1d2000b0310a13540900f0001c0700044080c600822114401d40e40070b40e0f010300c03951140408541c20307004203c40c20b40600c10081c04046035900c464510b4400d00c4100c00100c00c400f100c510003801070703501e410501459107040445a88070f90341e10082e140e8246013500c0000e0136840c50f01151000d004101d02c0500030340210000415156480001041513b0f0300104001800c0000e0004a0307680800700c80ca0701491038041d10f40d03000d0200d4400240200c40c041d292444080d40c49031a80c0d8a03e40c402007291003141d02500c02c0c002400c0490103202480c00007400c161001214007808107864520580b031110805958a01110a500341c210410010040f03e00081200c0d100f03401d145402580130703c004c01c5100008440c0e80204504002104c1109589907001d0400703a001c44e952405940c00c050011100303881c881581801301550600030300740d454080e80d200000c40d151308100030100c03030060300002e014240802050003241c40740361403541d151015039041d030080c0b4401d6075050024019410020341c540105220b40548 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 556718426 1250 556717176 556717201
    0x9090302010c0810050612040206071416050d052d16030209090601030c061805100807170603073b040507080106050907050703020a081b06160c0b040812 67
    0x8242c00d50701c800e1069150036480051104280c0300751079104504202415640d4101d848640d0054409807005042c4500c9646800d00400c2c1d502c0d088642d5402031080d05045402038080d200245030a0310107034200c2e1001d0b102c4d02c0d12036002c0c50400c4c2c041442c4183da400000da80300882d840a0750003000b03a481c25840003856004d0f103262440182c2c400c01e0000003088856801140d801d0480780d0116445503003500d402d00540d040c10001d0803400d030125007000002031588400344d40d005c04024a0769580800e10b070103400640007072941088000d45007000c00c200030036034a00040c520182d6030821440e0540d480c00002c01c00c01c260351040b0301c1d40d449410700140e491103130071204814050382c801c5054810603519490403500b2a5542d1007243c0d441408407001c00d50300c074000e038001c04166009105036106c2d025580c5070104294000742846141004a85d0301350340c07403181442450381200f12100ca00580050842c0000e080d0041190090240c000c3d070740200701001440b100304d070043d01c0d0070000000795140983d0355094 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 556719676 1250 556718426 556718441
    0x601090b0a0e0108010f0f031e0506010303080603010e0f06071103130e011a0702030c0607020d3c0209040201050a210218031f1107060e0a02040e060103080307030b0105040909030201 80
    0x8540740a0000c107220306c01ca2107102c15100d84101078480a85151151645228224034000c05040103180c0030300403903402d000b514003940c008c1e21811403e0400d40241421580301820340c45d0660001c05030000358a001062032a000910b51601d40c80c615101d485550451245001d8000819240040081d10306900e9102904840600e080e818040003801c5d02c603056880b480c0740081d4103412290300c840840ca02103010f082d00d0340c0003800580c1205d41994a602130030003180354544840d0054411a17580a4100c0c1c04d03801c40c9421b50300c503005c0981071079020425a243c090070090500c0400b089007290503224840800c401c20600c2c1030506514142203640e00203620201c03901a48081d80c501c10f01c4d56040000b602207021550550010142c0b4a118090004028003541c0d14240c00302004903101080f00c0340600701401a8000140242c5807a03441000f01f02ca00e9110004070a802a40c010030108040c00c0580340d10030000d007004a0b1000d00f01f001200c5a00c15508a1040c0c40e203089204414180e05610408 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 556720926 1250 556719676 556719679
    0x40b0d0507051503071b08070b040605010e090d0801180212070c051c050702040b03010609021b150606121e0403080f01050111031c020904090b091218090601090b0a0e 73
    0x40103207541003c80b03030385100c00ca410174045008941d200749034182200c1100030180c06012854101102a43c0796194044107a409942c1c2c1500c43e001480101d81e038648003608466000000d101004e005a00541a1792051085065044114192648940341a0115401a16018000a058a00700e8009040c5004800050f41c0380d114540c492402080d490a044103d404961100f03130500b0a95400c00c00a0868007400329019502d0307401c002141c5010340003034003413010300e00391500c0d0200485035040e14018021140200d08a466000d0002d5078492004690400ca0034020740341450707407060303c203200c6504041500b0703c100200300100424150300a01c5c40d80a94140c1010680503640d44004481c00c140103000300070b8903001084142244c852003003a0440403000703100b015042280e10070001c1c0484004000030b40346032822404001d991103003030141c05c0303600841044c00c3c0d041590142c0103181c0800d02500b5580282001d0010920680c050018900107044603031901c0da0325109003200401c03000030780c0c5509 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 556722176 1250 556720926 556720939
    0x302070e06010804020d0f061103010801021c0203010b0f07080c190b07020a02060307050d060807140108070305130b15091602070b1608091c0302010203011d160509040b0d050705 78
    0x10318079610400d940d90040c2c1d0001e0a82c046491b90380c032407070070400d00002d0031107000740d0f0745c00d02140120b4040081d50080441000050b1105414048031840102081c420103804c0e10400042c0714908268090715211412040e48035160040c9151080c1684609241c54503079201c1c0c41d4422100d6040d500301c0e403803120f02c030384418402916030860690762400c103594025031020051001640b030341d20540140890035403c0e01c0120714165609034240c180340380760300044007058002c25540050750300714080503049406842d0800c003030305e41a40e22240c02d41c21040020018200103022502c50810110326020721140181507a265051090740e03140c0012496000d18090f004011001a40510840c20746030940c0ba040d4802818240039903401155a1021064551003113240300302d001030302683c025804000303101b50001030340d81d41440100d0040d101040395103582c10303a17180208000403c079010905920b4101d814416220303a21400040c000c1d00d003082c1c0040e000ba080038041e0051103400120082129805e5908 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 556723426 1250 556722176 556722181
    0x30421211d0d0809012a02091b0d0b0a08030a090314150a090302210403060506040c0f030902040204271103130f020f06030106021e0d020d0318050a0302070e 69
    0x950070088075155081e070303021105007412000b18407000024541e9480500d03280c007040c2c100c1c448a68440009a25100c0f202c9941c0c03c421003103003400706050f40c0084d003102c1c1d240d803440c55a19400301180b04441c01200c21940701c495900b4241c4401c914407003d020340030181c0c0c0e19540d009000034511782942c4030030703039041100040c00c0320280740204607000d0f691100044c100c0607640b402c00e02d101034070085004074114440c6801c2c0c003840300c03c240c0240364200485500540d90b24070318280202514070103090103118500d0403084580c2130b50407150404e0b0841325404c2c0030030030a500c0e0001074004d01030b0b81c1c8540054a8000c1d010b04400840c440808031600c0e00100c02c000f4424801d00002d61030100300d54405250260f0242034000c51b1642d0100760340588000c02e0110020148804030b21150420b034490005607021520407015800d03841d44000421440b2001000b50200840009558160b81050f000074140e9400d54040c8407003280c880748000359000011600403090500d802583c070300c818410103201c100613101 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 556724676 1250 556723426 556723457
    0x20a051209060403060b0d05031b01060501140a080702150a060302040f05010b07380403030c0e01051806040f06020303060102100e060109020a031b08010f0f030503042121 75
    0x1075a070aa00d000d0010b50409045540c0d850061140c4e012007030744900b05c40300b00c2c030000e44100000c00c50300f07032615102c084400f030b18420745080d1445600458140800100e10a8007007100109881d2900c02a141035221a22440300a9090030001c125070190740301312604111095005800c1802180c1c801d079801c0145000400700c400c211842070281d0420b02c40c04124281c040303100110041507285440052800c03421400e84030450000300c288440741081d0f0190104418143c061180700512a01030400b075649182c0440002c2242c41000c00400345041006600000390325102c081d10050a220000201d00548842d0041e41c5c13a001150428014800c56807420341e25442d500441d49841e0024004003400c1c3d0074404400040c0d0800c204c030300200340d80c07881c07001c51b9003d095150301080410b68a4415941d4101145140c2408a50300855442150b405040001440000c100e0b000c0307580d0042940c101c480642075207c1c000301c0108002d00b41c3d1040c00100800c01600c0c0300c007221000c0d640d0320b40600d001c2c02d801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 556725926 1250 556724676 556724713
    0x12091e050303090d1a1009060806150405100302031f0e07120609020114030a050f01060f0203041a070c060509030115060c0303050c090a080a051902030a030e1906020a05 74
    0x1640c1e40640060104009504051403950704261003604620340e904184000320714824030458031111100d094590401030b5034002c0c4107410250010741c01504a40c6002c0031408180922110060b00995039040050000710119422501540c2e008080e81c441c4801614005030f22001c0001541c5050b18007102951600c02c0003e03003a04641c500003000c00400d50319151503000b801400e100ba8140700640d03c1c1f005410020000070742c03040246070310000e41d81c20040d04441c00b51384160011424458011118090304d0b4000043d0303001c4a449410102c011041a03c4a1819000c0c040c0001d200400c40d03400807405603001805088180780550080018041512003540045003074414940418a511403e4012901c2a0804c1c1c0d030082109250614000210000c40c990100507404200907030002d800290400c0f806001c650380ca2030140c0d0f84013a400c10140c0000e0f80310414101d000301030000e12014181d480c1c44015064011141200c818103c899480f032029490b6440c500d821500c40c0207a400e88036814205a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 556727176 1250 556725926 556725929
    0x6081b010c0b010b030c0f03071106090c1507020f030f030a0305100501122a030e10060f050d0302010f02131e080d11070b04030516230409030c12091e 66
    0x102c051855929045111030594405030028489500410101c80e80d000f1000043d40210050360724482203140b0f0980325814180080d00241c1260007036a00d503007503527994405000003400da800c00c0580d21080d900c00200383c80400c54482e50540142c5140c4103142c48080040c06006109480500030b03070707072000c1380d19016400c0c502502e0701094002c0c42e0302c103040c0c22584c040c2d0340d201117002160155502012a0ba021b0300400003030000060340716003108518440074054a00c42400790712007440140e0a02e001300c8042c0074140550340c01b465180324039100b03240c030075000024074140040045682e100c0c18003860b88000355034015680003190381002c0c0340201c003107100c10b10300f01c450b000b0203842500c10049007160690580400d0788064410340c4c101080c0c02031450300a000440c45032000f440300c101a1951000502806d030300c0000c184903003070a241142d0f403200030401103d84045070000751090301031800352590400c0910140c031070020002007401094003d041d101c1520310b51070075500c10011000004a000b0003070b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 556728426 1250 556727176 556727183
    0x6150a0b0f0d09323705011509060f030204113f04030801050f010c021203040e06030f0a030c02180a0c12230601091a03060109141c0c080106081b010c 66
    0x4490907007040740680b5070003194245178280078a035560800221402c80ca180c0300c01070f00d040e5924400640b80407a03d1070034100134124148140406c61900019940300f010b944006802280c45156010985e2040404c940703404102000c190568242d0901d001c26024048610f008490310719080d244041d43c0341c80510740302c1d95045c0d841c0f40c06d6a00704801d0164060310028401d05103d88800683d005980b120100c040604e070b44802143c5403403400d0148841590013a0110b030203504880901c082c0b00e200469407000c00b98260404922a1000e40b01044040240000d03500d8040307030b10802c1c400305401c60b03002403814040d10303540c81d044141c00390310150460310003404a41501b68140700c2a02e1500428115032b034414814144403140c581d03594450a1aa4209a0400b503076080010412055680003911940540145804182490641c101003140c40000d07007904166611032200c40d20401110b801c0001c090309015009002e0344ad600c06540c1e0b520f40c6c610403c500a05040d2503084143e510445514608542 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 556729676 1250 556728426 556728433
    0x10f0c14031602031903020d0c111005150d11090703020c07031e0206220e011a0309011e0903030b0603060603060105070305070519030206150a0b0f0d0932 68
    0x42d5030380d2416190440741c200e98154002132103000c214440d0346108109183c01d44d01e000d6503e10000d407071501103800004581c0c0a0084610000466507400140a0307081c103881c4800088030f031182c407260141c02c100407280a51102c41d0061035820820400c00810303103ca802d81d41443c0c0350300c407440f080c1c05071302500c0402a9180d1016404201042c607021900e11400d407030758850f081240254010550035885444038603506600d401501440c0101040b140008003a8840c103907400d541000c0c0b00200b00f12110644800e1901c0120104041c100b082d03105040000d5056144c503041e0402601c40405000113082c2600800e02d02110b40340c00d810841e04580c8250320050000c0d140d41e1319100151142e4003d020160100300041c061440060070811144803200038507020341140e030b80c06250091404c03100401c5280e040308c0600040c9000d4860400c140f064130741400146840303c0d000c6660900c40c2c0202060f40303d2050a00047d032040c05511600e034105401d000600e0350000d03188519101d10454004030880441d031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 556730926 1250 556729676 556729681
    0x408070302101b180b03010f031e0c090911090a0c110a0b0f07110102070605180c0d1502070503031006020c06030906130f02060a0e090702070b03040204090c0506030405010f0c1403 79
    0x1d10031013140e03090100440180d00f000c0d442d21403204042c0c00982105c4244681300505001340324a4001508050803031031490303c200e0f59141c0e6517014121480c492400c00c161075031001e5081210303255406100c000701070600411441c0004075070000c0d018016004c008646025040303455080e02040c042c6404ea00282c81180a40314030030250341040e0010030042c20003541e00c0c01a402400c0c01e0009240c507074021400410703e800c280340170b140f0300c03d6185480c1156600002076048036450300e2010461160f00031000302094410524804040c2c4213030b000051490000100300412148084400c00a5503250385c21524542e000c80c0c280720444c032041d18000041d40c004000145001d03011902c90000c2c511806026030a0100c540c046413441e04900703040c0d400304d6451600d0103250f0a019407141c0c2c1c4054103200409000386082031200e141e100250010780242e4035105550b0074020328400010040070033810303055803468103041c114001c003c1c0d0842e040301c0501780300f050a241c0d8881d0391040c0c1070666510805140d038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 556732176 1250 556730926 556730981
    0x11b0305011406040e07051612020d0c050a0204090203010f090c0e0105060406080a0c0201020405040911120303071710030212030a14041a2d07170a08041217040807030210 75
    0x407400400c5107040200402a103007540064040c4448e80702e00c200d40666800310b0031308019040040007213032035007041022944d610114000044c8004400d0701a0740000c0e070b115141c0003181c094100480c001482d01c2c00c21311000101315200e06007404654006042e44840e90729001044003502c60f92003450001520200803135820410355000d541c5041c251f000040c6015610000314064954194003901c0c1c05180e0303850040340e410403a0200005081c00409103283d49841d04001d84007a0800724081d10410422000603407400c102d0078840051500204501b03140c182c46502d15aa2343c2c4a05201e00005410b000c503c5403c0d43c006082d101601c1d600c0840031505e076507907210b054894001a4403115626070048810862901031541c084502d904107214550380c800ea41055458921001360440c4007200410007034040c07076407013440031790041d0340310200e9400100c1c280d104644183c1c0c05e84031a610000380c03106110401000724001c2c54490b1098080d101c14039900e40e41c01c0c003155807450300d040ca03180d0f4030042c0f407028 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 556733426 1250 556732176 556732199
    0x2d04020d0b0c04050a15030c020d140d0e01020c06011e050f121510170303010302031009020a0e160f0e01120203101e0611030a1409010908011b030501140604 69
    0x2d4408040300d0a1554400014420407595801000c5003e00349401403c00e60b41030181d01c804088a0000340001f082c1039400034102409241c0186c501000429224050f1005030092100c6591020081d521201569207043c1c03140c0080c416002c8441010060808000c140c0c8003000c1100c01c0249000c0071602c40c0024001d81d15202c0d48440540d0282c401d0300c2e086400018019400b402101c424900140d04120300782c1d2080709142a210b0043d4418401000181c0d800200281c0d648089000803c41000710b1010030f62210090b000a54424000020401c0c01400d604180c80c03603007480e990703801501440e40702c1581d0602c60038200034005100301186042c0080a500210b2300f0025180710410307015030b100fa43c1401505850720080200003410002c0004d40e07445030b009012601550040d41ca40004410060400701002a50700f481e55404106506180c0c000d4440400604813480240030030041a440d031000002055000d00203e45400700118484d10420a40c0e06607101c090001d41c549805c00920005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 556734676 1250 556733426 556733431
    0xb0108011508210706090b092a1509090a0207020906090103020d0f05031308031902030901051902010b04050c070c060305070c021311041517061c03030906052d04020d0b 74
    0x43c441c4104404000a80548140a50f981c0038083d003405034107080c000315081100c6401d518010101030090354580849040d2070000d840c2c0101c50810b407445803920000700070301903000070031341c03100302481041843c0305260018018580300701d584061035900d030410021020000c5c080690402541e5441d000003c10308507010180382c0c01101103a0520140c1c090701d0030382c0c40440e00040501c0d000411041002c082c8401c00d44002003d40c005181054102d50008140e030050b0743c5200003880c512508107103094001c1d031006030f62200140040c44a498026040712540e0300182d405c603030f0030203810800111184a40b04540c041c1106590303140c182d44a98007000b9482000752a80c080c40c0e5500c86034042000164401807000303048618460a1010840b80c029002e186000c81c0814010a180200001e65807000c0c400c4d6205292200402c082141d2410704400407e0b450000070021071500d0305202051106c0030342c12400c0e1440c0c02440104181001d0610b08000c0c05a07402074208030305090400005222510256 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 556735926 1250 556734676 556734733
    0xe1609050a06181a06030103050d05130b030703020304020f01090e130503090a060f021b0d0f1e060e1020092419020d02060406021c090b0108011508 65
    0x203a803079100d42030064251a0000e45480d0140d40da130007010451058108440d40080403580e90342150b141d40c0702c050f03da40107240742d0800c00c04002031000900c0110120310707000c1c1c40c52541d007039182d180c0074401070001e60040c1c41c00d900c50520034146035a103620444669003a100d04006140b110780756951000c6485442e910304503850b020a004241c065184c160058000b0b050f250340f05030001a08503c0a4280100300700d01e01c081000e1201001c8180e260107400c4004c0c02d030700078828003c9001c47d0600d0f1410f02000e44192484080f20300c03005007488100c1d00003990040780c1e8020742d44115101070000f01210a0661030003810034101caa0390700001d9141000c1c0c003a08002070552045500302913250f00040340003180711303a0ba45001089201200c1a065400c055500d01400100340421940c100a035842100404c01805107400090300c01c1c500e04054001810001c4034902030103039004c0ba1400310110329090251411310761070443e030711400e800d01101050442d105900501400c10070041c0180307905050100f80f1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 556737176 1250 556735926 556735931
    0x140604170a020f15060a0506030403140901030b1c02011e02062202090703020d0b120a06151205011e0b0d0f020d0209090d0305010506190c17030f07030e1609050a 71
    0x191542e03000744858140713403410380311007601850008204040c160300c50f082180105424010040042d411807080004c020700d140b042500e50b90b00a004801502070300c203030150001038001d403090341d42c02c2501c00646818400d8842141486000d5201715060840030300318030040c1d1115000c19108041070141d0140384080a41d95100e4006a4010a00f030000c142c80b00c200080c0e0010b02410f074424240700716110000c0403960314100010704402070f9603840100070040c00721503580c0444581241c511501c44020a00303036000c040c2d848168106603008007a110f0200c8010081955500d59040c1d06110ba100107c00c002c00d07200000c1116160349500c0c2010400403a00000c2d0518a000542d5071030002d54032034101d05006004100c1200780081c00d50f501a88002e01074030080c41301c541c203042690100d028101c1d542c43c0c801280d0b030860500d80452809140700c0f03000c0c400004144000c50b600310309000d1180c0100d171000d100680210b503045540d40e07030543d03061100350812001030003554482e030807081e000705840102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 556738426 1250 556737176 556737193
    0x3040b0f2e1e0f080d08040206031f08010914070501020d2712060b10050301090e01140c0405181014030a02040f05060a060c150207031403040c03140604170a02 70
    0x8500c1c2c2e64120480c2100b049070100c02c2014090310041c41c1d019001000c080c050f0304401d404003500100014100074070644000c40080e415001c0303081082a14000b4840c81d400c0c4036514402075008000041e400e4401e10b80120a1103640800040d150040303c0041c0d0060541c11810101142c8001002d501d0203000c5180701c4182c82c0e840640b483c500003411540c041c4d080d4582851402c00c0817103000c05150790040b29214030b00f6100c0303a00842980d0460740b0302c0c000400c0041030f9617050b0340104650007106c1d4000d0500003e01c9030205e07c86020b442070b204182d0b08000c07000140524000c00880460700c00b8030104842d88181b0460320342e07a412044610010381140c1140b410f42c1d000038280e0303504582d420b40039695402000721a00d0540480390040409052501c148050b90b01ea080018103840301118055400044c40800c2510581c10a40101d090404164403402d01d40f80051504509100549200040100d103001032030000c80c05600881e403207000b41d00c801ea46031101b40b01341d030000260b86041d809400352 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 556739676 1250 556738426 556738439
    0x70609090f14012c0103031701140a1e030c030804171c031505030d0c03020c100e1005090d0f0308160c0b040c050d050f0d03020a050406050906091503040b0f2e 70
    0x441c01b86200352984481010300f20341d20042524168407500c00d480815021400303d4559051100c1614400f44074090b10000001c0210b40748000e5030700040402810aa0010a10641d14003070000d5440c40720030092030025502c400741d503403c0c1c070420703030740005506107070341c040b490700940c020303a0f2984e80301840544613661580024100806021580041001c0380309241c101070b814010018901c404540c00950303121601001425807054803071450048800c09201583c01c0c0c0288152135207600010800c4405815511307141601d0844c15108802140c0c0034008600104e4088200e020311560903500c400c11486591141050181c0c0070b441960310007003416000c01c0d1911018041441c46000d04006c0850404040000d0307d400810184c102c00c0510502a110804c0c0d03106084070700315092480d00307545800c00c0ca03001071110f100b00d42806a12841422900d0b941180c0000514804c40c0111049030243d65030701c404880c605411101e45019141501518040151101d1070390242102045050411a1a0700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 556740926 1250 556739676 556739759
    0x608060f010302131404060b0304030206090d1805040f02130305100501080c0f060d0603172107020726010c0f030507080105031c030e0d090812070b0c090d05070609090f1401 76
    0x26410b50043c0c103c241007043b511070811540c2d51f6a040c903e46220b00003801080541131860a003da18415511441140003003130b4650140c80c1c040c1402e00d04072520b26900d00d8015a5141000794000c845401c210001880b560040b4604020140180a1490081341402040130300c0d80046e01e0f241040b0782c2e501c0d003c00072030134003643c4607414070140301c0c01e43d6030b0f001510100c0303101003103994140c0c501140344042185241e070100d40302c400c4610b001d10440090303181d0f42c6e82194103074422024000303039803030f080d85004016402460a449210383e0346040000e0703160032000301c035540801d004068160b4040701d42045001c041040800400005250014080684120141c24100c02203a0040051072440050101c441c4c10301070800d501911840341031034900150343d8241c41e60030041a8041c211004242849191202119041a00c1d030101c15980c0071500c3c1d00001c0d01e4941c013405050030a91030890b82e112055036511480b6212118000c204149030b180200b80c60035001100c0b41e4011030700100c0560f001c4007140e207 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 556742176 1250 556740926 556740931
    0x20a020108010b0f400801150b0a1b080a030203010e0106260901060b07050c0f01110a020d03110f1b010311070809012601090f06060806090a11040608060f010302131404060b03 77
    0x2645c240000701e242c004490b080d40c00360315021a240940c41b5081122655a000300c5900c0c1b07030107040078172034940111544900d062411002401e81305002500718886035156000314103a607402c1070001c2c09a6210002103503640e002103581115500d01d01028100300c0d46e143c416a501ca50b240700045249511080001d085030000f207002c91b0180d0000251840524096031038400403202841d196544100304581556103034480329029006441c0d203101e8201341441401c4029071407000c00c0488e100911b03410a090350b00c00d501c13501210314901e4861280c0180d84a402103801404661100e00d041c004030351109641c9a115140c16410311401c280038040084102a070707008946404542d0441962404a200e001d4444a401c0100b4840c13518009100c82c903005140250082c2e800d0b5007801c81c0d0780d11031620400070801b03003c24018044010400050080c1e10030740c2d4500c560310a617407404009010300010360030790149031091640080b4101c01800f540707007801841c035a5003900800204805d607071450080c2c40d0340e009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 556743426 1250 556742176 556742287
    0x140c0102070c05090108030906030c0f0405100e03070533092110111b010b0402040f050a080f07051003090b0a0f1406060307030b1f020a020108010b0f 66
    0x881002a450600211801004506c0c05185002140000107609201c001c022800040001c0f48032805105103205031005010041c04100c2a19060100075082030311101e8524030900c110b54011605040c001c001c0001c000558003000c103082c00d40140d142100754000405006c228041c08942c0c0315a503600b01d1418129500c10401c055960a000c900e4107100311503009a25190070110f01c1c5240d4003654044840942138601d8482200900c0400c440c00344c81d910202039405800802d011521011844882048680854240d00d03115619010f55403a5100d10140e40856000f4010800840c1011650800d00360500d10340012406141e0b43ea41d100d0010580783d4030f205036520783e001c0880310b8040c403986c00039411008980840740f03000000180d503844028200800c1589034040c81c10203460399095040c5400038140131079550518204020360722105113409038001500784d800001c02c1c907140c400b150410540c4c50130b06440d0070040d02004140c1400c030610410081280c034595118509591043c81e440031070f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 556744676 1250 556743426 556743443
    0x90406020703020d021605060901030b04092015030619031416090e100c0314160e1e0d0807080d050109060807140f030f030f09180402060307140c010207 67
    0x290500031310b01075003140300b441550701c0401c185401c0b2001030940011642c0c05c4030f403150303981801d1004a014020b15088070790811700300080303401000702020740007036602001c0c241820302c1c1c540741c000c00480300444404103449460400120307010b400c00790303400320360340a9800f00703040c100380c0d40c2d501d83c03040001200d16038119400c140b031141140c001800c4100014481100140040d03480108016221140c22100041e4140d4a5401920450081d000ba90804104645084117450030843c507520800c2c1000e25035000504040e60140d4a1501d5000c451995817601d0074458034010500c2805030030726900d907013650010300500c070881c0040d12010040c140142c9400d00804c2035454041c030442510903d0300580d445400c13902c818428107603208c0c492034508800320b480303d46d206d409402090a044c00405090100e000010b18a0035003c07c180003044418001da41ca80445d11591032a0030b8641c0d07050b07030000e500178000c1003c214654842c110115401d18010001490720b25100380711402ca0b40201c0e0102c58484 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 556745926 1250 556744676 556744687
    0x1090f0e0303090c09060607150c3011032e080a050f010c0c1518060e011a041a190f03050706090801050c1b010b0a0602070801060f080d120603080310080f0a021507050c09040602 78
    0x14560033145074003110301110a085040c10070408084c040c6001c00c2d941000e402c0c101e0101c00540300f09944006066a4050340c6060044c4d0400540b11039001c000c0401030b6080c20f180315082445640c5403d0010b0b0410048c0070a1010304c0d941c10040c0802a480d510201010300005012030882e100b03040c21800043c0000880340325078240903010205009015101301e2034202e07042030300088000080603c2c4030132a580c10000503c207410b90360400181d00628a000c04403900401006000140c003070a0f19441e03290314078155603404509080e00d00807207a0303d101601c1405601d000d0745104521038107104120001150802d03079440881d01e0510319134005401a801440c080024034405c0c8503901c0540354109401a0050030040441e50b58007040386044200003c2c140f4405001c6903139848600a03690203075405980707082a0321b0118403055a8040c40c1028041ea11490a1048002a4680e0501d6001c0c101110008460044040e241c205034400d490702c0c01010360030390584da611090a8400c0744105001600c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 556747176 1250 556745926 556746017
    0x1a0a0605040518071a0d09050d02060903130e18060907090b01030e151807090c0f02030a0e010509030102090406091b021501090f0e0303090c09060607150c 68
    0x2148050300c60402c000e80903402010f00c240108002c400d40d220041090007810900c074901c400c03803050b1925803000034034107060702d0100040400c1e110010440c542c200c8203a0b80345d007900281c0f07a1007060411204079211620800c13005070041240c5a0182c1c00014511114120302c00440c2010801c90700403010360442801408151101c0c820010b902200f803904001075441e50070030b5584c0340501840a403808504c40c0001d80f1001c500f0045900f40c1c0c07442d2055901c1c0e1b0395100000070103812108804c601041800545aa00d40e200100341da8140840756210700703405070b12000644e55940a81c03007181c0c055400b0404103045465a00440000740806100012003041c044040e500c0131660813062011034000b8200c00360f10405900e6001d0548004100000f003205070704034000010b1081d50346500542c040402003001441002c18a00c0110b1070603903803114240d4848080144602ca41d110041080b02d040c83c815031001b425030b0007052600341600f0844000e0700c20182809200340045003800c0503a08031140c50500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 556748426 1250 556747176 556747181
    0x1b0c03080a0f020c0c0a0b0f070b270a020306070809030313060e070f090e0f100c021c080603060106020d02210c2a0102120a0e0a0b1c060506251a0a060504 68
    0x2e159980031181490034241e00c0b126103209000015000b40f60020205070100e2003600d003050f000340050484140c54421540b02f90706c600d01c1c4001030344a80506d50002d6807950043c00b0551151034024040d62a56a40c00001120441e6481c4161181d59a4560500f4040010840a00508120094803c06030300c1c029844080e941c900d00042c809800c01d20400346c5008001541d00580441d5480c0071030f2103944208120f1401070058001c25400510305580151590403101c924050601503060b0358003680c07941020380c1e48820a24030340c0d0040e80103c07403a000991400c54141004081c00070003600d480c03056a9200d28211a44414120028045100c4914401c190501e0300100e0000c1c0060003c1c01d50051041500b8010984071078180400281c04041c0c0d65074052441c0060321440c07223040d8032940060500d014408981031905600c80c5004404117507803501c0c806075201c01401c00340b0300c00c0c94403420b481c1710414507005004070381d014038003030521094050300c10505200b00c0c88100c00207802d61408041105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 556749676 1250 556748426 556748429
    0x60c0c0c0d0209070c030c02041b080702070e0619030c081e0604080306012105071d0415062609151e010b0903030d021b011b0c03080a0f020c0c0a 64
    0x218100240018005843d4110200d600020500f4000035a118509003960134080580000b07510034901005055800741c0034540c01c0411610f0b83c4d0360740d41139031640403d980c1e441541c0a81c041095014000a51914003c180700c40c1803044940360001c01550303952600c6441055400451075070304828034070303130500c602c018140d500b2014000c0244110704258460007200d00c009044141000700c410091000744a46084082401000048c204168a00042d0003040e078084100742c800000703940c0880a251f490300d8001c0540b2100daa00524000ea460040d0540300140c4031802d04048108084400150b01103c4a109129120303030300103020b50410301c45032145a19002000329003040700000c60708124a400340542415036102544441c0d940c1c4405000030728600415100b403ca482c0002641740707601c10a0b480a100000e41c0d2402401800742d4041d10390752070300c054840e14000a003002001c0001c00c0c0306400480d0041d1078100005410380103c554081a60320028441010f0f600c6004110400d0400720350900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 556750926 1250 556749676 556749679
    0x1d030301030804050415081606110a0203030f070c0e07020a050d0318060e070b0d060e071407061a06040308190801050f1228120f0e040c0c05060c0c0c 66
    0x1451503041d0b68a400b42401140100c0b8003440e901e048903842010458000009040c10701c0859000c030040107195113001c0510302170040003444030750b900c0f01c9109001070301039504c40d8000e0107582840c510310003011082c2c220315020340d40000c0c0420300141082298038407901980403513000c1c202103002d6041940c68101450710487c100f40c90320002c0901540b05181205c14036030320800c0460301900120b445840c0250740d410000c01c100001800403d01c0f2119032090084410000d80c04200d5541e0710002c1c2c6c0e44900c58011130f00c1c07201d402c1040700001001d5500c548000002c00780c0d030042099640e400314505030400d0300704952110340003030f000c0d03604080c21250244980161034607417410760410000c2002121941d1160340100c0245841e01c40740703003060152060a541e4010020354000421180000f82204140d05035001d4024400300880c00e4410068882000c8171030b00c40c809400ca0510a020003031100003900003c00000300c1400000410a0100600038541e00c1a025205c000c2c0b180d00f54244a00c9940c0305 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 556752176 1250 556750926 556750933
    0x61605090108010b0a030e030a02070f08010b010e0d05070803040b250203100c0512070c171e18090723070b0c090a080a1a07080f040213090b09011d 65
    0x5105a039004207034034152040504d04e607448510f000b0080d0301500140d075440e0341034000440d4007540c0d5035001070307030204480c00d4162105605903500101400c0743c0d24144610300003000648451180c2c2071250020506601c96070461321896a2000c0300c500b141c0043d00240c183ca00006481c542c804003000b0382c40c0d02c4481001c008400d8900304e0340000e03070701c0080190740202c25880d01415160700e0b00650a8590802514a000900b03240600c4020301200b41848100c9100064810107412120a0015101c0d101044c4400d2695080c9000b030302445604848840646440440040305a07a2a0b10344814002c0d483c84d00c1e5042c015040c820b0507003500868004403440820b040c0b01d081301281d030701c03281160801c02d000d400741d0369420300d01f003c03807078007003080c0c1041001d842110810b10410021640500c0ca1403062280c402140c1c40700401103c903a0720650b5034400441010000c10702500d00752501d40808001e2500c0007405409035500e1183c1200e007140d6002c0540d6440b03111114405038075140740d00d8070401d42e014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 556753426 1250 556752176 556752187
    0x30601081501021507020307060e0c01090f060c020d022205040b0703020f07060c020f0f06010e070903020f01271d0603030703170c070c03080a120c120209150c061605 73
    0x1e40d91450030b0784800350084c102000ca1a40741c002c2c4211001c2a410110a220344050a07016075692841700b42014006403000c500000c466103064031900589425986804012885408005419410100c1aa0311402100f01591400400503201f109070105050103d100d10b458103001e01c160000820355418140100541e9907500c0d08400ac50b600c00384c3c401000200158850300403464040048150400c0340708400409403608000151541251103103918585d050750742c0c2c002250003c2c1140300c029000401c8504450030341d0702443c0010404042508184a840343c42102c00940f130000740d1000c8030070960643c0c101048054014600d501204c00d070010742c50514103560082004c021402d00b0414400030f60f001c80d01d402602d03400c669110347c100e02d48040040c0c07241400d02545c0d101c0c464241c00321308000c04059004c10f485c01000d1400340c01d42c59501c10310070408000c4d03010703600c04201d46500c5040d45010440382c002c400d0203042000066001070040707242c01d0a164110740c1d0b0321034400041c80400e101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 556754676 1250 556753426 556753429
    0x2112050a05091203090901060c05010c0e01050a390b06040908030c1602040203072715031a0a030308161b020d050c0306070f09090e0c120319050306010815 68
    0x1101e08441c001e40f000c04003080500815030850045041c6198402c034540c00001d030455210b00e103108000d01030b8000704500e0112035010f41e0444c00b2524240e000c00c01c03e101210340e0f940900d040805800c210300a101082d9a10665480601c0741c0a440e0304119244840c80401d01c151601a0ba2340443c040c0c5040056200603103600ca458040104115004100001c0440240782e664500708621a406041552a03082030032000c2c10b5441444031044152960f80c003204c1d100e00199030200100d98144140c7d5145940b402402c4000c2d00600c640407545043d007403113124403070302c0c2c1007641d81c0198000c0c1e0369030700c5c40d007030140e54918455501d01e04801000982024511a08020703021410b42507811902443d80620320301d0202e0a003200d40358402d41c540602d00820601c0c5421540441c4041c20542e01c91292a0b12440c1343da041340c80d4040c1f01d0880303500c01c0303c1144560a0540c484c11602d6100c0d0100c0c1c0c01c0007821840030440fa03196040a8000600100a016007540c104040f1500155206c0c2c01c2c043d5007070b4040 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 556755926 1250 556754676 556754687
    0xf03011d03211003061515030531150b06030406020c1c1704022b020f120309210703060606090512030a21020a21050f13050102042112050a 61
    0x70f00351780e580b4144c48032544000d540f131500415880083e4a18500383d168040d0003000708076141c1c401041140c1c0706c0000ca00c005120020b1031804603d00c40307010245603d440041302203d40031126010f9070b509140300281e668001440c4a148038500150391820407148442c1880030841d640c07440c07030300c1b031800758440c003600540e07507840490485250701f00d030342e8a5000094210015140341d00098021002c3c50100c05122200300801c18001e4030004820f801e1503050002c034000303021040407a5003090044460a1515481da01e10f80100002d603030784070500000306c80c1d080402d65441209d80b035681e614100046034004142500500003240c000550100380c500054482c07041c0e010035400c200d544180c40301e40040303068244051401ca00804c40d110805c1050280844100407c185001440c46500141f9059a406020710402401074501560b440e00380f1030312403900940404498554082c0404211120107500072504030004106a420603011800d004080a24466140c020000b0400c91103082a4001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 556757176 1250 556755926 556755929
    0x1020a030504030f0507210b01061b0206090d06021201080613080a0e040e010e0109050c06071a04030c1a1602060106050301060e04110706090b1008060103020f03011d032110 76
    0x40c4d400791083c2000d1030000e0420550341c000501010103140b034160b94002010709030107024410b000701031150741c840c101940c01e42403900340d080b00c0800b000c4c2200014202240500031120000e056240c0049103680d44000b07980046402d0a0706080b0040100311002041000e15046040d030501814284402c0d11411214801c02c18040240318503050300500580743c43e400202603020700300081103036040c0c44580c940070b028002070540302c900c0340d520940503916000085588150303001405aa241c14a030600c1e5140100050040d42030224522a01c0c010840000058030200380100200d03d50f85003032241d0302e10300040c4006240c00c5500040041c000107070440200c0741076902a0810001d250141130008018000c0b03d0806007500e071000c1841c10820541d50825044244286000e02c090340c0d40c0b04506045801d5440340110f04d41c400c0c4010005402c0881c50b840e044080640040707a441807603061202a62450003042040b0f50000843c88092800301b0355440c48410121440c0c0701c03d05120050710300e0a94117 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 556758426 1250 556757176 556757183
    0x2e030c0f051605060a05010f05030c06041a070b0109140a0b0907031130130b0402040c030b031609380d050714030c0f030607120f020d0506040b01020a03050403 70
    0x144500800504542c0014856032041c1202d1062422101c0301024100a105184134010741e018081303000e10b00880d800710707060809081c80d801c081c5413045104804030350001d010000102000800040345040001a01171300200c04042030000f1101422540a50b0040405204030b1600424811968449100c940c12880505d0003051000801050000b01c0c8035020420114113049031040e000d40c03001c1104600c6204c5401e00e540e00300e81d215521036001404281c0300070690a4480e000500507d007540c800400d19241d854002010300d6004003003840e0000301c55001107803070103110040000442501842d0398801d010b80843c5003904c905000400b103240c1c1f1035290b071081c46401207013200342d886044207003001d1500042207902e0395a441080840c075101072507040e4000d01910328803011505040c0c002a0910310050020031080c3e840324002c4a4401b54a491005000d44980c0841901d00860003e84083c480e00c400c0001c560a0680800c82120080c10610741990090000c540221350050295411244c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 556759676 1250 556758426 556758437
    0x19141e0f010908190c14180c07060606030f1104050303040504020c0c06070b180105071b030e030102180103501314010b0307050613052e030c0f 63
    0x34900010384820640303411100c00c41c442d41007030400fa803140405480e5414000d0880c01d02d030a4654010902c58100d6044040c1c01c86040d03074107890284c030308840840c1d100002604843c20854180c0e98a4250360307455111100003520756107500700803105845000f0078808414001c07441c144c941800300782c803401903106540c4155800300307007440240340c103208a20300d81c000244880d03920300507440c04407144030003a18040c1d030200c1100441010b4000500c02c1e03d000d1800342d114081d840341140a1f140100400d207000301c00f008483c02558020391400d00141c0504680c0048508490498200050446030091602143c8030071425501101d49440c0d00401c4100403001e00442c00107841c0380e91340b240d4200b804505504452401c08119903011309116a590242c4031388402200300412a80841c00e9480c0081d00b0b90707040d0030a00003000340703140c214010702c0c5402404070340d107280b19691000280d402c1611b403841ea0f28a90780e02c80f8212031000c0e480c62003c161400b420100030000c11948010b00c805172002d003440c00e100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 556760926 1250 556759676 556759699
    0x5090c040e03040e1003051002030c072405040b09010b060423150703030204091410060f0c050f0109020f0916031e0c0215070e0f1e19141e 61
    0x200144203c4002e088808107081d0107003098280c1040c03120307862200b55414081c039009008400824001ca90240329a03600c0141840c5840c1c40700306011211000009070041e101e5005445103409000d058403c5000e10000703410791420f80d0f429030945503585981c0f03210701c074100b1051048003030090480311a19031444440c040c0112a501151160b82c508404603030034180402c4010406925400420075503d540701d05000650031301a040c06030b031000365110095005100403d1100c036214001e089003103c004c3c909210801102c2d10340c5030406050b0b00285569075143e586201c10b50030011201c02c0c070f10400340c980355414a4680d0868013840c04081841c0101900e40404400889120459a0445201903810003040041d01c0c1c019551310403c0101c801019034031400511410b018010940d990180a400760703000300c80d9841001100325030b020000050160311101100740751075002d440e130340c810681c15030400d1060a00640c00d00404511403120b210700c080003d100181c200e54481c0c01208130301a9800a143c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 556762176 1250 556760926 556760951
    0x50a030b190603050a0807020f040e0c0d2a05100c08030106030906020f0f0a17060a0e04021f02030d151a09040902090a02091503161b0206071a060405090c04 69
    0x24011540060013074802d440702e0b803041c094200f0050840034802c485519170209c5190a11003514250580b050044e00300600740c0349142404594012014414070b08082e44140c0506e84402e90342008009000580300f449061100d41055255501509030078142642051001e6854568511050080c081095100d4040100300700c0d15070142c0780000000d1404649650085007000f030707175402021031039000804030b03c82c04a810404000c014080e01e400f414042c14141049013244590001401c12604022041106080c9501c1c0110046807513890380e0145503540d0881c454042a0343c944071501e030f040034098a00700540c82e25040000751000e14034003c15280c0c400440040c009281403040a9000103140c0108640c070f115035801040d0b8004100c981071500340201e14218010301044803010342c0800141000403a00340121100c420113a0300c803003002280ca0304c540c003150b03131504200421260079210643c02d1070b10078840300040c2e0b403000301942c0400c8240740041c0c6143c1d650000c1c80c516401035640d00700c4992803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 556763426 1250 556762176 556762181
    0xf05030706050703020306040f0c021b1f200c0d03080604020c060f011e08030313081e030f011409010b03070210240b0a090b0a03060e040318050a030b19 67
    0x5030403941c1000149010b40e00034019510850f881d80c412840c040c112a0340708180e204001d0035113074641c000c1408040009a00900d02da40806450744007200351040401d011401d11201000f0710703a6542c114400309000300d03038007080401c29401c41c102d420510606110351075100c00c404000784c051410460341c0e201c00300824001c0c41548032440d0507009200c01c10240d048201125412142c2c03211091081c840350744041c81030751200c2c0c0500000c2da00b04001007070400c3c410b82c211140c05c034050f0b00054a400e4484070401c1c004140f4100304404240c3c080304121b0090400c005040c0180b00050018089222081c0001e6048005020f0103840c40c41c0400801e51461080001185a091a4104200c01c1910603028070340c4141d0f8a50071001480c041c2ca02050600d811003c0d940228201e80f60803120074180000840300350007001000b810180c1d03e5100060b04038218006502490103a11500d441a1889080301c0c084081504910700801c0c0c980c0d000c00000315200c2da1a6032003410001d0814482000c1d8100c0d201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 556764676 1250 556763426 556763437
    0x30a0908070308151905040515060706050403031b200727110a0906030f200d0f061d04020f0a080601060306060807140a0c060609060305010e060f040f0503 68
    0x40c664001c074003241095040b5041901405035003194289850120041060740001c8a4503900d010f6143d0380200100c2c20190815500210314042054108050f8404035030241c000320703030907109180c860f01480300b8941c062241070144403a00c00105c5281c084050054030080020f00071038401c8681004110415030140301210280c808041542c0740b038140a6405c244017121156900c1581340b4204985945c2c003956070480321090300603100c0d03240442ca4458142c00400040c8201c1500c3c507280d6560300014200c000024803002d00360103120785c40d00b091400c9a804c0b1007040f004946058038040f000e05c40d00030400d4118001d1070701c0c0c1c16002540d41d20740c80820385c00000e00b0051500a8ac3c40d201c0131412050118050781600c0c5195010400c00381d0b5440f00b05c610003000d41c0c6079404240c40c0101c000614003402c005280680640c01c0c030f28225082c030350340c10b0100c600690040340c0c800d03520300050003086030a0003030000540040c8002e20b80c40c102000707620381e02c000103480241507a403201d140c001040300c10f00a840 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 556765926 1250 556764676 556764683
    0x1030908090f01030b0a0602070501031503020906060c030705060f16080411061b03120f09011107082208011d010203042001110109110901080f1b04020c031602010806090c0f030a09 79
    0x10611691a11f010396140103500840340464100300c40c10744203c00781640c0304120b0350010010645600c0d9842402025403201c0210300d000d01040060401090040180e50b0185001c0c200d01900c0740f42c440f41a00070105805181c0701000308100510000c1a02c02a128444613800c44031655070b1f02e48514902c170a04040b4191109500000c00c90901c1d83c00115103591088000c885940c20641c0c500301218221b4100703480d4542d094100740700030380115500e44084c14003d542c4d15289610745e951000384800d031200355030121603986e4544801c19080c100f142c640070341c045105e4000b5070039400c0c0742d50341110132614400c03040e00d003a900c080c80040c1688102a5409c200303116100800c200820342c180400b9070003a000006000e94624800007540c11070001d40c8800440d40740b8081c2c0075507a00c880c0540b048402036541c280d8896002c1c04200d240c943c0a00040011100c11007007640b40c0d62040c40090200c40d00142154401c001307035020000c0100b40c01e401c5541068420a61903906e40c3c1d003c034440005d001d40030016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 556767176 1250 556765926 556765939
    0x80115110609060708090d02280204050f01050102100606140a260f010f03210e1216090513060f020d06091d0303090a021e0603042001030908090f01030b 67
    0x2036a0b00011035034501605240da00c0c50303010307075541007502e54640c80b10880c0d0005910080e5000c1d05c0f907001c003840d0318441100e000c20b140030241035000282515420b645002400c94141d00400c940d40c0c0400086040d2134514000380030762407070f202c0c0c003800d00c0010140301c40407420000781c11204280319490345030b811000c8150360b0a040846480e00719020008880420b840030080c000490520b4200003900c003184e0340000780612448030200e08442803003550341c4031021b202009410240380c0d030311a4991407109004400601190ba88101006001e40c09644421b000519200520113842848000c500a0f40d400c6640481e0315001021168020f11a100d48858143c0c545080419807803610380055a9401c65061030f4506040c55a0313080740c8a2105903200c006a5202c000a00c1c01030a0000c080101c0c07000204041840360050750106e44c2c00e5004a80845007656404892149807855420b50200d000d02840c00304003007030039683d40140ea4841c41440609c90240c02e031030181542c0c405d80060700c5c04903002d440c8 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 556768426 1250 556767176 556767181
    0x1050714030c0f0f070e010611010e030319180c06051b0102130e09011119050d020d0209030d0806010f08060301020c1b040b06071203050718030308010f150801151106 73
    0xb498880034565038030711050103459915107908900083c0c03c4240d80114240003801e900e403281c20b440340700000c100000b21b552100f800b4451150306002440c8212800444000040912603600c0103d0751100e0000c4200310054980202240c00300d50f460041c2c9880e41480b075520301c200503040441c800010001402c9600025820300444050038411080b82d03c8040001c03d5a107a9030002800ea03107040f94111f0040e14248030652880f020b00170307004060500f07414503a14051000c1d080a05a81c40b440109504940000342041c480c1004c01444144902d01e2030071001500344900000c010010390b050500c20402e00102182a80d40c3c29811145071811001c12079900c80c4541c4540c071030014407844d000c0d04c05d0386001c60994140c201503084038551540300b02c0c171504144680f00183c000346000741207501085500341104903020069940031001d50300946a1a40543c1b410300804da400c00c150f0845803070380b1904e0102c404900d07044110241500c1110790000d955110780c1500b1110320700c2e0310180081e0752092005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 556769676 1250 556768426 556768447
    0x120f06010b070201090b0c0604021c050613021008090c04090c1e0608010902040617090304050913150209031c1412150a0501091e03150c0e1e0105071403 67
    0x2d1002a2003a00d49550310b6a40d103488691501400e000001c490b04120700240c01880d00d16080c0c5581700140f004140e21300101c1c1c6480340b400c01c040b40c4d0941035120303042c1001e0030341c0790505604424106a1400c500c50307240404499486441c04100d0901433500d5103504c2e0304100d02002141c003c0c0c58910314402860600c00303200341014500e4805d10000c28207030000428810f260380225010b07905a42c075071341d5084403900410800000c0c002c00303201c1680024400410360350b45001201d030107001d0aa04a0700d0300843e078203003101a500c0b20584944078601c1009400132588010400b11510700b4905041c440a10304414242d8001c1c05038450810b40c03240c0050106041e101f03164100340900c5641c02c3d1401c42c0e14052040c40040d603100d011b403e0101c0c4c0001c0f070400c030031003040119900c0a001c050922000312350700c1d0340c1c15a10240d034100803528940c440100c41107066000ea281c520400040328002056241c203881c0a980c0e414800b1002e0422800160320000d002410740094155880d280880b03581d081c0401 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 556770926 1250 556769676 556769699
    0x80d020d05071412040c0801090c03060b0d02090112060902120a0308090309010801151e0804030807091a0c011b09030b0f0403050a0c050f0a080d1808040302120f0601 73
    0x18410500d03152001244900c0d116000400701e140b0301e00390301490902c150800c690841e60060089500c2c1042d01c001044660b030038058a644a0301c0390200340d640c2400e5140100940b03211145841c0200315101c042805651440541c4d0b045501c1541ca029200c292800c200020f8000c10002035005034901161481801001600c460428041d80d2400d0060707c910b0540c42d10391180003466800a9821801805544241c940d400b4051019003004140e4007004900840d03c1408200104c0c04180da18007080300f415000402c2c50391010f120724140384c0d070500f05120307585002d1021542c41c52141c5c004c2071070400c84209600c5100c48525240e0300301040c9010304c3c1c005081c10100d010841e91000414042000c4000c0310380641c1c09558980c0301c0508020800700c088500280c0c103001030780c092003040000950242c080c41004501f41c09410b0706981d4000348040fa50640f0000e200015003662520040750218410364244c4040d264100c602e07680b1040703e00f404c40d20300f009030020f05402c1d02404000246940c102c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 556772176 1250 556770926 556770937
    0x150c06050c091011060a0e160b1b010b0a030605100f090c11030322020112150515040803190905030f0105091207110112150605130e0c07080f07080d02 66
    0x321402c0043c0524414200e0b12103050012241c80d950101000c14015900b540022282c0e0181200315599007040b4441c140302100c090380044c02170034002640c112644489010041c15070428802401114141d0010910925a0307210103001c0e15074a101045a5000785001d82e0014070444c540c0981c0c50341c88003e81c400820a48540e900840c6d00030034140da42560100c1902e00c11b030b000c0300014010a580140441a0300e861400480c1001305241e80c011501c2ca10388a403429901c903890110041c00e00b008280450304403400004a01c510f4284400c201c0700c100002101c0521100e49c20580174101d401c01c003503a41c0b810700e400c6594580614025003905100543c449882055083d046614102c1c12203140d0526124941e8090105d408000d0816141d5000b100a5001c1d482200303800500070b600c0e418030208654946c0c20a0000030300c00600302030440020b41000000c0e1035055500181400d020307240d4103580c81504401807400c000481c04903071414548040c2c84500d0342154529a60b40d801000d0704000350f200 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 556773426 1250 556772176 556772179
    0x6020c0301060f060c080c1509030901020706020601080a1e0206120919080f0c0f07060c031101050f070c030e0423090a080a0c0c09151a0f04150c06050c09 68
    0x2803100016200c411003038403c04550303060320340d00301d00300e8203403162085035000f42620810303480344001080205180ca610b544c8215020b074040c50b2528078040009041a603680d01a008550020006101824020039201003040c0c2c040b043c0b11043d88801c604800044c00c251000c0e6201c0c4002c124030103010301c1d0700c0b0b025116655810030b5070703503000c94800d00e88420305010f000a46841c9081c045504640401c100400001044108880d01038000403602490482c4a0b017110001441081701041019003000844601a41807002440725161000f0240c1241c0c800034203070000c20072908070003000e2500a800741070700464054402d109409044021071090303088084003410b03100c1e154000032000c2502040c01c1000940c0106502c0c90101c1d0a68121090f032680a0150340d41580f21900140040ca144901602c0c08a0031120003a041d1900c01240280a400010b40384041d40803c014092082201c04680c1507030384065000c0310000200c14112544214440d000700142c0c980b405101c18aa00400502605c020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 556774676 1250 556773426 556773431
    0x1a070e061e0f2d040506030604092a05010203070b13150501081b0103140f0a020f0c0a021f08040b070c06020d0911010215060618090c03092a151306020c0301 69
    0x100f680303085035201c03000c200c0c0304084041408280000c0c5499001541c00c240000c10108031510300740c4074030000300b1004558407815403501034007600c4c41d4549840d8030300809090025500340f020039184c3e0100d107040104001c401d11001203203042000080c14401a40c88003d140400441da141ca48043d5528120a160314902240310701d0070380590721a028014064828181e80d1045456401e0600590301c0c015110b409800e03002d0012a04c400a0b0070b01500d045040c80d0000c10441c1d0060041c040032221035204071001c1c0c4280d24a003100150042e500310742081d03100490501d556100c10048643d4612a0001480c040c00001d03078514080e05030b044a01e540d070040b52114820b801d00340042e603841e11030200624005040d80001402443c1640c05041c3c500111130b0a1001d080030880081e603003010858004110900100034084007400401c10095120811810008821013091202c12501101d0165910428030f08460014000b840380a41742d11b4a106400004081c1d00d0745d202944544440f00c0244c065803 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 556775926 1250 556774676 556774717
    0xc070801060b0a021c11010218130501030b040b09010f020301230625051603030815040207240b041505120105060f10030b0a121a070e061e0f 62
    0x20b100d00125003854100b0380003840170488030601898903440602942c010b2008003501c01c844140c003030000b40503407100d0119450b00e482d80101042220301c400d02c3c000404170310741001400061600a000390304103800548039642c0d81e0307454840601400c03120755601007141c008400020768185c2c400d0244c4004800c412101100340200c001d012650180d100c14086c1c5c41d0158410003001903075954060040c1c0e000c2c40070b45540d60002d07a030031034290310142c0c003c0f400288143c1c10418400c805000c00c000141045805610701001c50f1201009400c1084c0a141134080a0352661040c01c4a584140c60007513001d0020701c03e41039041c2072020302060034070815014203c0f04071106411a0188950761241000910409406039040240002d05051110317000c00e0556607401c580540d41d5180000303004141c0c045a8484090413403030810750b69409184804244101c80060040701500105440b180210642e151615054081004403041040c02c00d4403c9240001460300125400036009280e6414502840300400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 556777176 1250 556775926 556775939
    0x50103020f1206070e031203040b06150f090f0f090106022805250b0d05070e01020d27030204060305030901020d020d02060a051e09070603060b04180b0102070b0c07080106 75
    0x500000360b05480e10b0b0000d40020f50094060103e103151001d01804844000c1380020010180e5407050b503085c0c5400c04604c007006840e00d0410724460b000381c03000d0181340c105002900440094056181020b124079030b04400305c001500c070320820455403840100038031032a503550300000e5100d00503088010000d404401310605050040090100c0d00759000004050040300400e2411402d001e034000d2000d0503920700000280280d41d1400341142040f51140058a401d040301c000d8103410252500c1410341d0002d00c4070743c206941200501e06002142d240c0464401c001d03034420341040c060ba03007000354841d2800d5800b006110380040540240c40c400c3e002c0702c103014080c0c0816a61030088591f2080180c0c4600c0016000c0e144a400031500800401000c0c500e01c03078102e100100011041303c00c600103078071058040200399814003c200080041244161030241801504603903001e000c013243c451386440c0e003d2004580d108100d4007004160b000036003600d6441c1500b84680300c00591040c1c80007582000c0011805 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 556778426 1250 556777176 556777189
    0x20111090a0504020309030903030307030c080105180f09010e01060f0302040e0106030803070e011e0c06050f01080c280b04080606040204120618050303010b07052802090a060315050103020f 83
    0x1a0001c0031110420724000c20000039505c02071050005010a1142e0049901d04101440c000d100c151000314080e11900001000680142e021a104000c1094084042c1040480d1207412840003c13942c0e0310baa40d034075480b902400c0c120307d0041d625031a0020004200078801d245d503094074421142403040c08048114582030b00c44e01d000c0900100420004141041d020b01003200d821081810190403c0001c0c042e0044c1044041081d480031694248c40001048241c1c8900780d8004d416010040246d4180f402170740d59050820f8171507008038102ea16400722040d440b034400b4100070201c0c40080d02903031a13040100e0990032500c03924000e44505030114085151500030303074090741e08800c2030a0440d04180c40f0311018140c2c000c00101c880885030800800b01e402840194083e04040360941c0d56084585081490302d14000030011320b001c482410342138442c1403000702e00341341e0303404a542c040c0a413140c84404004090070f0748004c0a816a0031941d0504007000e40010381203034021280700a030341c80d030101803020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 556779676 1250 556778426 556778437
    0x726070f060f11060c301605071502040f0e04080304020105090616061b0212221e0504050a05100302060c0120040905071404152d020111 60
    0x32100340c15a040c0706091203041d210074a0074051802d0001088036185040c20301000f41c611035110000002c9034461004000140c00c43c1000c154400b2041524070400c001031410084d040803d40d0140c4511401141e1140054400c040d070403140b03030a0600110300d0003030700a500038815102010b041e00000501d841c44c4003051031107250001a0545980c0c0c0d99401140c1642c4010f5645138405824810100e00001e081a008030361403181c1070000300c56440d401703250307909600c2d0f050650031540704a140140258814081c4d40e418903208407101d607015100044040d90400c3d60b040b0360780003801c071038150400c0307070058000c0f1040b100e05903010003040d11000800802c1e980200ca21824802d0070709420401420010001c11100c2210400010681403210340551a441e5101c00048001c00103c0d0510500c031151140c0d6410a209040131090403004002d9440c00740210f101d211001121011190340030341c000c800220342c1303407107200210407829990803042c0500144e00e401c0c64011b40c0791404407840b00744103808598 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 556780926 1250 556779676 556779689
    0x901050a0b0409050606040801020d0b090604020903120702030109050609030301091103090d0e0a0f0608100902033309190b0f0303160807170a020d0806130e0a05072607 74
    0x9180a04111081d806460060f00490708486c5c1040000f80710b01003803000e07003c80111050049054000c50080010000300a000e040c46a44100002c5c0241c1d0f4001854079503901002c44203940743d400900009005006016000d00b0b00c2c05250100014441d0100c000d5052b40c0581b5000c110490070348154406074003048500506075441490107425450148807000d50304440206509280350b1103229856000140d0342c08200440c0150042c015007486504411014180f0141e045003185440020254884291044030b42000000b0341040d10801c0702400400311002e02030000507007804c05c4104095804022000c0c0403c90746403c03414089850004014440310070300800660910720f0510b00340d40460380c04002295140810045640018144090540602d072507029103070300c2d40c081440180c01c3c1a20341440e00b04008908041105a603111446098070321082e08000500042000d00d8520308401c120002e40303280b044650010300303002603040e20480c400d0500748070074288240c005015038401c1ca90042c0c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 556782176 1250 556780926 556780949
    0x3081617030103330606050c120a0206060909010902030307081209070501050915160309030b010e010b0d110c0f010204081912032c0d26060f0310060e04020901050a 72
    0x110b01c10102c2103404130144076030344840d65251040401d44001c907011031380030310041400410b507101d041c00184002c0c441d841c0303100701d001d25207504101c0081d1180b40080c203a6214a5440000c221829030946c0206030b0994080c0072a0340d1a0f40c42d00b0101456000120401083e44082c0d001400b4140d02040c080100d42040c1c490398280358000c010807003025504658170007c00e80501180300300c4a18523100c400514002d40311005d2050560404040400c41600302c50701c1295000d004201000340c0d882120501d055181001502480009420703c440c400c41040d408c0a100b99040781c00350f010194001c000f05d4000104440014028150310054695050400b0f05400301110030145018001c0c1c002c04130780180c51100c3d40c0b441c1e0781114544481c07c0589448600350348001500361f04540c101c010041c146c110300c40001a0341b4595150303846c090700000c2a86008150041044180c0c0c0c40070003025680000c142c2c024072409071038034009909914129010b9200d84041030000519042c03020b1710000382c44810034203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 556783426 1250 556782176 556782203
    0x901020a030806280302041b0504030f020f03030a08250c1b0512030a02070909081603090906120213020c1b1804050105090c03031305010c0c03081617030103 69
    0x64961090081101d5049605010850030032280c00e0548004204d181018051203421070040c041140c200200d03602c541101c43e043d500b001500314080e14222580480300440882d070741c0c40407503060340580f44400d802d0b1002140422055801c000d10354810340c004040c0c8078500c40c003401814411100d0680407400304031001242c0001c0f03050806c0d000c107616040c0c89820303196580c40d00030600b048260303000d6105d50f400208070700b081e0a6040c040e031002072a13058400d024182d007548035400b552040d4400c1214160500742ca0004242c011403000700140700d0410204602c07981d4031250003612640003801c0b841400b006160902040907803082c0c07030000c0c4e4644000c2451000484c14124900003d1200c21780c8244003c00b08549140c0340918035100350b00c18400452075007018034226150244011400707100f50410b210801d4002c2d40d60711001f08940c001d180544111140f8100784c42913018580001d460180c0c00541000607080ea100714800c168841c0e0350442c2072280103400e031401e40c0005c0c040145081c0c41c03c800c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 556784676 1250 556783426 556783433
    0x10c050414280e100609060503070503070212160510060605041e0b071202060f0405122d03060a0b04050307030b06190305061506030114010f0c06110702150901020a 72
    0x45075105003121400201c5241c4442d85541080d4603503500000b280c880d080100140c5840030805a80107041900340907035014103040c070180150000500401c100140840040c91451080294483d15104215204c2c0e4411410045003200d0311a001c040d00e492003a60510b4030f014110388101411038403a9551241050300300b0622054135941c0c2d003050105272000f280003081500440300281441481940421002841010040e060410041c030b01440340076954100700100e04045070400c1200317464440ca035506d160300314010901d100101c3c00070790780d071121031030302d10f204444d50300207501030350040301c40c00e08469686405074040e200350300510750542c02407002000040c515110f520f0304402c0003860b43c1e440714550120180c0180e0194001e0b00c140e480941808a40c2c1d42c2e41480c443c40301c50039605103145604106a025005169040d910f04009602107500907091040d484440360341d500c054103002007508524034407100c0d00106c900341c0c072486400550300d02e802899800c440f008503041e001707810420010744 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 556785926 1250 556784676 556784689
    0xf02150a0b030f060c270f0112060b0301080a0c0509040f080f07150b092419050d030324140108100906090527070b090303040b0c060405010c050414 65
    0x1c1003070303094412141902d01a80c820310100d4418017035440e00c0e58175845100644280310000c3c60030b40fa40c0c1e801401690200d034507040c64005034a4002e0a003284440200d40880b0024401030323000d6600344c90301000101d0009004116007130b50038042c00f02c01c0d21254840d41040303d90481554010400c07428501c0282c00100104003078025101c54914040c1801e0003900c03855180c42d004201c825031140c0d50744c0e03075020502d4030300940340d0070010384410340c000e005505241c40b0320302c00900001c40c89a088000181d07a03100d1619040c070b0217000082c2c6220591941440c002c0c000c0e100054000d4400690841e000441c40710fa8039400c0210340040044011030b500e05c03001035425620241c1245402071004102040400d194010800201000100003c00f07181c007141c5842c041814240d9400030f52001c0c00304a400510004402c0d0a84003403184003a80c1c0d07420075000a19501c141c0d8416441c6020100398111790300c0000c03d0303041c8a54002e000034040700f410313050100c5141c82240100c103010f40107120710480a04150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 556787176 1250 556785926 556785941
    0xc030a110910051b0d050702130603060905060f090307080307050d0b030715081503030a0809010e0118050606010201110d18080409021309020a12270507060f02150a 72
    0xc004518000704a00480c50303580075410480702140c0000703040320302000a4150b00700225000300c05003003132210009005185101d001e002074882c2c030115098101c1d081841d40150021a030040d0200071000d4a46031a5485a00445155680d02c0141002078a03a100210845811310340c42881d0034a556610441952684c0180b4541604c0710b81d9500481d24a8404010040c080c2110310300360880c000c1454801407803c80020003a100310050b6080595180e10000151114100703036042031722070396035104109030040440712802d040560910242038948001500b0701901c0714002d40a0303950640d9001e0059007a140075070b0050f008080704200080325498694004003865031841903840316101c0b1074450182c140c10940040daa41580007400c480041140c0d203a440c000c0008040a508004180700c0141c581420054102c1d019070329200798003990500c800340c160840450008108040d180b5080255541315580285408605102008810341e0300000d00b1614001100032503004030750350307403414902500c0c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 556788426 1250 556787176 556787201
    0x2c0a02010c0b041a07110106060306050d020f01020a0605240103050402090105090603070b0f030a060f14150d0905010b1509030c0f120303070309120804020d170d320c030a 75
    0x104c1c006002d90811140286008450558840034143c83c0d0307100d03090840307025512103000c0c90725001080209480d0350700e101c4082c5404441a4208601400050303082c0101014020109032414081103855a0075004040000000e905c1031011300c2c201b10019400ca450039140650322101c1080100840e02c2c03c041c056901507006820f41d84402c0da00c501d565540d81001d032543c201e614000c020131020005610880c0010700020400c1c140c1c1d00d2404200c0c1c03005c1c02442d0321340c50140050b00b15501010700314900b1203a486800000c100090003c504004ac02040300c03440703a5200f04417510054a41980c0030058a014550003806859450540b00c20030030605690407600b03400c060948940450080c081c0701452085410340c9011450030300d140b804600301c80c03220020702c1c10b0056010521006d602c0e0241400c4c03413103612500341e22a1609120140140e8003c9403803010025007002c4150101000015002c2c0c202c1d00042d043c607022541e0003802032840303102100c84102146051000841c48890ba07003111042000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 556789676 1250 556788426 556788443
    0x40b0a020c0a0302060609071404090b1906080402040609050105130f11070b161d01051e0a0207180c0e0616020a030b07021c020c0d152c0a02010c0b04 66
    0x101ca8000509000342c111060f00940c00c0803007004aa414800c41941d4082030f00d20f4652181c03e0000d81c454000d0180740070b1903e034140e4030310103000207450780b40b0f9003e602446042030b0341c80e41d507039440000c0030940111822070081d8202280010342e51000d000e102d05940b0004d040701810400b1180580081c4034081d039101a190b2601103003203000140c0b074014644140200b9042d149480d04015485054249840080070000c00001c207090010002820701503444092a0203981e40c456101c4c4154401d840ca19040705124000886212498000440604a1711645a0b0b2240c940000c01d0b00030454000340c17510740c0402c8800046403621710300b1364010140d6100e0080c000c6200e0110750081605205190421564005481c0600c89215010401101c034202003842c9511a15200d000017901c40000940e640d0059148020480800c030510603400c201c110025002c1014000041e042d003d070f0300084886150b07200300705801103803068011500b054240d8040e10f4803580790809039185145100c00a00c1500d4007607 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 556790926 1250 556789676 556789687
    0x201090909050a050712230c03010e030301080d1e0305041b03060c03050c1303030f02011d0105070906050406080105010c020f090a0c111b04240902071101090e040b0a02 74
    0x4030503104500000340108001c00445080b4a0514904619508007200c40c8010070384502c0099106100c004090300c000341305001d0600781d202901e00c1c02c07694081703c0fa0301d1b500b458000f02c00418004044c41c12581c500c811119132007a4280156420312007a01c50b608403488000c11942032902940216130018801e001d07071413054854080f03104501d04203805c2118107c1e182d6484001036a0706004081d085020828042d00c0c0580401c074443d811809844001c0501c0070100071580c00c01d0007075000668844bc12918412202c82500d05207000f42400c56501c0302080c14550042511407061050314283c03103203a00d40c0110307642440010344030404e65440481c1e00c08040442c0c296640c6581d00e8484c052584501c0c040340d00d807102c801c081c04c0903000c0829441c0c9540b12800c4a01400c4901ba01500c418809071070000e203058000c1207050071400000144031051580c4000010043e0555000f80100c2c0d0084854200703c01c02c603001187c006a45200382071032203010501160100f82c01401031074108410900052070702 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 556792176 1250 556790926 556790939
    0x11030d05062b050618030901030b04021605070302030607050c06010b03190f050f0609100605030a0b0a0f1503021303060209010903150e0708030a0f121404060e0f0c0616020109 77
    0xb039003502d258100500541c40799000c01c2010001a0380121a0314500510120b410340010f030359001e80e03560641003540322041800f840d280c681c11204844144a01c41259071185d0600595464003440300328041c2c860000002c1c030041c0b01c3c8068030086440c3c80007601403a441d02c000761820b41c001500e040340c210711496000030060000e104803450f402c02d03840e01080510708114946c80b100d80003095503000b1409a010085049080b510134010f0f6549410540c0e01c940b143c011207001001d2646215800aa9040b40030500070881c41042d41122052810b0801e48046158114181e004003d100c2c011000c00003401c2c1f0010b9080c3c1c010700396140c010f24240d00306559940380c02055000d51345200c00030381d6440711200c90340c2801703002d018050140c0d41d0085180044500008080d03800c1ca894003803c0080300c00e484540100300b038200d8034401076440d5290f0820f09081c00c140b4014826003859851a1240075505c0722101004110b207105d0001c020130311405d0144101d20030065048100c3c0c2241044090030012420 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 556793426 1250 556792176 556792219
    0x4030b01051801032a0f0509070e090a020a3f02070506070c020303070c0b09030d050304050714031603030206070e010c05070605031e0a0e0622060207020d080a02010504020f0111030d0506 82
    0x50085012221b5024134080501020f00006000740e4101b01c9150036020141d15120a155040003002200607969040d02d00c040700e521215800c0c0401603071a002d030102c01e03e2003002c05155080c4000c203156850000081c6c2c018100c1c801e0500041c4a50099000102c000d80910307008a0b42a002034143c2e864550a43e0341e4004412003600305c100c1500d004105030319503040801030044440241d040261860502d9201e884d51010300340700e0903100001e40c000303241060b20288244404802c1c900d442c13145080d102e00c0c01a4448004490040014442d0159000c056215582c43d08030190401c000e010f5241c00c005c0200ca40d0b600c0104100b030a02001d6502040201007074461911425000070006000000c000146080140107441030a41803500510355441d500c0409100c10140d80c00400140c0d00c0c1c506101003401440d0f06500580a0400031407840459601034010910451080314a9031421002d01c0c0196210b4482040481d115401403200d00140703080b0b0381c0415041b120060a85044003000b1164071071 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 556794676 1250 556793426 556793429
    0xc060c0f08121f03030210020918010b0904200307080406021e070c0e06061b070902030a091704060203071e020306160f0f0f0c030903080d0204030b01051801032a 71
    0x4503220382c00c01c014481005445010241d0341151280814a1031602c00035500c11509202c002d20f190f000414411540d600130030000c80401344040401d4030340c1e449410020542002110318003c40c00c10a08041100090b0b190481030400b061006080d0346511a08952840000f00219080c541c02c0006039840980700005a017080e540d081455510402850901d02c03264030742d4401c1540300c001c00c0c140310503540c0700002d5594507004100f08402c03102041d8106883c20000d544a2008144000184a0f0b480d41503040800d01034011b124008828030355442114152045100f040011382040c001301c0300040031048d101c3d107005c01806540803507448507000282403050070782c1c00c03030b105000300000035600c0d90700000d00030716243c41410840e405505407030003e403410860801c140d0400059140010030180608501809107411010041d210702c4400c81c030344020340c418003003640d91001841c00080c9510f000c0d00b5950008002c0c22442e50541d00e0359556956440c12030f001c071911207104883c101c84010a450b403c50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 556795926 1250 556794676 556794697
    0x9031101020c0304080c120a0b091c0807020d020604120507110907081f0e1605120a06210c05041509050a060f0506032e08010906021905070c060c0f08 66
    0x50f40c95242178a00c03807400da215100300d4002c0c0c0041641d0509a000070503040d10468000c00174240303070364501e9022400d1007080d49069a04000680320000b02c25806480144200900d40859a030140300382401c0c1d0f540c60307044500524000081010b905c0b8a071041010b401c03610300c10aa400c00c2c030803030000002e108000494040001078210b104002019200b1420040595403032055000030900300030080c810408010064034061842e4a01910200e10400482d101c0000341c912080e810b00380840300b50064003c520600c50080d62070712401042c40111208424000d600c41c0f0f5140c80103280c04203100103017548000c40841c600f0b008400195039030705d03400341c60711425a0b40c10014429050410300500000681c001ca4000c000910422840c0c0c0003004004005a003146000c1c1428842e401c80d0301d800811079040a60b2030750030000010104a910b801810104c10b043c69a4030110482c0e40c0121650300a800000c0e100c80c105800800c1500c0c00340011011045c016a500302507040b5030b4507804519030140300d166 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 556797176 1250 556795926 556795933
    0x15120c12010f05010e0103051c0e04150305070602031c1805070e0f1302130f150603091e0210050a05091804030e09190b1311030712020a05070609031101020c 69
    0x21000c0700b05219160150040348600b040c2d650458454540c3d450940b80c0d00c1412003040049808094020503502c21030040003003041c00800c0ca850141c1440c00107034802100c003846905004034482c4d0002c41616829613484203000004002480c02d02d028013a50103807002c18921070341e8240046142401404041c1040145603229070428810403400c044c0000c0c1881007619603000382400581d00d00900720982600f403180411030340c8140441304002d0002002c41041c02c0030340c001c00182c294168000a0300a40100c03a0081da400c211440000b1484c0b000c08000c1d80440c000b0380ca1500703940244060700481036a442e08500f805100b0020429110340070360b454055048510402040541c00903415001a10640d0300065a080041c1a082c1e080242405c0f4155103850703882d107842686034043c0112a2000044007845112104481d11340c00ea84240c9600c40001c0075101d210214a01900031200000c000b80d03220380ca0310400d529008020409200e04408002c461050110742c00002d0001d0800c0c000701c02d015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 556798426 1250 556797176 556797191
    0x916210603050f06160305010302090103230d112404020d060e100209041505090105040c0c1205090a14010c03050a0e03070803252012010203250815120c1201 69
    0x1011724108205000d08250a0600500040c0c94900607141141c0e40242c0159844e46200800041030f1003142c21144140710303a407d0400c8850b4843c2010a0000f4400113584181c981c1144904017a01c80f10351401c0402c084002140041c10842d4003106da5501810300002e001c82107a201341d040c040040a8000e4194021980f03203005d2400f849801070703410240d64110701513440c20002c51510401413181d5441156540805c218550007102c240640c40e80c071554002081110380405001a006481c0c0140195111803001c98603030085200198a224140c585a800c48500d54045420340e101d018000100030b41c440d83c01913151800c11100b4050f0001601031a00c5d072400e807040340d60411107002c501712040314100c0040d020919030400d1040b00c114001824050549500215030708944142c261145c541c03001081160022010784035101d981001a40100072245048084403456010f0340d002c9400d00d6180340342c10382d034a000c60360710700383d4064131064401d40360711040002d411a00c540325086081e510b500c803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 556799676 1250 556798426 556798441
    0x5130305060117060f060103150b04090933021810081b0a05070206090f0d0804061223061c1a130c030f0201120f0b0916210603050f06 59
    0x4000685420082c485468686048105e070040500b4503130605650300c2c4048480302245182801801010310f600c0d035980d0313071840804000e0410a02c141ca0110403031400c13140318041040c08848048030480300c00c80300c0d28241200070080d80901d00086003480e08414115a0f81c54901441b5016559038840304074619003607001e0b44a595030f0381c0c450710280e0020080310612a400034299601103405881e02511140001d020518029503007070b03013541c011109144401040511002001500c0d926a82c202890900c250350000313440004080c06043d01c407001406c42e900c42e1254007103a02c580c00078048040244001d01010281c0809103003035407080b040d800b2008590000c0b010b165084240c003c40d41100781d01680302c070880300c589400001d140c11b0001c089001568810042c0400e0109807000030000d5210420444e0001e10501e00103c0c001e9185a00003085001c482c00031400c0c1000649603141042401c040b40710078103200480382c00d07070320707a94620200100d102000800c10164100e001407103181001070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 556800926 1250 556799676 556799699
    0xe0f0a060c1101032c030c010e07090b0405040c270c020d0305010b041a0f0f0406030903031a0906040f11030f01030506010e01061202030403051b03040f0506090d12051303050601 78
    0x80c41c10f15003003599004014101c0c05c203480c0b0020307882a078094000c0c1c942020034114030409008030040e41c2001c500301c11104000c203000013140e001d400e041210515070310900040e43c5c0211409003029034400400c000d4008065110f404030400001a0032901d56240b07081c41c00c45015041d6100147e00409850000c01e03010700c82c03240900000740c001818580360501e110700c240c50070301c10b010300c0c034101041c034100390600e0318281c801c0e1825070700c03070552920f40300c03d001001130155071001d070b00103420140c0040f070701e1000800c0026544409403048c510342d92000700b80000750081200c0b04181c1c9035100a240b4562410b44080e46c020441202450569491403c000c2d140c14811f8100d2103c21b01c00d80010403002d40c004080f00303401e80b40142c02603100d50b1507040c2600e040c019600152018074414412003d480408001041030702c1e2600d80d0281800c2c0c9070380504c490741c0a1001c40030782000c1c1c42c801e01c00204000030b0f5401081e86251070b000d03141c17036400c0d2441d803d0394001d070b8030480726070340040014400c40a810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 556802176 1250 556800926 556800953
    0x6030b150c0606040209180106170705190f140c0318060307170c0f0c01050105190302030309090a06050a080616030b0d0f2901180203160e0f0a060c 65
    0x40302000e04100e215030140d500d60501801031481581d000070603c0264658041d100c02180121380c007803100707696991002c1d05c41910725001039146151400065030040c0104192a048035640384420f4101d03a480005445070021001a10188040182070f040d4150404000f40f8000c0990409940c64219070310840d040300221018840c4150303010b0081001c0b1035801360307444924100b101c0b0b04034520384030300e0b41c54030f260310444d4940f003030241c2c0002c1c0d4a8104d0f141500600c0c101d42d0f0640744001c040b0140c0750714071054101404029816002008004124602100f040c0c6e000000300d0400940e203035a50000030b0f42c00d0065400300c42c003604800100420046100322003004100c203410280021541038000a82614500b0001041c907500410b1007400e01c4100d402083c0701c80ca21b408407510503005c00c400e850001c0030034813400c4842c20f1308034041400c94485009980c001c03150013508074100600c885007642c80b07018655a040c1c010124001c8041242c0d01d101c50480109160744920803080307054201a01c1c2c18201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 556803426 1250 556802176 556802209
    0x80a0c1509030f0f151b020f0606060a050c0102250606090212130f0b09010b150f0406210f0921200316050321010501080402040b06120106030b 63
    0x200030100003190514642c07007102640411050307521821450403050106000b100150442d14100480c8a03c051b41704442619100680807900c0f0307402c81500b000c0d62400d08690780c0d44c0005040c8543d142040c000c1e4060448045c0142c005801d1240c0040101d808008146129a00c9070b1400300365011311919200f002c000c0c00d1071142c154070348451505520490704000d009518010700c007001403424844101a500c100c82d03884116402c950034100340c110301a000071000f152250a4494144905944d20021a140001070103c030500309480c0580a840d140078050004001c1401c03a01c41032009146e0380301d11119101d9526002404142d5410880b500c90124152001054400341360300c00310743d810089403030300c03649004080d070846041840514218007980802e801d0b00d06c64400d40900300400800500200300381d03401c0440d03400d5181c8040d0070302c01e103003881214007194640d40403502504140c0c1164034114800b500151500c000c1d184d0300048003900343c2c404000255104038180162038a10b4070002600c64 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 556804676 1250 556803426 556803437
    0x6140a0501060f0c0f1b0609061d090601050c060403031b030b03070b0307090e0c1e040e010e04032d020c03150f060301110a08090d1b1b080a0c15 64
    0x1004005040100d0040d02d040c10300400201500410083c0300c03400304511b502140c805040a000f500c074070000c50403405184089580c0c1600840c1c1244290781c3d00c42d00e51480c64050080400799000d005030f48a000e0081390401000300320040201d0006c2001d0f41c000c0340f0036540094000103074103d2070a07031007007038404808242c10484e03004803565001030b0010589500d0190030f41c0c0da8a490809660280682c1e0002185161a400300202050072038060420200703840310080d6400d0340c003101500035100f40e00601802b9054440140b0031502c0a40840b0380c000d11a0401c03052550060100c24440805601c9840f600e0a5520079000081e6041c840401100c0041e8010a07600030101c1d031044500e50010111413140e03d841000400680d4250090686002080a9207507990703600440206200d008890384503c500c246407100752820b210f00c01551303511400c01003800080304103035200e0a29806c0800300d110000b884920201781110709100d468102841018070000c83c619203084031300c608442c203015009015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 556805926 1250 556804676 556804679
    0x20f16020f010813110112060b0316030501030f0308151f090803040b1c060f12031b0209040618060c020d09080d050301060c050703080703080f13050c04020d090f06140a0501 76
    0x1440c80107100c04442c0e1012000c03601c5c1941d0340040700c505010b81c240d40031090802c0d40015500107400001e50107032082298181e03101d9000310303041c4d042d9402840f000f01540d03004d99048011034854070449401000d011801c0c401078108200140945072050f40681d41d04011000525030b40703400070030403001002800040d600302860030402e0440390241810100610340310714038090503002c0316401310010307000b00c18000d1300407506c03080e4502e513201c1042000c03404104450600b0020400c42d02d118045180c1c0100100c0241ea961b0380c075440034003c11b0960881c2c40031080c1e1000009241c0d03004204804000d0740c010311802c0c0003d6001084d98103140d00c41000f54000d60b402c0c500ca507900c20304581c15111141080380700401c030303460294900141648061712054010440808041d8000d840c54001d482e4040c0392000d0303448403140f8510704204150000e142d035008500c4010f140c2480d4010300a14003803140000380070103090b2680403082c0181d80086402e56a140741c4100080000655150011130b078030003c10040d03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 556807176 1250 556805926 556805941
    0xd0614100e010c150609020a020d0203120106031d01090503210f0105060c0703062d15090513051203181203401106070206030f0604020f16020f0108 65
    0x10160070001d107042141c000703040c40a01c00c41c00d1000c020b50051010400041d60303a80503190094004026000060003520404601d40c2d200100b6142d1052400c00807511036448d00d40150300801100c0703180c0c00c055540d2044600420002e100d540d445a014a0186a6a14404014210061050000300ca10025400601125600c810704041c15103809a072500c1c0c0d03a040036240316240030801d502c0200391a0030f0002d00b511003030314001041c1c0c2001e244081c0c60000401c10031100282d41e41001150902e00c428417007080070b00c02d01d03004103802c6040d8103101403103203003240c4a25061080389036400700e03440000400e000700c840d54030282c824000c208401500350600442da600b1914400540100c000114001101c442941031044103164411401c981c120314035050515405180403440003510000414640781d030321400c1400444000c543d005105618540c0d400f803100c030070018007500032900030b03030b09205015800051500800e604810031029258071280b42c4108480018507800c03050411035a01c0031f10041 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 556808426 1250 556807176 556807187
    0x40b030f040305090a140a0518060f0406170a0c0f08030a3906140907090e0a050a150605030c09070509010e090a090c0803030702070b030411060d061410 67
    0x24400c0e5028034548507400c00f21514000c55907180d03409a8050f10024100084220010095406a4005100696038010031180070000580035845c06c0310f03e070018285241030130034400180d8000b070000480da80c5601d090200d10f01c0080241e0a141c0c030512086c024041007101030070040455001140c0070500b02811241c403401410f03101000c0c40845441c0c0820800459001c04803410500c800c40c030b030550242c00e5201200c08401c0d055508a180100d00c94583c0c000501840c031501d02c080c0284a0756160112100003410410048072407070291138580000281c003400400c103080c1c01124410581040350030484100e50745580244d00c282c3c083c84c5090300350b443e17240e40c140c4d10400324180503880303210740f00068900b034818204255103c00c040b8100701c08064070b03602140e50030f401903078180c01264540c0f1145590744000d403901000b44c2c1c0301e08010004400d000c0011a40188240c202404415403080454000d80008612140360340e100c00701480010380d000e004040e900c00450784038130070b01c00c4078101409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 556809676 1250 556808426 556808431
    0x50a030f03120612061b03060515070309180b100c05120f070209040302010e010e0105010308040e040302071a0702040b010c020f100302090306040b0a0e511b040b03 72
    0x5026a08510701c2c00740086a0000009200503d56410b40a0161402c400140750000c201c103a40c11607665040200703442031145509540d00a015a08103918140301e02c0c1c40b44d0054403040381040603a000c04102110b81e14480c0c044010030b4403010910000500810003189030440b5030504000d02c0400841c040303030000880240000d0400c507059a5400c0e032414800e0544103860f0003031340040d0800300380b1042550540c01072048204290080098510040219003601c0c402c2c44080d04a64042c0400e010000d00346221503000381c8640100c3d840c0d0365855004144030319a20814282030880840c500c003e504290150461101003460700c08510101e0b81c0c00102074840a882c468010308640d903002143d203010394100c41039840c0003000c44045240c5890044420502100c540c0481c42c100341000f19141000150701c1c0c0c17404c00080c1032444940c441e090b0302c1c01180d111580340211801d81c0040c14400400b90300c11804054841403111550b2030728440340e008a01c921485d042c01c561040200304041c2d04050180ca4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 556810926 1250 556809676 556809683
    0x7020a08180d1a01030b1006020a110102012c06010605090306160e04060b07020f0a0501050a0c0201031503050319050c0d1b020a260309100e030a0b010b13050a030f 72
    0x1090400311404161140740e120401401c050380049000000d07000da580241c100c0f48551080106da655a00304195040d6051007418056480b0080302c10000300c404106003c0319806100000b0328588800000701c50000105042468800403051b41c0d54070941402050301601942c1400d0b1f141100900111b90303500d0005103040e181c88881043c420040f8459642008440b0f0018400c0c4100c075100c810004960b40041c070124444e0150015502080c20301c145500103c83c8141c48040c10005411829103440341c070b08a00302d040640d40c41e01e40092000106224000c1c6004100541c0c5802084600f803002201c0907180f070090110902c051211750030001120b1000b46014680008580e50f881d0a04840e030105900017903201003140da000c90340600f1481d070303070840c04042c034420401c0e02e14141e0030a8a0b40700d040700440d00035944d03844c0c62286a0040c2c614040b01c3c0805000c48130340c2c030f2040e100d0b2104c8000c00c0e003003010005000240d00411003c0701807803e0151400300c40002c0500d1556450b502c40021705007008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 556812176 1250 556810926 556810957
    0x906010809010f02030c04060306090903020307150906090f14060103021309030203040b2113031707020c190510050903030d0b12010c020706090e090d200714010807020a08 75
    0x5003003030002e401c83e00110700721890a41d100c0c00e000c0e070b0f90034076900140030700000645050310005081402d4000d4511282d096000b541c9403071075584821841c03120748000381c0c0c0300c162900c41d9080040e585200310752000d40203d201d004032034003510b085003401500141030400343d0312041c0140050b80d62040c0305000f10030b00c5034000444103031b80d203800d0342980204d90046021103400700f00b422101170401c5240388000c140305000101d958822001c0140303400401c03800350000e200d4115084c1c4074010141420381000d0140102e9070b042c45060005107040580511a00c1c407041c1100c0200f0060815680e0281e0341d5102d402c0083c2003688040c0800e46e280100024012426140c3e1000302d9280ca0340d0b500c8051008009000f4020710303035841c5021307545540d5441083c0020340d014a00050b00030301c440880380074202e01005007a82c0d0151000c00c407000741860403000755071005000285820003041000000800322104909148042c0000141071180005c142a0035034004071540c400007800d0508543c80f4604035403a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 556813426 1250 556812176 556812181
    0x402120312244c181e29220f0e011802040312030f0209041a041406100f0c060e010e060106050c0703080912011506020f030909060108 59
    0x20600b10325042c24103960442410204a10030f0108400c2903003059103d00a128060710000032075001085a540f03c411501c1d00307405040707201d0fa12489100031403511080e80880ba090311050702c68042d0b0f0824110040c80480840200000b0441202941a2440b8440b11413442401e280d10380046103d600100c800440d02042e003180d001c081c00310100041c00c1e00005c10344801d500d070501150004401e008006520040381a10000780c407031343c0200c805496006429007440c0d01500401e80180070500050755410f5028088403203151240c0c800c0042c41d01911013004500043c0c01e0522003100d003002000c02060300000c0803c5099110700452082c082042d141841006130213a0080b60000c035646c000420b04d41c00c20200c54240101508032181d140b55050940e0740f56607841034103851700d104540c4c580803980c1000c0c500700003140300200608007652000c4d080c4101b0804001c4201e08440c465546058520503180781070001130340c100302c0100c0090351071000710700d403030041000209090002400301d4100030f40c0000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 556814676 1250 556813426 556813471
    0x20304122d0c05041a04020307091a0a0e040204060903020d060204080d08070e0f0109290712021015170c0d05010506011715060304081306080402120312 67
    0x140740d0140d500c210440414100c6400c024018444040c140c4000d201d40602050a203441d1003074841d2140c01c0d04e01d50a89040c1c54003440301030342004225030b050101e510302c0001c81815003c1c01d0201c00c020250451303a07582d030a0320b024008242d101a10307070095105010511659030005005070640c0e404840c402903101c03280c41c0800181c82560410000c0d401564015260160000c140e5030240c036098596049580801c42801103403101102c00303038000303803807000c040002808104444800c0c18000d03001d4120b002412405603441d911010f4121003203041c088889107550780c1400f2228000c40380140c1031150a40702d50140c1e032032202900450780600c18090304070041000421000f150800f002d00540360201c8142007043c003d001c00c8a08070b0108141c41c0021003108200b4101621900c901c01c0f00f40c069150700028002ca50b0170080c41243c15070000c000300d81c00d0300f82d02c4501324004e10f96699150075915040c41030010203441b08604864560050182001c0c0040039002d0580c444c000f03a07641490f0404525 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 556815926 1250 556814676 556814693
    0xa141909021215060a05090717070c082d07030e09060f0d060c0305061206180a0209091006050d2a05100801090e0303060306010303050304151113140102030412 70
    0x10306001c00784103d440d1040b0680540303c08511500040f03900c940010381e508180504071a00325100383c001085504032064403a1000c000c241c0107002403030990441e1100d82c1e215542680300340c1300300e40185e035140e507081c003035801c101c81090390484052191414000c040d80d01404030000550444d105840d40c100082d02900c9008a40d0031642c002441d0b6000d44045040c6940101030502c0c0140004e4105400100107081103044002e00c0310850004001d0303035640543c0c4c4130f61540480302010882c042c0900600140c0c3d01c14124501440300c00c4090100449500010000c480003030340b001c2e0080d03034601001400300780242e56104404004000c04500725620560819038100c00d80c000310752081c0c8001042040c5a84840124140d40c0468001c018501a8403850344c2d03280021180a03a155110400600000b44103001540c2c21900c0b130340045114109100c901c0d816244010304402d00d80e41d001c1800b0b1110b40d000b03001507005003901580301481e0310f01040000c1d228031444c000c0003e42c00c03e10a0703e07000c020307440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 556817176 1250 556815926 556815949
    0x3030504210c02040e0d0905130b180a052d10080715020c0909030306010507050c040204060c0506060a0f0501030b0a030212070501121a091e0f0a14190902 68
    0x10144007400446010301404005000d841a0f014929040e4000502c410006001400008646030070307980e82d10b480e08001a4001d00c03075048183d51b482e1094954036071901d104210303512001441840c1c862801071071007021500000c003a4090904030301c41d0401c036861247d00008540c911100121010390300d010403003406081543c00402d0710b01c1043c000146000540a844074007000990070390341d40e0740d281400c1000302d110071f540c040c81d16001000465090360082d8010000e140c41a801d60340a04810070005040ba00154401400f00c0d141054102c04c004090012030380c84030040394815134032400c4c24070f02d40c407040c070b18043c07103040c0b540c0d500000e011507580d108480000c55004003841c604200c0d001c0d43c10744520703e82c855107011880d05102001446000d008820b480c0c100b40e480411002c1e41d00007041075a407005801590004004031484220b034489040607441548000c403074200c0d03410300c0b041d118200c41e04c121502240701808424060020002e0404080d0b507400c078000850810f96a00002e0425202c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 556818426 1250 556817176 556817213
    0x90a0c170403031505010503160f0c0b040506010611010212180304050409060605010206060d20010509031605100c0309032913030201111207030504060e0f0303180d02060403030504 79
    0x103203030800c01015071580003ca800ca030141e4842841d241e0341c00054481e400305582501c441210704c100151000e00c034880c0d40050817540d24240d180f003601600c4084a41406035025100c98001000600c103140c0c10100041d040741003480218541034000403240c1c00980e02030400e821001181c1100d40c0080020002d950283c00018010405110a0b2406d440208024480d041c0940500c078001016403424043e641145034110804401081c1141c09002c100302c0c284000a051140c1072282c15915241000400f80c00ca8a280c111101c1e941058100b1100844079042c44040181900000d80020381c8031010300700300c82c0d00c000840da080c15248a0030400c800c00d00c6018104401004c20000c0c1d04d1a0380d41c3c040c0800b8040e400821031131711420490b02c0070307101c0e030000c1d01080c0d52986c02050070103100c2c0c0d0050394064042e9030001440e041000025003480c5d11084020764690011041c4a85c0038481c154548500c40410010103411004020107512800000c00c0070f000d141d5507030b0016080c0103c401d00382c0b100c41d99 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 556819676 1250 556818426 556818467
    0x180403030b12010f050105030706230403080a050702040609150e1302061306080c0307051611030303091612030c1203020903070b070525261005010312050702090a0c 72
    0xb0b0340e51080d4001d150400380040e0082c00c01c1e000050501340414100b05030359480d078942666044c80e444110310703131240c011115410f0404010000109941c1c6010348000446940d48c0c0744e84081d5401040180c54103034000c07008052a00e1600c0e00c00c0c480c610002ca00311030261005900755920190254454287c0c40d1f03002c0e4001d200014201d11040c01d9401c1c0c0b42c2039800503201c0524507110045c1020003070008071410008108104801c07040d0000207a1614151440389442c1803c0da03609501003800d6400c00e0740c0048a0741d116440512a0501841320400549040c0c44041401035007a10f0040c0350303008144010301001c42c0c040c4820303403141c4039070100c032810f100140c203e40b103165440540d00c42036800140f090f01c1900900f00702d19000d81c01506140300f00210505013802440c03c00e841c03201c1031151450b051001c4007955903035445417a0107015000c0b0700f11142e0170000700c0d50726504154102010f500c12443c2007160410075100103030380785203030283c00121401c40050342d1b801c41c0318251031410703942103800900c41 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 556820926 1250 556819676 556819699
    0x3070f030503091c0f060b03030c2b0302090306043c0b09160b09040603050105090d0207060f14070f0209090105091b012001110315010815180403030b 66
    0x7000030060043e11400d480c403000c10103140000e1018020b01310300041c40122840c2c0b8a401054603500014401103004055911706980c854105182c540a98540c000840181a006140000c00140042d46420300e003010b500e0324410500003916402e000340f00030f10308200c202800780d1840d00c803500c2c5c0c0040c900103a034841510f4009203544882403090f680890b1543c0006000a07800d5a001c039a40740c00500803454082d54904182d031400701e50700074003001da400907619800040403c0c0e090181e60700a40e400c50107056040e002200087c1440980c3d0018028484a0030744030505503403200d000d20003c82c07510102070300c4074903e29100144840044002c0d51000c0e00009110081c6c1c419400240180145012078407070b0001d102c0c0f4100c4941c040c0c0b5606012800d080100b442003100c80d080c0c3c00c110244000002105070100803d03480c99001135485030b5101840c2101400c0a5070401900398103d890002002c101010420000d881d03c013000da0001810842d03000844e040501a030003440301c04070018602151751 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 556822176 1250 556820926 556820933
    0x20d08162a02090604110d0b150a030605090a0e1b010203190305060406170307020603040602040f030b0132010507060f02220e010e070503070e062b0c050a0e03070f03 73
    0x1460340c2100b6032003822060040742d04d619007803180070000044940b9160400604100074802400000c0c40c1d1a08100c1000c0780c0c0c201041c040300241441c5c5455100017500b00c0c145400e029840000401900c003061030948844040b800025500441d9080e404043c030380d14020381c0040f81035019425804480c004004d81c904c44081c0c00d07800c06480f8002c1618100400c95888981c00380c5020145540640341d0010884030700542030240043d58854021407000d840d05a642d00c00c2c845045159000341c40c0c3c0010f40005020002d5804d684070074010403004202c2d1540c10180710003555090400c034060500000040c0041000050f4020141905001204644a54030340d41103090300c49210100c80c13650558403070003042e00141c2c40380c114183c4a4645085150744d440040554195001030501410b01c2404d9184c421260b880c500140102c1c0c4d454607400100a5500880c4a4880e08107104007018600304940985019071200556510f5601d510b85207541382d5000002c2414860280c00040040800e0140032051 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 556823426 1250 556822176 556822247
    0x1c0203030a050a18062703020d1415060a0b090123030912120a02070c0f080a03110a030c06021b0708030a08011e0b0d0e010f1b020d0816 60
    0x4800c184d4403000b02c4044111140b000a14071409040045840c41500350310344001e20b82e12026174620b04000d1180b5503200d40005212003070214084418070307182c200e1908d01c40e40905c141141030741103510700206400c04000158409a030b40c094020800c80c00310700404140c0c0b02c0c0301400d0400410007151083c02160741c1c4842a1980704490350743c0d42e8400c0c80003d002c450a8481140e0aa41c40060010000c3c0c41d20444100690f1148a0588015440300c00106003050100c003104020004a0010601d82c10b26140140c0307107202098801c4c4003608048404400700b40c2200000c0345850b0301c0600140e4a0000e4500d01c0742203280304038400030314401c540c004103080c44000b0091031441c510b600c03202ca1507a40e80c4404c8081d194407110a042040f0107800410148d02c1d900007404800200c800c01054000c40107602c64215596680c1c103200d1241c407000c1c03e09540c50021400c1c158104980b02134003407402c0700c407009488044080c000381c440c002035400c4030fa4007074821882504081d04106455203040c03800c3c100340d083c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 556824676 1250 556823426 556823437
    0x1141b060f1311090622060608060603070503040201080601180e0a0e01060503030412051009110a23060c071a1209071a0304031211040806060f030a021c0203030a05 72
    0x4036084007901161042c00000c002c210040d80c01028080584155414880042005041641c00450041a9018140102200c41c100c10316030400040c40502c0c248000b0030024000d0260f03406010100240405568880c0890303034031070f40a00345a00c8a0712440b004aa900090417009420407420880c00305040c15080c94aa000301010703001800040c4070030070501d0032100d0511420790705070b10802c0200b002443c461140c20500d4010b070245c2e0030400741314090030182c50315041e041310074000011618090b46080750a01e030242102070490706140c01c02e2200980c0f04060010300c548a8100450001101ea104201c0c40b170140c42007400030203082200140c41c23840781e0040c0b4a0082e00291040000310f900c040007403030743d04403154049040c5640312242c100b10304a034806002074081000e1540e1464951501340111540d009500345800e6403246000b40c13443c1080c3e0054145407044034141400855a0340c00584110401d804680103010808146c030107500c07901329000300940502000c1540c001c0b46030008040d01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 556825926 1250 556824676 556824691
    0x1e1107050c0a150f1e0e011b1104091b09020a0207060206091507020c03060916090902060306040e0715180b0a0c080d020f040b1305091501141b06 64
    0x1040a03814204202d42c00e10b85000e8210b40003008143e24403098801d00800344001c201c3e081440000311802c0480c0c40d030183e2030390001e0100381400c40d400c64079648402c41c1010f0030b480e2580c800707402d9081d64940d2056003100c00d81c9403040f5154a050302c140000308842d40c441c182030144204290750b072807145601a42202942d00054003c01000041490000c107540d4071a21850014040e9030b200400390354850343c40034240c3c404600c81c16040c1051030f00c040003c10f028118180040c1005414480c42403058026900900300742810558280010307140c080c04e8030b42200c4121400320b040040d184055290002552004144200300704041481581001c3c20011410480710451001611544504e41503c1403080ba1000182c286001c480814010b80140003034019008000d40f6118803400d8200302c540103508141c4080c500003130641e450391109210b2200800041d030340342d400c51920180040812501c0040c0034103000480c4481c070701041c00c020031140340e44141d0303601a08014841c1c4960b56544402c89040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 556827176 1250 556825926 556825933
    0x1b1404051c0b1308041e170c040f020a0c02060d090506010b030402180408090922080c010c0c08040b0a120e030705060106140703140c07030b0f060a050a030201031e110705 75
    0x19003c0e9146034981210180c003c484140342c14035107442441c030b501404845103002039090a012a600d84010703985800310500500424104001108101c00c80f41d50106004e002881089640c2e00d81d6007009404c0901501110010344580c0d4010200002d81410f200080c018040c2ca00081104085071001c1d600483c002e0f1a2107920710a9540302c2d8101c0031090380d02500400d0140000490340c54a010402e40c4114041c00f1040e00043c003885d0728100c000070144c100d6004102049840ca00b500c24400c0c0c2110760010300c0d0054018001e0f4403500c429200d0fa0045600c5460000740c5072007490b000341841d480c0300074010010400e03807500850660703c0e5000b88804407554050100001000e500c581c400035503d030414012580381c164a554241d0340c612200108000306081070201034030700c44091041c5401036004140c5185145495412078400500081c1400c0c417524880006000316101d070904201600e0b42800e0000b03050207030706001d5500d6103000079180541403c00b68101c902140700009000440d2054044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 556828426 1250 556827176 556827181
    0x50705070c08070608040f170a020d031b050307050307091206020c060a060608270105040b180706120b1f030c0e0604140f010c06050a0b010801091b1404051c0b 70
    0x1640e260f0440f441080d002508501c0824041424036000e294580d2041c80c40c80030082c0a850b10041640000c01c07800c0168100c220030f078215a81600413100b01800001c254030b05c80ca00040c01a0203400060405c0040000110001d00c0643c0540c4d145c80181281131201c80c1034480c1c9140c410041e500615464229004a03404200004107500810007950f000780c076580d0841d501c0c0c40c80c105000c0e010300682c6001d540d41148a0b144517000b8071400d80628024215041e403480c1c044200030b005030911444001581c004070081158651001d1000b06600140001041020f2030304001608501540015141544901e411200c0b030358055101080b04030b000e40b2100701c1a5203403000c200c1d05014a1082d082c89407222001c00310341c1c1c5081e0000003d0310708141081d40f0001032030740f00c081c00c850341100d401e960741d81d6902c0003508640c1c1162542c0c2c01000340b024140007a02815044540c6005407201e4903007070201c20300f50151924020000d40d400340201414008130041c010150380c20b10b03c094681a40e00c420b00501 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 556829676 1250 556828426 556828439
    0x9040c05120c03190828032d0c020307150204080d0503010e04030f0c021c03090609260a0c09020702090f091507090503030c01050a0606030c140315040204030f05010b0102061308070206040801050705070c 89
    0x80d030343c07a5406075401d088c90050710b031360030703040030300070b07600c00802180400c100210000e800030b00c50f456007032070740040141c42d1800d00d00720502d4110115080c4050000c1400104000000301d458280d00643c507240844180e0146501600c03904004403009500c0712013510312000602c08407058604090181d070390120282c0c3d0701d03001a280e2400034050204a0703a00742a5040c0e0084440201640840031502107500303045440d240d41d10a10700f260801c584094000584030150300c3c2026499401011b80c0b00d00580500b03110122980c0d4403460351890440c100d000f0009003002c1c0c01421404001e00004e010390341c0d500000007c183c002d000844901c00418034024001c11040d200e44503013803403120b40c3c4d10303a008001d00515141040c3e820051001c101040c840414003825141c0703001400c021841202000b460392070501d006801d541c0b80802c070742c0c115800709003000070f00000003400460560f0046c40303150b5030341400d00100c1c3d41c500c0b40d500030364190740c01d14051000342030b07100c80203150b51800740074003030800c645411 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 556830926 1250 556829676 556829711
    0x9030206072d0c150204170d05090a0302040507020c12010b040501140907080a091a190b130b121e070609060e13090209040c05120c0319082803 63
    0xd051034002c866800e411200c1d5800f90344001d1003507008002c04030078004054040e00599005030400600101122200010b106080081600407281410641d04203881000400e021010794440648520781b03400100c0e001900901c05002c000c400074040600758440c08480b64064210300c50150300580c44d183c00000c405060507070014009200502c0302d01d2903112454111860312024103040d80c4541e45440102c00242c41607440d01304040288400c070070514141d06130240312010f40f10100346c807a0030061201ea0303da5031102c3d8008032400850001404070410008140004d40a1540380018401d40840f502d03400b540d0f030558041044450102c600c940e03180c02c03041b1880030440c8194800b141c1003c030103c10903d03119207411080ca01c88200000d4030034071a000100c020b5810b42e4159100d070f10301c50060116061031140c401180240b10000c0501c4100d1002003551030545d00c0201900206000300801004001021039000504040c1554401d04010701c29110150703901a01e640400d25281c00c0e1500b011448 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 556832176 1250 556830926 556830977
    0xd08240f100801080d210c090810090c1401170a11040f050901120807170f07060e010f0c02070905060a1508060f010e0102300c010608010605030705090c0c100903020607 74
    0x900300e5003a1b00c690740f40000058440980100c0a110101c4400b0890903820001003500110303181d400300d403144071070405541c00324154101441c0121301c1e81004170240d03040f0f00ba10841c1c000100d188a0f05035900c0f034422004000807851203400c4180003a001808090494505d0148e8000b02c801c06002e99035580386580080811000900141c4184020b0001c1184862158190485080181d24200e5200c042d01d440fa440340703008403400750391a1340219182909111740c0300e16104049080203400540071000e51340e151113120b078020880d00c0e000000d0702c98076105181001400944201300c1d644a0080b07028252501c2190b8031802002000580740d02e66100c0e038000c89a140701a00030b82801c6444d464500080c0c00d550840615003007130000420102c0a12500800300c018015000203500c1d410851503c0c20345002ea441140f107031384640e0060095030384178035509070803400410620b6510281840c84605101d0300d034a19034080341c54101c5600c01d05401255862007070145540b031000300c089400c18002054203c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 556833426 1250 556832176 556832207
    0xc030e3304080712150e120d23131104020d060602030a080c0711010c0f081b0c0d050d08090a0b04030e01030b04050f010b0a02160f080d08240f100801080d 68
    0x4101c10a01c2c805c0556100035000b00304c00050750310440d0042c2d61500f46500000b07240d11050794816018124403660441884100030795085240203090550f403030280e07104020300c083d1100341780d03141c143c0413503039168121a4160303180f0704148803841da5500003a4413904264031581c007044145000503058003c440c11905900d82c040322600111010070011a12014204c0080301c5151018402c2c0000c249000f000d0038030807801c3d2401c1d4402c2400c2c030140d1814070b10b82c000014014411102c40034005030002c60942e11441c101d05d0408a241d4403e42980e00c2d01c103103c6809001c4441120501081c540d100c002c00204480c280c03418002040301d80c00b44802ca82040b2412652006520011f1004640c40f80051012140e148100c440c540c4c610a040085020140e10065403800384d80c1c010400008240040d405515460500750401e01d01144031001e0402449440c041c2d00c0d40320004403a050b0356038004121001409008008143c20381800945018003e0052041a20500901540003440341d844010807005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 556834532 1106 556833426 556833443
    0x20d050c0405010e0117060d0c0e0703020d05011d01060305070c02040f0b0315100b070c03050318123c0a0b04060605010c030e3304080712 61
    0xc0e0404081c180107265901d015225611289154800015034498103072380c0c618070b404c01083c445500403116400b0600c09203c0c1895055016114807071650314104456621040b138041c00b20071302200c2c46e014060100061107624800d81025401150b6814000003095041c0d00182c15a80e840484842290355810b031a0740b07504e01080382c54203510313244141e07905606180340e5664188006004d26107010300000742900402924100680040d42c001042e0703500d1361303032003140c0703410b1468000c8215110302000030040b009080003080b0032050700c65280c80b4042e0704c1c1c80745c07003482c400407100d2480392640080c801d64001036484c1032042a000c180300302c46c06081407a2502d0702d001101c61540189041001c4078044400181c0c01140c03c1c42c11040c00c9492b09138a0f0f0746490324003046540c40741d401085074601c0260403481c801341c5024100b6a10423406444445444010610002c104940050312101 = true := by decide +kernel

theorem cover : BRFrame.Cov 556654676 556834532 := by
  have h0 := BRFrame.cov_init 556654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 556654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 556654676 ≤ n) (h2 : n < 556834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
