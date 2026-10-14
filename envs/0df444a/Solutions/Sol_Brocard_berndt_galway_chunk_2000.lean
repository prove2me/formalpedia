-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2000
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:25:15.959885+00:00
-- url     : https://prove2.me/submissions/952e7beb-5741-4355-90b4-ebe7d934b0fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 359532374 ≤ n < 359712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 359533624 1250 359532374 359532377
    0x30c090904050d14250203100c021506091608071b29090c010509030f1006030b070201020f12090307050a03030b01120504020d0b0c0d0c080f09010218123307 69
    0xf400001170803003241c020b0341100c03441c4c160740409071181480402e1405098110803214a4100041c0c0980369600080c0c111a250003035040d00095140c45050004040c0182e0320310f0440d1b00100003101944d07016000d07294000e100b52414040248200800da403440ca400380049503000801c6200800e2140c5d0508028a0708000066034691410038100542d620014006c03a00d06000010400c1200c6076010710281e000742901034142d5204000001503180104031500003118a0880c0c10f003c43c07600e038414800c0d100c048400441207482c1040039080845488001080c03111135200401a0400140c030900400390f00034403c0d20302088465896001604a602e54815000c01502d880304001c05607443c0065800b016400807440015510750415a1480d44503c0380e1480d076150a1401b2501c10035800f01c01c2c14450803a4202c00c448036124810b09034241e01c11019450b4000c6000205400e152034801c891402e030b0360fa404100c0e8482d0510307002d4102405d40300f064950642c040d201842003111145600d1755070200c3c06 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 359534874 1250 359533624 359533627
    0x24e060f0a18382b06020405040c1704030c0c030f060b01030f110906030703060e0c07020108060108040f0b0c040f0602010615080601080f0c0409090b18060912030c090904050d14 78
    0x29190a83d01c54120080300d224182e0f14012260111204d1440c06807030814844c0354040115600300000a503005100d92070180d4503110200b0a100c1c8502442c071311101032008140701c03070748443d102118002d0407070074103940c1c1c840c003401c001000400b155418104203110b030002145181140e40050210384a2140c00c4a040d13003001c401d0f812525602003254200c101c2290602e40300e885540c3e04030000c3c41c1c5500f114040c2c075404400c0c0301c000450000680791140c400d98660707041c1e82d0f400d001100c0d44441541c00500701c03403100285d01d000401907400554803800228140d828981d4500782240d00146651100c00541d5690703800388658900c0c402d03200e008001c40e05000015007800c800091a80c88018800a11040e59001080004031400e080307a0041c0900d40301482020365508012526003c1900e592401c0482c0314003020003903402141092242c1c881ea000307081c0c07001c1d140458400700c1d4402008945440c504100032081d80c1d4510207410f0040d80158001e0144a8041c88041c218034100f806800a0210 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 359536124 1250 359534874 359534951
    0x4050a29010c03080c1936030f062403050f070e07050304081c02090f0306070206011205070e13050f0718020904024e060f0a18 56
    0x204012250380c1154181341500d140d689451000340c407402450740c950562900503100ba244c1c10f9002540607070006c4000d0900c03c10740640030180009080144600201089145040010807080294080010300803c4041000c52200701304040b06200b2480c450302c0c40d82c000005000784402000070484180e4064010b209050402480306010f1a0003840e04042003400000202000000c00985010880c80c60900740f5403c038401c09180690401c40306540950b42d0415401410b01c1c1c0021060300850050300031b44200d901b09607103403a8880d031546050312544035008001624411806100d44182520140d481c04c0c0052490140e0170310114103110707040ca52011a0511440031024401a10034a40441c0141d41c0c011120105002c2d014000c2e02d4002d036100c0790302001c03d002903032070000d078006541802c454400c201c4600480b51006503442690103d0000c200151140c01c22200c1600d89070401020803503084c0e81d44050314940345403a4500801191580f41003803081411803281c803240f05074024900c05450 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 359537374 1250 359536124 359536127
    0xc05030304020906120616080a141617130506071106160c0b090a0201030e01060b0301120c0b030403020a11040606051e040f080c100804080403110102030904050a2901 73
    0x707040640f1840840001c43c4103941c854500120305c078200d50586035507240084260b1440d0000d10400804600c50800062644e040d520071390b0f5801c02e40d14174001039a2140e03c03125a1501240d0070070300074040803683c80030300c0b440c05c088140d01c41c07030140c41020514141c2c0d18286040c5440980701030244020f900e50030321805070114055030310800b0049a0244000b080e00d00b200c2c440101e080151100e2040340a110714000089045a1030a0007a20180b0445078624005400c0761030503c5048051a030510060220306582c640d9a00e0340c43c01100f6020b0b60b51344400c0c481c02154403e90741200581c0c03003190f0b240100320036079070903043c001001c5a0800c05246040000341180c81039042d91010307460341c10300742c00e00c405140c41580c2c00b4000b5002e03004d8a00e500c5502d0560743d802a6040d071031284661082202503580b04040e0301e8804caa00100d02c0e41800d00c1d5039200c0103030101b186032984c10360000740700001168813544202442202050004190400044070316071912003251604000d6880316108240242d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 359538624 1250 359537374 359537377
    0x204050303040905131e02010206060901140d080c030c1f020301030201080f06040608010615090902040f060f0903050a1a0702060408031f030203121e0408070909080d1d0705010c0503 80
    0x981c0b0f12040418155142d440c2400e5001640c5001003040c20102c1c40f0072103070b80000380b43c5d1902034400c1c2c0841d01c1c00e450700ca04204134010709204640c2c1400b00c550138000c0500340041007200d000d10551b21a81894845040d03541035812000c40144c0550244501859610350741a8031198805603800c00c5141d175040d500001e01041c002080740405042c100c0220391180c0307030355121714020306200c0d000f000002e80301c05187c05032a1400000d00c0c0041c07440107000ca81026140700319411241005404502d80d481d0420a8602c1d84e02c91418206101c50003000101161081c82500111845901120082078880000b01c4081002130f200e0401c40d803240c002c110018000d074040340e4001e40201c666034842c02485042155595540c0c00094060040d01c80c03e40c2c52070707a00809040c0500341081b200040d00c1038000c00610501403442110101d91008004002e60040e40e400302108502940b00f4500d0181c25039110f8056518030b01c0103c0968122048650f2124014010940034180910700b40c0360100143e100c0c540e40703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 359539874 1250 359538624 359538629
    0x207050d03091b0e060f2d0102120408060106030e0615060f130b070209130804030b070905030a0309080c06072a150c030201050c0412060f020405120303011404020405030304 76
    0x40c1a0303100420001e100c0550407000f884400c0c1403c80424a80355404031138100415101c040c001d100c021806056450898143d580000c2142401074100018a00c840311401500c0c42c05410360142c0041d03005a013203020002c00207010300c040100b1041d40f41140050844864149010294214900340704400c898031680d02c0000b0000c40782c4035124107802d4000c3d02c02e03105c1c0399425000f10190250026500d01e000004c3c180d02402144e5400003582c806200e011810081c800090004000f08414000100c0398140c09400820741e1800d15251502c50000ca841c10300e81d881c1c26008107205800420044100700008904510192845400e00c84a9960340c03180b218410703c03140034280d1210a81000850600d1300400a200742c20b516400a040c1c40d2002d41605402c0605400550034400040e4000061030100e604840c4000d03201c041c22561911000005c002c800b10309180c1d02c1e001c02000456030b5415010540306024200a50303569450300c1c240c1d0540800a141085c0540c0c0144000c201654010065404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 359541124 1250 359539874 359539877
    0x30301030c080d080702060610260f060f090a0f090b041b06021b0f061e031b09210a0512040807090501030c050d0303140103291006030e030f0c0d0801090207050d 71
    0x41c03d60154105030f4811080902d00e07409507070007041080c003102109030174ad80212422040c49100d0707140d16081c403054444140780b041d00301e02100041110501660700684c02000d02c85000180e41c0280d40e106c085201090710181c4295480910002842c401c7c00007000c028035241c001070200a03454a403684041c0800d01d00345106000e802c2d541821505c64400721400240c401e0030391103d21050602c3e90409070825079003d40b2a420303280c40d00c0c070340c09442c0044400220009001082251505010740b681105d00410794482e03004040414000941c10040c0030001800358039016103e60070a07a011b0328165084d8401e400d100c1c2040010008502c00141c2c0009540f000d0f218803800d0314090805601800702c01c010460501a40700001040c00b000c3c0501110300300900098048600c490003950b50b400f80162003150b410151241c040000600960140441c114003030f060b6410802d00020104503030300040d0000f4640c2d00001c0c1011426580710020070301404128000b182401015140c66513140c5145c4801070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 359542374 1250 359541124 359541139
    0x60f0507060906110c07090917090d060606020105090c0103050411060a021f0f0c0c0b0c16080c0304050a080f070b090a050409050f0c04090f08030a020c030301030c080d0807020606 79
    0x740708094022200190f000401803150328400d05401c00958402c20844015002d903000111f40254039000346000c05810400c01070344429202c0804005600c41c907003903540540c00803200e200240060042c1002080e542e000000c031450720b84202e6051003070b0000150b0425190008000c00214810b0318000e5826041c0c03991a01c40f00c0c000b400360300d030120900140c10728000b0544091400310098021200840c1009401e0000036a004400ea410030350300a40100000b560b44001281d000b152000761000d4419a5260200094a0f0300d03010219445821708900c40d1708002424080da007861070f0490018001c05004020408044001e6070303e07001c5502540c40e40ca07600007000401999019440d40c05840002d0081003d4000c07450004c0d56082c0041c0c1c82e02079801013030f03e04181c2c0e240501c543c004d8107811000281c00030584e41d0b18038080e40c0c00100840101d5a0911180300c4041c002c1009e180618480d090b000d52290805210500d4107480310807040400018501300541c4944c0491003d8000b0400e84010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 359543624 1250 359542374 359542387
    0x31c09210320031b091206040204060b030f130c05130209100c020d03080a1b12050906130209041505090601030309050d2a030203011a01120e0d0518090c0a030c0306060f05 75
    0x44203144901c041031541b066800300001041d800104115000314801c41e002c010b42540c4a01181c000d010072142c0044513080e01c8005007000086001160805100e03c000c056000d4803400094048040c1c0791510481540c04200b201a03820311501d10440c0714424148400b1460300d40d40011070901c50074400508103d0080c0c0854403280c0d03290480c000d002c01c03000c80c05071000b15a4500034003240c2400f110000080c2840d0208000c00b00120344103004900480d00a4195400d0b5003d0084114000e0000c84013070811400d04416940c80344a8a03014005000141a5a52460500170702404460b04040c0c072400c4071207440d400007481c008100314182c140c05940c28000000d0803081040d081e00350310203501075080c14001681441d400210035a001d900b41c81e8050b21000d80c4541408660300748421100c40d0f0711203110181d295001e00003904598090505c2c06e0440c08000c0302240364004241c0d01c43d04100b0740403d03241109074060240c40000182813804003c0c084c5029402403000e00c0c80031030181841000030700c0c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 359544874 1250 359543624 359543671
    0x917032a1203041109040309050d0302030409090813060311030f040f0f060b010f090f291201030314030f071b02030a11030d0c05031c0921032003 64
    0x144001026010141c1d09285948048680d0715031080358102d603901180344401c1c2040c6800c40c1818082c0d50103554480c03106d400d100500142c0c415440c4143d05600c0305000000302c501d003030f010354440d0900c030301401c68607040c0c004c41d681d0008503e5000b200502d4240410a00c02000d0315050340d50004071100c40024035107450a00d0201129403541c06060120320301a0101030101c40e40041c12940805e9851010043d14480c0c01c6405043d01d004008500000050801c413540850030502c154104500c1e0442020324013a60a0003694400d024044d0700d520b22030010010715801941d071500d403080704441980303107140134240f485001000130603200910148a6001007100780f442c0b001150240e018040f0b5071503842d641800412055a00301b014801d200d0790f20101d0006100394800c8003020f50100c0258181003005d0200d80e01075001074691908156640c0904001c14034442c03520f4442d0f06410000d4803421441c14004040c0c40f507541c40d10002c0c0702481d000c0c401a600c1c1108982d400880024143c0809080300070303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 359546124 1250 359544874 359544937
    0xc080d41092505030a0b0f0a060303021b1f0909050604090203032b2301080a030815062703010b06090609040f060305030a0f02010c18031407080f0a0201091703 70
    0x103d50b4051183d0b01441041113a03081c0028080e11161540c14900e6540001c2070041c0e40c0ca5000080050b008040e420242e41e2500903007444581c0c0c0100700700c801942c59480d0f4816003049001100c00148c410344200891201d9100b000d8205030b0544003404a0700c00da0700402c0c0c2e6131041e54592101d8040c5809043d04020002e034000725a00300070802403003206890700044d22460070300900301050104000c00040d14010009150019590513100d01280340d0b1902c5442c054000d541c1402030b0080e00811441003500407a450213001e149008600342e10242d07910301814210b40200ba40540628000c201c40c401c240d41d090282c624001c8102c40102d440d001c1400b8000260141d070380010010721020032070000c0740360001d90440040c0030541c02008001845c1780101e075407403640030000e100a1202c580a001040100c0a20b102c0c41c420305044a0020340c0e1028128070b0015480e46c2e000c0305030001d40c8072404569000c5c00c1c4100521185881d0b080515a5071107250b200d100c0c28044009181250b070000c14514128031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 359547374 1250 359546124 359546129
    0x1e070c11010804110616020301110a39061a0f03101808040603141f060305070314010e1501020610050d050f0307080403030305060409030c080d410925 66
    0x60101b07880700382d030301c5900b05074540f281c000300e12a50070882c0c11240ba4102500740d03a41307164281d80b500619a40440100d040036108407181e031800750746002c0e0718840c801410130145110b205240002e03500340e0200e0b000305042011081180700d441044001c04180e9000100f003c01c02d503074a40c0024907007100504d4403045261181c0010003000c004180040c440c1e4140d842100790a400404030f40190307440c800180050030ba091001c01c03aa4401c111300f401070521944c00181d000640d070400044075101030070b030f40c18800001da028100038550242041905204c00ca030400000f0828002001107051403c0840410f5145008960040c5050900d07041844810440070306101008026203944940f02d05019401d9401408140c0100742044082542800d03d4800c100e0340d103406a842c1c3c61102c51a54605020758044070101c41081d031a003240920340c6001d0076140510700041c1444009400621101c92401818102540c500c2c07940c120070010301c400003182000c0c1c211840c110780c4040f00c4003003000e00c1d00d0443d80e4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 359548624 1250 359547374 359547379
    0xc03100b1e03091e030a170c0f0315130e0c010c020105030a0c020a12090501090b0405010206070c0602040b040b040915151112120907090605030a030c080405091e070c1101080411 78
    0xe2a80c1c00c0700c44d82c04001825031014503560051090010a803490300c0b50030599040b1a8100f0421600c4900d0221a01558000f01034840c4041504071500c005100080c0340391088402c20f41d03403101500110000c01a440d201c15003824003140c041c41a0700041c18600000305170750501c51b1183c00003041343d4424443d19111aa1200c000c0c3c0b5040b4411074000c4c80c02070070b4010a40031070343d03081010a50129603410f03902100e405a00505d8070382c0d075080045810f060100802c442d059024071001c2002c2c00c0c000050405030880e01042600c03645414291000d450000020301400c04c01d5043c00d20a03c0c3d0138507030702800030001c2d042000d812139010143c186008520030765a20324003004a10015a2080e800055029110580403144030a40b0f65007904121080c1d8402d031070b41544007665510000e40210820f8600c18081e5804600f0159210040b43e001201114161500d20000c044269170071200c0c401145c100000b4540b01c001015583d607000c0c03400781c0403c0400d041c001c030340001408002038160b1094100801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 359549874 1250 359548624 359548663
    0x3120f20160611030403080105010503040c0b0c070312030f140c040b0c1c0807080a0c09050f04110f1b01090503070f0203030702040911150910180e0c03100b1e0309 72
    0x14148042c0f0b29042514118002039203100001071942c40380007500c2c0142c1e00603c0d81c1c2800c41c5060103101290b801703082c940c071841c05201c600101141c0c1c038143e2032108441545003c00c41d184030248060841c0c03204c80400c42c000400c0301c1805101c44010003582c3c140c400045145a480e540c2d04202c500d056100c452408c0c040054030a51501c06a1040d003c40c00380c0105d0304c07800d2003612071107000d1091b50300f01103100000502c805030801452500302c02080743c64802900020b440c800e02d051600c0039a202440203003010400060403ca8030a100c2ea002484481900c020080410180d4450707440348182c00024005000c04151201595011b00c1111a01c59000700100308410b80b42c64604225521018958400c50708424040348000c100d008840b41c50200902c540640c00e0301100594292184200c901060021076001042c41c003403002c80b09000d0014000078a40ba450010a190f148154035088160307030003c2408131074030480c0d0b25400b0f80c00c2075110380072060302e907a25440d17420300c1e041ea46404011803000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 359551124 1250 359549874 359549891
    0x2040e071e090b030307111e030f01060e0117030a0f090803030403020a15021e0a09030512030402100f020d0c080c121201060e09040605150402040303120f201606 71
    0x146121144120b40340030405001000e0501e0801d6180d008991014080c100c6045c410300c420b24004e070048070301840020a940c0f2070790004010919010250f903610149070754800341840030b03a0000c009140101585207074100e0303503541c0744400d07a00c9014030101f620602c040315442901145c0502050710140031401d044a40380e240c0f900303000b96505440c440603121360004480c2d00701d00300210700880d8000503244c480248074041c00c101d00032280d84451954010010701c04404000201c050120f6031441d06074044086d224142801000038544440307181e0020300a009000207501074000c02d84102400c0982400c0b24064803c4c203080b41c0c507209400f03010041f40240344810181030011130140907000745c0510100c1090b81c80c4c00080d01c10b1220080507507400240f000000340001c0c011340000d540003c41e20421898000c9050205e4144e800580080b408a85401003402500c0c190f0320070402007420b000c0081c09880f01200f0000c408001c603a0502d88462800507100344108100c5840941d5181d024104028001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 359552374 1250 359551124 359551169
    0xd0e0a0f060b090114030d0804050f06130c0b1305060307090b0c030d0b0603270a02151b210c070e010b091504030b1504090c09060801060f08070302040e07 68
    0x40981c0c80c043c40745003000008075000c1c0c501a084400035030081c00400603040d8000b01035920310401407080b210352041c441c685a24990910142c2d000c0c079003000c5000103006451511f201c49403195003140382010002d210810856491980103000c4410a80d00303242d580d1507216040340c40d5425908800ca610400061041031248008002c0200c0380442d481000159070b00c00400032988801e0381e00a80c107200c0c4000070f04000300804c8441144120f03813800c440e02c1050650210300b254000b5070107940c2c5540c010403c0c9507201e4046d5001d2140f980f02001071701203050b94400e641d2402d2544038038403094107030201d41ca1720080030420130700c00986840314210107651382d911030030344041e802070b2002e601459007400d41034403520004d015101a80d50040080300182d9600b09110201c2c2c801e420031075401516200342d5400308000c15001c00280c00039000115045003015071160940e205a480100c40407000c14080158072713004101941a81d40c110350200304080c0001c2e800786003d4694112440d400100c07485a480719 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 359553624 1250 359552374 359552381
    0xc0109030f090503120d020a180e0402120303040507030336080f030307090e0406060b1801030c0f0207090509161212091211030f0312010321050d0e0a0f06 68
    0x100c16942c2c82c02d40c0300381c0b40c0081c103440e003141034400d68001c41d0034003500036200c017203801420311303100b40d49840c8000c10101a00b040001446034482c1c500c0084e801c0134001503041c12100000d091031640011071460a150341c649a075200144005410010100a4150b407a42035101d02e0380000212110100d99039503440ca0102d941801d03201c4c50000d8407071140d0800001e0307004400e5910680305902c84480c010300d40042100e5070100200200e840d603543c0c007008551384d00000c0c082d00e040c02400040c84018000c1c1c10015003110510900c00c0103120600c1c0c2601016a4001440403d0380c410140c04501074848504282c0b41202084203080e00c28490700003c102c400216001e80b9426001c0c004000c28171828000c203a600309003c1c090500c55404025230040400c0002075090390010003d8221040340c442403420b1030441e0002c00f00c1c0886183c40000403c24484080714111040d80c1044a00311207950888011341680f003040c1e0340f0101143c0b500c1c5024000f5505210700220b80c1e400018031a818285440c083c2c005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 359554874 1250 359553624 359553647
    0x10608060915010f06030b01020a02060f0a030e0304080a110406080f0a15050f070c050f0639091e0a0902190903050c0d0501020d09060b09090604030f080c0c010903 72
    0x154464a280c110304450501c403168100e41030880e1843c1d00908105c0c048001d481c8040c0c40a043d4452040702c42c0060700c0b40c40050501041d98107000340c0f181241d0000806441c00000805c00580c0103201c00e00c10144085403900f81a98000d650009081d10440480c0c050031142d84045500d00036140c2c0414008008a100d42403107104000c0b80c072501d44000b292000329201500c502c0c0c4440e041c00001000f4500a01160707085074050412501481c8a10784031a00c0d01200301c0f500703070078860a641e001a142903021408030201d006004580c4150200c03e4032504240100e031841da00c24a1b4101001c046800110340805a01902070805840d00c2d4640e500d0304040d5101c112800c03100e584408007904400e1043c1e0844083d6548803002c0c01e00103902c01c0802c0118185514161440c0d50708003c01b88006400303203d1059854400c0c134000c03404088800400203a00002000b08040c0e800803010000001e500c1840240007507681e003001d0041d40c607034550070000b41c003c01c03d000c0b04562070011040c0c1810707003000c421245c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 359556124 1250 359554874 359554891
    0x313030e041530080304140f0d0f020a1703040f060f0221090c04390e0303041d041104020c2109010519020a1505010e070507110f011101060806 63
    0x24007590360600030488110f185400700082d10b010b1142c0c0054155001035030050700410340c080d440003900aa00382405407007400300f015907002d507401241650300030140c032506007017038009072002e500c21b603c0d0710798940c2042c0c40010700c2e0b06001000030100004c802a0400c0310342c21050412841c0c208041c21300003076010050741108070505181d02030648075880309262203882540c024042c4000349109000c042c281c2d82030400340b01038810002040c080001040c402c011001c07000c2c403010700e400c0804054905000041d005000703070404c1106001a01ea40c042e40e20a00b24000d02105056840e82000450003454850b1a507203c0c4c0001190041c20b500011982c50110345944000e002e007048401c13502c1d50f881003912403808a1030521036003a000d10f06003d140031520250050311180c8082d0740c0d070b8070610b0300914520039816503a03070018051032800008859001c8101d00f0801d02c3d0074850b44039020080500307840b040c8628030340741c00780d0400d92103079400d008031325968002403000c161600119078940c0001c540307011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 359557374 1250 359556124 359556149
    0x10c03050f090d0305061c05060109050108191101091d0a0501060f200a0b0f0708060a0b04090b151605060a150501110313060924050313030e0415 64
    0x85001146142040c0a002d08000034188100c00c444180d000d85002000d070380d0712101388020f403003913400607031981006688540041c02166040c0f400c03440403108103030000445a0f02c401c1e0550342c3d02c0c2c0400c040c404401c0d003168840c0010001000104c0398400c5907040500d40c0c2050b0000004400706101c1c0d550701507000138806102980c0c94040440746610b100c03006000003405086140c1c05c030b488100c001c03026007410300280c4500304880c1e00c4a42c810b803020f4595003071f100300c420200035001e03500c159100d400c401c086070109081ea00d00104408640924018101c020703599660000a5581c1c403074400c0c04001d800c1e401e10740c5844c900d11607841411020001a5640c0c0030361000100d0524251041c510181c141001981e10303181008c0044480707404d140c0c1d03154403034801004a01030a1801c480004010500c0b50303205280c40b070820a52a5424003c00c0b04440f244080c2d0308128203954001d0113482c2c0c00500101c00458440c1c940c1000c5881845025016030003d01e07041030050084c007202c043c6030688040e0782411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 359558624 1250 359557374 359557381
    0x40f14040b03010e121602030f0d120501030b010303030f02160804061409091303090b07060204091b0207090f061e0602061305101805030a09030b061210020c150405010c0305 76
    0x5403c2e618208000c0805400070b40044111034080705c06401c2c1260385403c406800200c50740803a28045010788030210f15400400a032403c6584102c035803e50701c804680a101c40e500d10341d924543e43d070060200a041c141c443e20f08440d50112a410789007000b09015017020030740d1050500010590107405001d0018020a43c040000400007045912810780540403100c2c59441401c0004003955181c4c00320108030002c1c4001a0b0f0381c4400015107115405500c00513911440d0030000c204940c9001c101c01810480300c40000c01c4190086031302d8080b00c0085c1c03000b0a295a440ba2a440100210740200c0020a0002580840700d41c200700d407482030391210b8084403000d4a44103c080748135014031000500540c40b080b202032484445400215480d02c2c50410081054200d90b650f5007182c0104007100001880104104140039400c0c600903003000e0305442c40c0f60500322155219840300384070082441c400d0b80000703040340c0911040108400001201034800c1250500307103402e6000c2d0180e42107101c0002d0800d0b012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 359559874 1250 359558624 359558629
    0x507030e1914161a090603010b0c011508030304020103270302010e01050a090804170c0603010902310e060d0b10080d02010204060816031506050a08090615010804050102040f14040b 79
    0x200301c10b602c0e58102c0781c26070300e000108403041803800e40e00c84e030440085c00300340d20a48554010314041d280c40c81309280c65000310130300103003140c8552610050814035010100718414004c8103c1c0d400035028a40070802010a24a00c182110415501d0f40c13801c1c84217082009266041d800610f0851440009101d01c0e11100031102c20348854140207010382004010801a4400c2916079070759541030790098a01c101344082c00940103070002d90080c035145800048210a030700c007034030f400d1910700f850085060006180c5840d000da80c1020b8003c0c60807604150300801c60310b90740c01100ca404141e101c1c072144018613203d41c03c2c1c94050701510a03402d0521070101448156401030007603500343c8003903a40380c410075a02c0030100702601030860039a00515513030710b0007030840d1f00740007207040003801031f94607181c0d55040190801050310381c1c01030888249801c10b105001c0c0391007041c2a09804074409191038040c9480e242081e500900c150780c41203540c1d141e20200054128040598179400d500200c40400280ea4031205 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 359561124 1250 359559874 359559883
    0x41e020a0305090f0d050a0905090109020a11070303090b090f041a1507081e0903010906021c06030803010905040206120420010f21021c020405090606040305060105040507030e1914 79
    0x240700070300750170091a12980c0c510600140040d403d42d40784c0801d81e16905d10114101101c02c0c0c02c01451241c0000710400c2c00c640255103038009016160042c03020310719648008010310003600540040d410001881c0d0416942d91a019504101c014000c00203584640c005134901c2c0d4000c03c0e514014440b842e00b040c960300054094402903500a0b201e00c2c40c01181c0765038554002010314030900f01600502000718551001d1064a00c1c80d845100c0050b9202d07111f40c645a8083d102d00d501082007407d10206000141131403050728111500c061000c40d040c0c070355200089103402a60000700c00685400c0c00c0006020f034074503101c3c0c410b9a019004801c2d04603d0001164000c0500c0310b4203000c1800c3c000781404404c01c80d55151b51900602c00018100b0245c0390300c0e4460090310508111156401080601c03051500510f41a001031f070031200750f0300d001d04d0f46c0e80d8641c848805100c0c0e9441195110001100d81c1c2c000d81014a40c2a0080305441c084440380c1c15950950341030080a813101403211070400e034040800513 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 359562374 1250 359561124 359561143
    0xa1e1d0402101103090405060103090503130906090606020a08070203070b0f0324010c030c0804091d250e04030c06050c1218070b070203011d2118040b041e020a030509 73
    0x40a5460a201039040c030002e46006030100c9e041542d90620003011440a001403c0d80242c40d014080100e443c0058500c15100c031074111008003403a2400410010f40c000985010182e4032107442e076158841400028101074080d8020100b56170001248900f0f0b10020340114481c40311021181c03981c52096000180903240980198045402704040700c0100c0d020350040e101301842004030903d040c1c1c481ca11402503900c60311050704483e5566013414045101805000c00c0d1800010f5000e10794608801e10300d84400a174402d044c003851840000c50141441001442200ca412010502c00c1e41801100c00640c2c1d844043d001524007581004208400c140120101070081400001c050b02818918440210760045c041242d0540d03a40302d509015109403201c01c0032004200b03018180b070b0b01c0801400e04642c03462a0400b090301c0d40c20401116099201640303905200e00a40c1e00203810409440802c0040007400010010701c1118601c1c02c000e80c070503800a0070109503643c0c00b808a44c490349942f651b81c44182 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 359563624 1250 359562374 359562407
    0x703030219110f03011b090807080a03090303111006030f0b25050901050c0f010b010221030712090203010501090213050901120602031003060510050109140a1e1d040210 74
    0x61668100601d006503089880300d0f001400090b036081c561030000680021b4101e4500402c901c070b0000c0003940d00510001c8010038088002e00944d030040d0758018401c1c00f036408020103005006a10344010001040070030700d01e404000040184646909140d4a010410380f022242409510000b40c50031189190755000d180384043c00c0e8440e001a410190b03801e402004400c0d04004042c09005007980080001e00f0b0110040000050460303110000213013042c501c4611040701002c40178042034500650130880780d01c45c0b21071600164001c101d445003000b8000c0000702a50560a000000c40c02413415801082100d15515800c2821a50345080c001d014000f48503c81325000701a81c540d0100e580d540066606c49a420b103040341042d202d0b031701c450864070156092040d90000d1075041c4241d50700164807502400d20504205d00422141c0c00190410259010313000d00480400c0b1030b1652003014100ca9405401000c48500c2c4a0306072a244191800d02214181e200740c17030101401c1002405800c8804020000b0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 359564874 1250 359563624 359563643
    0x307050c0108070e180907080d05090405040c1d2409010504091e11040b0a24050c0114040c0501030912110316080705010b03010e10090507170703030219 67
    0x14401510b4040e8001c2c00002480800c1205a0007552448a0200d940c4001017241ea4181049282d0900d0440d041e000354880c0d0b0b01405231049869089419202864421140450b455940b850036209100142d031000400c8007070600485100000000001e206a11504a280d03420360303042c5880c85400d40392011260016095401409181010b410282c180c81c0a5403049140c600b20034045070880715600d80c00d50710426110040c1c8a03a103402d004500d0b040c8001c0b500b5907440e40c02c200c1c0300c1c031800340f6281c0301181880306605402c148a001c1c20a4070360480d20500200a40010540c0c016625101120111001105040042050f40c083d11500c985680c1101225000c0064000190b6000b04c1d01c0c0800e00c5280300500025641504040158218900c11550030361105460310b88142910f2400211301e22036410702040b66074018000400001d02d5100e403a01280d05442d6040503410807107942c021a0840b942ca144102c1c07004d8002078071504580c0309500f10354500d1251940401c02401000000700300e0b03400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 359566124 1250 359564874 359564893
    0x301052202070203150702060105061e0318190212070f15020a02031606030e01060e16050c0105070903150e03030105101205101505090d0f05071d0a0e030705 69
    0xa9140340350000a990800524050a6030000380c039084410b040b0ba840211803204104125505000090060038207982d0b031400c110f0010300741c41b05035507d04454014120b0100015040c0b6404400c0200408104400e6484805620142c50040c280d07100301a8020b001500800c15000301c0090054103e03a0f00b20542d0800038105441da000c8600e09981c45070451044c0c8203118056a002d200030a21402c8600105a101e8507006010f011303211117103100010380c3d14003182048550004c3c24601c3e0b10441c2a8541040740e030500c50207031a980140164030f0599841c1108020340c40b82c100c42c801c0241c07230103000d918503409100c40801041ea289021200500c2d042400100701c942080d0340850440000d0741041c405d00c8440405620884004031600d0640621081c001c106517005000081c101c0c03c0c0740e18210340340038000e001003120f00168000041c1030050240c000d0082c040c0a10115018180d000140f18030b00e886840001e00c5410152410010a850046071000c141070000443d01180d90040140443c4030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 359567374 1250 359566124 359566159
    0x80d142e0e0106020102030a0513170d020d020c0c01080609040302070e040c0b0a031a0d020d0803090c1f0210060e070f2f150c040e040305040e16020111030105 70
    0x80c15034411510300035200008202000780320000c40c041c00141d8001a280e181580c079030b03015140c02810b20415101c44814500c0840c041c080c800c14a0034030700c981300d5950300c803815030030b0001e10460141a84507840851042c0c0741440200c1c440340e43c01000d9070361408c00e882d41001c00c40500c0c016180100942e0000e4820082c03080d214040c964021f008140300040150f45284850700c95010200e2100000c1d40c418000112801c41c0c0781c002210300e015503502c015041c940d0701040780f40c0304402c4090440f031004000100042400c00103080e640742c001e414100c0d07111841c601300c5041c4100c0d002c0c8501502810010801200403440341904607a8501c0c01c1d403502ea00e40134001d8a00c10070500c070704000c1207120380c9000750020107680048005440c5d41080c2034010202201c02e4108131105042000020101c010300030010716210a84040e01c4007160394075144c4e222441d0545140c402c0e54040318401d031a06041007150003010360118800c202c1500240004000d20072021543d100902515a2194250005000b1071 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 359568624 1250 359567374 359567431
    0xc010606090b070b091c08060907020f071e1e03030306090b0a05130b040608030717090108071d0901030b0603010e1c05131a0408070e01030f02060702010509090103080d14 75
    0x11600d4030030b58855001c81065811b807501c0da0144440400c034282d061003582c0c14040f03040359001409102910320300e000300e00030a031103040503c90401681204242200100c2c40c40b060240140101480c00c0c203d0324203890800001d2109100c180c3c042850410b00144400343c0d80104851058010030380c2c9034030b034206800c10120414821511100d180d0301c1202e9075039502d484c41150007070907103d00110340f034a1480c82c2c01031000328407059202160b00300780302500c0d0701c0c1d8100c0500307a00f024140c2440140003005610300ca5041d5a0601003070f81c0114140d00003c144001c941c01e041c001c4134198028006036005e450f509540d0010119880c0d9910201d55041c41c00318402d4014003154000402500f0a0683d50012490701d0608450707684200b910001d0100049002001541e0003401c1040e020345a540c5075441e940320103004c07014042d004040000d01c480071a0722074000c507200e00030002c188495658403070800703920980103581c8240c0c0c006d140100d0408014160b4001a11031840c00c440b41c1c0b04071200b5a04070041c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 359569874 1250 359568624 359568631
    0xf1303081b07020d14010f0e06072006010b0706061403060a1a0402040b1801170412050c0303090703030f030207020616020621102403050702030c010f020c010606090b070b 75
    0x1103014410040181d4403144c0d4050458040c2c0301c2115102c04040c00c01d42100c9407812043c00183c40c00c2034408540101007131540d403100c09410204c4000407881c446e149001d11094058429000344400450410a074234041c00c110350044400b0000d05486405100003141c0710300100d94950b00042c0012495400c58100303081d8040038201d0080030301d40c1500440c044c0e800c603400800d00c1001c003180d683c0c0040c038541c02040d8070035401d1920811a5000c000d21000300701d405400a840c6c8140e507199204003900617411606049846000c0700e40e645800d48001da1140b0381d601007100050050800030850512078000d03284846c0e00100365500e88840d03600e0020111024a02c205d8021105102d810800c00c00c40072860b820000a8403954650714104602c44a51f00761600f03c01c0400030500c2241d07014103203c84124407000003070300b400100c03a01c41140a81c6580111003d20209600309003050390801001e4010300b943d00c5008000b4490141c50b035805442c42c041d2400b4a1046040a101c200042036034140520740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 359571124 1250 359569874 359569921
    0x303061401360504061418060a0311030a0c06122a050d0905030324010912031206360903050a0c0f061b020d08060303160201140d050f130308 62
    0x5543d69100420140c6100c1d0344000326568045440035241d050003242c11844840050b03070180f0914003000010305c2000ea81c04041e060a000040750800754408201080c0340c42d81107505810030307590b0307040f005010301c000e100c0300d80205d070a0400a1a203541d002c684020705502c41d10003040790f1015400101c8141c0c1100c0301d1103003041d48682c2003c0105c0d0050000790300411040c0340070039007488100030001d0032007803003401035040162101c805c01041c8060b00c056a40c66502d0f1802d04480940e002c10800546103d41241c0200c4840c003c204a40030303c0c00c40da03030107140400182c406440002d28142412203001010150100d08104007404400e4420440702d24280c1c880e00d84412540c2e4503842c4c800442d000018059000008030303280502c5540c0400200d0442220342c50032100d1858a07002180d00d0740500c0d0310203111781c3d01d20724036103045a0083c01500d1f003144030b80600ba500c03a1094414440502025a400d1414007100c1c40420540320106040c002d0442c0c01d62079440c200d0311030b4100307040e41105e084c032105c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 359572374 1250 359571124 359571227
    0x1202061b010608120c10050c120106020105060a1a0d021b03040914010902090d120504090e0a110901081522061e150b030601030e07030303061401 64
    0x180100e403844004120302040006007250600c03161074036089540201200f54a428031440603903000018400a00042d160004100f54899032100b111500818000c119034000c00c80004c600e00f5815402540300321400c6441d10501ca5035900310f05820a800040201540010011002c0d405a80d40081c19000ca41c2120500b0300322001000a0440d00660030101500e501d0301040c00c4445445508a40900140300d803c40ca400e000030700207004c4c2031480900600c4d903038803045803e080e2406181500c000f000581014404000c6900c04561030310160034084443d81080c1c60130030301034240166564160740018008003102200144c0240c20020010036081c0301c951030085120107281c0340d0200c0a05544100008140001d2440310301501c2140303449081803c0d8038064000d03107107568401c3d40b441141c0c28115555036946441004034003612070782d810300c2050300c60715800004055040d4450400c407940461500348190380e403401111150640c2c82c044c460b14803102c0701d031a040c820b14845054031142c13a40350325 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 359573624 1250 359572374 359572387
    0x304120f0c08030d060b03060108061e03010f1b080705120421051209190f051005040b0121080d0b0a0302100216050a0b04030312140a0b120106030507120206 69
    0x255007844558004035801e820125001c152500e080c0200c6002c0d244500c0c50b2419071600e00002841c001005000921480c2001114140c01002ea80c20024600303014000344190540d400000c0080c0142540f218100343c021510810114031034448140514095034882d0701e0b00742030410304000e000000d401540c2c1a6900340c2a104c07060b01070034540c50031000c02d44a06464070481d91300d2114004008260b2401e94100324050000310525140040000c0d510001d1701c41d90f1001c07070500c01c2c6085842c042c100d5401e4508401c2c841804500403449040700c0240030b00d80c21942211048040e54140c2402c02018040280301c9101224040e4200e00303401071000e0094020141d403900014000080e0340102c5000d81c02c20b100d000340c907043e0100c200000d41025164034045038500001c60609200c0c0d4032003d0b0800600082080303c510b507507001000e10707418290200f2706d1030401034614401054100c042c1d40c8038444590b0320009840381070250300101c94000015005c5c42c0e250041c035500e0400d9403001264004801c0180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 359574874 1250 359573624 359573633
    0xc01020903190303051303020309040c09150c05160f03080325050a03180b0a270305040f060e0a0311030f030c06100f032a05041e1104080304120f 64
    0x6240b409251008a607006018505000c3c00300d540c05040c902911901d6990f800c080307500001116065a001d43c2d00180c01b0001680071911281250020b41c2800c0a070030b034100c5000e600c185182400ea0240c0160307450404044083c10300100e0074841c01c860310801034000c00214610601569002503418a02e05104c0003c0306003840508060740340102240c2d0100d07031249101d515100707103212854241c0421041c240192140301d040e0b03500802d04170000352500303402e00c00c3c141c480c034640c0c03810f107130400c81541034000b140b81c0600184c00600a440010781008000151240306580c81c3c200140007500700b81c6041c0c11a106c82c0065080e551015400d8410500c0c44000d443c0100014403040d107141010704000d0400642c4010466000da101960403e110720702071000c6032500071495901c052004540c00c40c0600000c0410b2601826809113038042e10b844843e80cac05600d00b011400751401c8004080115205010005160740503c1c0540e2a0950040c0030a01600c0160200c001c009805484507400380e20040e501e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 359576124 1250 359574874 359574883
    0x906020f030406140c04030b061903020604320d0b0604111c140601050a0f0e0406060806040b0a08030a080c0c01052d0105220f0501090b13110406050c01020903 70
    0x404483c40d0342e07600d00200540e80004c5505401281620155180a15540b0341040c0800040d119601c222500c40140c125000a008406c0082d80d0141015031500c2d0b5070300034025a0500a4802242801e0488810f41840c9548503031114a00008002510500c0e8544071014011802400c01d6040f540d10030090040c040d154010305a54204413400c807200710b03854072803482660026400307902403484140c14402c1c2e0781c1c0c02c02c040e50119a46454540f8140105070004c40d01d440700359480790780091030944041001d59000c040d86200d86001d98041c00045100814031003081c1c00f5120300070868000b40422419076200700c590b29007000c0038207102030030100c2c518145402c54109890544010160b0400f43c4420041008a081c4180103500281b0280d031508001c9610011030400c595040d039401b00c05d40d0401c90355035002e011203142d9545c04000750b6840c0d8122400400341c1100c0140f00b11101003075150254103e0143e8410182000149814a40b40803825161500b114400d000075540a0000c1340d05a00e0820 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 359577374 1250 359576124 359576131
    0x1a0d110c0c01020f010c0c080315130506040c0c030203250501020d0507091d1602161e050402030115050c191209080f21040503060c04030302010615090302040906020f03 74
    0x1006420822072900000e40b400ca180b80755100320740d041904840c42c403a0840049400c0c0d907004070220303580383c2e16080850b14441e480305240ba8402a1940005081c1e140d5502143c4a01410749041106800c2d0007006d0303906007401c410040c016801004004040303203d801a040302408604442c214012165845e00c0c203a8100c1260604030964540820004641c003800e2280201101200e60010882c450401e5840b4035004281114444440c424221442d108000345803c003505042203a031613646507100b0700250745408001008800c501c600c040313124a003e2003280d040742c00b8065080358030750140a0035074ae507030004846001c280c01220b81c0c4c0c0526404201d00c1c103450350f20440695541886581c00076003041030580203104250b000c607180c0e201900000650710303400350352400c0702d02d1091611108001c2d90b108503044150103010741418003c08150074009001500c1c402d1f0028400306407180d46001d00030241c20541e41c0007500c206401c00140c2016400745000e40c0c001c450151900200b51020141c40d070003517 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 359578624 1250 359577374 359577397
    0x118030501090507210b22060b0901061b021512010e06030105070903051902041b0806030d02012a020319050912010e100e0304030b190501050a1a0d11 66
    0x10301102e01000300510000e409040902c00c0602c1080580c007255139400843c0350020203a81014001c80c40b40440760b220045020400780304e1291079006450044084e00d546c080e403c3c0150110000070a400f4000c030654401c0d40507000d41d040312035641d50200074040c2c43d981d0384d01c00140b030f01f000900c441134003081000380030341200044c2c0c207041d0600c1c41c02d041c00c54a00a0401003080881081480010808155000c3c1056002d04110940f1198000100204502c2081e081c0c103203a01c1440c64101038010700e540d0310805040341034503020780704620203a099030300e4803d0070182c01600d2188001c2c080440445520008480c2c4107d9040c07104038841c2e9201c4070b07000740c801c0f0041000440c0e64407180c5030200c404070705e40c43c000000344002d002550000e59120381e007170144002c1d00d445d420300e03040900c42001540c00942d0001050040703418811114021351141e07603600542c003410880045454203001c290781c1c0403984079100001e8542c03144126850182c01c00d8a016454588803180a40b2050b4400060045203184 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 359579874 1250 359578624 359578631
    0x1e030f0706020625030e12160b0a05040803041205190e120d02030415030b0d0308100b03060a0303120f05010e01150216360626100b0118030501 63
    0x400d0303030181c41d0090003004d60981c40b04d60016441c24540c69107008001504a050205a0b1900010107070b0500741c2d91301a8800403030b404900201d007521006203681c15a4061960400541c8600f10b0030400c0c2d41003220080c202d607000300040390010b00042081049640d643c5045414004d00d41c41301d80010000d21860742c000b4000f044039280310314005141040e500c20440c020000c8184001b4041d40380c0c0698440c008501c41054103000da154000d802500f10340c44010a54441d401413890081e0031944255054800342a41c110301144242c84081128040c000080c42d40d041036182d0f64044a6550032150a600d4503501c0340851130188411340103450180072281022011581044110114018850f00d81011907003e00890baa801c0070755003600095800044094410b0703000508881c1c080101c801d001c0d18503a0303412555035060540307a4043c8003900c0c06642d410105486800e280b000300742c42d51202d00003503002180702c0c11941c06294825115103006040801ea045103402c81852064081c0d07000342c441c0e944 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 359581124 1250 359579874 359579879
    0x115080c03032b090c210c050906150301081501062c0f120c030d0302070308130204060f060203030108070e01030302100f0b06070f020f0a06051603050d1a0a060f0e1e030f07 76
    0xc90b0a403024000e600006c20343c0b070209850308402482c5038441c1501690b5200c01085840e19000c200c0006919400c442035501d50b07644803801e65801d804210140807080342c1002250152084440d4060f4101c0c20b0029421501c000c80d84c5440c0201d0b20600961000c0c3c802070b4100e81ea143c00d4004076044c0480d0000e404482200c20926003480820348010007014410012100002c0d000130010b41c00148512079500407614a101280080180707800401e03203100c4500c070010707404d40d000004605076843c84080da1103440d50741e000429040c07420302009026070004010181d48000704e034440e42c1e9030500f0403004118143c1c00e0340031804071791012006540880c2f18001c40810f5050022030404200411345085600500c0d181e0010301d1809900d0591080e4001213a801e0103051080b0140c0b1030400345503508210011007400e54940c0f00040c84c4202c4d0088074549030008081e80141450b0b24521200d0b00c075091074007609420462003210701a413610402c140340503460200d45040001100f07000403c1d008200450 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 359582374 1250 359581124 359581139
    0x602031b011b02030a200703290103050f1203041707051c0e0a1d040b0408120c0d0c020705060d0b1801030f05100b150a1e020115080c03032b090c 64
    0xd18070040f844c1c2d00310700c2c40401b010100c00000e5610407641c00100c05581242104c40c484c0011042d02020400b07a84e0765000401131240208050310240d0f4a0800c40e0694080500c003030b00207010854014062541c1c0c0f1320100711720380e5440300410089100703401380c03031814419000d104c00d460b040001410004041f000100b1003030504c0c4203240040c1c44098015034405036150b039a00c0300160002d0004019040005c0810204040481510901030301401c10010a161107904046c05d07400c60a54002c43d03604000f804030780c0d1800404c0c10816181c024010520f002803c451080140002c1111740f41c002c00561400c003000b007034030134145000c1c611400344490600c4450902034942071a04080c2e500843c80e1000d000310365581c106420381000004502182c03928103414082d50340940c10303407059030301c0307403105840c40c058607419800821000b022074144141151144000303682d440e401c80340140c06a004205080d05588100c030902c24030501c402c01c5d2480e8801c040c9440701a40d2442404440084d000c0c0340503c0000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 359583624 1250 359582374 359582387
    0xa05010f0906240c06050702010903120507020616090305030d0504060e07080a021903050616030507090810020d0e100609060b120f060f0607030c1106040602031b011b02030a 76
    0x184045407051050904050542c22102c410100f00340710501e00700c4a20080c1070042049980d541d8002004010524001030301a0203044d948608a00148403c03480325a5090710344280390240a541c0d00516150b9a071440c0c410000714425540c2040c031840c10800400900100010510002c03c210b01080700d04042c83c003902514440c0d0340184603030301f0104080c4038445000610307610702501114a407983d07072145950158890b40351b4001400c2c5019120400182c05081340711211209241e580401140c1d40300101242c1c03005d00340c000e04509410403160b4199140c1c06401400c900d004410000030034009203100320b460131200320484070301a80c039020100310410701886564000c1c803090010f00c0c900703034203040750340ca800e5001030006602c00e40240224071107881d01080240201030103800f486e9500a0390501402c100141d030320441d503000c0e000c9000b41b814200001954200d0f0040d800444c1810b281101207044801e0414501e001596943c407803034142e01c54038501e0031188245030040c507075030403139003d004020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 359584874 1250 359583624 359583629
    0x60c02010f15174903050402091b0702010804020a120506010602060702060f0403050c0c030318150408031603030b090c0706180507050d110603090304051021050601050705060a05010f 80
    0x282e0013030392907502444c0c009074600e1201c100f0580d00c036410390886060369500038440380481d41c020702e1444d20241e8098142d80581d008030b0088811968540d44c1100f0906030720307042c00c1a44c10b00281071000e80015400b65003000d4000d031009181d40d00d443c1d1604242068406030030070a40e40d542c08540104a49078052103003980010041c400f0b81854070700b400030000e0515018000a04000b0002014140140b051016004000b0010241c90b130320001d101c001c0001c0001c014642d8030601039aa52001022140d80480d4100c4036244040c5007030001008942d140d01a1651042d401d268440e41c270031007903a40c0d604a82e449034005030845034440c0c16a043c42422203010510b4031080350f5030075900802040d000103140046900442d6442c00c00005481c014002c0e550008442d5000100801404a0038402001410903900140c91403c81d1200c820012100142480307a1040340505516045079958001e400040d4480307818100f0318070b882c40641d00c035443c14604554511000d95a04018440c0a0708140100c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 359586124 1250 359584874 359584919
    0x1b0503041502030709030f0302010f060b04090c050c06010b070212061608010801050601230c1f050603031611120d0c0204110702012a080409021201060306080604060c02010f15 77
    0x29441d0446002d44034034600c6c000075204150b040c0c0c125041601c02d400c4101c082403110024054155964025042ca40150041c03164031810803c0d8070005600c03371300564480d00188802026141d01c1d0a05614090f400304205903088550790400101407a000c1000d140545803200388030b480d200710082e0041c083d1006800c089201d904017010f00c5400daa1007542d1000000005141111000c4d0f1403210000c6403080c0c0c40221124001e48400c581381e00e01011803442880d8400360203214541c0c484c810181c4900ca041d03240c0250704440f2a9000200c0c100080500505401803c03154203404040811480e0040145000f400100c203010b000b02141054000ea1650400711203145042068030f0340003030038000b611301044e6081101c202c42a400400b80402e148071403030b00440c4450b17a0b951105103443c0654040c0400460b100f41000c00000c52500c43c0c4110300440d00503034050142511555241c3c000f030004500103504564071031000c0b5440d1102803088000c1c00900c2c044000e03503145859035030700303810246012102 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 359587374 1250 359586124 359586127
    0x901050604061d0a0512031c0b0105071506050a17010e010509030a1101110c03030106030501120f020603090703020402041205070e0705040e0405070312030b040b1504090902041b0503041502 83
    0x2c0015005494200704065032070442e4072510001012590262160f44803e50207801200c0700e0580c88004030060104003030034070700f004a5904801c8148180d80340c88076100d0001d0010800c2e0004504003489031540091a0076000c030320255110300150312901d0f581c11824203586084e905500b0150240324100700d071a09200288480e01c2e011000e640c81340582d040810600400183c03030350035501c0a50041d1940050310000540b40d40e03c044186559401c01d01902020a16003000030940d5404200c41d9104e440d0301074003400c00911a0707030034014a82c1024002d004079114000700800140d0f00d6001a03c00b4010170748a46000000c0e42c1820362070004940d1081040400817000d1120b0103901004980544030300c0790981020fa1268684146490a15440582040c111060a00d59903905403c41090500119018020240080c080004190b01103e10b074001c1c0f2800c100c100300080c0f40d40c1005a015000510024401d00b0440381c00140b4181a02400000307030000003007200f080041ca078a1410b0380d10104046 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 359588624 1250 359587374 359587379
    0x706140702100615140f04030302030a0f030b0607030c14250e011211060706050702061b030906010612060803191808070306020d020d020a031a100e040e0703020901030f020901050604 80
    0x660304413a0201902002940030b11011414100000c4441c122198202150355580c1e074180203440b81c004554041c00103810040c3c4101c900d210f80920a20038200612042c9002039a54094030100340d6848111011100d14039115503909051150051000240400c1d0600b4030014190380c50030200317a0030060b0911907a40050040803112101d180382039601c484102030110100300011600d01aa00e001883c05045c14100040d00354041403a6000e102d004000f192401000070340c0c84030710301084840b03220a900c0700004001e8a44620700c0a4591002000c0024041da150840c841c01c0d4ac1c46613107402003481200d1107103290142d00540020014090700c1c0210003141c2002481c0c0d89580942c0700241c00c068000c0b400c00b0050381346a0480d43c041c55104800c65807075a40741c030098081d0030040440c94003078058502c0341906081c81d070020f1032049090b0743c4100c03080e200711342004020960400ac0b411603100300303140400182c0b078840d0154040c42c040e0302001c2c400314081c810003003503c405802141c028101030208 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 359589874 1250 359588624 359588639
    0x5010605130b07020319060e0c04050915061c080301080f07180209040f09050c011e090306050408040902120a060911030103020f12120d1104060f0c060207061407021006 74
    0x1d03400e440005802c02e54403002400040d04c0c101c0aa9242c4000c4203001020900f0003405910050355421008192100ca0748500d040001300c41d011100c2180b990091400120071812011009a101500500c41940e074240003410401c0c1c00c2441c074044032500070000c0140700034030b02003203d0f20881808000520312036040a118038180f81c0106055070382150042402e4005035076681084403a600000010404404c3c03d0034070b180d0303442c0c50491582c04951004400301c036481c1c00e500951101480c9480c0c01d41c0b030701d01d113542e4103006140090007a101940144000310b00b9075507900040a030f40400040d54001400c00a0076002203819503440301090350f24106005501c49a00410303241143d4045408030382c040c254070003082d00d00916507102c44043c040c84640d0b10180b02541d014082440400b2001c0110700c0c1c4030090702105100710701030a800700390030421004101d0701c0f5a081d100c00520511015040000c5596010143c40060300b65246034a41c240400282036410007030031244107440c01003808446d207450b40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 359591124 1250 359589874 359589907
    0x180f0303090b0c1213050f0a141306090e070f0609030f030f03150f0f0506040509040b04140607030605010f0305040b01170a170702091006120b1f020f0105010605 71
    0x6054112840814410b40b070140034031840e0501960b1840c1981da919105885c038684104030301034280b0600b040380780c0302c100741420030044007601c00c58419008201c503054204030040d034103807554402654498001113110340040c021070001414000c024840c650618003840c50054068102c40100500c004080001c900c84692890ba010f0701800c254201480c402411000b400340c0c5051005000416900012020106980c01044900c0c190380c81c0c514a0729001004402d00c20341c400c0a600c03282d09030105020408500c0b24680141c0300d055a100ca0007900b03680345040c5201141d107040801d503645c00800143d40c01441c1c1d40ca441c00c5503d0304210b10310702907a800710390401c18015000c000f032080000d8220301e01c040000e011690b400c81a0400383c48001c4059000e01e6002c410128007072a140e0300825801c2035082908800d54001d900c03640140403040030002e00a00ca0711070810b40c45111044d504d8003d0340a020a0310344018144c2c0034280d00d5000306011800d48a040e440801000303c01c00c54144120342004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 359592374 1250 359591124 359591129
    0x130f06020304060912090f05030307050703110105070c12020901050904120c0321020d0605010e0901030b06010309060c020d0305071b111503070818030f030f18010507180f030309 78
    0x8005889440700d0409400901100c00010040d0490304151040b154000340303040112184480f850105540f50000c0c15180d00038400700030002c0d4030900c0203000241c011102e0b00f00c14070042c50241e0821b080f43c0c843e0840460130750b0008003280110310300341c019402c1100d08140900015a14180142007a0366000310064034040300f803003040b802c9107458040502c01c0c0b0340414484a43c044035910308850000c070000030361106180c0b00c112032802e039000a00c5d5000300300c3c01c0080324006005145903880d640f50a01c84a0b0300402243c10580d40c2c50030500051150b104040d0030310203550041c00310348900c6102404032480070b00a0014031a00c0c15410116080004e0403007082c0b5401b00e41403207103000f03103800b01c2c521070504080c01c400c056010003044212540007400760301c210481e0600391144c2104841c290340f80c0c801c0344840744011074100005110b400f03a030300503180c00c1a4001c0565044d10220021a42101c400307a0f00700000904600420020b0300071071a484000c0c00410000010081c616903028100c0c40262 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 359593624 1250 359592374 359592383
    0x1c02071b05012607090b030a0c02011b05032e0e0405210f0901050d02120916080c09150901080309011409090106110708010603030c02090a15050f03071a0301030b130f 73
    0x400025403040e11540481c1e000304080c06d0041d44034146518594040c10070000780d64010b41ca8501242041d902c840303d115441c00c0303c1e4503001c0c50740d102c0503542d5226800c00e94445517134081891041d500e00300260161030080202c81c02c2442c2d00e08251412604001c90328074410342d10100c4260300380000c425102215000e0f0080394040d42c0d2040300e080141c40c6409410607a50190317101080010b0107050140d140c0d441801c40300c090350842d01a01024400d104c8060164000075445804444540e0800001b0541c0080c581148982080d0b5000b00040d14100c09030003594098001181541d110f507000301d800840d00b50b0100318541480c2103035000c0380c044030051207110200f01c4804c14184082005102440c0908200c0c0c0c028402d081c0c5904002c0d0000d04d604400302c0c00f0b400700000080d4085506d12450002142040303903400d082e450402000744810301420345075032500940c200000d2030440f03c4500003841010000081d260b40c51400c285040410084c21803045000c4402c4c401c1c00503440c10800310055074030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 359594874 1250 359593624 359593697
    0x301050910051009060305030a020d020615192409170c063106080c03040b04030c030915020a150501030803010909060b1527030d051c02071b0501 64
    0x20424500b140b50b8159001c2135540780380001c0401401004002030105589640807501004a07050b012a03a8400840e9400404034503417410044030700d86550119031010107504110a141d840302c881038034903088280b0191260408a80c0c440000390071442d0200140241905074184180400c1075075105c0e00c8140c60544205000155200c2200300c9555400e141950325400301d1000000c00ea90113a9501a4081c0c07602064100d80000d0003a150241200c2c0304a030f01045400d525100d568050382e180d200300710200d0500681003408103812aa1b01c0b107689030704640c1d0340242400c511605116658480740c1060340011410f00006101240a101c21a030444081240c0000c0c00b0085007032a500400e8020301c02d5034003240808000c1002d08585000d4844240c04030750340340a0780700d000381080210300034070340d00750700b5401035002029464091406000030391800d58041008400507442001203a21110081b982b4402c40d0505601a00180318101c001d0502070820403450000c1e09915468010a50903e018403480c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 359596124 1250 359594874 359594881
    0x90b0c0f12131b1d0402060409180219030201120917030a020c070608040b150346170307020a080f12010303081801050114010e120303040303050403030b030105091005 73
    0x15500401d1401d80089a000c941c107400b0b040f07081c0c0c0d16494880e0034014001e1012400e221408111480d00403980288240c0c50103241a02c0600501040c048010303844d08802c00d80170160311004002c006420800c11120b80c0340b802d40c40054444290034910107810303843e1030017103c009504c0f02914904444603c41154595031039007011800303032045410100c1d050190070000241c040d042041c1d640202e02c204041210350340c40b0700e0690301020b08000d40c0b940c16032100e40262220144151060056880052040c0624000042042c8269201207110724800131001c2c5800c04c3c03190700040c100d8040762201900b07145040c0f014009642e0340c0c400b2009407040a000541e2030160351100c040391402d000c0f0808001c4290b0b902e04003e0182402280d1142c640c0352052240318140e8018440c5070305079400c843c03003400c1200e101401101c200e1680c84840c2c1c0c2006600e030510303204202c2080a580310745d100340d80c0411289030515000b000c2d10407401c0305a019070f0508007070041803880403884800708110070600042c0c0740d4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 359597374 1250 359596124 359596141
    0x21c08190f090602160603150806040c091803020622150f0c0302091c0c17371205090d0807020307080c1806040603060c03090b0c0f12 59
    0x41400c00c0800026550400e0055540d004041c050404506449800351503544410a90702c5880d05070242c0e000290380f100a1003494029400440505001c0c0d881c5c0f00300a40380c0d103090786481c60aa509590301c441c011010811035070380c2e0140940c03004c0d00b80401e00d1030f400da40d64080c0d500c100c05800c2e40c12052104804040d02d00f07078580c1646103642c000452882041400404500625007100039881441c00c100d054140303503029000300c4907504009060149452107101e104d000071001007504072624202020f00203400c1410010640420f51f12802600545801400743c20100b4003484580703c0300c0361800c2030006103014101c8450141500521050100501d0300c0701201d451051212550348800380081c0001400096006030001ea44241c0440b00211307126050141d0302c0840354003584d8031400c40f483e41a07130603e00007401c54002c100544040362050726941c89009880c404a981e00000f40d80d050207070300f48104850019000b40308552007900d4010055184207a80c45801c004010105070600461070700c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 359598624 1250 359597374 359597377
    0x61a0c0706050403020a0e0406090209130302071a040504091103060403050310150e01110a051c1101050c03040f031b08090f010903020907051b160807060504050319020d02130e1504021c08 82
    0x132b40c0e00030810403840c54603240c05240c0c000080b40c00c1e801403094180100f441d41c400100e22540030343c0103406c582014580707800c1001804a84204485081002121110940303040200d940507078825141e1540383c0ca0705460600703440115500a440d00000044e1380a50b40c0c0d000040b5460b0410280782940300c4e02004036280340380001148000b0074621641c203c0a11051a40300300d01160052a562040b031305500b412600d00b43e440c140c2d18a036942c00d0070404079002600c00706825444620909014215501340291044080d20410003511605000650342099151001c0c462010f800242080341006055401041c8a02d500030300b00c40c20702c10b000502200e20b02701c0e80c00e5004203841c04002c440030240d01d00305083c5005001e03c40c260340c520034220041070345800799082e40c0990380041c1c000c0580c00300a4a40c01100300b05000103036040000c00c8000000741e242d885280407c3c0703110740c0c00032607140021001d152030909a00c00c8101d1002c00f0109010042c0e689015003c4092011601050010201d09251019 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 359599874 1250 359598624 359598641
    0x501121d0f0c0d120509180f0105040c020f0a03110a020d050c10020a0b190204170f0d0e21030c0f0106050301050c0a170a061a0c0706050403020a0e0406 67
    0xc000a00c2100c410914000452440c0c0040030340554a150703202105101c044034098030001e0090b02c40341c8004410a100314058001403c0007442a0915012001000b40210342540d4103c075150011005020384d0400703025410b0385c83c1244c0b00800303203001040da03243c0c2c45c0c1c4070031a001010001c15a012510822003007241080198000b8081030100c5001d1070465070b03d410310042c850040c01d0b00d81040d141c450001c2103400b0f015800c0350844040342e4403000031021880340122880c0c40240d00703220206980d01c0f441d012094000384100207010288840103c5d51410040001c80c0041180d80041d82e44c5c0307911803481c1500000c031480000c00c070042c8090702ea941540241001d9002c0351181201702e600c032020541003a012668154020003068803511300c541310b644120540103002c90000707481c1da000e4800100758140e00c410303a9180020f40725110804100f00308402c0c00c1c5003601d100c0201708017a0409082c404900200498100070303191130724641c0440e0300ea024074483d80195500d0740c0e0004040c011760303030018580c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 359601124 1250 359599874 359599901
    0xc100305040c05010c0308060d020a2c0108060c0d02071b1403010e010605030d0302090d1208040b0a14070c02030109020303030109020717030103030912061808041401080907091d0709061701060303050301050112 92
    0x6158cd0244000c80c2c001041040d05070104007801c00001d0100b401003003a501031003002e1013003440c280754110004069401300780100c4402c205608603094000c2902070900140c910743d07001908000c0400c1c105420340344070b01e00050150740340c28003c02c9613030383c00241514000700b2070030056290035000b400140007016503000945a10515890f015100c0c1c0e10540c56445244500085202626040390b001c00b101c0c0040070090203c070b5144085909280100004101c9603c018004100c0c0015039001c00e0958200380e200c911700036008034404003000003018251030014030245200d1300310340c55920002c205440522801100e0030144440e0700038054243c01444c400031a00d0584d614070301c1280b404440f00d911901c207030f031444260809a140b403903108296083c02030080a0003010300d141480b01c142c0050540ca000340328401d911210200c0b10032024015130000303100d0600c00103042d901c0c0480c8008041e030010b030381c420b0691400c4400c6c40020b412038152415500c0070320b8450410b007480030009000300002c1c9405203 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 359602374 1250 359601124 359601149
    0xf040815060a05210f03271005160c080d0e0301090c09110c01110d0b0402090a0e1306090803010501020601050319030509220f0f200c0c100305040c05010c0308060d020a 74
    0x72612000002000d0a405c50601f029400191070102504d00e91250f11040c1d00006185002c90614444c0000c0c0c52844590314080b9624100f659500080102d241d020000d941c11485074100701e02d41004041742d80c104103400030710035602155511a000b20544c020000c0362a03490300e0803070240307214000361800358030158000c004800d603c004250142d000307100301c2c104050907e28001000d0030140252003001002811803c181d9050040c40c1919402c0109805014000c8184050100c0e0340d60207072400ca54061180341c2e5595041c8000241810300581000d8000e6008000b5182004801034131800004d4241c0f074450b40328003a80002406030052a00300c8201c6458559030505402a594006c680c82624900200522101e0403c060281c6030f01e10100d0103007140c29400031680d1400d900c01020b503288402c0c140d80c1602d010300c000071130072031b00c0d554200000b0b0354880c01c000801902440310b070301a11007420b091001001d036a400920f01007005109034095810110b4150842d2128107070140036009800080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 359603624 1250 359602374 359602393
    0x160f1d06060a03090506100524072607060e15070206070c020a0509041410060b0706050c070212060703200a11070e010602030a092c1b0f040815060a0521 67
    0x20050440c7d2801014402c0416074509200e0842e44d884000341a07000d9124242064403d4403454000c03100040d401d80d5810300002e15805001e900c000810009104a4001880e0000c0320b501c40d2a21a044854161140c004003d000c506074002800c40d0388090b0500d0008510f031400e2011490702d8405030701c80f03500060b15205000400c29900c5600340018016801c0f0b50380520f01131030f8041039541500c98880c40140030170540c000701d1001d4000b86d5100000f003040c1c80c604001c55020421083d01e44001440311f03040a82400f1130a075250180d0310100007140b8081c0c50401e8410100e8480c1e00c10109880e0178001c14100003e043d40701880303c080180a81c0340c1c525260f60355041301940340c1e441510202d00150b0703c03020120701c101e5660710080e4200c080c0038044005802d607130003809030747e6006840215100c1c20401000800403140c402000352152204030582c459181076080c928011040e42d40c0c000540b84002046a261582d4103500101c4800711005130411052102c4071090903c0c10155014600400c80718 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 359604874 1250 359603624 359603641
    0x60909051b072405092104051207080f03070201110a150c0309051209150c03040303030b0a030510061d060f0f0d021c14030703170414160f1d06060a03090506 69
    0x10324860344c00c035020b68003c3c2041c01103040e0040c5140b0f98110401c0404c0c01f0034402c505190003c5039030702c013201007103404c3c4540314620546405501340e40d114460b80000703004811964070814051041961400074401968250f032000740c19003841001c3c0400c140d48942c075446a610a40100c029181c209040e038003005158881d22449601c195481409640d4000070034070714210440494242c0080d00300618285400c60b5012009000070a8a007680000302c00b4000c80803440c1488460f2200c3d5100360005410b41c40d004082c03286c410515001c2c001c0300a4803080007040e4030f80e04c8603004040d000320344051034080d4200000d40881070444000e074000700700400103035404440f01d5158818074001d0200420504100a0090303036031048000042c00035008074415942040c1074003025400a00c80c00040039134a129032252403070000102010314001d441e18004010b01c14201e400c00015008201c409095542079941260541c02c001d0648d9008050009400c00c045201e6888806255400310a44815003405100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 359606124 1250 359604874 359604881
    0x504030804060606050a12050636071115070207120609060b0d0317060a090906290f21060c070303050708070c12120510060909051b0724 60
    0x81c00c803080c034030f00103010074224010010748203e54215624445c40c0040000942c001d04030151015811007007841513200c1d4450003059409081d20303220307520101306681084060760300401034241c0301072107150114808007140c0031644510740c3c1803050022070789880e03004089213400b85580c00b0301d50089100101c0400c0200941081103007a000c2d00040c440c82c24080d040040d9680c98a400802258010700182c80280581c04000d5000d03c008015480301c90f5144c40746002d6904412003242e14944ea003442c4500e9110000e12400005001605100b40c1801e6602184000405904041c45403181035604405041b801039040144440388040e60264200221200c00c2c0e41c0184a0440c0480d05010004060912840040e4812880b80d5250307a400811034940c030144262100401c0c040090740d010a0248200601499000703195000c0403c41040c82c0000041c4500b40f9504031a81443c280780600541054549400106038250828070359290181e140c0178800301480d8807105170644c2c2110740d9090014a950 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 359607374 1250 359606124 359606131
    0x15010507030e191409220f0f061d0c060a030e07150309032d03090807061b0e01050f040b0f12040f14030a080c090d050610050102070e01080604030507020103060905040308 75
    0x40400c580003007030b0700400101e00d03811200102c500c440d46d544121902c5540105a5119009090904c0c601e80c072074030f42e4102d40d944140d0070b0b0b581d140c4450801503e11280800240342074a00005001e6203076607a00003880a10559030300388105910b039407801c1c1505c01d0920032000107002c0851010003011818001401404a180080d0045805194180c0400c146844202000c820384601000311140d656010340c004c0501420503240346409102c00c80009009105c1d40c41c10b40d8200d0144148141c081a00401203440001701070304011040c8182004481c155007941c051799a010305154888401d0304030348900e4050500200a0049000140b10500c0208802e440d2814019011046a0608407480d2030345e074482c4500b0000020840c80003d03110030602005012642e00041241c1c42c03544d0303203448092805200f514813503040203280104004641e01040b030b2600401c55010352202545c9014406911408000c20107018400002103e808582c440d501180181c41840000c101600342400c0c002d1001804a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 359608624 1250 359607374 359607389
    0x8190308010b030403090909080f0d090b01050625050c090a0b040b0109032019090219090f0b03040303060e0906040303060501050f070f0c05030304060c031715010507030e19 76
    0xc80000c1500407421003124031483d0035840b04c07003403140313400303508401044825416650080c041c0007090301500158001c008090f080c06008c5410751803400c10f00e41d91141a4010b42c4180c5d03040005201c0200746801d40b50518190300103080700845107041c614141031a07402071580c41203100082002d0144c0c2d0303038450841c2c1c002c10740d81000360310000801034810b9955030001810350490300650000d0080d0850340c94841500103041104210038000306070341c9006054000b1000540c01190150050300640d048600b104520300d46051054a4030a0058800300c00e4003e0608410000000070b0500d40641c00c504000c20035110201c040345025071100341c4a01c0281c0d0100c1c0024103110300018158402c0d13045d504c8000301149040d00d400b800b40c0d50507421125070281120407460003a03001a00b030b642440908028101031b02c80003010402071a00800440203d1111b00c1329003043c800307000501c00c2000000103071000a003001982c4090a0605550503e04001400d40c40900400450400080c00d0300d80c0080f144d80 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 359609874 1250 359608624 359608637
    0x308010e060306040f081b1902041a15031506120601110d02030f070501060b0a080414060c030f060607050105012c25090906140a0503010b0f01050c07081903 69
    0x803070003007684904003a90b0141c05070a2040e20040401c1111005200c90082c1001c200c100400f0340c80117034103145440c0c0100440c141000003050a50900b8014211a07c5400080e90310780d581100c00100780004041c05030741c0f00000400092112201108402d81c1c02000070304850b02c5040c914104140000308442d0a80020844038100c10031140002c2c013001001d4080d0043c50804824034014007a40d08001000d503030369900c800c000030303801c0c07000ca004081245460707480a200749003038107002100465170044a240750740844100310f08a003440c0305594020064600325141034a41d1030000e0f40f14003a04d44060300552030f2900010f015034408176a04110407011210280c000c81c24a25105c40580072600c0040e41d25036030000340003070309107038074003110807186814510300003911400440203d40203038200c0311000c00685200e000c0b40c581650300343c1c01400c0403002402502400e50101351b010032161121818400081139040c2c503090b0034000c1c00301900680040700d0210700072901c904900c03040400c050740032560 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 359611124 1250 359609874 359609881
    0xe1f141e01090e060102100e010b0f0a030c05010c03170f01060305090c0f1002011b02030903150112060e1c021f090512030c12010b1206040606090915080a0308010e 72
    0x24603154414603950140c5850618500e454144070180c070004003007904501505da408581040301d441990078820418000040501c41001400840520070701260b121300c2c0c4040041000800004508041d01e40a203408018501c0504d016101900c014040c10a03800040c0100404086c012a2881c100c806617030b8140826101c80499a03191881a44560380040c0500140f0301c0f1800e044044949004c3d0360b00c0001005030400900380f18102c4048400340041e000050102241c0c80c2c10018031030814984000c1101c0c0b945003040044092070000401000192501c0c0581c5c0e042005001c15990150b0600d5000e4540041003030007515125044501d40d118040d0340c1c040fa2002c0310a108c3d80f018241c0c880c0c01030048041c0103040280750380000f8100101d00c1c50401c9504024510200054005c2111240560310f030694401c42c03c40c9004010400781c0100e2420000300559544210000c0480700d5851000510405c00780c2a1124018036403c00704540c840e00c0450000c156002241c241204c80e0b1003500b540984 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 359612374 1250 359611124 359611159
    0x3050a020d05090609011d0910060e041406011110020a05040314060702030a0815180103020103050a0b031902060f0a0c050601151205090a151d0111040e1f14 69
    0x30f00c004064000e0f609112403010b0354042e50241d42c031030b07000301c2400c3c02e000d071040009040854100c488110560080c8020801c09801080700c88228034200c40c02e0040d40ca034030422030346155000b080c082c10060a00420000e280060000411038019403106654550b2108005003e43d403240c40101d80d01e050303040000840d42c0c40861601d0044550340e000c0c41c0361202e2130a0840f074040026140660720712109100741020740e1625401c59604010301c28078200c0c0d40c51400050226a00104100e141e5801e1030380f0740600d039802040b850590100c2c00501402002580085007070f601540030100000c610020384080f50541001c03000402078400d03011128680c0e00e0f0b465948080b0300c10144680400c14208074041644250781003154001800c100f224030001103a190396043d01110780c2007864403070307a80608203c80740d400d500101003a090131000780403680b9106015503462266109a6043c0018040498684c500746d0302d824040d43c40508420071003030340711142c14890070440002c0303500c110810240350b11000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 359613624 1250 359612374 359612377
    0x10f02010e0a0b060a08030c010b1309030918110c0303010306110705120304061b030506030105160e120f0f0d080a0b091306020c0f061006050712030f0b04060303050a020d05 76
    0x1440580042e00e48144182d542c440140b02c0a803d1540c00a4107100100d240f142c100301070400c1d48580c4c0004612156440c0070b1008803045030801c1070b840d904000c22034002c40d4021480d10101c1d0700545410b00c1040c0d40e401220001c0401522a144c48840002c001401640c000702940c1030300d00600082181c41581003240e0004d10610300d0090803600009a0140750705218800b03154818040c00b40801c2031200c01400e283c1427200c904007100442c2d5900c09024050500740700322540040c002c4081c0c020181d16200c045d181c1111800006d1181c0008e900e1542031242c01d10441130040e850800321402c0c15041c00b201a114118150000001880b6030001000390708607006e010103030ba2001d0318244182e200c010b1000980c0d051034900b074038455000c01c42e8030a241d404002e149510500d10021300704a0400141c4501030b04541d03804402001801c1c001100445c0040b03110b460524944d0400081101c0d00c1d20f004000b401c001c02e40c580d40940360100000a06421100410340ca08155094030103039440070005441c030b0b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 359614874 1250 359613624 359613641
    0x51002070b16030b090c07061505010e0d11030f030c160e0a0216020303030c0424083c0114091909030210110a0206090d0c1e060501060806010f0201 65
    0x1210030000328041c040d04284182c1c40003510300e00070034504040c0000c40da0288054620a248420000f001c2c424000d50348603601c01c441da00d0706050f1100c0d00d4800002c00400c90702001511071030614110004211a42000891140000c0c2c26160f80e4220322070380d25240e40056860741c40d24001c01d0074041711180e00036001c00955040d020149800c0e1070f612801c3c4000c0d004507000780440c9044508000250f40e0801c0914400c424200d40e03070b59a14241410000c1006a0700303903030000c1206064140d840150003400084e440441358158106400c0e9601210b141000294200c03c1402000b840c20b0107401003000e000d41c180d8407800e20640c1c1d2801c540040c05041001181c02c038024a0903c1814540590f09800018496000340b04a44010900070310701d204071348400ca46025400301c0090b15101c145d8051000741e40c03000300d59001d41143c191400001d4062003071814001c110005a00c8001084d401002041540301e4002d40104601e42c2c4680001c0d042210569665000c20810684180710602c1405051203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 359616124 1250 359614874 359614883
    0xc03090201180503190620040f0812030606030408040f030b04060b0f0a03171c23010303080f040c0e040b0406060b0705070b090307080d03090b01052e02250305100207 73
    0x40503481c801c00300c20b00000349001c0360030075121070307c282100001001400d140c101e942c00c00c9a070740380382108110002116078030005194210070100081d07003000f0b1050340d91118007925116070f45c1c0d680e17183c02c441300e1040750071900c14a04011004024022500115031040c0e101e01410001c17003450208021451280880856200038142c00500c0000c407802084088100030030585410080000820b00c04855081300c000d50180c0d07681e050f224601030030011014601103400e240c9141d5415520020240305008050059020701035010600300a101021328000303280c00d510924141c00d091500f184034080c02e49040d5085070070800c02103000800101120b290561010041020718917000a4006036009060130320340c9400b0756a00091400d00c203200880701c4113215600081d21001700d1070090326450041c0c00017800703070b4042500b12203100c03500c404004a00400c04581006112441000c920b4480741009044025407121a09004980c5403214a03090b21700c600c0a0b035610802d10001c4108070300a4610250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 359617374 1250 359616124 359616133
    0x30f14040201110c040c082a041a0720100305010b0d09052d0607180905100513020c060901020f03070c05070b0a0503060f01090e06130209040c03090201180503 70
    0x180107600840b09040160340752003c1c0d60904c024a00003404980000307081e200402c6000041140750024280ca02d050613801c1d2040380c000400380c0030307850402d01036801144001c280c06416000d40400010030340c0d0000da17200c0180d000d900c0720070f1443c400442003444000c1c02148024414002c0a019005082c10380300841980d500341040300c13441c3c0c0080c10802c0004e84490048200288a2601100c5100e60340c100322001300001843c0910760528000c2d00828580810508200310403101c403d545412044400c2c0380700104403910b6110030200d20780081c6d4805940b00900d0a02c0740700020264010703180e240304e940181c64095459101e081d00703038440c101c007101144000b000040c04950244141c980454052411290516120044d650b40e607807240040074003081d80442081540e04d03111030007000341c050a103000c605151410707071603942444029041c184160004904035070084807035410349040f4500208148441950a0b00c06402046131100036070002d070440851521005040c000c901c101d460250040 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 359618624 1250 359617374 359617381
    0x110708060c090a080601030b10090c020c090a0e16080c0a03020604030210020f0303090c040515031b1512010e0609010e0103060f02071b0f0f0b031602030412050a03030f14 75
    0x4951076032000b52203a42c40461440007254000080286a0296116241e02000e9040c507240c4803181c69040e0748071480301410040c812400b01d03070100340c04000b1803003565490230715110005580c0c0a410070451102c0f29100f007000e03102c1004001003521003124100303800d8800e1008245c090107114400ca010103500650104820801030038a003d42200c401d410348151025a080070031240c0c150351042c2d80c180c1c241d51122030742901d149000c0c8203880d00040b0914080740f900c12000007181d152001408400440352070140c5c404030f02d444103042284111000302d07440c0c1c0e80394074640710520a42000c1c000e03c49a0314036040056203d0504564581c1610314000c0f1600f481da286d9170710003001d00108201c00104030703000d010316000507500e403501c640d01146d00d0205040e03407410018480070459256114225190404104015000e030020407290400a25a4130031580403040034107a00e1449613600c1a106031280980940c00e000d8041000300c1d13154030075034042c820b064088280c0010b540f0404860502c40c601000070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 359619874 1250 359618624 359618641
    0xf03110f070305040506070606030512090f0d06061a0d0c02010917030a021b030304060b0405101e0506040605040f1e05090a0b0619020c030303100302060a020703080d0c11070806 78
    0x307401480c0c424076015180545400205a880e041000e080702c00c19120841481040000d01002c0d0249041070f1545052018800005061507100900140105e040c200300600384045600150003404844000e104a070000b00311161043e071022451146542c98040e260801904c1030141800d6250451050801c46580e8403698115500203402d4600d00c1d5820001e21010404000798034510400c144041d5440e882d003400c0c884103890b103e0310103038880d6142000b04400501401c2031340e001d681c100064691447c11449548128040b142c0080d80d1008000c00c0028030f60383d00100400564014140113200b51366180e200111400d0804449004005031040a100e503007040300d0b099034412042ca1011500102c40710103ea9964440c4013210740b15010fa400c8000701640401c541642c0660075802980383d0b24005132019800005408020308ca000000340ca5144a4420030241e401b464100030310660320803110000b400100318202042002c54680c00000c840444040b900c0310440319110302410f5142e6aa044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 359621124 1250 359619874 359619877
    0xc070f06020a0606210b15041503050f01060509010b13030206070602030612030708191e030c022a0402091521010e040c1712040f06090e01031109071e0206070f03110f 73
    0x4000041c0c0c0391001f8840e0f5a8441c050503c1ca0f02c00100560105c50a600304503041681100150380079a041c500100920385610061034111030440b003002d42c90b44a059055103858865a0000e98001008a2400705000030b41d802107005070700c212001521044000009a2207000d0008081c03d03c0e0b6080c04891480100c08a103080508100d24000d4803110341e0044000e000c1c805030361000006aa00c50071b20000b540c0400880f0b00811a04039080b42044103c030300560198035800b50743d8040c5070085207164064641e020300951300580702c007803da02e42d0440d8512a000c81614964040b003000240700000c0c4101d03820010a0103076404ca40c6064009042c0801c40c680542e000c0300040c01442541e080e40c4003140e8107400b5101521007180c400001030302d010750040407581076820001d2000f0300c201c010400100750707402c180c030b4040d030540305401d15943e00c0c5d105131460f031031501d1500c104038000300a1602c42680424858411041751710b9000d400e40e460203044086800c0000c03009040728080001e9608500c4060 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 359622374 1250 359621124 359621131
    0x150c010608150601080406092a0522020a05071e0302061e1f0801091104110a090e1b04060305180316030806030f0d050406022506050c070f06020a0606210b 68
    0x1000c80c1244c0d159680041040880912728074641f008054004142c0c0f00038403940003800c048518502800d54091030144003410b42d0714450711154006024a50203000350141c40f0001d0700414224031045801200d642e60001c0280200c005004280004002001c4d41c01e000f19001d400b641480515540d0203021107850201841400072120b0300e00000450040900560b0354040c45040c01c281c860001900340004d41e452004c0c10309041100340940c0745c013140c3c0300c101c881c12240b02040c0c25000d52519441d48000802000c9407051540e00054045092601500914000c00740e07c2c0260100c0c001311150300340c0b80d0280081d00362012141420800c04240f18800d056008035000301540d4000800d8545a440c10081c01c594001080011404104250701480003003064001649400255002c0340380b1402c1500c590b01608080c0100031030b40310f484090820403103000d4002040100500c3d071f10303550065034a50084108642c075909051002c208100e034001581b618003011108164680d0b45d80d40c44020a00004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 359623624 1250 359622374 359622383
    0x80622060f020f2703061f050a0b1804110912160807050316060210050a14151c050604080901021c05070c0b1306030b040209150c0106081506010804 65
    0x180c1c034182100d007a070700c01001c0845140385040c1c0e5401d080349030b00b254503488804089425002410440340da80380800c00a40c00300c0c2c1803040740d49110306034030b001031100b0441d00140e4000c0c5840c2d402188801c00e0380d0040c040000d048074022440d00102d020441500c0da4650501c0c4030050038041801d542c20700f0480140c1d640d540200355400014080c0819842c0005580660b400740c0c84134408109605092140114007201582840e0340a03040807400f0707585056060111034072550b9140003030301e01041c0e03602c5600c0560a41030071810324140081106c1d01d221082c1c0c5414891140300c44002c82055417803001c84042644400540010350315510751441c250001540c2d14107502400801c1e03d1022a80790550183d80b00c5500c44940f01c1c00c19083c241c140c0d5909030010241e101081040101c8007400400d200c048805600e40882c205001c0c5000c14041c1c0516202d8a2f08024010040105880040080d00716a400f1900030095103685284131070342c8080010103948025044808900103512980c12141d119006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 359624874 1250 359623624 359623631
    0xf0f050d090c090e0d17040206090d030e01030c0315030209040219060215130515090f0316120804080313020402070b010b03040c0f080d03051b0703110708062206 71
    0x4a055401d8078102081200e99907803211050100320514400c0d024030f00c00070341c000c0c052545400700c0a0f00038054624000060301001000400b10355800c021150404000381c0301031101c03c042d10303000c0d00002c40e5010443c0801d0a208281c40b2a078441e215070178801107410000d08502c0d15503000d1090010024209a810000030842401801c80401e4244002c3c450343d40101030b59000402c19015410000d8458105000b40307039101c2d404a90300040e400c0d105159a00440f0198980e030090602d001c2001100341400c1c000410118039442c50003041c42c18541c041c881d94048580c403040300312051380d03003150028882c030020300101d00542885000112440d201410041c0360408a450b41d1301360202c241d002500b1400f00004001c2008002c8a9007801403a050906490440c01d00708400d4450600c0113480b0101942c500000326080da40030407018283d400c60b010b9030b40d1904103040041810440c12440d003002d100e11100040d54800008070316100e5181540d143e04501c56000840302d000580c8541074400715103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 359626124 1250 359624874 359624887
    0x307080109080304290c03280e061602120c01090b0109050106120b0102030406180f1d09030a020a11030f0d08160c0b0a051b070302030304210f0f05 65
    0x2480307100342250044980303584034642850060b9103d020003040c6512001085484080d800310131340b80c5900050415822612940c403803154140e55070ba1420501014404032500c0000303800c2d254400801c00c00c202d8143c41250b95011003010035103000001c0d01006070310011114001540350030281071508604000410095442d4942e510300c5002a0031038950180c6e1100100306054110302c42034000e14040070240320007408200048e40b24051803003400d080c0118094401e2441c64004110806404c068807007001c0035440f000c02000c00241205036000b000c0104011840e03034280001554403003d199402440700483c0c940e528050340e68a0418079825101e00d544250f40d40ea0144641c105508095855014500d070825407024010480c402020900604004501c04602c0c5da00500380d0000080b203010490340c070365005114840030350140304001c180010800e502010f0b8007000450140d4002c08848030107504960360300d94165000c81c0c001000c5149103d800300c8050140030038a40340191814410300307010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 359627374 1250 359626124 359626139
    0x120a080c01050106111c05180607150b030303012405040e070206041e080f03130b07110d0e0f091f03151103010515070f06020f0a1403070c110307 64
    0x10840d680340511a510340300103110103a4070074100000d07000e03554001c1a450144140d262802d4008102c048104140011a800980058040003195000c0907110964840003410041c511080d41401c00d21390b2402c21a611000e0b1400001387e0b4184d03010790b0040c0310f20021f01d180b501d12203001c05d50306c60305011007480f00040e0600144100c522a00c25900901724600d4a45484c04101070200440c00c81c240ea0400b401300410168801c0d228000f40b41003e242c0e0b603840e800400009140d0304100101405003c2e810046003e511003290607910100d202201d805800005003501c10300f0080720178603003180603600c0c210000e00d03007094110782104010703100001d00c03000ba110202c0d403a051074009413003c80401c4140c0910342094030031448142030141ea09030540d41840009201c0b180301204013030080c0400301d52401804070754000040980e80c401e100b156103d4008041540640103001d42d0030105040028844040d00b000080320300c20507082e603d4121024107940d0700405000100c9000760144543c0c1b01c080b40d4007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 359628624 1250 359627374 359627377
    0x1031106190f26040b160909020304080c0d0216091406190509180f0c01020604031d040204090614040608100c0306030c08070806150a03060515090c1306110c120a08 72
    0x2c0d8503000c90081c0c0c3d450207043c014203008001d42810200c039032100182c441c107540006220241c4079000350240c1c0d240c80e036003050b100c50701415041c41d0312802194a40445190001020310250b901950201610b5507100c03c1402200c490f00000501c0080c010700080c12850503407900f08500520000c4602120b17110400308000550840e41000c10f40f280d105c2d2840340e10b004102001489c00b0b440001c00c00380340b4010000303480e0300703010b880102803010710400411303a03049500c0340d5480305002400454556541c1e00070080602070610400222180e007032059441404d060040c6030941c1c050100800e03105102d5a2010300070902c1050071000c140d942c20011001a00b034103c0760b0000e0007060014101c0030304240c04070b8240780c00500746400c0518544041c00c09611109444400c690300300700000780b81e80d660b4021070b20380780d607000000e64004002c0040160040288020300f14020308100003901e02d503110542a645500c03584006032050303002070840d0030246480061440940c160070b09032403501040360b44500d0742c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 359629874 1250 359628624 359628677
    0x6090d0221061801091a040305120a050402040f14010320090a0209030c0a0806011a1b010606030b0103110d090303090803040311120306011e0e030304030b01031106190f 74
    0x6800040c144950000f800d00b114182d0380ca10740003004004c2d1950b0f290a042424284132010312104000080c0900d40104255000e42d50b210707000e85100d20340007045000074801141c040b48610b1070040170301e00c461428442c03044100200c60380001540d00b507840d8142c00b0110800f5149001900d44203081040d2200303000980660b00d07004015895501400400d0300f8120305c01d050b0f60164602d90010013601c0000602181151101601c00c3c45800201c102000c0d07602c01c04102090098018050b1030f4400e805501c0201101c500c5c0e581003100104500c011810b81d10080c6036a618103e09000203103003168942d10070f01c4407900c00c0c180010460341554400406810844054010903142502d142d10300070b00703204881103142051003ca24501c0e18000281544510762424034000350415440c00300346028580c19400c84100a04a0f61103a44da840d00300d512450074042111441041c1c5903046240c00c01c03005886580515041c0d001c0c0400c1c0303004080345c0003c03081707801c5000c20070010b080c09603144070f2217032144c2e9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 359631124 1250 359629874 359629939
    0x801060e0105090a0516033206090f0112020f030a0b01030f060c0f1b021207080a06060503061b0d0902042a110d03240803091201090206090d02 63
    0x1a81d0b02d040c0400100640080c410b82c007040c24401085a500440820317038490344014240080c0440c40e940303042a0071454444415840c0320720702192402d04080c0c81d1494450b200860340c030b2809030388014040302c001c07030280704040724031020220160040c1307028040300392860703400b80449000200c152608030212400307034401e4814106945520050051900844200001740d08020025100200e001400481201c0540c504035440a00341011581c0300c0260b155018000c004559030300e0380b074184041e256045888200c03101403804800095a081c08100d041c0f14400c0c0480c01144000c4040a118513176100c0a02c1c40951070340da801d070364010f80d2103200c0c21107a09034400b1a10796051102850200540042205034240081001c204041c1200083c0070074140c0c4035494081107901e19072910b4047c45542c090303d04403c80d034081001c40e20040000183c000d5202c01c0b604807034407080004000e401c071610780d50003a4210b001042044814180041e2007407485101500051403550129400010121000788607207 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 359632374 1250 359631124 359631149
    0x181205100c08041e030206041e05061503011a060405010c1b08030409050721021b120702010807090815061f1d012606060708040303020c0316060503060d020307080106 73
    0x1092282c0042c4c1308503440c80008082c01036603040e481c042d5580c03000038001041c03288014140311841042326480590075510100710b4086060074899402064401c202c024080d42c40c1c10301405a412032213801e20610107018114a281500740b02c01199100043c0c0001d0310b00507407945640c1844040c3d81e100e00c000b803444502650f00c3c0c5003003181c0d034416610013412032420400c0c4080102101404a200542440c48a01e4016503a078000304000b403461048076a541c1460060030504024400c2d09002041018404d0341ca040003076580142c05d58015005024a408503802441803011400e04020a140c020b04000c19a0b14031301c1c0420605982078076503045802c0066086101003044441c540000b000b1729400b400d000065541c2c2c0c000400c4007403001c04840390920f43c3c0c03402090541e00c070030045a10064102c4541c9945988a09000c1e58034600004464020310400a1124010342e000c4140401c0d920503960321407660311000100049060032200c240d034903000d80c450004a03000240b04607001081c40143c00c8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 359633624 1250 359632374 359632381
    0xf0403090b0306032d0106060c0501061a03150f0904050a0506090303150405041703180601090b060d0c020c060d1d0a0c06053016181205100c08 63
    0x104000303490303030201c24802030600912402e43d0303000c65407800031800702d40505604c5081c071386207074241d2294561030b24107540303441e10104040c0d0744900252001d9004400a104280d80c4050340b1900f0309040700800078a0000344045400e021500c02e548150b032000034071859600424030b00007038880c0d0080e03c0c203c0f0103501c2144042e042003020302196a200d11076001550461402040d14506c9c8204950300714070941d91440000c04009410303d000c003402c2c28205159071a881d01c08101d010100c80b00c0400d81181c4140400052860020300801c10300c20400780195060603440c0c04110042d040450845040d4000c0c283c000d000e68454802030440c041c0c00c6200401e100b0f80c900c09441e40484160360707803007068001c100240c0106010b0181c0e1001c81d01d05141065507015040c0506200b4528602d0310300d40b80e601c0c81208108004069140f80c020f0750b0b040540d40200700003c400341c4410f0720410554000700040340040024290f0041e00c0902c807030140080c1d4282035940c4c0000012600c540512002107030300c14007070 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 359634874 1250 359633624 359633627
    0x80310081b030609010c12091a07030e070e010f030b0a0209030d20160605090102100c050702010909020909041721040c1203080c07060209100207051203070b040b0603150f0403 77
    0x3c0c036400400b00b0008102103905104000d01200b401030808140c20344841800080240010380c09200300c882d83e20b000031608000b070f0010054880b00120142e544540c00c004144100021800da0407202c03002c41400d0900d255640300280b0f401c00824a5245540c03e008040d51034400f4441c4910503505039503012407925041d816202000c0081d21337282200d9201072000410086440101c5058801e14200243c550388c030703100103c3c0345c114404400f100d218200f03035013074040a40241c060070130307103100342c94002520703499071406000c90140c0c07180103900013800000b2a022a9902d200d5092840305040c8070b500c1c22202c40c1722036440742d102c88444e107210385000e401c020502c54012072090150500101c8410a04015200180050001703800d404961030001461002c121080c1e044a80301100540310504013020703140065101e070900c0c42461b00604907600700b0f80b010f91010040b205850342c0300c2e0001c101d03a180d5840c0d84107500c1c801070180d6058450031ba9800003103040d0010b018494071224201c483ca07407809180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 359636124 1250 359634874 359634883
    0x305060108030c1b03010b03030f0406080105011b02040e3424030b010207180e0609071802070c090603210306030c05060306030106090204060c11030316080310081b03 73
    0x180198006110040841d140403603680ca1003008440416132040344040020b005264080400340c2c1840300154840401c0d20000c068811501c5035140c03107034141c1c0e80340010750303402c0060580308a0600c213a203050300052410350300a6030f816080d102150101409a20101950f50401c441d820034001001419030380e10790080c400b00003070410300038030200060301c4204040d40281d240300703c0001c1c191a442e0000d40b5074802c0108400804014103084030b03408030284604010100e500601c029800744000040380c808001800c04211070407040800d4151020703001d00d07000bc0d00295802c0700c903203400380070000d4502c549000e007001650003840000c015030116904440d0040d600d042c02d806060a2510400100384d200001c80202c890540d19a642da0b41e5402c0001c0c010709454001c421080e2002c04c010802540c0030f0104100144954014941c040002d001c040c0c0d6402401e40d40c905100c8110382180006581c0c002a50b04141c1010064041c503807100d00f07940c00d040d03200e0006442030725100d504c01c0f2070346002c02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 359637374 1250 359636124 359636129
    0x912260408070b070b160e0607080438160203010c02070e0717060108060319050d020c04090506270712060b040b0d1e2027060112020904020d0603050601 67
    0xf0700040c60203440d5070711000301e030034010600240703c0040340c03114070703080d0050030a21044507005048a40d07a0440e8a03108559810500800e200d2075070011070381c150380e600781c0841001d0f55a10035119200c502d98070b0b0300c010180d1007111049a081c14408002005131000d004620f1540000d8018001140c104014400300b0300000301160104201040e100c5c2c1105046d0101e00c0d0030010070b180c5040940d445c0004a45402e02445980c00414018084001405000b00b01c8441c003400941c203441d00c02004a08000c01d031900c004025043da00940c0c003244480b1001c0803001c480c40d0044206004101800d90f0140c240300c626400b0784008003100790900100705451040d960001402c0700e040000341940c6011610b103500d44800144101c070205515014201da85010f5042642d004000c19100960502e8003206581c2c01003010780106c441070740c0c01c00304203a8075800710001d11000b244d00d90300d99030703050044500312607203000d18190b540d08204142c4547c4039400188084030690b180070515603d58641503143c040140d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 359638624 1250 359637374 359637389
    0x2090c0307081003030e240d09020a1401021b030f0d02010e2107060504080c070620010204030519020a031205090109060801140d1b030b070f0f091226040807 69
    0x43c0390030320009400000f000c00b07952098960340c001da18150340c4001038001ca50f04036001098003064680101020380c115105182c0300b600c145c1d6446e6601c0c40405a040b08446505016800c6080d03035100f0083c48805069400030024103c0d44e0340d03480d2601c041e0801c43d249000d080103035103030b50b09024101e008100030038640186e0040070409844c40b40d44d0306c40c540540340d00201000d40304c0003c0b81c103110f420029910100008810f48004641d2083c1c05002010703160314843ca1600544143c80682d00d061094404498011000c6c0ca03103044007250a504c0d507207a000c2c089a0200c00743c0c6002c80490300a00c080b4104c0c05443c2c907002e80c1d9030803000c0098940802035108008000b2040d0040c081041c00c08a140764804003652142080903891802c010803041100c021450f0000301c00c800428080301c80c01d84d50080440e41c40340122840c02c0041202c0407000c12001001243c0c4100003000b81d414480c8654072900e025810846840700284581244c0c0c82d024000849440e070080f50600855070144201001480704 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 359639874 1250 359638624 359638651
    0xc0702190f05090c0f0a0309170a090f030503040e040312051501110a11060708090405070801031416030201110115141915030e030c0a0f1203090f0206031302090c030708 74
    0x800c4080049200d41c1e05c502c8803032100414040b0301940a0f070400041c00b98011a2500070055110b50502140c03c80e068010002d041600d0000c1c583e100042c00e202540e8100018500e01030074000003843d0054050021400c001c111000002188824807999000ba10b060f03421003121035000f400140042c0c0340001c01c8010340c00c60202e18000500610080f40d48001c1034803090745445250610551034001c4003002c98006060404000390650710005041c181c92003034508513504d4400a100e01d540e0741002c04101c1c1443e120000138005903008448241c207441c440d200101e01c9240b02c000d0141c4229482e44071050000c00b90188020078034111034030141000f01100407054480c03074070610083c6039003295011002d240e0b8410b0703625194642442103070780d2903240c0e9084404000d07592522024090858206036104541d820002081c944640590300d1443e401c00c030a4040441c083d02008280c1d0b001404c0a1600c004262202005072a00340c005446180501800c5840f85824103000c3c001204c002e007140b516814 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 359641124 1250 359639874 359639881
    0x1030b0906030d030c170114030607110d1803020612060103050601020a02151b0616030b01030524040b120610050102073605010b0a0215070909050c0702190f0509 71
    0x800051101c1e6a16144c980812490754001003518440c002d110014420324502c0004a219040010111100070b000e504407005560f980303800b1204030030112900c14054014400203140507101f1000741c560060700140181c2c4290b92940040c14541c8103140304220444618100724140d82c141c400d0a50026080c00903001e90a420350002c0c0101000604034180c1c080c01090700f04001200001e10805102d03594115102401c024401e280450552085500041d09000580d03949500c2070064030702841005400d4490600d120015566030881c005400e60001c2d034509801c2080d5483c103e12260348070b0400e0180465081c515841c0800000941001d81958003510301041100034083d65003d00d18104440141604100300161080180403041c2020040c1404c00100d100a1030000501d200343c42c50302281c43c0c040c00180d048071802e000321800808504491010040200d903500300c150320140c91802c96262840079400114041613060301030076010707440b0409000b81c4069219200c05001c088540b40100e14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 359642374 1250 359641124 359641129
    0x160b040501110c0a0201110a0f0309080601050a0f051c1b06080105150301120602090d0b011e0821040b030f100b0304020616021207080f010f1a040c14040e0601030b0906 74
    0x14501c000003030407c94048115201468103000b4819050f5020045081038001400c009014281d20300985c0b59500800000003a03502c4d15149a0045980741c01d80e0340020f41c907060401c100585204109a1194486408180020480b403903154800c01a54010040385040c414000e20780c400582045000d40041c003403440305000280c003560704442c00e10304403c000c04d03458900381c0c0203409039005881c0c0101e482d504150400038441e00c1d01341a0b0b0303443c11000c0c600d0391480440140c11040da103c0d28455810065040405056100c101145140c101d100c0a28055891144002e16801100d0000042039110103101c48080310300284402005040d0306507040d03040c0358001401900c00c58000702d96034000c0f88511011900d40070752071541051070609480403280c4d10a48261548000300488015501c0c0c00d9403102d09ca12640b165400c13000b0890140d14000e2000400d00005200400300305040c490a40003038106000203c0c0140094000354045142500707000001500380c3d400c00400c540314058480411400c0d8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 359643624 1250 359642374 359642383
    0x5030a060213030803010f030308090d0807082d0a0e060c1c0b0301020d09050c03160902030a0b09150301050c070807020d03140f03100512030a030b06160b040501110c 73
    0x1190020340060360b5450580401d01c410502d644000e10345207000c0000600400c03581500001c9038081e880385151aaa0308078083d407583c40c2032011030049507000e07020501080c482c170007065004494051030131258800d00510031011007078601c0c071a20b240800d0300b00901540c0501030410f4040d0504000d081c85e052041e01080e090242e00a8009031a90002406c4804085508807010b5441c020b0021580c442c8402646030250040c07500a0340d003032181c000000018100095440350000e45504440d81c924100b54844000c1d620240260030110f455440440c219a50241d90900644030396031101e8280e0018810303d829640010041c04010009202c10400304420034103c4940c00c0d41140c100c410940e6a240540b00540c1030805152500c0c3e000c203900c515461030100450060500c1004000d801c0e50300ea040110442540380058540c0d0802d20045080724001c0d001401c80741401010380303040511221440300c0408008200b940c000b5102c10500080c000c081c0b0400b010b005c024481c080c40d008200201c2c942c0c0d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 359644874 1250 359643624 359643643
    0x10b09030604030c2f151c05100b0c01020703140c120309030403050118151e0c030e061317040506090d05010905030f0a080f040305041403031b031b06103c17070503 72
    0x10b520323031000a0403018000d0b005006880350481036502c3d0400140000d0007508000812030100d64000005090071580302c0558070040d050100820401030b501080a101d5007015045040512091101000154081c01201410307615500c400358100114203040c1140900001ca08041615042d088450056001c4d500b59a00b10a0140800c0300c54002c0307801c1740105420040070305c0303d0180c43e0500c02a65150044160000d0183c1100c0c0c0b5481d0702c801d40040a485103200e45540304004011109603420458001085507005000004000308941c07a0682140d00903640030380703c05800145803a540350098402500045207106d041028649960083c241c1e01c101c0c0590800c1030007000049500e59420801c603034541c42280c0090011a06000340107940350040c0b109070040c12001903a00b1140c001c00030b00075218601d0001031030201e0345003810130071040c070580f60214074402d07031185868043c030305280205841240086454464516041c020304045200041c040d8075500925420041070343c002031000704d07 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 359646124 1250 359644874 359644927
    0xa020a020a0b040f06060f080c03010e060612071212030e0a0b01050405180a0f030801060f080c09060d0c0c061505090103140f120a0305010b09030604030c2f15 70
    0x2c140c40b5400c0041d015050745400030300322402d00384040380d010303e085503141c04c0f41d00a030704880c9a298040205421381d8102c190b0000c50354403401c0020141c0c0f405d043c600b00d040d00201c040d65221520350800034522043d800041c0d946410214016220b90350502c2186103000c0580007800d0740744055900c80040d984181b107041e104030b48030f0010880d00c004030100b11028125200488034081124903200020414907142030700456102700001800354000c0b03807840d081056036583c42c0f41599039040741503034540181071042e40040042c00200c1c8884003d1151010710b48254540802e562258500350054400d01c208010b4a07001e001c030200b1850b00e03911000345c10749512201c2d141240c08926a5607142c50448a510f03e0544511003c22506031201c1d401012413610542e4240116a01c4400401442c0b00702c036545a01503211100050200e0b01c1100c24940c1d852007024440500c0c010309d030001e420214080d020000c15a00c000c084400c615100e810300c41c154030030160050804100b20074603d09046030382251003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 359647374 1250 359646124 359646143
    0x15030a030806040b0a29040b07030f0c080a0c0507061110020d14070c03020c01140a030504060f0e010e0c0f030a0f0516060f030b0a140409020d02060a050c060a020a020a 74
    0x44180c3e45641020807440700244c985840e20f5502c5550300c022400400c41003a0300324454401c48008401a400c84080e02c5140b44144d203400d201d5a002c4500c000200605001c00002d20500d1000580c0103004140d945031030769424070003012900b052410075040c0c1d4404001c0c04500c1e9241c0c401c0e1b1001040075181203100b440d00580312240e0460705000b13062410b40199802581008218140c2d4112065200c0c1f00c2c040d9003100d2022a801e001550560303100031b807a0240f01e40920180c15107034840d4000c9036000388104400714001039841030410641c0da0300d204659032a510360104230000c80041004045035042104c050490300b40c0b1344042a1200903101c4090111411000010103000f0204031005200c4110071b00c1281d200e0b510140200403000103101640000e0a10280710041d144c100c00340001d6170140d0b0024400041d01c0e10420001f8420360701e04a030010580000709025070360b204003404814480d522603d5540300c2d4004014108072000b46230500717040c418000c0c01e070341c02d500244800120343d2191465 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 359648624 1250 359647374 359647381
    0x24091505131203051b06070e061b0d020f1006030c1703041a1b0327011101060e06090c03040f0213140a090b070201060e2a0a08010e15030a0308 63
    0x1c80d00550310340c0100b0902c5a0a060240425a200d402020741288003405c1d521000c3c04114159203507079045c3c42d80700000312415101009071801800420100d41ea200302031410818101840d403c2500c40c0201c440540c110115200c0c0342d50b824401e101410b4006103040103640c1c1035550b1080031050360301441003803c0e01c14083c441c1c900020000c4070b0282c0306003a8807003110b01031041d00041551141558440300303000301485c240d00d404000142c3e411481c80e0032110a20b402038420140d03010783c140c904641040104030005e10301c14828441ca502914081042001515203d018400c18586c05004540d41d000204100008070b2640011605001d90450b1425040c0100301c031010040c00c074080b0590883c0000d00305000d40380c88a40d00c03880c0c0c41e80c420004c00348a9a00c115040e400c890251080d50800720b820000aa5503205a40d0405840d82da03521024844003266406000ca503048400c0900c0400c00d208014080c0440d450102c2e42c1c0300100045201020f1a9800401e03203400f805c0000506018030384020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 359649874 1250 359648624 359648647
    0x60f0902130b0a0909030e0909070f0e010e060303041802030606070b0a0b0312131e080f030421020d020409060b12030d051003030e060f070b0124091505 67
    0x8110526001450000111100080360004080303495542e40f295003150b9000a080110707001d05c60000b50507840b2415030300104010b001d541080140b00000740c0c014907030007044814216100401400c541c2c145910298181242c080f154040a480a88245e0040c041049049401081103807049203908016849440d6080824804c1c01442401840140b40b00104003004019500030344090704110104c6803d03007000b420140061003004003030075070920510b800388540003010070f402041d55a41105441181ea17100902c9007449500282904950000502049544c14110102050280c440544405070029030b0004080ca1014213000f03018945640b8000144007880d03100f001081e101421003c0c2542c44044807030749a500803888000214500004600d054288440e41000d480d07250b00c401e86004000d1042040680002072854000b078010000e420000e0b0340e20307090304d00a1011039106416210061030a40c2c650a00201c41700811021020400080c0d807601d016004495050412582e14807a0002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 359651124 1250 359649874 359649881
    0x141002070803070303020c060709140f060c012a020c010503010306050705130f360504020607060207032001051603052e0303032f0307050d0504050604020103200304060f 74
    0x40c0c2542e01011070340106050301074008202c0800148180c4011382c2e01c00006903880c0403140100bc4181c1611038840311300307041100e00d54007501da00401681c2025514096a425034080a0614a01800d51078a0340b1401d560802880f80400e8a40094920180030a00003041030005110240074241c0b100c0100740200c0c022000c9403540e550a480d5507408640780d0003001e10148051142d48078815002e50013003000c3c038401d4070a80d69522030742820614071000c941c50002512005e0000da80c001340410419000640e18401002841e110b500c621506409018546201038990401f294160b4108410080b0b030342c985d41e0b0703410680381031424001010b858007a1581044611035a1640c4c54901d0f85041c11407105070302081000705c920036030741403011410001541c028030380c0c510300c560342152008084003040803c070009180e01c050549413481c24550000c0080b001d8510580703050364284c00107401e00055581c54002d0540c0280d140103440b0746408900300105440c0320040028000680e80c82401c20700952a80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 359652374 1250 359651124 359651129
    0x60109060509010f0908150907080304120b04020f09150103060909261903050105040b0103020a1e0c0b15030c0405060319050307240e120702011206050402030702010c0905030714100207 81
    0x100311800c022245109000b043d078140c232112528400d0800000310008000104d4050f03940b04503081d258107200e540e40105100001c0c0c02240d00042c08203400c1400c0d11040d01280c031a060064550900d190000000340444e0260b4008080c028101441c0c4004906c00100c14030794441402c01e118041d1489a0301510304cc05485540c030200c1c5280c6882044443d8141c003c0e5040e40c904503000c002e95012440103400300d2007420750640108600702c4840300c03802c94120201c007000703090b0b080c0090061f03480e035601940c00700b046441000d40200d41c001540c00d070400300881440900c050360108604d00385000000d40d6a00040f84900c01000e2400c8001e040180a209441519902440010700f031280300240d10040c41541d18519036040c0340000030014900c0000e80860030209202c0140d1801005400441d1401e00c2e44150010351521100d0000c0c0503143ca100a44c4180030030b80c0005580b010300b12000303168120541c0705074405e41c04450180318042e4207259803014100e00311201d40001d400950164200102503 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 359653624 1250 359652374 359652389
    0xb040f02130c050a080603070509070813080d0603110a03230f01050f04051015060806280f1208040b1c1b271e0302040504060f05060109060509010f09 66
    0x184040b2103140c0203009001441e4640c0ca440b01c0a586003000c0c16070b02c0c4201d01c41c41d54054610300102d1071860081e10002e8000c02c6075020308840d40d05545400d00c203070740031094401040c0d68856007002030244520360300310003100071100309011a00d0358444841015580c0ca40c1d1003a08441b01140d2455103042100800c00d8028400078001868104448002081c1c100c41c2035aa81c0110002111201500d00c00e80100e202d0540da0402c80c3e0b4104101200d000c4c034002e043d90f03007144220700403e40e140901c00c240051840d04407590941e03d800c25401c0d10302c10942d41c0c07000140018110b09280028070350070a5078191b50301000e150b41c0b108028043c00d44448901100c0002481c5014640030040d0b19103284c1684849282c2c4030a01d10310f07152031569095140d806444412f007204010148400c02c0f604035103001010103064440d02490f180d0300001d0848605a07030803510565078401020810f0600c0c06aa0380c003040900b44000e4107894824054224414058410b0401012040d5600c7c400d00030724131800038200c01c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 359654874 1250 359653624 359653631
    0x1050c0c0414040b0601080f1f03051501140a032a1a0a02010b061603080a1116170310030308100902030c090310050910020d0f2301050105070b040f0213 67
    0x202d0700442d54240b4103580680f510f001ea00000341082d4080d500283c0180c240c0c103501601940c44041865800b0000c081000010311240c50000c00b090041044100315105540d4080319549084402c02910725010000780c01052088010800714446258901800016210340700703101300005040b40d42c1103050f40001ea03103205141c403140c0f50380c5120700c094240300206400801c4010618401c0100078040c41d0710400c0e40700f5490001400180c40342c1e28842d0030080c0f440780862070b0310480c15500b0103038000d07491300715040312141d0848082c4800c01c0e0130003140080c10003038940b450508007213044014003207010240c01c1c13210040205544100e4010924000c0c29134000454130b070f0511a0342d071142030f800400c40030f12900c82c010380540d14140500c1014080d6280360014164070081803800c1c0041c6d0090042158001d54a42c00c444890800e80141111803a4440d022000c1290703054110000c0d0390182c1207581000424440c170303000143d0000000d074200c1e800404d04900c0f401144006001040c5200301d00c20090304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 359656124 1250 359654874 359654891
    0x9181b0e2d060a12050619030201030905010b270a06030b24130b04050906010e0105040b0604081506031c140d02070c0311030f1b09070c0f051614010e01050c0c04 71
    0x10301c0b8522811010f80590709103ca03480c6c65040110b2907044a0b45040c02121101e01080198001d9100c507070003d10031000880d040c005e0307400082106442d644c01148100700006108200d03070017010341036030003d050308040241c00d08640322802240001000c80c01d04140c00080d0714694100c1c401080071082000302808181341500044e50b0143c070031118050300039800c00c400f089001c80f0101d6158103a814841d15540d09a181030200000b505400d442690030980810011035603820501400519266500c818004dd00b4031038281450284906100e00078440488442a40654440e41940403010301b10340c1c1540380e2a114418200070711070b901e0700400c90800c1c40c9001040140031401c1900c49502181510100c074030707628005480b004541140000c0b40003180f642502c520b0840c0c10f01d90003100c00d10381404030740b400d079a4840c080850741400f5074203580400b61001c50341d01001500009880c0001c44050300071140703c0040c150b095000c9420f41401000301d90410600740411a418120000900500c06e054 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 359657374 1250 359656124 359656127
    0x12d05120c09040612050d1d0402070503071110140703030222050102010c02030a02030d0e03090a0902030405011a01231303030302091e09040602030709181b0e2d060a 73
    0x1440500c4090040d404c10b0800a1041c0c04826a4403074203800c2005841c101240050843c1c648980c05414808400c40000403081c40d100d510180243d039219100a65032000305007000120a5a030001c500d100f0741d1707107458240300c256001380b1000f007038840d646815444d0b058600d03050300680981960280d85242140215040980800c41e24044a40c01c0c2c00030000300e41c080d08100d840307108018443c00035a204125a400560f200d5004030800b00d14038003503a092211040001b0624080e84e4032070040160088140805d202081c8140c1e0300d0040e07240c80c42c034134030360003c00080c101c1401d10004d0070181e5080d01075251800d0b610400c070b88108242d0303000411032540ba403601070020740110496074003c8072010080102c0840d034004803203030114014044601950341c3da907030801941c4005e003500d04024000500196651003060601e0400c050303080049094020f620049140f04080c1038044208946074001c00115160320886100594901c0596080340318680301410481e4099000303d03400c00400075107400402d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 359658624 1250 359657374 359657377
    0x2090d06020901020c091f050901080c0f0409060203010b04031a06012a060e03131706041b08160305150606030c0a111501080709052502010f050103061a012d05120c 72
    0x70320003a0250420140c0f51014040296000d01420085a00070701d200d50b41c40c40c2160440840cdc43c00140081400c4001340d44150a03a0000e0380041000900810148100b2a000304400440b418402c0d02d0300300713403a107000024500c030031034244000c401c200c115069400c0c4112122501095400c480c4c02e00c9a10201d514650380c030342c050003040c1e08905100d0008a4006082c0a200c0e005000e168020034050700c07240c8405400ca03100020301c801364181c003400058028414040b503c50004014000c0300e000b8a503082c00340c241101032440000e41620001041001d41d60001981e40220b0504100ba8031916240e00035035030031410300c4280301c280c4107000458000c04826403219060712001c2081d181015900d00704035043d66019141d010b0600003090003d10140d01804c9000ca020b421440045901ca0403100c164046a00030303041600c590751140c05d507901041c1c44940c48401c000083c44d1000056203403411281504400600d81c0941c408800e0031460587c0c41502503454001414400031641e080504141095 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 359659874 1250 359658624 359658661
    0xa11130e31080f070507090504020a0509060a210203011a18011208180603130c06020a080f070c0513050615030601050a231b060a02090d06020901020c09 67
    0x40310203910192005011404450040707000454084298469507520840c0030342114440709080d0000b4060a000725204100707010051400d03110014840c24240140610300031250403060080490360f003440300742c0c1c44000000b0100c42415060030310700c2007441c41d0750540c580d841d40007a50560070f0128214540c007012191040002e801c8400e04001c00f030b441c01104010314244240030300040a900c00b0b00202c4c3d034080081c031010240e0810188003400420000711583c10607201c680b8011650380c4100100540403aa8101820407030009048101c90b541d24040c0038868484404411080469000b00300070050f2014006880010411840145000e240c8001804220381940c800c0505c4880d0780d00980080381100d02620060351698904492403078140d600c3c2c51140c02c0c449020000141c0c02817880c0c41000500000d41002e500c40388061100b8032454a40040601081d106c0c910400081e89582c3c1c800105c5070549902907000361f1641e80b5200103074100742d400c504c5039070005408030801c2401c0420342e5070b0740039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 359661124 1250 359659874 359659891
    0x301050418120f180602030705011508070506163302180103020714070602030703030e120403030c15050f0f074d070806070e03060a11130e 61
    0x200c02484003100c021164440c0190060004001c8684854826035400401c2c8050f070610110000a441e007400c2131110710342c003200050304046082401c0000a00480100000d081c18403403005017400340c16902c0c0c0f10f00384602403181800242d0b48050480c058545806581c00240d445614050800c0d0304010200b602c0100c62002480004803c022445c4d10076521003111803400205c424551000542c001d50140da004d441c0d05100c0c1a50307842c40f0340208a240e01130016030303028688803d10342c13501130142c07032402c244070f411a0803040e1401d454820050944007125014605a14895074500302554410410704170058058101010800500058040c2078091076981d4400f020641c2c07400000c450364120200c680c004004241c1c042424030f1040c0d0b56404410094844040000480300005150203001001d01c1c40a5080890200800841844100e0b4000400c4c1400050900303940000303030316800001d0601004d1680ca10245e0303101190388045d01c0410f21321002c0041c2c050307141e00c4840010081100c0340b48 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 359662374 1250 359661124 359661131
    0x1c03020f030a09150f0527030109060f0b0406080c04150b0c280c0e0a0f0f0b0109050102160618030602070c05090105061e0c0a050307030914220b030709020f03010504 73
    0x703640f4468440c03141c100c80143e840c3c1d400c00d2080d20300c80840101d1a20000b004038851031921f4072503a028170030034013042d04c035510000d00c010701c80c030300c49003039a40103064070344201e1a0038000c0140c0d4001207a4119001c0044030000340e495000084915041d02075040400845400b1801041c0c0d020001600c00c8a1a00c0b0740c0408030036000030103010002e0540c810300908030703503044c40c08011501c105580d603034020004101c04035412101c01810802c46801c58009210b56440b6652220310303580014589000d04001c1c8050b1503d03400d0501c10308000d071401c1c0b28041c10802c0c00d0300294043d814aa41600107564410015581c42c50a401d1440048215008003485032124000004e02d92174240300311009801c941c1440d074114111548000301a8002d4200022540102000000040c07001c1c00117211300c9100b600c880301940c2c20300c0c0681c045008051003280c0100a43ca40903030182c1d0b440710030945070889049000c1840c0381c1410109041c04c0c6141c0c042079407540003088110807010600c020b941a41c10545040 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 359663624 1250 359662374 359662409
    0x1306050406080c0c21190503040c05010804020306041203140901021c0e0705091915230105180d051b03060c042d0b0f0d0b01020601051c03020f030a09 66
    0xa11984580030b2140c11036440001c2803591145c25100a40254040c041902d04040c980c405403035044550020050016000008110400942158100140c00e080c60708045608d05a03001c00d07901c880c06807010f45861115100804118800e822a095807410252a144242004c60400340030b034102014042c4a04071411144000c00418411010f21007a0640281a4586400c080c054000c1e0007400c101046c4c0031110011940381a41c2c0035507000010b180c1d00e0080b0203407034080c03c03074103800c0c081040c0b2850507101c01c1d07054201d81e48641581d0044104200c0210404100030020300041811180103020380112240c1185a001c00071003181080019029070301207a861000c1c00c002c2e403045000b14032030852818500d880102a03002445d442101c40e282c081d150b0380d00c9103030303000f642d40011606101140c00002c078a149140c50f406140130f405400c0c001410b0035410400001c520b50b985098202e481e180340440001450f108105d10303a90f84c400c64017030320b03550868a10000d100c808a40a4100d03a61080d01c00c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 359664874 1250 359663624 359663641
    0x24120a0e0d1e08060609060a05090a1403060c0403111509040504030203090103140f0f070203070f060b1309020a21150e21030112020d140706030f02040b04030215130605040608 77
    0x1014881c11004007402c0c90b04800d11b08000c040e4011060180400c08180840c1d22117864481996003e0701010507145000e00c412001c143c83c1c04401001e42c507071200c0c18813003000001c8010403640c0000c2ca0442c1d0402140307590500712001030140c2001e0035409814402444141344d004001003030350319000e90b000e1001001c034804924140a00f0740d0ba01005a00e901d001403400e0142c82102c9400c44070910640385031035a907854101c8035194210b8141e80440d900c0f0044440c0b8905104c000003542c01001d018409100d0b1900000d200c038041d8071480c8024200110307480001045d01c200252000da100f03405040406000d00140d0040c0b40e8071026108030700c684c54813280280001d1061420031400300e03241ca441e584c02d161281d000d805152108a0b00401003415200c00204410401c4611000300401400c0e00d0b45040c0c0010103541044890004c4a4410003041c40322813090011902540d405884181486524456045980c89850030900d00e40300c14039404108658040300400071116142d48928007a1034070307910f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 359666124 1250 359664874 359664887
    0xa170a0608011d15101a0406030b0406080c09041104020c010501050a12050a060b030709141005100f03150503150a0b1c02010c05150c070224120a0e0d1e 67
    0x82680580c000505a11342d15400640365921110441001c0d60080d541d580d15960000750701c4580070344a0700881c060040550500c102a440f903812581800002c0c9010703411522043c203003040c24062008800003070144080711501c0e40345004040e1085554042002c0114000d2000780140c910400c910700e000030710980c04520010700c540e0030034050143e840190760395100416800720001d03094002c0d0040000c0041e26481400c54140004441d000303145440da00041c44040c06c1e8021074401d0300e20140c2c0c080c000c1d5116058a072081c4d2a400c000a004410300c141206060456210590604c0307601c003044215240c07020482e0041d00d60303c40501c0605e031103408010381c030785003005900c69596240c2c1d10030303001d0b40c4541c0550036414010002d45035003000200d07000d084c03a401103e002216140002d494401c5081511850b19903080f4107a44203040c030300701100b82c0703001d01c01d05980807400281d000114072078460307592004110000c40001c68210600e02c89000e0303d42070801f40d54100c40c2203c154142c100902a40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 359667374 1250 359666124 359666171
    0x12060103031403090c04090b06031c080114030106031b0e010603090f030f110a1412030c0f2109010501170a0b160306030507120203120a0c080a170a060801 68
    0x300d410111105a91111002c0e800041c207503c403604ca50158021503481e0303031140c0c0c101540070b00d145042900d402000c0c14607014203c001c1e80348000342c2c416018240f60340001000e054880d00c950000c0c20f81090f400003800b40c0743c56040034200506000c00071380c028140070040001c89032440c503020070903030341c41d1019000c0301c1c000c00340542001451200340c00000d00c02d12009985007410f041c50300c804900e102045d4501540340c417003140c014540300325050010104010b42c080c1c69407007440c180d00d940351000c100c1000d80145051001601c80110300b90030b00070890050b2114505502c0b00d403140f0f83c504508054040c250170f103c0d104200428141d854801c080204030f55080d075070854513282c9181c9540d504242d14448060341401003650b00c02010000840c280703c100e0013020b00915680381d104460042505184911070b01c624800e104000710054160000d41144840b03401c80d290380e40704c2154900c20b45103901240551401c031400f5908000d84a007082d0700c80020798546200801c40d0f2184250b28140c08400103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 359668624 1250 359667374 359667377
    0x1501150906050a0912030306170105190911040b010504320130020f040303030f1401030b19111c060801060522201801021207020409110a06020106051206010303 70
    0x455013400742c03803507902179081c03078501c01d1400082c05c1d580c0d01a5204903e100002c6440c035651030300c060003150344044040000c034460020b01084422402c3c1e480b0440011884601e42c0a6070b100c100c0320101e03a001d00140c500900c0c20b034141040501c01e0018500c5c4480c2c0760310f402c07403148011034140ea029521a024914000c00035000764680303100301300c4500c40d19008200700c01007103540070821404002c4800024000440c0b2a49001c50842c1030070f04007000351411500301d400d88030711020041000c101010845a00441260204c0c001e50001040030001341195041030522a4000224000080e1090600410700e04545000b00601a100c03203503242a5442441219440031444941c1c4180c3d00340c0760032001040807074801c00503100c4040e64080306884480550b00300c040300040f800da10307031009803104903400c0c403002d201904031200c042c1541c040d10b0089004c0030780100e50301c1d1640340c00c000e854070300c4003110007005021000301540d07a10005d010344094010140102000d0704e40f51008070000442905a0307505 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 359669874 1250 359668624 359668637
    0x40204140f0702011a09010e060d021005090a140307050904050f0d0804031704050d030b01020304180c12022b15240e03030414010519170c030613020a021501150906050a 74
    0x8c15000342c1d2443c10141034079901000d561103150040c2c2d0f81c0e15030881002c2c500e4845a49890702c0300700304900a07000707034400412255070741800d0301966800300340d0b035060315802c0b5960711040d150390801c24501031784820318800e14462032280000356900020094410340c440d907030301c13140b040c60514001440360b41610f005103d030388001101e510741406900070a05032501841100c1c02c21f03035140e2015548880c040316011000ba9954011025154030510f80d64001b410700d80d0652809014445902100c010400e4000c000c0024224401030a0703100e400c0b04d08462504061007480700c0d151607c20480d2141d101100174020325000c451003103e8090f60015030081c0300280607500300340c500a1142401300c0c044544a040050400464039500664908180c070b94005981d43d107144082c0845410705814054000550944140200080b5548160140c020000000809616200720300c00503813070412034600f501c0a00b000d600011489100c800e100e20300440d42a900c00030050b5407008140c58601c10809650001140c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 359671124 1250 359669874 359669879
    0xb0703021c020f1e060c0a05070303021c0504030e10180315060b040603290d030c0215070803060a091103130c0e090309041b0512040204140f0702011a0901 68
    0x29590225807406a070040e62644620244081d082811040c001100d03074102a510740d0401e101081607640c040080b01072240f41040003c0e000c1c00d00c4c00740c560018101900060f100e5071191030800c0000c5006440c000c00e02040c01c10f0729018160b80031440c420b5010380c07815542e010849100d160400c42279505006115005801e6488111808012803120b08001351646d0b000240e00e0600c00080006001a079000165008100500d1401980c03503800940b58200480c1e186000341c0e41d001a0007101c1c1e0349414203000000c654400306440c403469020901001001180d40001d001500740103521490045172244607554498840c2d00c2100c0d10403544e0501408140000750211300c9002034602d609000b9035038003c1540e92500d22888a901c2282c19840d0b03070301b020503a0241410903008240180c00c00380003201e008156140d0040040c01001d005d408600924004034003503444550229aa407445c1012030542454030704110300d09030710300b5a100c000544c039000001c203009181082d4101d43d17000c010300b1000b45d40d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 359672374 1250 359671124 359671153
    0x206040201021b0d140111040314070f0b0d050a0b100f080a050709030212030c120405090f360a0606170a0f060203041407090e10051e040f0c0b0d060b070302 69
    0x11100c82c10b0000f19035a0747c0c81c0000440490700030b48015841a01414159000c55078900e085c01c1d046e034000c40d03074008803950a010028000003959124136106a0010300d80d5a48540c1c140070713250110304a600b200d40090318105096015158003808402c2c0d44550300c0703549540040d4000c95000301d80200000310301600610040ca8401000705e11540c0321422a0f0802a00c010043e0900302c80e0350703640305042d81c0007804005506082c44420b6105580c00390070f000c00d2070070100c100741400351744a400c032440e50380314001c12212400d00130802e0320b0014802240c83c0b2000782d1170700c0d2000300100c1c000c00c40304441d016404094500f00140f074524696101410301540c0c001507a5480c040d400151089a10030b041d01c1d66400c4005042084000400340c403040840c1c1c002003281032900300007400103401c40703607818a0108152120040e2070700307140e000d812400050f40d580720f041130802c0038020300004180c1002e010000070380d003031200c2c050310840070355000812000b0307581c0c0509007440c458040000c02580061140080c4c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 359673624 1250 359672374 359672393
    0xb01091205060c070c0b040902030412021516090f0f030203010b0a0609050105130801020a02061008010b0108160509030703051c0309030e0d020622030c1d0a0e1c0206040201021b0d 79
    0x1184101d00602c1440d4845006c0c4483c0d402541042d8141c940c04000c00051002c01d10808021500900240440000f001c40394092550000d20b44002c0007000502300e146035210b81d07400f90003007441e02d549403949900c800b0401c00721109071109910940c20460310403101e02d070520a94080b19229101c07403030100d01d0b000054580e504000d0006802004281300094076080a0000741101c80340d0390b000c1c06403854400c82c01c07024040142c20240041c0e04d80a400215031b41c0203900d45e1382180210a0038030505c400a5411901ea2141c280c0071038241c09980c07800010001c002480388040c810103d80389110a2410030704808403100c1d0000540000c94507245054642480f400c01d4440d1400980000d28092070001604082a026000b460074041ea1400410512a0340440314024248114a60304a150758045e070429401016142080703055442c03a5085030108204541324525140782c500e22001505650003a4565000722030503800b40c06600f483c01514017414503400360143e0020000f643d020412385500f440c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 359674874 1250 359673624 359673637
    0x209010f1815120f06050a18031103040503011e1a1509130c090f050a051008090f191a07050a270b0418050f01090e100905010b01091205060c 62
    0x720319904004039400f00000700904080d401410220892a0607140c0303001151001060604018644138003041402916041185050313010b20b41300010f94002ca03903070b0303085128552015074990300c0c2030032144a0902c503c0070044030310300d881010000c4038002c400903840070860003003043c4d004a06150741031607218440068440c1400c007420002c442e0751140c06c4031007224003402c5902d001c076643c05004c114040303503c81035402a000035039481020521300000310790010040300c400301c2800208000941446030410004201162500031070340310703480c0078129151040005205440c82d5041c0d008140c1ea001181070045d0058005940c1d0134034140d41c1920413202200b0303100c0e583d02c114005541036100b01031448401c1c0007810003000c005603101e02d0301000360122601050500303482420f000c10403100c880d20380c41844c115000420086409908155518100044481000c0c1c00900d06400350081c41030561003400c0300c90003a03d9040305c0300d49802c0780c0100c03d11540002040c81e440382001a404c0000c08001d03015 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 359676124 1250 359674874 359674901
    0x70f0f05150a061806030b010608040203030f03070f111603120e06040801060501030c1701120c08030a030e060907080a080c160801020702010305010b07051506010e030d0305040209010f18 82
    0x501d1800240704001c004002e070b503885442510b0b000144910145043d852003010381c000703000c10a0714503555641d001c84405100380010f0107000da00044c00d6440500444103000c0103146425582d1800010141540b4168034071100001c00c0410f0130610900005070b155424040545a40c0030303946155241c1125806992814040080031890051544c68074006000600a02400494020b0428000508130303003210304c0580812000300204c0298100401009041d941605c1030440905040d0904034428034603a030002a0a1000140708070055505601c164801031594094510a4465880040e40c0d04841e02a2482a4110480020000c1c8555000b040810480402d440e04181c2e030301d001d070712240d5083c3d0140040c1d9400003a01ea08569161242c1409410aa901c5500f405225280e142e6241c040301100c040f100910b0011441682c00707408030740a9541d0042c01c88a803820040c9005020b08810b480c03c90196038840c00101d22401c03a005600c0580c0c030800e1501e0600391001060740c02804107411900d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 359677374 1250 359676124 359676133
    0x12070b16121e061d1e13170a03020702040e011a09060f030d050408012a08040f0204021b010e030f1e070b010b09090709060509060d0f0c020105091002070f0f05 70
    0xe4180c085401920010056110013400ca0084004c0020792503500a0202c88280500c13075444058002008050703421840405041c20360050b2490f01c00d14070001c0014541101c040455070440607545034004200942c42500c050055008960a55080c0d0300180c001000c0203448204002450900c143c030942d001400800c03c01c1d40e40105030110742020710454451380082c10004040c080c4403c2400b40d81c1c24400d50400000700341610301c40d220201455804c45204021010000c20140403c90541e05050b42d00180215900d02c00c140707810288030501c500e44c045030750918008120b540001b1058880d00741000b03c0d0a0720b41640d00c4400541c2c40700c0ba22840100d0402444440e01003400203007900d0281c101400c41c0c0e955030911004014000134000c00f9441041800001480703480e1b4800d007610221b4400340c800f070351210f00e00c6581c0c0000e41180284ea1100628188a0100c800d50541140740110405010b844c001940400310754181d00c102000940070100c030803100c4c000204500c00e0752525900840c2620b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 359678624 1250 359677374 359677421
    0x1050f0d1a090303090f060705030a09060f0e011b02012007020117041104050c1908060a0918060c0c0f08030601030e011b08010f061d030a020312070b1612 68
    0x14496401c181d032070b0303401c940c00402005000f64080261200b0440500d005000c01c0c82c1c540d20007031003440002c0c4240f0780070352a41103000400c070a9400400c01040702c0c08003840000c0f002ca1101c3d00070a20080c841c42601c85494110409a00611039808024080c1412030140344d44000b03c0b081607404050200e041040000c0b4101031002014500d5003d82e200c0c060001d4603001d68410003040e9040a4034038502c0c100e0400c400c1d1b10501101c00442d1682005081907120b0381e40c0c1e400000c0c981044d5500c090039540c24854408581d8901c40111a0903600c035103010080d0244e80f0b2400c8501c180201c07001404a03424a900324041050b00020316849081450080303a6140880039990944903207a00c69200b1035150070740c2c601003d4000212501525908002201103458000d0040c4a00e14005100340c500c103441158948a403414400f050800c0d4000d4100e0f05202030304940811107500c00c803401d480317441e41c010101e50360043e171040c0d02d502c820032607840505000f500d540c400c00514804e100c3c2e2050601d5144803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 359679874 1250 359678624 359678663
    0x613060c2118082d03060d020d0c05120a1506260a0204060b1827060609220f11030708070c0210030b03160302180703060e131a01050f0d 60
    0x281010400c604c4805804c01000041d4200302d60031000680c000c080610404c000c0e0340302ca003030780380d9080c0d0101c13219403400b00c0d942401c40e00c950304e54000300d4005d0103480c414041110700042e0300750030030701c55445000105210900c84044400500824118510000b8020004410040200082c5801c1010b6441d92040d5500050448030258800e00d0580c0e404298039000410320410901c0b42c56043c0c0b5401e0040c982c1e501241c503c1120011190b10f001031050100c0d2168881c2019038060f402c4c007504003e041e05503000201000c1c403c150a48a039030f81058205c42910700540541c0403e03a400068080c10340e01d0f40309090711140c0004000034104504102000c0240c0e6420a8407620b00000d0b80b0300107942801d07001070500f005042084d035084206156810001030303c0e00500710b41c4560625a0700019a00c84003002c0307001d41103540c01803981754044002c0c01542802404170703442c2c151003980d41145000700c801d480205664240304203a0312100a030000f250b1400d00d01e02480c019445024801900d1000500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 359681124 1250 359679874 359679877
    0x109031b12030e0f010f081303141b1204080304060807120911150408030f09010c060509060618040c0e0903090a0b070308010f0305030904020d0b030613060c211808 72
    0x40940000f402c1c0c1c40d0305081070a10300038096101500b841c1a861103810b0311800b03070000d20091f000c02003030a0402e1200301414481c0344030b5518241c07441070307041d81c42d0788125403084110701c40c4981d54043d02501150011034100300c001c5804a9080340003950038503141c03c40644200c400200f0362014082506e058020b113205502c988000f480c442c0181c5241c010201040c40380b02d210420324540c05072130400050100c0380000064904c4443c11800301c9981e012180012a503500c2c00c0480145100d0403c41031100b0f090011421a106a2043c0d80b851200d2080500d00c1410440540d405030454502120a1040039000b0030010351000c522400c480c680350110010403600311095004035017486c0c000c503c2504240d03000c1c000b50b00424183c88600c141074295101c5503143d10510170710512959002450340c00c3e030341c2641c010f13801c181c0005080d2501d501c0d041d2180c408581c1d00860460381c00c4c1c0f410140444460140c0035094103800980d62000c500e20340e410400b8000e000b010340000102d2001065100056000e80 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 359682374 1250 359681124 359681159
    0x114060a2006010303020d020c0a0504051b13090f02030f06090718060504080c0604080303130c050d1a060306070e060309120a0c0c080102120705090d170a0801090b0109031b 76
    0x80c04591300d1400d00900702414510b543d030464004031150106035641c102180c0070b5460884e800a41520768082c050003200d0122003041c4849000702d240785542032101801811a41d01d80360078000c0c00c2110200401701d220440d44000c0c90f9030030a02054550401c02001940181207007480c6806e40c030380c8642d05c89800300d25032200000450002e800d012401301072214000000040d50300c0c5041505045003951680801072641e94031240700c840040a0001c07904054000b058081d20750f410101c000c0c1060340c4016800312841e0840701020700400c460f030a000440c1c80c850b0003e41e0f5146500314507102003204592003e0304501d0070b442100000020441203e0090072441085c0d191020000b60924241010b0203c070f41c000301159205115841c1c072240c6002040b68003071002d00d0312942d1100d042000a4491f4040360026040080e80384510399040e5003d8028511880c00383c6503200d00d603a85144035025140c0d4200c0702400190120310030000110490704400101844103840b60360151a80404500b0a8440 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 359683624 1250 359682374 359682437
    0x30a2d0605190e070f030207020a17012d1e020c0a030807020708031b01090b0408040512060613021303140a0201141204080a0504030609061b080114060a 67
    0x48800300114030b060603921000700411411505041d00d02108007204040041801e020301c0b00c14006030b4400d502c20750480c3d40e1150700506158401d41c64880141c40f500c1030340c4413405c0300d40c6070800c5094019041d800305a20b0051105400030040508000356000d40000b11607800180da0001300e842c0c001e2150300143c9014074420008208124850400503c4064007902c182b0554120600a10140f040401211015030800c40e24404032003050140d00d0040c0521400500701e40d50f100d050008200c0003100520450742e0403611440e280c001e03901b00545410050310900c2d40000081c090302c1c2001840e0f0058100012412008000d559980c3c9400c5d031885004805c3e141f4039001841c0807411503030000120a880e80da6010014101062006201c04503400504060052440820440005480b4030102d5010b940e01110910010b84945003200c003820285402007440c42c000c10280600911070503100c1c2c1215003c104100d00a41581d092040d03036803000703014100f00301902c4604440404414207111951088 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 359684874 1250 359683624 359683631
    0xc0d141204050f060f1009150803070501050f0106030c05031906081b030d030605091f090f0e0c0301090803011a09040c0f090905063006070c110312030a2d 68
    0x403d40b080c14030301c00070319081810003c2c0c001e010090380609105416aa0409000602240d40b091241c440310b1040d03004810310721001034a2005c2001c1908198080d810580c2801d105903241e00090702034a20040c00c120000d4004d00010b4a4400180528440801c541800103041070311502d0542c1003d500c4800d4400441140801c1101e90408111000c2442c80d00d1500704082c5081c100080d4200901138080c81c9501e40b420305200c0314030440c00d00c10bc0103241c103500c10000e140c06200500041c20b443d004034280d5004941e1052041d05040c080e2201140d40000c1342440d42e13080c08003a01001c004a0308082400405014102c00790e10b41d0300c2005018103d80c0ca9000351b0501c02a00105020a2908409401820001800540d0300e030301c2001040410760340441f2025040340c03046200b0040d00b844412002c0d11600050001040d000301c02030513441e009842d00d0201d2400103091554030780780040c0080b009201000010704d0720341c842c1d00440990364000d500c00d048081020400c0e0448141041030280b80f030743d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 359686124 1250 359684874 359684893
    0xf04020f190801231503130221120c0f0d030222050901050103020f1e042408130206070c062a080a05130b0703120501060201020c0d14120405 62
    0x34a0480e9028040310b0300d841040c41d0304168011148150b20710311009003486030342c0744148603a40d498a1001c660000c00c1400c0d164030f00020041022000104243d01440b50054101e00b042d80b0f1a4810b1f01c1c02594030b0003080c81b03c0040c09030340010317800190000654051828420171203103041c40b0310200321000b40d90240e25440c1c1c1c0f69091003201e11400c3c07240f9035881c08050030440383e190958039a04445007402d00680390fa1800c0700728500c9104201031000448480d50080c001f41ca080742c0600259500701001e0700784010208180c12840928101c00b8000c41c2d0762400050600540041c80d82d9000e10181206040801c0c40e03071703441615006500300c031002c50b17500074180340c50b642e403900e000a5072000c0c2c040300b980c01d52058403100d0440c421203900d5020800002960608005580b21460052821410455840c6d6060038000e2204107a034030b68202103400c00c000080c003103105009030f40b00030f9400400307485194160f20b01a20002c3d40301500c00384414050121690070300400b41098030690156003d0700c0c0868 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 359687374 1250 359686124 359686147
    0x30f030106090e090109022b02040f1b020d0e060904061509080f07050a0e060604170c011701180507020f0d170709060503150a0b03090d141e090f04020f 67
    0x580007407001059a141025040269070b030264150b49204940c1440f03608882c1345004001c0446d202c14000c0d410ae0300349800c486000c0340d81c0c4e1040f0250740101120200d80d0403005c1d001c13601c5e018107005a0000811001664045240c01402003600c1d00e001800014010b55594105e1500107021003540c000c5000100c040205000500601092034424000740c4912400d1800017010142c260185881d900750740300000e80f01c1d0b100e40c0215009000321001c0350714030741d081550690355003060000241c0051401c1c0f10500b400742c0d601e242c65050703904440381d072001e010010050100802005008004503c20440d000a601e8820b1041d6010426180c0e94260070480d00e00b40c18150791005050101000032128041040b80d07400f105403600404110342240c0200203603000518075402c80d0b006050700e2400042445050180001e4012102c00181c40302c80300c0030441008001c9901401500700c3d03031106240b01440003a000d00d00100f0707115200504a6860000031400f00303040360019030f094000c240000541c1803429 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 359688624 1250 359687374 359687399
    0x6050601080703060602030406080919080310050d030e01031a21070e0106080c1305060d0204090c0305040b0610031104030305030712061212170a0b0a060e030c0d0302030f03010609 79
    0xb582418180316072450320340001c2d07491156101d804104010a404076000140500c01340220007280e00d40510040c00034184548958070960ba04c04020300c5880c000611810b0a0604035541178168543c80e040415200054001d000c0600c50082542c4a6100145050390f840c281e0381e03401c203d03100c3c0600c6415103c85802d8508038481c1c00100103d98241c0040249035400b01100341d01c844800c8009498030400c0030070b00b0b14075400b80c0000e5800140070628481e510810ba01800465080a00510404907502815000c80701b045d240a004013030480c1c0025241e0070704207096021000c2070f00d80001c2d034a4449152080302d0b0030540080700040c20002c20301c0f03030b000d5214001e800c0d81201340b00100802442c1140f81e0301544a1207600918072600d01090300350884c0a90300600414528015407403d91070621f1100000b4a0000001c030b1103004040400310b80326124010440c00080013600030b1014a85100400443ca911030000314111311080284540c1c030007215002e54002c0c00f56454140c4031606120b03041000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 359689874 1250 359688624 359688631
    0x3020c100513030233190507050c040b24031608191a04091101180b03181906060603050705072f0d03080405060a060506040e0a09020a030605060108 65
    0x8000c4203000703024038107000e4100302040344d40c111803030300c3c036a2021a00151110380f0812443c01c00d40f0f00d4000140031441c04c07002044100f4030030f01d00c200f00420024040c0c840e030045101c09821a880104c0c002d80c02d040ca42d108200c4c18038000c04042c1100104c403800c11542d5548994503408034008000d00650100d4079101c003001001031304001c00503203020780250043c4034141046403021600c908441c100001780140000b1015070141003405000120704016134070700709110740036000807070040340c0c18501c403d4002c9002c1602c003502440351860300d600d10022001207119510351400c0c01020400482d294041d0003003c1414480d000100d41c041c5031030409001c481d002007070f420910a003009081c0015884a02c05048400b0040340c0700102d501e03002d00c10003e41084c2c000982c0054800111905060300400814892441001203500954501c44000181c0e00c49201340c0f0781201090109003c203603803088030103034040142180040c0c004520b40000d24100016882070303400603924001d10007103503408912540d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 359691124 1250 359689874 359689877
    0x3061a03060108150408130308120106080903090f030c0306011d0a1a041802150409050108120a0c06020d09140f01050603060a09140d0905280303030506010c05070303020c10 76
    0x16580341c003c0c25501c4245002020865600c4540050100400030b030a070307000e451005103c580d0464482c545031520794030081c41104088503400002070f0b00c42c440c201c214890801d0301e025604001e0320702d080c4942200b024003200e81c50b0048420303d0300329460401080d07001705104000b480e088403d519080443d80c40203054904217906005a50030900003480801003103040549000611140304465240c2c0b9030000d400007540400415840c1020240d42c20151040d07038401c031800c00c0680d9941c110640c2d100c1c02545001500303c0705100f20100ea901074502000320b83c0c002c440240c900b002c0c8400d0001250484c810032500b03c030703d55112000c2c1c080108030451441400d0b000170482d6040c501c0000e0355915004203000701503030b21003c5040402281d880c4103003401c40c9031800c40e04480070250f00076158880c0c0e40242030107014500c400b0488403c01400c003150040010010014490658400301d0141500401e018140404180003000148041142e080214002da000e003800907244010810340006203000e000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 359692374 1250 359691124 359691133
    0x507050f060417070809150715020315030c09070305090f010f091e0b04021005070605250906080a0203150d0b01090501120203060105060702040b03031908130b0f07140403061a03 78
    0x240000c3d0710504492001c070040701c0b40110941804401e007c54414100c2c02454082000142c144809864000e90f001d204034030b5518040b00104800d1650350b521414905038001c1c4804085510b45000368841d82c0c2100c02c0d1400d4511000c0c5080344035023903c5ca0540285c40440d900c0c0b134003005001101c5480c820214819013011100b9819450306000713a038010707001901c607001c0000d0b0420281e0190341161569584401c4c18440c078a41007621007600450b990611001002c070407101d4159503c15041002603d1403616644051b8448e051464000c2d000102281c80190100ca9000965a03c010426041c9841030b030381e9800660618408a007a164107074030101030903601209120050303030041001c505442084d10015112003980c00010007801c0c4003040580c041c08002500007000641e0800b42014550715207034000503032504601c1205070070b007909000e00310352107810205149142d44195590805441e00c1c02c0608042e81c098125041d51081e402166126540c00c298002900310344000e5003507502c00c80260 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 359693624 1250 359692374 359692387
    0x308090415050904151b0306050301050f040209070503070e090f07030605091302060c0102121003030914010807030504030e030102031006110d0c020105160602041d180d0e010507050f060417 83
    0x100f0b29000504001d18000c0c8054904401c002c06a10500c041c0c46800301d484410b111342e140140c0140814040c481c0a5420000080d168207415880e050041d80c0c050501c3d03549070340b034030301c12201500045d00d800104180b48250100d26aa9260341502403082110380f01e409040041010b01100e103d5400b0f54002d01070b0342c0030411030b80b403804024501c081e01558a40d686800902c000c0f40248a003509100108540c0d20a010b4000704244000081da03209031503a110b429150032040000d4401c0126050004916030b0012f401d503482600000d80062080c1085400e00e01200e00203420380e0811503d540c090721a114007004100e038030000c41c082178000e50001d0103902d828401c00802c540d540c10006411b022000078a00d10380c002c998252001d50341c010307404644864503000a0145045a00445171000200c072021806040003100e00704c405d2040720008001080441106859801c101c505290500c801030100b400812002e01580c803004070307a9030140003145420303e0f000e110400d5065082084a1050103803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 359694874 1250 359693624 359693629
    0x903060604200a0504050d23010207080f0d0e06071d0105090306150307030606080a020f040b030d0f0c0b090a052b0c0f050a03021b060c0c0d060b0307030809041505 72
    0x42d400c1402e54075005a92030400300c4080d51103110b150f0003e83c2100f81c0c000f11509000e030140f603485031100c11a64821034501e200d91400d00382d00681002800c4020100005c00c6980404401003950702050180070038400c0000c5201760500408442000100303140514941480840c41078260a4a0090803d241003a5070b0708007296a0b10760007081c8040031507660500c034905a504100342c4c4019130344030200b400030681760724520b511000c1d2180100d00450444c480032803a4a01405101503c5002034001d000b6080c9644d011185041401c05080c148140c801c0c2c0345021606070740600d0b10410000c401080c1e00e41d1075242a80c0b030414060b030000802501820b2041013002000045204490f07203103030141c04001c80d42440070440c80f020b81c0082951181201440070140c0126440c4448210060400c0d80842201d0600803644070b0401400040c0e0001c3c00460480c2ca00000300e04040b0b8003458000031348420010100c0c0c45d0020680050303034800310129544c000ea1406010f01400f80f1640d1401a070300510f440007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 359696124 1250 359694874 359694911
    0x102030f090409020f090403020a0614070210112515092a0b030106020c19080304030201031802040c120f18020d021f03020a110d080103030819020706020903060604 72
    0x1140b20710740710407a01c4195540c0d141141c0e030b0808010a10305036802d0524019681c2c0b829030700d00b142d60600340103100c48042003d1004501c5002d454019000400c44540c40303c2c024407001001c07030b41c12001806400c0d62264690701c6800c0880450401d070700b4011080c2045c1c18000c00d007066050001d8100400c1c0c0001034520f0031b030340e00d5628071078148290307484100c00ba000d41140700b0741202e081c01c1000300c0000307505680040c2114240c00150380180c1d41803e1065944040c40b142e00860315070b40c1c0100400c0006502c25409540000c0b260110f0101025495002030309031652072002c08001521513400d405601441c0c451a52102002c0760200441034007000c00c103010540d0ba40d008ac0c4504850002c500564980e100001000b5070741c103061480da140c00100c00390081d04280c11602c00504010184505100b001600d141209220780322040c06a207991b0301200c00050003801980d001c462070b10002c100324018005089018800c00025881c0d030301c008285440c00030001e20151059080480280582040d0355 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 359697374 1250 359696124 359696137
    0xb0a030c021203040f2904060204030317010608150a0b04031b090e2a0d0620040b090f030709051e1509010b2203290c04050123130f050102030f 63
    0x110f46c81a95114917036812080e02c503400d0986071400c0f11081100708200c0e61f00500580e0302c40d450b01c1008a282c004010b100010902400c0042503211f008540c004034440c0c00012000380c000c0c040c1c0c000da9200c00b0707002c0d42600650b03c01c40b50481c50b84031000e400b10f00c00c19905c1c0601490300d02000061010100c150f66410f81010189a00c07020314034020a2082a030954881000094003106c00d90905103000c4004041106480248568207002600c1807905c600480c0d00711000b100b011424000c00b14100503c401004d81855070505c030349500020410751038021300d8410b40c0034240b06800b081d0550030191410300000c0041803900c10320610301c00c9070760b205601c203819100b01ca00226150f02c403101c4401000c40681e080c0c00d2030101076000020030000c0c802441a10b10748030346844920b039510450f10f01880300d010703121b49600c2c120510050016500c920324030101100d011954035140318141c03407908199072211a035540142010780e42400040300a84805004080a00c011231810792211095840c0e8090351 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 359698624 1250 359697374 359697383
    0x3062115250e010e0904050a0c050d0b04060b061603050405031605010203031306061205060105041103090d0c0c2301090e01060e06070c05180a0606170106180b0a030c021203040f 78
    0x42c040ca181c80c1c1d11980b41c00244070f070080c005480900b460f00b8110703500e030300c001c40407185090b020801140750305000d800c842500d43d024100103096102d80d500c0601604400c4062508602c2c18883d000003011892480501d05029441d22a0344a061000303050a202c1203003120900700903140c1c0104010b99001007100c2e4044e4510f4686240100c640c5064009019241e12a4482d0010202450b041c408042240ca04a8500712810014403407110b0104040d40000c0310700100a4100305d0031905454025a0000345240c400c1c004031084984542c007130a8100302505814548002c108034080180d40c1281054000d80031030141c0ea89150b241c581c000308054004501c8500805003c41d000080004c0041c1e2a005890300070a4404c960740f010300442980b0800b2100016128181040000c6580c0128020100940b000d00260000c0e820b068069038140007a1300140c0e030548511100203511090722025002404950350040b54101845000070b117031a0241c0020700c04194100144800981e20b00c6507000f41d41c0e0b21 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 359699874 1250 359698624 359698637
    0xb130f2303070b0f0a09140c010306050406030803041e12030501030302060f09060a0209030a0605070c0c12020108220611030702100621080d0f0b1e010c06020306211525 74
    0x9400103040070700303c0c0184c01014040c0d0001140c17000707c8003150f4100514030a80c0d0400c1010f945008200542c0c000344809404501c00f0004140440c5001400280001c88420b0103c01580e580d50317403207841e800301440b101c00259240018001c140c2d0512849401c11030040e9622400d040248071291100d00151802072180c2d400104000b031034800348160910250442e208016a180020004d1305100440c0e2003203412100504021640f000f424a41c0100590107a59407950340c0e030381800900001c0300700d80c040d2413030b054050f8100340020407900070000b0083c1c04806a50b00e13030809407400303443c0110150000300481d0508800f031181144140c84a560082d0018610201019a05004100c0e10a000e03010400c60300b000480b050f8918150420400204e041d0340c0c8405000f1034226200a0341c12040400f0300041444c0714480c04618039070040d58124800414540c1c460342010174014100300c0103550600c958004142c083c4c401116011010380c8004c00200195107035168030740d075042e064820320304441072005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 359701124 1250 359699874 359699881
    0x60d032c030a11030601051906080a0209030105090c100504050114161a040c050627030f0d170a050105100503091006030317010803090d0b130f2303070b0f 68
    0x80480254200c80c00380076952802e0007820010300c034040d40740c1d005010703100b05000012181021400c0a07140d00c80008146c44850505c90205c0364200094541d80e5801e8090045000d6607a003071103024020070141000301100318411050000009a290682040c08001e02c0100700c3e81c1d801c2000340070442c900c030701c506955042c02d000020290201d07060180544106564849503280389410640c0164020000c59820366540c008006641c441c00c103001400c3d01c52484541300c035480d862800a02c110b801015a400c0c1901c0800403850f0004410300325000482c4440420b2102c0e00200505410402d5100140081c1d0b040c0030100320500300c640d0070002008000000112103200c107114403040c0c4200c00c00248200c43c0e990030001c255081c10310b140380310483d400000265031800042194540c280c0074042d020700d6051501d07040e6400e000106006405145a4201f2001a074001040e01219105004a441c0440701071400c1141c5610101100c495520804c40074000c58140ea0340541c0c0602c941811b58400d94 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 359702374 1250 359701124 359701187
    0x10b010908070b1c09051e030a0912020d081c061a030613060e01030b0103050d030e0c1005040503011d0f010c0210050703200d0b0307050a03060207031710030308060d03 74
    0x10006994184c1045c605480701c030030010701082000c01110500600b244e50500e02140c140c9074883c039981070f40460600c8030200807044c659044a452540010070110b54281c070782e280d045403540041541564000302d0500300380080045c0c860f400261982e00c4840c1101c88050040c2c441610010b40194490038040c0c220410810291300080003802c0008000559541d41c0d1904901c03501c000c3c0000c8507075001d00c2100e62280d500c248552040c0342c21460081c182c01624105000140310300380041c900f000720030400840c13641c800b4051084588011002e244c12082048281da090803918800c02c0143d0b41002610446594000399070264100d91910003d4140c40c0d81600754020041000d0a420f540752800e420721035400140050b041040f91000144600c1c06a031040607190304a50081952041c0d03951414000300e461603003e010040c0c804d042c282e02e1b0300c2c54140c0d05034150100726020026541c1405086c401c0591140455400590640b401403483c11250f40140c440801580c9980368205103040b5160141c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 359703624 1250 359702374 359702407
    0x2090a0216080a0203040306050903090f010e01050706110903010c08040305030a0203060d060c0804020f0d260f03240d03120b01030f020c060105120a03050d0b030309040204060809010b010908070b 86
    0x100d5006000c25940d03ca60034002c0d480345c00610080c0c40350380c906800610600804012200d00f020020f10700011020000c00544a01007442040c0741003060a000c04800a142c500c030702d0390400c95404016444d415042c080500303581002d1088400c100501040c480000c0e080000d59406c0182000c000d0f0300ea50b16038000c10308400d507500c0042c107014101880c2a0079030340c010030341e58061802941e03d00101c0150300144561040d01510040c540343e52480c030070000311100308203c808040f112000130701d0300c1c104100c0307601550420b540320800c00000d5411040d181016004400c02c0c20b0065410701c10000068a024118a10ba82c220445043c0c60300403d00d8580c1c483e40c00310103888807101085460702c840d03005081d074600090040c280074071400d40d046121144001981020302c1d52654a80d890180520224030240014044040d010320040c8000c0b007241ea01c90001d000504640e68821505280c19140b031800c0d00c3c5400012030601c40189014094036201041103070942e01007000050361006006041640e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 359704874 1250 359703624 359703667
    0x120f050906041220010e0d020406050d08030708072109050a05011a030105062b03030b0901090c0f0815011b0f110901090203130201080903090d0803010f1202090a02 72
    0x416000180071800d01c642200e910061809105101c2800d03036100d075051103003041d50504ca40814820031581d042c92400e000403100d4148068004a0115036034404941403082030001191a503002004000d0841d610034182948800d0503e40848025000c42d1001e43e0700030000384504c00b6644980f04501840001c000347c0704000d5010008205d44895454440c41c01101d1420181c800e508003070124900b4500042d10b1032003064904201680c02180c5008409841c01c440011410305489a43c0049507075241b07c01e1038001c081024010505ca42003001c01001d5400c1903150b0411320600d081444840c24200c1c16072502c031002801c04000200d5803501c0c2215075540400010300007420360f0400410801070008070b148450b02940d014210303988030011441607000c1102d00703444034074107a400f003005580700700200f0380c11407008000e5034a071040720340204540c981325070001e42c5c20071000801009541c050803810300c02000000c1e2100f01c0310907590300180c0400c001408403108190042108055400c02c9507487c0381 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 359706124 1250 359704874 359704879
    0x370e0901052709031909150507050a08030405030d05161707180b09030105090601030b04020d02010e032b0c03051911030a08040c050406050d1709040204030b04020f0d120f0509 77
    0x410310706001d078655264800c0039601c0301095000380603418039001d0b82c000c5090311815810080d03a132002e11f41c11101a0001807003030320346115241d51030300450040310003103000724014805182d035840f4401200c0141d403805003008035860940d10b90301022503400400250100384c0d000f113000316901c403542c0c21511400702d05900103008140d00d900040a526203001841541400e80080c482982c0d4a2100d9860b0b120910028100801107030002c1c0040c034010103025003852050424428461515010074035041c21345200b80d1142240f44a503080c1c1543c80d44000d4a021040e291071040c0d034000303643c01405030140b01128030006030241d0501c07400c03901500764081c10b05510001c032606d44118190041031202c0a071010b0700c1c1421f0b11103011529007814020141903442c094195080e1740c440d942c3d15a550055040d480007004003c1c482401240d40c0c81c001000218083c0030380111b2810316004000d20b040c40d4a0001d481280c000905c3d01c00103403940d0007000c4401d29400e20850317140750040305031001d201e80c1c82e1481c0e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 359707374 1250 359706124 359706199
    0x80f04110f190f050306011d190f0203040812061f0c0609050a0b0f060103020708071e0209132d020d1a0403030e010b01090503030f0d02370e090105 65
    0x26021940c505003804644e003c6003200c5940c1d80e651491109043d0f0b1a47c8454070183c6180090000e403500c075480401d48458007000900d41c0080700418080760011355040b0340801c03001441000031948401040d40190044a002090381041c0b20003001e08451980000240300d40c094100782032000d0b5512070b007174031034104058805c40c4410380380801c0015000c4075401440c041510219003594400d100303a031840b0341d020024510700f8502da00c9107080640040b0168111100503641100141ca4040700503024420307041d4500180350745440c1a901940140d074050704c501045001c1ea01100d1a6401c1c101020342d010760311145501d1440c1024124045001e00d0140c041207030b0024001019459480030380c021000030020806980014011282035403140714080d49a03000f4480301104a0ba01e00003881e6202d5061001458120000348241c14118145000d0300f170f007001401601c101c071424821020a00c0c400340f516060030040000022003004040c01058003d44140c561245409103040b40c080c8450507480100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 359708624 1250 359707374 359707379
    0x50312070c1205030d1d010f0c0f020a02090f04050a051b150309060106180801060902130605040b1c1d010c0f02030c03030117030702060a090303080f04110f19 70
    0x1161994000d100880d5031007040c140020300d8907024070003065800d5000c1e000c0c0d031410400c80040c101030030070411400440c51122141400300c110900c0f809860b030303407000c0c40070491350040b0b4806454085040c4502080d5001241044010303515410844d078090001d01a40a69403070750b04099140c0071308003a005290748900054a106100c03400508001d07840200d0701e040b406e814003541041a03010070390b02249143c0c80040103200c0f0380c1c06130b85920143d90b50b100c090300c0d846a1718040075003910352607030180e00b078a84d00150380310303c4c5d155016000014280905000c0e1800d4504441602c092180721003941c43e0480348843d5140d03179030341a00300302d210441c503c22071000c0c4031040c40d1003030003080c0c2a1001008128030b80c440000b101e0001c0300b0b81d60003c5180001c0c2d07045030b20380940714900144154a901a50000304100d00059884001410200880f035560000f07190a524000d040040080c0c0b181e6800b6000108000000d0005c10b5036550301401580e1090f0403021100209000b0a20b441c0041018030119102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 359709874 1250 359708624 359708653
    0x705150105090604061212110706080a050f011a0d020702060403080a0f2a050709140906090309062b020c0c18070807051c050f01051008010503100f060503 68
    0x100e05940c011100361030349840351810842241d00740e00c6461075007085000351401180312600fa403d100400703814038000c6005500c0002e400c042d0a9006100820100300911a28103a070b4480d1981c40015100107600650402111102080480c0406141c404000030458000c41454060315242a40a00001d84444d124500301c9800c1e0030126012000408a003000030010f481804500704c1c0882c6040c0050ba0804d0403107513450b4034050380600b81c03100d105180c4c00003030fa00c00c20301c580c3d603820110030050307604c50a00c400c025040460180c0b0608107584240420801c070346d00c40085039941c1c8040355a0802210710303c0c1a900b900344801030661504ea101051040c407a83c4042441941420120b42d0402e41c0032180e0b248600045c401c0d01d040000500c80400255110b000f5401030a602c15000d01120b54220b03062403c0302560411500b52002008940040080cae04002d410035025082a0610307044540c109000b00307030f40f00102d20a44421a4907003e88030008440c40d802140900743c0601035074829111b071a078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 359711124 1250 359709874 359709913
    0x30201140c0c061b1c02090306040f020a06090501020d0305061f02010f14040804030303020714010606030c090501050a0f050306010905040e0703110907020712021305040f050106090b03060604110705 87
    0x14078540b5000d184005a6502c040e0350340d121600c40151000c81c00c1802c21003121003256a41e01c5503007103055082020b40641c3e0340c100320240c803a5109618072598200c4910500c084c03041c07103901c903900b401013110050042c3e030303004288200301c008145000191551038000161201d40e00908407005d2080c0780c4104040300d58190442030750b50518800c1408006918a101e05011104690141607800c0c180020310001e07100f5001484020700402c1c5035558888020007007030071144940d1100c804640d5801c0b00941c85900034a6000050100b401d00034240400349038040c244014a00f0b000701045400000070340c80e68020729107103016203405007081028a0b464a0995900c20b5140020307143c100c0710207003010f102d18181c0b1b0450300c10f14a680c0941051407a04107102801248a030089a0140e0300c0114006010f00c2842540d20440c00390000881003d5141091421980786400842e110750030841400c4140c1c40c00280d064204d28141c03400501200c0030000e1124600844000401c41d0181000c6032005500c400c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 359712230 1106 359711124 359711137
    0xa0308091f0e030418090b1b0313080d0609021c02040312030906180b1e0108120c150c0a02010b1c141c0216090506010206040f030201140c 61
    0x454080004001205c900354080d540c052880600c29100300321078102084d007590304c250303100ea6203940c0240c2c48024014401e0b250b40d050b07510b0410000c40c0403110400c10550040200e140c850b0328140103544918201c0c81c20307d03107940d1414031500c521701c06c49040320fa10400c040c4042020950540c05000d4860080c0e820507950541c049422402c44000d5045905c40c40d0350f1261840e204406024003845200700c020b50040c5d20006104101300011b80384145120b40021039168036000721414074040141e0000c6402110400910201a017010003900308105035400900540d00b130182400203254030303a039090301e442c0002135240c0c01141c4507000801008032200140c40792440905078010170003198034484401a4040216608002d880025690240c5a032800030b002034102040002e641e14400342c00030f8101e06080c0210307030405000354054403104125600d044264900303d0b600e80703410381120313 = true := by decide +kernel

theorem cover : BRFrame.Cov 359532374 359712230 := by
  have h0 := BRFrame.cov_init 359532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 359532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 359532374 ≤ n) (h2 : n < 359712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
