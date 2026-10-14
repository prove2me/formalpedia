-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1582
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:41:22.25671+00:00
-- url     : https://prove2.me/submissions/d689fd29-9c1d-4634-8e35-c82786894894

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 284352517 ≤ n < 284532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 284353767 1250 284352517 284352533
    0x10020c0705061e070308040c0611060406020915040b0d0b060715150e0f0f0702010b01080a050402030c0a0801050f010504020c0c01120209100203070b07020f1908191808010b060403 79
    0x8456451100d012480c800010080401094010f10907031b50700c6400e1510342400c19480d2520f0f04010200300180c0c1081d40034801c0003c1702e941040d0810340040c0d48108440000f48007a080e42001000f0780c0b0007040003d00b8919020280400d01d40082d414000940303480c0030801148503081d4000c01e1601c0b13008110300070102c2a4086403901084c24a0380401d00c1d225142070418501c1100e602135042808000c00401c00c070100a800d412074a140000d00c907540d0200d0010b0300d45240100711100b4160b4400001d01555010010075051307540c0500300d5850701e0b071142d80b258064070040f50840a500324a0300000340a00382442200c002c1814500500059001c070f40c0111401034490b50286c0c0c01c15020f01c22503980327030740b80d442c07041361941c164000b150340345801d207031550f0000c0c0d006050000b035400c007015903010700300085103d480305031003804803519417045d51900400c213009455042016006044003201c4c455041414603004410b100c14000c0c41c03030703a0307015651b007601c070b461000c5c0d40c1000d0148004c100040901c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 284355017 1250 284353767 284353777
    0x603020309010f09060905010c0f0905220914010507080c1c200a0e0a0f05090919030314060409031d0102031c090b01090905060705071b03120210020c070506 69
    0x100700082510921442d000c0c080e501d42e141d0130b42e41c0d582c2e01c440003010004248220040d071186428000810036903a00d010b0b101f12042c4c8034090003440030342c00180040304191115010f504000c0c004200754420381c00d00354000c2e4107a0000840b558608070200f01014081c0406a1241238000c60840c500711005100c0c15000c140c5151503045551504070f9280a143c0300342030110825008203140313854400c40c0d400200540e5031031840c580102501d000c18084100f03240003420680700180c3e101001501c1d440b00c200d107402e091415200b4000d4106c140c8400301039040e001580c011403010700b00340300c5c3d855544c104011602c040740c00030082014811600a440005402c0c00083c400500507a41452940003042c0a80703480c00d01d502001c660350350340342810003190040b0b85001d8034072064100241c030700036030341d0036910580900880c0034424042a280c0c1040744e9131050b8942207030900388013012150303a031600c4240c40c1003620252015024002d031012540281c0d101340c0b18500011002040071602d00310a12420341c1c05 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 284356267 1250 284355017 284355031
    0xf0303130f0b07020607030f06031a04080f04030501150503030c070e0601051b0705040606050a0c020918010f06030213230405150f0a06060509090403030519291005030106030203 78
    0x446000720046108801c050b4031400300d0307401034500381c80c0a020013400c558118a21190b0070b0f24260341440420f5200aa00708e010050b801c1c98441501e031414912880c0c0200d94a004000d040094040100b01041d0081d40318503601469989805480b28201034490003040d601c04203030b501c0348108000d400003600c16107810090606101d0307d045441070390b82860813242c483c0e442383c41d40507817000c100500305842007074010704d486d10340f081c00c15490543c010315807900307014064420181d150100700700b810440250717040c18018400030880c44801c043c40034040d0940c0d00c0b0603441000c2e007041e1101d00c00868001c003000390b920072142506180e6407030003860300940c02400c00e230b840d4070900c40610008a1000e0019010341e8081d0030300303c03552a08003098001d03103049400000421800b40070320003d503100c84202c0341d001a414100402c45580707903600e15241421600c1c10f05600390914030300c00064402103940a900701d0714502140c81d16200300d81840358115184c0e4052000500800c01009440d100c0ea01035604010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 284357517 1250 284356267 284356283
    0x6060e2101020f03061f08010608060a0504060315060b043501060f03050c01020d05040b0c0f07060906030501120201020604030f1106010e011e0b16170d0204080d020f030313 76
    0x1012030640c00ca80060b01d00c07806400d000014072256207000036078809088802c3c00d0003840c49414000003040483c0c184581d00c10b100841d80465660794440c0c01d4003020300f201070010054255039050660a0b401040b441d480080d24110002c80c079140c00c03c0868041e121042c00015004001d11114a1510142c184c8110010f414940e903940e4030700c080c0070384002007442e40c028041590841c240b480c07c2c582032417121410756205541250302c2903000800c0d1421101c80d01d815030385544040c0b1145007880c20501e26003080340036100000c0f500903003054828081c0c40d01030b034081280740c0c0c8669440c1c0c4003401c007500c0640541c0c040400030780007a01c140c140c0c03446010507250481c4840b100c4042a07251a80a81185584403011401805440680c0103050965020700180d1010285814401c0d40e05201e88009803c03a00300c0c0510110500c0110003510708001080700705075a0700c0201a01c0c01000b03401c03d00404050b8014088840109480050805074014001000e145541c40f11600601064041c88040780c03600d0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 284358767 1250 284357517 284357569
    0x7031508070b070215071412030708060d1e0501021806130b09010c05011109040b0d0b040816151a0d050c0609120d0305040201260a021305060a0302071506060e 70
    0xc0040508a0540701f43c00030344018090032129410460020050404800c0a00401045592160b1320343c0c2c2102c401c2d10400b040300c03040d040c2010310b1940b100d8040d240e05200c166801c10004154010031a14075100c4840342401680c03000c01989208004142010b0240c5d150140040b5200c02c1c002d055507072050402d085462107a580b05825981515542e20502d6004100034032a03040c64040c3c2c0c004274001b03e40c181c0207440217a40c2c01044d09000380004d41f040c080802c0356003911103681d0b0b10200d01500455400301e000e4010654101074070702141e192004540707800c00b03020300f0f0901e1216004155404000391000c0328210090220720307040241042da201c0b803900e80380c505050051000110342002d9a802081602c1c01e8000501700c07180f044d03000e1001c105151050008a04d8015507650000022000565030768032444000107605204e401185e4440c60000d50302440a41650007064440e1054074442080c046070402c0104076100d5204040220f0317840c00b5102040c1c94420f161035810540c44200d02043c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 284360017 1250 284358767 284358799
    0xd0c0203070c0905040303140c030f0405010f140613050108030d05070e060c0a0201300905010902090106091715222f0f1008041106030403030507031508070b0702 71
    0x10142c55400701c0300d441e5a5800344801e040e8540125a141d881080d1101010705003d80d035101c040c440248030701200402103020800304107003074102e0440b00144802c01d10482c1c0712880d040080071010360300d95100d2582007580324110415070090034100d031240030245040001070f0340e109001d050014840d0003040b80b04000030005548403c040c01c0788019800041c1044809440050301c0303410500000c0c0342d0208088013602c2c80d540c58100410f00001c0800012412000518285002d8404083d000f54004241b03030000c106144d0000030342003112618840044046400220251620040f2104603000400d00b00002c84100324407500540710b50803615078001c0410b09442d13501841c038241d00c080f600003142200d11130400a140e04d4880341040c00322140502c001048001510103402902e400f01800b0b88900058284960444482110580940200d58901e000d181c0100205802c4445070302082c600031003881c1e8465040043c5081e41c0364030000301804ca0070460b40d0413040d04040412688421203d03003643c0d00c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 284361267 1250 284360017 284360033
    0x50705030a0b0604230106030f110c0c011205010501090501050325030c0f050405030a020904170a08061002010b0a061107170a110105181009080f060106030e070b0d0c020307 76
    0x26a000304007191950034503034100720641703814812002c088496079224004a808480d64541142c0035400c0008402c07a1008074040540341c01d4411038110b41001c505925118004102c040041d0426030310314556038250180300c011148203019860005202100601c8594020001190041c4d031384181381019824991006542c02d02400207000001d803035882d181100c64025448050400040c01d1250615040501095072405001c1303029218102107004642800407802803000f1100310022010780c1d44c00d13464005882100180c1d40d003070048090350702c4a40720714418860740b0400200186203000301c9103001803ca491449020322908940a50003000925800c2160bc246446a8080240643c01d120f800d240c101d44100d0381c0d04a040c850100601c4104800842840c2e00c00070f0101c0305002101c00040040381c00c41038075003003a00c01c1d201d03500d40c041c031301800001c0aa04940c1c550343e043c44026141d401c100d40f034910314440c940101c42c041c45614000c041d1500240d240c4c015501c1102d061030340c01d403140c42c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 284362517 1250 284361267 284361283
    0x204051b0a0e0f030a2f1008010303081b03070f0e0409030e030106150813030207050d1110140a05220303090806010b04030305070b0603010f060803271c05070503 71
    0x3002c1640c0800e14803850030100031010070940b048026185c040c1003074482880d01e5080e400900f4440c00000444c8410344600042036075890406800e00140b00706042000c0c010880a00098020400301d0002030800fa94070606401c040c20740140d11410341d20703402e40507100d0450568406041c458503c402c00325a807290720914010600903510780d6502c41d40c04084c14210f81090300014040c1c0c1c030300360280c1105900210555000344001c5d600700d0421840c0d0a08a04100c040c4e08040d5024004445520920424480c001d21f0b08108a0b48a00300c0040f03c8000d9801c0c00781c2d00c003880e60b460340500c0b2050303a42e80210b003d885015003001400003000307482d1f01c901000541d01e41040740803942c00e0303101f400040f000700817142c05440c500c418945031506686000e0054020361000030001800c030381c0000d455413801c3d0051084418070240902030203841da0909501d0790407980c05c11a415a524039000d070701440d8036560300c41180000d4001d003075080b645030008464921141040e5240d00c951480045d0945081004807 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 284363767 1250 284362517 284362537
    0x3010203150f0d0f12090b2703010b09070e060c01180b1810050406020c0a03022a13020307090305030705010b1c0201020718180807020102070b0310030204051b 70
    0xa001000141c20016001e400707440a9010f8040d86040703000040311508128502c1303802031400c030f20a500d05a81190584c01030b82144d0801e04001c41c030b2510307880720301000c035504c01a04080b82507014800300500d82200e24420040794895170f16000f0881950080e403221794110401340c0294904120988054291110f0110003440074030f03a1095101884203070700074603401904044088080d5001190183d0303842e80e40d0749020020ba0764420204080000b9030f411290041e0a20090b202c0c058107508001e515021401050100c1e0700102500c000311110174219801c2d40080242004d402d4a4190b4031070000303410040000092110303001c0e011001c00d00820107072079081d1150b0004160100c5003c148508a208092031402d12100840c0810041c0e030003141c0042503403180244401d401000341898030207040c001c040001128242e07801c1c41c00b8090403500401095000b81c0880b100595150b0400d40c00f07100c1160b00c01e0020341065070500c01490036800554000500504004a2a0442500352607580c0f04038050 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 284365017 1250 284363767 284363791
    0x7080928030809150105090a0912020705090c0c1b0f0a09021c181b150215010608010807030f060b04050a090c090507051209030f0309030c0c03030415050d06030203010203 75
    0x4402050ba10958069006000d00003424221030030021070000c0340418010540b00d0700d605000542668001e500194001d604860b5094941c90b2800010f515005103002c0d0a0180398072a0025000440e81d02c00c40300942e650704010300b9080c41540a0030103880e81011f92a5100404017001d2101c2e41e46d0341300c0400a08201440144c0c2d4a804200351250115000380f002002400e01042908910220240c803a56130382040703241a04001d6003000e81c0c20a03009410824012000907504848036500107001d240c207150031454420a40d0701c4220039950b6600c24803884005910020050000401c40c00f00312900034440d10000c03800c000c020700040d0036140c3c00c64411200550f5035022800380400ca00d100c0000b0140c02d1810060f42c10100b600a110340f1540d550104940c65400200d0f0807541d080003104c2c0e40303601100055460341051500c198807a4001c0c0000d00840c4543d0703040c05541e1501000319030032507800d2005e190500d2030034501a207160300310845c5280010340d11a00040542c0b0300780021803042e1100381103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 284366267 1250 284365017 284365093
    0xa0e161208070b0708190504082209050c070201090e04020d0f060e010f020c21030c09131109030d02030a050a0e03030c010e100f060b030105062503020105040c0617070809 75
    0x500201499980314200701141004182300c0071801c0030040303c12182c40322030000d0f84000046101548a802580b102c05007920b40b204201c4d1580c1140054252980300341da5040307845540c2c1072800c80c0100d040d90040c5d40150b01680c3c0500090f10345103688882480748501280380c7c60400a00c508484141c648007100a400107007002040100748080a805044071036607807210400b136038605010b80002400034a41c0000021320030815901c52028201c2182412000e0200103140030300b40010f07800c00c8458034000d11580d1241c00c2d901b400031080d1140c048190b0798031800d10f603130741404881d9052207101003a01400108050080c110082c0181c0f101c20600d00010051061414070750400c8442880c84038107002c0c41d101c000c0c003101d1309031000c99046843c1111115150302d0400d0800701080110b50751480c00070030300d81c4410304141d01034026a104070b01075151000c0499036501c003914907907100700149a01e1000400010016130191b08241d42003080130040360011a034280d041c40b0782c40080e18a01d98010f2024403 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 284367517 1250 284366267 284366281
    0x801050405100e010218060901020a0b0408040311010c030c060b0a0e070207150e0d0b040201031e050703140603102007030908010f060515030a02070f03080a0e161208070b0708 77
    0x90f081094507020700840c6818034020b980e070000040226194801c460000790910300368401c101c0c403130203a1781200b6240368078101450001c03c503501c9484226220f03010482c0000440d070281201d40d10300d94041c6c454502e2507034981c0d1848001c15480f101c00d58810050030700801c1300045100d4962203900355070018490b80c1e051040c14022001c0c11884142001a031a00f40901600d4640e162a40990300c0712080280d511148010f070050300241e0b220502c03216000d80c00403c02c3c201e6030011805120703a03423020000c407440104040404102285e40540540c4090b00f4589a034030386500c40c01100559408035170b1041d41098540f85203501000007900000c002c4001801801002c0c1b05e00780941030040f4082050600c1e2030041404a5443d0700d2000061801000141c0c0041058045900031544140c88400800d91880d024040140c2664031940c0d03039250059070541041c00082001c1d41d12014580102402e14080b02c4aa0014680c00308442125080c040c90001a00c2610a40c1c0110681c0d19042807611340303c2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 284368767 1250 284367517 284367521
    0x61908030c06100501020c120f121b060403080103020d030c050609070f140307170109051c170603060c0a0e0a03060e06070f1e030207020901030501051e04022107080105040510 77
    0x2070514203d01400050401c802d07a00001c202054000c1a1840d00300003c0e002c0480782040c045ca241e005003409072141910015074802c0041c80c5002a0611a03504210f401c02d2150341e40ca000ca0300280420425801031016240102444840300c0c4207103040344e00d01d111540c0342410880d06603190025a40240000d2022001c07804121000d04010030101e0324a40c0c8110020340d0b510914070500070600340301f07044a07150080c20b40059150301e802c282114101c4d0600601102c0031016007228500042e0405102c0b040c20560030280d900402004005213060b880300f5172020002c0e804030700d0003018411b2448240943d0b840d802c0348007005600846002810900f240d005509011004100c0b034200828001400007041d001000204240803010710406440f030748240a900900c01c02001039031007010300000000b00070054010920420300000840f0b282c1d00c043d00410b42e01181900c00035480742040030b030205140d9100c04003005400d9040c0450708440d41d0340c2d003102d0846100752003e68864000c10075400c190b810034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 284370017 1250 284368767 284368771
    0x13091a0301050c090103021b03071b0801020306220b0a030606060f0203071a180303040b2505031915120615060c14071a0304050c030a0f0803061908030c06 68
    0x94009114903c2e00743c0c200d181c5481038404042c189a03020031f44c0c0c2e82c8100f45170202e071414115402100ea035851a418041ea42e0801c00d481d21400c00303101107012a907244107000784e0f400740e4000781c0380c0c0c0110800d0099040013289442e9140e030460b59548145074003596502540300086000d24000214141030010082541305056400070556000b044240001101d011450390b0b41c10030301d00d01034000c0d00c80100440011441d00c00301c200d148030200c103020034418201c1083c0c2c02240014800250000c070702c041c0c2410304145105c6040400c6050000030348224081c21628194144a44000b507a04030000c684104c18101b0f8220500d004280c0358000304121044c1305000280314102e445d610064541a0018040124000c0042c0b0240b0510300713a418188003001900042c00310b104d840391311504030461034000c0c2d8000700c2c0c0943e1240b190425003225410b02250311407099400140020642090351a00446d517030000e40602c0d0000c4c5480204038413060080003035400361102c0b002660341c8080110080d441c000d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 284371267 1250 284370017 284370019
    0x90f060e100902030406020d020a0206060a082406120f0703030305061915030e1e060105090403020c1e0409080405040524040e0703050703081c050c030103031413091a 73
    0x90814403101007218050031088a80c9980003503669601da20304580030380120036403503060900100b0a19456500400c42e1881048152004182c0350741d10041c0694440300031443d8000e4954607401d00740c512080b50601d0760700050240407145203070810625180b406c04003444006071500300d08424403c155060040c260071460442d218880c102442101100e00b00207803003158600c65400c2c0e40180503501035005182c00b5041403007614100102c0b13034921010044402600400750168900105c0d180c54407801a5000b00d4042d40101600036004050190107544001180140a04008498290b9580f4022036441510074a94581c8861801e82440b080d50800f51411680c84080b00c100302a440036800191b000c82c01c22a0040340c001480f450b11800e042483e000900b0b1801991800b20030312014000424004074664a03944020951440c2142112810f486059921404000400200703110342060025154000c0049103000c074140161480204c00ba40410805a11345030b0140070282c02c640301e15100ca44c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 284372517 1250 284371267 284371289
    0x3150f0c0c070531020a020c01020f07090506060708030c04060801060c020d06110403080c0c0306060907020a0201121b0801080d020703080f0d090b0a0902040c0f1209030e0604090f06 80
    0x1c0484145803105041d018850007440d40104000c1403103010080d11800b414842d20003280d040481c3c211034040d502c1118080058490040d0511240d44009104010740781001d01030300362142410700314005040040c0002e031340030906008440c04921504000c6000f00c06011196644501c0c0c204c0190040350142d0210341405810101a009611a001100b0081c0e501c0080002e220046210400c1e060140d90006007040d8404104106203c400180e032a07002c050440440b09030740e49040400bc0f0703914080780c04100503009030a480005500030503183c0381d8250700b208041121144d0f000f02c4800c80d03560340085000a09803c0040090712014004640c40039440e10140609c541182c88090103441a80c410819041d40020b484600314590f91081d5040c590220b4030350300c1d5041c6006c89002408050030705034811441c01910f074122a0003180076052020310340e00c411000d0b82c0401c40070303402404043c800380d0a2046004211210740d4408000303101038007200350002600001513030103170202c07991070b0040740401c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 284373767 1250 284372517 284372527
    0xb0105220e01050f090a0b0a0b0a120617070b030c070807060c11010c0203040b0c070e011d1e010e0603010b0901060f09081b220c030b03010c1d0d03020a0203150f0c 72
    0xb1711a080545c0e8032030700e50080865214a5080851108c218030351010031b040b40041075005809a02030401d00c506101007906204040d182d071036403100c402c1c00e0301c5c00007855840400d003001101a50805103500c481d46602183c1040415241c4032180c2d44004400c41d413150b1b507503120f44011604501c2400a5506400080003103a94801e0040d54901c00e60041042d03600c80400c911460010800c01c082c040c1400c015954442d503900e0346102441c80754842c41892542d11400000c401c0c1e41c260720080e110842c1c0b000310800d546d1909101c5079040c1c20103894660595200c6198203403a8035010801c0d4000c2c200da0340c4e1481a0749164000510481c015046020304e50442c03035440c1014000c50180906c01101214460000e0502c5001107a1156030303000c3c600425810047e80781c0e806901940702c01c56142c01500240105a01503800b1548070840b1500004c08038596100415207090024504580c6403003401118088602e0360002440c5c920b904604008080d0150f0030005d00c80501c1c05d4482c0c1014001103d10f041c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 284375017 1250 284373767 284373769
    0x60506030f0f0c0f0d08120132090403031b02100e06040506040b060310151418070e060c0102031f050a06020a12120f14090304030b0402040b0105220e01050f 69
    0x1803c0405032452013400a1034a9501c2c580d500f11000c280180c1c03145616070341e155904801d901c500001d12440110344600d49221801e00d64544000e401098088030b074802284060342000182c11002d8801d404042c3d0300c402000c00321040b40302181d050341081c0c0050140e103d882d07022000340ca2100e15078103c650230030310034040064400075800750040da000783c81c402e80e5500c58011a10380708040c081c0300e20441c1048540403507118411030b0981940c00c0d00c95035150341080720003409810392190300346103600100d05000405484c441e01842d5402e040c018200b40c98410f9924075982603800544080048501580d03180901032460080710000b17004c00e0300c07150030b842e2610401035150340181c40090600400504005000c5200c2c00c04a00c58402d102410000c1c11030b040307814002800880900382182c003d050219481d60000819242200e80c0507402c0704151703850354213007c0501382d4132850034140101440000128018549103401c4800100342007240203141c280300d0000540181e218a003d03245401c140c01c21 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 284376267 1250 284375017 284375023
    0xe03130312031e020a0c0221060a06060e09040507120602030a06120503220f081e01060f1701020d2d06030807020103020714060705040806010f060e1903060207060506030f0f 76
    0x3800100d5200607140c4901c1042620306d20036004000358008260401005080c0c070170200304281da8601001c0344d0b00c941d13400004008445142c02103002290914040c54130a25144100341c0d8000e1040040d202519035950414207100405030f4102c0e082c5401100b00100c60301148100c800516060424035600d036401d0b121203441e8460600e0486042c48032010341d00a9440c0141c45800a08408003809401070355001c1c0d090321034608201503805107212106000000005004030020fa40b050010601443d14107084e462070500304c901c240c0040e54092000210342043c034130400c01c1202102c0511031f0010209042070702c030f00504100d01c1000320f1821405002083d401416034081640c2803e00581d60740303040c10070041055084543c3e1203c0d01c1b5140c10030844551000c003400c00c80d041c2c1400c8030300c0f903600d81c85072140902d007500500002607128000c102842c5031092020251481c2a10200701c0e1545a40312202a64800c1d40309031041d9803503400744005410100300314142c401c40c40e4090310140b0030f031140f03050b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 284377517 1250 284376267 284376311
    0x11030606010915120f02090306371e140601020f12130e1312080f0c090303090901030809010f1e180e04050d080f040b0609090f01050411090115080106050a030e0313031203 75
    0x881604500d012440c07210092f88054503c10080b0100f0680401003210f410280425090b00d01e520070f0034074042082c039400040c600000c101c580c8040c103c005c49800c1d00d00c00c1d54100442940891150103070002e6180340140700e0320f002c2c10a09510b210303d078400e0300741503504060504012040204480420042480d5030608542000c4010705640d42c1d5101c00b0f000900c0c40c018400c1c916882502c0d10000020020f621000b022108400c3e213504810b008119801d685241d2038800340d804039a1490b03540d410309442403407607809005500380010000798480d4401c5001c07201c208c0c3d080380c42d540440d1801c651030350041d5056500030442202c58800d45029070380c4280c43c0c0c0c1c0c0130b40708500444860005c100200f40038015181c521442000810052405041c03000c0348801103c8440d000320149000420481c0036036140700c14010a82e103074548640d1074540704840c2c03a07001d041e081040680d103000700100300700140014880703000640880b034185419811300e20110f040c1206108207140c68091241da07d110307001303c1c2c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 284378767 1250 284377517 284377591
    0x91203040305250506070c020f0604120b04030903050f070f14010f0c0503091503060f010309080f070c03080301030807031202041401030b030c06130311030606010915120f02090306 79
    0x10100300f9040310034a1000c0c44081d0080c458050002084107850b84a4140c02c9514000c80b146d0300141c684405200c5244a02d018580400c0440710641010403a4110416001886450f01147c503a41e41c0e280c1c98100140b01c0503075601a0043c01c402c021189503031040f080900700d01d100010311840c0c12000684107401c005d9010003030205050b040300500c1028030944001080c083d01d0415606d50460031116280d000300c4106100340c030792800e1003810303503c00c0c80742e18081c660140302e651034003a401c0c201c0b8515410601c0210b414240102d004800140313160003950007984110407507a00d5a8103480d000d8150035a2030704409020b48107000801c003805168505009000003070031300040c3e07482901c02090034208419081900820002102c071303c2107101210840880740107802546680340d081040503114441542c02a00003003110009215a000042030402050014188610300c03003500300c00401038070b50a2001c0c10103641d01240c1001e65042c00c3c0500c80c0d00503154107402d4520481900760803103100007100c80c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 284380017 1250 284378767 284378797
    0xb100c030807030603080f0403050106080106060813052d0c0103051009020d0605041d0d09050a0302041d010903020d1d0607141e01020711010302030906070809100f05091203040305 79
    0x442d4606009030302500280d030704018100d45c1c50032014410007082c2e000784000c0340c0c10b41c07070081300080d4036030103104090507544a03641e084580d8a49130300c42000d0a02407070054032103025440001c407009462216a455050540806801003040040306500b4041901d8405050601302420888070600000d8200142d0720440c500503191400142160010101500003d030460f1501c000300c0301b446440850119800703024000c49019446000303080b41c0ca128180300b1950412580d9109200615158101002c00d043d00d14000341d241d9003240c000c2d42503605805050780035070003c0c0910321015074050198018198003070b000342c05081040001c25024861804054803000900b00384c81d0500805101c50b240d01e440b96416a80591a080c650134003d41c00100201d40030040800c8404140d4068000ea0340304103070f0b180152603195078007403081d544144010210300c8140550f03049904404003510844001160700f0400180501e41150201d15107040e250308451141402e01c04c01000070792140440d81c880c00c0313030240 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 284381267 1250 284380017 284380021
    0x70b0a0e010e0a0b06040e120301051e101706010905010c140703120306210312050403121103040c0504020313061a10020c01030b010e0a2d1205010b100c0308 69
    0xa454018018401c03002c605000b1481d4030350510080124084c05044200d40421800d114018480c2d1b17100301c506510541d0710f80034401000580b074141d0850414296a20024018003c0d120000742d04803400109000480e0b101c00381940d00203484013907158028002c0c01d010503120300341070010b00f40c0f412100c0018040c1d42542c00c1c00c44044020f01c890802158008051007101c0041c20000c3c0280819004d00c002d546944000c60201d04015507040087c20380544a03a002c17240e000000300c0c05170100400c01d9040c440100d40321101c42a6900c44c0b4060041c80800c02a160b051038644507043c010103a100601c44c900502c2442114400c80a616407001e0707108000103a104c0c0312601529245801180f019800680c05030301142250300032502c01741c01007003642d04011220310310005646202c2601d0f1010b4104410420a100031035001400d4000e1946a01d06020040c02c90905150180c20b16000254606a041003081c20400c0c01d000d6000c0c40b0008845080c1210040350700240303103c06624002d410480c030040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 284382517 1250 284381267 284381291
    0x20c0402070c030f0b19050f011e080304060c0506100308030f04110d0605010303020114091c03020d0218010f0309020907050f0903060109060f09020c0606100203040e010806070e06070b0a 82
    0xc1400021a40700d000945080c00a060036000c01724102d039402854000310300b040071604501d04c1070074071404401100d031000740d01342001200200c400c08150b00c40346800450100341d59004002800040000395180c60008080e868268109038014225003034510304424107200207000901a02d51124620956240c00d50716801c9c16041148080b001c950003c00c02e00040b4107102150300014184d90003600248400345c402c548600b50040100e0300880d954110301d03040503400c00400f442d0300300c10026107800750406c41c20300f40800481c0c1c030201a17000d00464500418805580050081e4040d145030704040042011940204080360b80043c040d80410000003000d03006d02082405032281050041c080b5440b0b50317150a41c190080196004400354500025400900540070380202c43d2504402806000c40d901e41034144411141000c42000030360200340000705003004042d500398004d01e071800c000c1c01c080c20703c0100540010f4215580038050701e001c00c00c0b10041940010000c0d002a01c5050025110503e40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 284383767 1250 284382517 284382533
    0xe1f110f07060e1c0f0b06031f0f0b12071505030106091208070f06050702010b0d020a05091e0703020301090f0c050901200a030e0906040902180601030f0e03030405011b020c040207 79
    0x6180030584020101e161300130700c4484081c1145d07041c0706644070002503c81c0f008050f500c0c80d6040c020401c1d180107421070f18004500d03030095604032404171004200000b115000440c0090071100045095100410401056000706049005001d083c20402e1075075042140c01011a285c038010324020440c880d095404101c1c900003110300d50350b0071020303058504180f45840c1d00946015a0783c00700540c2401508406860800c4407840c0e85503004190b00605860041804a4010010030b20010300d080202d1080c451141c41078075a110f40381d1590010707525810039200d003040ba0a01c400c030031809494081004e44a5800a088411003042424110341041c3c056007080a150705040030080103015001b01c000405422208100d4003085c00c80301c03a0482e41e070321010710040320f00488020f54029400c0761404031031440e4580e0395410440626000c14060404410703030081c0d0740d0424100720244d00c000304101c140f03e0280321302840301c0100e050440f034658000200a51f5800a4000c0e28401c0d6070001e80c1804020b185 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 284385017 1250 284383767 284383789
    0x507050604081c180314010603140313060905060711040902030f0102090a05060c0a0f080c0312060f04200a210b011d0102030703030902010e1f110f07060e 68
    0x500466980e921039440c0c40e00e480072210f0a001901c00c0642c0e00b003003d400b4502c014000321303248108001040c60b6840b04481da40c514030070005a550b0b60300d800300104100f00c08601ca13a0007254000e55548500300111160807242e54000c0b000c00c82814020308c00d0307540300b40c21204030325044682c3e03e0040c2d40d0100024014090100c00950512804e811050252819005071a040c0c1c000c951b0081750540d0760061000c64890494490703a03a800810380000010b5040705240b403c103000b107114504102c0100482071850703010501c0c148919580008104180c84d04a100d0040c07028140d034140a000c81c200140c6101c01554241850f4041000c2941c0090038480c100c90711840700020051250843c9100b204001021081c00307042c0081c070844102511841e0264401001400c10ba00440c5003010b103440403002071000c040c0482c10014030300c41407200c0380e07640400e0b40c0410350a10a0421003c00452014084090002c054110b5403c407650114400c5000b0850710122885070a080150701007000c0000c40140c46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 284386267 1250 284385017 284385019
    0x60f060e07091a030718030605010807060806030709020304031403151509030714190b0a09081605130b030a050f010f06080606090702070e15010f030204030b0718170109110109030b01030807050705 86
    0x6d2000000d009031038000504032111501075600280d10350b102107440a01c11a40e154150340055000c2002110766401035610034002e142003072071644070308d818454940c815117101c02c00c03400420403c8103034904480c11160700803072600320918000d4a8004262a4032543c80742c440b00350480c6e910307403419403248030501c84403101465a400300203407200308901c06070701702030100b40004d1060140400c00e4800042c040b03010814034800d5080740c500d40001c0219042032620f46258540e110f02400f0015182001041d510a1003503010340400301891600e0740c00c4510340c1038a81000c03070130160304102030300010410680085003030310404220303075464500361301d0301100c0d03803080e200d9101e410700b041655001404260212102641c80c04030070301c1c81200031001c2e40035034040500010225000b080100340240b030a59906449810401c0c2e19a55030300310044c4002038a983d0206d0b59443d0203081040203405d48d0051019202400d00c0185c450940d00c8188150405001c0244170801c0050f0600a11400704510001400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 284387517 1250 284386267 284386307
    0x13020d0f05041118040b06030111040303020318091302210a0b09160608060607020a15020102040302042f03040f2907020f100f09060f060e07091a0307 66
    0x3000444000200000c4a003911074402811514080b441c09103030010202c02c1044c00000261100c1c0c45030314041030040c0c582a072541d0303201400b07000740d0040c1d03020f44004d501a4024549a4041c0c8803448017081064074500d1081209070300300302d45800703210b182e071102d1a0143c545041c1d11703000340036814101c0840b100b541c0080c42600c1103481080301d6103400714403030400c1e00c007590354030414907200307074032030742d45030040d4404180c2d444000b8009017030000c0900766550008080d001c07019901c3ea49141100d03d40743c00d40300107035000034080c01941881e019100281b80700e0103400070fa00ca015100c0e0411540d6021800e159500000003080c01e202d00340d4443d02c0361310b07040408540d8240f00740701d1a0018400d030880c031000030710716400020102400814110128040b02c13016005040d84a081e290003003004102602d15680d07103058150210703a2507c50041c041c05100000074001e030503c4014000b481005045a00b0410405800d000b800300c1403030641c0107180c203001c00c19140e44646505441d03030350710049420f009a03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 284388767 1250 284387517 284387531
    0x2100f150b04150806010801060f0c020411180a05030a0204111909090c03022b020705070b0a17012106021c050609010503281e060b0307060306050f13020d 68
    0x407039010060049a050802c0c030881c0040c41e03141690300003811141c00d404100a00010000360307000d031510f5401e1408610700b054800c2d600c0c2d40041c00319041c6001e000b014400218400311001581141444950340440d0144041132403c3d001a540d082d10a0000307024507281d0052540380008a003d030348031180f6801862140c2c08941e00018040101c51040e140c3c0c0e1420010040c2c001c1d0701034030031111038a4012104918041c0100c0b000315480b05641a912303440b0350300b0081103000c644c0c2404407002802158020f1961082e100718000c1550101c14581c01607546004010824000780020b00b032090000380110010406050500e08000e0250303070103504003410014240c111514250344032a02c1038000711010001360f62a036051503071700c1010f044545044214443d20b40e0fa00220030b041400441d00c103100e0102d40700030f00d121585c203244501d10111801900c490002e03419207410b01c410b40141496203000c21403a4030b41800500414802d02042d070051059101602c00030059804841e044d8248082c184040c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 284390017 1250 284388767 284388779
    0x7061119030209032a0d05030f1209100c020607080408040f140a090e150907050307150809010c1409040902030106120507080604020108191b080f09060702100f15 71
    0x19610000c01d0f58401c1c05104640c0080c08503c1c03080200075510b145c0e0500c01e2a10810074401000c10010081d10a0720050080e00d4030b80007014020f190404103460010550704019610340d140c000743c0c60910030070300d0502c08041a40d660000c0c945520a59501d05401d59132624100400c0c07901c941c2c1c00039604945010b45c007084102d0485282010403209403844801039030b4629003042203c0300d248502c029a00455a0000c003d0002d03114243c01506c140b00f9100c0d1302d5650b5000918058650380a01041511064100c103060b80000c00c40c6d5018282d58000c4c03081c00c111440043c140038810f18130015010300480e01903c2501c0303507445102116030103002080180e0311006100d103036444414045840e44070302c44000c0360710000466014040c45d070684440301e003501e0709100701040a2130309100d04040d555507268000f00402a03280c001c80d0021b180c443c0b004d5414148031f20703420164014110110b940c002c80c180060345034001045400700b030f000c010005100c4141400320010304802c030071480c10151050307804588 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 284391267 1250 284390017 284390021
    0x13080706050c0309160302031207061e050105030f0304050108010302010f030e06190b0a05090a050c07060c170f040b010302091911090306070215060402090d1a04060b060405060706111903 82
    0x103003154012100c2e80d500585c0343c00c42401d481d00000b0b40580069258122034403a4001400480c0e1103818003092031002c52122802e00d41402c0441c10240c3c3c0c589004010604040c059100d1021000c1c019500d06418000080c00388001844024100802e004250030164880e501104c0740c994441c007681d030141001c0c5100b4101e007030b41c0c040c01c200040ca081c118020502e041c1c10031808a8601900d8614155594040000100002070140c010b20004100c4070000031a0b41c428484100000e8803007160040000340480b55441004040b0035100e1000d2041c007000c00c8a41c034205044035811180c006445e550b40142d111811106000b504050b42011510600e1046140107895400c500340c084038002e0f0b8400d40202e0b9109001c1000d54101c1d60004c0110f500c500b4150010010700c0409045411030304030303da80d0101c4030f003040002c00758000710810500040243c0c0b401040034040c0c0c12146141003034144800541503109040000300020395420250106001c00d0003511914200c42140c105002141c500242c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 284392517 1250 284391267 284391271
    0x50d031710140607051e01060503120703090911090f04060906120501050f0106120e03120c03090105070306080d050c071a071115070b090c060d09030201050603010506030613080706050c03 82
    0xd0b4024a500b084006040000556081e41c2d0020001c19001d02c9403107125a0b034401c1069a02c803155240c2e8000f10b49500c0c200710188152044a0005075100c26508000b00050201d8002c079442c0303420301c00613506912024042c0c81e85480c0881b80710600390a088000f400422580d800110924140100001c080840c0b110040b0117601502c000c0c441660b88a2541e0142c1c4400d000d07a40125100301a1400c03002881c1c1d0248015580400441b80382c61501084032102008c00ca403121545035000003000040d4a0a011303090300042d60b410180941e509082c00207403070f241046900c0c1c041210200304080895001c01a50000340650316520780751400640410340668480c0740309503510441600c0004040c00c1c2100320000d20010303809007906010190740c501c007030703000301400b1744a25108001100d241a9102e81c000c0c001182d4800c0300241f400075528001c0c0c29104010981e41c420303403502003004401e440110b1100d500031003020300b0250b51002441c06100c54019980060a802d14140402000040e5040114 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 284393767 1250 284392517 284392529
    0x90c04090f0c09030837120501080c04020906070c08030c070f0501080f0712060b090a0605180609030f0a06052514160618030306050d0c050d031710 65
    0x44034030a121078030203060703030311090a11000a20444041020a9010f800343c00402c0403c0c280750740102c807020380c0c4480280e000340c1d10742d51030300f00494801403903401141c50708820700e0542080c8140c0d0b240981c019180c0150142c11409a5000103071864169a0042110b5803e41c0c800d034100d50064603034010b0742c1d40390001801e9070031504c28280e0226129001c12a42c2c0c0c00c580059403000669598080d10002d55a4060f2020050101001040001c900b6500464000c1d11103105c20340d488022040800070076803031580c030800600004200403031915003c60031440c0c0c8403905481060f03903402603d0120b4940b0114280340c0030103004820703000040000e1034221a001d140401c6221001d010309804454481325050500c40c0820340400c000c0302c0390180503014019030801110900c42e41c52580e120202590315400710070854100700d801c000201900b5101c0c42002e4141581c80a2220403150ba5044a00d0b11a0150380d20819410340c190040501c01c0301d986c0070300e07800780680b80c10605025240b003000001078001c00d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 284395017 1250 284393767 284393771
    0x403081804060b160303020703030b10111e030711032e1104050102100b011b0b011a0a0c03030504020402040f091a04050709031b05030a0b24010c02041a090c0409 71
    0xd60078070800c142d6840120070700360750004c11081e40d416802944260b008a0074551540e09d581070030b50340c2124044454029465014007401d0f034a00c2d49090413044501a4603100080c042d415003e01c001064440c0d80e0361010411a42c20b4000c00000d1600132001d80b51203208800c18036902070800c11900788040341d01c1122061060503a070400c9120b80f4040c40c082c441c01684aa0301d4070300d441c20306030025030308510103040507201292400e00c0d143c0c0844481c00140c0c2c0c5c06545800420100054040c00c3c000001401e400c64100610844020071600300d01d040a002c0588520204040d0750303071641100c1c01443d6000f400c0c1e42d015a00e081c444080d1142c0020400008100032400c070260425002d554442c00980e43d52086481c00c540e0740e002e0104c9501068419581c941001003425281048544d110320300848001a082c90070310840c01d03529845075a050320440c07015090346e50381e0341c02850740c86000d54120342c0800c45030640c058101d004c0b110011502d038400c610a05226060a9550082c0240c0d4010081 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 284396267 1250 284395017 284395019
    0x40603060f050906060715180308060d0f02010503040503160f020906041a130905060c22030c090b0d0501090b0604140f0f07051306171f090b06040308180406 69
    0x9030360440c4100340314580c1c002c083c41000070114a0604001c040440c410b401c808024050804050100d601500a41d8103918040c40c0c614141034007c424980e00c1030040701c500440b0300791075076042901c4010110083c10b000b8003001007001c201c0c003442500c58440ca00380c5280d00b03000c202d040070300d105c0c00002c0b005d901514401012843c1800c0c18014a04040302850581560480301818409403010751616a15a5940ca100180c000390081c01428014451071032256290071140b80d00c80b1074018841a601d900b5104108104001201004010203c88070300c42c0001c1c20b007240b140070500c00c030f004080c01056546841018010401c0d107040080c0220420385003082803900d40000c01207112415034040f1034405c8408002039003203010816580d070140d45464041d00b0080d1208001d03c3c2c0281c03a4000f040030ad449400140d81d17800946106607480000428031100301d0b41d4195074880c5104490040200d800c0e2281000300403a1140801c5500640e0b200344280e9540b9061800600c400c540941e40521032810014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 284397517 1250 284396267 284396279
    0x60607120c02130c081513060f050f0d0b0a0213030b04030206150109030f1b0515191403130203070503030c03091309050706081b040605070212010e3c0304060306 71
    0x8611010900c0a48817500a5214940200100042c0641c1c0b960310031040c545210210f94140580c1c4010a43c419040c0e1310f0070708140801861001240b140342c029211380d1206400710360241001c0340c0002d211840180d0380e10001301d02c100b8445090300301500030004d100a101c1099800140340307109841d0b00c0744184d8002007a02c01181c201400707101c06019045180300c440301284041c648540e00e202440c0212034510703914070205143c83c070002001c2100710700c0410390601c0c0300303024400f14840b01c1c49450171060924501a26040c02e000150140100c04800035440d8110b40b82000802e01900c0000c044a4682d0300b07182026949501c44082140146803400000905201d180200800319600001800505050a80482d0040e0000b8403184841940381400720a82103044020f0010b4181691081e41d503101074010f11a940b04c1411000c1e0150380346c070b000b0000c9994041400b140080c02090405507109a404400340240c6425103c1c030104085012100341c403940010042084500340d0700d05000c100e958107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 284398767 1250 284397517 284397521
    0x2041e050601031806020d1d1606050307050f0c0109171e03070c150219030c180e0a0b010e03030c06060a09050c030106140c0d020309120109080f03060607120c0213 72
    0x6035501c5820851300d2112030010311581c001e8031343c80004e900000381c10640d991713140c4035000f103d29007150b070740d04100071141d4029109840c002c082e1403c2d0507c00e2544c106036030010203500c1022448025100c000c940100d00c4d040a402006d203503a000145030301c0b4140808120442940030000030100d20807401e90101d006480380342602d20800389a00ea200040425417203401c0c001ca5042002c4039425802c01105030080c072640f40000345001c150350001120003036031070041d0255040651144d03441008030170400803d481c040712154800184200402e2162008005071008000b00300082da05000c04500c40070301d1400018914440c01c0c044a841c420981e07590310300c03401c907003081da00d1070385082e000c2005010345801221807a003171140a8035510304e45230008084505000d0454125401a04001103421039403a100c0d1581c4081c0b5840b000030802c00e40947e54080041c8070705d4860b841442400702c005121907035620b00751410702c1d07040f41240c10904140c200040c04109040340481c4a10f032500901c904260f218 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 284400017 1250 284398767 284398781
    0x4050a0e2116020109030b0a0204212103022104050d0507030e09060604050d060b12030c0709090c05090709150509030a030c060609021209070e09031b070302041e05060103 75
    0x12001d074500320700010311010a0b01514000da040c0601c000000002030751601d109482812411001620f50f800c1899164001c030104006000d0210030038558000300c0c0b0365042c2c0801410ba80060021001040c0350168040c0c010072005101d205502c0e80c169024550494031588958481c4050380c031280d003900015140d03402021005000100405003903105820142c0002c3c1e00700d90024121802e10340d44a000840c00500c030401112000e40742c1ca0a2030050510214401850f04420091401c014807105c1565442c003051090741900780d00c91030000207006070390340c80d80050103000e401c0c0c4a2900d05500d010300800120303c2180100d182c80841509654490810f0700c02174140100a894640f18545046482050020041d6803c9035503000005003401103100824418011018500081c9440e1001d42d0401d0310640c010b00d0540700040401451035008000c842c0c00710010821030003012160a041d616045958100a402030301d003407100141300500d107908502d0042d040c40280040d649100044003580c8503 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 284401267 1250 284400017 284400073
    0x1060603111b030921060c0306220603020a0f030c0504110318151f080601060206070f021c0306140f06030a09030e030607050a020601140306010314010b04050a0e 71
    0xa20240300c2100c0b5045010203036500c071030100da04200c0d00d80c002454992031044115031015801c0107065000509121319984101401c4d0003e040d4a17254000c01d0110582c08680903d914100880c02c0c0c15071520707809800a150080c01038429a901d03480c1031550146d8500055400e24480e050000c1d051804d40100a040d1043d54822400d40c1c60b000c5040e605a0301100d0081420b0003901100700540c8401d559852181c0d01c02e981c01d00d0b0740759200030780c00c5404c42c02e034000400e10707080036006009290b00001c003071b6009502480c20380e54201e1744503800c0381000d0760038003422884841600101c0303e055054020f0030a030b81c80c448a00e03500c4808201001868407203440c2680d0080400d00c0010042c0030603038000d43e1414003904200d02140000c80000e0700b01102100ea000109802140500c40d030ba6040101c54050030b038441002001100010010f070f5180014400142184c514885024840b1001c0d000303105a11809442170040d03082c4122000040d04060380000c0447c45040704c11600030440112540c90414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 284402517 1250 284401267 284401301
    0x708130905010f0e04030c2a0509060d120212031006080702010b18060d05010908071e1707080415021b191a09030601090203060405010909030f0c030318060e01060603 73
    0x7140902c0248403910040c07054051090503030144008c1510003081030030300301d5000a01a80a0a5074906440720310040e0481409102c460081001350349070a42c140d0407641d00704030105520724000d4001ca1500c096407a01c58650300e004801d00ca80c0c24044524541510101c0c0c490b901a580c0d0094101e0807a00c140190941c4100d240e0035882105503240708058001e0409072607032641c40a03a40701c003805e48160b001c1c1100c4c2e40070002150814840d1f15509460344a10710019801c0190241e01c4078003403070800c0405144204c1c8001043c03400c01c248181210000c2104401c91809000702d40d0000c1e44502c800307840581c060a101c0b4490300d4600d84411000031707c0707074100042d80207203080c54840d548202c20010300d0000e48008000500f05640c00704101d42c024201944050f94929060042c00107542c3d060b4880c0c05058288002c41000a8000141c0c0c05401628070f0841c40c10001c0b41030480243c00004a03281e920b502e2444410284541c0d0f808c10304c2061a45d0000780105542ca0030200c007100c501007030fa084640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 284403767 1250 284402517 284402519
    0xa080a030c03113c18090a020c07140103090b090f0d211e020c1b03060105090f040c090e0307030917060106050c0f030318060703090201020c1903080708130905010f 72
    0x729068a003130001e291a0780e203031252000081000c3c0d0090341300707141d904100300c038052100001d1300d4a40d035002c1e402480131a056092514880c61181d0f904064003800d6101100003e4400c01c50f48247e1068a140d82c2258043e10141070003055103032680c8841c01490301600844461001c0240038410310700c100002c5012140c201c83e00940e205009240c03007200380580542d29000c0e4486a00c6500191040241000c040c101c8400040341400d0340b43e210b07110003802500007400400c0700b41d0761045056031042958944001c80d95031880c10341c140007815040700c0000c070318154000302d1904000000c0e101c1144a82c5449c500c0c50703100c26040e11044036014032600da80d48100010300074603200d0006004440c00050403a151083c11509290540d00112407000c2ca216442a0b40c5540c0c40b41080000d400c03d401f824104810015138000170344400e40d903070304075000308030140e482e120344a4014a02001903411222541e00d4490b0f80c600a200355001100207000c001d4a21408507490b0910b124641c100c55100c00700400007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 284405017 1250 284403767 284403817
    0x9010504080412020a05030706030209190303020d03050c19020c010e09040209041e06050a15060e010903061508070306020c160b22080f250b03040f02030a080a030c0311 74
    0xd90194001260170980800700080c80b40c40070005030010340308076180035803507e80c00424804411108000410f5210050700d0030401319801042e8080b003405140360120311030307a9600c04003180707104000c031400c1c264218502e00e0901d1079000c034003002c01103c240c2e142002c41c5864010440007143c142d90107540b2a1100e004680041c05140a0b4141c0081060015626180c5515200b08552081714201c820701e45483c00003001d103500103e03400203090241007004a400030007000900038101130100400c842d07607500480390303004a480d52090040090780c2c1212030207512458070030080e4022015003a003e1141007041d4516905031069034054401c0d440101e414810744a05448100c1c0803000c282084016a003008900380409102e13820b0152400e0004000390707041885601c00383c4500386a61038046422060511101046e40e040f641c100f0f401000c040341d01030050000a050020301c0a000300b04007400910242030a415030441214103100b51010000d00c809207000540c0e500c00c00080103107116480301d0360307004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 284406267 1250 284405017 284405039
    0x5060a09050a021e033307141614071505091f0c03140c0a02040207021507030c06052401050d151e0f0f050d0f02090a09050105090105040804 62
    0x1005000e10125200d0b82c0b040c2e0003244c01e0070b45200c00504255842c3c1c58494450a0800120810003001d2140c1c40d4a110424071080701d4029003140100c103032500c00003146040b4410148003400d542c2d100702503a03807001c0e10010b030400319200200c200d4401d40f500b214035001c281d01007246000c0f2200e81016282d5032145803002c5800b6800401c1950b4403880d08883c0ca11280c03070078100100d80e05095100c07180b01d03510170304000c3c09403c00115054004c207010401050641c40c040344104085605503000350f01c800c82440020310f07440200c5200384007a00f0118214050644c815959038400c0d014070b004000c01c1e00c440c2440d4500c9200c1505911a105000142e070529501c110000c01000188a8001640d0100b041c048520010158808850030301207500c1c0c41d500302403144641c80100040c626038002c1524201e0100c008803214401c4034481c0140040c2c00381448442c001c007060980d4020144021480d01e440880c0044c0441a0b0503200d42d03280c0800181400014482c003406140c011064034140b40c581130880074 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 284407517 1250 284406267 284406281
    0x50c06030c040b0d0522021f0311030a09120c020307030f0809041409010b010819151a120a020721050c060420032a27160302040305060a 60
    0x401d1003010400000c0b5950f2400160072034921001e070200d2903040c050964a030004180d10f19121b0f070008007843e0300050f03a030070000714107000311081d0b030074411100c44000380c00030542c8028403c0070403800010040f01c2c40c1c0d20b500c200031043c4641c080c480340c000850320484044440b03140c0207403d6406154140301240f4000c035040041e03031180195a250080900103d0143c2d031920594460560140c030a1000d00c250031b01480c5c403110801c0c60690f00c5480c0c42c600e0150610020101820071556502000582d02c0d0b04c10000405059400c110100c81c1d0f0841d214240303d81d2155038805e1105101e40041500d070405402210302060304040d502c1441760700441c02c0b400300d42040300c0341030508c0010801d1103030341c50091000b2440740c4c0c000c0d0b90340740441c3c88018409015005070031232a803190700142d40180b4484c810510301d8400104140e07017901000f21050208403034411040d61980e000503418540400240112022072060f210035482890b0b0031002c100913401d9005a000040c00c54000000040c401e40325640440c2d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 284408767 1250 284407517 284407531
    0x7050d0c11030d09091808090904060e0d020c0a060f0c03140405030a08030f150d1b0e0c1b1b040e01110408030304120f0e0909160902091309050c0603 66
    0x4049001d8950000e0310341160040c07500080340515804209052803481403250003200c0c6200e8010540b1196203a1803130f4880d0503815403090035501d000c6424084268042042d07140c21004860003102c810b00701a5550a10300c1c41c1c42c2c03040400d44400b0811500c21420018030041540b102d80d1100405d5905a4070601c4a040c0c420503150701b400000781c596010003c070200c403801900b110b0380d01c2c01c00c501d0351004580c0003848129802ca103070040f01003988458904007050b41e0400102110316a070b803040d03500403d269600c101c1c2d03603801b07000a102e094903001000300341c601c0f0f800d01c01070080304480ca0090340310304400800c0c0800c01806003803d4224102600b000c85203003081c00001601c1611410f81200540103508004542d03440803040108100200c152440f80050070704041c1e07102031645100500000b41d400149002d0010030010644161082100b08440418007600c9a00380b600c51004000a4110f5003519101d07800f42401c14614085510401c2501a0490081c01503010300d04240a800c0c1d01c0034000b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 284410017 1250 284408767 284408783
    0x70f0c0501020307050a030b0913140309031e0609010504052e020301031b0b040e040f05240a0c140a0e01111b090c13060305070509040501090e0f0307050d0c 69
    0x2800029000c0c0b008511544054031955100e00f4078040c0182141c801c847c00500417502e0300248581101d0f540d6101d040d10740e0017100c0003848480301031440d080d40203004084d80c040c0310b02d0741d0660039100c0342c020183c0c2800a20302180c01596031411040d007038038000c0c1c6000e0300ca500b22031595580b040e590310760311841a509800440385036000461440172603009a00c103417080b44140320350fa42001c40080150004003d091402402c0074205882005c4800740500010038000b1074501c44800c1110600c41100c50426040c2a0080c101c1000d801045c0c001040312000b100c0d1f440d203103403801180d020345180740f911001d0510312400c0c60003002096855802c107840160520050286042100c20300300001101e041c880f104128034081000c00384141208081c00c00c0b00c5008062210b20002e5903625079800c212012441d000c01c0580f0b45150949661080f10b040c0c64005003040004114003061760483c851054601e0200d03081c1c10941d5500d01d031a8001c1500052042e007052240c40d80c02449191259040341c010484 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 284411267 1250 284410017 284410037
    0x610090308090f12060417130b28030f0c02010c082a030a090c051e040b0a090603050c030715022505180609090106120b0a0204121a060315070f 63
    0x4c0c21041c140d59a0010b50f8415410002004000c10341c0d86d0071502c0c0800c0807418815081010500c0c40d01c180aa80340d06400410000c6c102d01c140e41e03848c10320740038000d5074500d10b92454900401070084512600555030502070600040c0b441403043d454402c2c4180c3d035060541c0c9800850386601c4900710304000311021500c141d080808051401140201c0e2449400100240a0714040c48c070001607600c02441400b80f40f0300801c05181c517124000907010300702c400080100f29000000c8903a9190f4001a103502c0c40d00d040402003240c00920210f07040000c030211703a0b20aa40c3c0244802d000710410001c4d0050f0070030010542e08024400104026400c0c514a0101c0f49440f100070803000c0b6203840680005100b2001402040e04050707810f5034014a40c04001c0c400b0b241000310f5007001590040c002480d0b6800f100010b0003c044a40c15076015100028403084c0356002824241e5110444848500d01d84031928081243d610b0300145c2054070388400403c50030303a5510030401355505d140e4a5884414010f01100d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 284412517 1250 284411267 284411269
    0x6040b060a0206040303150609090525031e02030c0f070501090813060305100602061602030d150302011704110906191e0602070317090d0507080a0b0610090308090f 72
    0x201514008456600610f400e1070541402002e0364160218031640241c8071600340510356109403500c0c25030742402d03c0407556803104400c0005004000302d0740881565102500d00c0400d5160700941d0300c540078109c100c200984101801d400303d20050310244060305c0100032065183e10036501411a15018400000300303644561a000c45c26484241c44100381a96040c0030b0118a802d03119031508031a801c42c88540081c10080c1c01703555108003034800c40c02400000c4251149503c00c00071941c080500040a10200e41c0012031500c0805031400203d0114080c520900005600f019040c0d01c9142c00c0322580344421000000e00c20050707805001680c0015000704844070344411030040c0b40007030003000b550b8207298082002c00b00601c290ce030400e0085411240341080401e46c09602e5241c00c0c0040d031070242d51600d00000280ca02c0c1c080c201300500074081d410000802c0c1c900441e0744401c082c02070310201c0042d80c0e0340c400c020005031141c1e0b00e080070a40c450030900204400b00d0140c41c541e540074003401841c0300024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 284413767 1250 284412517 284412529
    0xf160203070e151305041104021303051905060c0324041d07080d0302070203070e1e0103140c22050a02090a080718180b06030304090f0b010e0105090609010806040b 72
    0x40303d00701d24020111010180d070411504c1d0500022a91004102c581840d03516440c0c9503403c0180e41d80719a40100b18a8a81c3d11f952070894011a4800c084802e080c400c036008034240c4011050640386c50081600040c100c0080400f01c1c0c2c860030845403000410b000c030050440c1d048061504440e00039582e00366002170315034850107485013414034800070b000c20ba2800010301c1c41d05000b000b40408040c0180404001614001240d00548210346c420402ca83c0d00c0f40704007503e03034100112612540c8da10070700002c00c1c4035810b07203403580705c40e000ca0a0724030940c500003d010214400d001403003070210080011000c540410750001d42c100c2c00c01940945414502d4000460440054200315401d0b0080d4204018020705640c044c1200580c00501b0b00c00c5c0b42082c0c0c0886e5803580c0055019026100703020002c0c026075418405c4501410450f201001f800913040d03101313001800d110605601003444c00b80c1da111503600503416a01891750082c501442e02020100443c0c03408006028950003640f9642c12541c180d482c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 284415017 1250 284413767 284413771
    0x10608150a020d11032e06120914011103150108131101020f0f0d02011a0a0e09010e0d030506100206042d0501020f250803010902181203040513020f160203070e 70
    0xf041b0040c0e1400c46c03142480340d03800450ba0074a928440d1002c11181d0740080001c0440700b0112030000b00c0880e14140012444140a00003100b546014401c054100c0c2d1407014601031540e0300d400c41648618032005455095094030719000c0d601121403071400250003000b0b540c2e034445040c41642c103070a80244006107849014101844c142e00040c0703414081e5070b170921a07003c40b0801c0d00050001c1c024000c01003610310f0749d94091b00f0680c860340030001d150080c0940021002da12004d003114608455510700800510042c1c03100d074401c02022202804152000894500035a080004a015000c0012b900d0886440d005840089104031103401004500284042d040081480342802c0c2d03543c00800002c1005564000c11501080030420030384003180300582603c1c103480c001e1200690301c20085650100d54034072000caa662082902c00c401040402c00b0000e00211401070710760b804020704102d0380d0816400b520182054541c41800888104216894809602400601aa0307041a00d51400d480381d100f003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 284416267 1250 284415017 284415031
    0xf0d0f09170c0d03060b0a0c1703250815010e0316080c190308030408071707050f06060123030c0403140a05100c0c060b0a09090b0405010608150a020d1103 68
    0x42070500e90410300f400401c510a4035460100400ca00700001400d190140448001c02c1107400c041e13074020402c41c0d100214a240381e1410403622071800f400010700c90380400288d582c0c801d2840c10030102503030080341c001d809207081c1d2545503144d10311040111640800c665610360f040c4244180000d00241860702c1d1000380c900c020180c03100000c0401440703102c0400100b02d00000c4000d0902f08041200032080d02c0d049039020480d10350f200c0da10700b030450000030160011226040c1c0094080200a400100d1503032001c20030054a1300c9644e604019241d006000601e50000e41424590207010184a8010b40d4004041250720303040503141d80b1452014001906030038490340c88282c100040c08010070900b01300000d40c08050010821001d0024010031001e0402064661100520b8405a403400300c10b10107040c01e480200f06807051400c24050090007650240c9d401d51800304049a800004a00100e13401040340f99400e50ba01c446000d0002544407003c0703801d0880d0380700701d03e0f244c1441d580d0055018000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 284417517 1250 284416267 284416313
    0x504090c03140a03020a060e0c12010203150a0b090d05031201060f020c0301021801030c23071103070f0302060309070509070f080702060f130f0206070308041401020f0d0f09 76
    0x20079480c10403048000e00040e8001c83c0c1c041140040003030f500007005080da83c1d0040000c42d5009604000a1800a907142401d50141000d078114188450540c0907605c1084020780340314203000080c0c14007032089658001e10028401c208203544490500c0c131151a210303849007003200d2a184a004200704002000c0c1c0050000500c105c0311003484950400c15000c240310220000c508c0c2c03001400c8000f80c03038203203904800d050540b144603844403140254102440021800800c41100201500c41d46c2c0707640c0320541c03c4600c244601e0070b04405041c00281042550710140005441504680030401d90f40c100504180541c85507800c08980703915411422401140640c9038005e03584100348001e05240c20060183d02194450380802405110384112940c00080500005601c40f0030f9040c483c91100345228007035040a0001145410180d010310344520481c080d08106d2030b01031420074094283d01c1144004c0c400b016040c09118040c520507071180000c020700d280001207568140e51994030003200c00aa0a400d03003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 284418767 1250 284417517 284417519
    0x301030309061403040611070512030106180503030d050408040f06020303160305060a0308030a1518110a09030b100503150f1803030a020706020c0307050c03070501030c05090405100504090c 83
    0x150001c91500151055081602994100c03800f0703400c1c0c40c04003d00142a4649900d00e01e100101c00300c0861ba040ca03001002d07600e9171907a02802003002d500c28850000007600b403030600f112003c3d402c40100c06951004010b0b501d4100e03c0440b041c080e01000c0c0066592400400c00099035210400d0084001c0001d40c0140d51246001741d030b03004c20241440c00110901d403c00302008465583c840f0035000343c0354008d407a60780f40d0302c0c0e00c0055030007404441c3d142000c1c481b0012020031841d800c4c81c1555078042c00c0e402d06208200c05041701c03420500401d40601c0120b04103281c00e01c0003514005c0701340d0f8011400013500c4d079400c0d600c00010380360070350301d450511b451860041809080010111110341c801c00c45000c00803842801e04046a492000410a1107030680c045601800c02605404071004014240300320b0b0340382d07100740c00d00c29190820490400d2003441800700018155002e0b0017070310701c40d480c10b441d000d0410707181c40c080c8405402d00030142d84001101d0710005c01c00782d4031072040107100c500940d0001515 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 284420017 1250 284418767 284418773
    0x60206010e0f09030a08090c1011160f060534020f0303030702120c0a02030a030909050f060a0302010f020c040c050409270210020f0703061e0c05181309050102030103 73
    0x40c540103000c90101d010150200300f2007100000c2182c2500c806880c04158540e5420107035030600544580c129400211812020003150303000851181516081060303500c0d910400461418030445440f58480e10001d0480404c44903000d5400780100d60301d507c6e008100149d2a031000044c0101e040400e56104c000e924140080d8207109840c43d6400100350001e510710308043d00003a649401a100c803a01d01000052506c0141c101888015145540a0211464a0038a103005802400b150050440240c41c0c2400201c0d010304856603039000d02e501030035107016141190011540a044003040b642907126a03020a07405440d81e205035603807103c4030b81d0740d1500e60f0f050500c81020b5520145030010080481c1c055810f0300c4440040d28803083e54100e650020801d2000c8007681001002c1c0031840b518050790f00004140501601300c0e05078125180c0002d8050b00101d44100c08407507203900c0e02c4c00052014416030310b9401d4540001aa071407002011018415001c0b48010b054a449060450302650048010010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 284421267 1250 284420017 284420039
    0x302060f0c0c1c02011a060d0908090315040302060a180210020a1505100608091209030f01050a09030909141902090301020f09040507020613060c050405100309051e120a02010b0a06020601 82
    0x1060741650422a1b51a4041c4002109400b94021445200c1c0e500d9256000300320f10b45045400c5280d01034140d420750111072142c508a80707000c5030141e026000f9200000c599012038401c02c1020351300458445281d0318503400707000d605108d8070b60030415489a424a600800d400c00300940d040b0f01c5942010130765140541c400c004a0410394091800e2010f08004d021702890f0109040c1400ca5022000d80c0c0c0340c1002a0000e80f402c209000c0030015540380c08140075040d0392640250f03503401c1c00390304c47c80e0f0f50a6680c1804d100700d03a82c0c441d66006032030800c80070460018408003450268004001c0150038204a80c00280c01c9a020a141c070704040750015582260303051502079241d1001807800648014034140300c012030410151080203002030f81c6c0304591001c05001d901601c000c0c09025200f080b000345d400a000d00100920207060312144201a500002c0400504220f661810400d024224088800e07030005000e4010f003840f00c0c25952101003800da9926050301d044000d00807a0b000703000303951500d885200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 284422517 1250 284421267 284421281
    0x5040812090d140f030c09150d06090605060703210e011a0a0609050307090207050a080d0b0301060b09011b02031e06160507020d030f18180f0203040302060f0c0c1c0201 74
    0x403024014001200760411204c207495000351070202c55682c0d20300b94000101c0a64155106440605021520aa4125240d4041001d4555214040200fa61590100b24040c012240b00600040206440300d505c101a000348018035100380e04c02041448881c2600750a4900d840f0b20880b54403038400c0c4440941c40c1400c0304a0042801781400840c150400d0080f80d02c43c070700c9010b1a038001d500051100c08100341048110307640b03a00409026103840324100c41801500b03441102ca8400d60030254003190b41141c4000302c410320001615104c1a2881107140f0031054140020309903414050103685601c42d502c03d500e490110043c10018051601c0e152000d2183c0001001c4080b08103c001e02c01c640041c0c40d00341a40d1040c036014140302c01c00342100142100d40d654084035840c44207040041c009034581500c000e6560000c0c56480a100545503c0c6622040780000c440180041e40702c8030200d08444101c0000d590020100080c6920b0954030080151038680215002d103415044000103036583e81d420310801d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 284423767 1250 284422517 284422547
    0x8010207021801120803100b03070804051c020d030f090b01120219060e04020d0b21070b0304020d0b040215070302030406111504060b01020106080a081e0705060a05040812090d 77
    0x21883d41451850503540020341802022100001701190140d018001c030000144101c040450f580c0c0383c4040b0061a202003981c04507007503c2800c0711600449280d0410001020351a4002c10602c14407a80442c090000140903101403a526030403080840c20103920b0a020301400c0401c500c0c0300d1180d2051154158180d0240d4942020000050105951250304185040800c45000d80c40c0c3d4802c1c828180180864003e00d81e0010907040e4004500ca01058010b02800441d0141ca0285684441020040c07100700ca000b0351006002d4515800240c206580a40190002e022602d0110f920808450142d10100040c1c0140c3c3c4089404c0041035404551818884803207409402c4450075116a6449550042c3c001880d05454940d2041d90343d10035070001c0024000c803011148612060304102929520421444c20701600019100c0c2500704180c044130303c51079000f4000c1401d5601c45202000800b0060002c0303c00c100100041012048840d42140c003900b0018003505045006800c00740689000a00074 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 284425017 1250 284423767 284423809
    0x8060c12060307030b06130f05040c050307060203390303180607030615030b03010b06040b0310060503010f06260109050907061d04090c0e070f081005060a0c1502040801020702 77
    0x51000807080b900c0c258100c181502c61f08902c0010400401c05030005c0c07811003140314900010803040c4075441d400801210010703400d403020709486800480c1c907841000c00c003030a40071140011800c03c42d0041c00d0311403042850464102c0320340c40038001d00c0c103645c0188c40440102c840901082c130740c07070020b0003020340184150070f0402156181110780140000740f28842d4052540d26800030010f510203402441e8030760001824a0344d655118490584190000e45160303440c0c10300360740c002c25010b0040c012641600c2d0943d0a9440d010301d010030480b0300070025034210620102c5201481c61002c20459144c1c0a04a0910081aa0f15044c20070342e241405039844042001411004032a6440c84c070394089030504c0c001e1f1400f0802c5002c500342801c1d01246544a0801e55140100b0010144d034081190008203415583d40c200ca62034408080751485554001c00c0e0380003500f0800740c0f19882c021812585660301c2044000d200f9083d410381c8804030f820a07844808141d4000641c002103280c01201c54100f10260344030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 284426267 1250 284425017 284425019
    0x602100b0d0b070305130203060c0a1101060303081b250203010b03010b0a0b130b03070201050609150603010b0d0f0e0f0114040b0f190608160b0c150a0608060c12060307 74
    0x9120b900c010064002014140c0e40e4000c00e26980c1d280c82e1942025070042d00b129110b0604242070851a0b025044440001e403c4102c03080e9a22810b00480049a41555070411151109501c80010f81c21205480400400c1080503a8580c039072034424540014125000440781813450062500392001d40200e46d1184e49008008501c07a55101c40480958501000d01500c0c3e1001400340c4007000d00540144242000c040100b061036981500100e10885068800302b60340e480314849001d00c0301241d00021740c068010b1006000304542b440180c1300d54503648502003449448404108111084490544507e0b0001040c2ca54511000d0141c92004c980350141c0c44030502d06529052602e08000c0c0440c081d007107010340030440c200441c1100015001c1d61000070000a070703035800e03a5035490b03540d1141d1740200c1100c0d120005030404c0e4035081c2d4003120769100c06000054a05098a0301a650061080314015955072000c2544801044105d11915205e6031a690b6818139622043c00c07580000c110034469401114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 284427517 1250 284426267 284426273
    0x403051903290102010b030105130204110c1002031003080c0105070f0219060218060f0910050903150405070801020c0c03070f210215180f04060f170106030c0602100b0d 74
    0x400110410140201d00742c0d080d4003080100d01400d28a41e0343d9030b2641c2010103001142010703104088066100712010885070210540c5860035001c0d074050710480f5000b041e0f48042411180d001143d22040c02e0307807050051512541c580c0f20a4100c0c42c0b800c1d00300d0f1b555900b003061003900000070904055280c001003142c00100d620500c102940500f00174100c4e50080f030301c0f00807004015400c1071058001045952a080a01c013081003a4000c072001c43c2c4104400c81a01200c03034010305c100c8080307940240190440c1c08212050b0072150101401c1111503200301e26001424581c284090b100e40c5001801034003060134180d0426207040d1190300000152104140104940992880100215071200300040d1081585000140c49070700c240300d62200c0d00307800152580c402c00c40d840064503030303540407501c1c2150720002c1c0c03042c48120b960300d000c0d855510305801402c0c005081410910000c0c031501000201d41e450f2251380310300b0302071038641c0b0cc58050380c80309c00100c1c0e49400500030f103013031540145c1e440c181c061941d403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 284428767 1250 284427517 284427551
    0x81009050c090105070c08060108150c040f03120c02060a020309011106250507080708091306140103180510151a0f1c0c020709150b22030501050403051903 68
    0x10b1242c1d4180718001450004001c0c001da004002000140c041d5031440da5a240340984661a900080f44140c1c0303000000341c00246860240d909170f46844000c0400e030b6096948000712890298452030500030648920001651290000d0401510503800345031070b112110005025080140c3c06102c603504003d0400c9500c00c200c4003e14400303001107e280c0952004100c05582d0b030f01c240b0b000505507900c001000014010100000c10f4044802e4450201750344c0c05c640d4030411241c0e80e000e82c0300340c009412602034040d84240c01022a4405403056580e1110890360f0701e0707240a070342d9010034490507210101500c1d90080540d1800c020b01d80700c07580d40140d055080207107000b0322404e40f85002014022034111200c15400281491286041c54104049049104065503e5074244030f1000382e2405c1c175410f5101d0b134818030f10704021070b10102065410000240e0383d804103800124041003007418080000404101d0034003540d03000318000c0d1500c946d51018013a880c014841d06c11180c0e001d045c20090010303c040f00c05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 284430017 1250 284428767 284428777
    0xf0e1903032408060103030905030a0f060b01020c0901080106081908040504090c0306090b0f07050c0307120c1a01030b070e1e12070602010b04061508070e0a090507081009050c 77
    0x1403078006444070b890311405076400b00000da48424020580c00c0414100c0d80020828103032402a01c1e044030150b55036003015582e09003000000c0c1044134a9101000203801c6400010071402c050041d030741210f01d851f0208150703400036400000140c6d121801000042d206100c0c18210220000820f0400040f586400e8818031036881158000c6641d0302a0505011500c650000556032018082c000c086880c281408500021b44046400d111560041a40640203a00b200c80781100440514200121602c0b5540400744031942d80f410301090f0180403001500c1c2d1030400032514012000c0340c00c1075040d82003a19418400501c54000d01107401103c009594521008c034410348a5490004401161000402c414403401d500c1c3c3e84e02c510944a000c41c07142c1d0103410070071f060142503404004007a51099602100780c400c40500c400704100c403011a500301d20440800405107400b4000044450307031a6020b5084a030200c40c018005110003061025680c03504401740000c0c5140d02090250341030101c080000c9100d4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 284431267 1250 284430017 284430023
    0x60a0323030403020607030503041209120b0612030a0c0c0e130b071403090708060609040c050909030f120103031e090902090a09090c06021513080703020c090a0f0e19 73
    0x31144004040d201001140c003d50b9000d0700103903c84200d4079000e00203030025501142c0041c1c691005020182c802c0314030307408590403004c0040b0b1041054035064280c0c036014201c1e0360003440300403020b58052020001814206038035550760420200604045824180503040b180f0015810300620480600109403a0201a0000080b4119031143d901c1a2000c50384e901c40a80c1000b00401005007520780410004112549501507034055502c0c40208411540110b0b0028035104903100240300c28103080140503404130114045a1a00e410b45400c4a405e40088104480c9144a84014000c0550152249291407840802c44289000c140d0000d00f0815150141821641c3d0204c0c003500e00d6960300b10f4050042445100800c51001c20341410342c01520300380505005842000c0070398032103060511055120360803030401010400e410b03076a61402580a000e090b402c6201e8030700034005603552100c203036000f400c40c2c0c10005894007515040b2411703180c070380384003c0140e0050149d98144030401c402100425074 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 284432517 1250 284431267 284431313
    0x106030203030301030807050d08070f032705010b040e0a02102303010810060503030913050c12090604050f0a03020c060a17090a0c0602030f07020d050a0c0902071a01050f10090816030b060a03 84
    0x35030078900b62101e510703904900744ec8240c00c44002080c000194003c1d89200c3c01030702c0a001c40090b0300f1070641c2d1034200203030083d0000404118804614480c8580300c20300c0001002d48410480300301c1070300310590803e8100e8402e5400507072075038020024134401d10005010076005181070100e1003001500c0e1511646d14008410707120700014200101000440e0030a01000c00342000350700300303104000d64644003150100c909120b1401c65480d131034000074014070400e41c994001c2810b83e0a020500200f600714107170710003c1c0b0034030b10313000d900701103401150038070900c0d061005104800081c01c1c6041d03450b80700e60221080d50410001c65a0404454080f01c0c503140e01034a42000700c01507480d1903071501c006610050481181340c00041111002900144400c3c0d01070044201050032180401460030002c2c80703560392102100f403c4110600f40030980c400d000c034090800b00082c65071110401d080c1580949190701c081c074080d00a00401810100075600b01c082990b0b514061400c0d0703941c0040440145410041402c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 284433767 1250 284432517 284432531
    0x50303060109121203240909020301061a07080d0b06180a09060f060305060a170703061104153c110102041202060d241d0906180106030203030301030807050d08070f03 73
    0x984c03218100b001c1d504400034140a19603441c000500281300a0202700d20075405c00c100021414015400d824a5000c40720450b442d0055540d6141c0e029884600010003560300ca4400100030342d907900252542a15a1a031105001504020801c00c02c43e150000e001240ca441410b1010101484810003032310044d0500080e1034880798002503a80c0410b600440d40304079401703851402c03441301041c91021644101010300c0f403c41020704445860085004005d00200c0ba408045039007840303503442c1c44410b081168200540668103c0400c8902c40140103c06814500e00c2402e042c03d074070000042e82210b811000314101401d1015940808180b0340000c0d226586c0401c070201e2800f500c0e8031409805c0680c0420f5044020f0502c41100c45107054820003d0050300205488103d5080441c641d00c41d940041c043d00031030303540b0341c2d140c0030821285504480c01c0d940c5031004001a102000158041d40c043c1014546030640e83c600f041ca0400300012420030800c210060058041d0400709070704014038a0300300441d8007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 284435017 1250 284433767 284433791
    0x501030b01110106060320160605060d02040f020414190e040813061e0809070306020d020f180319120807030b060a0e0405090c01052d07050303060109121203 69
    0x6082d48640c0015035460800d0001d00300e031309940403181d100102400143d5441400b084841540035614034403040c400070440d64000200598085980000d00804105102280e500032400300c4900d1000202031a03400502030020421841504031084021030b243e645540300401640e6642ea070511030f0700d404050340c20100d401c0001840075184105030f0340341c15074401c503940c2c00000c005c001d003000000d0701158004440300030188918061840f801642c8000c206032480c60342d41100940c09411041e14042c0d0910003011a814103000910300d0601c64050010241090b904040c01c0c0082c019010740e02d00e202509003070004050408900c00000e1a0501088a584107207054024103242c2962580c03000d800100102c42580020755880482e005581c1000146e84501c001d5580b605058109030126100f40050380c40007051405120100c40030180f41d00c02c4400c8000c000c0e40310380103414211802c0c0c0000c001c1201c1947d1080b84080101380d0903454020105507500c8005a9195814440c420113842e03034440c680b2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 284436267 1250 284435017 284435027
    0x8010f0b0f071a04050703020906042a0e04021804060e0603120d141303020d08090307170c0105070915020a030e060d0b120d0e0901030203030901050a030f0207060c110d090501030b01 80
    0x6820b18480705181140b13803d16160f51240d2003800203e1040a01e81d000c0784180c1071a1242c0905020065201c4410345100068545000c0f08070f48480108070b44ca50700c640043d2207500150001d441020a415445280c1c0740030002039940c3d9400c0342d00d10084000401c00c4940c2e00150080c07240c2c054400566940142900d060301a0280015842d609440c64051165a0940c4600c1540300350095080d036040c9108600121820030003500c294100d68000d10000c008140d41884020380741c2c3e048042030b403a000c0d0030280f17079003511011038103180407580d10b4200b00044010541e0a4000d25001e10203450035417000d40e8080c0090f0206800709004000106005040c084203600120003000d0040240307050103003040031195181c20381d40d065000500c3c000c5c00b0034010300b07200d0f0645041c0c0364010b01460a00400d84011909900100300720b50030552500d80342040d011044c8010700800d8000c1c00081606540c0d5000540b101c1009070b41325000350700161400f0406d076803008845003540c00901e4086203803600800100d031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 284437517 1250 284436267 284436293
    0x3140a09050405010f0e1003030815040f1407021c1205092b1206030f0206030907090c02010b0117061318060203100303090501170f07120f0c08010f0b0f07 68
    0x2e0024909070000c0742041c1d05425040c2203131940004a038190b40c503400c175a5040005848010080380021020a48004081c80d80d10700102001e4000a036441600e418032041d0344120030644030041480c000d000302a5170511007524491305404020716440381ca40f1004041d1a581e8070000c0c3d85c01d945001068103c0e800384070503d40c802c00d050510003a640b448420b00001074620468001041c084c94031001900401d00456007225041224900c2170780d1160288001584010a10a40e0b40034411010403205040c1c4075003800040e955000050000e5004005030420f400807514482d100412000c001d1107940b207000c440200c400c481c0c0c000c240407c0400240503a103558410061620f40080104030008002c10401c00440b8000d50300c41000715a81c81c019540300d031410401010400031303040019030101000d05020f401031010f02d4480810203c8949610454480e40d2031315002039100e44900346060b510140070380c00b520207081e17850102403800108020780d114aa524100000c00800ca80c000d00c03589a40c880 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 284438767 1250 284437517 284437519
    0xc060a140702010323061c0201020a060b041d030301031b05090a0b0a081f0c0c1a090703080307030c0206070206010b161112070602060f0c1b0c031002090102060603030703140a0905 79
    0x51041ca001704c131a600e4200201c5007035000b44528400b0f000b41143e81001141c2140d0181c0103080300c002203495200103402200552038000d6203820780036003025424a403540c030050402c400f40d6100d50451400d07080c1d80403585290084040d1514082c03005a4828030050f42108182000045000646020582110155102224070700500301c241000c1c0c1c0d4152943c500002d850201000301082d030490607228212500400703841744450410101e4400c45100100380c00c0402041151481540c81d900c801040d88100c807003a0009880b0b668140126030104160342d040b06490010380385644c1804000710b000d001e00d1842e0203210365403002000501802c8d81803c0c07803013840a85401c1c80c03d0b86403164180d40d40745d1032007244014415640011031030080c2c0e04041e03020303105104090b8505034203104894204c2001070781c80b24440c018095080801d80e4104008104c071a42c200000da211724003100068109a401030045000782c00400001e0b0010794494040c0400070754001145843c0c42000d1001c94510455801032 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 284440017 1250 284438767 284438801
    0xe240307110d260601230403110916121806090204150303050a120e01020c0c03060a0213050603060102010e060702010b0f0d0b0109050705040f030f1e02030c06030a020f16050c060a1407020103 84
    0x641c4003400b450008002303803401260000740c101a004107202c907142040f51740c2000344106110140e990751050f1a1650200500003011a1030000e00300b184030a01c0b0040c46c2218040d83e11100c00c011810140210941021070900c604c61043c5191000f403c6885041100010041406e11814140010340d0145d2114142c1000841d240e101c414041c994941810803d24828410400011401e0500b802100d803100084d528010b440352401041c00f480380c001070801815035407210307044500b054040100a100e1825a0b00220781131303c0305004e021001a90040e002e0103010012810030115484034a2030b4111103121303000251594403c46c0c00c413118040c3c0d0700f01c400321010203c00002841030088106010702d000e4000c800902d0f00602d170a100c13400000c00c1c020b4064118580d0b10400d8508140610b03803201e5031581c0945803e801c4071003402c06038040d0b402c003400f400c20442e000003442010459170b5480071095030020301e01164014043e100071070940300038810950000d07091085901c0b982242108040c21411 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 284441267 1250 284440017 284440067
    0x60a02100501030f02031615050901050d0c0c0c050307050904111c031106010f05100309081303081b03160b0c0702090a0c030e0d0e240307110d260601 66
    0x101d410302e0980003d00b170380f09224450246c00005080300000088461a40c081038115240d42c80030b6031355400c4810094140241030007170101d9413400f8042c03662132144680d00c1c01004248c901d0311402c50a1039402c2036000c0e6000f00b400b0b12954440c4881c1c16003241d00200071591464400300003441c0d04030703204100205485480807007010550002c40d52500c2c40d05107001d40c0c4041e0307240c00d605079844905200b0300d5800b10803240c03c000407901a0f440440040d028464aa20701049a05580c0f0b01051950003141d20304400150310541212100440b006230381d08002451801100105060044511103c0500340c8110400883c0002e080c14080b02c01d099405062840103142501b02d502c020800088000040303418980070b044070340c0004c02d40749000c12582c0c41e800118500345090004801c0c40c02c6803030301c0401c01102032030a1010f01101451040980f5030328507140c80c10701000241042d0541c2e01800901802503411812032001443c96881d80c0b1910030105050b40c0c03504012a07100900c1d1542c641d00c000302c0a0b0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 284442517 1250 284441267 284441273
    0xf030504230d2309061b030c030406080901060f180b19061b0302030421050f07050a0e060a0303210c0e0a060203031012080c07090b0a080d080402060a0210050103 71
    0x242d4600e1900282c030751510960b00307a001640d8071001d001002c1c1031504100003aa4042c40d00c04040c08499100c00403610700000034000403890340e4000080c00145a201107410040160f2001110b58484200c0000f03200e103078a008207102e446103040c002c004407211403801c038200292240d442220041401805c040f84104a2a00900220814000d500011342c1442e12000c00d1407024410303821003070b4964002c5280034502003071003082d04880203804003900400a40c500100300c00304a000e012030000307005881510302d41410001c106100390301c10402c022610b01001302d240d8a860b1003d040701e03058141000203854100c40d00e40e00c071180720385100c03d5038986001094000d0303020000c900512410b845030030619440b25030903607482c0412981344407030100d560024846141014411090180308030201410946490034150a0640541107810b070a5580d004203a11072920082000c010030009015109075540c0410040c0070700001403001e40500e10001e00b001c0707458400c00c000d000844448104000703d5841b85 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 284443767 1250 284442517 284442523
    0x120c031018060203011212020a0b16090f0e1e040c03112206090f0b1e01170403020303071d031b0111010c030905100b1e0109030b091c0905010f03050423 67
    0x100c0242c68034201c42c0c800704440da00004403089c03650f41006038100140e5808841c096280702404481c01040b01d00507000a50444950401e0090005511404c49510701b041103100c541c0138003103020323060000b50414400801d0300024030360183c13600715142d0310091420308007180b502d22451504040c0c09480e00104c0d6000d50a541c411410380756084c5061048005a40514080c0c0b011040f013035920a1380317075500c0d0030200d000051842c14400107052081031052009482c08031500c0407101034016070400001c00c8800f80c1c0c0725142d40040c040c46c0605000b440d4516020030303542e0461011150303080959454603841c1e0780c001c5e6400f00603c40940020301800244100080250080840850f82807058000d41e10740101107018400c0c40f41005824000041141d20400300d0101c403c400c028103204030b088003c000702e540c28a1440c8130760700860007040d8204107404510744007200010078800f002001d0780280640da074004001d401c03003075051401196544a80c1042405018094125070b151500b65840c4141c480c004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 284445017 1250 284443767 284443799
    0x2070302070f1409010b0f2d030c0c0d050301031203020318190201182108070510061e030305160602040807032306160309110a06050306120c03101806020301 69
    0x69540e40c4e02641d80e005038000900031241509500700003030040c200200c0c000200040d01d07943c00580000a00b0b410001455254019694031400704400513601d40c0e40c00b020008900004400e14001d071440d0b246417100c1a1180102c1d118a0400d03800002150100224880c520f200500d018142d5202d4a40342011045c82c0c09a144120701040c2c908402c1c110012013021100d0440e00090090450b40c8031079224001006203003030045481c0320b400c0c040000400c070b040280701e06602d80303240e002071400d04042000c030725007040030f225140c00d0001d000c1c00c0c0002070740710f800c0d02d19840700c1c00800011340085140c9900a4099900103070300c0c0703204107800042071005904518007020114030003072039203030700d60259280c03205400c81f032040c1d482c8611250b43e01442e20030761202c0d510360f0103031061241d44000200018080100e0354000707800544048144481440c2c00d0303500e00499144a0001c21080c0701020100382c07240419012441e5555895000007c0208400001450300f03a0140c82103590350703118202d40d640601c2c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 284446267 1250 284445017 284445019
    0xf0f06043b0604020f010807140712030f180303050c040b03040602030a18080403020105131d0412050a08040f0305070b0702010504050d030212150a05060708090f0406050a0902070302070f14 83
    0x900c1d2060545480049080760099402404902641300c1800054610302000343ca40010400c010218690264030b20303014008280c4210614600103c0d0030200605032039404005203407042c13a16410091b04086010802c801503454103010415545e44140c0041d140078643c0310540c06003001040000304004c65004501c2144030070002c018802810451404000c00b0b02c00091602200304424000756014a003d003141201d400c40c40751846480c1e845d4010107103c0c11030b80c0c03c612801c260500c03080251000100f001d401607450305a04003540303410001c150100280015000b941d407104004240b502ca0800c0f1900b01c0e070050708135040741c103108800074000e00c02160107070b449000320907402c0b011a11030b00032503400d41950600c000740ca403901d1158010026243c040581d02c404001d0001515442d10009000050300a03003181d034441140000303005800c6640c0c8040e600c900c0c50500180225070f01c010ba43ca0540e04017a00050302c5103043e01d401c0c0d01c3d1010300d81101c0341d044202035000601019010540443c0b02e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 284447517 1250 284446267 284446361
    0x506090c1204150e0f0f3f07050a030f0e03210706060303020a05060f01140609010e31230a0e01050412020d09060e13180b060a0803030f0f0604 63
    0x5640714440d889501030240c1e05542c851510800100403070328404c8111800f9014840032500ea43d184883c903c03623000000848036500040c55100c1030603008072140082150a04200603080c2140c00065250600100300400c1c00003210940c03048e1039500029211071560000c42040703043c0d268207010707546002080341100e0034852140010f0300d005040d84003504885421b5285946031104d542002003079044200d40604002d044c0d4400c0c8460340e10b02500764040100d4a0400c00d80f52108031159007030b1002c041003015550b0400543c0d00e1840b403003800c5048440c44040d81494581c4520038880702505441400e10519800d1078280001e00c440c0c46001505030100e5004c8441d1f83c4021541500c04038100d120b0000440c0c5840b0b05401a403c00c0072540140825002000a100c1170703121145580e001d41c6c5605480b0800c69030108110b40c10480042405411004010b505601d0118030014000c50010484280b154003007000c034085e515281c0113a40c1c100b9025080c440f640308034100303504840764003084141e4090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 284448767 1250 284447517 284447533
    0x70f02100201020f0a080402121b0102191a041b0303091d04050a02090a02041a030103020a080316081614010902040b0d021c110a03050708010506090c1204150e0f 71
    0x24014804c41d0000c4055510b0305060113140101903804c0d4000034010303a0007403070100341542c89050922400000c2e10410f00c1072640403400c0c1d000245041000a07640324403031030003c004408504c00c0207400c40e44250140e15900943e42d1894aa0400c0107524141c185030640d064003c01003607008007641c0c054490001040a240e040c1500009002c6425100a0204d1b0070034030380a0301508102040503400420814098030303040d5545c0d9803007010000300d01010034101c000700c0180b0462404000074001824010025420203885035185501c1d9560304400800c80c810011f803502e120b0001300003920b0019008005140034011100c0c05501802401100701e00c0303207290124510741c51a000c0468086160098440c04000c40f04240c2d150030220f00040548010608010400c1290b80d60b00481e4082d5204002401c0740901e0310f0021420740b44090407181c80744e8a250f08000100038850142e90041d40514680c40040c6c44034101040c0200c2404120015141002003071007040740005150700e00c4099540485644c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 284450017 1250 284448767 284448799
    0x11041d0603070b0f21061309020f060403050604051005090d1d1002060a051605072301060f0e010f180c090504050109090506060a03020609090a0b030d11010e072103090b070f02 77
    0x200385c0c12610035900c4104a400e100071552164003a03105144007a14401050300340da03002810b81e030042e40c4110758035804801004100304083c03054210390454007400b4032a41c1010500d00ea103402d41ca0840740c1c00c01a600303000c64070602e241403505401c16400341c0340c2c040500781c2030002915071030100c6600b402c2500306404034601c861001804a584441581d80b40d081c0700550340c83c0b20391000c205414010b607002220300c0702d140340020b10912000304038641c03450b10024035080c080721a00380160301000b40b541d40c106003000b510b5800c1100c0304c501d07080b490000030000c0280c40192202070094202c150402d00d050004170f49440342d0743c4001402c50103141210340c00e44e03031441081100141800700a4129405000000403400c1c00c1441c030b0b800114400000c103502e050b5001003850020840e517403100203200d852001c04811801e1203041c0807048070801130582d0074101500c0f004042100031800a9841c1c41594810070306208901603c0501454510b16030703640c099040203a00d0100700d0760b05078850b5004401c02024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 284451267 1250 284450017 284450077
    0xf18030f060621110613081005070212130e04230c031612030809071203020a0c05090f010303050307140313021504031703041502070507080111041d0603070b0f 70
    0xc40b9030040603080620002c405006480c2c0041e500106c0419044c0030100d070614050200c91041a120800002e85180448009150084040000c41201c10800103c121001c80c074000e441035803013000040c1c5250721140380c05c800010850f403801044003500d514100000001041e4000c046108904480a400325820034030b150b42c1c0f0920071100341c1410b001940300041d015243e11075100d114001640ea016075980e8180c04400b0343c0701000c03401030300080e80000c1048880c2c4001c1018000c103075017070111450309a040a101c01c006001c05014400088000384049219400680f003218501100503100c2c1044907458030f2248545030100c0c07044042c03101d1030050311581802c3c1d900300ca8112084003007841c0c0301040070880c0e51020304180c4d23440d103501d18040420031060000b090703080d104d5001000303805d01d13203065142141d10707440c0c01c080d000e0303000c1004102100040c40b03075403600e00409100c1c000540303419000900d00519580021000240810488001e10714503014100075100c0c541202e040050741692403070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 284452517 1250 284451267 284451329
    0x3040e0c0d021611030f07050f04150f050103140f0f0405031b0a121719090b150a05040b1302031510020312010519060e041409030720010f18030f0606 66
    0x6d0b81e4011501001503140850040f81c249c000508005141c003500490010320f01030942280406400c03000c410881e0307507890310602550054031000d41d8803d05001c208005100030160955141c0d5440d0f10100701030010607c11a01407070400076075030342c40e0443d00e0040c548a50000070196103d00c14840c88080b60350040ba48580343e40701d00d00711014070355155000c1c0c0c0880820300c050081459036420b000700004101c820fa441c0a0403d0051090800c1186801c01c028010250000c0f802142000d540c00303c19150350a40c8600060000400761320703031340c0740c050000d5451503640b07070140e02a2550700f40581c016004001807051000681050150385c1e00e810501c070210507900702c140c0300042010000c000c0e9a11906c5661700c2c0c4d103c02000170884540c140700e880c110500c2078807483ea5035000081c80702c0400c8a482c2030381e08481204060300c548c00264500103002030805452810902c000d0317520009a050401007103a0140d03501030b050031040e1640781020401401e49016481c081c1c000c00c25041042c01001c48200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 284453767 1250 284452517 284452543
    0xf0105090106030f030c1401020f180f0a052404091b02010902090106050f0c01050108030a09060903080306060901210524090103120504030c1e0e010803040e0c0d02161103 75
    0x4039451050303541150220301c50708058664002c0380003003181d0300e11f0a000424501004901a40e1162491441440f80410b0780c4071982c030920f822009c41080380c89002c050300c1202c03001c80d400008001060032045000b4080d0b4012140200c00080c0403c1007413090b441071311044003a103c00c03102c0c00300304c41c800e0307007282d1300c020002e507003c480000100306080c80b841c01811aa60039500f894280241d215456080d41c10a0304083e10540001c0f440b080000d500c000c5110040c0150302d0141300c010302e191201c501c1440040d2409004110004120010b6406500040040112000d81d0186c50826030300f4030009180c00d481046000941d44070783c8400c0b000b4040070403000d5000400c043c14991941d81d91911800b80402480284802800008045241d03005074000820045031034100424000c0840304082c1040d030080b903203120000300140051000001610117648126001c8070381900c41c0c0c101229940034010062840f5070000811109509000942c00311841c030428045010a16540415494003400e1a403d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 284455017 1250 284453767 284453783
    0x306050625060204170c13060605030412090503060c04091a182502100b01051309020904090611090a080616180902071b0b040f1412030c0f010509010603 67
    0x40d01c06001c4a180340003606200311001441d0555030030410003402002d40d0b2582c4690407200325000340c0d00303080fa030030340d9055070043e01044001c0c10041c01a03c01d0101a00140c000a50f00825603101383c06103402e03201504004040b07628900d015104040250300c18015000c2c0c240c1041e5507002104009464105060001024100521002c0100c90880c040c01001480003c0481030340c0e040602080d5220072410903103a001c0c1254411a40701d1000b80c0344513040c1d250400008105000004802d43d034001c00b5500c01020160f502e00c03020000802505240701d000e01414036040b400010050324030000e0540201c19a400c1c0e4065985840460319103c003121483c0041d002031201c0c4090a10980721026000c1c40c4d4002c4080d100d8a40702650101d800071b4008640441042d00c00a050760f400c406100000c0c1145504c5519260404482030302040346441280010031070344d124080c00380e0359000460074400402041360b84a4240303000d140c2e0340708291b540001c040d510708400f0030301010301800b8240c2505e40046003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 284456267 1250 284455017 284455057
    0x7140a150515190509130201110f120d0209060307050405040e2e1113030203070b0304080a111c080109180c06111002030901060501081602150624040603060506 70
    0x5001480c04008900043e8841c0020042100d58405113014011264100d00d961307455807520002d445400c2101c8102070503400907140c80800c0d100051031f640300310380c40d040c62502d81d42602200401b03800381115040c1d01150120030400c0860380607020b0011114111001e001c0c10411a00c190f46a54000d40d81c01c5e0902e0360b4103a094840d8240b140b035048a140e110f4000581800c2511011150350454001c50710100100c000410540ca0100000c038040c060400210340f8500740741c0d0358010345110f400b1081045c00844101c4440d0840103000f880503c0c080041e920403c5440014000d100c070001740035404000e443c1c5505145882d000d1800200c550798003400b0f191600b030074020300b42d030846007598140c10140f15600004104407203a002450007029841d002107006420880050424840140031040216140b12408070459002640c25180012410013600320b865000204054010b1146520f00c68a54450010a900034200c01402280e6541d41c04110702034039041000854031075039000c1840c034406070031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 284457517 1250 284456267 284456269
    0x50c0c0a02010f05120109061a0c030711010306121202070807060504091a0a09050a0f050c0a030c05130305030405090601144302040b0a0501021902030307140a150515 73
    0x100c0d014280e54240300e070906052a140b6001c45c08240c0042030000c0e200c1c4c0040080b9460b00d540c0b040030214041499086c9034000d44115034074040d00d20080d1640030481701c42c035050b9001c4e80c030140c003510300601c80c0150785456003030200c1c1e807039040209000107107c1c0c805c00103485203000c644070040d5000c80d078031036207003030f01e00140c000c0606810400714128100100c500d402945d5003c900c04000c003100403000c503817841c21140c8103048941c4032842416003401c2c90b080004c1c030b9010500b203590301c0b0107078140090300d1080304c28102c4031801850b1003003c0c0b580c000d010100c2400000000740c405c65104a8140742035079251001100d10240c1e407601d07204030003002c0c0300c400d0b80d0640341e40c07e04c8d1280301c2d412880c0c1c440317403040100d82c10390300c410155000c0c02880c1c0c034550406605050141c448502c07003d0320302060151a0100003551590b03913000e2550700702007502004085680038411120702c95007041d2017010880304842010340b15582e000302101c5500080055840141c910300a4500c2001300d1110b01d04065880300c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 284458767 1250 284457517 284457527
    0x1020d03020c19050f070e010302010503040b0a3b491e0915120b0d061b02011e020306010c0b010305010203071101090206190908060103030e04050c0c0a0201 69
    0x651420890003203480c1c0444030003c0b0f030140d0700b00a003d00010605207041919a5040a025400450410540380e0042c40940d800c00c048941040d03201540c032940d1b0ba00c1b1003814000b000303611200108816032a00030b0b0864010389180740c44081c04814401401c0100200340c0366a4034070340d51002c0ca00c2021082c3c22582e0b014070b001001002d0300b022060051b4014242018040e031024070440c2000c5501407146241c222203662010302c801d0518203215500317606200003001241e406c030b2241010000000715044000465404c000c40c4030601a000a102c0c2005140075000703410b84001e9004c100001d9403460408903c1405194180c50b5940d9402e01468481c0c0c0000010350b0000707010341d05000407215a20001002185420f000390b0082000589034185003000274140e078140e041c00d2a03c0d0f8101641400966544000c44503080103075803415006940c00e00040e241403495034050b000a00400000105140c0c000440200c00c0c4000c6404003d260381d41030702e40e410350090350002c001a038002e4110b100194024 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 284460017 1250 284458767 284458777
    0x2030d03021608030c180306042004110d060312080f16110604150b060a0207090b190e0103031202070b06150d02040f031106210c090a060305060a1401020d0302 70
    0x2c140300c01e000061600c40000591040c2d8540e0507950000440e4440b00c0f40342140384d070700608203c0150541d800d041c1c8512406820604803070480400c0ea400e0307090b52366541d6000e017240c1c044103403210340c07240036050310b00005000503c0b05940d0f080030b40443c400214441c0301c1e010b1080030b00d40ca04c0c1c0007a4441d00407042c0c00030340380103211050000400c07200300032030000c214841c03207075120f1400c1300ae004d031f034402c0c5040640c0c084a415a010b40400d2021644040e0003150f0813040d940d00710000201d2441000000e80d00207040f1101954064000d000410320641e40814203050f6402070704c0e00e008006007084880102d01c0713600d0000e440c405000020410a00d03000d101c0c14880b01034860344904144a80a1480c02c80c0c0c01a80000203c0304004020407c2083d0b02d0f1005d003212a0444400703041000c03801001000d00345800c50388040308010300c0010f00012001042d62003054014082041280d207a80d0080c000306070581e812440781443c1c00002440b40c0c50800d00700034200d03040e4040c2140581e00b140030341c065081 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 284461267 1250 284460017 284460037
    0x60e1c0203100207050303041119060305130f080a08070804020a060804051e012c061902122809020f011d040e0c1206060906010c030e150405040e030702030d0302 71
    0x200c84404072041c402d80050209030780694080c5a40c0d0409141c40e86003003642c0b03c0000d000d0b81c901070444a03440a001f00e04022510749045c0811640e80b407400c00d2190900514008050b082608194010302201c0c0c0c0140810050f6600e440d0110b440315a030507207460b1030850b8000d43c4072104c05800d00c01544180346082d0020310034000c848003800d8a9110424001c000c040c1440b160b0f54641803122080340800e00065500c00500742c525034004000d0034545c90b004003d10740842000090440ba40340115681182c200400131030103544181018001c10702d41c0302c001c6450700b596100c4500120405803041c070500b1021580200a82485031210380152820400ea4040f0f42c2030f0100500f801c0d003992200c2c091070350f1101000340541106d41000c000c1052822034440b030032065a01101c10400581c56641142d43c000400342020040000d15181c02c517152400c200364150010702d03104035651b983c05040060801d445044070140a5445154020790b40c82c0500d0001030340c5070784070fa2508102103000307500a28415103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 284462517 1250 284461267 284461273
    0x8090a020f210c01020106052209150c050310081b011d030109080301060314010f0b28091a070f08070611190e0d1101120e01110405030601060e1c0203 66
    0x150084031001c00d801070300303000310b8004400b4140d0543c0d0a105050141c10211209d1b01c101200e030301c5002d0300911f84c501035164550f50b43c2e51681401f44442c5450072180715440240960081014001c2c810741094400082048134243e0100d54040301055802c220004401103007410001400111480050707100d2200414851000c0001c85440038000c4401d1180030780d51a03640e035454280010111000e10bc1d80d05a00c61000300184170004c503005549007140d441d404416181d0101d0b446203d014542c29020800703d40d8220f44803014203402015050880f107030310401c41d00c80e42480d80c00203128807400c103000f02a0407500d0308070b10000381c4410180c00307018000d120005004503181e00d41d000903440004554041c00300d04d283d00c81c0d040d0b03104140702e0390030409031135824000120380d44d4003111105099400e4144103280c840c90940c01055404134403008119002030202014030110095150b203c0c0c020340e4083d0081c4000860401c3c05144075a4403041c010f40a02e00c1040150f08448842c11082000c85c0e042c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 284463767 1250 284462517 284462539
    0xa060510050d0f1a04050a08070201140301060c0b09030f12190203040f0b060f060403030e0f22051f060516080a03050a0b0906091501090302181608090a020f 69
    0x34444480e00c0c0b0390144680d1071500d400d00181404140030743c549201d0796464a004007000001100491482c00d6194071040507515442a440180c0382c68080b4102e17801440004000082d0065000d010365500902a800d1407160b070311000d9035141c4a100301f803414115807400b0066010300d1b007046441c0d59031010007114400c5407501001055801d07a8010307942a5880185c4040035400c0c0500f50042a411a004031400034100c1100000b240d6907004511016051046410001e4400d440e5414030014858005000009900c0140c00702c40d15041c8604100d90003d01d0b100c000303030500000e0301c018401c81c4d00201854904034070b8020111256480035021000c8106105001c8001031058805001c0007440d41c0c40201e4185010310003241240c0b8684201c910540d0307481c042c06181d0300e03552039294000f503820718140807820319400180c03143c031215400250040030081240441803440000c0c140030304d0b00c00c1c044503270140902c0c030700f268801c1d07041d07960a03026000504018014030700f6890304140c44102030303d142c09075 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 284465017 1250 284463767 284463769
    0x303180307120f02070602010c0801050409140607111605090c070c0f06021c05070c061101090807083001050d03111b030c2704060209120c031605030a06051005 70
    0x190150710a00c0003c9051034400e1926143c06100050180110348002c001001d09008000c2001c0d0040c40390a02070341e5901021014080c4c203548529851504004803000760521460041000311580b2107031519005100f0076006041071f004407030040300c6d001400b184007078590000f443c001e40c0c0005001c850b9403c010303000140b1071080c2031055005200c0c40e001313070034100860a1582800b0098005550801c941000300e03100041c1c44c0301600d0f0036a0030364500a10356684403000c80d80100314050000d41070080100710fa00400000d04020b1801d0710325180781ca40180296803182a00c5502100c84808000115005204038101680001c14050191900c04210030100b0205418040b02c4d003014150305005200407115400c0411a100503140251078486204180092642a0741d140100c0046048020b07404241480116015509a0100100100b10a54545000e503031386282c407062903400713402224440b407a095174030380808040b500081c000c0d0041040943c0c5840080400070311101400380c81341c502140e5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 284466267 1250 284465017 284465033
    0x110f0d02010c0c0f08032e050a0b0406021e030c03041202040b09070903031407020a14040e03041503020f0c03042601021204062307091805060d02090a06030803151c03020303180307 79
    0x47c00001c4040b01007290803e030511a03050078540100c0712480e0200810005240c0c001508007d401c1d0307000101500e5040700018609511914403240f0b80c512000c140400c000600001411a8038800c80342081100070301814040501750403034100b00401e01404c401c0010038061024120070680d800011443d011642e400141c2080f440e030061101c10030385103490401c6042620139042d8400034a002182000d140c100034001110110301703224200342d008583c5c2406c2400c003005490346950032030207691302c5603103900e00d0030b20311440e0760400442001c040b07080c0c198031003040c07003214002d40d401e1526500d2560b464603184e014000f0110415144240d010080b800056001c20107400f07410655200240030703183c400c0088a20b41c48807040c00c403891801c802d100700c503960605022213503035041d03904440c070303035034808030400200041d90001d0f101c8000002040039100c804510140a654103c0d204107a0425100698095004200b00100540d0003007010440a07605600701c450340780300e12821a4604000c60b034805039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 284467517 1250 284466267 284466331
    0x504060503180304121a150f010c05070e0402010f2109020d17031005010207150f090e13030906020105100302130b031902100f05070303020a110f0d02010c0c0f0803 72
    0x6a5103554285c40030840004104256103501411150640c18944400d0788135094800c0107a2140241c6030101d0011f07400307462040550b40d00b10302510481c0e0b548280011905c1e404503412070010300c045205080b6203009120400c6501c0c1c0c07800c05851310b90803040707e000c01408088020fa03800140446000c0004601076040300c4000703141089240c03641004c4e0b540c1c0a04e1b170f070b0641000e4159002102c051001035a8801c0281178a0040c2c504030901040b6800140c5200109410a03070401c0180820040144034000d28080300c1031080d92035001c050b940351030407400c1701d5056130740300300c159200e00c020009441c0904983c034210101140026082949000280c82d0000000c00b103e49030b2800580751096140000d0a0341d4003010300d00b41400c482d0b0700c51200900503c0380307007001001d05078040340032802c141c451102461404502012a00c0a2412104079a5116864000b0703900541c244040d01d0303480c0d44210300304204140d03c1450064640da4582d45d000040d04010080120b50517040e40d00d005501720818616 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 284468767 1250 284467517 284467529
    0xc03041a090a03110c0f09061906020c0a060801060806240703080105150702060304030c1b03080c0f2404020321120a0908160218070201060915060504060503180304 72
    0x102c2a81c940074201d00840360310301c041908515039021143d2540217400105400481da0418660b944400044220501e903540200c107614081000c01c179a17400041c00c402c0c80c0700032540b550056170340e0030003210040424052400000c8003440414081e00b44103564208041d4150000400c005c80e4460440b40c42d00b04203015000191804010891420300a00d10034042c02d080300c4103482c00c251500801c4440c44064401000c20205210300300030700440422890000c6811300381c03801c1050f0340c1d0420040503042101487c450740901c509004941344002038450800c0d14003039191002d01d01600c030000501500074016a01350041040c0d10300b1400052a00a4240015040c5142c980305464034250712900000e1050124900d00102c2c0c6011540e05001d807006000740d13076060004150148003185108000c40240c0f81485690024040760503010b401010654145030300402907442d0340c1001c000103007800d03c908000b04000304400c1c002d4078071800c01103a010045901000300740c60840a0689035911a038041 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 284470017 1250 284468767 284468773
    0x2a160617040c0806480c030408030d0b12010603120c05031c090302060708100506031305100c02011a0915010c05030d1e1505010e030c0d06140906040305030c03041a09 73
    0x80b0401030003000d652040c2044007034004411078005d00d2602040000013050904444089403501d110281001200c01070808a0140c03038980c00d1160398180600010f4030302501c100071401c280c5042020502c19101103d07002600b0300081e800301c0d0b1040e190584541010350315400308004110700700c0c2d48910010030140c51424001001c80080c203000b81050300242c899010044a81706000c1c10742c00440c44035080d5101200c09903035a0300d03601e9008040c107280c03800c010400e00030000d0100d00244150720110000f103c54009100050304050120140c800200c0034551080404000c42c1514820034403103041d001044c149034108030740c03503143c4c02c0c82d541001c02901159038030381c00c540170481c1240c012203c088126000900c0840c1e8445210745d148c0b8424054541046900c10000780c01e0340d4104100c4e441c0c0780016081c3d9404000506001011b0b04031200c02c14210500301c4e01103255044009174891086030540d58003402c41d142c140c0300071016880500180c0b075030701e041500b10f210344c0720f0840071038000d090180007 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 284471267 1250 284470017 284470051
    0xe09150a0b0d0c17070803030703020d02071a0108070f2301020a020303030405010f060b0c031603020106090230040201052b05070221090607020409082a160617040c0806 74
    0x218071308503021603003442c1c4241c020030030070420a840001581c1d00204141405600c07101d807111548024001c0ca0006481c200324a1442c00c8100481c2c46e005042c1c8546100b80e61141d0745036005403003017103001d20036910510201000c1d0f899031344001c01108404801441920340c44440c54000a2450b04155000e03121650f4850201100c13115511441c801010840301d803c0c1080d81030200151640941c40100b03800794070b40910901014406e5012801810032031030115103d500002400a0018090804180242d400c001e0b0751401840402c2061244d98140e403428030340f2020083d50402c9082103042c07007204056192480c90190b09c14080e0324032400442c1e008151b28441214840c1c540c01c010040f0044140007001803003c10303110501142c10b0b9680559011504800f5071030408181e2083c442c0124100711a041a43e0714000b40844990924441d08100c4840030a00b4810842400e014400d400210740c050310013000d00c850758600980d0080c000c02c49000d18650701c00480d070410071f0407101e601601c00c5240c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 284472517 1250 284471267 284471279
    0x12100302040c051209010606170a1b09050406140a1502030705370c1502030d06080102040e0f010b0702040509031b0d0906050414060702030a050a080706060e09150a0b0d0c 75
    0x8036007688502000001c1c80740138075110005c2d0485920301d541c28041001200011a40d10440d00407c3c4a0100f8bc01d01040000418000800b40300060055921480c01d00300d000071940303951031005d07518040083ca44c00c001842d250440345030808241404040d4001408100b021900030700048030140380c5400c0302404c40f12414844402ea00d00e0178401e00c22182c01c0142c0401007840000403200342c40d416280a960000e500744e099185001d281400003559081500210381d0740d0043d00a0310445070030030304018081c0c94050784890900310034011815800002e21101c005460243c020700e40003d01407059a10b005004015160fa0580c041100e5000e64070080d29040ca00394420002c40040845242072030a00b810030888082c41040c40e0030b002c0c891030000c40c454003507640900c45071b06055441412a10790304040e1a141c12181c00041042d14464030f0311000081300c0904500c454851282c0c60045c2001705503900c1007a80480d4054440030907030f940d07a04151025100d5031007039969580980e1410074418a003403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 284473767 1250 284472517 284472547
    0x1305010308131508151c05011b081b0304110402220b090d060b0105130e0709061e030f1d340b0a02030d020a0c020310020c0312100302040c05 62
    0xa440030680c2c2812080c0b443d4040d501103085900a8104d0b0400c1c03241c3d8a4030400a0540da00c4402002c1010b40c42038045410840c0550040c0702941d003806071100402c09451081d140814201e811001000181184401e401030f02d0005540c8039200b00c00034400ca610b054003180490f00504001c50600012450240051444404000051040c103040b24500030f55030001c594008a503002c020b00d01e0751075045501d0f20f6030046090b02ca13400c810100400741c02d903407005620345a410030341c1e080c070102d500180d01041c01446040c3c90401e51441003c580076980c440307601100101002610083c010380e480c440194100c408000b81100036103840000d00d0342d542c940242d00c1c04401c102d0b180c000d9010b880000400c000c42142001c1d011281103071585901c80d800b548041c0d0540c464103241d03240c03152001400311032064000302030205040c008e80894000e031a0440500f000ca02c40c040b207070b10499006102450704a08107009007a40003942c4610306003907903600d030b000c00c068646108026001c5200412a450100110 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 284475017 1250 284473767 284473769
    0x26010501050901050a0513020405030307050d090815190e0d0210181a1b120f070804051b06070c0815150a030b0604020c1f2a0509130501030813 63
    0x2c07242e1620551501300052203001151003030701c0c0260f85020300c2101440c80c0d81e06035002040050240d950b2100103141090304c8030540310f02c1c840450741400c0007084440001501445104600200b006180c4070f45040c4140c400443c02080601ca0700d0700c00c0c800705004180851100048a500280b40710180d2380f6030310003501e00c0040300d01d01e42c03102d88000304080786600540d000500460845000d0980781c3d00307070700d241c0080c060400c000d00400c0000d90800b40d028020341c051040081001121342038954030030445100341d05807005040c9178040c4048080c1c1c21240d151008200500a1510b80391401c103a581d0480c40280741e1000500d50815a000000b00a44044040d401484e015100c0f091141020000e2000f1484d800040c10306a85440011900c1d00c841e4101c90190000c03600303d030030a40c0040c1d0307041c8441c40a2060004d1403030801c600030841d11200340640c2240c83c0c8104400d1031585400104440b42c2e0441e003050b545c00050600380b420b008a2501c02c250213140984c40c6195107200b0790080d084d4124003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 284476267 1250 284475017 284475019
    0xb1003081c0902030a0b162102070c0e0124030b032109040f020309010e0f060c1c0f0e1c14090102031902060406110f070b0a02040b040e0906090d20072601050105 71
    0x749401c0651310b100230241e100d220000c03c000603121f00050030064801d1605410807039030700c07001e50000324124000900000215588915121411004a5003281560040c015094241c1d100c509a20290303400c84034000c140e11340d10030615081400d05000030301600e4051200c0c1400320b0b4004207211040f0020f0042010400c403d0001b00000340d003140c082d036074940008166600c003a43c046072441e4504004d5110512004148809204068229418000825100c1d015803038074800c00048036841002030680307404040c4581c4400f41890052454010280d01040302c20741140810410040e500b40341d90741d0b400c1140e00c2c95000707004528151610108444c0b415001d40ca609006000403090100e03d142203880c001d5000d400501c1d192a245001c8000c0d0042e038108541c030540125022a203030510078000c501c19207081007101c0180d00d607100100e803240aa0b10040001450750b42204c81c2c1012030b0364881a4072602c4d10100d5182955071305550070a07030304600c900c844100b070f0901c010707124070024000c040c09880 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 284477517 1250 284476267 284476277
    0xb100306030c0e04050d030506040f020d4a010b0a26120d020a090509070c06060b042103090e15030610140111150a090b1003081c0902030a0b16 63
    0x102500c17195641d1500f41c401808242d02e840000e4002d407181d8105000902c10740e40155251890341e51544060034803401b80710a113241034281e1070798900b2000080401da80207081c0c21401405101002c0781003070002c0100b02c0c00c41d0740700c1d001c05110781c8401c3d13034000092580c181840a01c8040015000d01c1810b1905089040c1d440a8040342c4000c10f43c104890754007050200069481c11305480a640c090131650107590b102c06004104402c041e001442c0c0350030184540c901708078035900d07402d40007018003482c0507a006010440c1c0109810a40003078500180c14001d05200c1d920603528456116a403600322142c907155004102d546010781801c2181e1600315000702e4407102e4243c02c14440c1d408000381e40c1642c43c108400601c0c0108010380900904a40243d07200000c1c0c1c0e1450030703400d05400741c07002034011038010701f404000070b0030008140007100c280c81d4407030f00319850003201210310001d44045100c042c500656032040c00700160740400c091484144100302074501c5103000181100d68100307203059041404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 284478767 1250 284477517 284477521
    0x70905060603060d050c030f0309012003041e0305010c05041a0a02061605041a03060312030106020a080918130b0a0603020306040f14030a03060306050c040e04020d060b100306030c0e 80
    0x250301c0d8416603920036002c1d1105101895a03041c400d01c0c000c1c1a008858041c096501d1014046801100030900d00001b030301c96400b440404005003807502c1034015041c4e50b07a0014002800074100d000780c80582420b5031310905200c591242c40c2c0b1400c460800c403014000c5a4006410007078245d450350121140b081e0313003402074100f0915000180d01c1e050000c1c5644040d02002c0000050b55000e04181c07000781c40b8002c0310300c0280c051700040b81c0340f9910942e013440c868400d88150b91000e60890701140d05864203580501075121260303982e42000d070809650207174042c00c004800803204402d42d00c0c081c800c0c4441c075810348080c00c10341020200000c0103010032400d98140310080c07005d0b8130f0019086801c60345c4288506880c4480303042840c040b42c41d0000b28980c074000040c90810302503040d0410300503030b07000e90ba082183e51a03800e00c1c0107982c8190320417002000c941ca400280545041304091103800d01440b0080b441ba0744203c0004d07810032705900f0180100356100740600920404240e1030000e07150040e1412514 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 284480017 1250 284478767 284478769
    0x6010b0403021c0813060206040c050a030312150504141503030c0307141c080907080c010c030e010c0b010f0806090a020603060913081303060c18090e010209091807090506 75
    0x14a010000001030f09a520800030400601c84101d038607121200c0344e00303041c031a100d400080d20b94001380c48c1030f580909102c001250718a031040030780046030381c503446517841240900402c1c0302900c0484415080140c80441c009095203890113450703109041c140b01c001070b914000118554182035804d009020358014840a036030084000708a520b4650000141c580c030750030840a16191079803541204500c03124502e05a141584c100c01210700a030348110559080710344808415603140034900384140000c040710f05400c01b03e40aa494110131707400616007022281d155854442c0c0404082c0e2110500000380e000810080d40f05100003030308080e0080203001410070380c0d0002201408003402c00c40c030a121850103e460380c2d01c081c2d9134038080c2e5806038080e502c404050b20441840c15140c4020703980703241080c1c00e00c11028031446040d4514407034150b141039100d0a2108040c000c0c080c11601a0700c039913003004401034640d20400d0365441174200d1000c805840c00744030045c0e4280411a400b0328038803030600c8140042 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 284481267 1250 284480017 284480029
    0x81e0309010c08040801021318140c07024023061206090a0b07020d02060a050c13030f030e03030a0c02101b030201050a0501050a030b0412031d03030906010b040302 72
    0x80e4a000b440c0070002c49841e4140380049115030f0b03003c5000d940c80007a920100e0565190f040302100c0d0400d10005920704c81080c850144c468182c001074035040c9160001d00100b844001030400709002a0901d1002d1200c64804100247d030520b0803012050705010a04c1c150040030031381d0035003004072401031100d0340440b0204518203900c0307040c20000c85400d0b0009000c0b40c4800c11030500d855050000c4a0141c01c06010007519094042001c1c0d0702e03031160303d00059869000044004054070aa030060405965501c000001420080e000c01403450040203210704c402802044040075500034184103902d040300e41786c00750080380b140c100780b40660018031100a10302d80280c000426030341c0540300c0c001483c0e6010300c100c1c1c45606000c01503094012040710b500905505611a80c4200102c620400090f41c8138000c2001648071031000422045100d8005400100e01603001b040c6044a400c000c206121001c600c80b030010710700b40102e2550750021042040c40c9901f00b04c03241c01404080102c41c540750031500448e41d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 284482517 1250 284481267 284481277
    0x40b220b0c030a11030712061203080610111e06010f081009170706020c011409100e07030206040605070302070e040f0822150806040209010504030f1401050709081e03 73
    0x40c81c601c0110005091402c01d420040c220005581c4580e56458001800707001c112800300354896943c0343c00350116541411075000c00409401d0b8844112541e038035010040543c0021090031708024003104015144002042801c0106104042554010008220851070f0060503845110719001d2004100304240010803103215100c0c0c85000407a80e028982803034503030b1401d42e000f00019608001410014400c00342d001c1c0961559a400070f00004906225103c80303c80151030b0340505400414080f400c040c0342da07001d000085603050580b402c0c0c0e9980c0e000142540c000d9441030300426000034000d030816a0500060005e0f010b080009446410700381c40f031103100440100c00409800b80025072500f002c50584640780c0340c0c0711b4810490034454544d4100b810001c400318115000c030368200042103261400e0b000795260400181d6030103080528545420008400c1400700340c2d0b2400d500381c60030400503070a0040600c1928152694001c0038a40018107240001c00305103000ca80c0303112f0700c12601440001c17080350 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 284483767 1250 284482517 284482531
    0x19110108040303230603150103030f1206090903020307210f050325030c021006030f0f290103030908030a200f070905060f01090e070c0f0209040b220b 66
    0x1903020740c0ca40c60140c00402c50310205803c1d00f008280c0c043d02107150400c0e00c501c96a03095098600d10031101907000f99452080c00000c1c0490300018912065512461554041542e031401c04681c199480102008640251006a0041e000060340209100717400b01003981e0202c182540b100b180010301002881c144541c43c104040103000000301d024030200c01d05c0d90b4a81c00580c40e4030340f041081a040900140364013010b05000d030055640d80c103200001c52003003000b2a5040140e000040d5813650315110041074010088030128601c00f49002c0059032000994200500c0c040e00c10a2941541009000c00000d540080c0b9640d000700404183c0941c0001242c14001d210101d403c851605c4406640c10132840a120032258811000300050000c80c907000f450060384103403030740c4004980a4004490f1052240107030400700d5502d102203072900e0b100d001074a0145000f400b0a44d980d425981c00035428000a030307815035200a000c420b005072440d464800c1a003101a40508461281c9030395140b8180040c020306903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 284485017 1250 284483767 284483777
    0x807170a020706140417100c0f0503160203040b130311041b0309060605030307150506100f0c0809130b090a1b23030705040801060b04140d1104020c030c191101 70
    0x44c1542001d00c019603019040030b4110385100002056141d03698102c4400c80c1c4406400c0109108425008102c4e01c00c0040183da900c0d49550b171405544040d00c4840f140080071444104800202e149495001d40144a80040058010361550400e014981036000c81548034520701019021700c9010300d17062042130b01c26418040303000703440e0713007007600090540360701164140c0400103120041150b014010420805c801400300496141e10301401200d801c00c1048001040850625840444c0100c60030100203100d050840c0c1740400c80408124030f52291002202119101c030056007841c68804600b5500c200803140400101c013a0408403044084281d400d2410302080062021b01103000625054481e41103d04940c1d690030000790060982e4090b00c20b502c00c0303501c1c0031004914010080c0880301240c2841c0340340c4074480022010031451000c0d8a804860320080044420381d0303a16680050010307848030300091512400e1900070313181806584547d510790310703840000d1980000c20306410409444402c2c03800d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 284486267 1250 284485017 284485037
    0x13031a0121020f0301021b0114040f020607080906040603021c090201140a091211030f07060c3503100b07080409181a01050a091a10020106120807170a020706 69
    0x2c2400022105983c2e0b42550001401000e42400780032410285030050008008851560101244403e82524000d1640c00d6902c81d80000d03181c0071000c0d1070000e010f40401c87c070307050040001130002c1d80264003440200c0d401046400d0b0030080f61141e1114008d0109007448510305603030008007039910300f81c07035111710310804141106103038482c1c1f200c400900151603c1c0e4031400603508080d80001c4403848228468401c41429000c0c880000c14810308480294440701710a081e20327581c034500000700c0b01e022284001680380c1020714411102070110340203900c5003080d540b400c10360f103a401c850b1081e400031032841008000040010f0031090844049a0081c00e00150359460716aa0101071540c5480150070090700d00c480c10a5100340e010120f0486204079250503405584848160030740e09410f641d01544d0581034000285401d0820b88040500380a00c00007543c19160704002c000341c0f2840c0c000340e031484808103504007005002e05a8980701a84890b125045c200501c000035650300603401210704000203040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 284487517 1250 284486267 284486269
    0x1401030b2419051c060b0a06020a0206090103140f0a1a060f07030c3f02030714100e07080c19090902040f1e0f0c020c011404080313031a012102 63
    0x1c0b082c0035040c020004440d02c2440700c00c84010782007009058840c24a806d42c0e8201500d01002c4100031211035402070941081e184d000c020f000d403c000181c5043c1030700c03041c00f10203032010400014404c50390201042030700d080400000c421580c41002100c03199501d4504c05500d5600c143c10b445a94a0300d6824903a9404a40380c101d51021000000810211040c0401202c1e00d20306031603501c41d100800074a898445400c0030304c034402d640310080400560800c10403440420414016030031460b00c4901111040382c2004d4080c3c08489005071860810340042c281413090810034080b43c0d06801040f2405000b44484515880040c1401e105a031a80d580d2500807030304649642e0003002b52409602800c0055007520302c8000c116019064042c101c4500c0c01440442501c40c6104040b08a403007503004140c1281100c0046d0750554460036001c81d14202808002424842080180800015111b600700050302e58501280a04180440e003503c203c844001440b07120340c0b80c801c588d810401c201c40c40c0e8405121740 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 284488767 1250 284487517 284487559
    0xc3106061b08040b04080a110102010203010e27101d03040302011e020a08181306030c0b0a11060112050f0102030108120f072a08010b0603041407091401030b24 70
    0x136010400d4020082000940d8178404070344401568051043c000e200f05480d4012800c0348004d02441c04188495808a01040c4803254611800d50200610304a00020007400701e01d46800c04103441120341e110544d10925046110020124001c07210055041c181540c4c0080e01905401c0000c034111031025901d1302d030310381c820801100c400e5040318240e981c400d240503504000c000c00b801c0c03150003160141da00400840081c03042c00110b130b400401034102c140c1041c082c0c400550010710305c4000c0090003894015542018000705008203449032103c4210340e640d2800d1400c20390604601c00c410392046c401045800004a0800070b2508028060340e0369100c8410113841c03500421a0103001095041c0510140447c2161120f040c3c4918810110600366244d890ba0700780d402121565800900c14404540002c003420304820100c4140c3d405c0c0d03106180c8032103a46d0102d44180800b00100d100c208010000d1101e00102c0c40e8000040150301c840b164807403000300034032181040a09d40500c2c441390104072801494 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 284490017 1250 284488767 284488769
    0xe03040e06101e0504030b07020a02010c121205010b070204060e10031b18060e130c12030c0503030408030a0f0b01230d1118040912030e0c3106061b0804 67
    0x310320b140388580e40f4400010450341080c081104c045c2c454102007100c0a00000d00d0300d4078103505940e8500402001e9958003910a040000802440710311554003030015201d025a60113826220b0b4426210b4410340100800d40e10356902170000e21281d5018010713248810030400d410350303400100300c95031001c204003521240106c9903c40017030b0b8500344038070f2407210250380c00202c1140d440320b4020400e516600c1c0903401242e40c802009050b9004040e0801c50070810281c01c42c1c030280282800b02c10001030340c4506055900403141200d0200d00002040b80b640c40501c61007050b00c01d0401c0410100c0c56010000e04208045c01c0e0000c54810b0071540390000304034400440b07140f409250300030322000c1034040c2141c0e11a0000211004c511000903082d80d980e04180c4107600c1020b4012400c2d440000600c901540100300d2100628014040c0c2421400c0c5a21100400380c40740c05904415850f0071030300245942000ba428501034600c40c1030010810002e0b50001c1d100e2412000e04c501d00c1342e0b5950901c0c10340028030171 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 284491267 1250 284490017 284490047
    0x50403060216150504030305150d110301060503030a051306170708041407060306050102070902130e151f08060d050303060f0102070e040302060f0c03090307060902030c0411030105040e03040e0610 86
    0xf07070f801151888500340c020a008601c00e8500340495200c0c4548000c1c00b102907407d99410510846100021594481d10115000400303400042d41e644c8400101e41168005540b84012071000602c079503403045464884d41c01440c1e2440c0a601e00b0145104880306010041d00100800034200b021809200d0008001000c0c800e440f0b049400740b681c2c0394805005800144075040c0135004017440000d44107100d0003101c0082c1030301041c100d910380c10b00645d0101c00c3c90181419018005600035558540c03a149200162038100b0b807990100310a894000800c01e400051590740100003d210000c00210300000307890b0080801c0322000303980e40c3c1d0703000103d02d080b45c0b680c4054100d15002c0300384000e00da000b28503180a10003244c40151103540d40b00d60400c5910058a100c40103510400000c408a6020b521200c1c1684c4001c00b039400c00808400006c003512000d56140122110010040065240601c41d13541c800c41024080d606240c60702d140703987d610000034400e5006181d64142c80c040030344070302c42014100300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 284492517 1250 284491267 284491283
    0x3070f050f0d1b09050102010203090d030c0203070506010e1014030705060d020702031f39030e06090d030b0312030a0207020406030f050307050d0375050403060216 72
    0x48049103070309001c4070f111030700011800d44600810194818002c03688103074450802080c5032003080004038000d2107401c9050086000900440700041e1051103035500a20350380000c56001d0a010503038965000c1c0d140d00c0500ea070150705950038540c0e03c0205074901220707011181a902c40e40c2240a41c8060310030404000c0d49802504240c82020294a044540b045212241001988039aa100a02144e070072403d403110034500000f40c000094401c08403654200c01803401003000107144042a1a04105071020441c5803c08082d286983c0d5151281c059040740440003004001e180c01c0d141e031039078400604a2100ba0381c000130414290345940c0c0180d0000c40d0f0059100100784010300b40f0030380301c0c2c0012504803150b010701206004024400d0041140c000e20a0520f440181c0e03000600e01c4c2030b2403000c04130152400f81d104104034180c0c11500c0c902c0301081c120902c00b09503107a1700ea83c40c4800c4024194003003255201103514407100d40c800143e60270360350301010042e6606807624802c00c80c03a9081000070003400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 284493767 1250 284492517 284492531
    0x2300406020102070605100b03360d0f180504020915040807090f0606050415090e10090e01020a141309050c0705060f010302130f0e06010e160503070f050f0d 69
    0x240c1c158001d00b0714074021441088107440e55160300c4401d0065210703150320309205001041c01c038900b070f941000e00e5403200701c9941c0080d001040c008507800c1504175013803c580c00c00c188005070a50030504000d200c4100f850019480c0c210074410727218040070b602866015a501190003142501e070040c0c2664081c40c51300345103854a40d03410456035110250b0188007a00ea040c105005d6a500b4a40a84415281c02d07803100e5003010f0509020090f1081030720102400c114240313100042c090307004200d9a0180744036161520405c4d00300032100b42520410703041c81c0410383c0304100402100794400382501a0740040400ca80c1c2d62501b401701c00000e680d07141c001900041c58801400540d4110000410b90b091044060b11a143c0d280400d0700c464420900c400780d0890140c049409500d00780750b00010f080e083c039a40006400b494842080d113401400d03005040c41c04100414084042102ca5103c0308802c3d403071406924514040d4001401c01e182c0d01c202d542440000310707102c82911890001d80311a000030907000c00041d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 284495017 1250 284493767 284493779
    0x3091109180f0c0a2106060905090c030313050108100e10060906051306030b0607060203190b0a03080405060d020f0c1b0a030c050913020310020702190303023004 71
    0x42105112074880c03441038a4401500e518080f03400c080ea0b40c802081941d246203001241c01c810154509000301c000f5a2126101c0002ea2600c2503002410030450005164a8141805464640d146645600c2030344144029000c40e443c084007480ac4da2703000e1030400255140d00d96101440010f94101c1c1004040d9801000440141603c9020072103405a6a6404050769150259203d1040044800e81d0350050f82080c49894060b8129400100c00030b40520310b0281191500401c030b07007042d200300d4030100c0140c610088c501494054405485821501026858a56650003100e4410352085a01505c40410910580740b2203505445848902101055865400014068503481800400d042e8603130241c3c82c140c4541800c0b8100f00130359503c4100022003030300b401c08120031642c0040c01d010420700318041540050710207104060741070031415000341c1c0700c0c191481003001c1101e01550041c80140c142400304040303640015480e001c0b11003c0b000300120154000044680031304031001202080c0000350000b45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 284496267 1250 284495017 284495041
    0x30a0309020a0501111509120f0912010506030d0305101a120906010b0d2012010311100c1202010615110120090907020a0b04060605030114090d03091109 67
    0x1030314801c0301d12100c2c039600c40b00150349034001d070503685911754024200448142c100004143e0081000d904071820b088000070741d10740c1c0c0d1b40840f400001d480404143d20030036007020703007581c18035860710f20080c042480c0c06000300c2d079500c41030641c0c4000c1507141e4011500e02501040c4c10f03409041d44010704041400c0482d130140a40c4e0100b808010300440c510001030082c00042800b40c16160f41c0840c452401040c07801140181800040e070480320208008000d5014043c0c00040c01020b020076000503207903245080c0314500b81c80f4002c1181c010040019140740c0b6561107111401c4095111a00d9501c0982c42d10041b801003030740c0d0300000c804403070302d051b403286490f00514100500013481e00280f00d40c1d030704081c2245018083c610400c420030024030640b9420b18101210030360001e00da10440e8190b07106611407000340384040d6003c0d40c009a80f20001d025504080c00b650b40d83c0c1e0110b0400700d40340d09140307451325075a0361122501020541c1d00c10307a0b4010040c05121403244480010500955030420002200e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 284497517 1250 284496267 284496281
    0xf080c060a0501051e01230d1404020111070305060a0e030c0105010806060a0909080910021c12060915090b0102070306090c05010906140a080a0e0f0109060606050708041202060903030a03 82
    0x32042c403090b450f401034800f5400e0040500181a9544da04403041c03190003441d0301d2001038040c600f010040c0148e52610510b4031501600804000c14001c080c149400050402e00003140d51001e80d8201050601c04108005410768006240c40c2c80010140c400c43c000702d0441c059803925514550030302c0300009014100045881c0100402c0f5400c842e01684c561b804000c0302e80903500106150303002e000b0300c050751405103000300c6600907a0040d250712420b40007400700304100500307070180420b100c0c0a01d800311023414402d880103080308001c02c110341c460080002841000e1445a04902910760f076082c7e180e40d10031b10081c4002e40d8400c60500c141049445d100c44510050300030180028812130002a0907403041b9112012003501802551800c01500c000f1100300300300038400195542c5030083c2c1c0e00318140c02c00101103648402000054581c0140ca4240c055401740d91003031040100522400010968071000c48089440681010070b0781110351005c00c525004903103a00f581800003040d004807198240d00850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 284498767 1250 284497517 284497519
    0x13050603151009090f021201090209030c030d0c0611030601020c0d06020d06180f020306011b030318060218270613060e0106170c070b13080d140a020f03040f080c060a050105 76
    0x1219030105d808044d0120302074a50847c0900039007500402441601c0e9008040c01100030382507924401094000c01d1610500314075090008107010b0507903081c0038541c030500034881070b4015024076608107900002e6844140e42581c510a131504403010041010a5044423150b41c00c1d41c03c103021840e640c08403007040c041c180d11604091030070545070320030843ca2442102d02c60754058489401c1003065003442445a09040c070110305041e540c0154588182d01d4083c5031161601c41c49016039a90400000c42444a0411800e5802996076202c9609070415404e20350740d8140350403600d02080d035500c00001c2c014041c0d2440580084c0e15018010600e10400e1103102e040c0d450948520010754250506c01041e001d0841d1030600004007404284001004007011541210314104800c1c0000c4443e281d141343c0703501c01c20800c0840daa8480000c204040c41584156000402034400c42c10030300841c5540c80c1500c8020700041c20001d03280142c408000c014030a542090201c1403c48056217002032800005040a011706 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 284500017 1250 284498767 284498771
    0x130e010927020303040b070c0306050112060b01020d020d03020c070905180f07230111121902070b0d0b150a210504050a02120a050a0506040b010b1305060315100909 72
    0x20940280c810700014049a07025000b5440d2510b072907481c451641000c88201c07140050304e030300000450443c4c05004d02030142015600380d20503081c5445c5082360302f00f03401d1506540100503000c04841d00480c0da0840d90800e070401580c0c0f101c0d0303801c1d401c0c1868416000700c940c081c0f42c031051004040c10200103aa8007561002191600b10848042da44c0e60b01340c510540d40c030000c510a540c0000521a016102380d1031040c181101c1c00103c0c1c020072410020041d2240c419100c0c04125207807030740380e46c888150b0703146014000303010303450704015a60700d0038416812601245a1a00249602615a85c03411320b500b21421400546507d0000030041c05030145103096a803002c019007102e802c48003d0b12134180a9940080100a14100c0d42d0038414881684100c100700ca0044d07030064408201e00388007190049115002030402d038036191130495040c80f4181c1110550440038022040c0c912051640c40c2c095600c00c80d0000d03265501d00c1417407036418a68100b070940012000d6000c9030069040381c15082507411540741 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 284501267 1250 284500017 284500061
    0x1c08030103020a0b040f030305070c030209150306070f02120c0c09160e0105161203022a06091203010303030905070b0403052b020c0123120703141308130e0109 70
    0x499560b0b40217900490400c00e540850402c0001e00590081182502c145941c03040340ea925000030f400c1001c00c84111442e2024a41404a280f07014080320303620041c68209050401c4c051074009584880780703003c4400b8a600064242c82056003008000b03030351400100410443d1404600d03192409400c82244804144142940b4200358001d03010380c1c032050282c0341d0f60b94444070340f500e480702d6800170346202000307041d801c00110b03081284e0808d00c3c00d80c845200300e50307140e20410700701601e14241d8001c2402080e5000011381304c00b006003444c00c80341100d400d0b280104660505041003410121142c0c04040c490340000343c0002040408203113072070f0740d40c034900403400040c181c0000b604440b6602c52103c8016004000101850340c02022060850b44182102450280b20091030000550141a0100d942030b00c500800810316814006d4000ca1a4a1003401005042c1424405a29400500001c0c01482c0c0400c405090300b010150000091040b03040d40c00c011f59561990078024251100c210600304c1c80294 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 284502517 1250 284501267 284501279
    0x313060c140f031902030903090102070801060b040e070219060c201c030219051306050903150606090d20030f060c0c030d020d0203012102100e1c08030103020a 70
    0x6229114491541d1510b1422000300302420842d4402000d990421028400080d2105070a102651042c1040c00081d5070f102c88140c0007a00d4980760354840302c00c980c1041c2040c404240c20030152000c44200781880d00b501d4644080a0b401c0903403600700040c0c00707984002c40e90184034040d00f01172a1039a8586506200c520f201e0340500320307150713400c1c1c111009901801510300814242c208010385090303a8680142000c1d08009042442d000c107640035000100045001061003140200703d200a01c25414482d01d03005006003c0f0703446640d0000100c00c00c00d21400003c525485000c1140c6c1441c0d170091500404400e80d103005550301e40c1c00d0f01061842400026685440d00700043c0c00d0f07101800000c020000355555185010003940500005004ca001c2030060100900050001c0c01c40048400000368496040c0b22182070f003403400c04101701c001c501c3e80a105d000b503254142c010341c00d8003192624110b6044041c02103005030312522024500001d80441c080c06102d21400954107803442220f1440ba0380d0398602d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 284503767 1250 284502517 284502527
    0x1508060712061202011707090e160807080103030e0904110603040606090c2610081606030b061c0b010509030f0714010908071502070b0d090302010c14040618030203030313060c 77
    0x403c000380800c1d060714032442004244884a58080a076260065002c1d03102c4090842121041c0c034183c1889843c051001c2102c0c0c1c0002e1855400b903240c2c9010411589540c50003442c042d80c440089000750140004a428007501903162504048040c00c03407580d03820b19207090b000421052045803200d500d00004a1007051165002c0c4941d6200b058194807a200505021203000300050000c820f030180b08800003070b0b0008140490742050500f075082c024210f00e001c00203001da5a001e03803483c0c031030030701001034034201802e506c80c0300035041301c0c2d140000b0140340c2940103860601c51001581d5040c881d140d1154004800080d801e4143c3d0117107d0300c80000c00808006451140f00d0340150300c4150030181081c00380710403030780401c0303140740c80c500c100c819041c2d944240c600654810030303848420507114407050041c140c0900541c80b01600a02e042c0718400b4100b41720006070300031801140e081180c08980c10391280c510350075141c003954005003070300ea5174100041520356080a41d8404c40e9214200f442c0107182d02c0c021 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 284505017 1250 284503767 284503799
    0x40803070309050a0f231c06050f070f1b14010e1504021809010906050412020c0a061e120e010903080121150912210e0a06150806071206 60
    0x141500140c0e410041c08030700c21054142d50351a04c1d03003103007111111030703030f521801801c1c0c7d100c1001345683e5041c05042030810f588005100c040010700c84000c0c4134106500502c0303204455842c0c0b4000e004082c1d44811402c8206103004043e100100e0220030002040c03040d800000345002d4402280e5614401140c030040501007102c0c080c2d8080402e110302d40d400d200b0740302d025074001214000050700340d8543d90b41d05c00b250000d42d4141c8a03240e41010080004e0380410440c130b980c49080b203021080350300e0840020300111000c041e4081031081852503080b20b40c02050100050150943d0900800068000c0c250003025072030b800354006031080000113588450b130b9007000301480042c3d2146514021a4803000f042090000007a00915610342090010540c44008040c1d0a2080d581e0412249984900c1076060500a5680211940340a000c01c00c020000a1000a039591045000c1521500c005801103180213940c401c070001d0188100700500c40e43d100c1e411600c40404442e0400c5003a8982584000d00004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 284506267 1250 284505017 284505029
    0x1209080c01021b1002070b0f040e010e06090a0c05070c0312080c16060507050c0607030504060f0218210303010909030909050405030d050604060b0a0305040c1508010308030a0f02040803070309050a 86
    0x801c012400550404e40240f4100028a004442407159100d81c0d0310081e40c414010021039080c00302e41840f01c070f001e2111450042c50100440003050815170001920000c01410381e41d050380d0f82d1400aa2190b000e241500c2d031085e0001c94441031940e0b24100f013504a50707504241c100145005c000201183d051000303441c02600d2603004642000c00e251751f040001d203405810001030160a20108a007603404101243c89100143ea003c6003a04103803070444107943c405103002c0500d40c0188440e0360951068903006050400880b000100d400440c1c03501200e0b15414850303008240030000000ca03021000d07400036804240700f581ea2b800c00603660040b03402142e1040d10002c103507800410101c0280e040c0d80d040190000340003800010060350350031030108254440c800c600080381c1c5400411081c002300f02a1040104200c02015501046403200103001074414040285803810120200300f00643c55409050901c078042800c41d0758945600e02c09680750090401240002c0481e403000c155410a44008812680 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 284507517 1250 284506267 284506303
    0xc0609240415061802090307061d06093c0303030408090904020a050a180b06040807051009150c051c0e0607020d052415100e0d1209080c0102 62
    0x4a903078840340e401c00d2450402c08501d4452001180724248004600d940341c000880059455082500f81402c2c41c1150b44440c0901c03030321500101c0e040d50b83c145803003040c00e01120082e03512200b12000682050005800d00d600900e110464404500042c2c284000814026003a902d044030b101c04050b540e22089030014280305041c4100340c0306090058145400904c001e0140004a8440740482c44106543c0d02c00500941c003c440301c2400d240901c1035051038101651030307a1a041c02d0a400075902e0903940315260140b08005515581749206400c1040a85844586d148071200140300c0104200c0001c482560749e801580c40300740e4642e0f24407034854400caa0340c0e00c030a130600980d8020800203401021060380c001405019503000600140601030b0760884458503a00280c5000406003481c0d24001d100742403517002002e1440d42552645016120003016250181c00a10007001082e007001d1005001403c0a0001460304906504030f0700314416a00c04004996030310280300f00490390b8202d00345440542c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 284508767 1250 284507517 284507521
    0x40e1b1306030803043c031e0305010f050d0c0b0304170c0304051c03020a110111060109020403230c0402030c0913050403020c030a02060d020d15090c020709060302090a0e0c060c060924 81
    0x103002c0c12106d6030300d4080e003050396031402403851020310944034400840009a59a0041c403a9401c6080c1003030140600355160320344440c071039480b03170440a0240116100d810300400050201325101600d45920304030700c00b003940c83c2c0018841031917a030f810501803203101c3c1c0c2c1040340c844113a00c3c10340340c0241d02941650090480c0000c41d250b10f00324200d01c040c0c8034104442c44586a41c080400c2240c5c0d170082400f550300680d80c40c694100043e084941c4c0e269801c9001c4400c1d4450240840020010003500b412100103070780e034a4500d0710f02058031651003040e80020890121007200742c002d43c0118822070080e001d0b10071015100040548942c14102c0003980040140b1000d24410100c0d40501070a0040e4840010103450354101080f1281d0b142c0d00000402d078488502048103981480840002e00d60070344140308860640c5d00180611400802c0101d40c00c1d912070781c0c0350082c941009441c000c064080c00301640c855010080c02d85034a000c4951241500c100d4a0300358180702c2e000c25811503008114460340c040d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 284510017 1250 284508767 284508863
    0x10e0108091c141204050c0103290d1208060a050a051309020a0e010305070305010e0102030721060b0301140405250810081504060b040e1b130603080304 67
    0x500842801e4000c0090100c0403e19102c25040240540001d902000c1d10707034a464030b001481c2245007107001d8105828161039810300d0340307004c0030200e400303140001d424041e03400e050100381d0040e8841030141c00d0070b80f604950050541c2141000703001e86410743c3c1c540c01c080d40f90340620070170540c0c5100c0c00d0b4010441c0b0002d00c0085c42140c2c00f0340e4149200800311001e095440d000442d182c1820780040d0b829400c40c0703d080003082024810b0381c00c0361001308c3c0254250716107940050501c0c00744420383c400c0d0706005401d84551010503801403010b00101221b10f622541c49400d191018200080300c50b00079485c080210368000003c41203000280304440010302940c40b40e950071507480c0f00191800400c004516000304500c0e0052140803150982c1014600d070750304d80f9040080030380d0b91404100340284e24103884007490309004282e40540f130301c0f0340c108024201403030b0020940e4003082c03030240c00b034441c0390520110410040c0402180a07900032240321607d00e030401c4e140a40703a4001e400d0220f0b400700b180415540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 284511267 1250 284510017 284510053
    0x503040b16150b19060915020a0b0108010203070201060b070c03031b0605010e0a0c080601020604060507171003060b09101a28260c03090a02031209010e010809 70
    0x40d04072801064551003295503540800002d5060035902020f8445000c960310341000d50340404085980e0b10b14084003450004042c2c03800c02a8006c10341440095204507880900800c07284c5285544004151000d41e507602015000350000d170ac804005509080c8002200d800e50000d0741d0000781c0051140c010989150313016109010104c2c0401c1c0c40025034003a40340465510300c00c5a0090500076010295031420f0a520000c45000111050500110106101a03646c0c000303110742d402a40f1500001d03181d200c0c25010380300318030700c82108207a00c94803404101c03040000981c00e03c00c8034030500050000e41000c2d130400c01204822500700c0c80c45084000c3c200040480e9241410340e1044c01c40c0c4007031070800c014246002030040c41c00c1c0c016907500d64100800c0e229074040c60565011020350f41c0901c2640c0034000b0040304020240c0041c840d640084041042c1034010300c107003070b61581c0c0102210311028a60403480b0307503034101240080c00b00340b59484a40183d401070440f03d104030040e10140814051705195000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 284512517 1250 284511267 284511277
    0xf21020a24110a020309090c0703022d190606080106050112021e04090203040c06021b010305090c1f02060a0c0c1506030605091005011703120c0f030109050f090a0503040b 75
    0x40c06503142d282c2440c8880003040184184409680616600e80081d010b0002030100a0f003110703890541001041c0120f9804510000d09882040c2d440032080c0c81c80c000c00d0407001c03100d14502c4242c0109600c02c181041c1301c0b952425001d03c250414444146d07640e541030300322200303846401d001c601401d001511801c00c0381c1c005c141c0c10401d280c0ca8146880021002d40140e002500100342e00d0342c0c00024030003400a81e40040700204403510081540c0c1e8080e0003210307401828807044a0501d03441b24003113500104103011203440403c0c0075101c6041c1444000c05134106009240011016008070350118140d844a405050389258183e00c4042080c0c0c240c0c0e6070803d501c8034903c66221141e56450011002440750301540b80105032100080403000050341700340c4115030f01a030000a0010a000c0c2c228624072010060f91002101035500100d140c0d525a5403e08a2042d0b82c2856640e81c0000008143c161055201c0e074080c09001c2c2504180d40d99200860b80c0c1d4481d4a14080c1c11540180002c228075800440184 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 284513767 1250 284512517 284512583
    0x115060f2006240409110607060b0603090328051c02090d1b06080609010302061309090501140105030f1507020a051005041e080306060906070f21020a 66
    0xa4000d1100070315081030001e40c3c0c0e41007a044030301c1d0140c0b03940e9114400c811082204841c01c11060000c0e60700e913650a40795140440c055000400c00c00180001c5500450042201802c0f507542c07881c00700301d000c0d202e6124003401c24410900c800c142011030703215542c000e09801241c48061078401e50440107a52400c80b82405210540c00308108204c588842d01c1e44401c2074420003d1107012518000001019143e9030000d508120207001008000da40701d25400d81101c3d0140c540c6030751002c2940d0303181c1c0020081e0b0490400d10341030031300220070030078154000000020400d203c1c001c0c590f256001c150300c5046c80307004508070768043c40ca0008645c41a07484c00390488114011581d86102030307a034080c18520309980f01e0f0f4802e95114100800d1241d107070400c102a150b0f4450769101c0400c1c907036810701c25000241c516802a400800d00000031b4440c04200c900054000e0306065003940d051030049602c00c4400310140e10583c4143c09103000720700010b116490684d01180c802c4d00030101d81d00d00d044040da6050340d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 284515017 1250 284513767 284513807
    0x50a05090d09060528020715020f0a0206160b01061d1e010828050901050a020304050d0f02010906020f0a0f020102031027060806090f0318040207060e030315030115060f 74
    0x1170014007901c05012101403156801610105280c0400142600e21000c0c442c0c0540d0031801c0a00340703035400840e80c0072040f0390443d1000c0e11030405ca091415001130130800280404002c500206180740c010f103541e0030301e42c68551601d482c12828418000b60407001e131101c00d40080848000d0720250300600c04140d00c03e6404801c0c040440c44205190303400c0040c41441030165a48105221600e4070a00071b055205402c0c2c01300350305c1c2d41005d03039605603030340340c0c0c41407460410010000e9003014501c04e4002103440c07a0401002e40d162103202d0f80c00d105641c411003980c00862042058078100a0060003500d214005107240012030b035241400e21000c1049010000800d15075a0740501c0141050344103450140290304020011131425a150500c3c10704211150b400603402032007080503140001007072414404003901c0250300c0b04400c2c070303040b03020f481d4070104009103000200030040000c41c0c4007403113080b0010071002404001c0105140a40414003401907000085440108883d414002d032140c1103004006598 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 284516267 1250 284515017 284515057
    0x50702090604050a0e07150305160c030503040303060807090b011106060901090902030a0203030a0201090311060c0307110a02040e030903120f0403170c070e0103020f010203180f0d0c0306050a05090d090605 90
    0x50142072401b06d42200c102e5003c2007402075080c1b41e06100b927507840300710003640300e4400c169030301e01411030740690342c0c0141000300004c002000c1600c00d80004004107a01c0007203441590300c8150342c1c0040d0862a10700e42c00105081e0f2002e0b0400c5001901c02c0c01041d0141c001e880507401e1a01c0d59029051045081e60184540906000141c40800003032048030410390000038000070ad442e00030041e2003c18020b1744190302031800d0000300c0028004480d041b1a441c1032074031a800540e800c0f5810048181c601035802843d01050880e540d402100419440b84120f0680724032513910011010359025030080140d031050240424000254203030190403140307206842050901808101e110b10323102440d001050b1802441c00104110704000c0c51402280000740082c500308102c0340c2840c0c45008013524680c4c4658500380760b940180d101e110380c0c042d070243c12034141c4e02000c0d12030404001420003501c1c203000da1407a100000e410b590001c1801c03c00d0804640d2146c46087c603012007254560800441d030055180300c140d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 284517517 1250 284516267 284516291
    0x90512030c0303100e06120c09100b16060c0c230a020a08010606080106050a022d0a080306131401061d100c02030606060309070b07080c0f0f0706050702090604050a 72
    0x182d4800c000201c21210001e060043c40d00b44610054a050b02a41c42c048000d4500711020400380210601910340e070040d9941d0f100e9a03030758162992f20925840f00000307011041c441c1c0461909641038001d20050101907460a000c8441c04d1055001805a07503881c0840761810324050381614103200c44030100e40c613103503071500040c200c61080d03800726800741c0d50381d5810841290020040f0f4010201410700711304003420b0b1b0354040c1d01c81d02081401e0607008902d00c2308030303d03403062669821074412a80f02117030340c200c10504c0c0403045c56006441d401e205044140c1801c0e103e41c45800b913107062403240c11070410564640441616003002c40c154800300033101c01c0c021411902d606081e462421780d00c2d918401900d015006244c00c114011344418001d01c010403c124940500150300c9003102c0700c08205640d24801400c0c2030045009100f448402030151052884010700005807041d40c80c4d51300801e60703011559800b01a1460700c11040000d400940400c001859407074654030440d07102e05408000300d482c102c040c07 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 284518767 1250 284517517 284517523
    0x612020d0e0d11010b060d0209011707020d0e0904080f13090c091d012304091506050924010503150a03030f031a0307090b06041a030403030e0c01090512030c 69
    0x220300000070380c4080031845210ba48041240303e07021101d002000800f5040c40402c0e1107102c4c10b114205403a03000501d443c3e040c2d21406101032402c1010520018505007a04020340780e002100c0e245000540c00c6055a01603d0240034031030040d039003d1202440d201299803480b501d0b802c148049034003c9001c40c40015201c82d64002c0c2060020160f65401c0038604061032040318030000410802c1d1104140c2c0141f01500810754411130300030300c0d06d64420601c06200c0005018008180d4010200c00244207518914503e607000041500c6048409043c41c0d03a03440d0780d554401c19000f03094408032460311124051035000e00c0003150482010010911141e0012000c990a4102540200c000403502d9500e00800c5c7e038540f10305211003400e145420717013600c5a000040d5031205640034025503695120604821aa504000c50f00100030000825444c5231120b081c910168004680a0b40801d04242c9402007900340411080c1c10654140c50b14282a0b050000f801070708008500c4044140c0300801070440408010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 284520017 1250 284518767 284518781
    0x10051009080d0c1e034e02040b0d1401050108090a0201081509100f1205070302060d0e06011815060c030807050d0e0615060c03032d010e040b07020d05040612020d 71
    0x25250303181c043c98255115904255404181005145140340c006c4c0d1415401e15028000170041c3d00000300500140c14400c003d200ea40d01ca0705880381c000800055040003070700000040340344401d0107101a030f80d840040d80d42c10021180424180c02c0050500010341c02520450f4001d0380e25542c400903503159001060713a8120540b82100e0103210284208211a20550380c8009400321015180e8882a00d41d22140d41d0305403400000d103d40b00200e28071018802c140d02a07400b031100107045942950355034540c900d007808078240e0f081c50319051401240824a40034114030071500c140c0c0e07480d84003d2084d28219501c0401408010422800f000201521111805031428100346c0c00c0c00343c08030b400c187d444203180c40250059580a090180822081ca140200540e548aa41d0308220341c030000498141d58691200007240369698101c51001080b010209544288182c0c440c42198a0640b92000141e948a1649031200700241c02003200344202c911a03158003142e074401e2030b4007606040340716001c0001d90380c3e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 284521267 1250 284520017 284520023
    0x90207030c17091003020d060609081f0f020f22030206030705070203010b090a23040c15030e010c0f2c1507050f0a0c1a0711060d0510051009080d0c1e 66
    0x100d00d06011030400c2c4204c6008003200d0514038512032030035130200d031113161400904c440c202003aa50001d84803050337000200d00c1c8881c0002103603211300401005140d40c00c84004203e820010602d0407040c40e00c25008203040d2500188143c2c05d41c1e4071850103c80320740c80000e0407a050354a03169800f2998039a460f00d030f070003034055190200e000c40c071501080c1241d006004021811030000020700020415181b020816558901c248e00d1111106400c1170b0042c12082442507540e40c601854030f1400740d4400901100880d0959411141070199420a1800c1c445c0404090301080503207d04411454003000290b644a05008080d003081550707150b244c2019030b000001138080c0c108c02980010003074103410840203404112400f01502d00041c03001202e074050140700070445000208065055501d070f0003600ca1108440100380601e10313011110342210130301886241c0c0500302110103440480d010b12205406c0d144404003e010210082c070040b103280511031011768030303040c1d40b000e214602004602c0305103000d80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 284522517 1250 284521267 284521271
    0x130b04050d1202031005011103070c030b060a05120606060d0e011a09100f03030e060c16150905010822050601030506190614210106061206090207030c17091003 70
    0x1003101c2010b80704a800200000d0454810401c100801d0000c2541301c050340c00c28a443e0554945d0442c281f0b1940c810311501400c2d1801d10304000040100c2d0440c500d200300b500f900d1255056550304140004110141d0b288c9900b608a40005807060500c10090a04000100030108500d04c20f80b20150850b0329070a405000d0000100c540001070a05490090300b1003040342c4698001860603d0505c070044060100508020f0301610094460b50303110706070b81c0965181c0c4240e0341c105104081c0b142d0311038070620400c001c40c12006589608507019004c03010071a10107841d580d1495840d0017514000c003181c0034111041c604048500000f042c030410000740070310301c6607004101c107080003031050501540c4444420300e0907003082400c0c02031020105081d40b10231015500c0303015103510170728a076a2844560305100d40641ca80030000641a0740704803448000c1c0d1041310100180380d00da12020060340b00740100074010851200481c40042c80c1c551807003100010401c03055081141003800220501807030500680000c2e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 284523767 1250 284522517 284522533
    0x5091306080c010e06070b04020d021c0b010b03070e0f060d1103040b130804060f0306090515120f07050d050a0c0e01080c09061320070c0627090203130b0405 69
    0x100c002c01c11414042e070b003403c000140c40a10307400540340c1d100b0100c004101c0000440402c0464540207990404540d0007441c0801841c440c8040030380c01106058143c5442d0040e000005008400d0011240105070903030318458820300c114188540701c009540500d80024081182c03c4001e4102d11440c1d0a9101b6887c0c1c0d240e4070705050812041010018151040101c0130f20000030005a41074115021240a410156440200311205034010b002c036034484105a4103080c1081184000c80d0490384200030b00b01d46040350104e020380c4071580c54160100c0e1903c2f40d4400c603010b01084c60010500ca82e10b40c482c44c03c846080303555a603800231180d4198458220601c00c08018080098180f0040c038042c0c01c16920501c040c81c085001030286d01602409101c1d03143e80b0700c101d440e051310a50340c028003841c031420032a569810328a4501d02940715445520002540241e1002064035605400840101d10400191a8070700f0160240025840508410103078030380c0210100020b415610718a105600582c0030b401a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 284525017 1250 284523767 284523779
    0x904050c01080106030213140117010305100c0903020f0607081b2109010e0108090709020301151106460f0c02190b09010204080a1214071a0705091306 66
    0x40b01041e009502810b00500c4540c02804821640300c0858900300200c0b0203c8900c0c400681e0864281c04100d40844401000803041c000b0024450841008070036003042042c000842c2126881100e0100035407240d000c840031035243c03400d200079014007800b6070303069440c0465125403544007154482c4401855000030000c1c1c0000b44281c4003011500115000082c50079281000003003090310343c40e41c03245c14440d0031400700308400303010046180a864410b000315a207584070301c0ca8608000d07500305040001124442014080000407804601440746000b41c3c4090310001000c5c040c1d034044000484500d4000c01036080c24401407907a0070078000c12107440006805840d00b20140685e1b0360740d0400c0c01035500456401c00341c44086150780d08145c3d0083c2d00f02e107e54841d01e090a02a11030f0341d00c984424411030419205100091041c140400c00c17588444034440d403241a080000e002e4007001801c405150030003000403178000c0c0030041c0c2c0278240740750082c68030000d40d00081644091ba42209480c9548400034401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 284526267 1250 284525017 284525027
    0x10e070f030b06010908031e0c010c17090a0309090506041808090102060106030e10020f04030b071d2b030e0910080106050f0a181104031a1f05120a020904050c01 71
    0x7290f42803034101030741414429019524450012881c2040a549180b504010b07055030a5400360300754000240303c0c0d0650300b0801080e0725860350b009400c89a904001c00c0d0406070008151042030307030584801802d1880c04180c1001004000c0850f07800607142c0f004480c071a6036142010754824402c04c18191515a504002072030444142c1005003070615100c0e00800703810300010320090a032070202c4050307a0381c07010405c0c10307595004980c002404440c0b280c052100d078940001900059030341e01701c82500e00c13620a030100429004003c5900450320645141804846c4400b41e048a400d030080c2080e00e0880119008900801d10880d00d90011700d45030711040c0010700081c0980d400510040383c000d58a0f0707201a000074254603007481003000043c0e201c1c4090780b0420003074218501e028051210262901d039a030502401d4000c140f203480000108400002d560390b50314074000c5142c0340ea043c61040c1800c0c1030000b0302c920030b08102d846c600c56211b00c180d11b8005a990b02036440c0b040788030b08050000000100c0001d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 284527517 1250 284526267 284526271
    0xb090c0a030e161a040f060302071209150e03010b030604030806180f0a0c1707030207060b0102031611040e100603060c0f020a061805010905010e0c04020f07020d05010e070f030b 78
    0x36086030070440c429a030030031030f0389090301d003022140c203054410400403610b18456644044440b030404100060a1074240d8041c1141c540140350038151110201c8088400c0c5180e40501201c64112940701c00c00188603000340d101078035000d000012b62070803010010b4503040301101c0883c002414042041040d06200c9100b0081070024030260010b03003444010801e10343c6000b03189a6101d503403a594031007001c1c494007180d01e150b0710030205034045c0c2c00d10920090107940102030680c0c030346044c01809440d6510000441d06542900f080d00c0d00c244515070744411640070100c0c02198860b4980b480801580e00512100920341031080e4005801840c615065051f10021181a404d205040424800c1540c010800c0f60082c3d0344176000080c03113800c41030051070494000c90702600700e40c070740421001044415808005201e1a0404903030001441c0070400044c0e100b091b0b811251404207014003001801c02c00500e10a9a1154001041c50a0701032030480c500240d5610207600c00e400508100240407030282425 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 284528767 1250 284527517 284527541
    0x609020403020f06030403020c150304120f050d0f020c0d0c020a050102060c120417120f0a05010b070b0901020f070506011719110a0503070b040906080d08040b0403030b090c0a03 78
    0x94100341c0365800255a200c0859803541c00b802e80000010101882404803400320034004040e0550522001c0e101b8030550002c96040b1000c000c0c404010038564090600c0111626107543c03014a06915280c2c0d0401800c0e5014076a01c40580a1116801c03000c41400032580584a0303030f50300c0818144900400c103c5032050340c0a5030564011400f070081d0315207a50103c034801c00d28103a81d24103c0d00c5074500748407403200890002a10f0040460210300081c400512140035440404030340c0000e840d040c01c114101e540030312900d400110100111000034405800c1c0540c8111180e00050034151218082e61150384640c204035450340008005200c0b602c0c1e8846525aa00c44030401403070740003c0c28180044c0400b010314090180511000c000103182d8031070003403d0261401506441d90103036a80301c1d0038000d8002d0301498600509080000c100d050f400a0003800704a115035590a031074031242c03503606010402134001d808040d11590140c41c0303a120045100d001d1000d00c441503980c0d25009000400701e0703000765400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 284530017 1250 284528767 284528771
    0x50f071401030f0213060503090a080406110105060301110406030c02070f06210203281e02040f060509090a0203070c050d18060e0d080c031b0708070b0a020601182306040609 76
    0x102c0c0f0307175045540a03801602c01c182007440c2d49450750510300740303003801220008281c0b0b54009800306482d0742c024031609540340000000d020705d484540425007a299174400d9114040d806000820400d4400d400c0399080c0041030040c0c1c1d04150700d401c0141d039a61102e0300001c2c0804e0901e0340740c140c07000c90f110768640002a9008110b0460514903034008680a5106100b12100448006901c000d802e41e80300e0701200700c0303445250302c3c03413030381d0304800c1010b074100d0711030900000c42d161800a0001e0164085888443c0c0050560140c1e0f81c1d1018072100035000a0400420003515058490016030100041c080d090a15256403900f403414140252080c146904030710204845400c0310910358544401c90485154080344540d03c6880c41341440b4a10b01032b09400340300d068540c0103004444c2e000800d0a0742502c4030310301620039445e11060005da0603c900b040302d8005074000801000302e459003403100848035003094004035221000800c08046440c501086480c085001d4080c464585403602c1481e0042880e0141 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 284531267 1250 284530017 284530027
    0x71106160b101a1804270f020f010302040509040818090a090b28050702011509051501080910050910020307030b010807031112040c0b03040515070207050d0f050f071401030f02 77
    0x101d1303010880c0c468442c90003152111181c0c2072401201030005030950b041c849a022041ca41d0902c184100d14410081c0d000e0b400c030104504e0503503ca8005c1302c0541c0c101038080b00003a280c594030000107a00100780c5900c100c1a290f0300c2c00e000d0340c600210b6030069244041c04624041581048000e81d074028184002c450f51641c0f207035100000f2007140c100f202240200005256803443c04c10790150001030022002c0506d00f410104070030049500050045600d215211117074045080195040d1030143c502d0200c9520401c0aa127200c0411303003100f64000c0d041d030141e48252815224410a03604107540c080c0220782c41d2310142001d544d1000500342c1c0f00703081d4a010b00408503a180c0d10b440501c20000303107214814100000400748011083c3c030500410416000d240d03645820f0410585404011100c4580c0c1c40c4800b000c03941581c400928002500c10040c44400d1000301a500c2c1c040402005030704980d20300600004140038802031001c003001701400d030144a000c004c1c05000404641c071b40e03201c0c411310b10707c140a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 284532374 1107 284531267 284531287
    0x21210051e0a090b131401090602121003030503160912050c01020d2f1e0f070e091e03070c080c01090803071106160b101a 54
    0xc000c0d10003510ba820110040d1207048201512026105000c076008485501d00c40985a214101c000ca0b13a4408429a6003034888600c810303100c40703901240d54104810064000c030f901440000b0001c0c0000c1c00d541d40580f25000140549401040c4181103008203405040000c0203403007441200c40182c1207a14040e542c0d0a4204049070060240510004c0300c18010300808451511641e0790804901c1140d8019800c1d80c4182000285071048081c7d10301c4100101c851007c0e1800200050041a0000080e1615151003940550f01c040c1100040124003207001c640d501c950404bc04000f84c1ca44502e51050303155004001e00942410100e40c03001801100008450346018020f0f00e031223890b40d0362050010b13207034019030354058041102c5054100440c504907005003030500003400d1062012005d51603043c2003510445503c0b0440703099100c20302058140801e00c8065041c0c00b070240d07180608423a = true := by decide +kernel

theorem cover : BRFrame.Cov 284352517 284532374 := by
  have h0 := BRFrame.cov_init 284352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 284352517 ≤ n) (h2 : n < 284532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
