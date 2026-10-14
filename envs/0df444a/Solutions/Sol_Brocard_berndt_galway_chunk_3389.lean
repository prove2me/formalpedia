-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3389
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:31:05.667395+00:00
-- url     : https://prove2.me/submissions/96fba03a-5dd5-497c-864a-e7d3e74b572c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 609352517 ≤ n < 609532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 609353767 1250 609352517 609352529
    0x18050306040b04171209150105061b010f0204091505010206100506130e0c0c0c01020c01090e130209100305010e1c0503070216150813080d091e06150605040807 70
    0x10740540d00e074603010303c441d603131001aa114000f0125036510024076a4550600424080c2c04031017018a085aa50031002401d01070142c04c454180008510f0f190b001a010100c4282c40e400030640c0c1407814100d004076046a0300ca1000c007511002111b4141d26008a10b00280c2020310240c072451900265043e01e0038201e210b040c1c0160300c005a5110118400350f4548003900c1540b413144e030344e811708000a01154102c200c650401c2d001b03100004000b0342c000284081d0312a010b03140c4c0e21386135150000880103124001c000c174180054884060006a44540790039201c2d005090340384c1c0e80141035091060840d8808000301e04250721889104202681c0e41d00901000500b41c82c06555030350f100c12040741480c9006016443d0742d0603030100894203d000d4003003c4520501c5a4030f21205030f403521a6000802c2d284000035041e80801c0141d075940320000d030000300c0140c0c080e44007400c034504c1e10303401188260a0040c06454965680700c00420061030398002d00001c014a1509a00305801c0454254031040a8883c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 609355017 1250 609353767 609353783
    0x7141c050a030f0e031315020705041e091412031b070f0b0a0c0e030c15030a09080403050c0a060c050c0409030c06150f060507033203011202011805030604 68
    0xe08460344682c0004409003900c0806100000ca0150000e0f501d400800f040e140c0701d0344008006c102e6180309041e040e5a03010300c2c1c8c0204100f030f02d000c0030b0000818101203196150300c000030002e020789900c0d010313080040d0f1040c0103a001c00e1500703c41c11410446c031a5154400c0610401c188074003103082d0100c0320040581d51802c0d540d102043d19200305400c1810b0b200a00300007e140800101e690030b548400441002c41d15000140c0422508140d181e050240c0540c3d070040c0c5203590307558144a01c601942d4020901c00c80002d41201540710700b546600705610440301c660241180304403070309008030210000d00107410315010704142ea985994450a0806a903030003966100401c2c8240f5100300400040c1b07640284c4200b082e514060242c8809411074080d04140809503800029814400d00864940b00e030160b0369a00301e1a069010f0302804041500052070402c01e0340220048190048001e6008180e880d00e07003d450f00d06880003501120410041d0140c120f10100c1c2002992070104005034401d6002440b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 609356267 1250 609355017 609355027
    0xb0c0d120c1710080a1103060a142404240609061b0f1a040b0105030c0307090b0d0804080d02070b071101050a03140112021201020c0d050a030f020f07141c05 69
    0xc070500e03040160b000311304070311403020048240040300c0c280c3c060750704068042c0c6030159100b080d03103001c0c0c43c0c00c51010390600b482d01c00050b03501060491042c69640140101300d6110000d0350003d410b0b1200340b40f194100401026840c000304400800440c0107041e5402c00c45d92180ca0000301905a04181030700040320b003403410052042140303018000382181c4d44016441090342d65420260b8000070200d0b022111a1018000401c440c41c0000324809080c00c010003c000d86414404a00c02414a0700072044d0010701015904e400a1020800b9101400d0840d0040c04442034464009103821060350004c89580d104006140104900280c1c010b081103007820003680c0c401340a40110024691051050516022040003040708509140e4000d40d903030080b80c100040042c80b0000a02303d01c00c00341240515403050004c4e03055140500041c010021150400088501a0701c240c1800d9a00200c03c10b8140400040d15100f003204a070108103031851b092000f072044180800044590111100840c0144940860 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 609357517 1250 609356267 609356281
    0x91201060e040308060301140103120f02010e0703080304051002040b0a0509030307020d050607020c0303030c0702040b06041d0f130302121c020f030702120a080103110a0b0c0d120c17 80
    0xc2404640c0c074501880c0900703006103560410384a040c030030750804d1080b842e04e8200701c50650580b60003400c0d00b142c1d0b0701003a8040d01c0005c0100420420365480d244990103682e8280a0900103500032614290b82c4d15180c60701a01b044810503003051794520603c4140700c0a80303440c007500c01c4040c0c142040d680e01c11103600040c3c035500485000961001207056101e00704400810414002c42d040e40071641c01c40700d520100350301d070300080b64480d03110f401c00d010080140c501608500c5051001515291030162240040c00169110021004590042500380f01140c200040c0180c2e0243d2155103071030a6603803540c0d0081d1548203000c000101c0ca4008207504400448400504403a034141c46400c6640f400d046000b1002a0000c03507489000d0b000340c4004100c081ca29904659441c0071596624245030b013941c1d2611404c4040c45a525001040c0c14804214032007910018006442d094000345640510b0308070080000402a114001c4036040180c240881c1d46c02c190030020702050400d4007140c40d5900b1b5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 609358767 1250 609357517 609357521
    0x61308120406140903160809040212160e060f12060609030f011406010309050303010312020c0909210406140d09020d120e06090609040506012d0207080111091201 71
    0x1014411054140c900344000c01585501420160702211255402c568030480390720f85900a1070803205815103903c0f82c01000681420040c01e800f0310080c0010b06100e00b050b01c907030420000322081d044840550820034600d54000f11141058002161032170701e894607038138082c5014082d64900000b210f200d0b40100b6069540c10054405001014088801fa02415120140640010000e00036202c104002181095109000d01000140c0003c0150314692841d5914248210a400d201c0c04500030101200b40583d80c0300c0c40c43c0d0040072140002c1190703051000380c186040050070a9150840c004000400170182c0040040300c80d52a03c10308c083e05d0305660720740c1c240900300503000203620900c0046a04200140d094941c238600d0404d6498124952030341e42031010600c61101d5960384110280070400c00c03450f0a4008943c8454185450400380d0303200e1100c422815806407400740500e02c600d141031034150b410014a001480901d000740004050001316018611801500c28001c892403010150815825 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 609360017 1250 609358767 609358777
    0x31a090109120f08010509010807030305030a060905040809040b011809110f030c0a02061311130f06080f0d1d0904080c0613030f02061b0c241611061308 67
    0x1c040d500542c41c0b110100101610b00c600d0504011401910010801d030410352465410389182e24003c002c614119101030f0741c56000103140c03048050325060045000030b403d02605025611880e070564850040500304010f46000c040c0c45410003403411640b1248503070204418080301d98400700082c0710388400c065a5400c1c8155208005400000010311859050040040600984980c01e0318441e40303d20307907500c0071000c0602010b40b0b40d1040d4100c100342c9180400e04209a0100c0707480000d07a0007a030b0b00e681000d4601c01e03808400250000034a24160007400d001c2c130000b60702e59103001400f681c0c04507a40591220011400c6000c0c2402400240400601c0d03c00c03128030b240c50800305d400e035280031000c0303500408a4180031000524003014071480d10f1300003d00c0e24002c8140c44114004110250341d605c0854101410803a940d09c034440380c0480c101d8590b018003a224000081407a81d43c600380c424150782c40a00c82900e07080044540684034181720200303145411001465801201d0007031402c01301028021 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 609361267 1250 609360017 609360023
    0x12040b06011112070c0f0305150601030b1e01260a02090d140105011a03150904020103150618052d0a030b0708160f0f031e0c1d0a031a090109 62
    0x101c011220507040120082d00001e0302c248200e401c0d840c6c681d55069003141951000034a035500107080c011001c2d0002960582c0881d041c9800036174402c510000815854100340300d00d1030902038045041031540c0c00b14480c07000144000d80c01101f00c118200c085440c20f1f001b010100c0c03c030750114214403d903943c811110388140e081600280340f82842c0c15145e0080c10207210389180744e80000d890741402e00b8543c0580744030390390702d004c5034030008980401d1201d10b40c001801281051703962001222080500c001d940c000e00b2440c0d491b6203241c0707034480080d0482c4005420051050313802c400c8466904000000002000030607010310000000c80502203201c2c2c1c0401c0d080100030305c00460412441ca903015801c40e100d00541c512060040b40800d0041e03c0c0781134001401000100001c1010291500a4002801c0e140d100505076100c2a01d080c3c40c0d20403036948010b41d0700010403090070302d280e0740140703012000c824008a64000f1002c0c44e540d0b03184603040d803188a004200c411500024a15030080d440b804035160 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 609362517 1250 609361267 609361273
    0xf060204030b0f0708040f0b040c08061e0901060506070312150b0a1d09130c150816020303060d020913050706110114090a0b310b070512040b060111 65
    0x41c4924100742c40380000c0394245084020000010389440c494510180560741000e440001181c0680302e00c1100c940090054602c030305460400620a00c04012840c81080c1c81707116010903003d80c0104207092080607001003201d82c10160240142d40d5004222180e541e49403d081c440c405ca13815441c0c01a149142c07039045a64481c11000856104280c0103200102d000c0da241c20304800640c120b00d43d11178882007960741110903100010180c40e6540400040f26014180b40c2d51000e039141081ca042a80082c0c20100081c541030038458800d804140c8a401002540091811840d00101040c48500300c42c030064800c00b4207402240c0b41070003034803001c11043d4004054a402d181ca410024180b190b038800c45061662078402a030254400600d005400743c00904040c0c983c071840358945081b0b02c540500104800d07080400c1100d11025050b0079020503803400014030030000c000d41080c80c45008001c11800900c0010030070045484501020341e60311030781c01503256480d92180001200d004c001c1840008282c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 609363767 1250 609362517 609362519
    0xc0e18071b080d05040606090213151b0606050306100303080c1e13260c0910120b011d091e010605130b1002010b01120c1b0305030a0e0601060e010305040f060204 71
    0x1103442d00110b102d40d001b0704041c03000c2e90303841081e03100301c0c41040304002200c1903131403040c049004820a046181c0740d0b0391400c0501c8040f03104540a20701217441c0304440165a0b00780c01c121b581400e0000c2540025000801d4480703500e90703140580800401021768000090008030103204041c3d050502030407002091038562140c0410710598100c850350f00902144100000d00300c50f1800c6106026803044c00e6040c064100810518180040c00301c01610050500d20b500da804240d00350410030084240c0e0150140c041e0075491301149440c50566004410703c52411502000406100020180350000200e41890f06c110001e28003540149410342019511040004048080070850740250042e00e004850403400c118141d401a400c9031600c00d00a404948010051854604254048021030181d81044400d04043c40c000800ba5001060701702c020410100a1040031803040c81240d03003c402603c010289075050810280c0003648090246040503200d60014040200b4480b5400b51a1740c4010259121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 609365017 1250 609363767 609363787
    0x1706060415120b03030a05070602030a0608060f07030c0519120e030c030414030c030703030503090c062709041112120f12090712080c0a050a060c0e18071b08 69
    0xc8140b52901d5007059040c440001d11030314001c0b0880749803840c0c580302c583c5000100d9540501940004180342011643c902c40007034a00c405200c030a10541e46d18010007902d1900c000064111b80c04000804108074080c03046400b4201c640c80301c00501003407070900c1714840d107111400c080904580810003d16010200b101d142d05c00b400005403056684401040075882d80b840c0505649180440e0581d605500c41030041010900490003150804981002d50742803100040204080d54092a0001c030840d40c8030340c0900310074080c3c0406482101c400c640c0d501d081c1c145621460b2515490400c072034440c002400c1d90380c9209000700508a030b440c928001040d2a0401c1c90001000b642000c0f5103001c1c034903d01000680361400c0400e801e0165040b0303458070624040c158070b40010130307041064510081d10451804101040c01008181c2c0c0b02c502c10300001c01c65588921005080044022096006005801c030201d0b01410150019031301101c0c80c5030202013290340b54002c4601100d0660003600340d103400240c0f01c0300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 609366267 1250 609365017 609365027
    0x312130f1202150f060d080c190311010b2d0a08061b0c0307060903050c0102030a150f0303080a050601170403050c06010b040305031204060f060b090a0509071706060415 74
    0x410441da809564084611400720038030040300304c4408903007158440c0068268986044116800742c0120034081c2488404101baa1402c05030380c2c008180941144800c000b00350b44814464400d811850080c420b01284101240d00c1d00320203075001c0800c030320350491800424920000480c038140010100760907141d0b1001856107d04056079070320109002c0c210281c1005e40d403042280d9405d030801004510341801d40d219076008000008045013003050401601d245000c09001a501035103a0100c001480074001116166000c555031021500010b010383c01c002203504440702c268880006003000c90300d40e4a04004a4800f041808140480f0006600b40000e1680c400040e081610190f021620566202d0b10100403c0c0902c2c0300c000e04960007041070041040c02d05880540144c480c0070040381d6600c61300109020f0300c40542200807508000b140d00543d92610000324001003d0682e0ba0302c1c0381e801c1000c0b0080100d8459010441812041400300e81e454550b94222001000b02c40020b5100744907002c40102 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 609367517 1250 609366267 609366293
    0xa050a060f1d15030402090c03070c290106120c021908030a0e07060203070b100b0403060c120f0e0c060403080909040809041a01031b0503070f020a1203020c061003050312130f 77
    0x800341001f070000441c003c00000c103d1303020f0203081d100d42142d00303001d503078107908801603152600c5540303820488882b02161144107a400380000e078403140308011107a0741507030446104080c4402154889165903080135803d4413840010313030304140d045640381e645c0c0d480c030806098400c0d0218824800c060000a0007a40440581200b81c0b045c04000c032076444441e4420b40c42200c9001c0c410952030104010800500907610540c194002030511303400341c001402c1428100c1c0e004a0310362740c0981d00c406200c01400400c0c4580101c0d040100c0e4014245401c41c2c0b104c03640342c00f41c923280314080c130010804a8180308070441619801c0200801c02d118059441c0714090306078001000b4940440d0a2182511046482c400c403071010306e1081d40d0f05801c6a448110840b04501c01d0b0841c00198012f10030b610300414180c2c00d142482488039100981c1d90b104118100340b41c000001c04400c00301c0038100d000c0c400242c021007111618051000c0d25a4241c980302e901202e411603484000341014450b0b44028104081541640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 609368767 1250 609367517 609367519
    0x180f0d050312010b0301060219140a030e010228140a0501020d0b091501020a020918030f0705160f03060b0f041409010605030a030905041d0d09050a050a060f1d15030402 74
    0x2005607680c44400350321a005c207016010140e04031584038030321000401a0101150700441440400100e90040d2606100004a007600002c0c07108a03000e61550b0108402c24140c5a0f104412140d03d981ca03d404214180b90800104107408024500365010070411078415000e401c100215034510041c244000240b0701c807044280a240b8650000b980c240100040140100041c0c016001040d400d078200819030030010003010710300228907440300e84482e041000c0c4c90f1114111054507a10240781c1042c6180100c0b01d03481c038a50701400300b401d000802e851511941201e40c40b82010aa0f41e841400050815a084d02d410ba0001d20308500c2c00301c0a07105d1034289002c1c400c3e44000700050b9031201c041c580c0b1030b03100402c05004540f6104040115041c40e45c4843c520410440da004030049040000b1820003904400080001d046458240490b1500c190894000c107822112510300c1890490090802c40e03510070340c2000d122029810340004044c42c4922140d5010051040d401400c9446c021200d981094a0607 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 609370017 1250 609368767 609368797
    0x10311030f0601180f0c050319021603020c1c02100c0629040b01020c0d020d05070e09060a06050603040b0117070911040e0c18090a0b030604060506091b180f0d0503 72
    0x1114145e03c952103071500112441e43d45603d036503110003000c858801e070b0384003280b019a800c2103e06808544203610940c4a403103075002c1c0c0b52f59201002001160410380030181014231418003141300690f42c20010700c05400c1e45040080303802c0e40314100400240102009080014031b0000072000500050848882c01841250204040c22410004903590200d0940b99500094900d9101000d45000e862101410b4800c0c411a0001a143c0080b1080c0400642c0d2407a0300c0e510110034881019203902585000c0c14041c0d07211411444d01c0e4548441005040c41034206983c200400421043c106012010186c80c020380e05000d04d200842d49520a50300501c202001315800310080344034030741d00304c00b1103000d10380303a003040d4050029100c1040050f2001410701504543e0b50b104054050320306100640c8034900817100040e41c0d00d005070070f0096881c1c008200101c0705400c0c00c022900320407540150340020306d443d000030301c030040380d400410050321400710295400341e903056050082020000081c40712080700842 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 609371267 1250 609370017 609370031
    0x70b070303050f16030209130606050c190b0a090f0b040507080c1e011110050f070f0309020a0320060d0b0a050a060c08134109010311030f060118 64
    0x82650760b042e0550304200600410013001900a2203034002e00315100b00284044e92050880d0702075800c0750015070019000c154041217040d0141d0b01070042e0255520009249001300c9002ea4420040c3e01d0002c0ca82c1c40225940c007200c0060000030007480728019885400d04030a4105403c0c015603030390b01841000c1d82445500d4101c1c4083c14a03800c12000000c00b03190140c41c01c2d2601005581d10444248a00020f00c9004c8842c014001c0358000c0600620158010800713a003400c400040c2a9405140d072803081c10f0820b00040d006031211201501200e41051607119464150308e503082418402c541c00d6548210003240e80419180030360700c1509084d20031a081075085548e003081c032501c80c55512403d4045110281000041104a0000c0c03491041d80e070384c0303141001e0b2618503180c1d5407a5801c5807600d0400c1140442d40019818400c040c408010046048a004c14810000b030340758441400f00400a120401c0940c007182c50410407175402c030901c04c1c00d50b405503848400651440645100c240562810f0182c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 609372517 1250 609371267 609371281
    0x323011e180b120742090302040b040c0c0b0403090b070b180609120a020102190503070305010609080703030c06020c1905120304170c2b030509010605060405010f11070b07030305 78
    0x34004c0101d48a035840f1010700c43d4004808544203c0d544104030718000c00e040c46020b000d0404410759100101600c400e12644c1c1580103002c229451200c04c0d9009a15240e0801e075603a070420304003900340e9440086030b0941e503100e1404444150841e8459000500040b920004000015403014071031207a024000d8040102c04024654814040e94601c2c61078000d20b13010a0b1002d00b1400401c54810b440c0005403418007800c0100040d150341401040000d80c2c00700070b1103200f540c9070248a0040201e458594840c5041180c000c2e124607442c0300007000e0100302e1000d402048040d405a821440081040d0f0f25103610b0000d520900c44120f06d0101d8060143c0110b00d40001e50110039070b400b81d40c01090010224111b41c2c014034440c0d1050380d08031028440c9070807100014038084902a155040e10030b0452080751008000303019110040c0c880c0f01e60364105542440700b501c448003502c084440c00d10b4140c1c402080e80c01c060700d4980750390310a07503034a0164400100341c100350f4100034800c0700d10940d0208400d03a5044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 609373767 1250 609372517 609372523
    0xa0503030c090913510c020a08160312060e01030215070c0e1510050415020703020f06160c031101080604020702010f050a120612030323011e180b12 65
    0x3010050040382c5d219018a100000c50211a400030409894101e40072420f50302185961550003050398600300000b40d14891034003902031000c140c02d42d070008109481899561013458001e4207400c01c143c00b814074010341454800d01c0244500c40c1e40c2a0704028558991803034a41e00102404160300030802c0c0d8000c45200e1025100301c5a071590010000380855003440c0001613040c00c080d100003080d060442d072050a655618000d071500314040e480301c42c2e449140041c2d00024076100041c0300107540007200304001503100c095a280484004691080e580c41484030000f000b0754003a44007601d00d003640d20b0044104115400c00859025003601d41d074640b50b40b00c00c10403050388204080240050168420398101c50f005501400c544851810205120107822101c0c10464007290701c00008848810100018035816205021610700d03044211a41103180500d201c03e0b481c3d042c401c4810f0124a50001150070a64407922009002000e180d83c616000d05540b00c806807c41c80c1d4050310030b003030010150400c65800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 609375017 1250 609373767 609373801
    0xd05160804060203060a1e05030c0d03020616020717060405100908070b0a021b06061519260108010221070918470904080c0a0503030c0909 61
    0x6030303564480540e00d0799900800384d0805059542c1103031020754003040d903680140a4841c11001b01045584c1c403450441003526000a4083e0280190100d04541000c240d000c030b441c42e0b00800d8aaa0b65100302038000049260941641c0020b091814003030002c07812100200e03190f4041d0f070042084460500322440800f00f210114030008220100030840880042e1140008550080900c0b00c01403e000c81a0856040300600301840c14254002204102d110302d0b140132200c585100c600081810000b05410307144040c034403551040284074512440d1204529560100d503662042e102102c1200e5a40703440590107900003002e03003c00d94100320300c0c100080008159244c4156065526800924035081131001410103890b1521401c44e107800d5131280c05003a094901e1810703070440c1402e070401c110070f400510001507540c0c00e141c6140c00301f811030140c6035a9500c0b915002a00704c008141da6011201c126444c140c00104020007a00000c004c0188001152001d0081d01c0c20540342a06965aa00d034200b2a5041c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 609376267 1250 609375017 609375061
    0x90d081908071b06050604090b1306050c0304051e0a150204090e010c0807050703111506032b1b050114060307050d05070303210615031d060415020d050901020d05 71
    0x1c0700e10f008010030402c0d00324540141016000294826154880044a446c22030341c95219000500014003008422311600f1b52121004100c141103007400e540301501e51040c0e1808171454010400c85030b0f042c041c103000f01800d0941c0822002500d408040408000e07400c1482484005880c041341d000c01c90606000d206042e001c01d5a580c0803c5da92480309880c60303000240241d040003040025804031410801104c0015441c849401344540b80030003c040c83e103c08510305040501e01110440d03820140c42e00001120385650510148484c0580202e060740c103583c050240180d030a00700d081c0041070b942c0c92113500a41d015420354503030589560600500c400840002007103580714240400200307118800d690a0400159001c10300500020110030035140180c1240000100c0d0814640040d9094801c101e20401c0b104681c0c11048510041d598a4290041000d00354140340b03184140c104081e03070b0454058001e02c840800c030500348119118002c1d0070207a0450307540751501000c00c0324220349900300c40881d51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 609377517 1250 609376267 609376307
    0x1706010c0302120a0903061104051005070809010804020f09070806030f010c02030405040209011e080105130605010203090d0809030106030821061e01030603021309060f0e0c0402090d08190807 84
    0x1040300e20f10002d03910200b088403c0104540c1c01200042060007240d6513207000c00d4015442d03d0420041003041000440e0364000c0c040104000b40014100c41c00780e44007040300742010030300ca645a00101d041e18040141c1c80e64003e415904001c0010341207206c40e4000c64040e8103c07403215000c080018201d07a1a04101c0d009a0b006000810007460250028620010185042040c2403c0e0310154550310742d810b48100080f480010040c401403c1408ea803c009000b07102003841000c1c03914001035241c0c89503401090040c00301030f5440c014031090008852040b040500200320141d030380c0c100b00101e5088000081c0c1c0c0c24401e2002c03a203030b4100140d1554002c0f2401050b01c680484e07100b111641509102981d0390525032603180c000050f07990501000b000040005022505140740d240850445160802540c0d05a16055414000707150000e500401c485003501c0050303403841c0100004106001a12008000160000d54040394030b100c03040c040c4100e10136443c0c1c0340f40b0352102c1130182c0d404e040401b00c501c8142c2c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 609378767 1250 609377517 609377533
    0x170105090c1813020306010b0c0c0612070f0306031e030e09040b0f04051606120e0f0c0f030a0c03050102070b07030603320601081605040513170d0c1706010c0302 71
    0x31403484030305600082401030502c80f1804a501103401c2079000da2000c0c000141c040340d01d41740c140042c0700c0b40ca0b16400450301c80c0d01d0800c9100400c04402c1014000c84104140c48502d030510764002e13840706020755004844c0e501c0981070008180d00242200710200c1c0040e12810140c4000e003441c171072050040754080d260403907556800c0c0b480210080010170a45140c810008000c07581c03449079403810040d00480d1789000704039a0050004060f20506000c4204551200311300b940a024040340401b41170000316101d071004c8141000191802ea034000000d4072070301440034000b0410074150b00404080c0d00c10036403c4070a0703991003000d40480b17410b803002501540d0381c40c540c00e0a80d283d01c242e02000554644803e450468103801691800d90300360000b0950f540020064040241c3e1031141100504049500348510b10740040d040515807061840284140c00d580041c840024001040d1801424040c20402c402148180014005a214510720410020304004100e1030351013141d041b00c09175010340042183c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 609380017 1250 609378767 609378799
    0x130f0810090201021608070f06050a09090509120d02040e060316060c0309090e1005090c06040306110909040c0302100302070b060910150306080f06010f0303230301170105090c 77
    0x5090405802c0381140564119004080c0306000c140002e0200308004001440c00d1103140302c0c5c02c1c52136402203c284407082c8015545035034890740080c19601441d43c041500e40f1000032862800280983c1d40300c050201054946002c080c69000d4400c0718105651042d09880d101705240d01e504444520000c00e0903400703003e104050140040c404035070702c44d00d072001032940c1d64101141119918413a411140d044105080001c90303450250541050004020b0a10303010301400107507031403280d4400149210380b02d0164000c41c4010100f03990b984a07014251611900d02807401c0b17940c03e2041c0c0130480c858858004624411071103071080c0d0703102e141c0c404840d04498075100d04000c0d90700d2009204a1040c000281f000c220444a5070be8031181e049152404541d1070b06080085080103c29141070003517511490041101c1100b103064202281d4040c01d0100b03104107035210381640c0f00b0701e4034075071940c00b01c0000000541c9402e4140b8100040c4d00d0200810071a1524080183c0b20340d41076a6850340004c08064075585 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 609381267 1250 609380017 609380021
    0x311030106081f03031211041d060402040306020408060a0f14131106270f06090d1b03080702030d1701170f0a0302032208060a0f0e070b130f0810 64
    0x80b400c403480b00c0c2c3c01c042800c090190303240034a030030071800540610340c04042503069018610591300c4041446084c1402c00111600401c42d184180b5000b120340004038013540c4441e4100c07405560800d50a42d80c460300d0390b480d0396495000b40e420341d018600c0e240c2c02c107240215510444080328079505074500991201d01260010300c1c2401d1040d0340100c40c400190a0b07030b9481d1801021031020800040340b01003480b0b088080504c482c2c1003420b01a1407000700d0f04400e07a035000308603038140800712158004003150742440b10b06540c0300d81ca0212020700240011040c000e4400281026500c21411a00c11100080c0300301d85080540071280750b1820303a40c005009000b001d000b40aa00c00022040785c00291035001c90314a465601c000c243e005d40c000185141802c00544480900d899881c03580d2051036142030001c6a91f804003c0c200300c0d003e0341d942d00d102c0c03981032241c202800450304103080302c44107070b2a00342800f01d0b03901042e044010025003510000304030041d0743c6840d00302c601c4100503204e240c92910b00840 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 609382517 1250 609381267 609381271
    0x903050a0e031504060c14070c0501050304080c010606020a0605160f140904150e1305030f28030608060603010e0a06020904020403081306021b0906040b061303140c01031103010608 79
    0x140c18003071412819a1440d4180c110f9110b14062800403c021084081c05404c00c1088104107104604c04c004203808a114001d06070110381c02864050761341d0b502c07803c013401c142c013031400140190350910b840000c641e54001643c204050146c0410000d68580440250741e1071001154003011421040c45258020b001e07189400d11001d980c0181ca150402c410000340c00c85100e100140c0729404444c2c0140001009101c05035405683d44254a01180c00c64913404d80d240035455080902039000140d090407a1282c412010403848051200c0c1d201c01d01410015000e80032601540c070f25441307100001b07840340c90140550300c594901c2d04082c101100c0d094803001d0180d03012042c0950489c0c0c003000004000341403c00202050440c030010300d0040c03410000c009040c041480c0c0c031a9130110b02216802f0850f600c666040b9080340040790001fa0620325840072074024060103002e0080c01e202d41e140003080c4914203218824170018070080d2065a10084015030860b68030078107108032080b060005001c182e001d0700403aa = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 609383767 1250 609382517 609382519
    0x601140a170414030d050a0e010b0a090e12030702030307030e0106050d0221160e060f0a1401030e01050c0c1c02070e0703020702210c0f1f120c0c050d030903050a0e 72
    0x1180380c03c4500f040c140355900001c00050015510410005240c44c4c51064100d002c45ca44004d012a11030500016a0b640083c080c06001564440c0140043c1000700601840720105031501c68482c82d10b104082e4881c3c0048030910042403c20031050481e400c10b21440c000e42c0c80040840c03922030425001e004c48100e0381d001c016100d041d4041360081581c010800e619840001c610191002410007003640700c20b6074003500c114021905d90385541c4a56881894420550324100c3d0280f00c40c8803103c0048016246130341c0d0b06440e0303510300130500c10742c505080c004000080460040703894201403009a0200c00d40351001d0a0010380010405004040315a0702d8640c01003143c0c9030141c1020742640020f100c01c000114049900c120550306014590801d01c00900d0300c0c1d4040320381d6103071455000c0100c1c41d1380c41d50300101d000c1d441071440c0072104540600c50011100345410001c12900000a40c040c1170080000c006507164481e40d035070845494400e02501100940c5a83e0303043c02e1039030720720080d1024450780b4002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 609385017 1250 609383767 609383783
    0xa2001090909050604150506061b01021603030e0706090509060402161b06120c020a0201050c010603150902030106450c020717071a03040819080601140a1704 69
    0x7030620018000c000c0701e107015101400750740c03c0030b14140145822107400082c1036401c0070b0401203240d45000980c1c81d561120901003074004a080031140c0284104460000448040c9c641c910a06a150740b0040421710b20201700e80d0800e84440041e1180f44991045540c0850306000188080c1010f4000e00ba01d00d561880035001004145d4549510107043d40c00111748114042c010006158400002c0e401e002d480d140401c04410802002921160340f0b45010341131007800180890340f510254000801560010303a40f02c2000c21725000324000c0c0504d024140c0c130941c20802d020030302e04c0c0c2c480f0100b400c0e10031149044004408072500107065030a8035803c01a00c461351a40000602254003840d48000840d40c00350805030300302030803030410101d590381100c01980b00b450140603441610905040000d541d40780e09443c1d5840d89000c071a40c2c0304a100c51445494104d121181c581d070049480e5001d6402601c814910042c1d10003045c0c968007030a84d00c0c00000342c90050031940440f8081d14903402078050000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 609386267 1250 609385017 609385019
    0x709060507050604110418141b06070605150a080c120303060a180b1c021929131e05041b0309030e0405070c0203120a09061805040908040905090a200109 67
    0x60107555607c01017080d2401c000e00f02882814030024080500c00740f440c030203141104450000420824040c21400500300c80d0351b0b0740400c0041e07064580d10380b00d080d4010f02c1d5056040e01ca84420ba01c60002940e140e02030bc030220b5020201103004401d40e44140400360401202c140303454400300c103172551044001e400540d50402c151040e119255103001d410210011074500d12001c1c41401090380c21201403011092100a0620955898200c2c90b4024841d100940c9500002c1010f0711142344180740700980300d0a806080010000101c000d16070502c00010100c40d2003030303903440c140030a0b40da880e4911944a44191086242d2038000e6004083c3c650003841d152103241c03080800305040380d2095446402260390a44001d08500d410000d255860941d00c0e10b007401d150014202074070001907805014140040c284904c041c0d032900e803c0030350007480f00420600c40360283e4100800d0582c464001e0345010350401000504109000410000c0701d68494084202a4024022140f044501c01050341c10040c0d1150 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 609387517 1250 609386267 609386291
    0xc03030c07050f0a020102030927040f0c0902030601050a031107020a0902030a0c0c020a0501140c10060e0a140a0216050615040510270608100507090605070506041104 73
    0x1a40c0304204120009584402908055143c00c00101c05050180e20110788540140d0703002c4281e90003e174040c3c6a120524050041e08002004520354172402010300e83e04101c14001c0400c0b00c000014010125843c2e400e8032a003506003684811904180400d004111118080d440703584100d81d1150f01c01803241c10a116980020000107580c0d0110380600c0e000700900c0a407402c28841e030500c4610314101510b40c10546e07400300d41c040d201880f030b141c140074240000c1d0402000c03a034111004040d040301600c07041c0002d000280000c244a0045207031542c101f00004000b1900c52041104040481d820342d0310356945d21032450b01031f601046072070000d44604c4203d040000c0c401c1094a0081303113070461a501800b5100203200440b50002e240b0046090051010401c44100e10040c490394100480e10440480b654204240a401580e200e14001d10034800d840c406140356a100074081c0320030741c1d2981e9004d50368803412141c034018058050303c07940209002c940020b40881400c4100c20010b0000710f01041052 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 609388767 1250 609387517 609387523
    0x3030e0a110603150904060c021603481d1e060a08030a020106090b0105040b0d0e120c1501091505130905030a0503070e040501061e091a07170a0519050c 67
    0xb481c21107d0a80340c2101485964052140c40700c80002c00e0042c00705140395840e4101d480084000d10100d040d030401c0e0680840352095800380f40ba00b030008a1039146003005484e1036190b09184140c0c1c030700881640107010140d500d090602c0c02210145080110785184c8961428000c07000307480030b42e00040c81140000c01d0075090000c0c0c450351174241c0000400c07500d042c02c58000d480c074400400b410010100400d115561500044c0c980c042c0c03481e440003c0c0c1940340c14440307140c8904850411107104c3d000c503850750034001c0050001c0c015156041e40002c5660b840c19010b081e1140b210070089030407824a403d00a60412801554100702c07040e5001c1100c0000d070300c80c18219070003607910303400041c3c000080152464218483c1c00d80c1c444281c13000c0013a0361400000a180d02030500140030060b200d8000a404c042c850400c000181c0081902c1b4540b60384182d071103034140c1d400b0034030844261042c103000120050744801620503805280e2112407400d0690000c40410b00403025200f401d00c08184a00003000d0010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 609390017 1250 609388767 609388771
    0x7120303050a09021207170a050312042402070201020f1b0f13020301090c08011d060f010c060606110f03040e060906030732091506161a0403030e0a1106031509 70
    0x103000341000c3d1f410504000049100446c4110150380560320f2040010b000100301c8642d5000320641c03000350784030ba241c21014424290110340c1c500d00703a12541e0140125a50013400c01c18400d070212100219410002c40e1200107a07010043c1459200b1074140d0541070500404105000003003004000c9802031211404070380003030b000100746c80d6403103400110107a00504170601405000d03018000708102c0500074180281c1c001e240301d00404848081d298164000c1100c6400c00d45e0108050100c2c0e0303284c041c0101555074101c4484224450103090341858580030040700d007070303804604000703003607030f039900203100420001900183c1c043c81088400105c2d80d0b1006a0700811104c0200507954040c84500d8040700480300000c1240303d402e0a100784031542e0000410158903043c140c60b120b07122402c02c1048102c400305900041c0041605400b442d141c031990700c40a0340700328801e032402c01014145940c09580e900d41e01d500280019540c81101005103041c6c4051355201307c1c295041c200003c40940803a0340441d003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 609391267 1250 609390017 609390049
    0x108030a090e13200301050408071a04081c0e0d120510030b0408070206070b0f10091116032604140a0201120b0301020409090f0507060320070203070e0106050c010e07120303050a0902 80
    0x100ac01c144003001040c440941c241d403815510214181016101c80b10345118009008603440c916000076618051181c03c9074811480b100c0945049400e01782c000707007060200451805501d031a0030001005030404017480004e9a40103007a8100c1c2e5aa207a030340021030382c42200c2c10b036800071040c4000e1001407501c00010340b04d00172280c1070800d113003400e000d0942c0510f156008000c0c0b06081c104003102c80c840c03804c00e0701c051803140044807d42d112282415a4802c0c07140031000d03c070241401c0e0301040020780d030104d070340100d100c0d400300c071021880000e5060712102c1e841d400a002504180118503060282e0b0400075200e84010f000624042e036a202050450704100401c540c0c4141000070007050141c140310520041c451400c0501c410041071040384908803142611803004840821404155282000800050059454031707030b1055031101b4000e0b0517030708040c415100c10742c24100c9a910440c000304109003242c0c2c1981410b0030400c441e540a4018050081409540c240d48014200140e03460b24030b02e600c8012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 609392517 1250 609391267 609391283
    0x1005090709060b280f18090f0e060a11070312061e0312020f0c06070c180b1507030e010e0619030c031505100c03170108030a090e132003010504 63
    0x4081450000c14013030715a007803550a07500c010003030380d500e40124650ba09552145020485050701c81e02600310f80c4115003021803014523014040030034403070540c00416490410022240940d6410100070140d98482c50000d110b80c0d0148202c0e4002405124001c00c000205000412090f480c0c600130100c1c0b03c0700006a030951510780104005020584280301e211045620240a038110003884545ea660020b04c200c0b0b006400000f881414400a502401e01030980c005a8400e071000d05000200506820981c03a40703c0e80303e0100c00c80b44207800200b1500c1036941502c0f0404440b207076400554000d01118225a0040403c0006030b89058404050807000b940c0c9031800900c0d0005180d004044880072070005085450607002400b2690790b000009600b0400b42c80e00700c3c5540c0741450212030050f03074400c032025018a400300201d400781020000d06415601596078030700055494021030b2000318150380d00b511598283d19a0404554040e183e81d03005900c4071140c0c0c0050f40002c0101e402c4580494040c0d509078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 609393767 1250 609392517 609392527
    0x110a0c0e0a02090a0303050a020a080c060708071e14090603040f03090b0c03090609030f0a080d0c09050d03030c21091e1e0c0b042904081005090709060b 67
    0x10600852036800c0040e580003141031a41001c085501440107020140c1840000b0960f46000c41c402c10407102d106a11500080e250202e060b11107558401c155085070200350000f0002d00030a1003081000b4154440c0018059007580d92030301030f10181c02205041c0c01302c0608000f440a00c0d12010021401030384102c1105014107800d0038003d0a102442e0840c00450700d04124a9040c03c1000083c2d445002045410030b9403040d440d40041d10700401650004040e019503240281480745450142c0301003968500207024200004404036401030003400740c4e5500100007020080424407070781c4403142580c403500300031030240da81c0b03460340c01e4034500d00c240e6203242501c940421003001034032030540c80a2a05102c0012b030368511541d410b2106038144403961044544018203506000d400c202c200014000b540c0026555520b4482c510380c100d46012008248001980441e0201e07500d00307040380c1c12551248058007480e00714841c1c401c06400081c1490100307100389100851740e4143c82c42034100500100c54810340c4c4d2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 609395017 1250 609393767 609393779
    0xb1005060c061f051e0a03020301150305010b03010c09063b0a0803031b070c030204050c1206010206040305160501240e01060503060109050409021f02060106112b110a0c 74
    0xc40d12054510120f03449002c2c100416140e81d444016203d01c048604805113020f07002040c4038818541c000307945582845120500d00c41c00d0381952041e40d00950003030040022000625007238a00503200c441c00207490310010407080d40301d25540c22219106840100e004011801c2c0d0912840000d200c0302480403202103031421500e010741c01c0c0b800400e407a001542c1145042280501071040c119410003c103040040c404013040541c982203000745600030001c00107410110803100700c54200d000500081c43d101d4010440960000501600c150b07410b64500745031104540041011407220030049880e0341d20741210950300c030007254420500b08107900c417840c07499180c80040c05121320103a1003202031281c201300380035450340c0c040208000d0300d20a0703501182005551000ca50b10800032450050740a5104d9460040c465012800a049690581d54201d1440134076915a8880d226801301c40d625403040c5802802c083c043c4171008a074810a410a00c2460804003e080d081965419046845074118582401a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 609396267 1250 609395017 609395041
    0x204090c1401080f060603071205041203050c1303110f0d0b0609010b040e0a02130b0d05060316060206180c061617040302010e2407080c010507020313030b1005060c06 73
    0x80780e0700074070b00f1100c0343c1055800803025079000f608850140702c00200103010350b40111081311915100d04c0d410005807a190403d210f001e140203041d04002414000800e0250030f012040d00c0d030303c0da40c942d0380d45140703450360382e42c5c0d030f030a941310107c6c642c110380304c040118180e66542040d04940c0d8091110340d1040d2502000b00040124141c10414440406200521000e840c1c450480d50202c4204001030b078580c81c8890740d2165680030703070010442d200001401650481c080e0050790086506900711a1610000345503500030030914000d04005901200c0003c103440c4400f620120248440c1003540c2800301414049120b41e0300109510900c510340c50304900c20880c8a18000401400001c0080d0034141036600081649120340843d900c5600301c4251144c012081d11112174081c010307041c912360764401900c3e0000c2c8680002401028551070107001400c0c007400402150542c1e1096646021518156510700c5002c80010705203002240c04007030089015151040100a4a0442c10007400e55161030014041 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 609397517 1250 609396267 609396299
    0x10c03060e090a120507050721140102271203040602150105090c0d020d0b13140f040305190210050f04060c09060207090c0c0507091e060e13030c0204090c 68
    0x42180c3c001c20703080c40414440910300e107540b0510300e00a41d485843c1c0c14841d01c1c110607500311103a20420b61500100644000401181340e510942e0007a14250010005600702d01507001c04664055058000350a001210724030006c1c0c090005000d010880313000c241c007626582254200c1c2026038017410082c14184000c2106034018041120350380c506180c90005907900340070707040361078000701e80200d186021500f0941010408101c081c04c070404038680742c500c0e403001d00347c001f0b4480b25071034141002c1544a0480003c09104a800d80c4072945406d4110344003801145620900101b18010ba410b017100c042401c0c0103030b60042c2c02e2600e13140e01c541490304042e804c03101031103e40000c0c801d0240080160980109071101144d844000009078191462001e80316120004002011400344100204204103a13510404481000508040401c1f003040d008004407201409140301c0000302900140740e140d902da400c80c40c500e22924003001e16100c0c2d68042001d44812501c1100e40040d107050510402c0045031900c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 609398767 1250 609397517 609397531
    0x8010c0801090e03090609040b09070e0a09021810110102040306020912150a05090a0f05100c0c03210908030405061501052d040f090203011a091804060e010c03060e 72
    0x2015107003280b10a5039911603403901724000c18002c41c2e11354240c0e8465021940c152009403c0300f00ca4940b0103001402c1680c004011442001c1c5450007040c038480a10035601c108404408c4801c84050200400800f42d0403518002e0402c0b43c4201d8402044200780060001140308207400f60305e0700d180c40c0030450140d004540c240c2640c2c0c8078400c5000245034009059400000401c0009540d07213560358840d08084400300007030000700c072007104007080100010f00308002d4250f5200802030782c061040c08650785010071402900041c070004500c1c10001c103000c81d108603402079040001e0300101c2039071181403541084505650580280c2d080086481c1002d8009001140900e0110715101e100c03c5050741140f0816000e4540b20031080090240401000445010340000c4100c1c080d8941e0300da903120081d40c424010048544c2000d90380c407012001c02c600f50f440070b40d001072000d090341d40c80d210f43d4071200800400c02e9032215150110b550b0301000a01c241c9400800302d03074000c581c140c10101c0070381c5088406005d207 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 609400017 1250 609398767 609398771
    0x10b0904030c06111e0c060f09150702032b0510060c17090613090b0a0521100c0309020315040503040e0a02070503130e0a1b030903050705010608010c080109 69
    0x1e80c00508845001d07444280040c1d4200100c4c0c6682c3d4a006242c40034801c0c1ca440c55a00c5201016080501000e0000d80100c4903e40d80b4075008800d419400e881c0e0000c035070300242d10381d00543c10b156040d82c0d101107644100c81c00c080c071900001e05081c04541c11400000c50306d03010f0f270121082a02446604c046c07800d8404014511704880102514407410000c2c141212242548120900c40070441d958035000910032510f8404c261030340141d0410303912882c249a8500303c0039400c0c1d4180f03070708050111075004004c004500c4c04640c501a8520b80d1075916a0f1500503841140040c882d00e20030007040d19529940003e118009105041c60858264008010780d00340d0b9040000241c0000110780a568000b00e403500c8607150841201c01078000d900000f07103075010104031003800860010740c0004486190118620544400e40c0102c1160020070051070b94060208a0f86801400780d00f00f444e00910902c1c0c491300c0c200c826240c0b98211405038104051a035100c100300984194003051140c00b501c150380301 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 609401267 1250 609400017 609400021
    0xb0a0606020d1b0b251b06020307110601080d030c030b0a03060e030708031f05090f0708100902030115030e160e100503011401090c05250204020f0f0a02010b09 70
    0x806542d03808840c400c00d081000e2003014880511600d0b40a000d00c80d0301100d100322505140c80c0312001d0343c4801884c080c002c1c5814000c10001c0b403040c40880ca000e407200804000d0300d0696101d04010b03510082240c420b010100700901c1c1030302c00412006000f0040030001e0041c14600e600d005058942c540030200070941401040141039803500c140c003040b41d0b41b00f4000500d9000c0e81c1d400302e0442c01140809403d994022040010760004000816021030034103500c103080c90744030b40800220f500b09486009004110800003480d13070340a031f2076040c1c008088140b00102142e171060300c5004d0ba4002d0b00a01c8001d41d0710020400d5654040c011291071695010203000b49200a40d140f500041d001c1c480d800c090300442021032801078451008401401d0094000d000032018075588840d168400e2051410f180d14250482600e45e00c5102900d0022003441d5501050a6182000700300104100c50280c0c2c0c03043c1d080110072180100f0301c0080450a07441c150702500c40585038000381c21a0b00d4200024091100802 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 609402517 1250 609401267 609401279
    0x6040b040b151c05150114030d030203130f1401020a020f060907030f060b040207060f0b0f0103061802030a02090a0f1811090123220f12140a0b0708040b0a06 69
    0x8410440054801101c0600c4450800a141030501806448081700c490000f1030b9810380191810980081582151440048150300700c0c200d200840e0315458003441098580c0000f560104803540040c02032090400f85010384d0601802c992020440d4000340e8400c2d20b8440c941001486403990024103080549495807840c2c03180c40c00007110840041031280d03a14003950f425a220b6040d40c00d22508008108000403040d04040020421001e00131300c00c085500021280750b1281c041e52007a80c410039400e040b90485071a452001e500044c3c66100d1103502880080c0041c1c80303030f040e00d400511003107040c407000303910700656880c0254000840d50002e03400c0c1089400841d00c1802180c9590b0820b01c0e01081040348803610f0300c403100768154448070400c0009035008030360503451094031102400e4215450002c3e65080d000016a00c035108042007004103104c0d0202003590880801309000d00041500da240100d9914203c43c02c80072940c2d80003180c5d0100510051100218082e544024000303000c020180c103200f = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 609403767 1250 609402517 609402529
    0x6040e070804140303070504080c090130140105040c1d161e030606030e1501120206040b07032a021e060c060a050106021c090b0d060806040b040b15 65
    0x80000d01809241c00c04502007041d60b919180d400c1000c3ca054035124100110014800d40c02440342c1409482410901c012902d402c0d9072080c120b130841c01c010011901c0c40220761908041f12220b4282c030140100c05a808959046268183c442c100c0c400003400740742603d443c68402c8011340050404000f001c0126000241c5c80601c13039006132075040940000035040744101c4000a802192880401c916002d0032504c640581000d410703100c07240c40c144070300303110381e01c000d90f0720907181000d2120384203010010010941d03003402220300303c0d0005d460307946030a4494035208a50382c004503003100095102c0781581c105018170b042c4078100c80a160f000d02c15941543c3c0009a08954440304020ba08034030788030740d200c40c0c0e5640b0b0840d00d5414040007681c3c007034a0000d401034010a024410b240150150f02e051461440308070220155141c0130740c6078415080e091410b44034498001c0362907690425034410300802d040008005c810b2082c1d21851084589103410f02d0070400d032440251501c049a001c10402082a941d11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 609405017 1250 609403767 609403771
    0x6040f2109031b090216050f0c030303151c0302070f0f0b030a0c030b10031506090807060804031430090c0d1b0605030109202704021b060606040e 64
    0x202c128400f0380341901040c412100499800202035501c00243d0b940144440308662036418000c0b0162038056907202d8002d5103c490410490b5859001000000d9401d001100d603c2943d40e0b01508404010442a0344002ca244000d61b0640c090b07072200d10f0400c55000d2030081c000207845400540c145c502d01d400c4026000e408080c10211180e6200c003043c03203a944c401c4d4402c04e10404000c0c0607c106900041001d002025048400c40389110000008241c440c0110301d200f00f11800d990040000d286404011202c100c4082c200b01c0403c26102d294140000444024040789980320441d074110300c00040c1e44406041e4016520340f4034103400300812405943c0410040f520754800e40b0900c00200b0310b440c00e00081191904045443d0254a00110310254003c2c040d60507941c4491703041012010303101f82800810180c84620071080010040303042441c1d0410052140000c000c641200d0915001002405076001821848c13a289040300000702007000411202d83c10071401e0720b000313207040e0070003d41c08071041c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 609406267 1250 609405017 609405023
    0xf050303010e0a0b06090402090d150b040f050609041e080310210206031303090f03080a020d0504030c03150e0d03020901030f06050303030f0903070c080d0801170a14030c06040f210903 81
    0x800305c0c0b603127415217a00350500d520580c030280050307517920f2400001c8010150411b2882c011031600807a0890b04000c0d102d00350003014014018295a90360781e8036100c031647c40407081c10090103420402d0001036001c00142d8041c2c00c000380d031a41b245042901d8403081306850444400030b856800e8180015071510f81c22030303411640c0301a13040120030503802d00ba030f4402c200b07512201070000e08000005c184090140580790f039482c0355013605c0241c46501011a414080c6020107401002034440400008101031400501072246100c04248210711740135041c14030f00c40001e1400071a4001030748410070369241c400d024206039110300400149050501207a41c0340030040903035030070494442c045500c10808105a405080d0b001c40b00e10b0881d5220041c4a403140b090f0a0640c021910f84c0e000411102e0089003c1240d5054481c02440342503582d4550008441d25151842002d0004100c060340b4120203004180c442c80c09600304004035211031400b1070701c503040680a4019034152175907118815600c80000780441e50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 609407517 1250 609406267 609406271
    0x150a1a09060d1103071806050114180103021e030f041104230a02130b0d05010f030308040320070b091f02100905011e1d01110a03050a090f050303010e0a0b060904 71
    0x40c0f9000070078900003180e005036524407501d00440c80c148019801040540f0001e07070b02c2900c50349501c080c41225000d25452008403143c030b180e203007009500c80d0340584541c5c064a0030000d8401801c01c4415640c1c0e002b071710380903001040c03001000144050000808080c98054078100251070550302034072080743d49102500400a0854049039041402e43c042c7c039240303200e52002c4100507960b160751001d10760003c2e0980611504110000944c080248180070440350507484104859070782c1da404aa80e0340004614020080002000e0103008208210010280221752066540e80d20310004100d08080b201c1e0105940d100d00046015400398045240910001c41180c0803582040a14042e80540101803a0940040041c40c5400c51005150050595004002d0058100140c0420000e0a03900e1030019074040000400a0074402d61280d40310551200c130315103000030701d0840c4d03a842c98400081c220003a603ca46c4044018041800604059a08100204410064400c81002041d014055804010b206039 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 609408767 1250 609407517 609407543
    0x6010f030b0f121c0504050d08070309150504031505060d031107090c0302091c050712060204031403070308070f08180c03100c0908010b090612150a1a09060d 69
    0x180b50031142c0c001c0b1a01c028003500240b040030095507036580081e1030b04901500860814250503000e00c0071038058480240103407409660070340385c40080e0307440740400302c1c00c06c03006a0700000ca420301d8442d20b000c00c2845684440e5a2880d41c20a441280d560703086410605140c0800e100c100d5551041d0350041c0307945410100078103418401001c1c01e10241d540029511820100e40440b0140e040d40180007009086581d00c61280d0721124040c0c241e003070010b008019500c800c40605c219804480400a064851480585015120b503142a001c07003865015988550000c24041c6c10541c000d111154052140d01d41000d01011201c4020304120001c4c05d20220400d002e4112211803d0910900514540c042c0444010309c0d007050b4010001c004e101d00b480000703814121f010840ca1010700601002d800c00526181103038541100304506070f40e584002c05030714440c00046010103003040c0d4020344564200c4800051048160400d0324089a001040910584018081056a94441c0100c4600326002042c9400d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 609410017 1250 609408767 609408769
    0x521070c1a060a0603091502031f09020918040b0112030c02041a1201060b181909020903120a0c1104060f080106090e030f1b0705041a0f030606010f030b 67
    0x1400680001a11001292074082600c80c1c03180348250050900381d0b4050354080e81c82408404585c0c04c2c0300c0c01040280d050480c038111801503009950413060812107448100c0220181c8900c41c0907a910031980030740c020500c40254513040600f0202b400302c45803807220b246080d03030b00c169002034140138802240c00d508010006042c410702802050984c058010001e00e03e11888070602001c0828209120318920400200c604078180130b00c0049440b000141030401241074260309088004019282d009103160b03100345c3c10810400c203414004d0251000050f507407010740f024075007840c0070030800102200c4104000d03c032265011030307115102c1c0c0d0080004003014030300c400020090010341d441855800003400f4080380c4040103600410031102640d40800c130b01180d14030b503191171b4041e81c030340340c1c2126000b401030004a10071520300140e048000c10507203842a4481c0005000c841246101e503558003030307003250703c022810152030041c26042c044000f460382d0f29001c0002480e15140c17002910415448910140103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 609411267 1250 609410017 609410027
    0x708010b12030a030c09121109240609060d021c0c0e09060904331802090f250c03030b0a031509050a0209040501050f0f0103080703050f0702040c0207080d052107 71
    0xd050320b02421410b148423814040b02d84440c101865124070114008224500101d0302200501d580ba000b828100d051342c07508103c1d594219490203500704504001010710a10329200400c0c05101a41d1943c4a2408210206080b03440305010441071110706200d115941d52066811035201d0812201507625544926126044049503204132840c00250f552001c004548003c2010801120340410052400f003581d52000c0301403801c2000e5007203d0380d14007182244100d141e0321a80000a00c02c2101d010f41c0c005028112010064007200008000c9900081056454040c0d0b22340d14030100e816802c058119203500e0011032000b43c1c85120242c1d192000c1c02009024001c2424640e0000e04403042850a400c02c1400381c0001c4501000c02c8040b5400a154592842c100d141031b80c1d0440000c40c20426540d40907141d540c0b1007481d92608d010305000792401a0383c0c80c05a40180251036000d403204626142003a0318100640d2802d03400c1c4141840000340002200703030048103da103548a9a206620380481c01d5032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 609412517 1250 609411267 609411269
    0x12010b070f0204140a0b09130f0507080f0a0b0705030f060f011205010b0c0c0109030b2202030a05010c09050d15050703140a09022e0e03120403050708010b12030a030c09 74
    0x142041c10104681305141d00d0b20340ea28415101c0310f10074012a1100410440c06400444132500001d001802c04c0b0302040c2000d1403240300f5072148d800c031101a51920b090f68070b03100410703503141c200758000c0540004200c900d012554007c5070a04155040d400e107a072580049110040c4035602404481181000030380c4115040c031046d601c107000400507541c64100224403684101032590743c600c502528a119544651284001c50b03411150110840c2c0b143d10704143c0d080c030700e509405110b001d40c40000015036014040211400e11a600010700c4445214010300742d000d4540c8034501ca810201050030204903030900c80d41100d10440c000003010b03590f1b80825401450004030f081d40680d4064108111003180b0f41c818000b8030f00131504100001e040e00a0840c000d000d5a120b501026008887c500c40d690090401c4902420014191241c0400f40805d0341480d0b04107a005882651190404100703400d820301c645031401c007050310070504402601488650740d12882d41044101640d03400f410102c01c1c441c80140e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 609413767 1250 609412517 609412519
    0x307020c010c0c150507060e03120a0b0a0f080a020307060e010c14100501030503040306050604051510140d0204050a0e0408071407120312050703090b0621010e0115080312010b070f02 80
    0x201c03001d00c028200070071703d1b00144c00840d006450142100107a40340001910b9120400e03840141555980600c00009408100f041a410001202d00441c55140710020314000d401032000401082d0001c1c01007514144480d0b0000c001c0c04150901035403143d901907004000650046d201d0f640084020000034034100d0307101c3d02040054600000401000408402402140d0050310140311684032941040111001a680c0300c1110951a9150409081140203020f0040f200e00300024020a240410320280d07000a180c429000c0c2e0001d418000f503c1c004600001400c800803d41d54546401c0ea1910158402c440003d80484905449007102c24020041e00700904a4035403548210300940c54080c2551380f000340505500c40c148400240d80b64400e21030b0b020a540c10a80c01e00c1c65450b44014003040e14002e2014030b04e040c104500c2510750040900505022a181c0c5c000001c0d6562174604001c07005195801c4403446030420480d281c0484a1040b0960641d030080c4401070383d580c1245070802070300f0380b200300003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 609415017 1250 609413767 609413789
    0x30c02030f061006030203090c0f0301150f1a04031a0421050a03060b16030f0203090603100e010b18041812021c03020c0709050c0c100906110307020c010c0c 69
    0x1120001d1001c25118081c1c07043d070380341440e03160700c44c0d000742c0c10390200720745040c1150311448000e540307031a045442d183c0c81040500002a8440d5106044140d04210307002402c0c1018105d00402c816000850124800440c8128090800f8155520b80d013000c07180d551b0a5030b600c41c209002c242481590100035020301c001c00500034290048050141c03440d00074252031400320b450200000383c00c046060032151404074900d0140c1412000d968203803521014003001c002140f205118040c2c540d01e4032801140507070b204040c0c11858502d04403904401d540143c020b095a51f105000c0c001000c580b0340d40c00e5070a18401c50700441d03011a4508240062030700854060316a241a41c0806403203900450b5240c0c00c00c10341d4620102107507164005800342e2042c040c07190b60503440000c003000a0822540065001101081078600c0c1c215813a01b05071411042031161180c140e5117a100d03008201040c4200341d102407032942802c1c218500400d0207901c0e009800c1641e814041084141c4081081740b103c40c101070f0090041d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 609416267 1250 609415017 609415033
    0x2a20060705010b2106061002011526010b09160320090907180303110102040312120501120b01091802120c0a05040207080f0c1204090c030506040507120207030c0203 72
    0x20b80a80078006820b130250704400c1600c403411035201c400d11000c981d9880200440e8659400703109011040342c58050444d580c40d0b00f44160003040220150041a040040301986001c1641e81c2d40c40a04099240300140e261070704864085d03c0300350183c0d9100c0e010120460010040c2101980500544103001c1c080180600a06410000b1217000d0601900d0036a00c24074141d943e0300c41594401a10030000b0030440b500b0390b0400010f4403c00c05244400001030016086c10703640e50300e05284040007842100490b5040080442c1140036200c0c140c01042020480c621429007a12007541041c2d040c019440420f440e406080b0501d000c002c0729030021a030180100300c60341c070030404d407540b611200040c2500c500e00e102d0340000e461800b4025a408079421080b41da142c031b01e400f00d041d20644c1c00341e81a0281c1e406040103600c0003461460181c00100b401003401f20300d18030745940003001c42c0c9008000d103101e103180105010400c1d611003c00400548802c100607524100d6040964030028484802580340c450804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 609417517 1250 609416267 609416273
    0x2403060109091211060624040902070b16050a050a05130801021b1615110303040605060f04020a09090506010e06042d0812070204060312020d2a200607 66
    0x21050030a5400f448001e118440214412594151135000504c503036440000450035900d02030074100f0780c00384c000000c0041d03043c0f02d003410341c0740d600306501201c60a039002c2208410b010048917001c2c3d00030100510422424000600a003450049940c80d13020810080340d6a2a4a4041d80c200c555001030042d11010b069941c2418a01130341c4001d401c0d202c1e00341c41c0d0340300800b1190b000501c16201c80fa0f45000380d002c02e00784840101d0800d801c0d201c030800c21404250000540b42d051000b580182c1c00781001013a0b0703191040610500c11121500940103520420a81030038640c040c0a800c141c0c0c20410010a65845d0200100d44458191160651000c000500001c0300d0342001000310702c42e5906071100c2c0440c40d021031b200e4074103006803207044142d810085048146203048002802e8581c8020400201c40743c803a140e003180d503000203417070380e0142c0d105000940c4c6803604000d0008400702c01c4900f0f1103003602146640e80c940b44011200409050324241092880f0303159100a099009015048a85401443c2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 609418767 1250 609417517 609417521
    0x120f15020c19030210111b03070f0302150105061204060c230306150403021c1e0f0506160f0c1a190e010b010e0105160c08070f0f08062403060109 64
    0x807003100076104601c94220790b02014001c605460306e080d030006052000d034480520750585405140074060104010007800a60b00840c0d42110794001d03401410030340d4401512000103d41a085103100f420f003884081c218445000c00ea6611903400800400d0501d800c03034050303449c5605400c040381400c04440c5880c3d40c001159010718400d400071621000b803c19a40c00d038140c20f2146020180d0001c8a8460664203e20042c00801c3c0c150b2151003c28041c1c4d01c0303031000c5400078035007000c1150a0742125803a802403003810042240c0003400e0701419848a0715991024103504031801a800a011000b00311100b40450b0031071142c0500b40021841c501880c1c01840d5031034007059611207252844c40d00da41207900d2041413007010040c0d4010303140d441a0403020b000550307039508007201c0303160841142d40071000051048482903004007411002030503c0d41c2440c1490007254515000301c0300010f80f040c0200700c010000601035420000311800c500712000c200400d480400400760080703401d441110000543d5070016 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 609420017 1250 609418767 609418813
    0x21017071d09010609051005090402120106030e010507021e0a0c0608070815010c0605060d0f0507050418020f061b06190c080f0103060506040207020306040f0606120f15020c 76
    0x3201c104441d03900600300b240241c000c0c020600014040d410501c82424807030300701d0021030900d0078198184121701000034140d90044032440302c2c1a070a00010011180c05018540c08100944000d10852401004c001d41d00d40e042d1000901c91000c103144007040b640207000c0e071118035410024103001c1ca502c0c1d6401620304c0f001611800005035542340050345c03038003030b111581007441d10581d80c8000e0384c1d615450b01e4018103070203050301c1d50001c40020100300241301305e054640304512440180c00380c03d01e0501000215802c100386054400c0401041000581c0d4060340c0c0110640c1c04c451241e1149440085000700403c0130180302100d104903020321a11042840e540020425002c1d0144882e0340b5824080792050020b83d500c0900900b40070040c0006541904090b5200700080c00050805007182c000901e0700e24282c600b5140c0b05541c0074180305002030f600842024294006040076562102e9603680c04040c000c00d4003402690300d001d24090f821001d034040f180c0e008d800700101d030014814050000100c5580c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 609421267 1250 609420017 609420047
    0x140d230f100f03110604080a03110d0309080f0f0708040603060509060117070f02030d0609090b01080c0307030312090c1e0905010b090d0f080a050c0d03060b0702101707 74
    0x5068001218003200000c0c4800b500c29004012000502c1d5540c0c1404108003803503134980c000002d00010030b084c0010083c1640c898085c0e0740d01c0303041c01c04030b4116604103500900f400c0101410803c03000007060340031040301d40760a00c0030843c559840701b850202c045c41c0501d000081c0660b6000800183c00c5074184c001c0f40664208450400e081d031900401910042c039881c611003400041c0000090300d540c0030300c0384080d250b41540103992030180c046052508845c182d8000f242d001e5074501344c100038000c070541040c1c0944900001801d0b07481a074030000f60b481140307100040810510301d403c41c0c0340c00301c260840c01c0f40380c0d409251040001d4130341c1e0003090001d520310049051b0750045d010008000340603010b854100ca803400c1490b464021008240b140b00d0000d200c040e101d89002203406c00010740000010585003605981c1c2c56101d04001c16001d061000211400c000c040c104181408602d51800854040c580c2c100e45065103511800b1082d60541c1194a90000300707504a010014401d401910048081c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 609422517 1250 609421267 609421291
    0x90506040c050108130f0c0504051e01050301060621020405060409062c07110319050a0f03060501050d052a030a142208120702010b0a1401140d23 64
    0x1031560300440f2084c004840c1d039a2640310300c60150002c1040c1460710340816000e10000351b0540e403154041800c0e1141600d010620029010390060724030b00b50320b102809020110000d0015910b0140010b054111107040715100f6407001d848021110440d0303040300c0003045c0103820b007626240d0b0341900b0300c01800c07140b140d041008010f914282c01c0102d0300b241084d04000e807210720540d0b0b8540e80d8080306c454840844407103081c031007004440340c1044101000c282c655801d5460650ba280740d40b1004054800e40c20509041c5800c0c00e60900c1075030703084401c2d940740200c1c0440c009915a640c40020030f0780c0c0e034030b00e1020364101940040c550500c080b5030000c4d071003030008000900851842090f10048680c0403642e4042d40c038014410701ca12a122213800d1460180506092801c10300902510041500103403501405030703542d8506a1010304103000f00e200180600301c6030382415010940080e1190041110881000100003442c030350341c03005a40a4807219040c0c0d00d800032005204107a5490b030304d2013a18000c0d8121 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 609423767 1250 609422517 609422519
    0xf0d05030106090b09090c0d09050a0f02010908030705060f040807080304111c021f02070f12030906030b280801020d0605130501060f0509030c270a0605030c01080a0609090506040c 79
    0x100c4080460305c5104006d00f0703441e442d90341c959002c0c0094010a072105815038030385c40d911000c60810031910202c5401010030b038010341014070001d404400c840c1e0005800da007041c8402404580089501035003c8041401d12190b60344515101703210b8840d03040c00074080361300803060005012815803030a103038050a9030341426204084a41c0d01000602000085d8412455084201c014000c2044466194042c2c01240c502c4c503210407840422200d91740104485818142821003415070118164005050504080041e244641c0201e2840060f0500d1050803448c0c4044042076103024516035001080d9050003152942c4061015502810441c450a4480d04400080301c039400e0b482d1142030b040358904d0305d50b00c120080da007100b0380d00da8108102d40c9906005451904030701d501c2d8000d40305042007c40c481c42040021501d020721036402d0180451041d1850110f080c4216100018480d007402c0090a0010b0a982ca008a04020f0701664221300e5801d4100500700301003210000d400d501031407245220040b05 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 609425017 1250 609423767 609423779
    0x30b0405060609060406030216050307150f05070801060c0219090c020f0309010206040f0804030206070b0406150e010915090c0903020a120803011214010c1d0607051506030f0d0503010609 82
    0x5004070300702d0304d0b44503408200800c075150107035005000c18408191101e48100b160b03150541150440c0c00700b51180d0504080525900c01541700d88084415415400c0006083c07604008103d8981401410284402d580610055544424800c0c2082514041c00b2000d035032100b500c140070340200101305016110700d194110028034044141c1d9000d00043c0e0003444140e0b19525900180c00c00004191003480c41040040b01503116800280071042c0502090034036030400389070078000c0350b0445200e080c00f0344141c0c80912120105a03a0349045400311500801d98203604d071141401c1d444550301100c29580380a01c03541d9899040045542261f00850782c205426544030000d10700781010b10360081c40004200014031510301d101030b02112480c050a146000c0c424130b001900c1c211410b5819103000300e0600d000f1901c000c0c007800a140140c20f410344180f0b040841590303601c1d6880c400004464120408140000c07102c0c1c60070000382c80f584003a08100e600e903450807075000c1c110317600c00e018010006189880204030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 609426267 1250 609425017 609425029
    0x30c020d09150e060d0509010911030604020a090b060c06010f060305010b03010819030c0f0b010311013b03031c0506121f060506040306021908090d110319030b040506 73
    0x200ca10441c59941c0032504840100d400c0000902950350080e01405034060030381c014481c29125642a100000344a00140ae0030303900041d0300304069100380e100404000043c0c81d81301f0040105e4101c0080480c80c80c0910700003689038040d032003c1100e984a1140005145130415510108460954404206698075070001060900c400d00801e42164409034070b445040741101e005000fa5406032074000c2110740e540d604c3d1107004030240350a13a2080e800800500510010001105001c4800d00b4a01418031403090f014001e040140300511240b01c1c4402c032240c001c00d0301c410096100340c00070181e039501e91500407165041703200c602c50341c0b00300380c07908000070b52030308014007100c42007a03500004002c54205000d07603c5400080c41814001d81d900c41c079002955891f614098070145208880141c0c640d0078003002500d02034005e4001030100400d100501a00b50808901c04200f090300b45009405a00d1548026240d0b205246e00a017813010110118001d4560607481040341c0c80007290306002320744032001001700c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 609427517 1250 609426267 609426269
    0x30a150807030b0709150f0914010c0809040e01050705070c080109020609240a0306051503070e1320040e060a0510050a0318080702100305040b070f02031306030c020d09 74
    0x640c0d0384035910600c0402c41051215038000001d24100c40c400707440344d400b00e140c0100300c002d5402081c03081240d40d450581108001014026070400154001c10b44c1c1e000a00d0101412000345c401e080005104002d51140d400000910842e40001c0c807180c208800020b195038089001078910109040000c45d0182d0103004920200c1d40007801d250418038628101f06501d9514107510b420200103811040e194a44c40c0301500944106480000d041c620b0b100501c42c20105901a8206214041080000d45a0042c0c44500810f6040d207540100580c00d548200003000c00602030317101c01014641007000e4000450041096030071100c00d120158841c0e0003406440f2460340111a400411500c1218007103220390083c111002c0389280200b04960740d0041a0554451200d09035000900000c0070000e46c10010208000d000d50f900d82000180b40c01d40344c041c4074000c003400d18420070030803c0c14110800d108109548800142d2140b01d42d21036615000034000305104483c45016010300784031800f806004074030301742c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 609428767 1250 609427517 609427529
    0x24060102060a020d0b0d0507080111030610141314180f0a150515040317030108030406050f220e010603090803012610020406090906080c090c0d02070305030a15 70
    0x20380d680320195454041c1d0400040c180c040f0b40d94245c0700e1016078642410003030180c060006403c0705d90900d6205801d44000715242c80c0100810404d1050944440b03500518a1810307150048514080390b034585c3d440c0c032604681501d10050008042207d031401200c07404041011034600424031103030203100c0302e407100403a00340100c00070040006141e9800c9400c054809549030001144081d241c0380050403481e4151107224100401203804d000f041034001a00794401c101402427803c641c0f601d15415503911560094408010340807030204101c0710340400380d0b48000020b00d4941d500c84460200c50750048642e1269240710b4a081c80009180e90007880b0b4101602e030005101c1c1c0c03075a82015500c031b20188040c1c00b2107849500781954110088403e00c14403481401710500560b80e10b00c1d2420007011500f0540013403160b41d261090401c040b280c000b980817062441582c26a90b0b03681e8180904541d400b40f040c0c54240c003400080c1460401d9848001180f041903641e6080115280580100f640010140a50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 609430017 1250 609428767 609428773
    0x90d090608070815040e0709090c0f12031112030c0a03050c040506121302060c03130e011203110a0c08070e13050304030327030c031203091203020f040909030224060102 74
    0x131030900000c03a440540c40041c044c00110700316004d8050a460904190302c18010203a5500b803444c1040000c2d10b40100401c444030300f0070b41e81ea080241ca080480d00740c15005041c082614640890f220050058400390a401c0f806140ca9142c200403246444d485621181c0c002498240000d02c602041003c1c2d030160703074002d08081d042c40c06224800110300e00107070071203101c05480030401c03005030390b1035000702aaa0100405161035000340c064030071401105070030000ca0403010800510103481108580100309405250803008115040c040c10b08000d10000083d2000185240c041480030000449000710389800349112101e54030312003203c03c0302202e0200180150403c00c0304001181c413442c40e00003044800c860340142c1c0c440d80a810050244582c0c07044443c034501070750403c280040c082000d104003849080c140f260a4007962542403100070342014405041e0301040d8441440c0c07007001a10094880404200000c681606000c0d6075298136038619080250364500300c482e90001d8800e814007503d01a001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 609431267 1250 609430017 609430021
    0x30103030206090f1b040605030303010b0415081905060409051002041503020f0f03041506081e010b0f1011060a0515010203190309032705010e011b14070e090d0906080708 75
    0x10400f00007a00c8030917154400e44450000c140caa509200440c020055814140d95481c07030182c0f0700c07110480318251203051000301c504001c98400062040c2c6800c00a101c0e0004072542c40a00080052001d4500a0000d03c04c880c40c2c6607554005600a10654100b00c0104c0840c0d4601d2108900303078429445400d40007070040c012801e440390030274040c603007151003400190081c04028a05104403101c41c1c3c8a12402d030300c003410742800c0c007120080e1400c0c0c80546d44024445401d4a402160844d1000d02a060103140c40e18000740b0b2103480b80001540c2480103200382da4142c100695000c02602c0241c8100151003800c03034a40d0380c00d40c00003044800c6081520510581d07590020800d4000300001c1304241c041c0544003a418032000c3c110036050b440c022034050104521404c080005051103030b0083d800303040c003541003080c1c0c1c44d80d1000c1d010b0140c011b81c0429640ca03e12800460399052181c994000d150000000041c4102c080c80412004000020707503444d80101a82c8800c2241c1c2241d05407910008101c0c1d40b00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 609432517 1250 609431267 609431293
    0x30c0109030605070314070309170405090f150303120105040b0f0a03060e0703061805101104122102060f07020d0e010305060411040b0915070305040b1605070308030103030206090f 79
    0xc0754130443c0c03820b000030900541c80d80729400d5a012620038000903918044031040000d10382600c52141040a8468203050401001c03900e001400351182070311640d2500000c03591590125200700f0860040d00b0381c0e07124400d5500c00481e2403020f00640b4030840c20b1180d0f821190400da210b0b56050740004004450051440d140c200003000000c0340c8200e00d002e0544084040f0702e003409681180400c4000031801c9070083d0404078208210340062610190030288044180c90900080d9000c1d200050302e01407101800d45020119040c940101c20000f00400c9100c03400c1e42d8020460a1180704038240c200c03c15500c807602240c444d01c138800c10030045100341640303040c0355100b584859030000c8058800141e5104903814540c141e0026800340300041000104c144031801c2880c03070002403c4600c10100c2c2000c0b050b40d00600207016901030218204004540c6110550303046010241094010040c5ea120603107030304240542d07a000b404160054400e90000c00d9005030000788404c20300e03144101418000d49802 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 609433767 1250 609432517 609432521
    0xf2e050417010c0f0c0c270b0d0c061d040f0204150305071b15092303160305070813030c030b1f06080901020f0c060106030e03070c05090a0207060c110606030c01090306 74
    0x15003c0c6d601560034240442c2e00c4800c0c1c03e00104040071070441d001c40d104000d42003810354103c4106203025145030071011000401d282c840c0800d6a5181c10645a43c00700c849031070507248000507156600034244201711101013407035030041c026034410b980b01082e04202500160182ca5043d6410000503070911000c1a05150b9220710f00f01c3c030f40c4a11001d0384510000c001100c01c0c1d4084e494240c4160100c0e1420744400b0030001e40c1c2d41140c0b244c690203181050381d00441e0420b00560307000b010f8107212000800e1010000400f003251807000d80d101c81038004545034209040038810501045843c019070f0030208204040d40c03030024104c3c2d038031a20101d130b400d170802504841d9500040c140c036206640a0100c3c0c20b4806d07225001d0b219049400e00140030940c542076000f4141c1d10242c3c0f07511030300d400070004100800e0846d03403443c00f512001c1e542010207407901a4800000c0c490500b0240c541071411304c9040010750321044031020707540f03050200da540e40c40b260109038076101851070711b81c042404c403c0c0420000f00345d0707 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 609435017 1250 609433767 609433787
    0x509060a030f020c0616021204030605060307051302030a0b1518010e030a0b060306010902030106090b28020102120901020a02100504060e070803071a060f2e050417010c0f 75
    0x20726011031031019002071901680c12684104031281c10075000c010b201c40841024100350b810030b2000305070040380030320808070510035400003901c500c1d03d032070005440351810040c4800901010786207417444031100b1100c2009401c160740c0300840318100303162331046141a801e03131461021580942407a081c0420803841d6041280201f060610180d80c0c6a0050b9030f600703000c00b110f2640200d04001c41441c04a080609100c016000709941c1807061005200a6a20140d00c10a49900001550b900c00e0b05074030003e0700e1605a074280300481c01c5000c080130300320b5040d0007600386010b009041c00b40d00e0321640500d034240e024030001d1400503400440c803008040390035048550043d0040c58000389003450281210304088403a040100c690b40000b851200f0170004094000c0940c460842d07102d2503007070540004000e500f00030b0209105809403219644c1030030016000d00c400300e040e0720f400c0e40c0f61014030501600b82c2d00203105144250b61881c03244070700704c201801035828001d62a510350140d403401c0801075540d9020 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 609436267 1250 609435017 609435037
    0x5010606080709090b22200a02031902030f040b04060e1e06071e0c210b060909010f0f0b12070b0d05040c0305061e1f03081c0f09030207050d03050906 66
    0xa1100e4041c2c091804008205211301c8800803846003100e80300000c0054a10320001200c034800c108010550782d010042d0b0350103628005da507050b0164104bc0481c5140a1141c21513540000002d0014100d4020001007044a40e103071909200c40c6034000400c00d4441d17003000151050403204071004140e14246005000c0c29200c1c0b14003c000705500e0306034081c1440600c0085801f00e144a10034800fa82c404100d0019007000c10041211245050780e4244951101401c0103018040c42c1000c140355190a40051b201d0b41e0000d0002c102d803404048103140074140000c2114000d114042081c00441804990041650a15045645400603421900c002040000d2098071541c0741004040000341041c06010300680303003180800d050000d4500b80d00382c0031130094240c1c0401c00c0d003080102d0061854403206030407030f6080503140352900261032480c00d4124080c0e046010b620310301003d214000205902220841c4d00aa0850700c51513110410320048140c042c40140c040792044c05400030602d880e200600720541 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 609437517 1250 609436267 609436279
    0x3010303140306031e120f0301030203011503050d050307031d15010b04080c12070b0309011a040207151d0109031205181b061603050d05060619030e070e01060c05010606080709090b 79
    0x41b494480c00016000344003035094003c0008010000c0d407a00b4010010032940c005841c01c040d43c69030780d5080c1d0f01e0f428150404107011000c0300007203c1500a90287d102c4002c0d40311406100058000026141c1c80000344450f00c01600500106090a00e170301682c003561018001883e08000010400c010801c90001d205a6803080400215044184d680514011600c030b50000c25500300003000302541d03001a405540c040d51041c1300c41d01c081410780d070320042000302058002612034804c41d240088480c05c1c01c0700711010343c00c00030314100b0513a200e02401d0340d2248003102003160362100382504c0d07524030f90819916041ea00a00c242d060342c9030f16220403020060002d200034542242d0340d1200c0342d94164464198007040000c43c140c41c82580c103011300f50b84a9400c4032418500000800700c60018080c80300304004050369440e00b2210341008003c01c401034024450300300079640c0d40b000000c00d48001c80004036840d5090503000a0514010340380700d4000e41154486541e003504002031440140300803859194000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 609438767 1250 609437517 609437533
    0xe06040302090c1b031b0309010e060310030b27010b010c1203020d14010815060a14031603060e1501060c0b07030f1109190506071b0b0309010203010303140306031e 72
    0x240c1d00c0c0b0780310000c61404d40f010b180ca038100c40c00c0440761074010340d500c1100d0750810016560507aa100124044801d800c803900ca481e80c41d400300c9580c2210311030300010042e055002c1848071105880c910b44152807441e543c200b5a0054804407075003690742c05110540498205a000b00001c2d40342c21110300840369516005080058140c200016540c0d50100780c0481102c0ca0018460301e8401c3c4110320421004210680c040e0a144000c40c0e460394440c03107020300d100c0306443c10200076541400150f1412003101d01c10f00300e6503124200080103003150300c00645140708030500d043c603028201c81c102d4100c40894460201503015607c40900ea400020300c40d40801d0340d00c5030300102c4000c1c0d52040034803495401c2001c644912460b418090102107808184044582c040410416035403200122040310b90300c010000103440c90644414940d090a4010b082e8200c0d010040242c00807055000e541207d000e982c40014540040c14022964881991150340581090348000c01c200c0d400b500030030100e6041801c40b0900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 609440017 1250 609438767 609438787
    0x10b0117012c0103030f0e0102030307091806080102041827030e010302091e0111280201110a0b040203070f12110f181806250e0904061b0e06040302090c 67
    0x7000b42600114041900c107591840c0303441c0c0c42910150000000e00046203541411840500040c00c24441d00c1032403560b004000e108410580c000c04001c2407248000e5484503100c240f005000401e40c25920b951520704600c0015140b01d006100d070004144000d61440201c040c6c808680ca4080c3c0c06e01141459002c20420685440b8840c001a00c00c0c2d500c0c1b0002009540300300014030001c0e00c1074801520360700640e0030700e403440030f207180030002a580b036840000308441c1c42c030050314288081c02031a8014020f0024020920100ca81094441c40c422811780c0c0b581c46d154800d40c45202c030b050041080056440508800040c81d10200c00c0c04604001e080345503003414540010b00d01c07403c200c1d010740400403a109120040300c150f20744088888840740076003a946040e03150b0900800f01c039a003240b80328200a175288a0180503031030000070f030807000d40080107515190520f203004e081280b000780c01d601d0804101c5004140b01da051511001c400500c183e2070145150208034650710f01818915030400d04101703440310 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 609441267 1250 609440017 609440099
    0xa14030703050402010f0f020c01110a050f030c0c0108070e040b13020c010b0f0315041b051009030515040b130201090b0d051b03010e07110a061508010b011701 70
    0x400c40d4103680201c1c4514042c800141340303031500b2a100f4280042940e00102c15174004c9101011500c0a281545600c08082000ca140c000d01246c0500070f80606003071144466800f00080445110510840d0740c1c0352440b100441c0c8032781c0119500c600040c4c00000d05200c40c50a80c00001141d43c00411400e8a24054440c400c201c5c1e00c90611f4031007517992907541c8619801c1490316140c010070104c003d005605451101002c42817002440200000d40c0c0000c4150f450080301c0b4444003502c0301812080f00707032050343d0014120200502094440c0d1080030140d8908841c80e103d040c1c4140c2d0b10a05160742600c1703c0c0040b800d8a02182c8080741400307452200402c10124031005850f50341401d201c0440c0ca81420420f0003030039020303d02c0c0328840a01c00c00050114442c00c00394250024202d103484086140072480880c20700d1591940248042c1c1008004032036000c3c0c4034034200030384072400020003040f4400c20040da09101040403120030b040445004000034884418007516101c400d501c0342010f0721004054042c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 609442517 1250 609441267 609441271
    0x209010f2102211b09010b0d020918040b010f24211a1009030b070e04090803100315020901020a020d0602070f0c0810020f03060d02130f02221a0a1403 66
    0x40ca9100c1030030380ba1911309002111840a100b03442d81c10040d41007044462082c414840411417180d000030b120300310750f1101050315a4191782c212070300c1c4407420540780c03480b8140028852403412042c02400403405441c242c201da8050504009050017040d2440000d5800701d90002c00700130480c020120540c40d41c881c03070251081050a4155245010900c201040514000400e24004100001c2000c0c000501e82071407094210100b81007a80018401c8000070700904110a402005041d020003072110b0594201501c1040e244106150001c0c4000c480c540004c901030b503c403080c011b0b40082010005410b040b0b042001c0640554400b51400340580c41c1c00d070110748428030481e040c1f46801420002c407801400785600401d903070766056142080405040c2eaa43c0000380030b4920950346010b880c03085555441c0c6524403200031000601400d20314209800003500181c61800d0361301c540c60212200c0112200c45ea1055a05518412044109011f9610290f4000c1c05812041c8240c2c80c104c105c41c0503c440240d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 609443767 1250 609442517 609442579
    0x20105040906062001021c0b0f0d03030920030307030c05160303273203190303050108030a0206010e070c3c02060a03020d0f060e01030209010f2102 65
    0x19501c01c9244d0000e001c8149051154100d92040c4645c071801410f00f00d601c40c1c0740850180c003290701c8130940009454143d050034195448000340c0b0303804041541640000c4c007007600420b00b030b401e00303100060126081c401004400758175070010810200060300888000a1160085c81160416003e01a1011040149230010740104641a000c400b0110703032801207070305410010030614289450400e02243e0a681380e030001ea6502039544040310440e070462458218104018103e41e500422028800103c101081c41a4000b80c103103000070803402d100104840d041040c550082070300fa0f28000381140001d00141c00c2200b000b501251400c041359241140c1c19520084080c03110b091092a682c1c2005000c4001e1000c203075100803103114016076140c00696100421071705016990350210494980248072050000343c04c03070310f4a40d010518079501c2d00d20078141c1e4801e0700c0050300769807991b140c1e5445090034803402c4c0d028891860940c0743c4154001c0000c0035a40f016204540418400a100783c507880c0c800991 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 609445017 1250 609443767 609443777
    0x60c03030b04060608090717031911011409011104030203030a050c0703141006080f120309030706090620030f04060b1f08090106050a050306040210050708030c0c060601031a0d02010504090606 84
    0x44882501b090103a01e00030f00c00446c4919201e40c0d9404525107070f008038a148144c030081040b40c036040a00031610200803102e030100030429109044003140c10b000c3c09450900701da41c40c09107003018125140007214103694005000358240308150344210b605a01ca0881d050560103000c0001000074800004a5811140d060181040c07200b100d00407012651240c1c0b02017443e601155100e0317154031005c11aa01e0154003041b04030b0362913a1b01c506562540c441d406000741054908074810007406000e40c03140000c0300c2d041900c441300003809800c1c40351a000c15250748900042c03940110740000c0403688070070407400740a45921640708504c0259202069030001040c04108400d040044821081c8540f00c0a4181100d45548203400d000100e542d41c0c500501c000e002c0d0040c5000100c80c40d000c2e4003602c0480364409049030392450030801181c02504200c0340c0c10424410100440c50660082c064400220711182c5c00ea002c1c802c0410820010010341e40e42a81400000c10010951403400d00864000d01502c0d00c0e5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 609446267 1250 609445017 609445021
    0x70b1315021903060b270d03020307060c0315180906050405010b04050903040b040315090f0c0e1e060906010e03030a090807120b06150f040608060108090106060504060c03030b04060608 81
    0x142d02c80c000c02c0b0659450416140020074000c6880400a8445070303061031040000603480700454030500783c16000610342c0a040c5140c1002051703030010003052070503c41c0c2c2c0240100541d81c802a020380b0112400c0700401018a10240038802c00382400c415058040c1c400031400c41d0464880070115203040c0c07810340701651180200c1c000c0c0d013014044c1c590000100c0008510700703840c01304000494022408001e201400001e0301c40c18008094010407151a0410007105082003030745007030711a520181c0f0418020820b240300248030403080003106482c1d00e062802e810348990741c110420002d054010006810b101107601d4120a07510104081c00d070503980c544036480218240110580340114550040302c05660f0000100b00040f0f044010580010050795601c3c0d007170b030350b40f02c0a0389503002e11805c580301d005001c50300040155002e100f00d80561000e072108080c5d908c40120903800e1b03c0c002d000c5e200205400b00400c11216200b5111140014020f207000501c8280ca0000102aa0550340c80540054071801c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 609447517 1250 609446267 609446287
    0x31407020603040b06090f090d05090109210b0f090a030e2706210c0f0a08010c03020d050106020f0718020409090503070b090a050c06030c070510090323070b131502 72
    0x201b81d9000820051140018900907000c1951124000d104c08200940404c0301404e590003282224094200da0201d40e8000d1040c1e000500c003902c44420035030f541e8030803902041c24034013250085805806003101900400202ea00c1c01d4800c6c1c910400d80366040280303401c540003041d0b8100c0000034120342e01c159140090030b10f0001c101c03040602c1010700004407880d000648003110001b03a4125907180030380d119480240c04000290800301241d04c281515403d0544501c1125030660052441207400801007220b66240c0c1002c036030f034414900c008002c42d4011102070240921290b0102400d601d81c100140c82c1c15100d06018080d40c0010200311583e0b4008998074003005048100b0503440080300c0010310184540d44c41d041c0d40c1c0c00540c0742c0c490240307100101081000041c0000c1300c6c507141d04041141c03121160b200000d00181402c0400350001004003100c42c800d610f00890103440300d40c103601407905218068a64114441018107042210318004805c0d10000740c4980c0c4004280b4000100145c40d002815 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 609448767 1250 609447517 609447529
    0x702220911011d1806123304050604061104050d050307230d05031b07050604110a0605090411130308040e1018150f150215060a03031407020603040b06 66
    0x1014180f000c03c21500d0250702c40e101d00403100ca011500a05521140e00e03541c02088542c482c000c1d4100c3c2500407035108008003034642e90041d0150460075042c490082200005e15031800c0f0070380d00100103403c280085008200b060708603100d480394181c8842e241ca591032001604503500100e003220039800c08507080e014820303281d040c080d0508003480400c171869440308040361203010380074065043c00380110108203410000300342065007000c0d0040690740c0e9074050901742e542d400101d904982105a0312000c1c07440d410320381c0d00c0388200c401c903840c0c590130000c64108000140c800c40c0d608041160040c04000e6404c0303241e03c20b5100950040307291316501d0303050012800780040018003510141942c50003c002c2c0c41098141d80ca03005000d0200015000040c01460030b070071009a1151510035480d000120306004031000b840d04450181e021249000c00400c48141c0300d42084542c1030b440754202104202003401a5140c2082084011065241002039070001e07150350000e85050b40c21a000800b004020b040c54 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 609450017 1250 609448767 609448787
    0x3040612050c031027020706060e07110309010c0f0203060c0a180305030a0804081b0606191a0c10020c1b0d0c0b0d150308030405061b070222091101 65
    0x1503030030146186040042c94190421031710a43e10220840b4032909443c00568a0941000c004000705541c0c9100303a040c210083d201500904400219600126001078003600c0602c0b40c1510882c0518100070b0b1001c01503030520712644041c1c0302078529559000050b5030911040313219244810303c041c0c8410700310200512a030100d440f91401100c00c604140042403000041d80d100c03403114a40303020181d03070358030307000d18240140740c00640b1001900b032707d8104010300810b4440c801e11003900d41386880079001010410b004c0b624401c8018040492080c0d000c4a0410700081c11850440ca003102d83c041940947c000883e408a80701000d035030800c01e40c0060719410500c414091750002c841c55460f50969840c0c44404007020f21030b207001c0c444005209550388521ba00410365182e81040b40701e007d01d44d07900306820158401c5500700c986008100000d01c00081700c40031403c1d4a5100039225060418a90a200000d404850000703202e00c660190181c1740003480c005c65154500c522130b80003412100c2400900790080f8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 609451267 1250 609450017 609450031
    0xa09021305040e0109060b0d030507171c0506031902060d2301080a020907032a201b12120703020703020901180c0e013204060c120804031d040e0304061205 68
    0x122340d01500100398401e098546003900011010100a4100c01c11560b6100b41c001410030301100c11000105010b4542c0704a109002c1238064400da42412140401d000c2c0d02210000e42c0440144a03a28155120754040208840a0903d4000d5848a1030603402c100310260f02501c01380d4800c006010850a1181119030080355900f0140050742c80c10fa4003441d410640300600d0301c1c03a0302805081c0704491040c419022600161341440d4041201016000d03105d82c60882c850012015840200c5914200000d05180744004e80001c0e21108518001c4503095a000810903801c5124a80022000d650740d074040500910307420a90345035811003045840d0a5804d052404000d2216014502c00d1590300000c4024108880c422116079005100280141c058000e901101c002000402c2c08200e0a400c41d4050180500600e0100741d135a030b811804a40d2050112030080001d5400c11404100e07002000f41c4c10100480180701050f010100b12400d407860b04550300820008140380c14107080115988140d0fa04061 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 609452517 1250 609451267 609451279
    0x609070501050a09150210020d0c35070c020916080a0605150f1308031e040521030903011a0a05040e1c050c030310050f0306060a09021305040e0109060b 67
    0x1c3c0040c0203004540180700d07088400c2144115203078207500c203224401014440c0102192a05101088070000f09944104c001c08502c3c801d0b00300c801c0c1c0d03c05c1c40101e40c0c0726440e00c0c59a8a01d001e034145400d03442e003020302490280160411507034016a11103200a201e0b00301000103001c400c440450003003601802a1207061000e240880602140d10f6201c04400f0f030411103000075690300940494101c080c4100c94814401302c041a601095000004c030007801a507040e04400781c0340c0c113059000003c8520a500c901a4800e44260441007203c090500c800c400d094081c06403802c04007a00082800e5840e00d00b422101005400c196189529041c40d500c000b0300401e480800c0500d070100c40c1075130b451100c0281c0e804c041c00c540e58801200f500c941c045524005128095a0f100c1c0ac1c403001d0000c0803201c40c003426100d104400385080c0c2c079003070000c0d4031072042c54001d001041c144c0c0f40c015600000e502c40010380140e251110404581074a550040320707400521400000340420050400108540e82e6001c00b61140d8 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 609453767 1250 609452517 609452527
    0xa030f09051c1712010f1d0f0f07140a030c03051303080406050603071e08060a020c0a0f02040609060b03010f08070312081e040605090c19030f150e060907050105 71
    0x42000154000c0b05a2203280e1009542c90900c804801c1d01903c0302036107840b0701d084000f0500051019800d41102d00045035560408a101001061b842c411103551294111a4000501078035290024507000802c0d810b11101c2890085104811a4400390200c4042600d07194003100c103d9040c480c0640c07111405907465106142698020710715040940050703c082c1c0c842020420a03602030104000810000300442c24001c1071a446081500440c80340c0255400b948001480900c414003c54185036601030260004000035902d0100c1d01540c0403007a0381140d0348000c003084081d0103200d04405032120700039882d00d81d807401d0301d4901603c8a070b80203484103800011040002504400e15201a0b4150741810748090f0b481c2c1c642d11100021140da1044e083c2d8101003400140485035122a004102141c00c1e102d01481c1d0509021844c1000b8100d001500b01a000803c003084250b48051043c84c880e152420003200002030400581e0120409050f00d9080f00080c44001e400410030384005040038200b082c104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 609455017 1250 609453767 609453799
    0x30209030d140f12010306140106090312020f031602031006030503030f0405191202060a05010605041502071e08061e130f12050d11030c0a0e060c0a030f0905 69
    0xc400e4981c075481031003625581d001c2c11011400030760307841c801e5680c412038840c815607078075030b10001003840103880c01881c004e6115050f0810403801410385500f5150044454656501c2007000800ea40410003180100409040d00010610091050300d95110800e0048140b90040609100c0405000c0004a107401000c00008801209680c1c2c0320101041203da07a58940c00e046051051a440c56225403048821040401c006021203594002840d82160a1642c0c1e0801f0700044070428002d00000c200c060000b001003044814965006a202d8810748031401c0c4d6840281501c80c04203429540c40c05079040e0107110015003044469413001d00c422074440700107241c00145680348405401e41d40c01c40703001e14201082c440911900904298800154002c0c03061460000301150410001c2e44181800d2040c1d03a41c0414180003924028070081107454505000d002098414040384044960040001d02c0000d4103480e083c48001300083c0203840792116900742280041185102c0d4012600c0344800781409510 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 609456267 1250 609455017 609455023
    0x4031d01091809021c06050103061407020718090f050d0206091b10030603121805040e100f0605030304030b01060f05040b1e0d06170601170316080409060801021903020903 75
    0x141c540c20b010000754240e228004126408607451506200401e1281100c040104c10340c48641268061402041609c1c04081c00c0b0001040035510f11006034080d1105228640400c034a81c035070010070040025020001da0741b080c0050303000c0c8030260784903013100d101240443d4050200340e40c07006000b030180101c1d528005a14200c045a004031600400380d0004454000d4041da2080780950340224130195481c0c0104c000810485840450003120111410001071600b40313070207020b0041451002400703500c0100388120b40108500104007241c0d9480710340002c0c45071030900042002d58050100401d80d03605001c005095408078241c00300800508100811001b5980380c10f4541851441008802c01c04400074941c0050044165000754941340c10000a941c5001e51000c3c1400314134132040d0350740c1e40c0e601c9080141d00b44200110001d03941040240308150a030240ca00c0c802c9034482d0032000d04290303c40c4070010855040340c104100c1c917940002d88070a58581403407190190300051609500c2c0000c00c0b400309803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 609457517 1250 609456267 609456299
    0xc120807020721020f100c021e1c0b0907140d061104080309031011040314030409050a0902190305120903071a0406080709050a0b091804031d0109 64
    0x4109005012030265442440b0020082101480c0d000c0700c1c41c00b00c0c0801d201c0d8002010101c2c8038a90201d100e080724200014402900c0810740c6032040807030115000e02c184408100c10010514084699840f01552060312818000301c0070044c0c0c078044100c500d4200e03000d02000d0500e01d1140c0c412a0200108aa000380798020b000302a5908485c2884629250014000504641c941d26138041000315890400101400d2003050840442d0480500150141f04a94242011806594080005001242e4200807405c5e480000b40100c034070300399891010300300301ca0003511112200b03611885c00300c0a51902076424081141200300c0060300310305e91380d5025a1900400c409070200c010115000300c181ea81408110000c000600c40700c0b440540c41800a4010b80c045e0050102081111000c2a070343d6103d5880e038820f5610127840119110f0800303c100d01d107034100c94103440d80400030303042116101800d45805400b480c0f01741c0760200041600c1148501c01c40c0a10411790400003446404c00800110710a026 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 609458767 1250 609457517 609457553
    0xc08011a03150f0315091f1406060a1809140f070c12030b0d120f090803041404290a1a0706050c19080703110a020a020907030204120605160c 62
    0x212603200c1c40f001c03d04289030381e00389079808104441002007a400100d00801c0b040d501c1a141516400c02d05030120456490340380c117a0075a202240020020700300b81000300131441180c103104c07607030b10210410300c0740f5506035410110303d02e602e03024200c05c40118280450341104003108100840d25100c1001004007507444d001411001d500b10354884c0e82d600136880010300d01d501074816070b28071550303040215050000403840c00001da01c075001441254492002c003420b8030021800b96240514115800340c00840004507180e2081c1e481800000105d41200c0100f518801d5200050401d8886010460114a03603440076002102c5842038102d00c04107201190001940000c000070f050300e403002c0c0041c0c0d41c00740016525244c1d003081c030a4882c040d040ba9000d4490b018035501445001e01c1d10722052014003600c01104096800304500c080146001c680e4194032420a250050816980c0d250404501111410a0f500d5665a40031300c24982c900482c0c92100180e6800c02c14404501a5510925100703911811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 609460017 1250 609458767 609458779
    0xc010b0f060a21020408011811010c0f26180a0e06010c020d0822210803040b09120406050c060a060509010b1b01020a2f030d09060f0c08011a0315 64
    0x11210b00e010f00c2d8162005016800020031900d0b0344400145210062920151070300e040d056260307640d66100d410b000c0c03102584070b940c0800f80340b120380c6d44a40e02d204c40407159000d9580310034001d50710103107070014114409028408515040d841c40921601c004541c22110402980800308440c50740c10070801c0b8011076041e13940e14084802c07810601c04502598101d40c0b44d0800b260381a404480c60801a40305448c01e08176014011141401c0c10303030306150f06410052211a00f4800140414040e05800783c0c40306001d42038a014807078100280c0165442a000840411800300f130303988900e6410006a680700141c902c0400040b03083c00c0000e0302414052080e96001c01000810341d2031540c0000f56030b10401c880320000e644417100071401510600c20f25401d038800c1010b1124802850140508281002051001640ca00211502ea81018100209094507015200c0c101502410300d00c0c85240038a500320760341d18180d54100680d560a2100c40701c8415030882d0140709000726005010000e03005c2c83c07021126 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 609461267 1250 609460017 609460067
    0x1508061c06060302060409050f0c072f0a0b03160503090c2412040b0606130501300c0f090303080105060315030f1b0616020d020d080c010b0f060a 64
    0x1c04000b604007074100a4122001007000103c00f86a500181c0c0207c80c10b4441161035512292213074020f002d00400a0f0503140f25203036164013500c018261002011b1400e400544000318080411808a06d81c2d0000b401450004108180d42e84e009002d140c41d19014070700070303103981048400d066882c440c50a940b03200fa60003105800ca40b205041e00340c40a000669415074540f4070010b84c0c244060b40841c0c2c1659109041c50000d841391034014201c50b40510224903a002707180c1481d00455030800c0c18038402e01c0714907848480c0348644010507191040069164000300c0c000d41c00581c01010101d411052100380201080240006034100300000d0544034140e43c0c0540329a07806140485800c0e0355034109806014868030300200030000325440c0c0301c1a10b030380e20b5803819810b01401d00c1858801c0b42c0391203083d2056100d41000502d821810845070364001010400c00c0003031030b00c40c04807680c0442c0304da015a80d5217454200e07140c18401104101c100302102d085007000c01155014101d9180d411682035086401e0034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 609462517 1250 609461267 609461273
    0x2090105120f070b0a030609050f04061d010f060f0510050301030303020c120406050703020d1404050d080903010203130b070c0b01060c030c0506070509041409120315191508061c 78
    0x2041160080e204003c6945030369991440b1012984407030400400a400c0a8010030646030a020f240d024001c5811407941d50361341c81d1200d00c010503c0c0070030300300d00940301c4440401501c0c003401400031501481c040055624034258910800b4046070f4000c0d4018110404540d0b140c68109003070707a0442c0d405090251340e801241240c103040c0103940c2048606584085408503e80382d201c1e0280110314400e4003120215010520140c9950503030b4034408000e54810002070005042010203218030354401d250480c20409410b0020b800e981003210b03e000c1e0b81e0b8010400c0700c113000c1c02e6a102d41c0c00a1540c20920100e10035a2038540c40100140180400d00904a100000701071152440c0c4200513001016034009042440c0c0040c003c0c2c0c00b00710921301c0b90f070070464028008005141814010006840201000746900c9070305595500003c045c48074070741c4104540089138803045900020317003401841c081080c0c0d0a0120001280200164901c10000840e00b00007107915090300208600140300c40302442c3e00e025207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 609463767 1250 609462517 609462523
    0x402060c0109080a0324031203150e0112210504061b140105100f0b030106031e0908030a1d07030b10030c0e3c180a050c0406060c0209010512 62
    0x550001c03c142e40000d110720702c0943c9940524011201c80a040c1e0406070000395051a16005000103021440001240f0f140309000744e1000d480c106104081c0c0c0b040e80c1e03407982d0210b0010000d9010705582d0783d8840426041009012070400c001082400094041151100c020003a005034054502803014100201070305501c1400280061944985980b07103420640303003954041d1805850016007003114283c08903203240c80200303050981c0c210002c0203095a1074640110081c00d03601d0b08100410752050907584046005005000302ea6018035179640d50b03400c00e030000101300c1e8038104440503c904003d07111110302c40c0c04959201181c0e000450018181c6481603510081415a4030050010b4075030036000070b400c0c8040544134410041745544501c240b83d4154204000c4c106101d041d0034081d8070109030000a20b280c01201e40000400000d4400345800310100ea103809050350058a00e0390114030150b00f070780b0302402090080d20b00e9190841c0c0030080307079004c2403001c081030150030b108880075021360010804c10 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 609465017 1250 609463767 609463781
    0xa0b070b070507020d1b060c0f1704030510050106080a092102010e0a03110d2d0c0f061d19060f0902030a080a022506030915050c041706010501080402060c01 69
    0x40c117048403010035140c800020000c9480c00345030420014000964140a019080d00c4590003000e080302d0021146d45480d8804803500c2d490320000000e2001001040b02000790f98210302d615640021107505014000c0c0c401d102c02409800b6460074500c110740011025001c0305081e06048981d501440d185990990241c503204a034285a031041da620b4a00303240d445000000d4401d00710064406055030f0340320865200241c1481c240b0224032100c40c425000d003c0d001c0d0a0507050003803804041d031503001d9448403140c3c00c0603101507601d99210620440d0381152608101c0724220a00700030040f61040800c15803e0204500025000540c2d49034014190b985035045a8500c540c01000d60720b400740c00f80741214154000004440044c42005803c0343d14008011007400d01c00c4141c2074101c40b580c035020044014144841080f170312400c0e001a5501e800d81039020b4a402007080c40a441d84860924490b1050810039803c0840594808001000f090341c0000b0625001b64040d41c1e40c96517181c0030304a0a01510003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 609466267 1250 609465017 609465019
    0x90d060b060c0a03090b09030c091302210f0c0108060d020411070602040e0c040303020703290c0307020d030221100b0f1b010b15180603090c01020c0a0b070b07050702 73
    0x60b0090145404140e016400703201c2e46803403c58a4070340e0315032005030040c1c828007905030744202c100c1c3c603091a2224401c2d501404100e158003903440c0b00c0d404a0700040724484500840341c8002c2203c0d81d148001d115001004d5440d100410034001d50100080030550040c00b02e5024001000148003991a0798101d94aa8008032032415640e8009207007480007580607100b040142c91182c004101071b51030080445080381e415034002c00a150468a421340306400001c001007014000c04440000b51003940c0041b44106c00c3c114a6645900d000200a420300270451501e5040510402502d21a410b5842d1410010390140c26800c0c102d50b6520b140c400e4900d0f140e00220403020020840d410000003040040440c1800000f042c4e00c1108142e409038241c8100d05030107507115070f42d1405540c1e10344e60a00904082000c0482081802103210081340b180c0e882030301c614500341c002d41c2e80303441036507010890b900da492819540e0071002e40c900b0405a0b1140201e07403008007100340720740114075030754400c1c801d403206203070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 609467517 1250 609466267 609466279
    0xf0103060b061e03090c18070e0d1e030e10020619060b07110a0504090f110a1505030a06062a020307032a090b0102030a2f060f06060301050105090d060b 67
    0x4034100718141d81c2d00210b90717038602e52090500340521030800080d840c0010142d800c0b80390080d00d07603110554044d20642c072200c0d00b000a007480c034004102c0300312400100002c03080c0d1041d1000f00302d0030001c16144803413040c98000d40244882e00f4103d0713170020b100c1c1c0d8080d666070492800c4408006850002e4480f0398001418141c1c04240c003030620100c1a6801707001c0408035074400801e80c0d904280301c255001da084c003a000c40d8840c00342d000490349c62007007071510f40002001c007031b00ca603103e2442148d0510424051000150f003c003c02c2030550071840785401515a9081c610207a141003140e0b80004801c0042d2240000050a14403045483c1000305401442c0e0041520402080802d0765a0b4040d102420308a18050711002c0000c4100031445503a01e8524103030f003e5450f142d8440c2054641c01c070242c43c0c512100702007000c20042c100540300e0300124652075601811a90502c4820302c0c0480c440905680c0c403800c0c0c01c00040040c0e80c2c0000031035000c1d92080d9a883d4a0660b03c0c10004020003001c441c60340c0001c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 609468767 1250 609467517 609467557
    0xa03030b0612012303010b06040b030402012703050606031506060f12070e1009060e0118090507021c09120303050c0c0a11030f160e04140d050306090f0f0103060b06 72
    0x81c415828807104070380c4e04a1044200760403100309402c1e02c880e040e030960091003c02082c080c083c4810002c540c05030041c148881914103903200007101d0034008030078184841c4050014001c0020a001c495004141100202009048075200300341c00d140182045108140001d0203240102109080d0b80700e00c5440031340724046103015540606030018a6407130350300c1001f40504540c5481c3c0a0003031130301607070029564420a503c82070015120042a2406a000101e1150002034004000d00466100d0389082d80070340300311035020340c6946400d8103485e6060144080360000740301103415200390300b0181d5014507002c40e4a898802c003007011071042105590444c01220f0ba00000d103d188118000070650603070803611012035038012140c5615035450b1910150003143c400300020070350740039110b400c24040c600e019080783c805c0743d916140c04002c4101d400818404820054186408900c0030780c486214000a1140e242840d0407540c011414000281a20b6a81c030015040307864000a507801401d24030b84440c095 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 609470017 1250 609468767 609468779
    0x1203130b1e01080f0c090c0714030403020103060e0903030c0a0e0d0302060f01080316260301090506100816031a13050a0e0f1c020a020d0b040204110c0a03030b061201 73
    0x100071551040141d6040000006000003000900800ba0300003800034000300f03c00d541c00c01600ba400a0701c985d0702080203000c860301081d0000102d010345d8401e82d00445c0e0300c52a51001600381d650030f0f40b00080681400c020041d00c00c0e00441200c2d8080c00a440c26a61000004001e071400c644085032280c2040314202814105600060350345c1c0104019182245142c0c3e0702c11440fa07581c403865a12001c00400c5001400006011282142c8100200c8101d9010040c0456a0106542099005a802503214405c1c461281030000d0094294001481e1045491034419106503202c099140d005082580e10800c3c5810b41d85000142490f03018002c2203442511541188800540025624505424a452510f1200420020307800c0d03ca014450064644107962030743c200d4000c00321441d20001d50148029040c016030350003a440c103216110f030100c607050703060a0040c00300311171484220740100d0400f0414500f81c014005240ca280c079615190104078aa504804140700380110410001080321070700c000300300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 609471267 1250 609470017 609470041
    0x803041b0602031b0318010c021318060b03011103042010030f0e010b03070303050f0c010516080702011a10030e151621050c1308061b04081203130b 65
    0x610100d0b0380444c021071905589880f40b146000350700c00e03c114911080141c2d40918005281140020000500d002c4900160000d6820807910300b60305802c50450001000000d204d000d645e0202503000700701c1040040c599010324400504058400125107500900c200c034034034402c050940026100c0d41c0182c21300340001e070180501e80e810706541401c0242c050440d40c014410101c0789a00200244001851070300d00b503915600806003d040001c04014a074100c840c2402594041d40841d0180d0071510440c07540140340c03605c0038041204590408580c082e621126458001c8105000c603942c07010181040c070107a00410300703242200354a010349031120000320101003e841c400c1440d10b46001c0015641801202c0761841c0d0300c2c00c2400343e440300c01d03c0005c4907842e600c0290320086028030145400310300c07a14403c100b900c1d607029501d141d105d0f504011002c02c41c01483d540034000c0b0910350341018103000120341c1f1201c5079000000c3d10b54010000a9482210790f622880c00e83d0070110210050814803c6084 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 609472517 1250 609471267 609471277
    0x3190f0f050a0608150c0a09030605090c1008070807030b0d0b1e130f0b0604140f0106110106080c090402060f0f041d070e04050603030c0106140a0914040803041b060203 74
    0x1c1d0f03150080020380e8a601090301148004101c200300855582d02c07501401c560442d41884080203021100030001640030712071a07001d0f8a4580050401c0b00784441007291600c400c0710028200700c00181400082e907004000e040e00461207080214040c4141c1020408280045201500204402042c088002ea000b20780c4852038624181c104030566034164103408611406500506600c0500d20550200d908618050f4000d5002007010542000e9055100c50700380301581c0c40f8140c8000300004003d0b00c0d4000c85081c2d0075080c0fa000a00c1403d1502e80020744498442c0d1b0140e00441600001504641c2d03140111179a1b03010b5001450f407602420440042c0d141c0280c0a40c2490903901800082d030200d981c1c1980344104041e984850742c9903028000d110107020b001d44001c1d0035100510509000d00b00c01c0c001d030006868108aa142148014070401c02c200c0c1c490303801445113624202003040e400c07042800300c99000350400d6116590f510ba0346481c1159000d07a40007402c1c068034a807000700d200c550110042c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 609473767 1250 609472517 609472531
    0x6051f2606190533070501020a031d0309040f0b12031804091509170f07020f0d12081302030307080403060b0a150e0609030607090612020f03190f0f05 66
    0x112203807001103a4101c14103050242e035500284000b07000c3c0200481c1130082800c4034000d181c0b00c0768405444080700103500017407812607081e50045980c0c400700b40c2c103109034042c5452648102e00040e80d1704400d261030303100d00820b49000380e4650a44041902e02c94224060094015100300750940e100c0d098a03450760408600007070406500c451355601d070b1a183c0540d101c5150041d40d0051101c9260100200800b01000200c50644280d03c44011101d101000340013288a9046000e984107417900c10850228990409503104030010b6030300c08017040c8030200328aa00c6506007050b005940b030b0410115006c40c088030380250300d0310000a0030310030010310101401c1224442c40052243c0b00c1000d042000410090003048400b100f505501c0d08424443c29003481c61000c054031091038120321034086400d0100440c0d007403000c90f034010b40401aa9601600b1030070015041001141060f424024070750302c900c005010b031a11441204e480000000720b952041080d41125030342089200210b0f1190400703080f00325030803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 609475017 1250 609473767 609473779
    0x11031e070c09140a2f0d0f0e030316210614060702010e0f0a030f060506010e03120d1515020105070206100b071b030b0103030207030b0a06051f2606 65
    0x103070108107000b90f40418080d840076010a64402101e04001d240d0307002c41000240310610a10205942004000c803503014004029030766992503200fa800355104000720800441c81c120f428052441c0c0030060301d4014442d00e81e081ca0b03060284400315101070070034200000340807140d1030100b48124503502c80800c5403c00407000b010000308a0820126005440001c0d0104071005e802201915242c4800403508400410741724900341c4981399a094070b000200c0469102c0e58850078001c0750760300840c402d040040203e008280860300f042010b69140103080f80103504c1621201c1c400d00b0b005200030408050542206295171582d4074038002806868140c0315070015000310b201051548600142000a458840524515054140e59013001c0006400304e6140521144030b8080002005007031224000c2d4069401010000c4c10350602240c0c0c0e04002c0d00c0e8001c41807034000100f005890300384140c4c4020956420755805c5072000035042c0c6420080e9203104000740101c000c0d039400320000c030300301134000d00b015944 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 609476267 1250 609475017 609475019
    0x80607020705090106020d032f0d110f07080a051615060f05010215091c080a0c1e1b150911030f03040b1b030a0306090b03060402090711031e070c 64
    0x10702011001c20302170080180c000105a1a085005e600124094400310080c110721051010244200d0f500c1c4c00703200204c039000000c0a00c4041d2030b60003910000e10041c08801d14148203071003100c400e840303030341001032603058041240032209003c3c0040d03900311020070515880f0007480f0328141c1e41e616070b0400e000138880d141040215031080304002c0b10054031010b80041a10181c00e500350010382d030300140060043d2160610544d18502c01c4c60800e801c0d01900e4071040030505014001500f0303181201c0c00302041204000e81107481c40c410009040005880d410103a45904455841c1860034041c98005071000d0312004d00b6150000e0160b20503032515002e0000c0c40f910010b51010103072224002004100c480d4030500051101071607500c000c02da6042180c0411006807282c2140a095400850104d0b010a98a40c0100038100482c024000d090078101c0190035031746015800100015000303001182000440080305802050400880c0d203180b5041c0c0d40910074001101245134254442c000884840c800000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 609477517 1250 609476267 609476269
    0x2130608160306181101030e1204080f15041a040f0b090f01063c0e0f10080d0f030f0902030a05210703020a0b060402121003060c050a0c06110f04080607020705 70
    0x61040c06145d40401c03592104035205004502404400340290304034010021405812084c0d00014030003000410042c08595a549480030304005030b040e03858240d40010010000002e43d0024210030080c0900c003550100c3d141c4d0f060101040d204900000c1000c06544184000510300080c00304c8002807600081c040c05d91280c0c44000c070700201d282142044030b40300340c008141c0000310030000d01461072a051f01d0b40c03490751000001c85240042c0c50f80070001c0c10007010310068611464420780038108201c002c0101c1d24074240010a0300221119060070507507643d903200043c4540c1d030443d080c0660002d00303c40c050840c0e81025511841010700511024480d044160901d034164410748d14915011340180c215101145c4850920400003010035900c16820011004c00c4083c074500e65028050440340c4041450440c0780c411304649108240e202400404d0180e2010385a11100c00e08030154000c3c004205425040e41005190003810105003801c80081008514164000b80c42c03445800d10390301b110340c0c0c0750fa104 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 609478767 1250 609477517 609477551
    0xa0b010b041a0f0903060f06010e0f091b09030a0302011a040618180c120203390402040504060305150a0b01050910020f01110901090905070c02130608160306 69
    0x200c94031442e1400400b00102c41901c0e4030281406900405106190a514000003814208222012682c0e03445180900c042541d00200d4011a40c40599212041c0c0d0069000514407400041501c54134060031614644403003141419036000042c054100c03910303d01c9030300e000f90281c124032110300c1c00305200d40c0003030b5141c0c5000e0107000b0841d568030710f941000040640c800c4018208100282e04451104490300d400130300c2c80f00d9258020440c40b00c0e03240d50a40035204140c14503410a1440a024050341e80c80b800394580c0001745031485910880444400c4054000b040c040c1c000d0307a00c1070b5401440e00da000001d100c4089848000b4150f1070040c0c140a030b40b00c0d91003504484091100b240020790500000d00a4181700c16006141009070040fa00c284446000250a440e9054003546581c0c00128101c4440c1d41c0060b841d03006050864000d001034600707408010280302c05120040d100d28145c0258103014a03155120030007400e01c0304152005510745d800c0c07040111410b80f000f107403c02d03c2c04100c00380038400c2c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 609480017 1250 609478767 609478769
    0x3a0b090106050a050d111c0b2d0a090c02010e060703090512091c0c0602010b010201050f04030e01050f040f182d11030f060301050112050a06020d020c0f0a0b010b04 72
    0x1680b07034507041c46003007602198140c021071064480d0301c1e590610703583c8080030500a4a2001c02c0358109600301103084840f4010780c0c010000d0240a08040e41c526002015025030340c1d0022002000c043e00064660b900081501030f45500c601c10741464508240c0355550306410070810380c8441c13400c46980d40c803010713003c42c00c40c0e1104130013401c1500040102c200c100c02000040c04650b0380140310480c200c0c0c07248644110b210502c04100c44180104d0000c014003a020f000d02d54000d4824002005036242024804c411214011710040411480c1c507000c0845078040e405460801c80034140300d07a10340351030381c0c540101100ca0b401103c0c240c107502c03c0c5034003c113142c1c0c0c0200441c0d11030b1090b8180c0614203130300184000c0f0702c188912100d040e4035028004420041003003c1d5100f0000c894019445041143c2818210f65068020506550a50101c0400b00700001000c21f07419611207401a03403100071151400003030261849105050040001048902100180310032200f80950201a066641e0311980d650a1040e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 609481267 1250 609480017 609480029
    0x1080f060703050a23090705040e1209150d061d091e190303090b160504030b04020a0905040b100e0105030706051b0601180e0c010e063a0b0901 63
    0x103503002610803031003608819000b059807200429101100610a405451000300d100c03040944d01e010050f80f0700c030400020005200580302000f100244480490300d84424016800300361070001491030550b2113a901d484003005010410383d84404411500202401c0b1501c5180400c00d140c42c2c522f5400030200c5000e030b0007192244000d2481c41c0c2c07911190810744245040250003402802040041000031400844030603120382d50005158200c0d1604041c0c901000e041c0701d890b40c141c00840d0300c03055000001c46042c1d07034000c6071070304c807a0341c4a100160741d450150b007005083e0b900380414402089090307200715004418813000d24034816151085078840440900c03074140e06a00c8240308110440c0141c0007003580c408a1034a02207a0a5042c528500d400800e030310021020822055480590380c5604c5140104900c00024002c0e0b140003500007402c5180b0a500345100d280c0006003000e040022041c0802e240c8209200c0d1861903801c0a081d03c007900c980c20404004905140c034a1a06141180e031140c1a180 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 609482517 1250 609481267 609481273
    0x618030e0f0a0e04020a080601180e0a032a0203010606080118050411010c0203030d0c0c12030e0714060909010e071218030503040c0b070c0515090901051203041a030103030801080f 79
    0x880e1400402d40100044c0c4140d820510415001c6000b0130240802400f03001000240c80307040c2d01c0800c10380102d4070121001d90168000b100c114000940c00018400800301e46414130b1400c0400030714211034100602e000030b41c950700e042400540142c001e50010b048a508410b200b40c000b881298100c1520307400c460040c07030460300e07901728030403903010300c005404441c00941168108541340c90128100c4140740c8008000c590020100010071550701c180400101d507507e810f201802105003007607645d0109005189030040d180c048201161a0703035084e58004003008104429a581d030341e04011740c41201341e4400001858200c2c11850701c0140e40070f0f0381d8210079402519141c0c01070b162001c860a8201420880351a140d81c08001014280f039406401c905d800303418a0300d901071500007003000b80b04101041100e16003060045a05a82d41e0385003103030445000b0b40d907102c41001184480c906502c1540c1002081e104440c0030000c0082921024505986c82600c0c0e02c078159072100e07440d50361159802c03510607030784e4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 609483767 1250 609482517 609482519
    0x50a021602040f020c03180f010c03021009030c0816060e03120f0601020f33011214030c030a05070512270d0206030103060f05070e10080402030a0618030e0f0a 70
    0x1052a0f40b001049801c08080141086100c2c2c11560840d4000ca000081c441e20b2032508130703003624210f108078440c05001d007020303001c2410300c1ea800394a840081d8242034032140d541140f50f05060107140080400e80e80f00511a80d101c0c80c00d1071a1469500d00350050320741c0b0b031900e8285449514008100c42c4880000d10004070242d6a4854034080844000e260074114044c40025018040b010001c080b84546800b103410050f82180ba150803003103464402014840c924000100090391040401401e6950860b0b09a10800b019100c1d05155102e030a03455104e078030001540c40000c075404400360590922a40c15240852582c440070b09840c016a150150a005104603500c01101c4c01c41d1046052000a083c403102c04001e0b40008070140c10980c420748215848440c400d680003440d224031a8842d03403071700345005803900b4540400c400780c2a1120031401e0110358008a010755604018000c01a584910705024418030705c42523401040c0900300403008600200c0300c43e00300d8908090503c075400d0020307091074182 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 609485017 1250 609483767 609483769
    0xb150f0d0b0a1202150c0d020a12030614010f0201110315030c060304030203030f0a0f0606050309010e0a081c0b0901060c211b02040b0910060f050405060a03020a050c0307030e04050a021602 83
    0x410405c40c88036900c641088907800e41e040a1012810241054024009580150400ca804c0a1a44030508101881c01c00d00f8000c44c644000c03c240345900a00e0881c1500c02c81d0b8030709900401401d0b4510011010100402c00c1c07a558004501c11801c006800b568516000602403210078002039030010701503007003800001e0401c42e0740e4001035805101d5503008078040b6145c000c01c10458040e9040000080c60000801400c0242402010754083d681c4000f801c078040b064030749400501420141c40c000c0000e036148a000103215400085003408010305c001031f2542c1d1250042c00700803c1320300031a40428030002505c51901e01c4002d80680041c16114020380784240404c20825141e01c141c1241d00c03603030314132110b6241d45810090900c54070001d1540c402c03140c10044050199216107030314104119003004148410b1301d41405a0764800310307906015884d4520b0280945090107150111441c920011450600381944038100e0541c000d81a00c0400c0540c4030f03c008001a4480d6000800c2d40f881c0460001c001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 609486267 1250 609485017 609485029
    0x4050409020a03060f090c12020f01050c01061a040302010f1b0f021c0309050a081b060304231b0111030702010f052208010c020d020a060b150f0d0b0a1202 68
    0x120360720081111900c240c40faa6070400b120590203107100c81307964400c038000820098000640140c1402040c0400d180c1041c1d00041d00766075110035460400a01081d480007401094102e04040d22191207a020b01d5040c1e0b0001404542041c8410380c00605840b00c001030141c00303644e100750014112100c0c08004825a00e44030300d51284c40d42c1c02c036004048072000e910740c52043c1d240354000c0c074826079880c160b1518000c00c110300d42c9250341102c0750541200b401c0b140391500d6041d075058599000c0d04da913030301c9595a040015072000c4100da0f41d0342e04444480059911500072414401850351014020186911180111444040011500c4c12640b08007c1c050142d0301461a400f4440c0ea28a030180c9001c04044a0401441d02c00c889500c00c0e13807510205000300d00e820b0103500042c1d03006c1d10003409a00044840255158194000a400a0380d140818202a243d0510868621440f1000160348a070030304135444080c0d00c030300c070303000c0300c0c1403800300040154a031007044081207411100307a03810010400d801b0001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 609487517 1250 609486267 609486281
    0x1f022107090f06081906050303270402030f040b130201090611010b0a17070503061302091e070807081003081c0e0f01090506010611060106050901021f05071211040504 73
    0x1480500070300002c00280c0c2c010b500d0302400700c82d519032a01c1e050090584114100130f201112901e0b05040d01441640c43c00003c0e5102c0c026012041112000050108110b041600c054240c01070300000402445c0103607281d0b05800307144502d84c5d500b11030355a14410880503005240c002c0c0043c201000c20002c83d0b1244140036111581030000180c100007540c0040d5008409911881c0844404020041c03800c8041c40f055005000c2600a0940352070f100c209007070700340c0044000074400c07842140070400c0b00f400342d0030b00403921074241d909241d40d04100300c0182041c0b908840060001c2c28403000985c1c1c2e075010100041c12a40c0c05101035041040e0400d0b200304444d001c260008078565100508241076004001da425039240020000454000a050083c100380c0160044000d0201e00c100c0152031385800a00c0504480f81d602e042500c0c2c0b010080100d0406803001002c074066418180004450070b210f0744294094030072034690550810000300404183d0381051b1001000000c180410001c60410350040c0d6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 609488767 1250 609487517 609487531
    0x30703030503250f030e0705060a030c0c050703061d0a02030607030c03231b0301060f0c2909071409010e070212041d011a1606110c1f0221 61
    0x116122100c1040308101c4102c3e8a21200065503100c0c1d04500d11742511070080b64224074000b5103c82402c060204a052007403180b032404055440c80102d10a0313100b0141524060307401401e603000c0703d5490406101400d03040c40701c070f85000701802c0810180f5400182c1c1584280d400b401602603555640c00c04d40080921941800a040d1982814084e02360070045402d50b5041000a0702d0590070301c40e07036000c00100242030320594100c00304010301145401c142a03500110f070629110742020a5032814441c0e0403403018613501c140705403082602e005881c01c480315202c1c000c01d004540805649010340d0610f440074502c0d25802c14107600041c0b01c030541000405602108600480301c0d0709080308a800015800340e0f2040e1800c800301200641b0010320440b40c10300420032414034030700024401c0c40c101074a105083d0040e04d81e07100500032000700401c9820110848900c4400292a58011a001da803207224003000045070440031551601c00300075503c20754648060300c1270039000d070000c20b94040080e00f1002d0995 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 609490017 1250 609488767 609488791
    0x50306270f010f0501060c0b0a0e0c0628030501050f210607050301060e010e1f030f060906050405060a1a030405100c030903112a010e0301090c1e05030703030503 71
    0x95641400204014004601e504000149003450348200408035041070308208200300c0840312200108000d001603680181d0203000015805940304482890088012040344c2c202c40003055094200828200100f005031020704484200086800d00b00c0444000b401419840b5242c0c03d50305010f030428a504090081c12001d030f039100803011108291600c60111540000100004014400785a002d078003000b80b22801e00b4003009201000000444034400d00740021800035a02c06a020800c0c420740011890103000c00040040e16115850540600242c1c01028022402c5c180440c409080114902048540000c0844030300c25400222031860703800584190f456106401810030400d486200700001c907902601c0000b0f060002d0701d00178002e540c4800d400510f81e041180404020800f0b642181201c032050504001824080070050740c428008107401c40e0036610704a8044104001840c1440c282e981d80c4d8006500a0844c41400020070410300610b23170190404101000003c0c05a03000d15000400b40c941 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 609491267 1250 609490017 609490081
    0x70b0a120204031113020a020606040f0b0a03050d1106090307081606110307030606050705100c12020319050c07080d110409090f02090601090e0411041d0d1404050306 73
    0x90340c0070398100d0b8000303840038080384000ca83c081c50000c0034051340e191404001d6040403103052000e5110800204050b000d02c1e182d10030f104071102a41d0002010f000014054050a0748a06000c0d946050b0082c0300d60200d0010300706400c0d008000505180f0540c1c03010015807070302c142555034003106e801c021190603a40803c1405803000401d6030107100081d00ca02241192a840c0c40c44000f0152041c41e4040d0003401010000480820340101e19140410320729880460707249a0480211400000a07411110b014404000d015204000000c06421184455028801c0d916071032003440e01031013584030080081100700312a01502c4096003215055140c2252070509056072101004155100545d08807400c0039480c40510440c540441583d070008403e207070880e0543d040600108003250081c1c0b020b490100f021419840d655926048007410502407a200e070300e0030b04682c4805941d91200121207000c6200301b40d40031a03a51040042d1811540010005d10403900c0e2110f403070801c41c04031040e0014401518207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 609492517 1250 609491267 609491297
    0x3150f050607030e10050d1a010c11151b07050f0109030b10031208190501050a050906120d020a0506070807090e15100f11030a08041e0c0e040b0f09070b0a 68
    0x45d48000d020140c5a90740c1da500c404600740d00b01c0b9240b8000c5c520a0b2100201214142d900590f80c0024542c0300501c00034001601c0006040b14983c3d0390101c1481500180026841d1034468800c0c000c0b03082c4d0421968401e44450401c8136045166401c18001070f200c400820205039601c030722581060210904407206510380e1518030149000c1d417284004100100b0034030aa0602c2924074590041520004000e154100000540140c41a101c0c00d40710b4130b4410007081c0555a18010544c1c05e411203000c545040c0919500603440e4a0044001d0364180143c00c0040c80c060b014601e4603120394401d0790359040c100d05007030100e01c0c1d01c000034000304845040e200448076951910807400310044034a44403091324900b501c81c01410715112007010001c9400521204504c80d41040702c40f41c2181d400350f40400341d00040320030180031014024010b400d0000c0071800003203101c9524102030103980502c0c0a840d040d0f07150180e0343d030011816110309816600c440002c000040394413014001c60050713850000c142449110b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 609493767 1250 609492517 609492529
    0x30913140a0c0e0f061c1805070509010605090d0212100c110706110c062b020d05090a120809030c060a050a0b1c0632060103150f050607030e 62
    0x964a805550381c2d4009002c040f40c0242c400b05482c40c0440e4000148926800462081c1c06008440221540c0d002c8003140d000015811802400031580d03120500f1152a05240342e440c40c02e13110b010b01441603c0004200c45205e602262800e401c05050310b10741a400350b0a220103540c0001030040305020b469600c90042ca491b00440071442c4187c2c0c0d5844924010244c51410a10154001000d00c02c41c14400801810041002c42d00e12000702c8280d600c401c46010b0380f1a914410f080311403001c03401c250b030740700114103190701404210070100e40412440d900c2c039025503030320780c0360100180c03003001841d92801420740310341b0381b5a52044c5604d0a0368100340c24803000c589000000d84508070304035102c900f0440103901d5481030710b2101d0320454182840720181851200100300403d0302600031b94a4807183e80003002a06016040a880c1560400c0c0e0300c107210103030b14520001540c110b400a801c0056801c01240010303001c1d0140e8040010280e901c500e01b0b010044641d1080c60200e0501c507070400d035041507507515 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 609495017 1250 609493767 609493771
    0x206180607120212070b0a020a0309051213090b03150a0b0406170c030102040e0a0203090a020d05010c1101050c040b090d14070f080304060c1104090b0a140a0204050303091314 77
    0x541220030b08210800c000380c14209942100030700c0050038095940841e0403c4002c40d0000c849050050741d40301d8a03507045024100c003e001134402d101c0d100140c9806101b4030f00030b1004011515104000f03a0700d903c1e010042d2542c2900c1543c1c142d01c1903c81b4590b04140c9070349107401c0740d608403001910321806000324080e10040e90040c0b00c80c0503e04448148400203114100c4010781c114000c40c17500c3c2c10724400380390a140180810140030350201c00210411f500b0801c00c20900c1e001407154803485050301c1c1650281010508400009452040203410100d0500400b4010941c0518071030a06003400f90b14803503a04016181e0354001e15504100c1c001c00c0500c0d981600c0c482e183d001401c041030030505d180620450b50750003443c0ca90320800040110550010030700030040d9014200da1031042011002038007821142c0300140104c8803510034000110140ea01001c03036100f041040010903030720700031740400f01d0003684a42070b01504104118607161030610007004261521081c0054991000f0510307880402c42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 609496267 1250 609495017 609495023
    0x30c09020d1d0304080f010c02060123030105100503010b010e010e1909090804030308090705220905100614010801080c01030203090a06020d02031e16140c010e01061a0301030803040206180607 84
    0x2002609020141c0181b0040000c18030020003070044030000880250388110511910719410000c540c1808440240c180990000c2c000800902c003a040c81e24040c03905090a03c03819110750f103080d0b209001395004010071000140e05840c2c24581e1400704050062040725506055601001908003160a2410b845411141402070a145e9122400e41c600038190380b001500450469222020400c00740c0e8400c0b8680304821421340128100000c981c500c14058031400100404901074100d03022102c411991009007150302d02c44454504010590040d91000428020200140c120351611441e82d4000d40096070400b01d4002100c200d032195455100491300300c0a81181c902d5000414052110645102c80c0d0203180300e0000b01c20075042c50f00f2860303140c080155054043c09160044d481042600b00103898008150310300901010040b190300500818880c0140e142c1b110034030310154070410001c016241601d502c03132021451510f59808028845d00302c0550803003c04403190250400d520741c940038000707040c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 609497517 1250 609496267 609496273
    0xd050703050c03090c060d0e061f0f0819051501030506191a090c13060503010302100318060209030102131d090303071709011409030403051501030c09020d1d 69
    0x104480024190350000d0004020340c04284140485140d02042d04840300c0000c44000d55250750420421000e840a0400700d901030081908004d81e03a404108403480d101c0c1d47d9480703021501c1d101c4030115540d070450b006480541d4000320301528288140d201c1084141e0040d4100e40b03144062a03d00706000d40240c008503641c7d0440750901681201c0300307030a80d2810041000901100b0450400d00c4400c3c1000003ca9100e0410031001c0f624075943c920881d0400315034100c11411507600d40c100038200e907200788005c82c06802c0099001e0b86051181c440e0314511100000c101c6411401526244081e410601856501d55402c10002d1208850b41c840701000f0030070506051110b007902c2c9c0800711161001028040290010010440c003540e0003050b000c010102e07602101740c030b074544012403801442c803c106500c4d160381b0b0205006a00b44008041c000300e80c03140c030456081d03450410020102107806e10000340b000504030310070721000245802a10803480400710000342d0f00b92921400c40414115103820300746030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 609498767 1250 609497517 609497521
    0x405070905011d040f030e06040909020108060f03070e0403090e070e030c03010506090105060d02131d0a060302030c010c1509080d0e03030402130902030a12020d0e030a0507150e060d05 81
    0x12490700415004041c02040940800b001c8016030309549401003005028130310050003481014010b460710b081c40100900b00e00d80396a25185c42d40c00a02c641041640030403031900c00a41c3e81d1030301440c0c0e5442640050050203100f49800440a41040f020344200c007840070701040800e0b04824070900d280300b290280d03980544804240241070510000006aa000380d0401040001d152128484241160b000b5113510759241201c6d800030009020b1007404809040d081003000030841844969501201800414010301d51102400003046503c240306c004d415402c01c207040705240d0f018500c05c2c600e9078014184a1880f80e00c1060680850368240c2c011646154007182d080007084a5226280c2442c210388002c51541c101a00020b600e1780760042c0141d2003a448021280854405110314a40a0b62007131810844408400700691541d54089000e40013940c411042e100c01d00c0c001440c12030060b0040e000d007002c14101044800c880041c2c1d01200d013070000300100c4c42c03465201c1e00300500ca14222400001114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 609500017 1250 609498767 609498779
    0x3040b0708010e10050909070314030405010306170c10110a0308160f0e040b06090a03150506010302040308030f0603120c0a0c0f06091715042103051e100e040507 71
    0x64801070700006154043c84040080403001e280c806000e0366400c40e98201182c0d030710340d006880d080300c3e41c0008042c0707002c05000c000f010301c00001901c142c1d0b609803414840a6280c0308415146c1c0000800a009540034600301402c60400d5060418080c5a03843c08800b08104520030302e1410885100480004504008000107010b05c00c11002c0300304841d14020a4020301b107100101844103404159106a6503108640342a6444400315800001d018164024040d03032420802913403c4a445103040c41c1d424040000c6166102e8801c8030b00b901e62181744141983c41c1e0800d2041c07d40780c018810f07030301840750941e61002030011001806551140301300400d0112420311f881c500e294600e40c058442420000000d1064540140e00d4030203030380140311304007600024a01114030f04040c1c4650040310000210500003803240290031100c00c003450350490124030b100003a04a0894008664052806104114202c584840003400c1900f007918400c5210800e0b88031a060031b006071050310103c64a0b40020020495 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 609501267 1250 609500017 609500027
    0x3081317060f0f0601020d08060607061d0d02060f0c0c070305010e011a030f0d14041e032105030a020a0c0206030f0117070605070803180f01020301052119031403040b07 74
    0x100c1aa03e402c0302c03d4505100c00040e50b0381100e800c442d0140030ba0000054641e8a0b028203071811190841c000340160019030000f08150024074040303030460701400007440b042c40e00004481c9d010380b929040c464001e58035403400c03d219800910710320080d070083d02800000324009004250010000000000f01114101c032003100d02450741c4681ca009410052032002c0e45c15002c991408180d030f107804c00c116203003001303c04410540314640010440c3c106004000c0402e0782849400c0702900d01c6046200c0c19154501c4d0441481c030940f04040340014000c0001401c003d14035006044020341a0400801c0d1a1141d400101550812108484030802ca200100705102c1000244652800c60001401d285410910010441d10541c03a0181c0740074000808202d00f440010140c4c500b0703e03080e80540c0d60309100001001e010390f00170303c43c061141e000754504004c01700813098140030a0180d40f0050a0007008400030b819003080c136000607014020020084107011140000841c0700e2403143c584409686000c00000d04 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 609502517 1250 609501267 609501271
    0x6010c06060b180d021e2115070203270a0807030f050c0105120c071106070c0f050312121e04050304050a06080403080703111308010f0e0109080403081317060f 70
    0x13124500400b2401e015031030702c0e180c403405105011400741190150101107621609410251450320603400180d0320525004a842d43d0802040880c1c041240c80308202240d8a0081c0903103410700340311074201046d070104c01d1001d00310001c030040c0a080c0c0483d9101e810504048150f03100f07941802c5100c0c0c2c0801009402e001ca401e4405e02420071a09113031090202036180d0344020704440d403c10b400201c0c8810300c402c00265480d40000104107950382d80da18a0500c0e14103041380315034110308058500100741843c01003a040000c000b141c801c00e061400a119081444401500c60203000303220b02c0e01c00c181d980100301045d01c02d07402030004680d110300e80303024068842002d034003990800c05080c0502000030b600204c1d10750011a2f0340b50110b0041d4459010884600c1425800b15502840d0200000c44500c1900010941c0e040600204107a110b94501d881c03e80c1c81810b0000c007030500401003440012030380006002114602025858040d8482c0c10a0f0244024080507400b180d01c444100044c0001c1d40c49069 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 609503767 1250 609502517 609502519
    0x2508030a1815140c0c061902010f0c0e01140903010617190305040b09210706020c090c270a30080a030209010c120e0909150f06010c06060b18 62
    0x120400422540040c000c030802c1e0581001d000c00043d6080414104003c80c0303000c1c0317000419041c4e031403000c0c02108142d000c244190f0301c095424852500c51030340e824801c0d480d0000280d103508002c115118011107001480b1040f02f0040f141c107100b01c007840d490920440d009095612006080030003000400c2c1c1c030f022154080401608040e40351040001da01400751001c07140542e074030701c0e21003101c500007520b90307661301e80d0079101280c4d1655040406c00c0005020021030711280c09a654901c2d0000501c054200e003200c3c0712403e89010824a000b14008004016503200c280c45000c08040c00800010314085142c1e0041400d000c134009640c81c3c205080c500c42c03240103208901c81c42098841d90f41c1603e10b00601081c54107140d400318213888182d009a4441c0d18013544600c074032103128074155019010b481d10b40100c9010340d1040b40002c090f941c00050b02903260705000954071041c0e86101031184130400c02800c503410003841d0841c0000045240c05200c02400f0a4003009481c0c1c0035121305400f8a2588070081c1d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 609505017 1250 609503767 609503789
    0x1a010909022b0f1419020405030309010e0a08030a0215090a11010315030b0a060321020703200306040b0106030b03010b060702061810080415050103052508030a18 71
    0x600d40d11404000c0d010403060541010419512800c5003840041c6012503c0042060412100142e809800e20281d072041c0414140d01190040501e0300d042240691f001d055010342c130400c8422a5580035040c4400603120082c80c501c8160745800c1c2060854000000f82000359004005d000700000c3d5a6580e20b5014001800610390030a80f81c445e41c00c0c40201c038401a05040c2d42c2ea5061200e010b0900000c800f0756003003145c08005003000c1600c6401070880e03200c11703501c0d1342410704880480c1850302c244503a0700103941d0062201504503100e03403a2400c1610001040c211141d444142241c80c148001403040780510303280d810542c034188015080e13a0102510307070311036494101140002e9440500b80d42c105a0155451515812580d0442140640341030401d5444080b1454040d01c0710760008240d44198814402a5180490110000281d035000c2c00000e0240c0c110070101d2020204a01c0045000360310208003910326039840040030f0950f8000023040c80055103150304000810703802009038004105d4602d203 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 609506267 1250 609505017 609505027
    0x30305090d0806060d1a03250b0f041701020405270c04081f0b031f0f0501031703311e051507050c01061211040c0806011b061a01090902 60
    0x2a040d0b1081c1c40026065656420704065031803100c000199200034054221a030040318020004120350400d150341c04031900340440070802114a000f03031742200c2032b1008010b041c14200b0305220403002060710103440d690740c280000100d40e0745011140c02a201c0e03100301d4040700707900080c1c0c04006200c01060020050b000f00001c1040c00c2c40080c202c00c0c00840402000c10440c200300401c409042240314040c0e06200d418650b074841e12500007501c24186c08080e0410a0050740d0b5412000d5a0702444050030821001c0d00150302c0e030103140002e40d803000b12414151040f5021100d002e00c15070318040c80c48007003a0246d41c810f0030066072000e0b032040c0e2103226104c000c400b520b030303560144d4607a10310100000050b044004605c201e801501175070150450701c0d00034002240c840d02d440d44041042c400646090710f1071042c9107140e040c140304001c3c0c0d0030007650b11900150b58100043d0b40c0343d4400460b113101064071051480c085000c600c02d070201400c8078018241c0f40b40c01c03e80010190704003908103405251040003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 609507517 1250 609506267 609506269
    0x20f031e01031709010915180f080a0303020a12111b0109110d140123010603020c06010303080c0c01090b06150c0d14071a071103070302060f0a0e0a030305090d0806 72
    0x7a10104800c0f44103507075500c0d140c42004903001c1101e68401140e00a143d01442e00154001304030280700c4000042c1d801030355030b48454008000c4440d21680d00c0a82000d82c06601091080c3c008029110075418555400d64051944800311a41101904092031f404100b1020502a5082d00001c0c00010002440602c0c015101c0c07070103182c6000b40140c0b00d14060b10694041002d4000340c60464689500204206040d0311a01045055120b0700d5481c0e064000c0c001081d558064802d60741d1340c148081c01414241e0950b60140d548c00c0019017020b450350000d1104007045070090142c2d134919031082c041014a41000b100340008a040903e013003180f100d060181008440f00040c20b0942140c03280342c2501d80280101d400c000314031401030041c250310042040b000c502d1840203c2c0500a545030395038490701ca1296800d59480e4059014002c3c0140c001c1d1010404002c1d200052940003446082c0000740c01241c4010340e460960103000440129454404014584078184120b40c6100e51604140080340391142c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 609508767 1250 609507517 609507533
    0x72a0f052a10090503060405071e0b031f0902040f08060c0304150b041d0d11071409041707030c0308060402032e03050f07050a1a030115050706020f031e0103 69
    0x5160140296040210b402c011403054403604020310025060307560f1410a4108540c942066000d1400d0403d03003038140c1071002580700c0b00702c41100d07c00c034030300c07421604c030f106103208560150740322125059440d1401103075003002803000300010a000100c58095a151032a07a504000c8001e00c1a000c0340313410702c100300c0441c441d62401d44000e401901c001234021728680000b0020169038010703080303400800500300c24034040001e41240c204402c0c1c840c4039803c290100c200b5942c114500591400455039800350308681801c5001035042441003002543d80800342600790400d4000c3c2d6001d1b000521074403958000d040c3c101c1d40740341e00a1010780b401c2d4990300c0c1983c08218250640c00100c1c4114051440c40040c03401c40820120140d58440c00351001c400d07840c0c80740e03a81c603002c40c081c00b413142100c00740c00507a01e0b40300040c51682040302e42401e41582c0c60218014a03298650302c222050010402407580007a06910050016602d842e00c00780d160b0420604944903503200054000e004041e840050003c10101 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 609510017 1250 609508767 609508843
    0x1090c091401090e0901090602070f03080604150611102301091406010c060b0909030915041d1e1303030617060a0519020315010201150b03072a0f05 65
    0x2c820701c030007901e500070b101d8011f05407801b000c1d203031903c0070031407100704101c02034003003413040c002d65510b00e0944407803041004440f160120044560f51240c4100480d9020381c4000c0307504819107040c1c13403503e54040f04c0c600507665418898000048020145840b90712152a89800b40c204c03980704200840d000c01d0103040702e000240c209810310241003001003c002d03c50700800d04455016100000c241401e4035415960341102500500c40c105041c0160326030902041034908941c1001e00c0114442800080c0e1882140701074a4aa50140404081d46400a060784420f0151040c914041030301c80403810000c0c1111015044110001d1400e440b000134210300040c9250002c65800d400102c984802c2840300800901c3c0e0302e1400500d00100400c10032081030120748415030400e8001380b08102103440398415418081c003400d040c414092010400b81486080c503287c22400c602c101c080c00302c025100480410b001a1800c0b83e2101c80241c0315800c111061100e0500789442002c1c40c40c004104e855034041c0c0c03101e2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 609511267 1250 609510017 609510029
    0x1e0a120b01090c0c080d1d0d09060e1905100212071101020c06032419080a1709060d0f022719080c060c07030210120b030705060a110a080301090c09140109 68
    0x549820750382c80447d00d80000c80c0d103140340342194500d080c5418090306462040c0324000115044054269131410800051000d00c5050030100f0806800d11081201c0c5020341380c540c4046110302414a1180740081d00200b0b40c040c012542c100c1e440c02c0f01c0000926003003038009014050300d401d1084c0040714802d10300781e5015000b01584e6181180400300441d0500380c1e4100007490019840000145001001c95031055240c00341601c80a81185030001080c58852052600c4e00b10030304020001c0303104202c1e8082c44900c01c80308009403034480d5205415604081c8144141840004031440c081285004110b040c00c080d00c6c000312200c402c0c904183d5030b88540104034424040c80c3c000540c039826603018000359015540c02000000030403460100200400c4207509140081c51404030346103041d01d0001008402c8036030082101c4e10309400202c00301c0b89031450717016029680c420022400005000f0344051400f070150900005000c4054800003013405a040d0301c00b500e1460503901041041e40d020ba840c0040d144 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 609512517 1250 609511267 609511271
    0x6011401020c0117041a1f080d080601080a0e070e191a0105090102070b0d0c1413120f050a050d1704020d17160503180105091e0a120b01090c0c080d 65
    0xd07071406d09124880f4020340e40c046905004041003508030402d8103020341c24200030344e5055240e4445c0c1c61155140403a02100011445030400103549600c541840c40d8410140c03031000c5034401f481d01c2e00c3ca00d0b1240d10780110030500110800c100e4040d4841024004140c0840e1062004c845021100b20200c040092401d0421000144168141e4002c0203148010011400e2450b07a640322410351034024800910f4050020303101101c0001034410540688921000307009100d120301d890040c1e654103040820fa4125400c0e45400b0070007000c140700f0311070342c90321600034030140c202c442e0340070401000060704810040c04403264006000158841c0c20090030b01d1640036a15000042e06801920700501600b2900042c1882d00100c0318200580400a840b411100100c4071210142c0f031001981d4501078040b8017038009840040e50400070a002c0014800e0385070203000d03da1000c1c0c450422a079003804a00095079841101c1c001080040c900348030b0035a078210f4a20348160000000d45e00c190680c03040c000c820111607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 609513767 1250 609512517 609512521
    0x612100603330e0a02130b0f03030f09060a030e0d0306030c0f0b03040807020d0b07050408010f061401140415030e0d02030a0c0828032003131e08070506011401020c0117 74
    0x8404001204d200ca400820603a03520032500300d0400a0324111074002c1c0034005001240c040350034008203490305e00c96140300007801c1805007000c1c008150000c10082c010151a901c002341e21220900c0038281d500f200399404034040c1d0440c10710940346400303a400320840d460b800c0000c00c8134004a0b4143c9030000d5111401c01e50300c1c803a5000250021100c01405441c11360399109101017240c20400504c200c2d501c440c024032038040d10741e5940c0c040b41c070144a607c3c20a25203081101d06503204000e8084800700d02c0c04502e080c540c6520509100703403062041c40010030741d00c0d0000d200c0d42034104100181107409100a51801c001c0304002840a40c011000901d200c84c041103958038140010501c684540782401190000318540e20024040c1c101035441c458580800081c03640302220710f004903481001400710f40d801101c51640d88180c0c10100d01104006a0841e181480010300d1110041c40b44d203006000814035541041001c50295080894803815988801d00e2001181d8000c440d2a40804240030149019 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 609515017 1250 609513767 609513791
    0x5060f1003020d0e15041109040309030b040201090315060f0b0403020105040308030a060e040605061c02090c070501020d050c07140102032701021603092d0b03061210060333 76
    0x160904c401a000c09010b422400494110003800f100e2095025a114030703540c80c0d04005100008030140d03005000603c04500920100700000c0d8069045441898055234040d56500c5401c0500c469a40d1140655103a080400041d140c0482107405031503c404040c1c41d003455075001034102c2c0300314840100702c0c20380070000403080301c0e6562010f00100720f000d03003074074003460180703032000080100701c800f244100500144611803004610788080b00f55400381c0111240d0b151100010b005d40c00c00d4600300c2e00e03503400304514801d02c080341c0101406596032292098917001b0034036048200b031107a00c40d0002030f81c1c0f0500400201c042c03014884028980280420115500c1d1070500b28003a205c0c030f0301061000941d00c6030b2002015800000001115000b840c1d100c0c1d0040300c2124101c04071b0a11110041c0304981d6801413104601e03d83c021034002c0d000500c0815810720b075100f40d43c1008851241c034140640d0350041000ac0c4104102a068803c0d120000c0c0c521800e0903614160400c1c40159a0851555540c4440c4803a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 609516267 1250 609515017 609515021
    0x901140d020631090209012c150405210a02010c0314030411040b030309090c0c160609060305070c0f0f020103020f0d020408010e0f03041e05041e05060f1003020d 71
    0x18200203020010180b2044021048081c00101d40c03011011803d40001500c9a05403003900c0004070148c0d07840c0d4030168004003440300041840008802d0000f41405a00709946d440c02020030340e0320400307505490b140303400308000c1c1200e04040040360650005052500d010030100c0c180102941c24240600c9656580c10111848aa0f203200b03c20311100000070300c41070012030304200c401384100700d50038002c56086505154690090000311600611501c000c2581040d0450240c249011a007080390310b240309145400d20010496400700d00450382101040c000d1580c035000c0c007613200c1d03043e082091402c0d0140d647d40014030380002e005400b10408500503800c6a210b03404403585840d011100c1c0b929100743c0512032009520034895094190300e4042c1d540c0c011000410801d113190a2030b405903081c2791501d00180400c038840180d007100e0401444c0041600d50b22482210300300e0b00c03500450741da05500381110034100d0b00302800d218424007211b80104216903c401c6a0030b00741c1018500076807205088441c0c200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 609517517 1250 609516267 609516277
    0x70311091e0417040e01080c0301110f0d050402030a0206040b07060b103501060e030f010c08130f1502190e1f0c0501140915011d061906031a0901140d0206 68
    0x170300030807035000041b004000640d103040c03684114003c000347e0404400001c00b0740f2841d2407008420505103d400b1114946900c034603030040c0040e090b10b04140c503560004095500c15000780f41990030114221080c41454482c0400c011400d079000d1540c541e0103d4081e05041c122041a50ba100c5080c070003d1101c0c03203403c06255005501481c0d002503585131880038112880e410b965602038491204104848034050043c00c481e000241c9500e00035480d55100000700d5078007071800b0b41d07590244000e4600000e01205190350060703041e841c01030700d4601085c0040c01c880000c044c1c440c104142410303d54029030316210100b0781070803441901c0e030800c0e40083e81902c225a080c28060510b510381115880741070442220144610320410603200c218106a0304406401c0e8207000d160702c0c204011400c926207900e2080e4044d04080001e046201340d4204042030680ca40040c2c0040300000d85511340c0d805100043d110b0710756075180445030f07003480350b0415224480445000b01170601c40d0600076005010b540b5144201c0d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 609518767 1250 609517517 609517529
    0x605040f02100504081212041b03051005011503091a06011b121106040f030c0804170c15162d2d03080403030f0e070311091e041704 58
    0x80300203241c0c4001404680040c4503009140c002d1082c0c018074804006c00b2134a40d00c540114141198039152a19590010f944a201c1d800514403140840480c3c0100180b5601015820002c6031075810301103429040d40000300300d0340500d41400342c1c0c040010a000810405040700b00350390006980d915004943d8582d041c50005900402c8200042c14400060b96a01e442c195684481c0184001d0160b401e98602d0201d802901c1c8070780039503941d000248103a10b4903492074010004a800c1540f24485440c3c8525001d05680d81d41d03000d400c041c645030405c81d52464803070030030003030302c1d03050000c504801180c80180031401000c02000c250f8645803806501d1174031291000e41102620742010b41c2c80d149095000c003220049185500c11041c54200308010850b82c102540750f030300e002650300d459400303402900c41d07007608006d160b8071407100015450080187e58000c2d802a43e80507200e0720504113209014a014000d025100d4212070741d0200c1001d0b1424003500310340c0c402810b44908400806030403d0303014982181d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 609520017 1250 609518767 609518779
    0xd020406090c020c18010501081b3a050c0409020327031e030105010c03031a1f030b04140103030c030e03062d091f02040b030a021e0708070605040f02 66
    0x12124a030780000d03c00003103501a651903c01c05041c0017003860141c02482003038002030b94280002c904012402042019402214250303003003c41310704081070300f10307290008070340c4d0000500b1080c500074034480703a40041e40c220900d0411a50601e810700d540f00d8812401414040d81d000004103121100c02c0c00010f841a24040203000c141c1e02103400c1c1500c1f6488880c10090b410a003a28180c4400740742c804880c100c8005840b000320458259900741c01800d800c00b000e888840320500c410f44c041e06c62810740000209117189014401d041c0d098040d08841d1000d000342c0c043c614102003170310701180a0640b541900d4040c1028401320030702e858101c58141c0c81e0440107070140241014413140c0c1d01040f080b840c0a00044014450310b40e20341d035000ca21540c0c101d0700340320540d00240ca2002c0e00c81640310300c176810392200c0d50094589500e6011601345584192002c1d1b102e180d000450a485403000c0364940001d0048030110340c603160480c0c9070000075014a10000e048699109c0228040000200311000480d0340a4a8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 609521267 1250 609520017 609520031
    0x10f17070518100e010b300711010f02040323070b0412020f0d0c1e030507081510060c02092508040b070e090f0901060305070b0406020106060318020d02040609 70
    0x7420310310030800d5540c403501100900c0301084044c1d041c01401d0680d456480d00f11700300140003d0349280c0c1c1111078900078800d00c20400a008000500b0000ea00c1403c8d1900c541d000c280b4401035041c01c4a12080c468601603106100600c0028203c8076007502c0014611001c183d02042c8000d403030b04104040d809050302c25400070740021021881c0400c00c1c5c0c110b0003281d182510f00022824094111959040201880940481440502000300ca0006901c84000319000440c1d100d40d2030b0f03031400764070381c101000c180d10804040880341080754800d135218240300c0c18000310600e44080a4922900301c0d00081c0b154490070300040300343c2a030103200d0600003c2e00c025030702c1c2c40c003c1010141c452041a1030686403882c003400041c4005004124000300d000c0041c00e01407165684110381050800041d2003524107540f00c40340000401c1082001201418201039201d5999141c000c010303084034a1b950080003418104040d62083e10b490002007016540c0503121100d69052034030014001304600d03000812150b24200d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 609522517 1250 609521267 609521299
    0x9090714070c0e0c041d0919030302090405010501050a120c020109200a051c030c0203010906150807060c030e1e0603070909060509091c030209090c0d14010f170705 72
    0xd4440460b0f481801610041d1100848580c191041c0e0044010800d2130040002c02d41c00c040044903444802041071316003007455440c08403074200c02131400b500066000f05665182e1b152620825004200c02d080c120320b40040d110340905003000c04402e050541340d031403080d10140b50003900b040200ca5071014401a80c1d200ca01b084a5440607031b41c0869003e1003180c40c001c40c0b80e0801c8000c000d4881d034414164440080182c5d800c80d412600408220307059522049071300c000500074014220500d80300c2600c0300099082c418550314151040d0b00c4402004414080b04010030380021110800700e2060f82c4072a00c020140fa4138a901081d0810b0311a0072501c00420411081c2d4030445810035250034074130502075680d0703d07020000d0300da000ba03a0099039500058507500c2500d20300b90703180c030700b1040b40d007000743c00d210381c840000f0b0404100b1241503039071003030000e140c03035080f41c440c0306003c0c1d4512000a40d41e015410000c3e6280f038030001c0c0c0202a440190821750903034885d400c02c42980102002803450818000c410 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 609523767 1250 609522517 609522533
    0x308180706121d0705101b06021c0c080a050c0913021c0204030c120f08040f090b09070f0509030f0f0319020d050f07020d061d0d02010e030909071407 66
    0x2040034030000d02d4261106400303420f112446181540500041c1a400d00703090401141c03001c901130210a004203440511800ca54000d0030413413481c01410300503103440d01e82207440c6821402e044814486440c2c00a8160950b4005c07254a13049107042c0400241c0d60b0b01d01010010f5130bc2550a695030004a01385140710103507481d0020030484041503900d0f034540d0004031280c0d09901540c0001051078801d1403080c4101008100c00e00d03800e07809200403200d01009621480704541c01600500c2486685030703030901588055000b1103000740700580714589245040e00c00104690f01c012542c07010070000184e01c00495408216150503600d1a80a45000103c10104d6503660703403015081c184c003108426078030031000f400800c0e20f041501c20380e2109460540d14076071002e0f143c0d022003004c03684130070007028810120f41039100d102507036440006c54a00f00b242e40c20b4510f18100000025904688c10b02a42068114003c000e4545980c0c0c2038440a400b921a0302c82554400c03110060300c0000340011500c0c0061241c05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 609525017 1250 609523767 609523787
    0x80f07020402032e0b1207030216050102130b07050a020918011404050d03020c06070e0301060308030f0a0b0316030206131205160e0105091303020f16030204060f060c0308180706 78
    0xb0304d0b030343e44515040200701c0e403016401c0d2094402a0805009452504513541e241316440034452500601d0300c086007541d003004403d50103040e1210707903011607041120349952200c6009850b200031000c0c1000066912940e4404000c50028000c418090110740d15100380103950101c1e406400090000b030300d4061010741c0941c070031101521a4801d80240174003081c060b10844080030410000340503c2c0d44e4512059816244088107075030550760b119000000f0906003005140103e000c0d40b9004042d09001e107821065034100c3c0f43d034600c01e40064403001c00b80301803000c020048071350607580c4948079040c0c20484595a19180c0c880e9452044140d600c1c0b0403c6004915088510340c2e400700048400e451b28420382004000b4080e50fa08500341d0001b04010609404036488014403030b2046a500032011000c1a05014039100410460710680c101403045203058082c0c0d8002e044000c2071a59210f20b418402003605204040c041d00340310720280410030f00308940244a035480004070449620036500c4000410113000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 609526267 1250 609525017 609525061
    0x2209020a080a21090302100210020304030905091005030309040911030106030809030f0d0f0c2301050709050405060a0b072d06050105030f0a0201050c15010b04060314070804080f0702040203 83
    0x1510800540e80320511081a1034925144da4403400182140d0a000381d25503580e400409510441e24030b40d00701485400210f1084d84030343d6071403003c2ca1826091004410001d1308101c80d8a02c02d500c11700190310008240d5402c54011140401c1e494081d0402031002402c1e200302d16019401e140c408018440c841000300035030b04c07051b02200d130f44d00c1d94600d0303040d00c81700201240c00000b007004003a0580a0f10500140d8404c6000f00e03587e100750001000c07a219808004184480c080c0d440c0c4040102c80e54100f2100300c0101810380d010700c100c2c9481030000d1400c00960090710700036203000c18840c013400003101501002c0104894a0b41301840040c1103a00500d40c03540d001c890f410709100003c5000d08001c642004c041d1840340c01865590309503401900c00b40c000c88440e0180d84100041c1e1030076002d10a22050081c0b0000c010306503550b050150090030b44a03078880381004080d101051110195110401950003500b00003816111401104e030501c09208410002e54454008414030044920145279400c016107 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 609527517 1250 609526267 609526283
    0x9060708030f0f090c040209011418011b080f071e03080f010b07030e150d090c080d02061009021305090c0310080606010e01120b0306040506070306090b2209020a080a 73
    0x51400002000c0890403102140c2c4c580204a0060b82d42c1866005845414814104040702c503e0500d10541c82e40c02548182121035909491110303c0d5070010811800d0320850030481641002a4803454241c0c402d0443c2c0d603503c0400003070201e052200b4000f044104540c9c0b03190511207412103050007051164107450300850070802d02c0c000540000780302c0417600601d40c940c0341d0280b408440c1081120000c164001216484e41c204100c0030280d01c144110035202d0b00c102c000040742400e151541d4030b0700c010481c2c8601550300013010300c102207511140c1c2a08595032400b001d81c1c3e0b152240c0341c0425045459020a4009001405100d0140340c403a0256101e40e80c1c80c5503964104c0c0d6109200c903a2084241e82543c00328910b40c4010b01c0301d500c1100d80c48165a440f5102140c41402071340424640f0034219001d550300e0700441d003403007461540741c0075000007020034220501104020200241a034801402d0001c440040d41004c3c12100e05070f900030b15240e1760000c00d854241652908544d0700c4580522040754107030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 609528767 1250 609527517 609527521
    0x9071406040b070b01140f010e01080a0b102a03140c0f0d0f020d08010308030a0b0307050d06020a11010e070504270312180f060209010c0f0c0e070c050a11040209060708030f 76
    0x2040000c11f410000c5c1059540c402d01c060040019500100301400c031040e020384428000d6004d8490820003503180c03001e031f030311050408251140c80c13000b8241c80c80c082c0d203004090f601900110b03a008617010800969800070651300d61510740001e2425403030890b2114503018040c205400300b500803a501466130529009d0300c90310640114216800175003400000c14a40041c00400d4001800e503004802801c0050200c50403140caa10010340c00d043c18031021180150001030448140d0390000d01c0c481454107000003800100340a02000c0c1e00e801090003514042d0b580c800c16202a00c0c4040490445409400b9503c5803004d03041c14000c26032450319005400030b608043c541c9105040106100b4405030308640180c054491a60354440a5070107106101e0400401890440c04189801151440710744558a8580d00915001c8420f0b004c072001007008060101030b4032101c01140c00815410141680503c940c802440040f001030002d0048121140d0041b40200d141c50411140000030360040051480304002ea07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 609530017 1250 609528767 609528769
    0x60e07030c0e1009020d140a0c09081b011202120f04020907050903070b0a020f0d030911060c030d0c092c0a200c030d090b1503030309071406040b070b0114 68
    0x1034241902e10aa190404060401a2031303026406042c40041050011818003503a22101c444484140c540310070143d07681a42005480c0c20203007a030f00070700c5070300080c1c85510854118110f031020300306000d034107201410703076030001420a0390304031010712069440036860f80c1042810340c1c5842400721000c0740680b1124000c01c034060300403029038010210050050650508002da1081d85da0018817282007584600040e04901800c140101e011407007480e5000500e01e11242000210359202c3d45444c0d0081c5e42c10401c600b8400c90120448003007950074900424030303490f004070483d460511a0300c41040d400300308074907a01d540c1c0c11100026400c0c811240d003c0c01d5490700b480381401c5542e410b26900402c41101c3e101084c100182026002c0104240d050360305020340005c0007030644e0507030303041204c9808250082207401c82800d40751407040d6100ba0010b50075071425441d030710f41da54500e000c0c400c40d100c241d00d01c460280d603486040710050b000b404c82141d01c1d00414035128051020a0040d035545a01706a040c1d802 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 609531267 1250 609530017 609530039
    0x1020c030606280305060c0319020403080a0e130e030c100e07051905060307200c01050301050409060605130b10050f1b0a17030610051207050a020a060e07030c 70
    0x5441d0003051200c441c1d00030091030b0400c0c12550f9241912020089000020860500c03055108241318003e03103550b894607891070702280480800000420384180814030105240c8001e482660000d420b0040c429442140081c03002a40444007120741800e01a050710400750100c080c000019903101210a00480075100c0005c1d03170b5402009c1034207a400b6000070009840c0480c3c49080703040b04130701c00c0540191140701040320741e8400c94038140030030100c6500d002d209014517900f0002c0744a1002404014a00c500000c07d288810310503184115100d1180006010140e407048000309401489041d02a8030349880318013030404a170b000b9200d20b4001c6900003600340604202e0301004003c1010510f046400686540e244c0c80c0b01508149900c1841c01d200c00090100090000c1d44500c0f0000e50b0b200d00d054410041c819032100a18010040140030783c101c460a80e02c0302c203401a007282061501d078104c0c48803c81c94030b094240e01070b28503400c25051001252020400c9000c2d20300540f000c401c07681d1030f14201c0078 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 609532374 1107 609531267 609531271
    0xf03061c05150108030a120b032505031612121b050f060109060303020a0209060d0c12200d0b04050c10030e30030a090c1401020c0306 59
    0x1168400402d90040410340300440c174018038900e00820019041c10302004545e01c41028064558041c0055410200010881d5021841c0c00300303503011071f083d28414607007c0c1c020460324000e05801c1c01401001d555001d2140c11401c0b4441d5510052080054011002c0041007600d4580ca010750040030180d00d406040140442c0000c5c03c6a54140703401a4091155a86404801c00c0002d40105946890640440e0120300990740c180105c0c0e080524102d0041840c2090f40c4041400001d0307a1a1420762401907103c80d061000c0c0c0c0d0340700a501c0101100d43c42e80610881d40a50004807060060307a8082d10404c11340e0a440c0285002c42c00600c1690400800b003a2100c21951007480100103007404846601c100315030000c40c10f688008894104038004440207000000607a4200f070b1600885803150b4041d11590101e56201a14601c80c801440458010700982d105440a4070300020780e28 = true := by decide +kernel

theorem cover : BRFrame.Cov 609352517 609532374 := by
  have h0 := BRFrame.cov_init 609352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 609352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 609352517 ≤ n) (h2 : n < 609532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
