-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1796
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:42:22.741261+00:00
-- url     : https://prove2.me/submissions/0f9b892f-cad3-40dd-bba5-982b4edb67b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 322841726 ≤ n < 323021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 322842976 1250 322841726 322841741
    0xb0d0609110f241c051006140703090b031b0d0b0a080d020601051908030705011b0906080c0d020c031204050d050403030c17040803130503240103030c170304030e0901050301060810 79
    0xf0101d0580141d0310b503c1203000c40d40e0072219001a024065810702c1195000101000d83c52500700b403231131a011040d54010b00c0b810b9603120b440708210f4080b0202d5001c060840106004d03072041210292109500d50070000a0a644508140268051040400c4031080030500400280c0550014071a9910388000c0c040901ea0b000546d0341809811203020904200500081440300d0040c000440e103456500c8a400510480410354424080071003030401905d908102c0481d44070b156408081c0d00c5100140100c0e011740315070240b0324403e01002801e1012505e03040c41960055000340d04481c2038040380700d010340b0b0920590001901050700481440c0000d40300104a00c04070064019050400b070751103030024a140c024403d6950500d40840090100b41010061295504010003407505a421046495407280784103000140811406900790303010700010b148940c880050201016980b440c0c01d041c002c00400401c20201e10881d540000080e4600e41405058141d80400006e8154072141d21541001498007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 322844226 1250 322842976 322842997
    0x4020d0b070c141027140705031e1902150918070903210c020603070302132301021c20010c02061b0a0509040b0d0609110f24 55
    0x8104036079002400340c082001d03c442a201c0245094541c071400c0d1016160700d400381a0058215045942881868844100281d60405000c018800084094a05000064014a800d40314005155012403110484042090081c00c25618141920388840715201c042e142e010354403400d80404801171444020081c03a5540000300b5078940c1d09084000e107258841d0031100c5002150600c481041071018203c164030780e5254042c2d01c00c0211440c14000307403145a0164001e03008801c08000200e015010783d04031002545040d01040c040ca6803804030080c1c0070103e03440d0501205845013076204d203500009c0c2c000340d0002d1021030b9070800240104101c92500391900e03c25080b4035946088500d81d8000e200f006460181580036002a20740090b0040d0090725400d2100c070500d908010400b551a40304090703d401100c102d0f000700d602e001100028490340510f0303002800d42880d0104a408114168580301c201d50b20175a01c0d41e002580700710070861042001c0c040b0044144007914070300c40102d0310000a10740310b0314 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 322845476 1250 322844226 322844237
    0xf170303060a06260403050306040b1203070f0c091113120b0117010906020c07030318030b07031802040f0b0913110409031107091e020315090c0d022205040504020d0b07 74
    0x304c0346440c0d07808031800d60f030130360100c2c1c00001030010701c0c2814051920904000d564410961090312911a601e01c10400b01510000c0c03150003000421858101c4800201a0407000b404400800410944d0551118201034805000120001003c0c0041e601d54030409402c600884441c1c1c1c6071001d07040c01c00c4c2c111104a102035503500c02e0100000c4071403000c0c0c500c40d4002c2d030041c0082e1b400c514025203640f614944006c3c1e00c1001400410002c0c2c01c00e85515400022440c0100d5002c00b07514070061510a00c80300203500c0ba042c10440c4442000c145c1c440c860080e822105101d01d44c9034015150351039000008054801310b50700d03554840c0c41c24207030801564580310b868980c415414500003241806800e030000c8a40b20f8582d01c0e0302c1c03000da040041414205031000401c6103542052210304c000403040440076406500614002402420003205689958114a4080d0341e90b401103c1305000220343d5014000040c11204008182810a0f200c0c551240c5d502a0210302003000607200d408009200410304000c008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 322846726 1250 322845476 322845527
    0x140601150f0e01140f030412020102030f04030c020a0314061902031006080912031e010602031303060506030a050304080c03070915060c0623040213140c0c0f0102040f170303060a06 79
    0x500d5030f0010820014171a00d0b240d241c3c1010308d4410203035010303e40750000310383c01401444041c800e0804010b42050b0f140c1810051440b1520224946007a5940090192000d03a0004034202d08045502032089240a95051000c21a04d040c20105d02041c0c0b038200781c840005c03600740403550003006080e40050703084084070032080200a400d03507a584100c40e0310101c2030051010010101c01043c1060252000e800a5803c0c01c0c0f141192041d64002444003a2a40f80c03181d000c549240c44c18070950326030a4110043e40c0d42c0741c1d140c140e1240c1c0c8082c20489140680708035100092401c3c500d1003091410410308503454503452605c6130031a2040e05050055400030784c0c8194524918507e40b0003407248100250000c0c0716442c0c41d004010210030a600c45d8a44c0783e04140d400c128200581111b07541c8240c035843c0060b111f608410400d40303030035286482c0194945c4001004102d507912000744108580d41c004460b01c401155066498a9005c1030320750581040a080f414854140a805e000b20026581c00c0c0f0307643c0b0007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 322847976 1250 322846726 322846757
    0x50309091006080f0609150f0316080c0f1f021f0b040c0507240e0a06090c050118090506040e0a030f140406020a0f020418140601150f0e01 61
    0x1100c291488454a403218108102c50342d04102a1513010324a41c1420a50b46001c50220710391150091091401003489906008a507480340c10701e1078040c50140032102103400441806024030076a005c2d9100c10300c070303000e03907480186000c1a020b0900380000d0850403034200111a804400410101b082d025401005040340ca80b0fa80d0304126a0015060200840d00100c11810b0004840a00c00c0103010410100105170101d61440030000b1000c1c55001e951801c08605121034004001e42d041e0200c0500505007038500b0b0080c60740203030310000c0c001c039040b103c09681c0b0001900c0050400b90b082210302c0e90290100800d14a90340130f81d5000a002d04040f81a4510000080c18001042000c9001c0340c5c0648a1200c0c150340010382e610b0400400700f68a02d020f0a000c0c01a6807101040382c01845020036800d80d40854549400100d011070100c0c84042280710140381c205203011000140e18410311501c000080e102e40c03800100704215040b41c0f030f0400c254405005c05c0700c3c1140040382da5030600c1981c031a9000d10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 322849226 1250 322847976 322847989
    0xa030807050d09090c022a1c0b0105060c10050408040306091b29070f050316050c0301200714070b18030a030e2101020d020a0e03060106050313050309 66
    0x145100d440681080003042038083c0a12916400200c0b14900d82100b0812042d0000b0f00d00c0c1d2203841000350103c0d2503012804000c06008038642c2d4070b40160000c0c1c01e90401000d00941c000c140c0340310f50038801c580d030303280d01c00d0050034000c0d2800c90321a0b510804030b01160059651050b0f030172034011640f0b14030b00b648a0702c5000036a0048041103800f2409c141c0c07900304003060f4240c2400908045940d001000d011100040c5101800b4031a00c410110000f460004005045d26030a00c090f510400750390701d40003410043c18003207141903000e4506026621580702d1900d03040c411805000b04455401101c00c1ea0032071866040e41186c2d004540c0440126119162420308100080040060895995503800191200040d0200c5150514000d030300c55543d071400282c1016084040300000d44078410980d0700d0b88611030240c0c82242c0420a41c0d48005407100240310703a500105003058160b100c10030461662018195940e07002d105400c0000c030300340042411130401c214800411800381c41141d003040010310000e5074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 322850476 1250 322849226 322849237
    0xd0b03031603081302010f050f0409090b01050a1a0d0c200606030c06030f060108040c03120c0b01050d0b0417070c12020307080601080d0c06020c0109030c0204050a0c1403060a0308 79
    0x11034084081d24508059011840c194005008403880e02140101c2c0d00181404004002d80818420081780c00803061510f0001e41c0c000b00294442807149240c0340c144294010b500b809590701820414001040c28070a040441400c1c0c0c0c080a5600e02e4001820f40b014028500b40c03061500304045207000d082c045042005140c1e054a50101a2000382000386c1018500146050094010705c824410040044003c12601e81c2c0081c2c00e00b000c0d02d00d40d586150158454559800c01400135800b07605c0c00e0109a03000c80321742c100c1441418a041241d8880040004a06450000400304400807000078001603664961820841d049000d141c06c080050340da154451260b50025911008002d8481043d8542008044010580d800143c034055051203800c0c2c0d11807da0503d68010321047c42802030400905504960340c5a94800082116070040d00c0e009144200c844401d078842e600300808900c0e07104562003484401e81481d1106082000c8041c0d0041460708020300580d44141850ba0020114820000030705 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 322851726 1250 322850476 322850497
    0x1509020d0506151827071e021e0c090702010b15190c031e02100b010305160f05190f020d08090c0d0618030c1b1a0304050709060801090302011a150d0b0303 68
    0x11414900305900808081191031f007000310a001908072800c041c2c0209007819040000440d014504c0002e18025280c103005030b82d800c0c2c0004140040000301d680c10b622000b6000e10880707900e046141c500294442c2d43c000c4501c0e0160000c000142d189410780280c0307000061500c01d0804103007007000c02d019403000400051814025070041c001c1d44490400d80e101e50a4819802d003010407090418000411681071041000024001509a41e050300c9000d0410785160302400e951000d00c040c43d40500401d40c1200d800207102503c40c2c2090b10108034082c000030392084031100c00400a40c01e4420800c00e0355950504c1c02d8642e5a40e4480b03d00e00c00c55035000c5d030389030503010b5110150b0060340d610f03100c0205044d0400002c010000341000b800300c03021007464010200010300c11182c5030f86603800d1032420640c107640513410613860800c001503400019000500154003940082025820a01c0c0301c81296150b028400e03400091200036420305680328014107450811080700080d403101e4140880c2c5980c7c01100c451 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 322852976 1250 322851726 322851799
    0x10c060f0905010518070b0c01140127060e0c0a0903020303040b2a03180f0406080708070806060907140705060c040e0108010b0112050a1509020d05061518 68
    0x1000b401000d015075900f00080801806103d10746615468079113020340140c120704d001c0004c04811421094000780d0b4600c100006240c41540d6a020064800300307030804481100500302841285000a889401304448450780c03130004a84c0e51101ca0012540101121740c2840030300343d07010000d038500b00007401c00741a403240e03c155141094410500700c0070004154066461400e0403200d580d00c4c2c040190f4514491400289000032546400651040b0409081640061820400158818002950030704940500080d200056110f80e4441d440e1001141c1e41500a68900003080c84280b099401c030030042c0c0c00e5001c090030032215a6415043c02425104a640f40501103010b008035569001d1003401001240020051816000006820143c8520003402e000d07075114001402000950480005800310b094000c03402a120165480290842004810118a0071001035001c0c06c01489200c400308010101070300304007040c1103040031903c0c0c1010540e003000e240101450402080117554007032a062600c08d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 322854226 1250 322852976 322852991
    0x70e01080c12120d0b0d05060a05160806060d060f06030c0e010512070c02060d0c03020c0c240d060f081b04150306021303080a0c0b130c06030b010c060f 67
    0x80d40c03801401e07198461055000c400e0324000350318000781c2601caa02d20104410303221600040c1e014014044007540c9034104094480e0071040020220b58a84590f100d5401000561201010b81c0c3c0740105245402c00402c5100000c0f0741245800740141c0941c100c03101000c600e40d612101c1d40c00080019601c02c030007003510f070440489202c2c1c20a50720626443c00386003580c02c141c2c6d4007601e01040a00607100c8014000707100102810b64035150200c3c2c0307010030301c220b040c08161150301005000794401070808200b400b0742d0b030403005546030100ca0050449d080b500c02e04240440001ca0900301d5001a40b0740707001661301c00002441100350b807150401400301070090144941019550304031103551000a510580c50810920441c1c0707070b060b000c0d405503a003110005880300008601445205402d40025000d004041224910305510117045000c051207104545001c0e22480318a803042c401490000301010a40b90b018007525100e58001d101c3c030041454444010400c45c0c9511701141c0401c12100c000b203031541e05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 322855476 1250 322854226 322854239
    0x3070803090123010e010b0307140702010903020402210c0c070611010f091113060b0313030504030206030a1b0509090c0d090c030b0115080c04050d0323090f0105070515060111070e01 80
    0x19180100108503503d4903510b09270a00a0604d0100e000340e44002401003514025640b150603502c02a5038082d204559805440a0054170454419140300c9049488000110340703a00b000c003503581740b58480c4002c007032480c03c150080e2442d40c5092404101c40d903039003100701458480c0e4002c01c2c4513540100e00381c2c11400c4047c1d06009021f41c01495800c3e46509028081041030b45007021245e2020940701c0c107128812042c0b03021202c920569001a5000320080706100e00448150300a0080c161010842520f1940711501680c0900900804903030003604500013800000341040100f40c2c10303030b82c120b00040c0302d0525640d034145400d0a030400d036088204000180410404050070041c41c0156042807090f524103001500c030144954040c00d40a107010706c001e581010b00640d0300560703410801c00040b401a4055a03130380040e4105015881c45aa24544199404d500400c1210103454110001e8134821a00072a1280480000341a203410068001031000320700c00306000c03400250501030003805c240e5141c0700 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 322856726 1250 322855476 322855499
    0xb061306050901080a0b0a1e0308031521060103060b0414090f010e1501230904081c060308070609140a03080901060e09030a110c100c03021006080307080309012301 72
    0x10038070a0b02c1352406c043c80d2001c0c0d842200003c01c40e21800354181e45e4290002c00b14028121a1340b00800200022040c03000341c2d50a003a8a06482100303880084500daa0945140740007410328030040f1558100c48018008103500c0e40124290325005030000c40c200541440304218003408850740c1003d50030500180d4020303c3c0038040c10070f0128960008141c0040000b03100d400ba4803062290345180300012481000702070311000640d400d118020404115441c2906202c0c100307900c0182c5500108000c07016003140e0894a20903103061305d41000d6440e0402c074082d902c00004007100d10094451840b0b155101604140030440803082c0ca00c243d451054038100a842c5c903080d941107400c2411560036410410103084400404d460b4501007d240c07140e0042c0301121040d007000a04d80142d078202d41c1600c4440212904145130400702846982140c4000840400c44000c8078210f000d0004550003c1000700e0109005401450b001100d6000006940345014a03801c500140000b10210038210100108403001200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 322857976 1250 322856726 322856731
    0x191512060506010e03060106020d050d0b040903050a09060206100303030b010e031e06060307030b0c071415040b06010305070e061c050a0b010809010e0303280e010e0f01110d0b06130605090108 84
    0x154020406d9505140001e500c480c403642c078a5007080303004100c1c1d210116441c0c000844429020700200144011814014041c0e4040c12101022a062450003d040c0b0710010b001c0e44102c85145000952500b107546c200c0c06445001d1046040002d4003010714404d50b020f100107590450225603840180505002da01d0404030000d0840303100740c100038820804580c25203c4242e000307100350038040d510595458401c18090051000010301e10920205c1c5d2a183c09105005000f03030302410304e503552962103d0044007680c0007120340000082d0070940c504142c0c1411800f6100b4584042c4004540c1440c400c800c00c111074045803070288542d2502c014a40a51300f003144107400c801c0100092003440d074020006e0766244805810f821070080ba04941c003d00d05182c2203c140c55011150301840a10626449240600701d18890066140689112402d00400500c0380685c030081142d9000d05142d10301c907440c03000b418400700150304080c0810040c911907030014000005400151500760311103000400042210000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 322859226 1250 322857976 322857979
    0x1c290402030415050c0403050715120b0d08130801050c0d0e0a0b060d0309080109060606030b0604080a120903140a0302070906120b070212040314060f191512060506010e 74
    0x1082844040785812007030f0440c0e0401d4100200369600d0b281040300062040798005020b6004032a0003081d03145c0300c00c001c0310150581b0383c0c4142c03080d6804440481200e0029414a5209402d00240c4000600040c00360400300b40c40c0d0100703c0302566501e441400c0d103600b2aa2060b209000041460014000384100540501d80e04020034680c4410756811901c034802511051040400b95000401c0606c61300c14400500b010788001e02c40882d00b0b203044006481e450040300b010a0810004881c1800c1510170398040700c065900511500c513040d250170040e0683c2c1d44984040101015010000c515a950b0301d684050810380145820030070740c00c00a0802280e90800b100301803c2c96000c00c54001405250611b498220003c50620b4440c00016440d00203452440945408085400030601028031401070b9600e078510f01b80c45507a03031282904069858110789005840b070310707140c070100c62050a81c45280c2e110040f07140302c0c1890f51504020805a028002c04840064881c410800c030b41d680005c0d0580c85030300 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 322860476 1250 322859226 322859231
    0x40603050a02120d021e1002070303140108390901030b011505130504150f09060602060109050c19140d0b01030b040b0616020a05041503051e060c1c2904 67
    0x3d2401e0001d446034040500d0b02c1c4420303d101c6c84c03001002414405401c0002014800f195100011f2501a0151001d545c6034013501268400000d42e640000c05d05106c44a5180303803071031180088208603400800703545940301c40102e000058140c25110041d1a81c065402000365203147c1d0b261147c3c403283d5942d03006100003001030a0140c03002c00b011003c482001d03204103c4011620304034082c0c080c024005564444007180644a0001036600c129502100230f035031096003541c0d0700d84e032940d850400740c0307a05881c1e0b001e0348441008017148055007441c5208200e407280c60300b410121205d60042820b17802070650f00d580180d0343c4240c4c084a42c0c1622920700c820078282c9080c000e80340074400180e00c0d802420600001990a007400c0340466441142143c007802008004002014020b26414060119408100c6441c070880c810303102080104101c3c609a500c4c0b200c000c20842d650440c0049154000c081c16403030003593324000820b20b11050160815080403419040030801c0802c1021a8140300c914401e4042d030f1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 322861726 1250 322860476 322860493
    0xf2520060307110f0d0905010216030804050402090616030f0806030a0201020601090c14040905010f1a0403030302071721011502060c0a050408060c03070e0402090918010b040603050a0212 82
    0xc40d500266940b0004900300245030a44540289050200c0b0010000135070040201700801e1680001d80031055030000c1e030031180300c81e4400741250304081c406e01000d4a103403010b100403c001e01d020340007022181e074040c104a040c441c0900b4101c0411540e00030440115003103040300c2000f00d40c4240685e5201c0d40813402001c5030a4180c0001c0d40b0340134180501c0c51520340f955100100107002d00398002410504445140e41d4907525503411006082c00e0040302402011402c0010707400c038501c59907603e04a0820310907403403c0d245560640c025170044030201c601e101380a641841c4111000085c0003402514880424031a44142c014191194160401c20104422500d69052140c0c0010005c0d8000396074185182d403208124800c0e80c0c0d41c003c990018000d40300d00e50803c01d8008603d80558040c06807034647c88000200c0108000980c00386801c0107801041c4140080c0c2001081945441304003030100c0005210360f41030f000b0900351256504151754507030042c0c144104500744542d2203544000030902802901 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 322862976 1250 322861726 322861729
    0x31407031a041a010827030c06100b0a0c0606050904050303180607021b032b090902040e0610140c031c06080a0807150204060e010e0108060102120f2520 67
    0x43c00440c40b060400203a90009541c2030700200120728910300482540f10814402000d8039942e51006040708000c3c00340d00046081209014000015150304888440c2002a40102260380443c01c2100b946c0442d00c0301c0000440b82c0b103c000d034500950103080903650701d25114249000100514000308000d50107102046000e60b800300d104010360010792200c040d41d54107040041d16008260512890544020566944401d07500300000b180002e01d4894001d021342c0c4011001c22800380748603e440207068080001c0c01031038014480b483d410603609000b03503100d01d0702c0c0c000314050b00301e400d405589901c000f43d16580429540c410417240d240260b4184415400c00c001aa1601c803500002424040082052000c1041c61451140c40c0600504119161544c41c900201011407150910303002c1190102015100d500c5100810b204d658180c00410010319000c00210342940300f600c0107552400c0500442c07040000d08203880b0075091059042d80c0052420381411030b0345d6150700003800c485580c0c000061401c0e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 322864226 1250 322862976 322863011
    0x3020103150501120b130203070305070906090b04030b0c0c0a0c0f05040501050604050d142506080906060108130204050108161203020712020a030203011806051006020a080a031407031a04 82
    0x50250900c0041007100d03a6001040c90226402c8803407446c50b00100402001c41c0c4c0c103030702441c0309062617507070b4610341a601c140603282e081150040441c407600400c0b040c000305d8031104000c2c0e049904a0007075850041505586030501120710421165204402800c00c0010400841c00015003401c4404000d9541340000058407889039201e054000c0340580400c1c010b01004583c40c200d0b51002d00152031100c90a008030510722880d0704401c003018503240b907011840c1c601c1000080d101d10000c00050042e9126140190b580c000010188a503100900940310010389550140c0c0d4000c02c40c0c4070003480b00fa140300c401040c510000e5000500010300c001d81c850007007a40094414122460f0320408070301504203002003282030142d134002941542c00c04011203aa58a02e20700581010b0182800b0442c0d91903100903c05160603d11848005910404101d000725036440700401c610f8140342000900720500f00038500310f1410031101800400d0703032440c00c10108034441a19a2418000715403c008414100b40702e01d84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 322865476 1250 322864226 322864247
    0x2010f0b0a050330030411010f08240619111e030f030c09040203040b150f010f080a1b020318030319030509010603140109020111060c030403053103020103150501 71
    0x98460010900d0100030307a04c82450340092036001090f82d8070b02e0141041400c441803040c03d80d00280d0488141c0e0050f910900c4018000c40241c4040c2d264003024840344044024086a103a51105042003a02201d99803842d82c210303c0f01150711003813101011516000c0c01d0018040c45c14000f200c2c4c2c100c80080d490400f104a0fa940ca100a15031601c030703160072021a00d036008107003200d40c020b84000140001d00068100341440b4800020400000e072004c1c034140301485a80311003c9005c15a0140e00c0e851756406640556444644910001054819882882074a00900c0000300c0907800c0040c0c0b10084a000423501c07092031005400079498500c1040003849840b0300603042000700340ea0340c00441d422103003e4010000954010400340003100103000a14001c010f8000c0890200b029075100b2840044041402442030543c0c034a0f00f0305580d0385032803d0311640e0191b0b5046000d10402114810080d0103154000b0520b03072400400024182144005000c0750011101000e00300071200b02004580c0e0f0041c0c1411 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 322866726 1250 322865476 322865503
    0x1b03070b07080a030906060b04031b080d26070e1f080a09020d050609060a0609050f0c1b01060b0307080a050613180b0c0903210a0f140a02010f0b0a0503 67
    0x1660703030f440407500b10020000120000c0c00241030420001b107122900300a001600e0140484822074902604070480c00341461103402c4468100119201c4000c0c0503d00d0114611340f40040c0c07240c25030201540c0341c492407003164030344041401e20f0560a2241000110f8135482040079082e2900b080102a000d80091001000c0070381260f201c0c0380c03107021501da404402a070268483d04a580b10300340441e125840b91400c40c0d01c1700744d03540f6000c80090418038500600c1e000e88100c500100c01902d07500c20307064190303000381c801c541040803010305c4a5014200f403140c0b100a0a180c4141038490600c007000400d00d503005401c002c4400c0c1840107021607a40c0303140c01e041d00c0c141e00302c20005010400702c481c0400c02041c010090b01d00da490300104681115100c00a0200407811400e4800524a400247e46810100030400e03420b05c10510050601d140500c03608149007800c2c1c101081403030038041001e40d160b405400420b0040c1d454480f0782c02c1c401514041c00505410403105043c50604000200360380f00c10402c001c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 322867976 1250 322866726 322866743
    0x311030f04121109090705010201050c0405060405060d060e0c0712111c02211804060303080403050d06050a08010911040b030a0201031a090106090e0705040302061c06171b03070b07 79
    0x40303081102c0c04112502a200113004040285440000552941b03268401d0b1405542800c00188182906104840507034500400d024101b07400c02c0c0c14400d4607001044c2140581d560351401040d20307004600d03600c0c4101014003c003503a03195180b4065030203604070400c442c1803000110400c4104000441d40070780d0041c101050480e0280750f45800c92030a00040102095072603603110313862114200f40c0050985480a03030201155030014014041111420310000e030000b2121408140046d00c107900074614403040301c801181c05c0e920741d00010f1902105a1041c02144c1d5110150b404100d081c030500080c5040496040050381823910100351100f69100000b410990341d01c0a860a80b1b142d201c1c151030b0064060804d070141d41c2c5400c401341c4022020b005240c0b4801c3c2100004070305510420443d81075075406056181004481c5a401c41c0607110340780c0381d54076a519980003040082c2d1054081003104e04120003001e01481c3d00741c00303108220f551460300d030194001c206e00b4090b110000c8200c4001c207603c0a50b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 322869226 1250 322867976 322868009
    0xf0304060b1315050a080304061403070323070e030a02030c010f05120f04030801090b01051602010e09071d18060d050a05060a061701151701020d14040311030f04 71
    0x74a80100a5203280c0c061441c00b5100d61044424040f42d0090b610141c03900d2541d107072100005640ca003c4c900c00c560003d80d0702c0d0250030558102d82b0244d40c0241160601151100c4240003040d03030404c100b15115070641c1c50004010174158001303003090502c0c0050b4064003918005402107a1184034100e1401d05120340d4185080e03032184160308030740c451980300c02445c400382801c82c410444520309460503000a420341001081e0554070303102d04404060141c5a051070f100103200c00c03006440b0400004d0741400b001284036106500e504045034030901c6503903148a000311606841c0c61401454940c0c40e401143c80106103908542440c0f0b12941000702111000125491071810354030b010341d0528000c145029901c02d2100394402a0420005e54002c44a4030b0005061152114201e03100f10301c280310150010b44003045407001c00007156040d85410000513240c0361150141405642050b030308401041e014004210902da403103c04181e2032030042340034510303100a811440e80e280c0114001d02c4800102d01c140c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 322870476 1250 322869226 322869229
    0x50603061203070f03081f1509091a031b0112050c0f04140901050d050d0c03110316120c08030417071505090c10052a0f0703030e01050f0304060b 64
    0x8010400d03210040440382e0f21000d900d4003e0604c0d10702e4000300e001ca07070a90040392994460709410741f40d000340c100502e0181441e00031000c95801a146034502030115030100410b919105000d100100b08112070030480e103040c04c01c103262401eaa80d80d8400b28440404008081981c0d010514204101c4c1240e03000c601c3e5110f180d4400c000748980642d281d04148001000070300382d09100c00c01c9003984011034800200fa0380e510f01780141d551441d8802003194020b0881030240501888a0340100d42c007070700d08030701c80d892a1000c8030301d160700c505200c21519100e142070000b008400710340083c800403e490001e840c00107580c0c2e000280e000180c0f00502c0c0c940103107526544420550240e85945030000310102180d05286880c400800b802e032986103141c09001c0000b00b442c140188070420130907241d41c0b102e03d001d602101046400e030410b4010300703011080d05c2408901c00010480c21680142030005850120310714a0b000c0d0801603080e2045041c0501442421510060303102640e40c840d800c00008100c0f5001c000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 322871726 1250 322870476 322870489
    0x18060904020c0114010306050609011202040e0a0b010b0702031e0a02010507060f09030809060603010b0f01030213081501060807110a030509040902090c0301080d08040b0403030b0102150a0209101805060306 90
    0x203544801d250720f01040703910f680c58140d13a414120380c001c0390208029152103050001d041024015004c00d48582c25480c0c0050174181e0000a001104c4401c2da41400b10590302c5450300741082c3d120484000012a41c4425458140040f09982d8400c01c02c03500004990070303540b07031210707001500079060020124500c4144003580c1c00054140650500400000c54649000b034440482559894403a1140d01d0000d8014103051042125180c0010403000c04a944a4011000382d40182e1091a805043c0980010002ca080180c0c114040041c44444000e40c10700030010f202450042c002d000b001a14400400041c1e00450005406501840c00d1a580c0c0300040115000d000321800080d00440d9280801449c4003401000e541a21401000e0b60014a81840120f4100c141520090a14840b500124001901035030000b8080035060040e12078510486d4940b008005c0f08a52070780c84541c000495071a140f502c00d60072007110010342003c0300d003889481ca07460003204c0b01d4000e40d40a080c0c00808600107a4621 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 322872976 1250 322871726 322871737
    0x27090610110609060a0e0318090903070c0801020a080601021204091d0f0f0f0c0a140307150306030c0b040308070308061c0302030d0c170703020a050702060703080612031806090402 79
    0xc01c201d4100d8188401803030340d42c80c401c50f800b98015103051520f20040c10048111828445036185513800902a00c040000d499800343c0306408520040000d0700014002000810040a00c1c4000585940001a000e403a20301d004000b18110b4200340c447c0303925441140150390076940410070000e1034810704a03020704010460610308505115424948001103000074455180401c2c410035603000790480381429a59181d500b240d41c0c0c3c40400c064040c442190000300d0890340c0300d40107048401c401ea83d00180300001c40601c003c440000d49441c03091003030025140d95400204080da000c580740a10716220460075000790709004040080c104081503440c2c0da80705c034101c0340303003103501c280250400c0d6890040c0d5a6845440003212035420b03c0d90700740b0400d0140f10740020980540e01d07003586540d51200128002d62003800d4020501c0001e0220398050b07114000900203461017500c41d4141401d101e01040b140f0346070038000c051030354030800031040c0428060821314481107041e25010f44480c40d2500040c041d0050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 322874226 1250 322872976 322873007
    0x705120a0c0c14040c0306051c020409020604031506050109210303110d20040b0a08091603080c061501050a230c010204180b0604060f1e0527090610 65
    0x2d00d4040745580e000e0043d0750750150100c0341000540380b0b01ca01941603030181d11419910800d26000c00344503207814443d4501403480207000044c80c600030360005406400641058565000807030400410302210311611010302024240710001c40e280080780304140044040004500001941d4001018000c0c0c210800824289500940b2004a8031080d001030010917030020305c1d10001060241c03140301010403202950300104c900c501d028600780c816149000050310f0b40e90140724078611548500800300d00c40c406984a49074130750741c44a191006d035260650162803d0b0b82c0134410352040c0116a000011182d010741701d82043e140c20b2400d481c0c1074010302180c2880e6100d0325000945d0200240b410750050050721504140d4800080341d0002a8048841c000f13001600404108400c0c42034034001c0c80c107500250300034900f8000c2002d11410241c0c80000e100c482c000820004200c00341c05170f407030400c0c0d0b00002e0341800c1800c130031441201c0040c0c0d1404029081c00e0140b01e80011802e405c82c071480c10401a400c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 322875476 1250 322874226 322874243
    0xf031214070f0905090f010302062a031b010203070915050912070302011707080a181e050c190308220305062a1c0f09060b0a05060705120a0c 62
    0x7030180e40900300e1541e0070001c10009600d5240820f8920f00303901e00901070720180540c00360b568215400c0c810298421001000640040c1d501d620988480c1c100c020b07a043d10201c09907440b1368480508a285044507c0b04141590040c000c000100da8041c9418045910001503154000c10107841954541302d00210590403241c01c0c80610100480000d640c02101c0c800e9035000c4106a100803281d05559040c0c641a0000701980c0108003401460b81004642030301c104038012442a003651004441178100001c58000c20100c641d0350b00303019080c014035071a0b0340c0603582c0071341081c001d140910305c000305400024500e10000c5025118102804199211140400e024078211134803403d040b45d0b101000c42d0152134070701c0a4503205140e0005000d00000512070231006a04001e01d4208501948000340c98801149070f460240145c0c40b1028001c504545010f96000908621810f0600c0b01d00800c0c2c0d0000d501501c010049200040d50002d2072055003401d4000158035008a600221568201494050b00619 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 322876726 1250 322875476 322875481
    0x5040801060e0405100203010b0315030c061605060a0e0a02060c0102090603041b090b0108040f14030d06090509030702090f0a0e070f050117010302030c10031d0601150c0f031214 78
    0x69080001c180038601440c201e80c000b800170400001030b803000340104001182d01380086000b0640ca840c5158016030014282c1e14003c0107800499901c1e00038000800841c0d500300800001d01409100321340d000200b02038140f00350642c0040d107695903201e41000074003900001a800051500a50544141900080001d40d83c1d091908000008500c26500d03e40c0400b10450001407001c00c0e071041090310760042c6c503510556500c40e00e03145540c40c2074030025641d4070028803a504007500d0500051031202c05180c00042c4442c1001d0a80c0c040300d60041051220760300401190015035200041c16600088070980c14066079111038180010f440c0c03800d100340740d0740b20307090000c11040540800071094850031398908003d08500c9040814102c420300c000381d0903800c50389401d20603003400d030340c42a0000c046040c045111a190641d1041c0c6a5000742c400105410000041c0220a4041807038841c0c00001c1c43c022984070440c2d12241d884071070f40c0703600400303100c00d0000208441c449900301074405544030400040b2403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 322877976 1250 322876726 322876739
    0xc12031909050307121106070201021504030305220f2d030503060f090f011a1213030f0f0906030f0b060a09060311070b0f0408040e040c030210050405010f0e010504080106 75
    0x1c03882c0600c520074042c6000c04a00040a90b10310014140c02c8820b0210030301c40c1e182409207a9005c40c000f6811801060b08003c03440c4440007100380100d201c0c2e500001e40386820011013129092005007403540c031250304511800f00d030504d854103841c40d130090240b030008004010400107854074070f140e01c0c00709501c982d007800601d134000c0c0203180700b1003080e6000003446880e50100a007045045072806e44840030840140101100461800b45121039132a00310710307150f40c6c003221080c022400c60f10402c0408103c4151800c05500c03500d585403080d04d03400c10036100344001c04060100442401018209070381e82c4106241500303150071840c0b5040380500102d035614100d0f034000301003500038080e080100e8140701071007803892800c1c022115001e0b0000000301d00c2e51a07954004416020150050301c41d000d05000203c0c0500040020f45c0c00350b4403606003025802d103188180034120071241c0c114001c0c000309000401450740c0000720140980f082c0e01e0514141030107180140d0705401681c10110956282040c0455103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 322879226 1250 322877976 322877987
    0x405011a0f251b050108060d15020d0e071701020f030a0506010207090207031d0a06050f0304150507050a030b01021506060d140a1a0406080d140c01050c1b0d020c120319 74
    0x642e40c2d09201e400070f00d80c80700010340d2210010f40d40300d5003100028070100007180c001310020b6825500c44e0303005440e0000c2c4012905c26180c807001201d03956003005004001e4000b4410307008100c00c01c3c450080d400c0000e1100d81482c5804024481e4071159200c030006503003a88240801c80160000c41f400b151114898100244102d041c0d04062004c0001d407003040005240ca51400380454070aa510603142c2070b00400d0464a540003d80b0444910100f00c030f0b07120450782076000d62442110140c0c0c4298450503040c01c01001d40790110580340c155040451503110600c4183c041035072040782a00c4290743c40c48091403550060040c0308012286448078030034804d84402e1600300c1c8d40201078203800903207122041e504000403200a881900d980c6d5021174110240b40d8000d004611500803103500c21824071701e20004003429030364125843c04941d0000908a190341c4103040c80700725081c00810049c624409100c202a545106004401e407150080201821800f04100121400d40e03104119a019014004501905 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 322880476 1250 322879226 322879253
    0x21c02130603120c050618010e031b160e060f0112140105010e01080f070c0f1707060617070603020d0204052205071b0206070f060504030801050405011a0f25 69
    0x20f1210342e41c0481c00d0100c3c880c0e00a01200782c0c1110103010700e5200c03100c8000c80410114400d807041d5481d030b4480360710340000b4000b918019440040d046401c0c0d8008584a08150342002120010020350314244242c0c800440030356031000041d56641020082c80f40180c13003000500299501250514100501081d00c50001d281207800a0300e9011104448034019035056400b1a8207426030f03101200000e1580d44a0440504d10a008807902c070382489580d1141784003e1031a5619051000000482c181040f10900c82c1c2001014090340071903e0b20f03005510251605001c0c480d2008154000c00c601401040c50f0b0b049800030040205034805032000911285140f120302002d515800d40b07031800242c0040d02401008031040520442c440e120820344d400c0000b9a000b140c02a03513400b012442010002340b00c0d20505008902986401c00c081d0b152100b08816904141c101c40000d1200485000c00368034207005a40040a05c1c594180e101d1000840d001d107511111551010412958002c0205001225030ba100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 322881726 1250 322880476 322880483
    0x706020711030d0f02061303050702182d0a0f020c0d020708010c0206060109151206090f110405060f090607021f030f09080409020a02010e06011401030522021c02130603 74
    0xb039140800b2103042d03131807204001030307a0050f80142d40040c1d200d6090300006840c540c0b19050071408d2540d10b4001c0360b101c41100c11074082c0c0343c3d1540140303c1e0500300e005e0300030f0100014640d849091003102ca400703001c005002c3c098a103400d8039858019400c0f2407940607a102a51072104039009050140d400035070390306061042d101c0719441c15001e108082c0c4080340e054880d603410703110240590f140c60810755600d04802d070703044e080200c005110040f811840c0150344c0204048100810114012130031031080381d00300112401d040d44100401c001a44510040e902d48804400511341c443d030303d60021070198410320300e00940c006000c50301d58040c0782c20f69031040600f0006075802c000b103148030b600c508119000030101a141003024030040007200426001080c107401b6a01c004119102e060342d0740e510b000d03803c0e041000c1c5088010b03400c8546580c140b19240e808a0313010f1a00c2d0400000c440c002d01701c441989800313400f4a28110030b0554802a15405034240f640c050701c150300101c2ca43d807041c1c2c010b044030700048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 322882976 1250 322881726 322881733
    0x60504021c110903070509070302190c03080906010f09090203121218030307080103060c0e031f1103010b04031101090f0e150306240312070c0608090304180f02070602071103 76
    0x100c1540358042c3c400c0203a015000b032007520704103001c0181c0700200900410416800b00115100d000e0030100f6840d1400d107548465120215900c1c014100000c010051081a4400c1d00108841200c421403203084030b044580005174003070140046030400801008800c801c040010b400d131030100c6040d010b83d00c0b401c82c00760a42d1050840b002150740b01d03c0152130309000241c1010060010840983c03245c049152241030040300c0e0001140400d080c0452070600c1c1c02866140c520b0078404c000c442c080d000100f20b11482d03462456042440020990095010241c21901d2420341c4d00e01c42e0340181c00c00c0010345080091080c0855482c6882c012022044908a4602082c5c0455503210f05001940360300810203002051200794042552014042405000e10751611611405d00c00102400000780480381c0666082c0401900303241015103840e8000d420031006a00401c8100b10708198041815449560b142c000304040c1c0d00c86084c1c0c0040c0c09039182c0542001e2002804c0010000c080c1c1001d01c03104415800d8 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 322884226 1250 322882976 322882991
    0xd05030c0c150d0507030f0f06060f02010e0a1202030f0c070f06030b031005091228080408070305070c051201020d0c09061d03030c0f2b0c110301060504021c 69
    0x10300081000c008289192028288044042c3c900c0d20380040c2d600428514001544c6200382c2c0c00c0c1c6060322034060481052540e0707000f091144903444480070726405042d0000740f202110461003255507084240d400b40804a40c04505803403d4800d000301c0d00b6400312038013410b840d05030450405031281310a119140c820b14144000003a510701178001d03810b5800c002400342c080000c82c65a0030024100c004c14440e001d00803039100b41040f0140e90051325101c002503001c8400b080c4040d01112500c004496403c00f407140380010040081d16190803141d003c0d6142c84c04503241c0e50076141140740d064650300300e160f2200c0344a0b14141c40b0f400540c040e1040741d9001740d00340012030043e50142c5a010190007001c00180a1414100d081060b03038000c00f02c1c1c1c2c00c014003100d01d001c0d0401c0a007820000b240c1034515050f0002e840d60301c0001100f046600e0703441d545060f124841100c003803016103011001d44004048080011591071696401c0d8000c4d401084d000e4015503641d03103280800d40250030325004e9070740c040f0b240c0302a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 322885476 1250 322884226 322884229
    0x1119020607110d09060e0102070f090c0905040b0d0f140a080903011a0906011d04050a0e1c0215060301090f03050d141e04080f040e01050a0503060f0a0e03090d05030c0c 74
    0x190543e60380003a0300d03000542c0b400c29800b200d0041c145141c1606520909100040044c0d010014000822181c0350004055040f0000113000c1d0200b64407242c821828180d18108541d55101400700c01075109003560380020481c5072110b03d82d00c014503005054041c20584405008845004180c0200d04400030001040c20380944a5510381c3c001741d99400c803043c0710014030f06500034035540c1d51058814070f141a10b03400303d03000a0159902100c8202d40a51609014a10304c0001c00504540c40400159924284a5540000d43d584040c2d8200344000440b2800300b40309480039448036007803640122185104c417040d410080d0059000480d0041168a017002201d03241d0700e41d0383c403903000e0b154080c5401c1c00c114820000500c410700180c4141c52510b02008001d07100d6465000400c010041c000000d03203030358504010403001c400c4562016010fa0004020001c40b85000340310960b012007002d1001034000900b5031800d156000e0340d8a0640c0107200d215421041c042c00002501c081e01c481000c55141c2c054500 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 322886726 1250 322885476 322885483
    0x70e0c0a0e0114040b0d020d06080f0c0d11040203180601060e09040f210903030e090c070f05010b13051602030c120c0a0f060f0515060a03111902060711 67
    0x4005000041c15180389520a6201e900290000c45581c40792504094590503d04800c3d071048990f4410349500244030704268406000b00001401e00b41e000c2e1440100095a164588645e840314a20603180c119a0600b00000407810710541d1502420131500c27440c0000030440000940068860117101e00d90002805610441540114030301c064181c0030079442d503940d100664a41804122461540203450b5903854101a4288404040b142e83d10700c00903185090240000d5a04403c0c140075060000c10403440e00060b4080700c4049a0103144080000c0090030150300500102c0c1022364890103401d0103040e0750003940c02c0140035a0720041c0c030071907100c40c05405a07564801d040c0c01841e142c06c403030f90741d00e400d01400020382a4110381030291051705502c1c2d500d5024151201404440c51035481680c1d00080049104241d48200f070f000b071070324007024001d0012719140101ea280908240d141c00b440d0401c090000240c0305007005445260710a5080040301039183c02040390724100040c1502d403803c15682001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 322887976 1250 322886726 322886737
    0x504020d140a030905100203090112141905070206160e13060b0d0e010501080a03050a1806050a03050a0e03160303021209060615070206090f1801090c110705030d030c1701030302070e0c 81
    0x20b40055227030400309030040d1014000300402110655580c0d000c5010301140c0a90644240480001d00035035864040c0f1600440d5405005681103500c1030007000001c034911003241480b030b1a0750600b65540b007403240000e010040d20710341900b160390178035070001110031422001d00f920004200f0180031901007581c88030300f20b1f2400d10401c411540311115100c0402e0003180201114181071802480e508400c807680d0031030200c2a032050001400004034800d00c5589442100c2d00110001c2050008840c004200b6030390340510200c01d040c1e084039130304002c2018004d5044078207003007170540c913070985140101500d80c0328501150154000d101820581c02020401011155007941c0148182e007821240c03414031901d12982a0403d0f08049080352007078803d020140c0941c020700400a01084e0705401e40d200520010500f0651030f616030040106004590380840c02d401004007603d80060207c10903002141c51018141014080500703c4001105056010500405072000103d07903295584505035814002c0c400c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 322889226 1250 322887976 322888009
    0x319140403180b03071701090903080103020112022505240a0510030f050609160f1503020f0409050106020601060c02030a02010e040b04060617070503190504020d140a030905 76
    0x80010006401003008401c1d80b034200c90707050000c645840000740180d00070750b0200b000c41c0240c3d0300002040b2080404902500d40281d0500002c0c4c3c040e54003a040745010301000341842000c548580300050075a041d00c505003542c1301250740301c112046c980c00300d100300004203588601850701d41208540202000c02c16520303030010b01c242d1640d0340c0030300300005100103890703545520450000003000c5442120a8406140950081d20781c1d0b04140007114906150811012004a40d8000c10410159200c407094100c84500c4000440958400d00c100e00a114801d82d51179041c0d03020034003180400b001d17400141079444a4003110420b9882d007505842e56007107901c00940c95800152180d00651166641002d0454050300114024043e5000141a41ca2030b811040000c3c1c40c8198044803180000302080c0c2060407401c06a156042c20080310503000c00e65080305064544400100f000c54440341001c9908a401c0503601c10a250100401030300c6001c0070b5002e07800141401c0e40445d443c45d1501c04040440300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 322890476 1250 322889226 322889261
    0x140105010503060414070e040614061e060d180c080705010201052e09020415091202010206010312020c0303030c04091a0616080f13261e031e0319 64
    0x4070303542c4040d40054911600851030146c08400141c500e0543c900d00d00440c41954082061400914004120f003401001a0b00c1801344040141c07110b050004a500c80000503518140e50304181c020000141c4001118603448031030b5141d0b20418400d0342160b150a40d60581e0646002546e035030012801e84006035441c194203080481840d847e5145061400c0300440c800101d000c3c543e40e6248050101d0708603070700440d1400740c0e868000102e103a025160340040c102140960f46598000d40000755903480501006200080110010020500801050000e880000c04580d62840e00003040006600244070b04640301e4105488e80744c2c0c1c0c060120700501c6050b805003100e0304180110406003c8030094441c140e580420811200c140340950400610008464a40c0441c54906c1c11641540307040d04c10b081d298803d421250426240c03000800c4801811800c3c44c004230051520300122410362144a50f4803241c41012a00400c0a01b000343c041c6200707400c0c42802490801019500900703440e6803514001345080c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 322891726 1250 322890476 322890481
    0x1209080d020a180b0405010f02061509071209080415170c0904060b070503090f09100303121d07081002071505070201020913092906040b01020c150714010501050306 72
    0x5a000e0a200d1941d454035607500e0b00a5015003542c0c2c1d0f8540c1100c40d142d01d000400b4425540c1104120910190301c1c40200814905208030300c3d50201e2034410103100d1660040882c0a007485900c80c1e1031040c248400412100340700b071030110401c0c0c3c010701c41c2c1d2401c01c0404542483c0c850003081c0c9400c0841442061034101e50300c0002c40821640106c01c1a030f4403544c1d8010100d882c601d103c018151191142c001550703208100c008120b11903011990042c03055200b80208110f400c03554a00300d045039410b0401100340e02414203000054891000759001404918513901a030039000038014003240c2200003034070b062905000f02001030344107056024041030340b0301507183d01250b41980290303072080003131000504028001c00000e00030000c0c0c005a05403643c5550103c4180040f00105140d50a201d560b07440da4810000c0c0c004c90f400d980100b07030307920a40e5580c4000e510f9900034400701d0031202c0011b240390700d0140005c8010751250404d5070140c0d00308400500c1d003001c4400502c00ca82c10f1b190010010481039 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 322892976 1250 322891726 322891747
    0x603080d0903020708150117011b05030a18533105010306051503040611041805130c170f0706050912010b0105160606050909010b01120908 61
    0x14107031081c0c21000c6110740742d0001071003101030200c589021422504800c03c2c0d45005c04040d402d1183e031071008102e900d440361902e04e0040c040300240152106007011616590390042c02001003010341c41018980c041d00000c441008003d221440c24000b2400da8600c200070411224103c011b40900d0300003441801c86107000b06090000d00c01904030f4501d00c40c0d68940f80d030346c104590484134400c038080c00061859650080050000d5052006000700380f17002c00810b454007002a46c0c0000c51030310309066030400404582442116041500c110300c4009a070303541ca0303030f9803010158614200007010540d80d14060108200108501304078010315009186804818141113042c14541e000c10f00d003a10314446c43e20810809441070240d00014070542d180c1d191907042e107500303202040c02d840030f000106900d4106260b405a80100c1901c40002c00c0b40b51102800b40c551400d14001c2690f50002944043c0803010400725803015004003508070b074280c1c3e54440701c040d5107003050161010391100510030341c028403050101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 322894226 1250 322892976 322892981
    0x109020c0a08070f0201020d050c0703080c19050f0d0c0b01030201301b18090b060f040305010b0f030a05210904150303020601151407020f18060406090603080d 70
    0x984006003991030a01c40c503500c404595001100131a2a540003040a00a542e010b001c460f1401107113040c894500011005026200c0d9201d01006006c004041002c0502407001c01c640c0243c03881c3d1000000401c1c00074204250740e1050414000041e104903040c5018582c0700d02408580c0d5640700c4514a83c5174250b500540e42e511440c510b8003505043ca026110b5602d118625000d007103d0400c81c000303131001c01c40c0210b903510f44804200b0414010340740b4030303601504100b0004c0012140d851900007801e00d546000600d5a00c00c20905004035500400c005c4144041940109020305045805801c00d94052090540303c0086e60005800d82c0c102001c0c6072580080303c12000f2804000404c074504d0156002c0001d0115241d442150126030b000c1c032418000c04d07804002d241d0150041703284d14161190b2482d001040c404100c05a11030000c0c010400d07000315124182c00728070801008001351034800c4044e1035050b01c0c140c11120075106a0520301c000501400601c04e070016070344c00c180f85500d0040002e000801 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 322895476 1250 322894226 322894237
    0x30203190e09010308030604050a09051504080c0f01020c01061406040e0a27050c0420090604030b011806060512040f11040507021609050105010c0b0a0b1c02090f0f010902 75
    0xa000031100d400500c2d60320000028003840c450074082e0b807642040e10a00080703400040c00b0060701b0b03103003406281c04540006200d0315120b0000c1034014155030f03140f91601ca540940f0716410802c0c810204410303060038040d000f0f0441c019840c4001c0042c240d072254556100c03d0505e03082a0020010070040c04190312507055150301010015010038141e0020020f8001030180305551001d0400e0f85201104215050104e40d00c41441250144240030f6145d400d0310030307404800010800424001002c07000354070f0702420b8800442d001407400d02d0307070741e035440c00e03190041c203c2d602d6400c566191020118030540944159941080d04204140c05587c642e0b45a0b005c6d00414003094a5407040c0d5940100c00e44d48070300409119044641c00360019601d0407031f4090300c40220fa0803409046040c500140204c1e68003103102c420702c0e0b810849042d000d4a405101000038540220181d82043d0042c80d944200c100c10032071000701c1f901c00d5076030704804d682e68110a45252025605070441800d11b0300100310680c0190090300d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 322896726 1250 322895476 322895527
    0x80c0a03020c1203040b281a030a0311100213060e030c0406080706031d0c0f0d0c0308090111060601080a0e01060e04110301050c0301211a1e070903030203 68
    0x500d414002d00a0b10f192000e1841500c4a000e030000810040100019800c2e81180c580805000c0d240356080f20216507014000f00c1a0b42c8950b1814a04040d1800d02400c4071076600c050141c540d0903445040c0200010b0756828100e16601c1080c1e964006002e080c401c5620030300d4110301c8100c800e424400129503001d00f00a400e5814445c0d542031041c140c3e11071013500700400d9000002c00e80180307000d2019080d04c103100300d1642c80340400759005612080216469120001c119541c140081c0400e00045c2e014500d130b00c0283c420003034010044100107102005080b01c06090300e4420030a4500d002e1142c1e0382804803019400940d29801003262400517070840d01c6595503444c00400d1040d101d002030040d115040381c06845100c40c101201103241003e00c078250b0094680304000e1f28660412108844c00b107920b07140e2500c02d00104050302c0c280030030200c0d0103005108540b054081c50505d1002a24a08090390720b848030f610340440840c40341c0380036000040031654103402540c1020183e09122010070710918a01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 322897976 1250 322896726 322896731
    0x4020915060a0332040602030604110d0b01020c060301061d0a08030a0903110603040f1104020d020409020304050705012a1401020309070e0708190209010c0803090c1f080c0a03 77
    0x44481d58859002e04082000e980e0001280c0300b1045540003619000382e00b8920207507001c100141041480c00390a94825041203003d1394a442c1c00005c10014410307841580b0041c00d0105860142c17140507040741a00420036821511408001010071009103c20321956010540c50300322001e501c4c400e148400e0381584000d1400b10302c550707151040343c01c5070300070018c0000181c03454400380100b0032000218264000180c0307900742140b070305607075200d04803c4608010305100712000700c00c80d95a40b260100c030003095050308255101c41d50343d0a0500650015a0100e8850007000404191035105a0302c840c160448030700340000040b4181d080d0a20101945015034107002d41101400e1603c40900095020341c0743d10000301007161070840300c00700342c0c1c1c400740a080070420010b080c8900b110f444500c03044421041c0000694841000f401030341c0354001050b00410782440030041020040012554080c0c041051713600d003220100d80464449582c81c0c502400012400c404041590360b21500c01030b004032821360600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 322899226 1250 322897976 322898011
    0x3040b01060914510408031c06091e0515030601090c03020712050703090b0307020303192c010b0a0b07122714091603021606050907031e0308040209 65
    0xaa412220138a401c911101054404001103115404d9005903000c041c0080241402d00b407a8499450303104c2c0c0d02910071000e0107000e080600b0411a4440310060a18035401c11019440d0341c003070001d01a010380d000312b0580c035210004600540189202e128441c0090191000ba800c141400000309001089401095401d1080c940001c4080320700317184135181901c600b900d0745c10510b001000e80c10150080c1100042c180b05000c4030316000000d0704d1308010700303080c0d0450031092811400b005200b03488031a070601c0d401031100901081c4210750080d00c2a00c0c50001d0080b20640410310244848074842d0400340c0408104170800700762040000020b00f0643d150410034101c0f50343c0341021004441a1010700804159410003541c98002c00c030f6441c25509850164a52070803505034445405e410119509054001900700390301d90241e0500382060743d010408100302d040c0000001d40d102c210b4001103986001c8031035242c412440d050503110341c80d45c1c9603684240e2a9920380c00d1291000300604984645030508a5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 322900476 1250 322899226 322899289
    0x10318020618030f15040f060f0f0b011e1709031309021210060c06150f0605071b050a0311061c0903201002090a05041103040b01060914 60
    0x81030b2104a0989503004982280c08160401502010010703243d844401c000c1089801d0000c0a40e00c10f4005800243d80300040c109000a48503004180c1842403608140e8414801c145e44410481c401c280d070b4411252100d03a14024050340c55410304008501d0001c0c591640000740800c04c2e5000001000f0780e4189165131202c40340317203200d541110401540126020841c0107200e030441d03a0201200c0d0b03000c031503036240c500b0213801001c1c89000039100315140e425200340718004800050042500045089405a98220050050700025001c40d205000d00d00046001d0070190080c0059031002001118072500d0759658841c95044494802d40003007051100d181c0081c4400340c10503050500e4040840d10b40c3c0940f4000704900c103c0401b8070340b00040980c0c1c440158a0004204c1c030b51130781e00318005a540c003c01c0002402000c40b94030140e0b100c1d003001c040c103074410703079000240d4050352162213881e8041c1d88500c2d09030f032180e00b9800380140c3d090501c600d44116240030220b0f0003148056903510a0a144800c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 322901726 1250 322900476 322900489
    0x902040605070308090a020d030f020a0b10030b0a1119090509070504090c031e0b0d0c08010c090603050c0f0a0e04090b01080d05130e07110a061a0303070309030201031802 75
    0x6000c4808981d01103010020301d900710380d41d2a8003025000c007400910180d83d0002d4869000500080c00300414100c1c0d48100300d000f000104807c68120f0701500c0301c1d01d80300f000310b03510b1011030100315010380e0814081095a00e882c000d0205580040d10707407a05020b400d1442c00802080c8030300050800c81621800200360b1580710f000c1c0e02691351030b52069510f03414410200305603400c2c0800d03242054034010912900c00070707803241500480c941504c0802d400007501c0015284441c9410302411500c00c0d003100255002055108081c40a8035440e034001882e5260029002c440c0c04551000c84c2540410500c142e150001e4001c011070552418514022089040441c0440341c0041089450003011030060042d120100b00f102c0840c0c400d40b07000c0b1315081c0796440207004a19140f140d000045943c0000c1580e807801460308041065403034040381e284e842682030040141c0006484601800150301814540d81404002c03281c01a806868081486185a0044006011000b800e00000000705d0f160001039640d407 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 322902976 1250 322901726 322901729
    0x10e0c01052a1b010c0201090b131710060f06020309012003030403030b0a08034b04030204060e04020916180f030b010f1d060103091a0f0606180d02040204090204 71
    0x4030082c4020041c0d416030030709160003118000c4c107110003140c4100c0181ea0141d06842914207120340c00391a0407118169040344030017a0008001101e007690590703140c000000b1402c4030701505407424456141da410042e8014001e034003c03200142c20030440c008555000f100c402201015414a440c080401041814115081902c040380046d440700544c80a900c0c3c129145005040404051442c0002c025107207006c60310800e02c440c2d4046a003040070104106201d018800b401825415850744140c1d107407a0030241d41c06404224440d40c90020041440050b8489803881076a02406810190700c4e154100001c5d031020356401c40c100185030968041c1c80340c90310080b00080140200c081c1c01a402d46c50548110791050b00311580b200c414040030458404484603680320005404141d0300d9544480c401240500000480a44802c101015404d01000224240d9203d489003134411b00c1b2548462080040506c61090004001c605c2c10454000624010200c0b010030b6200420052505e5581d25500c4243e0b0448d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 322904226 1250 322902976 322903057
    0x1e02040b160809041a010306140a030303090f020d0803190207020f04090c1a0406091a07080307020a06050c0409231b0706050901060f0602071d0a02120408041403010e0c0105 76
    0x20802e45d42002c0d609030003442c02802d01807103c0c0c4900304525010079601d060302e1002030704040c1c50302607170420312508141640075150042d01c40d241e401e41070700703240380c403a84240c0b20b00d05e201e052007806480c0740c41288241c41c40103600400c0380801000600820028000001d401c0e00c00c00340075040005c2e000020f05460003a140004017003511a450210058a28025540b200110318440c0d5000c4180702c90700c5048405039544820380a40700d45500fa8201e2400d44110b01c01810640b8000a1044c01c24400024204880c600390f4244030b202101c00e894074400c0410300b03c0d001e1050300580419015004041c3d406081154010702d241850410340b0780e1401d60b4002c1c1d959a140365901c0c81c1c148090011038000d1005001c031030008040c110b01d820b0488908094030107c00c42d84580c0c0d24003281d2104201d804580c017800408040003858200b03030820782410741c014810340c1000008065200e41508040c022280126040805400d0001c06140107594640c41403116a2800da1656603842e0f98010f01e40e00c44401910 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 322905476 1250 322904226 322904261
    0x21020c1603120306080105060303040b28030207060b0f18071211040503120c0703111302180a09060b0f030915070e01091d150109090903031e02040b16080904 69
    0x10b20000a000c45685400c141c0159041004106690f10000101d808603030b5800b02c010f95411702103007001601140440100d034098040820350101c2541600542b4006000d9201080034806000401420030401c0c0f1240b80c104207604510fa40008800c0851030744200b0701d04003034447c840e4040b03019044501e045040c3c0004600480c0c140038504040040c00c0d0380101402c40f071880c1140a4242645d201000d08c8014104c4207001030840c09a01c03204030f5851a40d25008040d07451301030081d000020140b41038140ea009180c0e242c40001d1100143c001c0208030f5a078549414a004002000545182c1c8002c0c5414030910409146c0c182c00401c08030b81c207200300050740c5e49080d019a0038000501c40314042d80030b410000e02d002d80c3c2da0721842c80c0b00b0845401c10b0040e030302e48059030040f50050341c075001e06500c4488407038a4881554285a01074100551554142c400c5000c1c4824560220049000b18040d0610204080c4a0182c00801c0c01810708c140c0e0713004030715841c103041e21140041c0c1030740e0520080c2100741e01c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 322906726 1250 322905476 322905503
    0x50a08041b1d101403030d0203040204090f0b041203050709050f04182607020105090d0201020708030a05090301050a090b1f1a0414010c212d0f21020c1603 68
    0x103c01c1000301c80540150b4607140c0300301100e0400660b80e401103a2400c24015400000314085549a50000c0d1155900801015282c003042c1000c2c0c1d0b00d82c004450a64000d0240c1041d1401c07584240b0519129461035110298024203010900c288a1424408a0307080313955200411000f455484003101912703c5010401030035a43c0c145c030110104804004956121418413140c1e0043c0c0c0c020703080c0c404080003624001441c0d001400100e1405001e64006101c6000000340c506509a1100091565001c241c0090100d0307151002010204c40358903034090408201e10b00890861107d180701d0641c4007480495518800b070300c418540c40c11151848d003004100100003410400c00807050300f0409242e800f420018590005520707a03441c14155000e21100042010b20581d40041c019094448448a400002c1100d100c64141801091a8044044001c00d0000c481c0c80191849441c281001c1c0004d8440546809510000c08001c1d4011864007141401014106991090004585801940107060b1003602c1e2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 322907976 1250 322906726 322906741
    0x60f090a060f09051201141017030301030b011403031b07090506090609060906010c06020c0f06060603070e0f060702030a050105040b0606090d080c03070b01081c050a08041b1d 77
    0x280620352018050102c4114040c42450700500d1501c03c482e003d0325203210004100a04900400054403221880741070310090040700990060000e081e115503e076019803102071003c96aa0380d0100f440700130a018040b03401403185400700550806541c00283c1180d0600501a050502122041c141c0c0c441d50b40c00f540b01003102e40014010b42d40c21150645522006082a001107143c03410010030660280014101080c560391055240100d45508494210340f20042d4020079a1500c5401282d00424403882c00800e00e946048812213000ea045a00c42000890207101030000380a15104000d50202c4181b001d9809a00c003880b050752128820f00c0001410301d85440c0c103800b02c04000c1d1031035009550a001c3e4074095211016050999038000c050b090321043c69402c107030700d18400c03003800401c40b03440350300001512400040c0f00c403601811240003030812050804100ea59010f203000030000107101c41e0119000ca0030114035080d81564070211281d140d42c603451130b0031743d140d248514012a4a03a190030003012 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 322909226 1250 322907976 322907989
    0x30403020a050c0d020f100516060902090a050c03160903080d05070906090602031206130c05030405240105010e0409050d05270307062d0c1a040c090c0e060f09 70
    0x3d40f1088030444584081034010560f0039100410f86402085209010300341d56000304141c420004024110500c01a41840e00d28050440e94104a01030701d81c0d5000308000f9081ca00416200381d1940f202942940e5503180384c22200410150b02d2010700c8a04076001c40802c87d40001009002c9a180c1e0224075814441401071079089280d003d0420001d00001c144001940171003200d10140b0044190451740c0c48120000f004001c2c03424503c5641c41c035100c03100b403a05070000040d41c4500c0c022401d9401440d01c444102401040ca48120100040680c005200e0f560061030f4802e4103201c00303000014059080e549861400055100120100310041080c1d0016401070500452010507214134405d40400b207404a42c0c0c40380700380218824019003207400e61001120b49048100101e4402d86040351001c42e5001600c0402c0070380051b511054070600781d04121001c1c0030030070301603580b090081e02120301d000115002400c035403199004002030f80300c0f00c000f181d58441c09046a03441802c6050350b6403000e141003150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 322910476 1250 322909226 322909243
    0x6030609060207020f15030a0c09170703020108010f030f080c0f01050702062215020a0c05010f020d05010b070b0612071d06180709121518020307092c01060803030403020a05 76
    0x410901b6001c100c100720610010b581c0c101507141d0700030a050000f1001030310003140765082051074003480924010b44020000716003003128001c0c0c03915081640c031806511080da18500018090840320f80c00900041e42c0034004162030403070311060328480784450103c5400d40301e065850100503445841808004004100c001c400c2c25616807409600c0015984c51100c0c1c09c07406480c2a4405030301042d98001da6026080d40c680c41c55011000b00840b6244554171002500100d554426042c038020000c02c03100d0b1070380d007285c0080d40c120f1003d03804d80c1d4880301040604c1a008c040c039003040c003c00c4000036005140307022003540600c10681444503480e2030b00c140309018401c40140c14410300c5500520043d0781d00308064900381c40c00c503289056240e51604208608580c014a0140d203941340022039400703c903446404444c068401c074103076a0510356501280c42962122545003e450704c011503240f09084c04800c030320210f00038100011802036580c165040c15500304950075405604060717001810420b044c0403a00b03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 322911726 1250 322910476 322910479
    0x9110f070308040f2114090a030f02010203190801060f03060503031905040902040617060d0308130215030117102306040e010212090d02010c121e0f092114070606030609060207020f 79
    0x1420075650800198408e220b80c400075004105121a05c019640300f80100c0e10020420b18034502e80c000141801824800300f4802c04000601c000c03810a0114400e00407a001c030740c0014020340c14221640150308078200d084070341c50140314041100045201442c00034000500164a030700350110444607020b041147c0003002c82d440341c280504901c000a40051281d0b8104692940303008210350144085404259201c107450080d820120000038035154400c00d10070601c0c440d60545410300659801d1009407107180603860103002080c508240c45659000d0074a6000340c00400101d10034088141e2503003240c2c040c24403000544038031000c018011108001d104c819200300d00c003c1040d80d045100c0149290407010b9643c42c1c140e250742512545000c0c0d00340300090086426010040747c0c07811940e0100030305c848a03049400e101d002c0c40380d0318000c400d00300f07085c400126034840307003070a40c3d40c406042055031001004071500d030354480000c0045111703403080d90030b11803250200507aa41d0300d9004000d107603440c91030a42e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 322912976 1250 322911726 322911767
    0x606090209031c05090301060e0103020f030703051e0a0c0828020918010f060803041e0f050111120d02070b06120c040e1f020409110f070308040f21 65
    0x10605442c0014084040c203078400c0b41c400c0302e00e6501c3d41102c03144202059183c1c50740c00c0070000715007410602c8615048a100b19614135010507610241901c620a500c805007454001200d1652070006d2001240c401403900420390380303401c8007a5500d01884160343c000345102d9104405c1414034440c0030301103081559100000c4070301700800f030b800a501143c0043c102800300315502c640c5100e00d9402d411080301c42041050512040e5101c070b184a949410611800d24010007012001690245a40702c0d1825101c421070300f40185400c105c0190340055542684905134400c910b0400c00c06607840d0060704440a890b080503a40741c0007810702c0001c0c4038002d04254415520203c144c00c0c101c0000880b06144001581d01191074a841d812907814808002c000d403088114610301e0044d81c4140e40c2c01070095030319039582000310300070942c940c000c5400354400030344000b80c0812891004c82d00460401e0b82c0188242d018941071000c42e034924112002c0c1403c0a000c1e04401000840e0880c0c000803441c0423a030071103030b00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 322914226 1250 322912976 322912987
    0x9030a1b05060103020402070f06020c0606010806040603050a17041805010f090c0804020108060a122906150705100e100e0d0522050303030f100b031e060a081906060902 74
    0xd0710703200c1c50103100082c4161340c00107941040203003446010300f40a40204046448030b82c00c8013134030346640b012180302c1c0c001044d5400081d040d180c10710900d816290488024140b444007641e402d04c150b05000114070b0b2060b424000003944c109214469a040d401c40b0340041100e501d44220311004520706c3d005005803c1c14541d80c6071405030b1219100360720a809280c103d000351120404542d403444aa0003810a01c2d52900d4608140003140111180591300000e03541b0382000c01d1100045180c0003540c040d940a05800c20040310a0040c00150001c2f43c082c00588a02950304411401152440e0050004540058100e06040000b0f0303c00c00e118003a003400038080207241c0360380080551051b400501c1c503500c80d14201035101e0301c90300100000781ca405022a80e503410306007a07207060000102d4080c2c0400d14601c001040c80342e009815070b40103007508442a0302c00140d018000048140080c8120341028041d240050203e404101b01c1c8036034401c04800e400081c03a1801d1101c192441c41e0000da280c0c0c7c2c0104036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 322915476 1250 322914226 322914233
    0x50c04050c0f09180a1406040504080a050703050d090f120807090504020d15030c0323062215020c010e160509091608060604060e07020c0f1809030a1b 66
    0x40b11000702990712401c1c0d80d1441d0000068107140040780119035071000c0310400003102980c0c0d00503041c0c0904140076101d580e0703c4c0c1c0108401d4030001c850040c46103106200c00c0102ca400340300503003806480382c10b0a0b8246036811388840100d600194096501d5490b000010050000600d6a48a80045840c0c2848640b40658000d0211f450314030030300e4040ca500003000d402160203036000c901440c3c01c0d14842c00070301d42d407801c008841203402d01043e1100c4c0411040068044000c545040d0f00024440280c0096551840c25440851042880c0401d003412449080000703440442d5000344c21a035200c0060b103030780000c03407218211208900340403865403001c00d00300c01d11140d004100045990403500000d440c0d48a40c16103040072801140e0040d440392015010540d140c0108103030344207120a960400043d9603d49002c8002c1c00b0554007100507030081d01c1c8019480c14002c0203950982030161042c1a044005404d840d10307207034100c89510241d04045004a070f1a540005080003010728000705079030380c8501d0348 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 322916726 1250 322915476 322915501
    0x60d300518190e0a0509070605040e07050d0204030b25110330011211010906051803011b080109060e1017120f0a02010b0103051e04080c010612050c0405 67
    0x71a07445030b549940400c2c050140354004001500950100c59418180740c500700300503120945008401d8000d40380c000c21440e11900641d02100c0d070328841c8840d0b51b11217200c182c03140d901c40c80790003070619000c00c804004a25504515805030491401c1c1072100c0c1d602e0320322030880d0407103c41c1440c08c01080c99001c000c03a40002081c1e03003448420000090881104646295203020380e05d52400d00e0107581030000506000480c015801c1b1030040351200c5110080c68011904080700e4002c41d004a01c0c18083c0c051003102c07034100c0744080c19010300001110382c12022007500007000845a04001a80840140000203450042500605003102c0c603801504000b024548040070900850390824509261540070131001c00c20041840c03403455584d551403144601960403540724810681c055802c0c0402927070954444e00c10144100910864294095100314001030b00e804003505c20782c1d40040501c14090303500428070a07074000300540459030351007014515059051400e1145214031441c60310007003168901000c2c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 322917976 1250 322916726 322916767
    0x606030c0706020912010903121512140709050a0207231510150305070e030a03140a020705041508100b030c010c02060d0c02010510080c060403020108060d3005 70
    0xa8005a1200302078004150070010501610703ca031b42c04c0085e01c0042c10340001c00140e041d2010503040c0f02d00031040100c1e0600400d288a241d04940b00712014001145d104904940341c0001e0a081e00d0340a0717279884500c810703204103860840880e40d000440804020300c00411364a00300642034104005180040d28544804400e24455284113106001881c0407003002d12503009044042d04131210a80c02d00c42c02401450110f079500040b6200c0707078000150b881c00042c540861607240d46d50903c0c40d01041c192209a42210641030194440c041c0049030941e0750380035800c0c0851480c000c1c00c562620301380d64580351014a0102404d403d10306405c1c0390242c0c401040340c41e1100028200281c422800741b0100e8000d00c070320303516000024640419080c03070070b906402c490301030920102030800040c0c0303130313511151503800703081d030f8190b22003000c000800055018142075540180010022084c050b1540c89056400d81c82040b45101d0800ca580c400b03088a0381d030401c2544c81540f52030480d003880c7c2020350040110511 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 322919226 1250 322917976 322917983
    0x308030f0c040e04050a1a1009110f0316020105060904080919080a0b0403080603070602100c0e100509150301050913060f0c030905070b030c040b0304080d020a02030a080606030c07 79
    0xd1000400d0080104101c2d4020030000c29101ca551500303082044d00c41903500012500c00751800c0c0c110b045202c08101e02405002e04c0264901c909203044840c5c070040400c148000100304080c02644da580e00d50320003a40c45841c00250103a40850f020400a007180c00081c0507611901215044c00042404082960b14985060740d201032011a509051901000c0350307804107200d441400c049a040140fa0031020340514400d071900e80b05600c03020101a26141e05000d03140040e03008140001c4620720f950080101000716040640445040501041040302e0140120004c00c00c0014503142509042096106920002000c0380c10755060100059007220042c06d00101c10320000b460006010032644940408008841c040042c83c4ea4004050060f02c0819001d0702d0324000d454000500020a500710f9100f11207a04085190500b01a078060700f98201a20a860540c41803103184004105032004260181494000359210100920010508400100b0480c010301051050217140703400c81d019510016030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 322920476 1250 322919226 322919251
    0xd02062509180908030103030c020307090c1d15040b04031203090309180b04020c070e090a050a02090705041a1803150c0706020702090a14070c20010201090605101e030803 75
    0x541440c80c0700540040070380906131803000000001010740140c007002c1d0081c800d9017500d00041d074800700c40045501c04c240940114403802580290001d003621000707800000105041000425400310700d000740c010b90080c00007240009414403d1003590819042c2001d8140303000e100f00402541c0007000710031544034148641c00c154540c1900b1844a41100c1c1c41e140c3c0c0035004640700d15000000c80e07560803440c4104001d251810000c506110000703c1c0c0007040607000001410500c141d5401d10a038404001e1013032040103400d00c07020407852205d030000000c421840080d0f903102d048050b0040c0340c01c0145809603219611001d22210b8140c0c522000c0c07a80a00b440003001d032955024204940a44242e45000f94005110400c11540103425803040702119621260010290f6405409550a2001340c0f009002848a0304103118031000200c0c0c0e01c600c110040c0700201e0b62401c20b9803658191034060719411080c040010303052010100303c20400c9400e2803d03a0003280428516100c5005a200c09030003241c0440 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 322921726 1250 322920476 322920509
    0xa0c0302060703020f0d030618020f2a011107021f120b030118202e05071407052818020408030408010203010302040f0905031b010605030d02062509 65
    0x40c028012101d45c88001c41c02c0e0f072500c17203072218000c000b05098010a0541503100500c126802800d00c00d4840c16415109000c0c902460818180880003011400d0700383c0c03007540384850b400700c4820300400f02001ba80c40300454480c56144104200034103820014103140003140c078120100da50201c4400d0941d84c8030400054503004180219024003110403480d40e251340c11898003420011a800381c015403540d135420f02c10314041040100011001c2500303403070140704040b030310300d00b042d40114060b50070b014110f041851411400d035560001201c0c80c0c07090b0000582140038100458100400d170905501c008094610881c002441c0801500d00a4060b1408100c11420100b80405c003a60448001d0481b0f03404403038481d0f81c0c1c1d81d9200d01035442404101d00490600e10b40340c1c4050351502549003440d521402849c00c0507801c401200c04555045021000c9640301c0000180340c1e1010301840a11403d141e01402940c500300004c043e03a02c4000c03e00089074881c14030600d07607140e8044258030a0710b010111500c10b40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 322922976 1250 322921726 322921733
    0x50a03110708150108010f0504051b04020d050c0a11062e32011704080a0c020402030703020a02300f1306050c2a06091519110a0c03020607 61
    0x5001c40c0c02207001d52088091082200c19010a414102da50202c000d02100c4003050400b415a40281c0c0c0040882d07005a5181810714400c88201d00c5012001d0b00060a101e0110b401400340d40d0107440306c1404c0c60000640000041e44503008400180c0000700620684c01c00034000c0d44075804103c41802210494a180301c80e180c41014508018a070010300030300220000d010b016140421a0744250240820407001022940100b98151145051001402180d51584c842401c01e60100791031108103c1090300540c0160303501d2010714003500d8199401601c5052864010b03140000c04050003620201248180541c140c0042844450706086200c8903142c1c42c500045c840240141030360311810291844000c640c00350b00501601c80b0464000440c4d007010300305059030070300010a403445442c86600d00c211035243d050a0f802000501000b601040c030010010f080a070340340c0c100010160015030316019032610300f07074801302c403043c204c05000103402006800e66984040d0703a101d00c030003800303180c0200304c0700c4c00d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 322924226 1250 322922976 322922983
    0x10140303070204230f090703150e07030302010c030c05040b1e070b1302010e01170604020f090618010e030706020a06090c3302210c01061503050a0b0d050a0311 70
    0x509501410611a104959198034900001c04044004d60102940064070703816007560085c0c02900e80e40080e000b49815900d84218103024015030b04841500c4010020200404200d4a00218060ba00001d01c3c1c60401c1002401c0d1600400c649040143c14801408011000c6007115040c1c10006090022018002c403007500e90302603504017a1040d0000320810039000c4980d0010703000316100341c1e900300c100241c4400540e507141400100b4842d4800c2e00000802506065004100710010070902504025100c0300040182d885002c0b01040c40b5031600e00480359580151492823400d40480c050800181001c1000f99100341c2000094126a2540440d000b4801901d5800380601007603511743c0112380d080e010340304e450301a02d130300b621100c01c2c591520100360341301041c074184545858101041240401d402d1fa0060b030016501030351155070b40c0c0e80c00200310898004c0007650111175200032480b4a0402034400484151070402d5000c0c0d1240040d25000640c041954100990706003071045101c48040811440c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 322925476 1250 322924226 322924237
    0x2030715020c0d050604030224061e0301021c05090d170c0409060603020901020d050301080a0215040b040e09120f04210c0803070c15140304080d06090204080d030510140303 76
    0x10040c82100460f401d100e40401c5051043d8040d80884071451242d104079500c641610500b410036400300c0d00426401d1074a074251180195a4040e441c0e00080c171080043c2c2207070f205440019012044140d00c49480115001d1715901143c6c2c0c030b0160207104e042c19401340603400002c54100119040302c2c000380000480109070340180030060000c0100ea91a8003004e0004d601114050740584551f02c1140c40c00c520078000c5905890080c8040d08140c031440e1b0178045030b4020308080c003c0c8a0410302c030100f040c520303402c007400c02000b001980e02c480e030600c03000681c20103614020b81c3c00b0a182c1003045500002400003254200c40b100c00114010781c00e082c5a5298240c01e0460042900c02d58101c0021100400000350507494042c0804080e0300e56a14420800c151840310000045090084604200c541c05406158042d000700540b0349800300840c1d11408440d001e4001e030711220307401700381032190f031900300050005131030142000c000c83c1c101600990710460140c412401548013184a011250314140192403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 322926726 1250 322925476 322925479
    0xf061101021e030406050f040c050d05010f0e0606010f02071409190516030b04050603120901090324050c12010504020a12060f05030c0a03030c03050912060f01030c05060702030715020c 81
    0x8040040c2500010407030f60050b10140e03801d0b0b060001040e00c080200c0c61903030046070f0000152180e607181c071091000004c2c0415094900c1d541c0c0301e40e6441607040c9800303080e242c10750801c0074291919042c1c0001d00a0702188449078115800a807092240307161400c924189080100c0d01c001c3c0540e94041203100501205400341007040c01c00c0c0a0003008a000400e00f180380545442c14005181c040d400d02c01112030803070340264551701c90150101040701900041076600018075110380090784a45030880c800584120103084035560401c0a007206049100341c58100200065103031410407224500300000c24103014884c0325a50001c2c6036410940180082c0c06402007a0b4800e0103010340e0b403084e480c1c0c0703407202c3d10405e0300178040d20000391003078640282c9101c16a581900c819102c00f00c2c6460440e226008090055040310750460102002542000220b10070084000725003030075811480c1000d0f0100b0b460748100d001c4e0b1424044040140d401140040950340b00540791800700b14080401c901d041d1070f035203070607 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 322927976 1250 322926726 322926757
    0x8060f06130e0a0c1e200f1203011401210c030504140706170c091e0a0e0915100b0301030305040e070203070f150e01020c070302040b06040f06110102 66
    0x910142001c20101c0c0704403041d040740c00310b00d5a103414200c020303661151490000200300b1040807480c00402c140b40c00c489130292070f2070010f0f6544601d280340100048a0600c80765803115104040d880020882e40802c0182004a2400c65140401d030014128a608805e814814429401c15403002596200c401000344030300103014070001420042c0040c0f10076281a83c0710640d5030a81d11440c0c20018040701100d010ba600c1070301c01c100000ca051035080300600200d0002d02f04010342200d550b104504c22085101e00c0710b29000b0032158804000401c03209511804404845800704000c60318041140900c400881013044165a00c020a0300d82c120703500c0e00214040c030310220003c002c1c10782c4400500199001c188504003162500030741070341c0d28055414000c1c520900300076042c00103101c6600301c0c0e0b21522000c00225203280071041c114266000900c0c008082c1e44841010400c2d8070300750040d40040181624118905070502c541707407860031001e0149009110702c0e4103040d0001c4030254101c40080c850700e0b140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 322929226 1250 322927976 322927987
    0x20310020316020f0d0207060804140601031a0f060906120a1e0201090f0b090d030c0501060311130203040209130507120b3106150b04080304030b0f0c04050108060f06 73
    0x942030101080990001449131000c0b00280810028603410f0707a07001c0350010f062581c42e00d081191400b000500807201802541c200403190041045001e000c0c0d4800d00342429082c400d02074484090308010143e07402d0f040c0340010701510740c68941219070401c500341d03100003019207144046031400c40c41d1900203001c0a10f900111209404901228a600c1c0c0300f60780e900300303640d40d40c4e0740401d982945000c0d0b074580ca4020811900140b070306200d818001ca100303007040d0403845481d494403400c403131441c0d000b5191026a11034007a0140307444210710800c01840b100071821030810350007107070b0001c000a0043c4070080031028a18148001040f48200900c020300c81000d00e0201454000320f01442942c0d20003601d0500724507500103488103186569500e580c00540074010700c403070311000041e10102e0f0301126038086c034080111303042c45003000034000340c0540001103035118990320b81030034400320090080c92030350110780070321800740d002c00200ca04a60092030700260b552290720000340340000d10b40041d44c0c0082c00041 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 322930476 1250 322929226 322929241
    0x9010504021801060816031410032609130905030a050a0801090501180c030216030302040e06030c090a020304020f06030a0b04050c2a030f0f040911090a0306090203100203 75
    0x11a620540c0300381d03805524518030401e1a2090034080c090b0502040c0150001485003403905040c003d10400b80c54049902c0b849440704041084c0f0603580c054030704100000600074044242c030980c980c0742144000c80c414a050b103030510400c1c044d0b101014499601300c0e0009100c00c1040d04802c282c25041801d40b030b034030020320340040c1080c0d011303019103004540000d000144d08000ca114580c101d41107010390208507481302c4018802046010a054180b59090000501820403038076080c2206200e03440059441d070400a07060783c0843c1c024a56403080d80480d030342c10042c1c2c8503041e0140c0c0080e81e0a20140e00d07600c0710310019054956803041c03243c100402004000b00200b55400500c0100030540342000707161a40d60340e5680a204100c041c101e10170701034400c4141075296214400950290b10b086c1d038200b0040001c5000c02d40d004c0c0000907012140840c0c103201c0c0d0245232144c01041d844500503540750040c00004508a10540c1c40050240740e40d45401c4025902c082c070100b6001040307070384119501d150010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 322931726 1250 322930476 322930481
    0x30c0301061115070e0a0906062d0507030c0c03320607140714030a0c1a0403021513020a030b070f0804080d1805030a0206010603180f020402090a0e0901 67
    0x70901001541404002c8a0103101082100107208041d804814980c0e8901c41603441e01e41c040c100c240c10a0345000c0000c0c95078002d100d0280070304140d580f002d0854420001c50800c2c42803010000440d2160350810019017034120b1b0485407056450f0030308028090050402c219441c9061344041c1c03e8a603440d5000c1c620b01c04080c0f0301c0c1c144550840d10300020242d2070710380541d00d082c00c0700c001c40400ea85130b50300925500114041c00049128503142602071400b6540a411a001105400c001c41c02d80b03120117041006104c0424408400303400d0f450414985501c2c02551404100c17601d00143c14880d000c42c0010791741036600c009041d000341c00c0007600b954900d400440c03580b0031980341d000a01c807002d0303954003244036504060040da0019559810f000032590640020455250b11071250f12060040d10009241803029101c40d15040d00070344041d42c5007500103002c0c2c50000c0856040740080700180b2000a805a02c00750010750103550040e2142c100102003400b03d042600408000d80c5000104514440f054 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 322932976 1250 322931726 322931729
    0xd0f020a080d090f08010c090501050c070f09094d0306181002120103060c23030f0c0a080711070f08030d0f05040804140d020a03050a0b07260a020f030c0301 69
    0x203003134401d072561048440d080f6001013040c1000509a044200030395031051001e080c00008034804c0d80c03c81565501e03a03040351200340e80400d03070f0592100e4a60051000d5a440507003146200e6110426011589a56519549500f80f45124401e4509140c1300e00c00400100c2409021014044880a0501c4041d941c0c0020608000b00d00a00c145403442c0e20104150003565525400d980a4150b00c0e42140c0c1e800000d001100b02c0c450800200082d8880294004061000e10804804501d0364904000f6a00c98031520000e000f400041000c0044501c42c0754824030440d80303e5414984243c403096181c02d010b04180e404e40c48511041082c0c0c80124034400c000c00117201c0740ca0003050401c200d102d000000c00c1a61401c035400b4041c0c80003800204a030041c2c058040420110050601d04000c80c640c1c0010590301842d0402e0305d081d0f020703c051100b00a54028420741128044c24070140f0490120810480c007c04562482ca4070312046010486a0001e034054402c00e050942c88251685050044158150800d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 322934226 1250 322932976 322932989
    0x4090308090706110d0c020d0c0308031902030f19060b0d0204080601091a090705071a01030b07030b030d1803020a0303020115170a06021b0d030f0b0105090d0f020a080d09 75
    0x354080052030502460813081e0f00707001540540020b501d081c40a0310284c903070310001e9800101904642c4005404458400301652054241e65101e0a080c00c003030301d03900700142c8051500d07441001401500c44111a0603a88104154007240d01a403030340c0360704000f0f408141e01c000d001c21703400325149501c40d00e180c0240055a81420131940103a0740d03000380710f0540f04802359040501c42d1010205115040c8018190b82c0404075050a45c0b0b00f030100e507600c0c64020b1008103c1d00d00e1300c00c400014000c00802034040d541083ea00d01d4140056001c2000180d104c58154004e1420b10010703a0080c0c04448040204200440d0020100c404c042d82d0381c24042d0290290f00007401d15140300c8103000c00c480004401c0c0846000f01c0d000103011014a40e83d03103000030351150f40c031900021801108242460000c110070340005800d65400304800005101d80000d54041c1d020701414000203101c000401d0b03c1d1202c0000800d82c01c00c104440080c01070000c120306401e175800507442c03400750841170001ea98000c54000100c0d440c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 322935476 1250 322934226 322934233
    0xf0114010b0c0307060501180b271b070f030909090309170f1006030b01060c050304151e030b03060703020c0312130b040501090b16021c03020f0a08060f0f09010603090507050409030809 81
    0x1480b10421201e40700c042c0501c1ca102e4580710409032b84012640000da44096801001c60b41c804c100350000103190414441100c19071120400711b0101340c1d1040303048000b4025200f0510081752250f4010304807003800d014480469040c1542c40041c00000c114421220030360704155242c00ca020b144540203480b003800181c2d1300f440c01d08000a042d9200340c4103440c800341c0000255040900b41500196919411130222081021100c084201614100310707501e9003240395100041c6c4076805900340b50801000400104c00d2520600800c0003094020044403044d6101c00c001c20095030740c0d004141d01004501c1800351000d0320000800081002c150306c2124690300a0489001603690b08051802903c0384240000050b044402840c0c0c505543c408850080d1616040240c2000f94401c0b00140541020078040700150002090101da802c09e403c60f84035403c000e1b0780d4942d80303000140100300800b0040c4100e108041d65000d95000b40301d000d12052021f00b0004205100000302828028000001620718504a00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 322936726 1250 322935476 322935491
    0x24030c06020d0f030207020a05150c0f011104060e0310050c03040c0509070e0108041110270303080610030207060903030903030c02010509060106050f28020f0114010b0c030706050118 80
    0x9000259120030920780c1d6881550143c0c02c05021000307500f01820491b0801d00c0324001180541d110000704950018541e0500d8032142640b01061130414841d9065800ba40362818030522020180300316030a0301c0c841d05000750320141c08008a0328008000300034901440c030707090074080071003082da00641c0203d00420f00920755a4036003080041540080e11075034003107001101e0107141d27540a6500310754054050300f426000c1487c40f102003422942d020074094001110101d100440d1080038642e441045020000c8000c1c05045a50161641c03401510061007094400107000003688290110340c260390b481502480034049500c0d014015150118041380400c1c01d201000640038414415503100d094104d00600d0640d00c0d024058401c1d9001e4030107481040c504010850707031500381c880030300020241c0e4000030b4490f661000380282801081c0d54040010b904006030010712200050506042da80900c0c51242d0311006010b0091840c85100e8004090030300f020000a9000e001c1a1000000d80703516000740840c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 322937976 1250 322936726 322936739
    0x4030c08060105060d090f051c020d0816200313031203051b1c0518060f0c2b090501050601091e090504060e1b01020106090605011b0624030c 62
    0xd41c030900035540c0000d8240704510411201c0d40028020306c0c00785118071412111904c61a091180c0c0c58801c0906601203007e09022660404c400d1080d804035140c010598100382c4e5110807040c01100c0ea540400036081488410b075140c0410400a40d404981101c2d80c590320541c440d034074404a44000e5030701030f1014110003107050180c056944511410071240d80260ba0104030a00560800340d2041b1101c5c07031201c48902c021046206d040e000d004030110807402141d120385540d01e050340c010203c07059034100400744040b034003051090701c455055000401c01c030442e50100741003a1000502895008900b4000c9140c2408019405140140c0c401e98441c8103c40c1c80e4082048110190000c2c4401500e5200c000c000d04003865000c2900684581008500c80005c0101d02345002c265100f091020305442840c1030b002c3da024070a030b200500c030800c0144291841c203400a890f600c1481e03c0074071030014000c819010040103901c445001c904512899410a514060079600203250b0300049030040107804c8040b8a4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 322939226 1250 322937976 322937983
    0x50109140403050702010c050316150b04090201090e09030f070605070806010e01020706120605030607081501180509090a050d0f090902040f23060d0507020c01090311190e07020304030c08 82
    0x80c41c1c01d52240c5241136050707401100d03442c1d98008240c030a80801d0010036800c0c10b00c07801c0a0030780d41c003484650400c03070040100309007155080c111080c400c518002000c03005076001090301044a46203607035600719560300c4807094250710880404803e014000201c45041049681c4000d004103040d64034545159104801540c0310328518600f50b015078000b1108001c1c03203205401807031041e030280b0008100c040d51003011a1801609445540100f8410f208004c140003504170340c40051070003440c140f0709203032031098002076a02d09801542c0c0220b0001c000114582d40401c0840999a444000c4072070031441703003100900301800188608005504000700040c001d0300c030f009540684403c08100b0701580d16201d042a003003010000030b0f01c40760403000c1c802c28184d9100c40203070455842805000c11246041100281000410000d0a0612414030f41c14004100718480d070560364501514040c1c18008000c250041e074410b540c0c00507011400c01400c002c00c03da400302c050802c40c0c0c800d0301803061075a101c0d01c1c11500c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 322940476 1250 322939226 322939231
    0x3120406020a02160f090209060c03040609080d030504020a050f0303090d0309050120150702160608180f0a14011808040302012c010c030302090310061404180b09190605010914 77
    0x40c41e050717070314040c0b140c44070603402003061807030050007640b40048aa0081b8215007080d03102d0000f02d66010070030465004140304030003200505207010003180c0380650024402880b1b0340196400b607031001c010345070306450410480c0c213202c030000c01c420600d05003454020700700c03a140c0c0039031030000b0780c84d81600300c0b100010b115069401020305d000e0903040013161b4540300513040003419501144a20300340d036450f210b203a07002c44024011903594081285003040009071146610514054603174401c0c0000007503c140881c50b40100c03640583d00b058401208510399024003c0c0c84c04500c840042d001c000c2c410852504010812a4803e0300c62120070100540000340c130404210509000441852242149601c00c22500050034480d0400500304072248010a01c2c10741164511540960b070354400342700c1218104036450412100f101c041c03080501603c02c2c1c00102c60480f40040942904002203611280c05000c403911031303d07040b1642c0940401c1d6060000143c0428418441d0843c40e00300c0041d40007903016181c52 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 322941726 1250 322940476 322940489
    0x70b0a0b12060103201302041a07020108280e07080f0309030d12020d05010e04170306010e010c0206070b0708070f0801031a15041a01090504090c150203120406020a0216 74
    0x7071182c1c40c1d40c588681404285c83c0980d40c07540078180580c025580c0e03030703580c1c04000400180141c030fa9080280180200704000608180007100b4400c150050380c1c07040040d9030240880720b000340b1900020303541f5441c010100d03187d26101418120224044034000441204039002c2000b00c5051400b1a4281034607413285c401c8890b0150403080007174035040c0c05010241074115420350700501c0c1c490542d080320200e4100fa004000c040e1405010301c81402041401c0301c46100480e100c4925504081001134070404490085905000b1840d0110040d03544c0c0a0540f000c55410605180903860500c40042014004170342c2c580c04a1071407143e0410481c814030165040e01d074098142800d1030041452070324201401400d43c880c041c840d108100c0c05403070750f00031032006508000c0c51607510201a07002421f1131510740c110901940c40c1c030008001054540b2458012103d0b030b100307180012080884201c7c1103120b03081004944407020b10a100070468694000c0c001d24400b40e080e10394001d0f00c00040aa100c6180c810342c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 322942976 1250 322941726 322941733
    0x30d11030c040e19060306090b1b04210b090102040f1a030c0d09060c050c0d0e091612020f040509070302120f0603070305060405061f060c080a14070b0a0b12 69
    0x244035050b810000f098000008101c0007a0400d1452580019200c490b04211201e0f600d800a42081001700c40d4201c0c1c100f103071080c045105180c07142040d1801c1c0102d03c44c801b030704031041001380c0c82c50181e201070854054026051201500c0d1204c1d202e8043e5100e8820b080d1042500c40000800d01e80c80381d140000c4072045811213156494108008000d40c11030102d15584503a0b41c42440300040c1c451180320b906c5882602c07001d0310f410b03080041c3c0d800d160f120030443c0141310680c00c01c0500760f5640e42c0050f50113001081d400c0064004250216003003850108a044002d20001d01d1462a54a41d4058411240e0464080700941c3d00d00c44224240c4c01410344e000340c100300100101c1c40d94403405caa410f80c0301e00040c08880702590351780c41c1c6d0362402c40252001d0f0f620350890f070144500c00c4070841031561a001c0340218000100d2034901c1c020400460004083c00722940841c1c41d160461080b10600d0a240d414004a51600308508110345210820740d00806600d00c0c0010690f010304040c0441500b010012024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 322944226 1250 322942976 322942979
    0xc0102030705030315120118060b03010b21030f040e0a0c03182607060203090706030b060d050903090a08013c051b0705060702070509010b0427020c030d11030c04 71
    0x101100101c1407134405ea407000012281002c40042482034403500303428103250b88000203060a0030310840700c4030240280240d0600d04805115261240100c0f801c0f1500348411401e051526141c80c02c0d8080c80350143d0320080000342c001807400906c21804e00441c00e01ea030401131800c8559082c2c045401c50748038030340701100c540141000301c1c01d09a10210041342034903400c0948139a52904450f15400f02508807504d603408400e011800c07a0400a203406010035040c10840e01c4c03812000507002d070040e40507440740c154803800024503048090040c1d9120001c00b0701b9048926898a00e654081c022550100001d141404640081402000f24403115911140a0109400308a800b4000039010061443c011614050f54070203807000718000a241c241d008901038056800d000e8002130803c00c8a0740203030705c00d101010052086588220803542242c1003440d240e81150043d1500d03003100e406510340030f03400341e10114103c0800a00400140624281c0f940304100c481c501d11118052400b0030345180441d40d030705010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 322945476 1250 322944226 322944241
    0x10e09250605030702070305060c1804090314070614041217061507080403080f1201090b13091103070e3306090d2a05062706040305010905010e0c01020307050303 71
    0x85800004e1841a58030041d226200c4074a001425211a504828001407079000c000c5009040903400a00301c80501011900c0d841c01040070464810084001600041c01c004011640d40010301d40c044250100c00035140605180c0741c011603c410071400304a0310701142403512102d1510030b00c5050300a00c647c801d07240111340400380d90056941207a21035010080403000c04c0c1d000b8080d110f91010b0403101e56072110801500d001d145010381c052808942055101561691a02003440da502803810b80000c080401d401e004140000ca040c015816008016010540c1110500303a40c0c4146003001c0f44207201c91203603220860f401d6113040303446e0a10340c509682c0d281a14100c401041e0303200d0024100d2100701b907982c42d190007201c1c01094400c03c00c849810174407010141003e80100400c806c590702400d0040016802c01441c1c04603243c240101c07080540988036950300b8058502030754121008025001c082d20344140204400d0700703520705030f02c603a80031050300350320020807034420b168050003460075500c4211 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 322946726 1250 322945476 322945487
    0x2042f03060102010f060b1e0406080a020708040302090a090201020d0e06030402330405010e06040521010f0914070e010501050403080d060902070521190c020f0603010e092506 77
    0x240780e00d0440d526800309401002e000d0040c2c2014120701e0228642d140000e80a22041c011244a08841da02003884104100c0d500801c0040d0320813809440540c7c1c8048902e0596014030540d00005e602c84042010700000340c90f580c1c0314540042c404c2e022204400c0011805856510110012030b51203036040000900506181180c0603e50400c0065100340c00d162042e05451200700c20075040360408003103004c102e50340c1c0c4040b02e24400002690400d14081c02d00001c101c10103010083c03814860140012400045804d5009a0a004580004111840d018640b8070310301030442c142c005081c8141c1c0004070b1640300080550f412128140c50782d0f8505071940c0d4030030307403690085900c0d00101c90b0f65510003d4070341c034140001e02c1c50a10500160401c0070300054103840030f04e01061aa003100e48180050b10b41142141d84100d2818014242881d1110b4140700103400c0038004000c1d1900310307001000001300e01c0c0c00009403038001c888041c01d1320b10340d5800e00445291242d40400c542c2c0660300402d01085903c6c00303103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 322947976 1250 322946726 322946731
    0x1206020715020a11032d0c2e0b06040603021615140a022b27030318030f0c050307020604090c09091b080603160b09030c01020f070b280206010302042f03 67
    0x191103041c10700c8105203a0a24401078440c0d419069498003511010b046030523411703945050011308005e1900c0082c089002801140a501e080c554000780904202e200e101218450550140c80d14161000c0e550008002c0c01c40c5030302c68515030050308003160100040b07000baa4412442e2034168404201103c82028074900a814164049503941d11081004101c500c5403482c109400307103c05030003458500d4014200e0b44138404842e0f5050003e440d0034000f0754800d60701c1e1042c0006180070a0682c203035082c01802c51081c440000d5003d0030005d030000b07804070b194100210070038272500c85081c903941d204c005806844180c040080c6100c8420307034841c0a03900500290360001c80c0a0300b2281140005c80d000b01c055201c80c0c00418201801040200d0743d480e00300018881d2420a101034284a0014400c440d41d64030180981c1c0155640400c00d00d6036103118108912054080c0322024030390681108002c1e4a500003070100760700840c20001720303000e14000b00d0b04070441862481304070620990044003201d12031700007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 322949226 1250 322947976 322948057
    0x4080702130207030305060907020a0b04022b1208070924090509040c05030c190b031305070b0a09050f0d0f06021c1d070f1206020715020a1103 63
    0x9001249024940c80a04840c2d842030305c0010391420310504000303c4450007400d502c110741c440c110020000b0006074402d82c0040d4141d40240110425602138220211280400c180c80803500d6018000d100313400c0000c00404a4039110100940c9611004449140c05070044213013080020510400d48254036000d0904d900b164600b84680949a00000e0303055002940c4c02e69254030603500910a5140a1044218051049450f07a191049102c2251043c0c116445816500700380800003c05940082c000c0c0c0c0e007c26404420360303400c40d03114200444c05411082105c80003c007040320200352030800000c046840c081c01442002d851000382d03150080043c017a2002c58815400f4041141c1030341c44011250409484a230000c03170b4244900e64100c0c219900300d10685401e91241004000d91000360081109580f44260760030b04d408180c0c00e21001922903214018002c0090143e2002511040d0780980040000c0d40d0342c880100c030603011841d642e40a0a564040d940080030400500140d00125000c1035561 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 322950476 1250 322949226 322949239
    0x170901022a0402040612060b0307120e0a1a100f030305090d03022107170304110d050309060a0801150e011d12070b070510090c14061909050f061204080702 68
    0x41d00804102a0307001036001d540410340352030410056a00c94011000075008074042c107415454003603030040030310000901e5040f10554815207054140010b101c216034541e0050780c408180381d100c1c030008941240c2101d140410040404012071810b02d0101c0722070480c1c0e0180e41c2c06040951034410010888860b0758228217600c40c0d03041460b09100241c018030760381141803540a45600c82818507100d800801c000302c84000034200300b0000028900322880c01120000d98407141c225001380340c81403862045843d440ea01c03d001192070039440e030f40842454142c032800c100001c90b1a80d0074200b40c1d11040d08552207404a0006040c1e203d803440d000840071000c082c02002d002159403046030b0181080f1043c0c0001c02080030008054042c8402000307052b040e1007181c903042128444070b40b1341c41c0c0c4c034000c54041c0fa001d0792403421090b600c9603118004d480211404c0c00300006081c0d01228040c0441145116441c000c1070a4030840e0350500e4000c0030f07105804554000307600da81d900c0340d0b83d2010766440300d04200d0b800340303 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 322951726 1250 322950476 322950553
    0x302012f070801060f080a1505040c1e030618021003020322080408070e0906070f0c12020114090109170a020a0803010306050a050a0c0e01030506031e030717090102 72
    0x240c10031034100201040000028000d0502491444072096a04140c0f6980d000034204000145440d002c5c521000d440940000d26031038600d000b00811119501916003003071003880c56005000b4040280341100c0c4a1801001140002c3d040c1840b40140300c800a50700034080c5d0491000305002e41c00669100482d200d1402100103030700c41d00240c451220105603400000800c0c1400410010001e40d006402c004032808520b1038003007055941c62000400050030080c0d4443e41840c2240600b805c45c40d2280d1103020301118815216009000300002d0b1103004107a004500821000030041c400d03200d15540082c4490f8031040191000c118039802030300c601c01184075070007400d0f0201d1108805907010350310800000c0b60070f0070204811016100042c01071007000c0e1401003003405640e0480c82110001800b82404140c96a0b03030300001382000a013407016801e412155091000d8044040b0040500c03d20a43c00004101195074008a983c0615000342d03001d603220b03001807071443c02e1884070b004800071500300c881c0424 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 322952976 1250 322951726 322951817
    0x120a0b0d0302011b050403051002090a0504090506092b0c02030a050105010b030703110a050d0911030105011415120c0c0f120405040c030b0906010e0301090203010e0a0318030201 78
    0x18020306059006035076a5500640400619000b8010940309290150409042d500c81c103844150495101003426400101081b00b80c56000814008080091040014ad02c17030703080103600e4450880d2600c2c41030150328039603840d08105643c24112959200103175240780f038168106030386003082c0754400c0c2d91501c960004580024006d004c0c0c075010700990150701e52a400e025402406451960048090094061201c42031240d4040c05585155001100115419032181400e21000b50b4421400d6015400e0000205a400356003148040041058034100d806e0005480d850310300340109806051101c9003200414020002e81d4007801440c40c0d001d0a07a004244001130051601c51b20381588020742002240030801840c241c4641e10414069041c1408484003001c001001c400c40103040c141841081c0c00c080c4903030b4070b0035480340070000e5018008102420303007107900c0b0380c0e0341510820460010b0315840b241e071807018003170204208999040c0c4405209031450700e44038265a00a000c4060411491900354048 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 322954226 1250 322952976 322952989
    0xd030215090304031209120303020a0c17030601090f03150e030d060305010c0905100909020a0e1801050f0312030103060b1305070906120b0105030631151a120a0b 71
    0x900ca824005554072032441c038003410007845001101090006c4407000304084415010211110340d810300e0010394035011400250350300101c0b940040c0401c1102c01c1c03c0c142803180c0720000c40c000d1109803112270000c0d54501c600e000400003400001c186404820090160030740c160454608107410340142d90030700c1c0344401d5801c211421580107591607911030419100082e000107070302000e00415987d400d1600141d4030701030584a43c620610700c5c0320b40c5c00640d800e1003520503023414004000040403d0303c91166900354200140e0207001c2d440c440c81d1035860724030b42c0c2e140000d100c400701549003103040d05507842c41d210300c2c00400400024680080009406000000961048522038501d07601c4001c125414084028048100c441402483c18a05080e07140541c2c0c009c0d040e40d5100c0310844041e1458000c940c0f480581c4400048040111009501c2e17013040c02c0244e03045458039240c82e049400e18107980d80146a136100d0320503046489508100001c1100d4940d0042c403070750004070708201043c90b40d112004101e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 322955476 1250 322954226 322954231
    0x3110309030403111206060d150e010204080607050c07032010030203040605060f0a05060310091503150501060504090f140106110601290a14041202040b01080c04050d030215 76
    0x1460704009414003c129010070f50f2010014252696017640c3c0116040c81e540300c002500081c803070459020b4442c1046484080c0d190100b4100100748125200e804099010350810301132414640103800005070418802d10a40704191005401443c41a1442c1c54945045032098500f240041282d88914529200c001c1c0040b441ea4071590010707a82c0c641803d14500f2184080c202920441d40301100c1f038056600c00c49080c0c140d80c0219042ca0743d81d2659040d00741d0206d8180d003c1e071181820411000400c0302c0070003042d42102e0245c9103400e858082c0d15803d6040750002d004110116500780030510140700d09a000e412401241c1c200061042401074200c00080000d0348032200298045a2030341040388207020b00c82c01404801c018200074514041e4600d000810a8100881c070800868840840c61081007016031500c080d0a036944d0781d5031203180c1d4103a8410300d400e0580c0240e0624405011a52150400f01e200c0c0304055400b9050500309010413002d41a00202a070440c400e103075150011810b011000d60 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 322956726 1250 322955476 322955491
    0x11a0a03120903050106240c150b01020102070209040605100e0103030816030b0301050a060f08010b100c0507090c020d090e06090406180c230303030f0c030717090717010207080d0c031103 82
    0x2d04508840d00c640b0b00180c48030306400c0802c44410801e20000b1409c0005148480500c200031681711702e4803004038024003450348081e6000c4404001d100c01d0048a0340710500504881c09062141d50b11028568254003003884000c00040405001801c555440a02440106100c0c035012030050f8083c800a4252002a1180310100340e68900030440c00d078003400c00b04003d24059000340100303098035000a42103c030080300401400314803103420081040034040031000c0c05a40f0010025143d00100c029a101e070101b010001207403011002040204030740e003c07648078000003840800c0c3d5a40f107a030303100007030500d01d1401040c1000064214000891081b43c00015120100b0041c2c1000401d00742605445441c480031802504100103102400300003000721a84035101d444420740c1c98075078620481e103c426035444070344c0420380c0005010042c480851400c1c222101458030f426044212903280b8202e00c9121001444243c0c200701c005004105a04404960700007420001036440390703802c0e842025071080703d200 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 322957976 1250 322956726 322956749
    0x10180b070908010c021906090c0b0f090316031e03050c0714040f05061005090604030c030305070507050301060b0a0c210203250804030f060f150602011a0a03120903050106 75
    0xa00581c2c10910030300180a90603c020000f100c080d600c0024a60f1a10302c01500c1691610059001d0001150881c40100040c00025a035154000c00c080341c40e420400d0f0341f40c0300c1d0051014994241c54540c207100c00303403900149a002851003865200d08600700e030103002c406000003407262599180091000c107005020210030504040c00c800c0422084915103103c0400c441d240005120041d10b410095000ca08581c1c1802c50380e5581035000030300a03009650009198140165010040503030003001352541622603000c58081c10341347c6041600740c48480c058202d5071201404180201c82c46490b20080361170044440c0300501039070752a4480080314010031200541d02c0000e01c00130080c00d1a200342800c0e00528500e0200201c40d42d1011228401d0b0b12028050000400044080c440160b01011402c13090f50b50810001c15416404002840c641c40340d600994a03001c400d180300d2a120282c0019010010312100311a4215501e002c100c0421102e204204015404c0c0400013840c00d10800b4080c2c0245a9134 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 322959226 1250 322957976 322957979
    0x61213121112030108120307170406020909090105010302031c050408150403110c010903112701080705030c0d0b090a050d120b010e01021506010c08120601020705010f0210180b0709 79
    0x1141e1602001e10648001a50b04000400c400e98022800703513801741c01e00b80d42d20303940d0311201c000b10b07002c0d025080729080644005040c0801c04c4a0b0390300038007103100c0540724450265106410306080b20400d1001079010341159101c40c05a00c3c071070481e20200c5400b81041c41c1815181c2100c0d07803604481e00d000c01c0013428024213200c28541c00100c1e0404c1d1040c08001400e40c2180d030b0000a10720700103480010807811000ca0001c1d03031a0744502d408941c0c10b10b01a01030300c25290084100c00546004c1c4111081e41c00707211004038171030401254030000003a000c1e0002c00d03e5a155034410700700d020014803207481da00640403d1400540c0a02c020b6503208011359584884121031410b801c11940d842d11228140b091800e010019a6008600c804098140940d24607496035100e0040c0d0320030001480040520000064580310a14201005806010207a080780c1e90300361500019142c0c6110480d4610150344000c128040030410b50700903244a0f001050190b0654089a4501a0b04c0f10181d65080109041440 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 322960476 1250 322959226 322959257
    0x1509240702090619050f040207051b0a120c12140d020c0a05040516080a180602040f08070b030c0703020114040b060f091b18100909180206121312 64
    0x4006030409800c44040540000c460b400511304c000034807545c0d01550b25006600000d44c2d403507040d40c01c0c0039040300c1a035008003545240242c0c140e8110030420b1054a01c002c010402419030070759100e0b02940302d90340d1045c0381e0406000c040321a130381c00001c840d541e00302c00c1020031545085c8048056081c642e00100000e00c80c0c001000401d0195800c064002c030300d41803c11a001001e449106403031445414921001d8036100e00c5600941481551500c1c240c2c801c8448000f00442070780180119000403101403002c54954210585810f41d6101d46049902c0900110f03e10380c5030040104512480b90000003042072140c1e61004c00322104980270b031210043c08003000400d0425a191001c014800c0320207008918004181030300394807800c00e13081c2d001d51011420b400d0790100d0750302c10900014000c00441019a00c3d4200130131030702081c011031050505000b07214462040c1141e001c18000d030300030403e60400031241c048140f0150700a0001d800031a0754016400401c1034004c0c070104500d007a954806900b1007030003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 322961726 1250 322960476 322960489
    0x30a05150a02120403030b030c03070b0a08160f180f14030f0a05060c0a140c0f0708030a050405040507050904060e0105030d081303030908120a020301050f030109021509240702 77
    0x1041615440d00401008030004140b03d042c81d0b10941c14100001c44004500100c1e00d44020300c411140c16100b101c0c004030342c1d00c2e0401c001c4c01422802d940d0300c8205a0703818889a000c0c00129480c100400c12401007101b00314000c1a6004070791311001c51611080c0d9440c10b131002a01116804002203420701860900b05080500124000c0d882c040c00901e0121500c0ea601d59039544010241d1690100200b030043c50b56104072602145c07690344070510307038550711010f01e03203074035242c030202c3c860a1441f90507000039214101000f50345000c4120f44910b0b00b41032134141840f010702001440138040090030840c050240c1e669210301000b901a82041a00030341c1020b0605d45008a2a80d028040c056001d0030072604d986026000e03801150300d4a0041180051481c0680b418052100c000c03040038a150b0401c41ca210140d0302960403982c04032190300240c0b00000c103240c2281d084080113504809181c80700c4e081e00001c400100a413000180c4481024102f482c465003080780b00416051209100151000030f41c900f90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 322962976 1250 322961726 322961731
    0xf06090b100f030f0b0a031101020c100206070804080c0109050d030b06040e06190e07020d091401080708070e03030f0309010606030213030f0206190216060302030712020c0309030a0515 81
    0x1a03030024900c076940c1c10040d240040b2107002c9820551100d01039a0848803079001852070030400b91800071401e46a02c0c11070315079100240e1040c01032040840b080040d19142e800c5001c005c005401400e0143c030780784412540040000d03c15184441c0030411624414401d110300cd88850040d03010301102d0b160004001c0c00da907403540c01d031845440d05002c103010310042d0f1354529800410032aa40381055510350b2009000701c000e540101c1c0e84c0141c000c2000f6000b030700401e6592605010740d5174024942e84503c102c200d00310450f0b01c0b150000d0710610020300c081d402801900c1d0081002d044c035031030881841c0002441c5911030408542203507000700030321840420900581014122604003075040031002400862210054030000e80345406c1001706c18295260901240e44c15221121404230310409040c019581c2c4002d00101003582d0b6058900065032032081c0300f9240900d10594551042c1a15085640041c1d00f00d580032030558007080200300515601003110300307076080c07040001c0c2581c1ca80350100c4c0d283c00d4100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 322964226 1250 322962976 322962979
    0x70b070e100503070f0e0d0b100905060103020a0c23060109091a06060702010c080f0409091a16110309060408070807080a02090708041b090e0c04090f1112010f06090b 73
    0x10b00078454032a17040400840c85005910300880d40612440000b83d05890000010303100d01800d0090010882e001041c1e18180e400c1c54001b0300607600c0e5000110304078801c9030071030000501e10502010000c0e0641c0e5482c90942d1140c43d00d20115a1509600c0b41055020780c00f00d070b01c043d50344400e4020400045908030100d241c003160f050651420601081c030902c00c03400000d0400203441d00000070040c1d01c00a580240926000e560740751a15a41c048008004d110b8054459140c40c41c0036100d400d5956460a10804580d0b40c8030760507007000c4a0a03240da0403202400038031030005101595a548500d0050001000064020b0514519280301d00381080d4041e041041c0c603800c0442c500c805030700c40c400c055822520703034645810a40c0d0796040c1860b800070b080840340200034402ca40081c522809411907030280d00315034142d840802d01d6408000860301d103114011302c0b015883c3e031900045164401c116a2440002d040241f0b5105450b00e000e08607800554000c0b80c2c555204400d128245040c400c80d43e94010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 322965476 1250 322964226 322964237
    0x90b07030e010c03060f0303052a0c09060d0c09150509040b04110d030f081803070f02031b0a0302060309030f13060806040204030809280b180d0f080f070b070e10 71
    0x1c0032903000c186c5085000140502c100001c004182410055500c007442c00802c2a03041890003058015443d21021104d0394828084540480c010785481c01c1c1014100d40e20402c0518003e01e81414000505500d140c1802100d65030a40007829032078128a081c8524402d0b80d408400d45014a0031080f210114412a8060038043c01c600001070740144292040000904251f4032070313074424014501e403101c2201c9200e028040400d1590800c8404040003030001c0c4210f05960790200c031512100c034407407001c1d201e482c6d00266000e0104058281100115003020082050702d2400410000012055019200c036114620300c80104106050344000020703041041141c1c04c0d03142910f142c403009060301500c1c4a80744900e0904280340d403142502d05910a4030029a154203a80907601d00d0060b40d507800020003000c40b020600d02e4a20700d454a40c3c03109003036a070701078192902500b450321400364a8020540c1c86410203410800003011901c200e046d00d2050f180c50b030303030000201c000c1300502502c0e1100c1c06c418428040e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 322966726 1250 322965476 322965479
    0x40e0f1810051b040306020c0106050105090a06031a09130c08031602041a03060a06060912080703050f0c013204020108011206020d0c02010501170601030f0204050901090b07030e010c0306 82
    0x48010070030312a000801e80012600740c4412000c0641080d02d000300c0e050326000050000200180c3d03801030701000d40d16100811513560b6600045d549807141800c183e80c170171540c140030300c0658043d510103142c0b22290707020722071011216008501c201f4030a5580c5041c4100031460001041000018800030b4000301000c4e5052000ea40402c3e08100003548000f0b10564641109042e078040c2291851000d03a0018100d91040c00e200300908000d24880c010f02d030010b00b0030040404d0703011000078285a0294400301c410310707011183d03c04480300c1c0c0056a00040e1000d0400040321251400d0180340c041a480c1c54800d09690b40750601d01c00b112182140c1d170b5148050005c204805030380c110000d23a04542c41e11004d80a9060b051034100002d205800008403054600418034800c0c0e54158041d03816070300c2c0090705140c00e804140722143d41c1c0c903003480f000308151410662200141402d4000c941c115039240300102d0182940d903100e00e12901d00701c41c4080001d58494000030000801d00589503100b1203800d0401c1382c0ca = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 322967976 1250 322966726 322966771
    0x506070c0f02091e0f1e010e0103080c120705010b010306211101050f0d06030b01051206060409030c06091b0506040b03010e0705070b0f0a0c091202011211040e0f 71
    0x14104064840c8007900f002039480d556110000b001e115007002c400d10503280104100500d54420340309900220641c1c02d0014000303001c00040c3d416106a901180c071103038a1684d80706000e5210403440c080500030704401d11a01c07240c020160a10520980021070100310010004003201c5070b50340103840143c0d550f54202c4d80c1c6c031219505002504e412a04484824022400684152158038104000700780000340d0b88050072540d900103020b40748250008815641d039002040321b440d2840940040b5a00b158000c601300713140a50240c69064840d0070200422444c6031260f00031998802416146481c4c0d2200420704006400c1e4158054801110341038202401d00075989414041402800c00503484071000c07425060140003030301d80f07540d4001d8000304d0b00e250650000080f42003d84900c81614200052400000c0c0250039a100b0307a00b10710610030070021180c004542960248a0b2207000341d99a003208240c2140041c01400a014007500d00b151a040144000c040140c000740102e117a4540c2c01681c4094 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 322969226 1250 322967976 322967993
    0xb040506250f030b0a03050f0609010507170709050604030b0603100e03040504050a0e0105011d06010c02281a07020102191703150d03030509060f010b090d060204080a0c030506070c 79
    0xc0401e28604128a090480e000340c008002944460743e0040d0301d0000002041030007e80c4401c03034106a81900d2145d208e9040c09400c0c3e410549108020034130704144880c600018100455002006107000c40c0b074a691200444c03010362003a0400d0300c2080e10003040010505081285032182c44516904001e00650f144011780c490082c0d0189522644c0c0b9240442c29014050308811070f94004c00c0020895541e40300c0c501c00d0304640c000c1c1b80031102e15a1b40001b0701c5541c000d1500f044015006081744060241500d51402410010ba1000000380200e44001c2682c3e883c00c1020305208540509045d511507440c000079140600c0c6880050b00c40c0440c2289400048182030956281520703e6002902c9403600324420400c0c4070325580617030f040341510081c40300b032590580140c0d01841128040d280141c5840c40b600124070300034002d05a55910420000c4210304048000e450031074003c0c04014107264a42c036800e0f0405126050582d10400c08120520a0010520240360481000e0510b903100000903603a0000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 322970476 1250 322969226 322969291
    0x6031d12090d060e0105041505090c04021605011b02161a0a0909020f030a060e1b030603070314031201080f0c0409080903060f010807270e0a020d0b040506 68
    0x8a21004651071000e9220a0205281c0030382c00002445040300404510b0300801c0c0032107040d500503450042c20216007217584070300781c060340b41c11002d0440d001c2b03818180400f950140c9005148400038155000c0417a9080c49502800e5000c10f5100c8001c45112000034500b4941c41e94008050032005800c02244188462024100c000003200580f9035003444819500000c0341d6202005190000420300c0c100c5540100651150400c42c1082107410745079500714800281c00c440108800611181480305010003030081c590100c0c000b01207072407094403581c8804400c500a50640700b2a40b0100b130000f2110f0088404602401012006040c4803000c404046d0351030f020a0501030165648917140ca05006000c1c0c00c4a0030148050222043e82c100040c42c1041118240300d0042c2c036008000002c120284c14031803101d00305144041c0301e90f1644984070300c50000d103040c03151060184517500044005840d088003105680d805400e001c00a864142811030814900402c2e1840c40320340000e0316002c070103c1c0c8c200c0b2503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 322971726 1250 322970476 322970503
    0x50702040c02030c0d0f0306060c050a0b0402190807140301230a02040f0b0309070602011a0f03010e011103040c050103181203060b0d0f14070e0d0f1a0106031d 70
    0x58041c10058243d0a40c45003003684690760040c120500070a41c3c0000f4100450800c5076010044079558500854101003004401081600003a640d40c0215001c12006070f0401e000400e01c500070302e150140411000d03050b5100f55000d0b003000300d04000001000c04c08498080058009008003141c02c0d4102d85100d15081844c98641c0071040480c40a4601c0d074161400350483c000b004260646400100d04590001c4900b00030a08ca04400864114810701810382800b0701e0031600700c214418202000703419007160001d070b40c2640d40c44500c031900010034041ca104035101031140070b90780c1c245410694200c45103900143e052508141c40d4081342e1600c8002e0051a0340c01160501c0d10311f10410048015141ca03510021a94102041194400001d0380c031185110101003006c11074403c1300e0f5812109590f0444403d0003261075103d800d241800e05480c4070113007502c40e0b04041e001020a41c0ca00c00f00300c03040c0404d01d02c1103054500501205400d8032038811481c02900d2101404030b00300c9100d130368803005c012250b0b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 322972976 1250 322971726 322971731
    0x32414040e06010e1306051302190e010510020a0209280b13050705070b010608060307090b0901030f1e03031406030619021806030a0212060a081018022805040c05070204 74
    0x91500c5070140c0e103005c0c0381684074500f402982000141528040e02c4901e0176031044040500720000f00442404100495900c40803040b40c030b07860031040000000d41d4003442001d40c0900740820700143d407926602845007c20524140e0b1850160902c07200d03500d02d2010304e88500740f9120b000c2c0c8a039a034019417120118019607001c42e10760341d5400201c8072030088800007000c0c40516030002c5282500110b074203108070300980886014994400908054454100a258202000f00018004a4080016581100e0040e1f0a0604140b0024138a100c0c41052007400e80000ea6a00b002d0b0780f80881c550546508480120000c00c41030901d05201c43e1100c2032544400b0000c0d6000540b01001c4032801103020454600420194580c41c00b0b480345000f0703512000c2e00701440540b0340700040c06071402d01a050242d50015004100011142c3e518200030203d1022562101d00030f90407900041c4c1d180280c94151007400007011a0407040d4011400c40320386203411140c03260341042c441104c81507100f0280ea03100f58046a02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 322974226 1250 322972976 322972981
    0x6060f0909050402151801020d180b031b0c0303060a06050301051e190303021b090403020601090c0302090d14100506060d18081303030908120d0b01032414040e06010e 73
    0xf0704005c07055410241a80c03800306955221035207100782c000815200f81c0984814079400c039822034103003402400c4003403d5000c50400b80403042c2d0500103160710484a0080500c0603910303030380c1d103c603542005030842e0990388008100215400c1c4289984018003103410020706650400c3c0001c0d941c0c160300c101080e1a400490103602c00f0f03503541200030000c64100030031400c1040e101c0c10000d44445141c05004546034500300f03005000e04120030780380d100310b0b015406480c4030b90030050b80001602c4280c40004c01c2580074807110010359201d402c0307208514450300f9a0707001c0c11902c0c04502d08042d2062948640380e07143c5010001030307882c2c40c021110841c001103000242c0601c0501000d04010611801508541d4003040b00522000c007034015000f0780e8002d85a0304075003a42d80c1042965442160030318480868180a001071641107504200104541414046503ca0540395498000341c4aa9107108047c120602e0803c001c1050107900c48001505403410f00c40440c94003441c542c0c408042c840c01c21141c809000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 322975476 1250 322974226 322974229
    0xe0703051b0c0a11030a0201080711240a0c030c021b01020a12210911040e1c021e19080310090203090303040b06182e0305060a06060f0909050402 64
    0x411182510050720340c4074007810689668840c0740f040c080304c04040c466211000d43c5000240e400702103505079904402070740d55603000c41d60f2404082c000c0c4a9882643c1808140605100c2a00548021051407482070302e810500b079426250071003840c105140c909410301503040d6011a00e03400040710500c00c2e07a100650480101d10748281110081c1c816511600700034403c0758041c42405550100d000501c500d18801941c8038100c852021000706440340450101255040581040704e54003101805c0e50143c21445444c1031040008000050042e0415920300b8081c101c21240c0c003405090100041040524089040c02c0c00c000b280809000300202100207110650000310840c054001e5203015034070b0742881203e080e41ca8009480455800c401c18000826609081e555261031007201e130b1965000d92130b19007011994481e29107080c3c2004212034400d516030401680644000c6102d04018487c926242042800315420f6420803800c000c0c448201c44a80c640c8840360105031007092000240c0d640350cd10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 322976726 1250 322975476 322975501
    0xc1101110a06060f08010c090f0e04020406080d0e0111070506030c2a0a030210051306090618140106210b130218070e09010b0406031a0d0c030c0f0e070305 68
    0x407002018642080d0340070400c1a07040e1250720449202c04024000301041c0c0300e0a070790002d01802151030499042c1020400e402054200581241c0040d000082e06512031041c02c0c03c000e2402e1307401c8040b50480c0050030340c40d60b103d401044024280b0700602001402c0c1341c0013958511000d4000d8810100100300c000410f5160400801794081170003070480001e4418508a803034848416065003d03020f03044540309045150b0042e1441010006c800540145117640c805009200d501030680c0c1c040c1d9141e40940c106000414008503050042c4e09401e60016250352040c00c0d140141c2001e0301c1ea2020b0048030900303e004402c0301c4405507001c0303403c0b002e80d9102840d4211240c2c180c0c0d0040c0d80042d9165540c0303013455803442d107503000b44150790710b04410540000500c41201000e101d0821202010041045981d100c2c0e801000d5404841c00030340c009905410010b002d00d80c0700c2d001680e81c4614020100104842659080024a034021980d001e5070305c0c00c00156030f03c040c0100498149900d81000070100481e09 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 322977976 1250 322976726 322976743
    0x90e0405031603020703150c081609270501090b0108060607051204060c14010b030304230d0c050117040b16171510110a083006010305070c110111 64
    0x302d540c0c2c0b00c03120b5820000d60700c690611042e10821072000c4621038903c3e05005419040c0d8064451002d951141d00390588107031300240c0740d182001010f580c082450760b005041c43d2860002400c42400310005104140101c0d18182d00c04d9420a188c80c0032040c0030398010f540154403a134102c84981c1c0390007840c10301a0404451074598541c010002502241054001001c040740d02c0c003a80428101e012405040c900301e50120480e80d84c16072041c00100301d000c1803c42c0c1003e403130101c5c400501b80c2c100118040380d80a440c244d022500961602d00a00c800e503030040c6100d61052091001036914106515810040b030000ba1100086002c0c18150490090268249581d910b071030310034400103072811401d0080310400e0b9809252042200c0c94a4442051188240419900031030740600014140c581c0c0300d0040f940410419881040000d024401e001146480010599078880d01d10380e00380750800c001000c8540080885051010f000c00f80d13030124011580030b80400c1d401703003424040508210a030900c1c11001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 322979226 1250 322977976 322977997
    0xe130807020a0b0301260a030804170903010501080c040510030c050603060105071e11030a03020303010e071b151d030a0c080f071113020f031f031a060906090106090e040503 76
    0xc00020440314030304000c410039106d00c0d41ca001581c10740180703e40f0b440329040b0250008030078901003404a0080000f4200300041c0c25000f03403900120700e000c6400d441d003da0003061160840d80c00b40d04982024095941c0c032010015111040a05507604c2401484a50041a0042c8004400101d45902800c2141d1a80da00324102c3d100b80e400d1200f1100310310700313051001c8070080d82d000001d007101e040c0001c9610300b1a9044e000b131130071a800d00080318042c6100403c1541000740a05449840004084080e0140c40c0103a04600e584640760030b03500c05858021940c4030b803451120710010800c510100503542d07022828038103c2d213401100e0514604070f000d0000c000400e842c1c0018070608000d030840003400c030318030107923402c844005040f440d1000303c1c040c000f1901c000361410000a0411003a840d100c9410003400500c0000e484c1e143e40315802c1100e201c1141c1c03c0394120701828400d803881d041690550155003103403030790780641c10418000d01d80107061189554990400303010808209043c02a1491200e1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 322980476 1250 322979226 322979249
    0x20613050a0b0a021305030c1c062c07060504050a05010309020a1a2a030307110f060109060608060f060a1d03030706060317031e060301090507060306050301060e130807020a 76
    0x1410f1801c0c20095000030342a103c841c18100c1c00007480e00b40410130340c00c2400c0040030081c600585102004914100c0307081258516596104458006032003804404e08401d5092284005003007a00340c517291108a40004043c0801031000704801d83d501111402074640c04c0ca80821500d40c540301007086807125400c540c140399040c4036400484c0041e000544846995407809120052520b2034900749a5000400200e0704e4000300000f400840c003c000380500c0d0700f601e0044480c403112960940703051580a82240c415103868140422aa540c0100c00c1c5402c0700046901e82680c00e00800010000c4c41307007100c40c1c02440800401e5101440b4a039403400801403019080d640d480c07946180c4000184540d0004654081c4a411054000c004141c1624070960001c100c40301454822051040103800041440d58550b40b0340340418001001404500000e0a4a403408a8405d06004c10142515150340002441142903020400c100005104100c80c02d40c03c140e03481da80300c074640040740d0b2061068100f00d46414 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 322981726 1250 322980476 322980481
    0x20c0d150f0903030218040b0a050d0f0b0a0f1a010816020708010f02040f0f0311010e120f0c0307120c0b070303113006011215260706020d020613050a0b 67
    0x140c041d0000d1000015520b0856a942c1b0100c080000319a29591001d4205c1c41c3c1044c02d001ca1306041c94040038850144240943ca403032141c0e0b4082c540242120218003564803806d0401c090f2241c0d0260380c031102c0103009800d0351901101e00091203070400410f0a69100200840d12100500038041040a4a0035000901600f00000401006940244904c503005100800005900c1d21000810701c11b49601070003076000c588003240112001081650915441482201c903041c0070705007000300c501d04465201c09000061100020941010740d03036408802440c940000740d100046040740c016080e503182070b80c1c0039203035003c904088005041d10542d8003403075400005e50003291240340c0119000841d0f01030b80e41290b510b0b010281980040c2c141c0b80302c1d0205001c044003030b40015850304801c01290038500b89a0010f1750b01c03284001c0080c900c2d802820542801041601180d0040c030030390004d007401f40000c1015060300364000f035603000018204940e076800580400c04000c2c06000d0580d000303401294800745030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 322982976 1250 322981726 322981733
    0x2706030212060907050a08070203040e16110607020712051005070203031b041d131b03020102010e010c09050120010f0c0e040902010503061c0c03080a0807020c0d150f09 74
    0x254400480c1074510340d280c0c40040c030749140610b001c3d0b1285616696103810801d42c1041038440c05800b601400c1540014480481c9040e000f00034240b2032546581050384041400f807001d000d04030716065460258001108000d01941c0000b80107003111003036911b01d405c1c48154100701d400d1000740d14450385000e0514080c00003040d8004081c6004001da2014018407c5000442c809103108600c54440070b4100c0341202c3c0c501d2213012184550098980850034842144c6a4500d80386aa80c200341085411b4082418400d5507030922845e5800d141e184000c06c5054001070015202c8030b0180300d0103042000c108100743c0d904140e007441f85c0d00c0d8044040240556507a82d0302100241c07035884801400901e000703460600358034150240d690000c0d0103854182c07854445c070062083c07219403d22840000908080c43c040010f114070010030095000d485681c1e2104c0c06000020132191740500160119413240d500308801e5581d00d00440101540014070342e4a050007030703980760080c0071a8590800740340c3c5080014001d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 322984226 1250 322982976 322982981
    0x2010608030309070e070905010f03020306041e0227030606040b1306060804031b030e19030209040b1503060412050313050d11010c090b031605091c05010c050c0a03270603 75
    0x780c074110b0407405c0e41617179034102c100e40e045083d20400c0d000402d01e9001c1c80000e40260f006581101c0b026002291014416450104103031041d2503002001d640002c82c00c000005240c44191a03510088a40100d2103810300081e55609010f8151071059543d095111540e566404800c800e4000c00d86051140310394501d009041e044c000c584c1940460601180034103501b19108400000c258591150398822142805200d400088058541e07440c05240c40044056074507144140d205922612403103100d46002040c507500b80c0c0944410358084c6e8010340610000942400803405d81c1b0040346445501d0303a460701780d591810f02e03101d02c020f4030381d0081103a641c1110780d00960315a08280c56034000d0220741c1c41a0021202510701d40700d22105442d050001c0f48000d0140d02c400c0617560300c94034140382000010000601d0321022000c400e4a181411044582000000c5c0034403412242070307040060515185104154842400040040c2003010011141c20030380c40003101090300415444c800c0f110340741c4030070b4080c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 322985476 1250 322984226 322984229
    0x5010602010c05120703050726090c04060b0412170f09040c0e0d020112020705030c0f010609021812010e120a110109051203040c181a03010902060f07030201060803030907 75
    0x19420209140e400d03d001d00210707408000c04504210080d80e40410031402030a000d400a4100150315a0010082035101a00e91415401d04071610b850300780a06810300e84141c038082c0034011414014204039650140080c0c504661841107a40c1c07501201b440d1440606182c510011844c0b100442c040c3c4014440d1405040100c805a0b010000e0302030b011000d4034a0f17050912016840b5515103c0b14005520500c0d1402e550a6514400b50070b04500c0d80d43c6c0c0b42560040300d200403680d405654100c0310441c0900a1500070005001c6c2145010880000d00c04003882c4090050301a8520381041c1e00d440b1425800100012240030a440c41d12640303a480b0000c50b8807138400c07000020402400030f01500c00c18481c540321103a000000f4600d10310f40640c6d11420b80c000400584000a0311300300081c00840c0500f04401d03c2d10328000019821851400c00d003100a0100c0405009a240a01200050f140d8400f121408a8200c140382d4a5001c9860120302414064000c21001d000110901403c06c100150060 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 322986726 1250 322985476 322985489
    0x7060306092009010f0c02030a0b040c1505120702100509010b0f0f0a05010305060d0f1203111606020f0c03041d090a030509090403090512060106080a290415090501 72
    0x2440c202082e00d02010740c15400c641c480c2c45010850000c06602904035404861351901b4404200c0c4010b40000b428007802c00c00940d0003e003070b00c0400081040707100c4d45a002c0c000c0344038410b05400d40510f0091440c003038005190034000d502c1c800719003128004c01403601c488251031028821841c1681d4103502031703c0080100380c000c1c0c100b541071441da885c01c14080215600c016120488040c41c1c600114040c000c0503006681114807400c25001040c0b044c04030b40d40c83c5010305680c980d5005044002421207110145000d05650b0910000c03001c40810000301446940048003d81ca440060714a0342061040d0b180f050361034440041c0c0000e454803041c1d8083d85800c000c260480c92540da0708010754441e0409000100000e1042000700170603e4602030f10b940003802442c020403501c4d220004200100901400c20411303034011001041215802048140e2041c440d420501c07260707654440c50080f4103900c244c280000c5610070340b20102c58171203600141901c42036104912071140d80b408004002c110038010302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 322987976 1250 322986726 322986731
    0x7030c030f020a0509090a1413020f01030c02150406021b0a06060515041703040f0605070606080c18150603100609050103110708070609050d020f010509060c0a200706030609 76
    0xc020703924400e03524048025102d262602400c4002c00c4040c1b00d0040804d00780a681c0c2054100c1d844582c480f49100ea0102c42104d0000000c0c1d00400485d01400d12800b4101410070102b81c15650340450306d00800b2406546518481c0c0b1146045c0019004007007864200e10b810000003140c0f0940041e024980c0707030145008012094980040c480100e41031884442141c4c01044200300e0905a840b80c0c2110b000e8180c160ba0401d40c44091070028001c02d0390254000540228210301401024442c4100600e000d4004090690080c00400c1e145c09101d40c0704031a96852000080354201d142d046003100074002000c896032460000005c0d142c41c8510b0040c0000540d100c0008107255001e0b11900ca0030403d500411414a602ca90314102640d03c0f4074801c80c2c5503922581c900001807801c0022642c1c10341e0a401501d0f8050600d6400d40c03c688004000e040203a00802c00d010314200204121a0728540d10708d400184a40300e0120390410581420b11403400b84141038002803010307810b521110640b56034a906 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 322989226 1250 322987976 322987991
    0x20c030d020c120a0506190f0501090504060b0315163e010506010801120501020c06010b0c010f1b0e0109030f0b07080c0703090509060a0e0901090b0708040c091503050607030c03 78
    0x280c613520a6800c1004015078014070102c0d1400480f0b0072644c560f42e00c03140000ca5000340075012001954401e07402013040c140c031030040c401004400e001c2d400c500b41c001d80060400f4000c152a1500c01d0302e0150038444a07002c41d000e2000381520640d450544596880700c044401c0c4401141c0f040401182000e0020503002040c5000c0302c8070060043c0c5029a0301695200600d908008150a204001301421103031507508000f809a20300e8203100050003407603503035615515440e0a800203400e40d0740c45109054900c0c50000013404000708020480e85004561078244203030050b00e40182c407084215040504843d08098140f4104082045107070b120300c0c1c05989034042034445452a04803405400401004504d0b010b600380300c242401d030318040d8426070050500c56144e9a070b18000b21201015504259103035101c1c107800007407111350745070a5041040d80ca00201286085c0e2210b000302c2c1428011001e44039284c0191245950b2040003400c080c40d00710303041d00c425042503500a00245641080c00c3c0c007180c02c0161 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 322990476 1250 322989226 322989259
    0x19080606040b03010f06020c12060c0901030905060a1b140d022104060207020406060c1101111c1701050a2103120e010218030303100927080a02010b1504090903020c030d020c 76
    0x1080082d0b2032070030020216511250b44040302d540001c00310353704059a500b900c00110302c003044940c0c020700300b00d0070000f0590a017005548103400c5050081050107a8500880e81010820084940000307800a005031100c03044080030a1140700301c02e4040e0400c01c48003d00c02802502c1c3d00502807148211000c010700b81c0e860100303036440707500c0010280c075070105401d00d02e0603540502e25500c12025803c060300d10316135001002c1070750345414803005d01c0011490401040d41205100409024000c100d4a1746d0b9414075000c0608003882e0070072100100074215150180415024140000c0c00c04803c0009108000a01c40424000c1d000b0090107403060100c039000e4009801c02000712070042462011000016043c506040f0190002300041000c0341c00341a41b098450600700e0300a82007611980195649903903001009003999051203065105440c120003040c1608403200032101150811040810070017883d00b801da05000103c000d04d90940070b2500e01182e482ea0120b845840920216010400d442141c0c1c1d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 322991726 1250 322990476 322990489
    0xb040b0d0605130c2c090303070c05010b06120a150605030703020702010918140903030702071205012c2e0b12010c020106170319080606040b03010f06020c 68
    0x425180d00160021a558085103164000982c003104102058000c6042591260340540d200e50040c140c0303da6040403640c034075100b807800034000030b2102c00d80082420001071803516480040d24200038000d1021090040000039089185422002401c1a403560070344010701d98604070450700049154604070100d4440c84829600405450480c1d55a80c11583c6001c4280c0088d0310030f0f02c0a1303062013088180084c0075010116024144103601601180380848025040442c0340d0191846580c0d803c01c1c410082103590000d1700b28129440411403582c7d94206040950040c0101c110b444407002d8201d01c1c4003660401c0c02c0c2c521044c10007a404841d400190a1aa039400a2903000c07016404903854003081d0700c1da4801e0b008903825542c0184000014031040d100b90b0700f141c031000c11040160b510380e0400c00100009007008100140c00401851800030f40042c4d0008540d40344169800703206808000c41c065488034810380e005020805040d0f650703540c540340e900d0b2a6864a11681005110324050300c0700d5030a00c1c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 322992976 1250 322991726 322991741
    0xc0730090806040c0504050c07060e0d1704030e040f0209120c030c01170109380a0e0633040f05100504030206030403050304082802060106030e030421080406020d030b04 74
    0x40416074661706110410000d44009080008400310900542020851038810030318014100f07802040c450f042c0c08005400c8030715401c2c140b19034402c05c90130030003c6500902c0742c4003512003c60700000c081e201402d900c0001d0281d0b42d01d01d501304500400c0d40800400001d00c82045010032030465a0340e44801c00115040107880526004614000004108141c0c05403c0240804200c070170010343c48441c10280b800640c52500b05442c030310702161a0b4003090401a940a01910301a10142c0e4903180c1039000c40d2512340390003251a8103151124000020b0240a258108501c0302c540402d60b0b038640c3c440440d040740d003003402400d1107010b422400301c90301406207003268110782c0e01030903680c21940d0700e0f2402e4815800c010019521f0308030400408480511210042c84009055403c0c0401c0245400e4028036001d0160000c000f414a8403100b00e444801c0081a201101d01d441c44010480c41d050180e10041b0100c042d00174003140c000324000c03c90075008102d1410700d20441d035040107022501e10800c0241c5018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 322994226 1250 322992976 322992983
    0xe0103060f0b040b070501240306050c03060d0f060e03192019060f06031a0a0515040c1b060506100c0b04062304080c240c073009080604 60
    0x2c2100b00405055139000c1d00308140144000540710030000544044050842504000e040f100c0105008101d0705219041d0006041407401c3c0c210b1505c1008990180c201540c0a0440810403d1107000c100340c0c0d80150301c071116444281e94694100c0c0d42d107858050900f90941c400718117020341c0d00c0442000451a4030007c80034600170f25030a242e403a803251307842d10042411b803142512038030700040c8051035000e410002c52185e04845030b250b0b80c81c00764488002c0c0203444031402c10308050501414a03506d414a000d440303401c83e0000b410124400c401c1c0c0b41c90420b41d140d0811490441700850500c1030b11f50107140309105c103079225058540c00d40c0c42180c2c0c80c000000300400a41204010402150740c55114040554031a00c4200000740c0541020240c5201241d00b02c80e8100001000c56a54405201c5030303150311041d0884000c0301001c0d41450505040040c2204c98080003c40d141c0140b1030f06540d1020900c0f0504805d09855207882501c0c101e085440d041c0b00f011403040302e000150703204002002d5109541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 322995476 1250 322994226 322994249
    0x6030513030f14030106021b03150406050709031b060201110a02030a050a0c0818131a0609030a0804030f0b0f070807030b030f1005010314030301050a140402190e0103060f 75
    0x2260303409a402c805030a0703a420070401c44040d440b09007a0001c000b140a4285030300100b034000700114407a600e0070b2104000c6400394214042082e62035403280d42550300070303070301c00800701d02c1d07641e28401150940510352020b01480350b0075501200030662000d460041e0350180d8020321126050b9413003840288030741811030005a20400c5a0080144200b001d0801020f1500c0d14034110009500c80203a9500054480021000402000c65007032414149a1140c2c51603040203000f621a01e000d8645000c0c8030180580c00303800d0004901d0065542480611640c07a801240303991a280c481c104003c011074107010846480d24103070f01254154400040309445411240c0d200340035a40d5402003200034022400e00f26400d03118005071013248900504c140d402c21001c80c40000b9040d071640c10000580c11008246280d01e400400041c80356850f07068200d025503004080740340a404400001c28000c6c451030700c1d0140d15002601004103000e03409003000e5201e8500760703028080e6986074074128401c2445849100010307034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 322996726 1250 322995476 322995511
    0x1504020d060903031d01021206030d1202160b0c0309010c05091e0a26070f0803042105060a06031506290d020d0b0a060c0b01030212010207051203070207060305 70
    0xc0d40e0b40c02c2000102c0c403070b140c0400c100100c46005241ca1802102801842c0d4012441c640e50b4540c100c50360350f104e201100100007005c400710025081e080460082042c07150000359140311180d901407811b204070307407003440c03600710340703003a0140e181d042d0419514002c0315403c1881c20342d6000c1c8200d09654442900600c41a66215480c51090100c007581007101e410540c0b0748000a03000340d0f19203403250912081088179440e56440e400090070030105800c5032440595001d01801000b038004141d9040e1018003c80b42c002050f40603148824451145005015100b008104810410341da0403c80440c2d02c601008042c0111088641046d42c03514015242201220b106450000c4034241c0c2202e209000304988525104091700c00b202070340c0c042051002d07010344405405c000c1d03080c450000d40c000d101c146450044a001c2d561000786100b01071001a1041d81c40e203503030741c0d9800e90030350468045075800001c4039110381c00c01d03420340c840d40c01c00c45d00640035001e2150300144d00b034024024184910521f0304840e501c02c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 322997976 1250 322996726 322996733
    0x70b030c120f0403051c29040b010c0b0f090a0804031505071b03050a05090306130507150f030203070e040f0903030f0204080309040f0e06010f030506070519140c07090902031504020d 80
    0x30500b280d4188003860701c2d0300c0c0260343d13100803503040b102c5001c811f030382080b1580304441032009031105050128100401c4c018800702007040c0445068009101346040c00803915010725091800c04000760190410320700103400000c0002080101b415445116018081c980c5c03220f2080e10480c5003107000182000d5030007880c2000910410042002404074101942090f0100e404645004000c60b00504490300c403e0148041c090304100e03e0000706130903441c00e0a0140001030040c101c001710310302c0401f07154000c008612401d0048039110340c0c031040a0020846500d0a032a0b40001d00304101003900401d280c034505070007200a9008440a07602054011440c0c04849024071000340580002d604c01e031036a400010444010a0100600030004075500b00e440701c0c11350a181b418010040d0242042c003c0801c0010440741c0101c80c5c001402d0841c5c01c1020000d080580114054442c0598a01c0f01340944440416556440e81c01886c0c903e0007607084500f40300440707814000003c0d00b6100a54041c4400c818003000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 322999226 1250 322997976 322998007
    0x301031506060e040b03120c030322080a081012060b09161706060d18110118051908190c050a0303052502061c0c0905010509040e070b030c120f040305 66
    0x5c2900250031101c8240050701041c3c0706401140141009810010a010150081c80b0031017a18540d103841069101480f0354810300c0078461041403c0500caa8540020484510004601d00400c1c42000d42e03070048440e0710307040d4010490220100d108120600c0480d42d4800164400419611652514403082d02400d5102441c0c0c6e1000307000d281e22170b0f41080610041c181074051007141c40c4200303000c04060a02d07450200304c030216480c145410000100d11401c800082d401d01241210700607501d026502040402c0340050441582101e10075200310b00c0d40c1900e10320000b8002e5020342c010000005c03003030780b98000c001c5141c8079440040c0020784140502c51681c01d00000e038540075141114a88003000141e8085256600082c10101c8404442551056401040d02480e6069480307880d0041c0030350701b401c001800d240681d0302c1c80c0d4021b1340d9a0b1000d040d200800c0002a014014070341c4115101d00d01902d2241407a400801144614a018000301d03800403600c9a01070b000eaa410b885641c01c140110404d01007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 323000476 1250 322999226 322999241
    0x10f140702040e010b03100b060703121b090609090203040b0c090a03060c02030927280501030503040f061404031704031a01031e0203060f0a061a0301031506060e04 72
    0x55005040080c080142e40ea8400c04140c0658080049260200c1c0350805007805040c482403180942401e82400700c981c1d60a04684016501d4200794607030000d01a843c00c0240840106240c40c070642d0074001c090241c1150b00a1700301d5140341d42d50040f244c2c40ea0488411307400f00342c5004240c4101c1c0c002080680c41c1440c05040c41300e0323001e8600b41e07041740d40303407510710aa856104003140540c000007503d0b0103a00b451640c520a0a800310306541c940e460141c07100d0304115000f40046c0d6044a1000c0340d940d0540b0f40c0c108128400b1061005004a507164106262298042d2050000b61a0100c00020342135000d860301590b40340010343c0c094145461600c0f1054502410000311403040c0d410000800025220440c0380b41140b0213a9a2441d40d605601c2c0c10825000140f501100280c6058802d9006a600040030317070303002c500314441c0c13007560b26080380003000b80c100d5802c419000000c02841c000406910000785040b0390042261000f086e18803061001220228020b04000070a051180350903130a09401598 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 323001726 1250 323000476 323000507
    0xc0303011703090a09050708060604030201080a0506040b0409061a01030e06040b07090308030112030905040b100e03031908041505070c1211030301090902010201050c031509041502030a0203061e010f 87
    0x3480c0c250680002030340e040f42600880c5c50982e66a09001640340d00c8041c182d8031800035100e1038505811900003805100c401028280520784403000141c09840c0c0c2d4100c9407411402030020300c0790040a140200c00b500310100c2e501800c070382c034108a07500d03503200c1c0c02820b8100c810380c0e0251146440784c1c0c81d9520200d000034115402e0105651001000842c1c00c002035009244028016001020074900140f000c802c40d444a8030803402c00c410302c2e180c0e40e2514400c0c07041599a00700a10320309801800300f403c5006004507001c8142c00404131351010340d04000d105d44980e124146054a03128540c18190445109507401400102030f4022040002c40030b202d80c60011100e03041c56011224507541702c0c3e145603c240c0044111070307102c3c40c403402107507024058590003142c1080c910f800d528160200c440501d03407111000340b08030007102c0405c0070702203004030390200340340510401e544d01d00d4865840d101942c02a1170050080d0213080b840c0c2e2a207880c41e0040090540169a41564030100c00011210100340440c3d61 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 323002976 1250 323001726 323001733
    0x3010f0f09030e1c083f0a0905030a030c030603060c030b011103030f071b050d231213150c09050f040e0d05030907081603031b050a1b1710060504020c03030117 70
    0x305200b0810f000c48481e062a032048003c207110703500f41801c030000c1014103041016230804029000081d030110542e02c80ca092440e0002d5000d01d400d208401401ca25800502160703d40002d5601a1340c0c950000e600c058403c0e280c0e881081c040d000304950b40d2004461002d0340090344030200d5012b91085910745002403082039042110045515480d0408020f02d043d03a022454150f0300786103900380342c005410703a4200810341505151421280121400e001007403141040304100f804001c206d4185c01e0003440e61b018031820004024075010190809889001c1d5a200c1c403420600d0515907d003c1c000c0c0400540068090680d10412250a0751075410240800300e8030700030361501141c5280c04108036042c2e00d071600d003031407051132841c103003e884866407100c00d40c401c01d10070440d4408150005030210f001c6522001220509030f4101c030746141c1001d1274120344c40000c800390601c18031000003c1e0140090700203a508014060b81c0d001004200e11988480164540040c03004100090003050400104000402903 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 323004226 1250 323002976 323003017
    0xa030c030e27010e06030a05060c0d15150e1e04091103010f09022701060807090e13050f0303010f090504020f1804030206010503121803010f0f09030e1c08 68
    0x151805400102c1c2030042c0c140d00104102942410440d400c142d00b640030b0115051039469907503d0f0f410040240290450000d03c1020507030705a03200051203e1000680f00103584c81c4c01661191040071401400024611036403020203180150220034a0481c00c0b00081002480c0b4051101400ca0303c90240c1d5022100040d03038a880c5c40c03c1c05141c158000140000071a80d565104104080c40000c030940c1c404950f948040101d14203042003941503e4030b41c1030184066554200c2211440400c0e04110a4000500c06110f9210021800c240b000c034850801d40e1110a1003e4045603030340401d100d10b9030342c0c0300b005030200540421944980d8001c0c1c0050262510a10b80c8800703e0305400700510029018600201080145581484900e000d400100c1c0501002c02c2072407190403250050050403220030314500300c0d2148540c0c0075803010403400d40303450f414480d440d0100307a10401405080c00c10380128940e001c0700b100314540040381124000302501e0001040c503264407a4245908114007e64020500810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 323005476 1250 323004226 323004259
    0xf070e15040501080109020a080103080715140103060e010b060910030f050f100803030c0f030612070611011104050d03030e250609050105090a0509070207031a06030106080a030c030e 80
    0x215100440d8040c00036986601d02000104401ca050740b00c3c0410782d00c144081ca849943c0030f80498116500032141c03540b126941c0c02c01d4589240d0b0303820900c4055181800c1030380c210540da90054100c03405039908224251138001a90700307a07040ca000c210340c1724008206c0e12006103042c01b852948541c1c2454001900482040c40d40f04a40c0e00340d45a0003a00c68800401140c0401e00307a415014243c1c4602640c1107040a462012107806404800e48800a0200024200b51035940180f11111102d40491303d00543d00c1c900a1b00380155404c0c1c04540d9401c03c0041d034454180e9004075001c071540588a02400d10300b41e00c04900500c194101100603002d43d0026030baa034640c4a1180c1520040c408100d0465450404c000e090340c8411342c869030510000b4046030149540d14210913040b03c509035003040342036842400807410030105030001040401401c044444551034401018402c1e101030b0003c101040e128213155513a844820320040001e0402d102c1100028460130139812502805420340000651046 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 323006726 1250 323005476 323005489
    0xf1501300e0c0f011b020103020304170d05040501060f140402030c1204060f1506050315040b0301020a020f070b0304020618061b1f02090f041802030f0708060108060f0f070e 76
    0x20241da41d9019001000c02d52030718124901c400c510909012800d080200d0083c50103461203c03003c2e0502d68003200140a001c0e0130091001080301ca60103a55951414051201c01483e0a075002d859070341c40c191011500464995802c0c043e1440c18024002c010302036810400030303502c020300c940c006400520840c00d41c108616416805075101d20004540041d4010010040310501d82c1cad000080802084100303e91900305044a8100203011050803098400b000480d01424550a41d66003644c8000340041c12140d000c81d02144540032401a106190340e968000c3e90f80c0d000644019510420030031807a050610703a0001c03800c468034007426280c2800c1c0503007a240600d62010500d54159002064680c01c03195140140c4244021203450441c248118480450800e0103e1240c00d802160360310843d401c0c207003aa0000f14405d650083c202e9200d02c100d895540c0e118503881c03250304898461038001103410745021806511800d01001c00080c1541c071038040114040d4003909020601c080c58024041c8c83c0c5a10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 323007976 1250 323006726 323006741
    0x115120804050d0f03020f120406030905010e0d05090406080705030606011b02060a0314060d150b04020d11070506162a0c0b03011404060308120c12010e0f150130 71
    0x41d8155200f0320300034103010f4109031202c0c480d540e5980002120f518184406401d031012b45042e842c0004074a411450070500500000c0030300070182c49041d04001020b54080c00504040c0003d9409008040d95442c820f070f41c0c0c3d59a8024a540b40d00070000158480d44209010318042181e41c4d00c51132114070316000315140e94042c600c8800040d465240c12078041200401581e0450410380e441c5a01c80f0903903c2d045140d044e007090000300583c0340e142c60302080e5201d4064400c0000300c001d007000464201100b1000c00c2d030088800b2529400b480000607480e018080c046200401151601c0307a410b08071000316400c12028040c1d50301642601600200030440c4948008040c20b6040c076426900d50502d1803038110001000340081c401e42c1854014400162820141c1d180c81100c211984500c0d00d070180c00311414000c180360107100301801e100020701071028030328060140b0b44c4e8103820005074861241004c5da80000440d8140428041582d0203000e00890106015044113450850a40c944104c070400a070340c020f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 323009226 1250 323007976 323007983
    0x50903090f0d050a083f070f080402060a1416140c13050603010e0307210c0519061b031506180902070201090b0c1e0115120804050d 58
    0x114040005007044a541141c01c041212106501d008503520f0307954480b62008000c055801c080740340740011441c00e21310801c0380001750088a0b03040004803250b000c504142031840212003003401041039036010350050007041c103d559407000169150340a011842d88103040540810843e412144030020401c00902900e00145a00205110084c1000b024011181d407449056801032000508642d4130072070624812090101d010410f5501d0000007401001000c4880348a400002001e5040060740480c5000c80640001c0300c113800001c03400200e8018518000040140d848860500b45101c00d80c5a00130a02e0310829002c150381c02a601078450304000380c24008003190721070700c1504141e4501002ca0004d01080e00d48259070406081000d81c0049551151100d90790b400140c3c2c40c1564843e205540280002d003507215a69052455207903030b40c01410500c8070250350000000340e01c0308018000c162140401010070f1803290300f44a20301c0a11895a44100d507040400c010008094603408a1086540e00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 323010476 1250 323009226 323009233
    0x9060d05041a010609050f09100803030c0301150f200a15060906120b0f07020708071403010c0c03140a090807030302150f040f082b050703060801020909180307060509 73
    0x2003000c480300080e541138201d40c081c008241c07001e10841c0ca8a82020170003a0040310b41c51a240c880c6000000384500a41000540c2e0200000b00300d80b102d1903c0080d4100c40180a13007901001c0c814500b15031600040440d100000e46601e1258807540703014038030b0b82200545605070341d00a0342c6541d5810200a0070340074140c050362154010000105103104e920010400303441900250180b90f61043c0a100d00140601c4500d100140400d0301070303208004590141206008490b0040e80301c060115000c85c0700c00c54548a5801e10581380d10641c828903804c1e9882e5419204d202e00190710120600d0b50b5040b02070f045080101400002800c0c01040000100850103600640b0764001402c0141d11401401407080071041104802c0c0000200c807020261511500000d040780c8031b6294030360b071140d000d01c1190440c00500c0342d4100c0c0d0756404081c4e8000743c065496910200b02e01580c07160410709074000d400b6100d034882041c030005048402d0648004e585c00c2c00322400c1c0c0b440c1005a40d030315811170760f05585840d166030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 323011726 1250 323010476 323010503
    0xc010c20030714131e050c0705060415050c0c12030901020d020d050108010c1d0103050a0b100306050916051902030405060708030402041128090f1d0a0c090b09060d0504 74
    0x134400c43e08808500d83c040d00340640202a600c01c054210b0081c403400e04076039180001010100224280c03100300b45e0010548030b29042508144808865044007203920502e01130126145042c0041210000310081d40070349240541d680d0603000d0742d003009100c008295001c20080c00b010130300b44003d00c01090500c0000507254107202889003101c101504140c14840c848881d800390581d50420000150000d2901080d150758008034070000c3c107650160750703406c5070211008817007107909900490300b03440c0141d8184c029582d80380b40340f0b401da8207510b070100003144042090821840322100d10f50031940490040b43e01c0d00da601d50104074103078041c03c1c09891800001c000d00c02103281600481c000c50301004403603030800341c070034500717489a81090f81c103600c3c041049412003000030700031111440201100c4560408203542d495070f003154128010352251a07101540d001400d607500c40e01c90020040d041740d0724054441c3c14119941c01541c014458076511070010701a001124119028080c420b611507030750b504019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 323012976 1250 323011726 323011729
    0x40f020a080304080a060614060f1c02030108030d05090105131118010f060f0c0b150d0b09030a030b03061302010809150a020c0f010608031c06050402070f02010906020c010c20030714 80
    0x540c4960820641e2034403401003023065540704415103216020f00c40846544040d000ca00c5a51468000c2c401000c46001000000751018080050140803240030740138042941d272041164201c5004885603025408444814404030b0400202340082ea8009030030103100014080b6081110282607001c41b04032010700c1810300500c0e61104d0010210003840c00d14100c8074005036103007041500014190f211507242c90940301358999540820320080340d00202801464106240c065403a80d01200304000400c0c20011000300c0d604001540714840c1000202e1108807a003103030300444882d40003400211040c8203180c000444c901061401070700500e1801c000590300c04200f5010703800c1000c0b0a801011513403401004005100002c001c83d00f0200301c0b01d101418401002805000811054100da50800d2000c43da2074200404214145000da000b41c8510f0165552414126980c0410021884c009010441ca91000851000c10076a2581c010320a04101201810210f07140050b15445100d0001004003400f81a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 323014226 1250 323012976 323012981
    0xf05030109091a090a173a09030203090118030f03050a1812030e01020f0718020708040b03270a020607060204120308190b0105041707030f060902031002090108040f020a080304080a06 80
    0x40416802600f8111015401644100c61000f000c91a464580f000e50b81304401c90b403440020040e41f44200008040d45c10029a650030104020740410a03480e1100d02400b084c0c00c1c484202eaa0240312281000307040c0c1d500b140d060300082080300c00d01c48003d141a03001589460342c8405030040c4225088c054280341401000c0110022107281990003e410103e88070901140d4601503c1c1281c030028541d14101040800030322802e1005001c07130201050102c0e544101400a44c02083c0c40d80c17440c1402440103080c076200c02c814400d0001c95900110304940181420006000000d01402006051940c2d411040003000c95149044001501c01c400b04440c4e05561116a601c5a804010801801c1041c0300042c01e10f1207a8062001c0313101605600c85480303a0100140000f03036902501c465400310103840c05201270400f209040b84680030760092080b04001e14070907100c1d6071300140d54019964a03140c449400001500f0400c0c5d8100c480200040707090396040008200034994840240618402070a29070b04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 323015476 1250 323014226 323014253
    0x10e0606042f0c070602010e1c020607030f0b100305091e210417030301170d0906050d0b0603010611060a050103020a060f0504090912020d0f05030109091a090a 70
    0x70541c0750070002e060000d60180c1000c00014025107680010794a00500d140030b02840d2606070b040e206200c0049205079040d0801065501084103d502100403814107000c070b0700400100c0001a0b00071000240181d100740c202e12110040e0000005070344440340042020440b0114107400480c1d00e03181072060300b05c0100a041c4074054603d11508685030102e42103034540768200c1e945441d076460241d45aa3f03080e44282198002d1010b48418000c4880303c0e001d03035403650400d10501d410407110300700c4041c82480c0881c02c00c40681c0903544905241d42000d0060300c02da0002c102c15550145e0700e43e0b0320f28998a69100840c041e10703081c0c580800000104420610300200140030008180c2840d00400040e1110309400c000e66146040581c9034080004080f2440d005543c0103a9842d8100040ca205000c05011515525002c503400d480500035005e1003611512404080500014001c20041240017980e07449801a284100d042040c0e058400b4001801c803842550302c0455038100c0221b2900300110340c0074444 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 323016726 1250 323015476 323015479
    0x306050618010302130b040e03070c060f05120604020705030c06010b090f060f0d0209030f011a120d020a03110c0307090f150b030403080403140d0f0509070305030f0c010b12010e0606 80
    0x1010341d811135020039101e071054850503131125101d41c03100015a07515001803d5005102e030803242c503121036040042012401c0e00c02c50b40881c64260102c07142c0762258084540745207540d0901001c0b500c81a0510000390310007007003074a50380014012030a4110051207020300820601c80000d84424ae00b504219013000c1e40103025200d8402000301d552020415001e9465180d048140142c079900c0d0580400d0130000b0a01d054003140d4a44600c1d42c040011019146001d081c081c1d6010002048240d249030f07070b9580100c01c40015a003c80c40ca6000203200380c80c04c004030070599003580c01414030007011074503090643d04000d203407d48440a11a200320343d4820f030350f0030200b03441c0315141e42850414000220310001d0b00190401414000003070506010b00e20001031070718540b103019074520000351018002c16080382d03441921814207022a8482100052500c2540d8020380958641410340340e81000661000030010069501c2d10b8000d4820b54a040200c80c00c180f010002299140d500c046035400c140b030042445 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 323017976 1250 323016726 323016769
    0xc0706091d0103020f012d02010f0221040507170f010c09050a031e0804030614100b04060315080d020a15091538031e0a1b080703060506 60
    0x500d000307480074046811070760140d801d410720220400c0102d0344424607030351200d205944040e007106600202a521500f001d5035074001c01000043e104040141c0c40340010604000460002c40203204049101d45a00148a03404480c0926540c00c03005c2840c1403a5030b01d070b80350b03900540f160311b501071400c2c0182c041100091904400660030500001d8a401d2540009440c034281c000a8840201d0107182c01c0586641260800e61659540e280c098098461591015454403415000c0b50340740084950b440c0070b82e8030301031409041a0802504800500d01102a003428910841c80042c0da01814001d250708800554081d149079005814045424030340220010181ea00e40050341300402c04145030342070b00c0842d81d1800b1684021100e81c00580307201e403c018200c00031061078510f0740442d0301c83c1051000701096095600305040718110260b00080121100c203150002808000010703511404101005a0307604a01080c985400e081413501080d80c000f129038650728012f00c4a00d2802c0d003030182c0b01000c02c0044 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 323019226 1250 323017976 323018009
    0x1f0e0108120d060e0408040303110601060203030112020607020a060c140c03070302040e010902040501091a0904020303180a0e07030203040b010b070201020738070606231e0301020c070609 82
    0x680d5a181c6080c1d81c0840c2441010403800020040740c0c002400900f2960740500c80d9041904003600c0c940d10500c000c4010400782c0119484031940842e246040303441a40245041d43c0c6482d1980c061580d80c900c080740d000c0c000704480030050b0365070400d40003d8002d540e0b0f220000c0240f0300e0200b21840c0190200e04031540407403c20704240e81d0005c2c0032400e6960548000c21008240d01403907003d0810844020360003401c200000c240207409030b0040702001d010000c1e24240040038014007078030190960740650075400400041c02d110840d40c0002c03041200c080d0000400c0c80d59240d942d0032800e0156100c0700040e400009210600c600c41680c5405804580d000034070709012580040e6951406104104121040381c80b40314007807044c507241500c0170001d050203030240400c070301127108964002917003200e04604c0c4c540302085141c008500104040c00c0300840c41c6080110800b0480c0490401c2d281d005009503141446001e0380342800a06520358003900201601800e149000c0d10301c0501e03130000721000d200480c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 323020476 1250 323019226 323019239
    0x12031605040f0b0d1b02061609031a1512060618010b090d050708190c08010603020105031803090607080901030b1504031e1e060b01080105090a231f0e01 67
    0x11140b0403650880c44850355011650f000d000a4824042519080341801000302d80c880e4010500c42d114604641e200c5104d440554000d590103100d9001c06402c845600060f801d8a00340004040e0300300c5084034840d21441c6c50700c0002070300708800565201c80341d0082e41c14007485050070301840070100e04040c1004c0003076040c08040d40c80e50244010080c4501c65200c00c070400e2203801e02ca4007000e004500c0560300d100b1100780c5d03c0b00341071220440c1120100401580010844010b100381c9040d07035416541d1900e19110a60000d1481122040940160008009541da01d0780c1c0c1e08001c24803903108184140d1141c16140000d000c0f83c40152a45024181000d407503030004032004111801d89610040b1610303000041c2c0c1141c08440b040b03d000510550300b110400322209508070710810f002d4894182030000c0103c540044464840a204160b0010914408203503680c071280c01421500030030070351311545a207071800180c496000546070721149100d20004074030340301c0701e20b103a14003c1d000603e80f40d905945080d6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 323021582 1106 323020476 323020499
    0x2070c0305010c020f100204060c0f0503090307060c0203010e06010602061807030b0103030305010e180703030e3705041404030f09031719030b10050f09031203160504 73
    0x8106d013522590900032513050742d000f507440c182011701d03903503e012899003801d0342101c5501091003104404c1d141040848014602079a54100c01a0703180141360840d505036509400300e4210100601c0540e0300040c0e120f03041100d0720483c49403460502e51003402e0100036040188407240a000000605a254000e58140d550101c107031a101d4441030b00c50110a800880b40f51569040080e080020a0003150302e01802c40b4085c0168080794080008141000180b40c0600c4c100400b07160320400c1d8042d49201407001d00800d5600f013000068801d50302c10344410040004040080303030003101021038455a2150f0080da440480940020b00c5503500720f16a800c44200480c4030205645114501c622a0190b031000c04009480d10007142400f4204891a41c0011611000003a003001000c09070745081200112040300c1c1450315849003800c03940b82e81c9000c040400700d030401809020a01c407400415 = true := by decide +kernel

theorem cover : BRFrame.Cov 322841726 323021582 := by
  have h0 := BRFrame.cov_init 322841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 322841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 322841726 ≤ n) (h2 : n < 323021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
