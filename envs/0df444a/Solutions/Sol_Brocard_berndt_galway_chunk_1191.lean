-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1191
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:40:55.118606+00:00
-- url     : https://prove2.me/submissions/42f3f6cb-5aa9-4b56-806c-a4ecd81ccb4d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 214028776 ≤ n < 214208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 214030026 1250 214028776 214028779
    0x10c0f0f06060509180106080a0f320105070201060f03080a0c0206211503010c120203070c1509200607030c020a0911070c1d070f030e0313031103060114 67
    0x1008029000c00903140e02000150500030085070301400c04060340b440140b4891701c1c1c0c912a41c6000030100d002100044c43c0d01c0219889140070207001c1d07495841c01003080709084c2d40d500c01c0ca600900507050400b0080707150704d50308030080000764610300088000d003510319650001100c21500c1d5000c1c400b0a01c040c0803509015402d04022000800c1403001c1074241c1721b585100041d4004015035122404482101c0501407445001b9084403850400101401c841c86030600d840440c0195494084814698000d50b51000c20713030800641c1c00b001c1d601c80d8002841c41c0d400360358045540d5070600c41002070440401180d40c02c1d9100c03c100d4001c040000c0b9080e8490346074060188003640d0329403800c44d66400089c20241c080706030280103801d012454440d19402c0b4210031518130b1011000412004c0c44c800d03408607030b101080101a03564603603130710550700203001401103070415860341890340c44000708000801145621000c052100c600c5c504281c0840341a10030b10601c03c1d08407400401c803803e041a43c0003c1000c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 214031276 1250 214030026 214030043
    0xa0509010c02040e0304030309090c0804170403212c130f0c0306170a210203120c090307050913030305100e0f100504090b04060e12180f010c0f 63
    0x14500141c945641c0044001e600c42e080942c070b4201c8981c0440603101300c034401c0e141e07d600c11b03450b400d413281910060780307880b000a803180c00001c02250411903c0303d40307150b100c05950b02d07041c0c036600c0d2900511100c0c218000002615224128055400031130701c2c0c0000b80c1c1c1c131503450b800d000f078907890300e8000c0c4010034152080c9000c0344990848101c1d6401514003a14920b42046110422000079010306031360320503a40101944070030301071210b501207402c08003654003200e5450303100700e612100c0c5102c4600c0c1144404502c02407101d001d9001d4043c1605016034045d030b02058032034803010101450b1001e030f078000d6802014075405010380c542c2003188034042941e2500740403404c0e5a89490b1082100c50710b0f403201059010300401d00c0408410303082000d0060403941c5002c403429454030144800d407101000c00501c4541d0150000c0e0100b002031f4050b2481c4480c14040e22120366000c008400a44c10600000050152090190159280c02c4130640c12200c800c0c204050101820744030764513100342c0c1d244003900161 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 214032526 1250 214031276 214031287
    0x90a05061801020c0106120201090f08120a05091002070312050703051c020f0406030225050a020f0102010623120114010b0d0204050402030403050c0f07181805070b070c050906060a05 80
    0xd0039010307541c4c12020100200722845d55001c2130a54113110180c10303408200901000709800382100d80110036200204020800548000d0440c4070700ea104450140800074203001c0c040d030070f40e00d21040309104200c5500070030040f810350a258450340c8040204005002d401c00000c00005d400400b603452882c480358a690070f64201008140181c8142d81d842c890b0440300140120309190181d0140940881e40e0301c43e8800c0c403401c4501004c08290302040a06940d1203c0c402030014079000c9540360401c9010b00c000305c2d40c20760315039074400600718510118101602100740c0f103946041070405900890045030080c4001c4940c0501100149018000c1c00303907000700082c1031020500b1030b4040358001d24000c1d204554a24080c10002c0564000c9240b8502c5802860a0b01e4403010002a90909581526110f1180d0f4081154068000e01087d0104d42040440300b41d001c010070000d214440040200040300d65503002640b404a002c440e031508014443c0043c03034240701490b166003050702c9a003007081c20a9540c0340c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 214033776 1250 214032526 214032571
    0xc0e0a030f0f050106030c0e06010c0305041e0509090f0c06040e010b0705150f150a03030e060d0605060406050a080a0e0703170c01290d0206030a02071707060212090a0506 75
    0x4000c0310340183c0700d5030174403000104001070603061000302d52403150f000840e5181c107001160f002d10705540113000180300317020501001c5084c1100c4201710921142a10100741c4d41c2c40486d402d008100c1e41d040d42900150551f081d008400d1003060340ea0b038400c070388886c9042d00b01400300d001d01c8418000c0b03102e48600852031174100038041140c0103039140d00303c1000e4050314120b001052600e901721100520400010403014140c241400e8186c10760380d040d121000c0710303080b1405000040d085a11100c941036101d10b0b00043c01d8075044010b001804440d50f9039543e40d1000f1802622a01001d0240c1031214030f003585010054402268210030380c0c0e805040d00408048080d088100342c000d803030108090394603062403500080c400300301c0304901986250b1141a080140d0b4200a0792100100b80030f50020700400c0000ca52549981c000c040047c1310f00d1000643d240c0302d6420748501d0700410f2080325140e41c00136203400c1d85c0d044c41400591100d82c2d0360080c24054026501c8540704c2c44084c10301e4a04981d600e1039140c95 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 214035026 1250 214033776 214033793
    0x7030513050f0601050a091a120c0604090f110a0e01030209010e04050f070306080c090114060f070309030218041212180515090d140a1b0b04060c0e0a030f 68
    0x99400c1401c0310000002e40e14400d4541d4400c1c4241352049685220001d0440c0c902c0c060f0000040002d8842c02c0c08205980901405640743c0c00907807668002d09128030200c9d40d03141c020704080c0050741c0b40080c040d00780c401ea8100715001c1802d005040307881440400e4076242c0c4070780e8259001c4828a0050313100d500702c10058406142c0d4000150f80103041504109842d150519414490f004a03941802223541e9050300316214120154a85c0d007000103100107000031500e81d02505100c0b0b402a0003680307000d6207000103054a070000e21044000486001081055160088030390740d040802c401502c406040039600c1c0116005091080e03c280507400395802c844034515071107942900c0c1610420a804142e9150482d21001c500b0318034080c14014002158402c0000912104a041642c94002050380420307412141604000920410441070042c8102203001500c00313140c446d44903014204842c2014038050090741c4c44840d080d42042000b21303807140155613013201d0707a084a800c07400745030300c100060414403103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 214036276 1250 214035026 214035061
    0xa0311070804031202160f030803090f010e0f1c09030201031a0301050106020c0319020109050114040b0a0306080d08040305160f0f0b09160605030a0203070e1504050f0402070b070305 80
    0x700400d00000744071a901d04000110713410760994910191603540081c0f0303000e007030080c072044140c180c20500004031098025030f00290b000301114031000701040d01a00b982e00105403640145c000c901e00d22501d02c41041083c0c2c80007207001c240c030143c10741681c009112001e00e10000e41050307261101e14140401e84000c40040c220058000d024a40e101c0304060f50321a03c02003454068860110404020500d501c4620b1080390b05940700c100451609004640c01a1040d00c0c031070f9082010000021600c0d1520000c240b034036103945000c1469843c2800e15030815071503d112105010a060410000076071003012113102042020501c09005441c0c2030a2660340f071881d80042a80c0d50008120f424024020002d07071190340c08a003114045c03040c0c9521500b19103164410300d000b06005001087c2c401e41c664005e1544400e041c40c200c2d03106521040041e00c0b48886204018107c18000740610403401d103e181409000c005440540c0b42c80e400c1e40e1007551095004011404040c0d651000c1110031402e00b18424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 214037526 1250 214036276 214036283
    0x20904090b1f08060f04080f121f080c03070611030d2310030f030c02010e030a0c23061903090f0c0f050d050c01030b1306060504080c01140a031107 65
    0x900c907140030740b1254211010b140e210140010960400100c3c42400a2910701c600314a648150040d141e5a40d00040e50308014280a4040400d014200341c480108c40c215102d115520064143d04d0a0201f846c02d00080c107070440100ca070003100004105450020b119411601140f0b04062180411441903085000c0c800c4020170103403c2c00d0018041d03c10105000c040030060340303402d0701d039501c030348844903906040c41c88018070b0807003c248070402080c040c401c864081401814400e903003803034950001e410007510003002c883d9988221028056080424809400f5112270300788103040d05030369800500305000b9561901c102490301c500f0002c440d44250040d10425030301106079061070720a403509807405103103030158008640c2103000c006081d2900304410070410760010040c00c00750030305400440140004190361508007031903044a65090b211441030000030142d55550b01d40722410701c4080c0d810b00041c40d00c0641009240c0390b0501d01c1c0d0301d580045a286400c1410000b0340b6000040e0100c3c2e240c020500040d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 214038776 1250 214037526 214037543
    0x50904170d0f0209100203040302090a020313061d0705010e0102030706021e0313060f0605061c0b060a050403030201140606030f07140a030c0305130b06040b1203071101090b0a080a02090409 83
    0x5002041d4a030013402041c0021280043c1c0c0c5005514126664041c92101035408121080460342451980d1700a58000c1c042c60300b40c0c8004a4107071555004c0e1107a40050544201121041e0400444203012081c0545001d1900045c072403101e0000035507a0103540000b5192650020745517910103880725100c5410403020308425200c0c41c00c40741c80d4420076202182584d42605204520f0140c1a080c49010180c07080201003a042628480c00c1092205012141c1400c0300e03541c41030007050342e07120400b0f0300400020b80e4070340350381e079045140003800d481d00380724170b98020050041444030a40da05400c0c0e80c0e1060007500c1b40d4640c0c3d62212002c030b4100c02d00d0391103043d125100041d6101003603410303007240785080190344007072209403910041c11f0400141380c00d01030103001c41000440e0703491601e07130040498100000c00c40740440300b01c00c102d02d0850380104c10807110081152070404082d600310a5402c010850a10418201030154202411440c3d006000500d5642c3c006209511903071070f07500040b000c0c1e0b0800d508 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 214040026 1250 214038776 214038791
    0x9010606270e1315021e090621012c2a0403060203010311190504050c0d02030f01030c15050a0e12010c02011418032a030f0904050709050904170d 64
    0x40070f030348848409552500da103462181c11a00b1500032140100424010000000401030490805820030160540c0c05201004015520000c0d109140f0143c003082413030502551522594128801c0350402c84051056200b24402900791103070703590380d4452030708072030700308d824402000b90b601209040306081480c01d4080b6011052103581d40c0070b94140c86c403a0380300002414103c02005003e04007054080704894109000f4006414990001c0e44c0011103141141e0170200d00c29100b200743e07041103a070069140541c20042040c00340200c003801c010010b000700d1440c4030941e00e40007000c510422100744107000340d22500d00304507102c1340c2001f180c925041000f0400d060302d40c60024060941c581c1e03103010b180d988102148095118948442c08652120011407030b2000407190000280c0310305010b10080c2a18015501460b50140000e181000e40b10200e156560b02c07000803c42214005008441000000704040c800c603207a10030116001a081707003524418055007020344081d4460140030440a41c00c0284 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 214041276 1250 214040026 214040041
    0x504020d0b060a02010b090a0e06071409100e031b01091202010215040807060b010219200307030b0a05010b04030f02040b0f040f0606020c0301050c1b16030c0e09010606270e 76
    0x118102d01b4008940e00c000640f184002d401c1644c0c2c1344007010713042d500b1480203d01c006006640b010182146890003908000220001030002503010b924080802ea0711043c0c07801138a401c0c0408a0612290030544808215090008020021900440c48062840b00d090400e42e8000c101d8000d4650b103018048030036143c03038600030000e9000f00b00c04030b44050030402401c2066001080d07500071130f43c5140c03044040c4882c60302d8400e42100c0d0881c44100d40e8000c0f20000313003592000d11081c03000d58001d819044280c140180c1c0142101d2059205a0101c0c00512050000580711415040310030380480c0c020070711b00318860004110a502405055005182120241601d0701c5500200203e0b90302e41c00340e0b1403a410702d900b45070a03154210b41e44001201c04105288070010403103039042281c80358004848014508811300e00840240350802d860700114003004001640d40c1400180e0b0152410000388a0103284c280003404283d8010700d080708035a0042e803201d078007489804003480180030b81e0045105504001d007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 214042526 1250 214041276 214041281
    0x30b0306040311010b010801050913170a050a021207030e1513030b010612020909041b1208040e011202010e0105090609060f0a080916180f0e0f0706020a0c0504020d0b060a0201 77
    0x1040c54100e0f500b0240c50500359805841f050781214406081c80c0995642e000f010ba249004090f012168281c400361110303d0710301844080e040058541d1265552117100e0311010307160482d00110400001010407440001030380c8140e20041065003544d0f2295081e9429610030305500890211a40d0320046510000c1800300425009040300c02c81e8441c0034046640d401008260302c40d050f5015040501034011400003440c2840e0015001c66008840302c195441d8200c0c441804000042520315250114061000140b0301982c0d6004154083c1d012048046590003e8540d984000d0018103100000c80c42d5040390b00c804044814511004002d555254031085480a03070340c00c10000d139000034803010001020028001204100c580b07c00c283c42404520300100e808604569002c00c1c4010f80c1c80c0c3c45481044941d5000321407054081c80c010b0000c510b03c01e40103e10741800340d03120348110b5000ca404100468507000c681021395a0580703000d603540e000c4440440c05407110013030a5400250024802c3d08055042d03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 214043776 1250 214042526 214042547
    0x6160302030c0c0d0c14070b030105060c0304030b040b070e0105120718050d0521090a0b0a0c060c020606010210050705040504020706020c0708150c040b0319060906080706030501290a030b03060403 86
    0x84a002003586500340c0020b030741f100303e4040c0c1c11000004100600c114500a0060030b402c00c034100440c4d2810f41c9039500c3c4e40815200340ca040b00c584544100b4001069006090600000d50a05c0c1079410f100d032034000d400640e01301a16150521913284ca0310170074070800680110182c07002600c05100b0f41e545107801c0d03956000502030211403110096030508006162400c030740128400502030320a0350300b42007030404690301c002c0404040c070021070404000501a4040ca240108241d005081c0b1460083c0002e400c200721103540007030003450081006045600300c401d441c1070f51070907200180c40b0b1840e80b5001000f441803191002d4a4410410001900d580c0000c4402e0311a07400d480310652500d030807140011900903030041c0f290081c410701c0041c0504051000c03403000d070000c002001c0b60540d95048920100c6016800c000003a401a071001e11216405020340c07401485001034010480b50f00009200d07840108481002c42900c00041d00740da500c4c401d401658141200606440460400e4130b006450180782 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 214045026 1250 214043776 214043783
    0x81801060b0c0f0c0915280b040504051f091503051e0d3f1406010e030a050a02010e010203040b030703021306080906190e060a0b090906160302030c0c0d0c 68
    0x3001c0c0c4021301070600700d103c0d9001d5070000000e070501807010001c200091105030a40800b007516001c80d40301c0c00d10464485d400034505511011340d11403c250500c07040e42d50007040318a0b81803081200c44806501070103410102c6801c020002044100030f91943ca82070090342c40640a0312803540540c1d00302e00f10110100c3c0071403401c4101d40300003154900903583d40c2d5100038600e03c0e803888040d032a4991000c155110209018a1200c01c2050b17291078600070445500f460b5085103c94600c08000c66560001d4a42401642c110010700b40c0703501c07503603d01c1d40ea10b100e1000281004540d00c01040c90380d00820070743c2d010b4480c045621b034903890700500040c02900001416202c06c80c250b03030700040300c0d80a104850f00501580010341700030f903604901411509a51201c4078512650f0b0250351b400340d00c00303000300341c0901d000140200300600d001c0208040c2c500c0103045501190048018131158000d00d500c034106240341d41c1005a201d5540315000c082e54016991009280c0c06040c1708021001e5000c21400d086510 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 214046276 1250 214045026 214045033
    0x70501020901030e3c010e010504020f0d0807080f1204030806010906030c02250b0c07170f0303070305040602130b0306010f020601150c0804210c050d03081801060b0c0f 74
    0x3084070031165150341480e4640d035040303250044042031842103505c403a04550000303e401c40c2c0c400000402801c50749541d90351002c0c1c1c2d40d5141840304500e00301c201000300768011034650000e26103988450290340300d0014006e040c118009140e204442d550429650440c100a10010035882c060030050310504088840f540010001400480c5444c000e1140203076122a41e4020440d2290085145001160b162401a10034032070080000e41540c1e00b2000b82600c14551020309541032822038010394010030180440440d401103d0440030311709000061300c0c1d02081c9440d011420340c4071418108001d00c100c46030405c501c40e58410104208280f40c00079030042c02c0a07a50810012603801e000c070385500081c0911038603800100e030f410064038802d109005c40c00c1d01400c04949415074034151030000340d1001b440c03102d0044100168005002e0f220100c840140400d544031890301d40c0d030380d17001820035130010550000c00c0d024811550b900542503100d40e011300302460109551b40c840d400000e07a1101501c480a6941c031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 214047526 1250 214046276 214046291
    0xb0405010e04030912030503061c02120c1201020f0304122601030209070c0b011701021b2d0303010509190f020910181514030a0f050c071a070e0607050102090103 71
    0x480010443d40c519003507650141075442708010401070b525484111205125195480030141c1e80d40219032090102d00e000401007910480c0c14000c0496481d00c1c0f44400382d105101c0d08030a0500d140459030700030352050310403081d50b418aa050b50452a07554403a04103100241468406003800601c07076060340d000b11102c042540c0c4072442100c4004403400e00500200701040100090100f203202c035000700102400260070071342d050300ca26401142c40d01e2203140c1175012050b2180c3c0380910071041c1045225840559003c4000300c10826030701d220622500d80a03542440c006800840f82d5510307680240c1c01d0600c280304100310101030034060b400681201b0b1141c144040c001c64404e0003100031400c8070003071080c1c403c07100c0d1401c09840520701e10301d620702c41807111910203e1100d00902c00110300c5200c25101c0064000d06011518007100e400800f0b079500d0300030412030b00c800301d1046541a26100426000103009a4841404554010030346d0350040d000903020071900c04212064001c0d00b0854020307a410070681 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 214048776 1250 214047526 214047539
    0xb150a0512010b03271509060403080c030f0106080705040b0a0309140705090a0b010302070f0f0b0703020c031801020c0307061d0102010506130c02120a0201090b090303060a09020c010b0405010e040309 88
    0x144010781d001004450507076109065085c4420f200e50180302000d007600c040201d810741d45120a80100e8000800b81c01c440100030405411510654101c0e82565130141186808500314400e240180903940c14001c11500017441c0a214204442c054251144801d4444ad55038101402800d03181d001122501001600f80107507400001c0c1e000304449006011029940f6115040001004180c4140e07041540811214001c1811141200388051080080c180d2140b810704206010385005090b900800d40100813094000c10700009480c00c00350745d048040641c041510040c1d151994030b41754590540190180000d09580000310203c151640c01d620300802d001e940300480c201c2c2c800321380f01d940c00003507284603100e50758945e406a40138080c5401103444003100c061225400381c01c02d40048005139166501d040400000700c8000d0f40000d074010003581035003414000180c5a60907402600521680403450201c903040035007001c104c410700600200140c0d6111401c01040000840d015004074501403c001940c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 214050026 1250 214048776 214048799
    0x12061406041505040921090602010507020106051e0a090f0b0a050f22020c01050c0309010c0f08010612020d02070c050a0b03070e06070f0b09070f1a07060b150a051201 73
    0x801d4800c40502c0058109020007004102c04007003500d62410381c080c20700d4010490782042e4601c401a48170051400d00d407141c02401d6800c000c04480071a41829020080780e01c0e0142d60380e1010300c03401d007054a280260130200e02032484660021400c00d0400742000b0200c542e03680a6501d00740d095500ca6110303516041440501070089501582240e86104011309091002085d00343c805540d4001619007082c1c03103425404d50300b05450700f040600c400000c0c0a074a090910a17a09100c20720b0804802011100c40060310451051084409008500b0705000e91550544c1c101d0300c1c100c0e151001103403078074090f050400001c200e80c01418010b2001801c003244c1c001000054a1090005a40303003645549076105010503500710742401ca035100c85860030700d030001d4444010f00e480764244000800100786400201030150002c0d9020400803820700d0101c031035000c104000c4031001a0448004601c0300c030450007140c0301c100c03058070079494403601003000e00005a1140081c0a40c10501c4038076a55a62a02d40d600c92 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 214051276 1250 214050026 214050041
    0x1009150507031b02071d04050a0501020307030c031803090e06030708011104060206100b0403020d0c12061e23041e0b01090506060c100509030f04030b18060403020a1b1206140604 78
    0x54030000139000030721b581c00d080d01503980644a5002d9440d0101d09907612400d82c2c20a40d10380e00425265401d101c10241c1c18451100c603880d4160207500e184240e0345019104880764050f1801c807107a440002061902c041080b0002445000001c2008050500d0034000580160284c0d40040c081c6101054944940ba900001525008a4103074901407440c0c0c20094803001030710003250006002c880001c0e21032103a810038140503006150204141030710210745540110312020f007840852900318900c0c0c080c400c0040701080e82c45c0010b070a10954803617003400c801d001c140c0080c1040d44803006200004225000c0c01280c121040e06400b40190b0b107903070040260740d0040309100b148542c84011041e2035141c40b508515000ba80400690740f070b05900002c0300120707034826003003035464400203818481d064414440c401101e803460310183c145810643d03002921140c000030090441140c06016002081400110200070642c1010015a148841c58504064030150380000d04840402c07002803c0f504145c002e440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 214052526 1250 214051276 214051289
    0x3040e15030a0209070513090f05100504052a07080f0714150708100f060309020307080303060604031205162d02060f0f0405181f081009150507031b0207 67
    0x4c20395078410340100d5642e048100010820f0b10072090000c0c2d81c07072941c803801c6c895010158002c81c60b49021206c018200d4200e40c449c4d406a2f15240810080c1c4500c20300307881151190a001c04402c0040c140080200d010711f40b800340c20002e002071541c80c0e98600308000c0100a03c03c000e224500c84032980816183c200014802c0a80130f40c0500190405114002030380e4402d0b600511006525158101040805050341003800400d0b640c0d00d41740300354038042200700010031130180110710f185820000f1501d940507074800100790320108100889900d024406823411050503444484000409040c10552501100c904800c1000c0300c00c51b410010310310803031600000c0e8000d02424035000c8441601c0105500000d8001e0b0340b440140b00c049540d946a0720740d03c0507002c11844240360b03420850030aa0001102c00c0440311070700014041004591001310720000e8014031600f00090101d881c0c00c00010508501e80304e42e02e002d01c1c01c0104290300750180e124400500c0700c0e5a010300070304807020b02030340d03150003601600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 214053776 1250 214052526 214052539
    0x9070602060109020307020a0b150a14060d0b060705100b090a0903080601050c010e060f090d0c0c090911040e0a0c0803070c0512030910050d0b010e09161103040e15030a02 75
    0x14043c8011a030020354024140d803044400307210030b0351959031264405030ba01c2154584c0e161070b190303020700c0c140011401030868480421541510400010185e206250042c20120b4446d002403449035a20426280b41c1d50f0441d044c1c810343c1d105600240010a020701c4282e204041400101c2d0700d03061144079451040d82c0c152500c0300f45890b008010b540315000850240c042d50341321800c40000002c02e2214170300a41c080d0380c841429040a8581d0ba09060341c0401c102e0420000540703050110704030403001da045a0b020140001d0102803800c0c460003805c003228440fa042820000c0d0360464641c00250700515901841c00d1201030307505d940449480303105090001e812494007003802c0c0031910b0045030b0704c01d020340c0c884212031030f00c04944045082c0380750803502c203000b180c0b000c41c0c80c4180c155180560704000742e003440c0443c1030526517800600c411b8400342c8038131202000441c0c1d840b503090055200a0140d0503990132179448a503201390342e1086040458449a03181103240307210506090004503c808641e00a00c1c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 214055026 1250 214053776 214053779
    0x510020708180604120503030a06062102070303020d0603080903060108010c2a120c1a040c06030b01230a120506060403032307030c0209090a0512090d0606060314090706020601 77
    0x1410325034044071102c15803080d020440052100303040c6840d003400701c2c03148000c1c40d02c91400004507400c80380e0741c0c0d00580502a550203840302065882a000d0404101d9410040c2c4a03602810700314001d0140c0500c10240515069004c410710072060054054601c04400b120041e03030701e0701203c074284c0e403464040380041451400c550f910483c0d0442880158400b12000040f440c01c6a10303a1003140600b000d000c0040707440b1074070b20428803022b20412401000c1b9035042d0051400d082ea00c1300c0b4541802d00c90b410070942d44280300a200da00c06d0954a00d03840071604040b038a000811610666a840481108046a10aa03035070185491501034030707200e1310008000504061640d1400c0d9001c500e4142d0040c107600c3d128041c19680810300000d010503d020703603540c11942400e44140000c0140c0030b010788080d603004c000b40d03100140340000d40401c2224241085902c0f82c1c80803000c12118018040b0041c48141400004a62160b145c0d225480046036441c100700d05496100c0f0176521f41460340203c0f401038104200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 214056276 1250 214055026 214055047
    0xc090306090f060604021e0d0603020a2102010e03241608040c0905061513030204050c0c0616090e0916050a0f03120e090709060e0f0306041112030a03090510020708 72
    0x240070620b030303280180088007085a1103112242d1010343c14918949d90b44c071041c425414004100310142540e042d00000404410304400802025418000d04110340081181e96544007401f000c01100009a0482c40c0d00c0c0c030002d07074202209000c8a41407540710004240005c0640f103014482e000d684c00c519021800790410240f0710203403078028800d94000c0c00d4116800072080b00d5400400000d9000040100c101d801c510401094a1000e00040d0440c0020300c003140c4c030000045122500424000e145c4400303000a54019203018035240d02c0620388003590000c11508410104401200c03900c60001040c10541741c008101c40c0248501031002103941c0e1080600000300d605c6552640140141050000101080006107095401b11130703150026a81e0502000000d401001000c044101180d105001ca081c00c00030950b2094020005030010900080e0883d17280c42e00d2031080c140e02c13120400e40355181d040d090701801800d02814125418800d00d0240440250716200351240190f1040542e441c2904011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 214057526 1250 214056276 214056281
    0x360a0516030b1b043c1404090201110a080405030705060301150302030c040302040c0f1805031b0d0f050607080604060605190e1009052404050d05010f050c090306090f060604 76
    0x94080c1c0105000304000303e5021040c1170060070708144422074010111051011981d01ea030709501d002c404499480003800341100c4094080c10114060b51300254040d602c0c001240c08281c50720000613030303028000342c800501075010007c0c019524158111240e555550301444500c4c4030901c81e0003a40a1744100010b8000d1181d0001c503000810f000031a07041c551660002000c442d2205120800310340c40510505525802505250210f02e20380ca8040c4043e2510340860740b1b800c0308034075042036141d080c500d409180d5142404959626000f542c0e203e012482e502d462aa603040a81e84500031880000c0003600038689802003d0030348165666140c10310581c60302055075074603010140000d001c14550494001d8170346000000d10040d031981d881c919549030a0900100889240c0b070510307410306800c88200c00b0b40d211000c480886405a03084003120303005042041c010995402803034581410a07090041c0034026601411b0007031000c405071411911051402c6982e908441d0304080d258000d10b000a0051a140d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 214058776 1250 214057526 214057561
    0x30b0114030708280c03080a08150a05030d030b0102011401150206012106091a070504050f04060b03040206070804180b040c05070506060f13140412020303090303360a0516030b 77
    0x3942045c208a1302c944d64207001f81c000046120000e007007142001101c01c814600c90080d044d09a403001c400e02d04203400700740c84c0c0318201d92407008e0540340c0015071002c0e4404d6000808520900c140314604c0d5840e034a0044e41d03284070b201e207400144601c1001203191040180003480c6ca11840540591440c0f06035558800380c00e0b19042031311f50300040801c100300400346040321441001c40b0b5a9503a916418501040314400f80c80c42040d000324500001406181c480ca8201c0e50170a8048a0032900c1d0aa54603020705144129084207801c007540c0c03161014150b00a4100c03d010349001c641c10b1007603c10510088845004d1355402401590141021070018202052203080040d006086c016100c82c44131014425204c101081600084ca26401c0105001b9050f40c50f203009000c0744080c42c81e50401040b030a54130b020203002100040500100d031038078050038040d180365400c2c09400b102546290b03825802c1e140c0240c40b4099400d030094203039011048020006403001e90b507100c0c0c01c1981507200c1510306212900003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 214060026 1250 214058776 214058783
    0x90b152113020d150c050a020318030a0206071518050a140309190e0c030c03150f1201050711010506100e120f0a060609020405010f030213030b011403070828 69
    0x20540307080150b01d62507108400180100d0070030100701c0c2d0a00c0000c003100e06040841c0200807081c0800010154040200c2d50400f00c0e80b0210803001030b6060000e03091590f2200c0082d84440001170780c9040191042c0550001030309a4000c0100700bc0e008020540c8500c0184024955041041001d00060301044540328444404045904001c1c0120104040000b00400242410251901088410b00c0c41c0d103e1603200f00a191504e0075401c1110b001645408050100109011442c004d800d01b40c940307400061540c14001c0804400100301c1556900802d82541d11500082c04500d000030b100d401405524002c0d100079007000e00c15500700c041101e503030400c00c0101e54050103221800d0b9034848108440d441402c1c3c280050140b400903450280110b0300c05031311091845005000070411390303801a418002d00d1400d8217000d40d81d5882c0c440042002c004640008020074402e0002003070f225216400340d240220194200c03825681c0741c854007035440b8500c194680150030060314048010b1001801011420321 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 214061276 1250 214060026 214060051
    0x807050715090219032901210501230702010b0618040207050105090319080402090117012c0708010203040b1807080105010801050402042d150906090b1521 68
    0x1031070740002d0060740814207203112485241070074814440700c0d10700058022803e60102c84104103040ca80d54060ba070510480c02d01c035400c0c6141c0840c0c8c4200381c54100300c056001c4000c1013401074040c250143d03050703109940143e42040c0340004100500501c40d4011661004140b0390400c458400000503903041050f003250495003d01c4030000203182401214000c6110901554489105d030501c04850400c8229a0b01003010f48024440503854013400c0505541c10b0782360802111404060081c09401c0c80da103a502020035884040c0c40b14220085446800b92855056805640d60755081c1307030907070009035406484e500c0341d000458016680c1440d030640203080442565800e584e80c3c03101608450099118007a10b94507101080300b1444c05200d0b203600300f100d4141d5510240604480f041181c42c000620005d410394400d03050b0f4002800091100c000c1110045c24089152900201005000c1495442e0f0107509607081404030520f046041c0c17044d0030b0303000a41400d009402c03010180811006000b5a48800c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 214062526 1250 214061276 214061291
    0x50723180c04050d1103010b180f0c070b1303080c07110d050c0d05030a09051e010f0e0a0605040305070905190209040603020a090b130e1902120601060804060c0807050715 75
    0x850f1080b00d0034a06009100400710031505c0da082c5030960b60754510b0a44104240100703001003510f00d1100320f801000d200c241c040c0c640d82d484044580f52183d148050540d840d00c0e4100319070220480b92051401d48a030b594400c0c0c40e12680c200c44100d011380d410040158001ca104a0214100840da50b0031040c0074404031410303580c804010840c4040c01e81c4003600c00b03030800a1004030031504410320030014641501c914842048560100741c00000c640000c504000c1000220600302c4d00c20440200008402003403503608650301e80000e8020b512511040f50140120701f80002c44840794400e0714429442c036880c40c600d000c40e10b0354420007540140c40e141d50182e80c540c004000350700e0310010507019003048840010741191220800011510001c240c510080c04c00299201039840424103004041ca01c18216145920b81c1c40010004041d01c00071048510a0030000200b40e50700c2001d8500550244604002031103a5500849034035408079110400729004001b01800101201040500d40710700c403d0019055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 214063776 1250 214062526 214062529
    0xc060c0c0a2304110f04030c140d110603041401020406020a14190210090b03010f050f030f10020c150705070b010f0605070b040317070906020d020105012103050d09050723180c0405 79
    0x150410b03001a100030b80c96201c01d009c205540c1e003036031010080440e820240030391965280003200154111076070041c44040046010840c0384e004454056555400039522951107100c02552169103842c195040c00203120380024505021400850007640d45455080ba9449902071103000b064047c1904c0030000d00c0c4c1c0d000603841082e400514042e00c09a0f101c24000c514000c104564060f1103420070340b183e00300c030605440d0050009421405c005415001503250b05c006a0903d007041240060080ca8103003d8080014280d40b040c000c200c014428008501640d80702d200300030445e0114020300020603010065100071035040c801040c0c0c491f10070714040c1d50202005080719601202a600c030004155824401d0080b20307010b0040d1f2150300d100d0320003002150303d01545603581d5960504c1c04840c612030704031510b09251041d4210b500e0b80300c0206c0b0500821456180c11503076034542d403094551000402080b4861181001c10b141c03581d0000800e81019070b03040c860081d00410004d000c0c4800c0c6d8000700000a0706 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 214065026 1250 214063776 214063807
    0x6080d031e05010909020906030f28060501090903030510080a1b080a051e12160302070506030c03060f120319020118061d280201020c060c0c0a230411 66
    0x103030141a4011608011620500803011f4018103041e00c6a00804822102000c0010711000203e480d4034007148020906e8420901c045413000003c0c14443c281400881c40c440a0b8100c5591030f4400d907130400096940204c062100d0819014004190f0400300b00e61010076107a085408029291a0030b440302c0075a00c0c240c8920740501400211001d807c002c0b1207032115100700e5081c0458440740b1000c0d01c040c0b030114115000507c1425405003c1004080f20b0030240740c4208400c0024040180025649082c1004244201c0e04121401d40c03040d440010f400700d06090201c40e803400074515000840c140080b1540c1011000c1200e4144c0b02150b41e1914840c10718401600d03200c1c0305d0b0780520300024002414690360b28080c141d003a0600c40580c40030032000c50381401b500d00b41c1c071102c1e01e188811a43d0710701480100d040501480e0340581c004400304030f0181c48200801d140340b400004541c06c9181c2551110040d0071012000e082000544601504a155050070303000382c80c1c0c80c0d0007588110f14154003020540c10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 214066276 1250 214065026 214065029
    0x60c090a09021c1a0d0f0501060f0e0118110703030203280905070807050a0b0a0311030c1b0d09090e0a120f11030306060a030f0209210d0306080d031e0501 68
    0x40c0c1030f118010f050f01c81091080e04071240d01d8480c08403044807044081000c0c1800480f000340b4043c55810311030140202940000003800020301034564266880056a01461007030103045005c403440c84000104103020706c0f44100d0111049001401c01c000340c2c80503030094000030303e0302021a05030603490650b2010381c05080e008a009000003c1c000040d4201146007803c3e50700300102a80c01001d061259943c1d0306030440450b0202c18005036038000b1034604801400c0c103c030325034144c110044140505100c1c201d01415400300301200300d8140b0019194070a50320050b49908002140c4017810900c180349880d0000c0c000e11012a04032406a04c040e550200ca1545e105808400100000d443d1440a680710301800b40a0608030011825418440f0008a4900c21080310005050b030311604a80e501ca1703039405880e6114002804214240c0d0341c00d182964042d00030a40100901901100c8101340b030091150750180d81c0c040e070051500c2402e100d0154010303c00c0704480181d01040e05da110f05100c07420b004090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 214067526 1250 214066276 214066297
    0x301090c0e0a11030402031203040305070609050d03140f011712030f01080d050301180507030608060f0103060606050403030203040519170f0c04050f04020d031b061e0b03060c090a0902 81
    0x3500b8a45000c1c1d040469003542001503030b8840c100244030250364001030362860040f1b1601d95595035140c1d440c050b60603200380700000f0452410492004140107001c20140301e4066552800d0040c400816031402095034121020392186508400600c18150701c1c4141000e0a2650012900c01031520034a19070203410880d072508007400f036200144814a428403158445007070340d081050855047c00d0042c07040e24182d540d0544610750b0345001a003024480d0304004010b02510007a01c28906002c5070752080218240030581d0024103000000540521510486003181d4140d0b021b0f42c00d2070300f0074080200128819228403464039100c1030110303642e4018031030426a1280f484c020170455015203000e0713081802400d00681702c2c81c5460108076541146010003503106a040f10a2160402c0a14040e2000c03803903205807020100c00d60406004000320784e032142219012103005000c110340070440060a9440c3d20880320b8050f0807980103c1c1d80d2500c880e0142c0b001c5000213200f0b040b480d40f60203560301284c20841103003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 214068776 1250 214067526 214067549
    0x402130e0103020f01050301060912110d0b04030e03190b2a040e090a0209060402030907090c0309020306010806011d22080304060f0e030a2609150c03010e060f0301090c 74
    0x400c110720341804403440381d22086c2007030f90840d0b142400140c504100c0380300c0d5a00c0340d008c5003100780c100184071442000d140001000380c08a0900f0f41010b074100c03601203600b1004a1800c10080003180380003d41519074610104614001168a5541001c948005003082c0e4100603036038100d0141c1581c40f40640320f003290541410380c8580c0b40846d41001c209024004515a4002c0c0c0001405a11501e2102d98041401d0320090f82e43e40710084580c2ca0020540e201251a9103000c0c28023204641c180c029940d4240218100c030761690304c61007000e071111750030301c01e00c80f90104540341102e90004034400507a116104580540d204c4a100390651030103103400104035841c00f4000200070800041c2d100f44652a003803440100001803028820303507502e100c0c2184640501103e029281183ca107403040c0c00d10200540000c041c102c2c2807014150365940e1408200c0e5421800d46e00000314000100002e403030494400700707800f04103a140c1d04d09004540e912000503540554981220001042a203088034001301b6100166 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 214070026 1250 214068776 214068779
    0x4050409110312030912210a020408161d1f0312200d120621060608030a090603090804050613080d02070e0105040f021b0d0e09160804020402130e01 65
    0x1c00d410106007903040c1901e0f9505000f0710141c207500080a240036140c680c54507984080c40c03000e84004464004007102c840301407504020705c0c048150041c00c11946541e0458030000f04c0d016071803100d030580e809280c980f009a04d04010954070b003c2040c0c2d400002d140380c040200703c00b0f0b14a60781c482410b034005407820b0360005c2101d681c50fa130012020031000c040402c204141001c4a540c243c4620905074800100000380c00070359000c02d440d50000e001001500c12101581d581c4c03d01e09042240c038000142c4000b49091400543e00c1c0c004011112a00201e94484c401c880c280b24043d0002c001074031003500d205d002848046203d844580c000c00b101c0d51383c0011a07034510310b000a00c6203020001c5242d0002c40d08502e03401c200c000300b09028241590000c580c0494410b40a008000c020f00682d82c95881c4c040c05030f03011045064003c03c40c1043c01c0741640e0380c15907030060030092205065059a0a0000803965070f14641d201d0b2190502e0307504240300420261408528002c000000c4c0080e80080f100404100700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 214071276 1250 214070026 214070029
    0x20d0b091501020d03060806040201080907080d021513020109030b07030f02270f01050f0c0a0609030504080c061806180306100f1203050316020a08031017070e1b0405040911 76
    0x80f4242c4d0a43d140c244000d90501310490748514014000a05000c000000300d141c9503020b0010754003910381c6400302d80300c480300400c00031360711028801c91800c500e55090110706141d0419903203200301501a10340084c02d5145030b9840120b041c004020300c0070150340d0b02d01c0b414244801d0000740000188415800c41704924280c4140300040321114180c0706402c2c201c100c04060342c101c000d603801307048090306298541aa0a62550800b0715400005080701d26081c0d030a410150000c010b0019038a880302107508440341c001c280401c5205484da8504245480b462881c01860540000d20300440c050540441c00c08142011910704013040e2861500012024000c0c0100e00c9142100c0004101c900b464041000b46a10050315510000d4007000d00341c68011010841103008100c802c0980340d02003640c60b940c0c900314600c101031100602500750302090388940c10301c4121000804000341e412201d8a4a01c0b601c90601c2042c14130720706850340c80310041c10302c000240d03a076803403281d0482c035806007013500d0b40350810380d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 214072526 1250 214071276 214071283
    0x3080403050f0703021c05010e34060c0b0c1c02090f0d120e030a0b0109020d180203070902030a090510091a040c03110a081905070b04030803040204020d0b09150102 72
    0x35402c2c0e0069114000c10009641d0300a018645000b0704400c3c4a40c50b072180c1050703405000c107146101c080b4801e80007880000b5500420b241200000010504c00044040c01050f6a410143c4a107000098403a482100490400c2c10304030b0708180d40c882041d107041e40c00141c04814181c0051800481175010a00b800d030360600c07802c8001102c00407103403038000f9003a40e80d8596050360b03208031760800c00c8090f01c5140e1254800f0006210f2094101c0f00b0085103603075801010009e5801403c241d0056800c1c2452003400c245010000c042031940107001e4100d1030308240380d51009400c0244090662611008d000340441d0040c030500d0410902c3c1d43c0003294003031060400100e179091141000a208403044100300c0072500c04c5c42c1e130f503040c3c99000340382c5001546a90005280740c000398124804a000d5035a804230050507030320f21014224812000e40341d859a44100c1c640881c095480041d0540504100250041c5055402001c280c0e11114000620b20120740208500c1c140c222039082d015a0340c0c2c1d40c0b1008968040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 214073776 1250 214072526 214072543
    0x3020d140a0609060807030c0e07030207021c170918092e052d060301110a0c0b06062109030d090305040e06030a020609120c03010e0c01081e042a0308040305 69
    0x244004c0a01518540da4040d505d4054451142700f415481c000c11440340c0b04c0e80442e101d05800400e12003040c4900740b00302610307070510441240c1c10340c048444201c03114140c2040d86c654800040c490300d14034543e5140120010310082829045010703801d00c0001c000f05c04006540d104082e0b11102d04410031000c0d03003104840002e00b000c0c5d261520740b02032180582643c64000000f02207202c00945907281e82001ca4003400703084503981c0302010081b8900c4c0105a002c03940d204914084d248210040e1207a0041c015903104010340703d405e0841c503881051708041018040303500005100100c910f4600613036060000c980a07460228006140042c0030070440031a0b1149039008403044014124160103070703001078224480c1080c1d0310702950038120403054444050240344031440340540203000c0d00d00b0a140a40e220b486003181c141c0070074048000708108030010b01c0380700d960203c0d4109000c02d6448940b10025134810012240c0f100d0242400c07901010328290015000035842200b13540d44850440c6861410030018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 214075026 1250 214073776 214073789
    0x21c05060c040e01051f0f0c0807120f030506011e090302040609020319060501090e060607170d0f0501030c0b07080403051c09050f0f13061a030f160f03020d140a060906 74
    0xf0280307000c520804820708404146e94505000f107a203e8012410380f000404450090603000b008034450091014141c55206151820f580c0d941d420001030b00160b0861340282c0e2064005181c480e00d45c1210004500c900d40450010700b42100082d03625800101036400c2d541003262a10740120901c01e1390100c1e407400c8005c00e402150180001c40c14a070000301003003000e00c10020028044000701c3d68544644045070b01d115082101c030884682110009202e65000a580e690828602140c03200d00c40c1c000d22401341603962101c03032490000c0ca080006401a0402c00381a00d07218030400c00007002132000c0000b680072741451a80118542030b59000549440c0e5990f1106c1e0062400d100300710199980e03d960a80c030715008840200340301d0301c03441c0002c00410098000b4108082016032401016030168051032140051101d28241550f42c54420308550ba000300c0d40601150b20605210b85c80341c082e4001e0045502800000510307103181c030140080282e420341d407410301141c0d01c500500c40c000050007820040d060 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 214076276 1250 214075026 214075039
    0x315040522030516081b0705042703030e07030f0507050603040302030901030e0f0a030206040b0619030305030405010b09010314010536030d0204030305040f06080c07021c05060c040e0105 82
    0x158292044005680104001c0c10400d00144041d00c0001d4514508500354000b21101d4403407901c1b0802c01001b04d003d10205a0500c124100000c4501e0702d8050900c2a803c01d0201a0491407404011880718030300030000c90901d070f20b40900c102c881908001d84c200450060a07514400c076680d003401800e040041d00482e00030b280c04c00401003c250004100ca54600c0207190008500941c1d011803400d007102c045c4284114017031160a10b042c10340c0020003e000728081c65400e400764407000304100302080c84d60915040d0604e4900d0401c00329003c0c1d0061f607400350080b0000728401d001840040c0c1c401c0c40903001101c2d4412118030042401d8003d1081c198040042200e54004803400350b0b110072035a041251802d60042840c0900008071030600694001c030310880410340d1102d440386000781040c0c100d4001c880d848814054001b176021700c5081c030300e0301442c01000402d02e8410039400340031500314100401e001400c00c1418150000d0410851148030b503180300e0300305454a09000d2602c141000681c400d80c45101d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 214077526 1250 214076276 214076311
    0x10e030307050706051b0309062211010e0d06050c0c0f1c120207050d08010305100b1c08040306020a0509120d05030f0406020c070e060a06030b030c04020a2703030e0415092003150405 80
    0x2f0403203100c0c10300300d0100b4205070f14940000c0300051003500b6014030003841c00341000c081c0003500c04820060040690050140c60a4455644c1c1d020356480700a403a585181039101800405075014100d0704080c1c180c034003c09807500180c1c2e01c41500d88114000e024001414103001002400002c1c040322400a0781000180000d174138542c0011f0a920b0540c803c00101d504145402d410040004102e50080d98844415901c0f452030010141c007070b400c4000c00d203000303091048020020354000704060740c3c601103640342d6900b59110341c207020483c000c00034011220190300300000c0841030401c2001000420100700305030403510780003007400703c1210355902400525003030034048202c956000c900211401810f42d001a1504210f50080f01c0d200c81c0c61042340058518dc20040201024949070320098a001e612140f81060b4403406000465041011551021401c01d10920512a51f5041400c50701954488504000d00c43d40612802e64400d0310203c146480b05901d0004074101801003552106001c0385410180 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 214078776 1250 214077526 214077533
    0xf080f0f0606130306051b0a020d05030402010306080616120e0303010b0a1b050a06050c030c07200301060b0702100f0f05130312020f010e030307050706051b03090622 73
    0x2010050190311189049000058460300e940094402284040e1200050b90782e807410000000c0c241039038910400503240e00d481c2e40346101802250009171640e0300401c0c844d03405507412100b81c0c10161080703040549072540050503403410420719000344504c0780c11440007109084090300d80394400c01601b100134101004082c0241d0003106a80c1140c84038440607075511851801118a40c02d10b01c0300403070b01f4001c1c00b986018050700081c00740d1030724401c250812244e110801c1c401c020f800116510b06c1a01000c10185001841518549400c00260500e544500c484c000009007542d140381c1090f954280045400b2083d03241010056440500c2da080c00f00c99a0b00e0400003c145c0a600c85510b020b0140005200040c0e50090012900954204008580c548500d040003074807041080d004000e15824036644840e03100e00071040b04c0c042c8040d911443d1816039541d032080040d210003400203540301800b0604184050720440214450b4461401600d400d141c02514442d511407490204054200c1d118000c4001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 214080026 1250 214078776 214078801
    0x519110304140f04020f03011403033f01120303110406051e040306020403030f0e10091e0509040c0510051204020d110409050609071e06030b060415020c010f08 70
    0x98510300e680c550003000788440403c1c0950b0381c820820780c010b0b1001034041c560008800103141079a018101209c9045000f004042c0c0c1d90240a82542000c0304800441f015000303690701c25070301c40d003000e4100d00d240c8200100132103c441d400da002c10001c5600807500000c1550520441c10190b0140c1030250606041c0103005245000b10400801c1c504140ba02034103450105101351401035a10100c00c4d03586030784070b181c010a442c42c81a00500814a0715001603154540b40341102120b59140c1d503a1100300d40303000d0260240301d0003403040341504d50000c2c134080713200d44132601c3d901c1c4074a01400e00f16082605d0001400415034180c640e02042100502005a44100440d40c80d0b81058045071008805c0d42c032400c0480c0b9a200c0207021584c0907180c001940200b103001b2803a14404d07000c010030342c1c402c90391702e203400301d00e40c03a243e42d48018007110700e10140400750103a4085107100c54040d10147c1056145c4280303d020003604505040540d00c8040318000a41c1d222024400b0b040c0b0307901e083c1050f42000c0d01e84401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 214081276 1250 214080026 214080029
    0xa05090f0a0b01020313080102040f0905070e0f0a0806090708150106020d20010207030810061b0f050f07080307110616060e120d0b0306060f010f030b0a0e01060519110304 75
    0x1909882d00022007090f0303c00c0041d50f010100072071407000ea0640e80d0300d51364002d511510402503c062800c50001e4604104d201c1c82d80300d481c168550011021502e4104400715100740c040c0d65004060000210b442c50041100c02d1103803043c440140303030316820185014504201401c0003074003914204014081e069010030342407a90b007241d003003882c11400e8442582120030510a1310140c55840070501109141d030010b4414066002d0040c1c0300c2104e81c50b140c0448844803c3d4003c0d540b0064035400c0040010b01807016000c034603004000b902d8100d000c41e10b04505082c1e10381d00440b07044d0302c0440e403401441903407a000d800160040719545d00c0c0141c040741d0702e05a088a00405800190f460041c52200c58062100c0c00000c6a00120300e44c0d0f82d0840c0107100d00505015030035900903c076013800582141171038070720320303002c1c00050b1a0600c000c01c004800300c026004000e01c4a8214012900004d4800317440070b141406401079898440c0c490300868141d410608525007801300308040502031080c1d800c00402280c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 214082526 1250 214081276 214081291
    0x60903070b03071e1e0305010501091202030a0204020705060f0109050f01060c03020c0306090718020a0504050603041103060c070516030206030c0912030c21120604050403020a06050103030e0a05090f 87
    0xb0346907502e0340800e54440c1042100d05080552400b64124800d50280c0c000d00c03103940142424943c8540140d0403070480704240200b5020849510382403211600da13a15542603684002c00310307800b40c0040e40c04102640c024480449980d4043c105002000c4144000c003400b4010280e02002980b6140c07a0908a20030103105500030b02841c42c54000605109024a155000010341210914104034400507511242d1341b048000d060701d11501010f240c00e9a000316003038401241d84060419052100308002580050400c40300c00d000302c2c16622440d10140300f0fa501c105145482d1544500c11410b0180c140080880d540311100540c1c9410b0006070303200c41c1a01e4010300c07041102a20758170b214000c2445040740303101c0282c1c0fa200c085003a0104040019072594101906821450303155a0b22007e03d0050044000d040001110440000d00504155009551040c081e2045031084181901d44801701e0b0303400c1e0016000120800304100b06820040e1811000b08000d5441d0822460000c0c040e0082c00c20207803031070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 214083776 1250 214082526 214082549
    0x20c0a031103120f0703150f0b21070512180a06020a03150306020406020705061c090f02040906090302010516021b01050403051b01030f02090306060d081c1a06090307 73
    0x40301c40680030410b5a65640c040c041c00d07401070408214219000d6412150307100000d0412401804000d80000700c1006c482d034100c0c805042c2c6d81000d03102032030340d040200300710a00280c48000e03d040744103200c4000d01885a5480d00b40d80c2d100300400b90300c4810f82c000c02c0303510500940d2501c480300603000901d1403507854000c5401a1201440c16045020b402c4240085c246000101c101106000143d80103000701e42c030540031540850307900c1051104a004a140341c4004400260100d84812013a801c0640010300c50480b1642d1a004d560000d0304441027070740141c078125a40d480000c02c0580902c9510303000700b070810042e1005401e881000399651610702e00e00803a40400000f01049074010000d0b80c000d10b91001c1604c00d800c0b410001005a002e0040b41180001d08101c00454031788500d2080302d1f072021000d0040d000f81c1c1d8810081c80070300c0d501c03500d0840c2e00d26400c10080080010034915507034240504e190200f00552100320045c0c40035a9034400c1c0d4803501e002c0003040c145030b40004404003101d00d01003c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 214085026 1250 214083776 214083797
    0xc12030915040801020705030903070504060b0a03200301081501060206130f06020f1207021203040f1b15020f06011d04020d060906090303090b0f09060c070809060c01050f0901020c0a03 81
    0x501c045004a0380421420b6001142d81020000f010020f86000c1310709a084440b095038943c1008151030180c895010f030a041000314000040c425003021007007803140c1100380004051103850f02c00c01c2e4003d07440050b003a007081d4080309010095401030360040c40d1910051042d401d005401c00790812a8020050100503510350060070000c040d01982c4d4a203180c480b00580360100d200344036008540407280c010044c0a00c00070504101004800e072801a6040100c0111110aa5807040d07492400b01d08480380140e00c040d000901c8009507010b8001c41c1b50940e002d82078451810440c1840c10750180c000018110461005450b20301ca1004404d50140d01203c818540060741c4c24454010078003010042c0126040c500e141c414945c040d0450301c141807103007103d170300942e45920030300c0c5e80784809403240781c080d81203e40842c84034030401024004040c058410203152031328071000a1810b500402a809145c0d441d0010040c0c1c0c000300c60086540038034060300a501e06080c10b00400e46514040c0d40080031722514000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 214086276 1250 214085026 214085059
    0x7091a0c0a021008010503070819080901022d0d020109110103150b041410080601360906080d0507030206010e07090e09010902030f0c0f0d030c0503120403020c120309 73
    0x1c1425140c01508020014542c420014481c0b0404d0140600a10032020002514640025001541c1140080204203040681d03a401041d500941c02c042c11480b400c1c3d0b05040c02074081940010340a80303249051704441038030b4142803c2600621111b002e591508000102203008090006944c8a09103000542c0b1103509901c40c1ea80034180e04507180076140400d000c500440d0310a281c190a880c101c40e0800c940b601e40a04803440d5804461450014148450124402e4020441d840060000d6484001401818108440c07070414030740c04545900e44620080007e400b040c44810120516890410720340401c07038902075650701040c0300c1c204d280000c0e5000242402d01c81d000c040c4c0034101c4007030790900d241000184980a0860048103034440e00843e004441c01d402c000a05440d8490003521501d0600a50400c0143c0c0c3c04d407840303041c0d06000180810700300040d0103000602d200c00f00d86804003214146403c00030320f00b0743c046081d2406904d0b11582c40044d80b80001c00d940e0f075030808881c0c0301c0302a1003968 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 214087526 1250 214086276 214086283
    0x30203120a060306050c09060d0506011218020f030f0a1209050d0501020931020f07050a05060f060901061202090a08030a0207090e01050f06060c03130608060907091a0c 74
    0x14080c03002001a801401002031058000c0e90899020711403c0c005a2100d00c40c1c1d40342d901c0703030301840c0e91b00040070465003540c5003083d0401c5500c050141004010f03032242001d4039040d504624480c00f500c00351601400210306c1c0c070b042141c108040a44c01403220818881c1241c1d03442c02e8401c13000e040ca03071035201600700480c4180d5009000d0003002d0042c0e01410b500c0c0c40e18038082d4111070b85551281440c680030040c1c0903c04150040e01c869506450b0070703110b9070886464000e40c06103c085007a17030010400340d0040740c0e0402110601030b1040004240074540340b0a0017544040c0a4056403190b600d9000400c03080d41d04c841da00c0725410f01c15074016541d4030480000380f8600030b650b104032040d010101d044110310b60041031b0b60003241e01102080c40b0155000d1015401c881d02104c00780305902c21a0007144941c04c000300074000640d00381c2c0031245800c04500640c041448203910060000340d102042103103500304018050740040300ca003442084141098402d0b040f400002c2ca601d801c40901080c40d2240e1705040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 214088776 1250 214087526 214087537
    0xb030f132103050403120b1003020f0909040f0b0703050c07021507060e060106090501030b03030304080a0c06050c0a0e0103090506070e010c0b0a1505150406120209101d100912030203 80
    0x1200c0044890a03011002e800760400301c41c00d0f40480d00781104100d8000ca03a005904024800074a03c1c94540301d80402517009400c111050a1080c2c0d05211800c0d541e1582180035004602800c0c0c0068080c05a180c04001900300401000c00c160900301030112009409054844460381159004048080001840789900a8080140c46142840c0c08031510200126486058840540d01c0d56003541d02c0310015004d5440850610345c25138810400203000c2103004c3c0c040c0403000c0c0c3c80e280545541c42c950301c6483c252842556100340d071600c0007030540042034001c4040b16528000303007820701503a0784503203d41c0c0d140d031001000301c018031401700c4102005a2058407074400710f42d404010482c0c281001601c60005100c40380c200041003594200c041458541b5407045c0b9855666240343e54500303400d0800c1103420000300325044480c55000c1c80001c0242c2d4a070040252410400d0303035144403100c01035444000740c1416181c12405204c0643d400483d06034030a6045003900d49001c0d100602074a40d18080b4030350302c41c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 214090026 1250 214088776 214088813
    0x80c01050403030902030f0a0b040b0a060315020306040f06080a020103050910091a09010e0d050c0c09070509042f03100e0108070f080303060915030c0a1706010b030f13 74
    0xc0c40204420180c25904c1a040700e070090b82107444c0080d840c0c0b54260f0b1084540800340a280314040081c0005540c0c0d4541a0301c410000e0000c100305980c0d41e0f4050204034500c410103061900130040040500b010311800641501d036000510405140110582c0c40d040310380b40180c1050389844c0021301c00f2008200d09504143d8a680410401141d410f00031103500741c4000c0d00388280c0303180c0c010800145050168020760203516015041048142d582130754140d10840c422503803406014450304890f0b4410858921030f01840d154580e5905102c0704010454080030100412181c1d1104181f2403648114080b000701004035201070350ba074a510501c4194201c6036440b070a038001c07400001280c41304c0003040c06002c80c0d03907084a01050685031690103441c0d020449a40d60480f4107100000c0813804505102c445a50001d02a58010440000418092402030f0800c4000003250046c007141c0c50070400503030340104580c400c2075095080c0910a115002070103012480d12044040c88042031100c02d10910280420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 214091276 1250 214090026 214090031
    0x115230406170304030606140342010e130305041a0c1605090903090d020f190b0a020705010513090e160e10080604020a031212061d160905040207080c01 67
    0x11009466641c030384c007a00003100c040d81420400a0000d240d400320500e0640014040c140703240019040c0d140345959198201042c0d5201c019034125044410b00741b030550303002c0354840741896052221401000c031340a85028100351114001a0200c0e41c000156802e84001c0800d40740720307a64118949906014401040c50070303010b60ba5803410744841801c04c01080715170541d0b00740425a510740701203499006002105401940c0c844c941001844c0010b098014407500400703c001d1410016105102c1c00c0b0310b50403248441100141d0324101d00d4041082030003c200910f00f040c83c1003050034510f841d040091180c0d0300301d6920303a41c10703c40100003440300c14a074a0f05001401714a907520085004225400d03100500d00c0c00c9080d201180381c42c00410b50a200700e80280149416510316691402004c442c0c83c1d200040025a0441d88042d001600440f001800c016090600c00e0030844c0c0105003030351000e0840002443c070368507800f2810350050684012140708580050301c505082c00c241c0b40c030b403098080400140d40b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 214092526 1250 214091276 214091309
    0x90712090c180c08092805030307080117010911150403020d0f06060e2509170303060a14010917071d0f06120a021908030a110115230406 60
    0x91034280c5440048030400c0e082c04003590900c01513410401c103480c100442e400100b2444c0310b00b22582a90480c90b032024411403d00030890300c03030909580094a288000444840040203411442c0c1141c0d901d441600008100c054115643c4101e40e12898031214090200c448440f48400228003c1d10021500903121401101d0146440e40600380065000c98802c0d141c01400b1403203c1200003018070404442c00052402e40f40b20f09081c00744540d00f100ca504000c3c1d003080c0454641d8140049070b107100c4240c0d00440d113074100315080091003e12504004075803d9580ac01440796a40b00c01c80038200d6010401d00703a52070b4606c012150424001d81c00144208000c651240300488585c001948155030411102c500c50b00c5080030800440c5114042042c00d900c154141e50140c500a0a4515420914400d04503080d43e681c0440303041d50400c1c810440407618002003c12443e000380140f283c40ca082401120f04a41003201115800c20f4140380c4041044180191081549460f8845006001c14440c00b100b040f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 214093776 1250 214092526 214092539
    0x70503070506070306060201060605090108041b0b0a08061e150d0c050712030c0806010e0d14010203070f0e0d06021803070b040f050a0b0d090201200706031a090712090c 74
    0x4080590343e0200003450311200182c81c1d481849110241c1749155211850b003513421004460f044009441511000000d42003c070307071034100c6c00491005061140e1441d44079103440e0b030003510000004014900400103035501d684011080c201c002581c080c1168481c00001d40c44040d0001401910402c45c8080c0c41c3c108080945604000070385540c51080305c03100704d201c61000044040e150f0002042c0041808035001c43c0140d0700030412080901000381c8200071070203490310396080c400f01d03098128200e40d500106012183d6806030390071521009a0814001c551086000704181070209034025150f282d005c101c1484107404840740078840c1c14003c0c01c2351080c68848400078a90b0748180710b08410400140000150390501e004c44400711500e0118a60910000c072840314060a00544124100810b9083d26020304101a42d00c00c00c040d1400001e1069500b000c101034100c50140354200c1c04217515204503125607a64491860f40180541790109580c10b000f8072080103000011401003140d200c0c0040071401 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 214095026 1250 214093776 214093783
    0x309140d02010b1c0510270f020406050913120507140d0305090d02061308040b0307050d050601030219110705030304030807061503050a0f02060d02070807050111180d02060705030705 80
    0xf034411210801c010250280d184070004038501c0003403e80d004410907004900d15036110070481c3c02203106204c0e074205003039000701d100c00344500e04540400d032100c0b21034107605003882440042c040c1036820b240300e810324607520006421407402c010701d5aa200c4031102c0b5850300c594140e40c101c0360302000c00c00c0d140e50030031710007500d8600035500703540002d141100150b202400062003d0700c1c00c0c066009003c0700c2c1c60f0800ca03c010104a4101603441d03060070000080e19080e0b560055120705a203641d5140c40c4d0080841c98016910047c00d40b03030415006002e0f003080020001d602c00e00c40085420034034009507000c160300c2d080a5080d07022070f925000c049400001d11210500400481303204242c2040425581981c14a03056000c0c007018225611a100e104001045080c2d02454107000170009030a01c803a00703400c1d4080e40e000c44000c55150704041070080410000b40280d030744078154404400d082641415000f64601d03640341046200321701c80103000003036488000c00c4440f0385400000b0389544401c54104250f5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 214096276 1250 214095026 214095041
    0xb0702030a030c0914060d09081c0b01090f120c050a080a050c030607140a020c2e020c090c070624060f05030103030914040b040c080703110c0d0309140d0201 69
    0x200f42015018040076202d01640c00c107403803100845240d4582e0341014002207400c00e031560400c842e034404108010075566800382041250310440141c103403003d0034103801640c142040da1030500a03900c505000740480d41d40000c06544520381521301603030480c200140c090b036140e8130650b0080c94003030300485d510b0381c0410b01048041c014401c90701ca201c100c00516a5500d000c903104000200c0030700120319003c841070001c208120791441200e0980c401d4a0014410340903100c09248098101503403290b514098040e808180200e0b8001751042c144504e0100c1c2e0300e480e00030001d084100c00003d104041101075404540d0000c0401e05080c16041d02250581401405010f2003000c00c0021507040c48403881201141d040c1c81d49652907942c228500048010605006001e0951143e151600c005058850303200b903000c412010f9441684a080c114405401c6a09010003a0a04407040000301c07101d000004170740c9101c604501d00040c021800b4200b902c5070b402196207090081c006e1640500d1216070540001a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 214097526 1250 214096276 214096297
    0x315030602130b0708030c09010207090e06060108010602031306030b06070f080714060103082205090a090c06051612021204080d08310503090307030c080c0d0c0308030604090b070203 80
    0x440280c03500c21520070340c020140005c1044400708005000d03c216030001e8041d007001801210030480e1102c150a05903581d81c0184c524683c0510100181984d00c400740c07500408607030010754074100c000d400e070300219040741c01540203141e180d00d10b4001c1511000103c8100940200011007003243c3c0385840e1586600103003068500030304140000d081d100021903014122036214a200d0b20300010751411501c3c901035901d024003600c95a4000151645a0a0b1a6031080f00001c200103006245440c00c0b1848444607040441007000501030300f1640d4011524884d01d44c0c0d000380720225060702a800403480c040f031450420000301c0f0040347c0062a03280001c3c41408000498030344001e9a0b4a80d41468000e0801d2220720300140352150900601000d540c4c1780d100e0040c007074002d403031030066600701003440c00c01603a108491400040070100421401808003e51804084a6000c4c110100f9201e9450804c0140030107044010000041416640c5a600c41005264031941c2d141c0b00c5d10308810045d490b6089841c122 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 214098776 1250 214097526 214097557
    0xb0f030109060b030f04140705060f030f090606031509010605060a050c0106080303190207020d02030f0d1e02060106050a03060801060f0810110a23030901061508090606010503070315030602 83
    0x483d6001c66101541c2c0310300401e12030b129280d569526400030000c0444104041e50080c3c52021030151a54001803001020314500e141c1d403810442c6002a10303200060081503140c120000b4814543d60102c1e40607000042000e10070029160319810358010a4994000d031781c41030000907000075642e00f0001a043da1502c02008102161396560100e407284400c845001000668038110140c0c030030a90302070014540042c2040d0318003c40d6602081c50302c403000b814500301d0750000c54aa41c1e900ea0000462021700600752072202c409c1c0340804042c0d95800180900c5040c00008100419018401c0d0b014000408400c40240a01a911003c0512444250260103840e0040100c80c4410402a0081074480207000c1540d902e090a44a0100c0d0360048035000080c01d544540c602401c1560444007031405a90f803800002500c620b800400741114129007201350601c0380400c20024a914003240c2560f00c0300003030031300b40e980e0b0f601c82030210000c020700c407000700740c00390403070408400c4c00010742c050040d0300912140d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 214100026 1250 214098776 214098779
    0x130611060106051804142a040f030206070302030c060c0408010609060302060a08072a120305190506010c0f05100606020d05030a11071a16020705130b010c050a060f0c0305060d020d0305040b0f03010906 88
    0x101d1640c80f56009827001384c1c0c1c01e00700400042c01c0060007003a080c0e0180c41503e0130850040e400505149080d607800088640220301848001700a10031031005242140c0b013002582e00e1903012404c07030b025030303c503120a00c0700240000f894140202e40d0140140c0003143c1e461844080c1c05218040e40c42c0c441815a0148030048498148500a100783c0c0e014400709003c42000007000102c4a000c0d1000030001810490310342d11140014546070650100c10340b18502030000100000e031040115172950344030504541c806400341c61104c0e00701d003c680d08007582d24030100d40603c41040f03a400303a214502d402800e40944441c1200d842e0258118a80292001c00c40c464201510703c00407a5100b03a1406023941c0145070340010185885268406201e90300181055075070a8201d8940c03a04180a41c0b070b003540e81544580703075407960941c1c61140d1080c02c1c1850900708204c0c1480382c003103801040088802400754002d00d0b208028580079400b41c5004040c00c2030072543e42e010385a041c4a00e03800a1054484103803c2400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 214101276 1250 214100026 214100101
    0x90302190b19021606060509101206020705070b0a0509042421022d01090f0302090901110301082d03120c0f13061106010605180414 58
    0x82031001240c0107402000c0980b20390300701e500500203101805225580c01c00c0b0410b007a102c005808120a030051800040e200e14000c03c0c08800c0c400100305841e142400070080c4408170450704d80b00840b9401000042e10361141746061460714116400c82100940080799071a5400d51000040c00100c1041d901400403030010443c2400c040700303003001d8200c0e11216074130a2040c02031000e42010407805009140c10546015008148054000c8175480181c3c10b20518030f143d1201c104844070f888500a18010350b9052514030040c03004556404003c0c0b040308000c01040d840c84c000d403ca84521440509601c1d035a50b9100c4001e07589600200c124128850003030340200540f820414100500602d801c059854080c10903883c40380844001d1050700011420711000807442c5e000000f902180039040441d82c0961308208003e822820340c09511501ca40c0401c0051100541c000156017aa0003215240030f1803000c03510010340502021009100d60000400400001d102c95998400000a600100c000300032440d96 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 214102526 1250 214101276 214101313
    0x1403070806060607020a030b010603151505070303050903070213021809160e01121e1a0d081e030a2307090b070c180603020a1215050604060e0406090302 67
    0x100e503a150350499030005100d41403103c002d048080c4010700000460340c0366aa41407803010203810001c0000d5455400c5640814105901005840315603010030340b180490b2401061307403003400300013810583c5860100b00c0652042041d5505507500902000f00e004503005c0140088d00070850301d104034111818002c1181c1011400e10340244110506441c840c90700101c2500c2c100400c040c1941001a0480110b10f9081c5511030520440c40048008044013029620603040c1c9550b10608840400400304070b000c2079544801807103040e0b40c406602c13a11980004851074895854410044d09840000304106101c400f592100c038100c23181c06684211a120098400d0105508480490100b508074005100a1620384003038922180304007042e07110036032920a141c28000317418002400310f54642c1d50510440c5401000c07000540340c1c03505500314403462901c400000d5295400ce50205556031710200f4815280ca41000010309000305180f1442d04181c58030500500b44a001980140611025136080390030b0704 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 214103776 1250 214102526 214102529
    0xf0d05091b0109060e1203070f030e04050c0f0d0f061503020408060f01031a090a0606060c03020c0402030c180a050d05070321050301090e01060f120204060b0406021f0207021504140307 81
    0x141d0301c03901d20304400c1080c81b00304d80b05004420f155101c1400040002565958450180c0748079a541c81541d6101400f400207681003d807100c4558031040c07040c0d044010003001a5401c0c522841c00221345110b642e8120002400c1030380120a240011036035030806c254068008004172103242d402c45070917a50392880d140c0414401c3c0002000c40c4003068001c0c50902c01141c9058000711a0420b850544055640d200115952540f1400c04540c01c3c1800340103050301400702500041041d107041d4918640700135203420a1003062014400401d0001c03401e20035031108a24000500000f61620026600504200755148101c0c0720448101c0f402507540f02005030011a1900d40700c00c2507c41d00c1c1143d081ca01d8140141004460700542d0b50b58514002030170380c082d113000780000e0040c1f480c0d490000c80702c0e00602003a180039800210080d102008104000c9900091841360b000800e600407520149515200020303226030031740694085403503a5503020300820040103104866006620b05507069480c810315880324600e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 214105026 1250 214103776 214103789
    0x21b160302010c060b1c03080f070207061d030d0201140108030403030f0f03150e071407050c060c0f0f0d0e040b1509030a06110910090f05060f0d05091b0109 69
    0x18540100010350240300383c00d800c00d12411010034004001408281d19010500b020594480b0f121035030418182c10031516a0010724001c1b000382c0701d10b45040b02a64521042c45000f00f080b540040000c20075800d882ca200d04004010185e4030780b2054168000e01901060f18a1100e2206020000a10803000803c0701e089980c551150481c2c5202c0003400d91340420000d114400341900c9840c200c4448202c962030b50040c20300ba90301c1e5207242c02c1040d07000f00038a0002e500b84112042c10002000441e90007d213000c230019003140e6a40d640c04960050700d00302140c5001d03176500c911400302d0549031a41d02080c03841080361140d460030814108882008290b41402c1c440e19002800000a450404045001030007a13500150858980c0c55044d03032080100d4022101450f001d0700301050f00b694900e0094401014103440b458100700361130502036a491104014461188540800144d13110707009642004d95011030381d441401c219a161074050b854807001032070300c1c2d68045030702281c002e400d641c02050701c40b080d02d03803 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 214106276 1250 214105026 214105063
    0x60304030f0e010c021f120902060d020702010314010f1401050703120b060405060d2003010b0f030405012a03050709151407020a03031d04050c090d03090e0a021b 71
    0x7003030300d000d65206200c603804a040081d07056000015841e00c03581480d154800c81300b080c1080410110040941c030344540c00122040c2071000010250b640d080588442078410080160794442c1d510041e4010002004642d590680b81000010a00c20000180c0221900d004072810310026110044910f840341c180000d01140b6500c2042007502c01a034800009060040c140910741a2140300141c00d5421030001031961031b4650303c114500040c110304019803001080303403443c11035050440c803c146001d8008038a080d50004000030381888001d400c102c201600300c6107244070030aa03985002100c10b55a21044000c2410200031171002031048031907a046981d030062210102d070244000b295010711305038200e52080018000100981c1d0342d03108910043d80300b40ca03074080452040b0030500070481c4180020b84201d14000400c901108468209d500f0500300320f4004041d4a0310346800c0e540c0c240107812814050360824100000303459541e004107410130401d141c010941c01180c07001ca50300c50400703040d620080e8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 214107526 1250 214106276 214106297
    0x605070c0c090c0903080d0c020c030a0314070606050415050f0a050a050d0314030903130f080c01120e010c0e010905090402031c1e09091a180a0b060f040306050606030403 75
    0xc0180c1c0180001c018916013411441c4e0389440303903c11078000d0078042075015034510000226a030100820030319024140d0150119010b130340c50291441800c1174a00b01111000180c490400c865541b00c00040d02c0014000c004824400d00300c42c1c00da890500427540039074000c102c908200e25101c115142280c41c000c140485482c00e04091245420120030110244010005222501c0c0001405948a4144c40f40210746a90758080020988200783d44410302041c141d0006000c10724022580e50f20703400e001c1c2440000500e18100f20750041141c1911010554600015002d009d13910031203040b010701003642c0f5000c81c16100c90401011101c00d8034000c1d40755201e440c0c04806018500440102800030b828030826060106c140d100074a84841990701c0018801c0b10305100075060761080b0200c00821a081201c614564404240d6507110390b4402e58039000100005000300c1610342041d00c044038044c1c04070ba1140c0d0a40d061102b42d4000d8082201c2041c1008009490b904003501035907c01c0307400d9a104400d60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 214108776 1250 214107526 214107539
    0x111804120f020307020402120f0609070f0818060415060506040f090e0f060718150c06090503090a0603060504060504020c06040b0618090a060b01030218010503060303070f050601030605070c0c 84
    0x106078005080640c0030501c038480245c0d4581c4007409840700c15038408451458140e425586101c0e0081550344910310b05424084d9443d44402048a1042141041c4140f0b8a4a01c0c010902008002483e540761054000704804c104554400516001390400180081d90701c030b4003081110700441c01112104402000304000e1001369400c000c3c031a1001800707940240d120303030740c40c80c5c1407820860315400442ca1002c1032840141d100107600b001015204400118031051000041002c84804405070900341c0b9440814280700c400d10407281c1c403010003070500800b0b41d5125005409858544540c034400c0d440c0c1b01d40010981018000c540741081c100000c2c04d565a03565940c5d01801201501e4150080028024250780900300540d1501031407010300107101d5081e01d45051307801c1d07034141d9600742e04060040c810101420600440e645100b5024248940c40c1e9865001192640c09081c03005044560001030300c401748403000c00c3c101c2c140da0154009000f5a076468406881c00ba851440050000c1500c80307040044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 214110026 1250 214108776 214108787
    0x110c0c010c0c0b03090604050f01020909040305030601090803130603060807140105071104060e1f0501200309030a0f0c060201060b090409020f030f2d07030803061c11180412 76
    0x6040c840c61140a2030b9448101d403a110343c000301c0da20109503224409000a0000810106c0a5580100c0003580b608880c6808180c1c00c5e00302070001024404e01002145180c0c0c000c82c0b44101515a0008598940c02d140320704542c1c0d0342c0c1c184207900109181c02c20129070344d18080f80113800d8800d4007c0000e1416041e0700112500c2e0300014096603030201e100038660340c5a8941c0035007001807401c3c2030205141d0528030681c008440100020300e1421002c543c041045036001610b404442240014444411000c440d43e03608500c516045242e0500540d900082008100a0700030400c1c0d0241001c0000c0c01d03154042039080701c400d0b005580000c6002e100407515442c15030450007103030b41f000e0400e01c515a087c0c0040307031030f060310703161404500d4010500c100300900e9040c02600e11031480c4442400072944402e8580d0301c904086c00f001e414403100000280d00c5450b07442100c4a0320074406a45850245107041010b5241c03000400a4803e802d0a644295229a021b501b0343c0241d402089110280d0030042007a0341 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 214111276 1250 214110026 214110047
    0x1902060717240d0804060e040e0c0f0105031e1303180e0109150b0a111014160c05070e100b27040605040603080304050c06120a11040b0304110301110c0c01 68
    0x18480d04a100580004580801400003002103451f0034402e14550b10400068800c20044074165a1100d50091307a2035813003c10600d03460000382011641ca8440c079820202040c2e03515115007c4104420a0181c9010f480b2080d040c07550007a43c403a049181c0803501108180070ba0700c120100705540074010300c07824130030780c0c0b03d4064206003c20032034649079100c104140d00e4000051000100328030a0701d0180603442407290b40d8000307140500420404103080724184004c0005090105010610420303110054001c0e43c040c100260844203c3da900c99030703007090445540044440f50b991403078001d0b00040110034070094503845980301e64180b401c0c12006155000c0342140c0304556a0240c2c842000040f240c50354802c7d40040d40c010030340541e0300e1510703082840c60f2450f0801014000c0300100314000d05d002c010040240c2180100001141c81c41e00000c500e07003035000c1c07508031021503000001071004100d07103400e8a02c3c080209030002d1010483c5800d078000d50b802040c4404d14980c00940710100d166104460404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 214112526 1250 214111276 214111279
    0xf181518060e13110402090d0b04020a050306010e090706030603080a0302030403020717010c0e060301030c030f0302030903100608010e1609111c0c20071a190206071724 74
    0x12a01c1d42da51402d00080b03026941c074058820341851100034001c0840a2071200001568103626003880d10010503407952215401030311002515001c1011565682407031030007070400070700725460382d40c545501e40c0c00307254103440106c1284108100000c42c50300034096030003100c1d08001c00500702000d8820590280d48000d2084007180140c01d40800c1e0103500c01170401d803081c0c00000000d20311802c458045d0000700d000700054401c40050004000040d80d01e00c0d110186c903031124012408403402c0c94141d29600403c3c0f4220381c1070051108009030f80710990f104200f207480c0880240700d5071005444e042c1d2a0303801100100280d504034801401108000c0e0000765084041683d00f030320302440b204081c06524180c420003a0500c1d144c10081d00c8040c0e0040000306242e01c0d0104c80d9816039009143e10356200b845104803101119a41041c55000c140181590b61224400f114100354168101c402501d6a00031203a102c08980040707c40024812140201b80c45401c868820164040e0b01c1081e82001020144209 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 214113776 1250 214112526 214112531
    0x7020409060e01050103240203011802070c0902030c031b0c060a0b0a0f03150b0a1202011407021801210203100911030a0302010e0c010e091504150f181518 68
    0x2e008000074800c903030017140a881c0035444c42d01880f940c440610002c501c1d40e4034241c0103200510003043c2d0702039050030b034055903030005980300f00d68079200110700c5207035000d590344500c0030041081404035040214440c403070360060150540f0311400f0740410b03401002002c440d994404170005a049449901c80c2d164020700909182e66203a8800601c841e580007a041103450b1900c0c510f0b50b980715076140c001d5500d00c08d41103852758200c43c1040085410000c805030080e040007162114010086a5142284c2419030042e1120340315a03240525201800000c0c4103441d240b401410000303070181b4542c00904030699006010b04420810090f0480282440000a035a8036600210880c01c2d0340e800c015003566180b20340c0020aa0404801540d41400c48501c201d90500425980703001c0d9a95943e15000e40c0402e0166440b0f12083c4440c0c04203006040729607880702d0f0b810500c9804500202d4810233001120a051422540303804c0c8214440203071030309108142000e082008091040c00e550801f155607240c03500000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 214115026 1250 214113776 214113791
    0x3030718050d0f0204050f010503030a03020706021b030a080a060f171e15010621051003120e031608060f07020a1b0810051b1b010609141305030702040906 68
    0x44140240810031143c05030610ba071241181824002d04c0d82c45060092016020742c58440400c2d16480740e03468075010550700044000030001c0c0c50381521190705c01c075080718422044041004e030792a0710044404011860b03040004080c500700b40078001c00c2d80c4a1443c105110742c070304852a1441b008581040c01c00e0700501d40308441180071917100b00039483c03501c0c00a01102c4483d441e0100c0c1282d068200c4003c0140c0f1542290b6099400c0490f080300040c20500021188d40d4421190701c080c2c0310344c0005000140703503102d0030000f41e03205010590b207503403c4050711a04003a03000344895079109845603480d11b411500000d151040c0382201c4c254132190030b005039070b000c420590380d48030840c280300841c2e10207184008050000340c408000340c541c200a80901003109080c2102003403960f81070038070502c104000000b0024154421860358800806141e40244645602e98003640d001d00300d000c840c03203919040140040c8114501a00d1000040e42110146180011540900c0007402c40d020302a14050f844000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 214116276 1250 214115026 214115029
    0xb15090312030c27010c030509010c021009090b12070e09030d05010b03180f0a060b0a090203010905090f15040b0601030b1002330f0406060b04171204080303071805 72
    0x21403145040a24280d900c001c2d1100c04130500307043e02030568458240001265050340c01c510550046a05428655191488800100c0c5c1e0b201e40300300020740000c01038105258045c2c1008008054515201c01840341240072428019000c0341c02e440141c1992005104200c01c10302c0210740d58000700c20109603490500682840801d4503001c1c0c0c1300700c0c6d10f10000020001781c41c03031021201d2200e26040003d4404c0060071030f8100c2c1e464402103406010665a8051451141e481011140081050001c159140d6070346135104801020200e03140641800350641500038040c000c1543d2144c00d0b50b401003103030643c0700c03511400b46c0d2600c010140c81c1459034424042c80d00d50350312200071207050301070750052940c01b10030f0f49400b00c5400e0090504030f40f81c8245241c14445a03107841040c1c0e110513105800786080d40d8a08108014103010360210304542000503011072207510b00c40c101d895645e21081107555010600140e03480c58444d0303200750001c41d003090012402c4144540f800d4207104005080d4032940ca0f40301d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 214117526 1250 214116276 214116313
    0x9120714120c0c010e041119032d0c090b0f030703060b190f091503091506150f0903080418090501060909031704030203040302011808120d0509010b150903 68
    0xa000b4510750140e0000d903115a88100d03050101038081e101403081100c00c2001c40c00394090900d03036101404c10310380001d44152203580120600b80e0010304403200112034034560940140c51140c03280c1c40500340140031040c14010005401101d05c0c41c100d051418040003002030080c2c001034a85003c150301c42d000021080300910160030081403117403005c1d00329008984013a2032988000c88072000e2102641080040c0454469900b0300d2912a06010a15620310f1802d9154041c8418615031042c0c5000300108106032541c0444580300c0050303d4803e0b082c1c1614405603140030b00c602c0003c040030300404c000c3c400c24a0460050303c080075074501c0451162103680c3d400b400d40301c4036084224190380e6031340d002c0203055100341c24207800d00b0048200355050a042c2c038025103a225501010f03046c084182115508a4804c84030b031002081c41c202512891168024008090b5125914542c069070900021881c0c44506200b40b20190b180201411035408900c86006a160040201180d150003003084103a000c8290a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 214118776 1250 214117526 214117537
    0x9020306010e1912030908061323070909060506130203091902030a062417070306110c030304050106050108061c0212031c0605040c0f020a06050c16030f0201050912071412 75
    0x36106d213885541840d00743c52908400405007281c1d050580d01ca4004510780c0382d03550560110110303541340798041c0320075914a003859560029880c9442c0025000074040300c0d91005004000486400030308841a03c01081a4007090f9805013103074001d80c00103299103515541c0c1c140c0c82440075041c3c1d800c0c14007940b900c80031603100d80d0a620448840c81007542c1642041031040c005084000d138101c14181c80c01c1031613075645140b400300400150742c03005812185109a4140e4482c01010303421030340d0742e1030649000c60203000c8030f21800d800310700c41e0310100c0c00920700381105400c8100d010410b06030380d00c26a002c01c41e407412604001c0c0c005000820200600c9845d0012003210070010301008201d191038081407101710f490010400042045208070b0051a0342c0c04560030300c0383c503002003011480740c64a03207204505105100e1080032114040004804041d0010082c080b840016002002142e1b5041c003010345955450802c901039602c10060171001542c00400000220203000858411401902c6001c83c280d010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 214120026 1250 214118776 214118783
    0x10527190c121808040e06010e0307121104020f0a03050601140706051b0708041413050a050703140108030d0f02040503010e030d0e031c090201020c0301021c0609020306010e1912 78
    0x50605059075082180514950801c05460f00d034010390158440e24482d01940c019480d0030304620001c030b03107244e115256100c00c940000b030960303809a40d0340d041003408010020040b10120340030703a041081460540300750750604613800141d6240601c0188220020305000786018180000700e0105140d40514002a00010344100c40010352801c100104403400c0d0491610940d00e504100114170024109c24250f40859181c000795440f1081507400081140310704149038400e4620300b408000c1600980c2d0030050040800385c600300050714480900f10101042401a40c0e1540d108000498402e03c6c940c1c4182030048841500500b0182c440e000642564200c001c1c001a170350010030842c1200b5060301c03418140443c400002c52078884500902c01103010304400f2500c00c141d990803001d066900038421115500d100400866451300da0008440c01070108500140308a45006c0c000306600f1150310869014540584075042208881f00400510b10b0140200c3d02c80e60350101b0b00040e41d40201c0c1c0001060304c0c071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 214121276 1250 214120026 214120037
    0x703060f0b010305010812093c100f05030c09060c0f0304060215040201021c0309060c02030a0905061c020c0312010305030d0b01020a150c090503060a060608010527190c 74
    0x100900014140c0c4c2c0107030041481c030381054516148941401044508892003902c7d80c864821034007070300c8800c0480c034201081459440301403007003480c0301d80d00821004100031108031a00a908803000c8a49007107030304442002c19010404540103901c52409002c0c0980c00130702c840e203010402101c06060400b0510f422500390302c04142484810340502c0404001c25600000392114589600000d40d1100b014140d444c000f0444244c0c140000d00c0390b0454120150051428041c0d117180440080d500d03404074120000007001136001180c1454041c0c200c03028400710000d890000d0550302d40f00e800075070080003c800d0310310041010000c54144044400d0085d40103002442c2c43e020420380013400d69156010480c115000000803000040d00103036a140a0130307a0003c005029080110180c68900c0a034118541c50311a680401144003a290082c0c015102540c0d0b07103646690341c03201801000c600d1486e4502c1c0441d07154082804600c0c2043c081940000100078040400b01342102035400c0300c0000d131030a00040c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 214122526 1250 214121276 214121291
    0x12040306060f120b010308030a230702120f0f090102031306090e180303040611090a0b04050301060b0c0307170403080304060b0a17190f1b0e0105060702011409030703060f 75
    0x1400c0d01100c0c1c0c020409840300d01035031409a500c4c2240c0880c1400001e0640700e010004c10b44070400b0340d02100d030048007001441d24032142c3c110070a180f00340490303d65005104000807074012003640d90a440348000410041401d08031003503042401e640007990780e14118403092200e46801c1c1c0659030600c00601658541c1c5030441c0c200020f283c0c42c42d400401900d80410980c05003096a1000800c49600a03000500000c8460490f20841010720070584803a920458005002c11b070080c0141c02001110303002c4008024244c1c1d00c05140307a9500402000c015150400e00c00c0034041654042480c03419503013843d20703500d043c3d2640d43e01c0b012904103a5085e1582c513541c050192981c244520b0920140221008000f50381134040a02c50355004c40c003074881c84030043c1946200c10072070190064113113150b0000c0c0103114039051a400005440c01c500c43e03609244840000003581e4240482100d4161750180d650513003241c90003040c1d881c0d40c1d01c01d48140d50148150740300000810710602c82c03114403a010020125602 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 214123776 1250 214122526 214122539
    0x30912030c03041707060302090a1404090204150602010b0f10080a0f0f020406020d0e0303160203070f0806041505070503040204020315040515010e041112090f0604030804060c0e010909020c1204030606 88
    0x64503000b03802490b08c10455545a5540d42e242d003011242803072100921000c51002040c054148418000d4000d42409046900000c0d8441e07a00d068071666402000101d04010401400e28003800900d504800003290390482c880c410f8554a910019101c40440c001100c260144100c030407844520701c3c09031340810103100c4582d0500c400e0f0490045890142c05050740900000d80303134410150840c00982403416040215281482500c00401c0183d4104600c140d40340c3d8000e48887d0100d604440a9040704c00d018080280e038800d4601070041c940e100b07400c0d0766869091100070750002d070100368101038182c036204456445000b841e00c0f030340c03616802003d4528110009807984e14007426082c800c0b41046c065a41c1151502c081d12141210080d4072400c2e03844400009040c10280a640100342c000e5004000506401c00b010f6806107104080400800d004c030340080301c180181080c1d0311b00083d51503404000388a5140c000e4604241540c00703556440d03000140c4e00c40302e0b038000d03801240c4280c0c4504080102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 214125026 1250 214123776 214123783
    0x40303111c0504122f0c040204030501020417030c06010509180a380402100315030b0402101106060108250228021c03050d050411150a02030912030c030417 68
    0x958460381840e59813200c038881210205000841c1c02c0c0407101140e4840c0c564080c04210603c1201ca01a008666458030bd06107503020758001c1c016816076500d034841d00910028000200c0b0078000020015028a90a010401c8154003018184050041042918904c400000e1042c0c040796403064900842592881c510304d82010054441d00390402110101044244a0030442c154480e504881d00c4e01c009108007004d5005144424002c5078150021002004001d983d800c0c0c103002d54021503610705111210300040344c41245802000c000c44d00000085249035020700c604a4201820340103821388040c0585000c4c001d440c3e030400000c0107a002c01c01440344a15003001c00100703451080717019082460035401040482d440f9400c4e014030069024014001d25115205131642c004004100307110b2400c0504020ba0a182105945440740d0b20005103201c0c0c0803015400c8550307520464001c0c500709040700081280712210000c2c03240150008205400c0c00325070503c0208054141032104038207070100716060918 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 214126276 1250 214125026 214125053
    0x6090601050406020a141c020d0e040605060d0f0f0f0902010306050d030c032109111f0909020903070302060708030f0106050705030417190b0613060b03040303111c0504 74
    0x6014003000140203c640c04201900c80c282c000c00c015400ca50442e8000340b5181c1200d220fa010301205101040c200c40c0c1c003240b929001c010395640c0b21100e500b0001004103ca0041c401d99602c80f004205807044100a40c005402c00c0c104481c00059920815a40038180c680e442c250008030f0381d454203000210b40c0c040c495600504010b690000000199640283c49506005000b60500c080302c8800e44201c41c0a258410282c02d140c4000d200c1001145004900c5081002001d4801da81c81c0404031310400d80100c0801854503d07940301003140d85000c00310720007075010b02489038050080710800300161321924020300d44284600d080035500e162510303198010103c180c120a041160030400440032030301c00820389040d15101215026004c5000f410b181c94907403050780c4030039820040600b84e0140000c3d400303664400c120548041e8500104014288200c404900071841d000d0010300104021038841e03407044072013900007160b007480c2000d86000140011010164509a26112400c100801103940030010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 214127526 1250 214126276 214126279
    0xc101701091d030336011e0515030a11060d1113080601080303061e0316060207090e03120a090c030b1e0c0706051b0a05040f080a051c26060906 63
    0x6046007007168107609003000c800917082003255a20420b00f0030700f0031034110244244e2034000070007502d0504c07900401c0c0d42510705014071200e0301e880700046030203070100121500f52100074040c09081c03042ea99145480700c800c80900d82c003d00207000081c48905d044c85100ca0942c07400d81c0d52070700c2c0c01c2c0f000c40711030505c0c000c1d4000500581048004100c07a20300002074035000729003150407000807103101c0203440c1d14030030124106516104e40040d05013625a500440d109130380c841da090b189031684680020013514911490200c4543c01040f401e00200d86040b00d05400120201300410b1542d160f4960002602950700161030341100c0c03105000550f4500003803918066220a9010320500c5c281020051500070321b42c02030244c5407260006000722140340d149504440451420603200d00ca6201c004009400a014100c070121020300041000d400014131424030a92150050040d540070000002a40050491840c1408803481c40c0030403408265500c2c061803104440d005e00790307103000b00070410400c03005000d05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 214128776 1250 214127526 214127533
    0xc0c050d0e0904030c020d0206030103320c1219030f030f0902060304082107051b0f061f09060603020309010b0901082a060c1e010501080c101701091d 66
    0x50120740c89203140075521130f405060030108503003280007140702c01421240017540001d00100101c1080200b907020b040c2100c101c942401c48603d56443c4045110443c031881503130350f2100c0c0c440310651501d14031041a425208003520b0301361403881024a00406021411404074203050500f0000660611401b58400910f41040c004104990003113407003444003400103000148001410300401a00c80094050103015101c0c141a0340b400f490010295003046840505e0101c0b1002d070b00d18035400000348020303005540009013040340c0319460f42002000c1c0309049c50f203034905c48000004800da100e200b150020b208540f809662881d140604038210b6500c0c44801b8810f42455005010341400020b544450040342c00d003c070040042c0701e4502c08500c0c1d0703280c09142d101c031001038407030720404001c6180f20002c030020901035040c00d040054182a01c40c02d011700d400039400381c8001c103220310b000000c200c502030390703800d082106108691020884c64401d0304041511030b1a03100b080c0907054402c00d6896030823001c4029 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 214130026 1250 214128776 214128797
    0x70c0203060c0a120905011506030501050a060206060312210a091406040f080306150c0d03380a0302030d08180106060e041a09010303080103030806040b011709010204090c0c050d 78
    0x1034000c0080803013001455036a141100c0800c034096100548048102c00358181c001c0e0395240041c080c11090140900034101c6078800100d05000080c541e015040040c003500b010707080e005201203903400c52499680d16102c03910110034080003400640e8010000010040307080c4140b8244115541c408620f201100e0f8049004c02012a515007032074860958002d4404d0351300d883d6400001c01c8100b25071a040d1a08000103901d800424001440c04812990303610207124005503260813200b8002c0c0000c0c0c50054000710f10311007030b024a41c03100412200c100108005140758403500031a140543c01e682c0c990201e0407034800d01200d0f000c0312102c4200541d000c4c00a006460820340020020800254000e00075a12803c0782000c110000d500e010070780300080c1c400249580c1d0390900408180086c03100f50b02003060280131655a06081c0666211404184c40d944002000443c4010200d180141148803d540c240000b00f40c490007030041040745012503540e00c07440005410454104607000c1e20850a001c2c1e015030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 214131276 1250 214130026 214130047
    0x2407030b0a03032001060512101406090c07060603080a0512060f100810080a0302031905070f02060702010e040f0e07090e060c030403020a080301030b0103030e03060c030c0702011106070c0203060c 86
    0x41c4a66185030b480c40c51074030002104d0340f1800b411044c4c02543c0e1090000c5a113080c5040006507100410550030024015240440c4541405c100c003138910542003d0080300040395a08500000c1c01801c2c8078110000f806070380c90319007101e10740201c8040400520001a00200d04243c0303885150096403c0707500c03441c80650b4a000414039550120a001480070100c0020b01041180c0e00355002807088405484c981c0c80c29180c000c1d1070354400c031f0072440040f00113584484d076a482402a82c1042d031348a88440c44c19407054081022a42000208a04000703482c00c25041d152141d00a94413401460310000c200d00500421042c1419523036000044003514012503030180c5c110015405030011742c0d11071044d0362074565090490402ca5113100181120000100001c10070002c43c0c2224100d0740243e030343d030120401d20001c246e1101c8054912000f6142e090003c9100c00729500b00030301405205041001e41028903105150806a0444081010580b0f10800c0410f5040034842c195005030804022890710140c02e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 214132526 1250 214131276 214131287
    0xa0c03030e19081e1c03050103050f0109150203060303090415050307060c020f0f0a150207060f02210d0e15060f0303032401050714060108010e030903030f0c2407030b0a0303 76
    0x1c01581c0e0f9604c121258a100d1400348a0017210303101d8007603005a0030005900142c0941302c00c0c0301c121043d00c500c1d240701ca0040d2042c403a035843c01344e1203a20f0201c1410188100e5002e5023025004950500042108500c1551140b00b04c601c51079429480221041c601000c050030007103594001c1d030501801030b80034001aa260340030741446040442c0c600c88030110300c20101c2c100d607006402101c0640c0416850248183d0001140001c644d0281e460b46158840000701b00d84078074041c4409070502c10307030441a2a24101d900046c002c0c600c1804800075098401c5080240307841a500c0e41c000c1d03212a454180121814004a40a84e001c0c0950055146d0304040030030f0041c0f0700035074600404440c2c00011041d4140c4c820022500010741108107071412019501e145030b00d400d82886443d08941c40e0084448035960f01005881845000034043c5040507141d00384001070340c1c080341c4401454080c2c8041d1102d42101c5446880c48580f06007654100e5181461010301118640310030b032072061189110400c002035201 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 214133776 1250 214132526 214132543
    0xb06070f0b041a0c030405060714071101050c010f090204051503070e0901140106030e060603120901080903070524010e0103080927070c05011506050313050a0c03030e1908 75
    0x1801044694440c1004103120010f02d43c811031164448090100800b54000510300460182094070481d40f110701c015120503000e000c0390102c1109c184041c00c0411000ca032141160403041c185a440c0081035114107084462012680103041e0340d51190b281507060034820a0b80c8081110109816a51042d002a0b03a81046228900048010b100050610002074002c0103c2004503554101c02c0e50710b444014025020514000072244107001c0019203d1400040c1440f0104e4524603051a00540c6401103a50800090004107548410001d000c00514100200442128840c0c0b030300340103452a0f01103602c44c04060380451303401c691000c010720228940004803503c0400071945082c00992150f4441d0b60080c0080c0403084549894007040006500103d100710054451002040400c55003074242d41904c91602070a8001881440002d605c40c140402703140c00790b0b0041c000c49111742d0090391000541c2c011a002180042c004800d08200340c00e184551070b0121425110004d07009051592160345c400d80c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 214135026 1250 214133776 214133783
    0x705010509060d180c05030c090613090c0f0305070509090102070c0504020702010c05010c05031b130302010e1f030903110a021003200301030614060a0e070309080f0703030b040b06070f 81
    0x74044020008560208803514a013102d41c03a03010159081150800d0080d2154078000d01810241c0310035441c203038a036035201c0c2d00000c2402c070b1042c081d00110001030619220488070841c4030000810100c088100a50043d88a00010f010040c00c2c14203000c0c0c20714002c1c00460480e8014005200092400c1409409448092340d00684074051800100c506451000c03001d0500c1d4603040000b54080e80c000003c5125200301032415480858919060b41c1c07900c40c803458404041914901800190302c5455a2030a080008119980c00c0300c021982d07d84010045070554080396840c1c180c3c104264001007200855409000542041072446d008070b00d0081d80a40100d04150340c1c0c0c40038441d8104940784c00401c1d000344102a0ba12903850f80703403480042c108500864049109440018054580f0b01a0b010641349004940d0100d6180d148054014281e29581141c003c502840460340f02075100014040d070b0748c040d5070b010500c840080c09010031641c20804190041c58100140004210700f100400d405551 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 214136276 1250 214135026 214135039
    0x70f080f040504020d0f0b0d0b0a020d1d070602060f0108060f190906090614010f1502031b0c040f0507020a0201201f060803030105010c0f11060c0304090b030705010509 74
    0x100c4100c250261103035801c8250301500c0071503504000708032548030b02c009111640c01044511446010080d81c15440783c802080d06203140002a10952140c025001c2c010011601144a0365031038544280d0f03e081c00d00074101c99101c0071003084001d504100480d041045840301c60615418284040d0300c0e09002005258030800d908085440307591450109601d002640314108104041341c1752017005400301101c240c55180c00c14121461580c529051207049400c2e001202019901e031000044001039495610f000394001401700c2c0070039007030012400b018a1b041d08013403c0400e00d00c40c1044211002c03521002d403414a80404c214129400248400b811602420503941401d2140301000091440b26060302150151040c4c042010181c4090035030316000001081c0700f12a10b402e0301c0c980ea80000d10a0600080341140e21101144611016150a5002d0282c4021482c0c00c0004a2810342c40800028070560000908110344106445104009031048000e46051443e01d0002011401002d100f18070a45 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 214137526 1250 214136276 214136287
    0x7080c04030b1003080d0f0e0114070f05130311030105100302220609060e0717040b0c030c120403050c0f0c0a0603050702031903150605070f14031c050601030b0105070f08 75
    0x10f40036540045600c0104a40e48000c005126005820081d589a8016051032812041503806000e02e84e40786080c0c00001c0c101d561011000c5a000440d040b00d60144681081038140d00c06580031104041c0d402512203080796265032090500f1104010803009103091903006c207200594941c4543e20f148a0328020b5903800300e61300700321880100300305c1d4801d0210910b0000c0002d00d40e0525030425104174000e86806c0151405401806100b002c01c540041441d584603000039030b90340c5140f01039900b200004031110f00700350b4480110016404140c40a9000c10404646205410010000c042101000d00c1c00303464243c140c070300414a030304c1d542e01582c01071640f984006010b00740b0800590360080c0002d43c01c404019003480c0040c0c02041e403086601c40c0c0d0320100d50301207a6140580b0448044680c040c50000003c00280c4503500101604100081d81c0c0c002000308950441040c01110383c0480d035000b000a0038184200090100d4100c0030505040c080180602c1012a002c3c02e00c843c038098100040c5075981d07 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 214138776 1250 214137526 214137541
    0x180109020a1704050c0307120b0a0207060209030f0c0a080a020d0212160f090c030b030a0f020a082d0c01020604030e01032a020105010b031006230705030d0507080c04030b 75
    0xb071a5414104054180c0d501004180180050000e0035608280c054071060703910b43c129a07160501520025040c00c141d1008034541d4080c43e401442c0309401000011b0808101d007001a007444802103103820654090102000c035450501d20041c000e14408008201a600c603901040301d0103a0303040044d214002d41c0d010222241000e00c81c0f801461070600240402545038003a103640380311b0601480103000d213490000d00145000c1c0c410714905034002030042a07400c03000c0d07807041c00200c2c0d44071049070046001140001c020b40100160f186198444005c4100740f001d6401021078000d8140d11b80384541e000700096540c5907001301e14141c000c0d41510b0029000e085031f00069014021901003000803030107404190001d401220403484007049541e000344000c1c0d90b100c3e0034613003d000c10b40c2c44079180e091042d801c014550083c0154000c0a03030345d90503401c3e000c0342100c602c6d445801100c8180c0d0320303400010340b81c03901c8152445826401052420002030301d0400c1c9614049501542c0402044241203c010640d203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 214140026 1250 214138776 214138787
    0x5060a0302040617060937080301060201020702030c04110901080903072010080121060e340303120506041b05040501090f24210911180109020a 63
    0x180d81c001d0800c1c05043d554841d05001400c9100c40f1100b1070080901082107208003081c070854403900c49075401005640e1b440c40c0785190301181c0f104500003040f101110000750185000d103000b012603400058462200380107040c10110560441407081d854021010f00c45440e80040d681a9442032901400b9595640c218624620600d0005041c0e230000f0001d910100c00700001091085a0030b40302e00070840004041034030007100a0049801d41d222034042c0c1c28010102d10030104000e8050380d0041498000221224107100380c191007190702550002403680c440d02d0751030140010140c4150f20100013485d68400602400b80070550100c025110320108049a840d5040b4840701e60241c1c05000c000f04241e4009400b42d40b29215130b902103403e034180003c00d40b092540034000c68028087e0001441404407074510110b4200311a00288010390420300e601060400d600c60035420f8616001800010070700b003d11020322080c9c0194810b00c440c0300ca404540440315500c1d0304440d00d00c540980c4035004550f081c2d07103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 214141276 1250 214140026 214140029
    0x307030507060e0d2a050f1e01020c0909060103021203030c0414130203151e010c0b09011805030406170403021f021e0304060609022110051305060306061f0305060a 72
    0x75049031080d621140d140210f111041403c0c201385c17080c07101699071b01880449a228482c060384103604981076407034110b8085411403500c1c0144140c501241000b00050a610001c3e01d18805542c8210b00500c04c45c14840080718000d04840c1c011411031505240032141ca20076401407906805074000344002da91904c185696031055182e4040d522850407031203e49246030001d40f214400c020304038244103007440000c1400d01c407020603510590301142c00d4841820080000c4d006801c0d540da1800310b011b1501000440c1c0300c80a100340061580d982c540745005215110b008080408420000144400640c00080755035466180540344071165505c5804100240522034114000040d1b82014558441e445001188a98482c41d01040748a4544107008124001e18501843c0290680441112001030055180c0e000d481d00f4010001c064549000c1000407450400c0c5401450700c1e0b41c14401035280601609a00c01c00581d0250f101c4040700d00c05c03040e00f06914040c0011300d50f94001007041354a41c16102c40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 214142526 1250 214141276 214141283
    0x210020c030c0c0402250c080d080709270509071a0c1b0105070206071e080307110c01140f0714030a12060b0a1b0228050307030507060e0d 61
    0x1500d0349051805180c50b5841242e03400036a0060070b420000e00e2516200780d40c00f080c00389030003040d649145506140031079000c410580300d45d5080300b4002115082000420311542203640c5071029402d0540c0003410034100d94004a00c1c0341c15004403800e1150b88200811144240020b010a4039103038000c02e10305040c040e401040100311003008000036104600c00814030325100c0c0f4100c03424507000c0d07402c105101c0c40780905a4001202040b0160140c542200500b030828042c0713142c1c8510842900303010440d096503c0d8201d42c4c694000c000c1040a0b03400403029510f850307021014100e448842c02c0005c00100c4200c0300c4442c07290010034401c101280c88000e0346c800d1a03020280c0561403004a00c1165a0b421803180d9600140b1000200d51100e1141d00843c0100c4511451160402400000c142d46400c0c3d1480d0860b015000c805020003d0307561541d50b2481c03c500d4101c0c4c1801d060810900d1020744201e030300094000d9021403010400990300207520b41c00c803032480c070340380c2e00d501c00300c40008460004212016 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 214143776 1250 214142526 214142531
    0x3080a0606080f060d0611041511030711031507030515010e0f04022101030c0e0c04030c060e01050f03040b0403020c031f15030506180c01090501020604020f010909092f1f0210 77
    0x1244d064a0000400c1664228908020012a1008112407082c081c0031505502d2f042880601c0006407408104119560024191030100e842490150401e01c011240407000a4803001404030152541400d1010007200707284c040110303110f031004074240a0b0340441140c0181c2e0700140420882441c00507001004001800060781940d50303051100b45051a40100c10720720000801040c0d000d0601c41c1100c048079882000601182e141c0b030b00c00d9803405610301c9010f061080800c00901004509402584560301c180103014081c10582030003840e041005112500a90000100a001c2a10300d00c0c1a40d120748401c00101d125480002212040c4000c0d5100510701d110302003c0c429440e0420410040088400c02180c90034103040c0011201d91038184540c5025801500115025041c100c0842d49500018184506800e64500c1c0a004845440e00181c030101200206580503400c00c0d59405a40c28510003618401a80d400001d201415401e0408024171000000b010113036000303000d00c0b2520300044e00704 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 214145026 1250 214143776 214143791
    0x1212070303090b10030209010e04050c0a0303122d203019020d1506030213051e0d05010b0301051005011b03020c040c0c14070303080a0606080f060d06 66
    0x6405040801402c03540c0a5600f00020f90302c92400780000122500181189101e901e002402c03032240401520994250082903040d00e2540c0310000c0e441c00035446070380c607148240d07909201c01086601044024070800110a4100300700c16072181c80c030a558100d110b0000c0c49034640800e810021408460340d507512400480c510303002d9242c90b6204401900c0420000001c07074415032a5040d0440201c42c044001c01e00c1c40841d8007000f1540d4003078130030504044030000f40c41d0740c00400b0001640d21644440b0010741c00040820208000ca031074540100b4080d07640c00b14a082c04400f102e000207981d50400e0088410b41c01079021b0050035001003444e108060020030480c18000864100190382e80205070100d40e103c0d03030100780340031201070700902c25030140e0140250300c41d4841000040c0c0502114901001002e02c00c0e000415141d419200c019907803e001811080d255240140240800406401d889840c0030020411541c1194440b58080614626162240d8500d4000381c4c1c0104039500c0030b050103151a41 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 214146276 1250 214145026 214145033
    0x6050403111204051c020315040501020310050a080a29010e01031103031c050c0702150c010c0203040b0904020f0d1401060305150f0f01032007060c030207030806121207 74
    0x1a035070122040c20281c40203030700c0c1510740540c2d0703103d240300341d90b048517143d000190b1380342c840096805054030040582c0c03540480d018585030068006c0d9070030707900f82e503000045c00b0545203542c100c50001d08040c1d401c029400e1602884680fa052500d1019000502d449055810b00c001185c00c4a0359100794040d2450558640350301c1e07814084240012a4411000948400107180005c2662140c2112120981484100b410004007420b8040c00001264005101100040c0c0e0b6030f0990300c10250740740e1002c94640d1041040107094414100400003950030810042c03001d0070100048981044080d0342c0940d54a945100022252140c250012100c0c5e14184000100320750303500c0440d04880312960b051026489400c0c07204d5110301c00c4180c05a104102070401850307802d00c8901e042d641e1505044c0002c800b603201000e01c050000540c3c11310440d500000b046001c2000c144181d60307101502d450118248a400e58003d01414801b03407809218012882c81e500d2020410484c900d041c20a503c0d5540d00d030942c525 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 214147526 1250 214146276 214146287
    0x21e04090b010815091512010c051207110304060305090c1008091005160e0d080c0f070603020703080105010e030f0f07180506090402130209190914060a05061606050403 74
    0x111298000390450011558480c41400c00c5400d01070005c01c00b41054070342007050f19086c2156201d1582211800c2c41e8035841180a21407400005000c1d1121955175952404002d559603008101400380803920f81407500343c5400205490545545040000c0da079207035074000c280f0f000038054076594454402561400c1580e4414122401070244000700d42c075010100080c1c0c3c0946004440300351100d140b1650004460740704040301c1265901c0a890f10381d078803060351070b01079540e030004a0750384040e80031034141c44c650742041010304002c00d1280750450424606540040c103204062064904100081c9550f84103a078080c400c0700101c0110500b15801c2c101510070503501c81009204d00b1200049070680f03441411040e0291038410360004129020550340d03071703081254044018070700d13184040c0e007070001c410513468649844050450311805040800d181c2209201611908001c900c00440320005114664941701803002c03d64404a644686440303000002c1081c00420401c0030b0989400c10040c8024180c011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 214148776 1250 214147526 214147541
    0xb03031b06060d080a030b0d0f050303180118140c0d0311070602030c120a090e09010912020c010206060121110403032309060d02040b030906060f030a02010909021e0409 74
    0x16810344195070342d41c0b403c1005800b0041c00c0580f43d8201084604c82942c0710b544010542c02c1d00400842d446005070f2983c4402d44800c04048400b940008240b004041e1b00303111083e07004800100034800304041e020721841110240c440100403400c68074400524050611110f424200c000c1c02400b0700002e00c1c01e009003500324814403001c103805540400f141c020f20200890b0700b040807050060603504a07540e40c1041c10f500103034000741000982c2c1ea0204820340f81d02d0100f80203c01c0c20002103203103040360500d1551074041203001001d645c040b800300314060740c001c1041a40030209003018000b0003030b04200441c3c40c0100d80d00450285240000002c0d41c003c05001510660340203540da00204078600d140701c203003203140c3c070100030b102042400300301510328009000b07100403001088007606055440d00c6990351900150303604041a000101048100d0601403004918030307004800406140c841500045c10118039401a03404841c0c0009529028214500e1811027400c1d0062001c0d40d15596201c3d000010b0090 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 214150026 1250 214148776 214148827
    0x5010f15050102030414010201061203030c080109021206010806010e0d030305041214250c080105070311040b090d0c0e01060807080106031b0c06060b03150a0e0702120d0b0303 77
    0x1080c0c51805410303040300d480c805845068004501e00b90900d070040c06446002c4458070704542d21108041515040d000b00503400c2840380c1c4010030962082040078002d11016000f00f000e0701e1050282c0011103a59030303290b98028200303007009402910b81c800101e40c62508003c0040e00520390064070f00401da03042d80130034802da01400000e07203103800005044510407044201c8403c00f210a000d900c0c90400100094450541d040c4504a85100707503550301444294030340d210603c83d0350f41e50300700130b405234242c000d0301e000328200f985482c64103081031246041ca0140c040400d001c1c0440d03411850401c5000000080604040c81e0701c00d44c17541c8c0d1031800070040300089400c000003c8001d0b00005825001c1d0040c500184c1c40780b1900d600c0b1554801c000c840c42080f525041c2c0d819038443e6000910b00c17200c100194010205d08521038401c030010401d004c40c0007000c0c0e00000da2403000c5000c20014035408900012903401c40e601559941050b03880f94400340604e030351103d0341030000056401c000741d40b00450003000c010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 214151276 1250 214150026 214150031
    0x150b06160c050603070206010620010c05040501270b18130228021203191401080f0c0609060c1614010318050a030f020304081902030c030a080409020a0c06020705010f 73
    0x880b0818041a40016101c0c000507038080f400600420303019414404d40c610003103200900c00d40c02d08011074299005442c0e010041880000c040c442542d0100c0c81c041d40a5070a00030285600300049000340000381c5110f031080070a00480c00030806000d01c081c40e10902d20013001911205076441d00070000758454585414204030361210040901c40303850020340208400d4005e40051380c500408180554002000f0042403001560a820783c0c0c84148948144c1406045020261758100101d241c94024a82e200403401d90080881703000c0e0303507560390031152072900a45a69840c3c0360000b15403032400c00d042070810034002d14400080f503603001c0c115070318030101c1c000d0b85d0520448913040c40001c54281c01d084094482d810004c079550100e80a4241e10180c150f051040f40c0c0350669810031740d402c051201404141c43da924042400135071504002522150034103d0181101e401d10340d90340245d622541c4074030243c01e50080b404400b1103004092400030707550002c0056544965a01e8401e00900901d04c004580c41d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 214152526 1250 214151276 214151279
    0x6010e130f020d1121090309010f17070216060201141501050c06150103050a0614090405100c02030403210c110303040b030406050910020a0507080c2e1107030507150b06160c 76
    0xc0d0701d8545c16006040600146142100b0700303004448000350030348183c0a00088000d600400c2d0f000c01c00b4248940d1a07640542203906480c2c220503413010302d951203130342168103050005c3c002142c000082d5411040045440840c1d40e9850010707541402061541c002500940080000c8525200c4250b00d002d54242e0f000c11040e40e5141080041703840601400e4124800034a48038620b003886220349420501802c102c400d8041c0304411042034400d05140d080041c4c2012a041081154400243ca030040c4080045000400803180041134a10788180c040c100f4004a0607240382903d09200f20b402274692005031558a240900348140074140a8442e03034000e124403c1008139405003842501c11011890b42d03018541821620b581c805034001c0d140c1703e00d95000c1c1340040b00a5200050383c0042003403000e104241c4107003a540c0c2c00d5045031244450030701c01c080100009400668010100c90845a1101c131a914040c06070110f20000d0442d0341c01c10740c1112000039005403070070b0507500e1356036801e115080004089 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 214153776 1250 214152526 214152577
    0xf12032a070b0402120d0e04110301030b04021c0506010e1909020a06050706060909050c0a06020604020a05041a03060a02190c020f060313120c020906010e130f020d11 73
    0x2221140000000303002402004002182a40c0294000740002c0c400c005280c950041e69090003402c045c42d4010502140000841742000d0090004203400c4041680c1150b04d107840740101c81c071000300700912866644049080c030080310300c00c076000950490220340d1150303111041001d00d1a02640c08418030350a4154540d41e00010740215890349a010300310f1501203260100a46582d000b003c3c00301c4a45450b64004101c0642a00ca48052603005a0040228100c6007082c0204100550412400c64001000300000b42e1204440345045840550f4001007155001f0308280f250301002d1200747d80750040805202c4881e40c240c01500c000384220107800c82116a81c0400d0722191944080290030034110742c00001107162840156500c02d00e05406e03001c80700700658a44800760b1b40b002c0b2030004901c00b881d150042d400c0944001b42d0041007820110324a0f40250f000071144e41958a20024040d110302e0b5116022a2a0b01680c0f03002d50400c0080c000308125158000c81074101058284021070180c000d41d052 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 214155026 1250 214153776 214153831
    0xb011805100608060a050d0602030a0b061204030c032f011a0d02040b0303091305090616020a060c180b0301031101050301230d0807050a051b0609120f1203 68
    0x2800028002580c8030702d005000da440860042c00700ba4001c400290004464036079804151902d03205060060b90391234000c1000c41101e10b01e15a25000e01d0081c0503c08191600d02011904544c150412200301910b0349402c4812841194103442008482d4401c0c43d50750b90a0195008a1240c80e8000c2c001e1000042d914403034000308401d4140e00c84804288240503081030341c403a0045407405019a440e00c240c1001040409039a1000040e000d0354400c00c21081c1141848015000344404160322420004e90380003d5442403590405001e40351340c0e00020064601452443e006905600300404095079603800d10f81082d00248000d941090701300c0c2d0300c2a0b0941c811300481e07041c3c0d040d1500343c80051003503c61100e04045103054440d04000b052082001080001000d002d41520840c010681402d8500e07102d07042c400d003030b00350a0038028900180b000c00c1e501d4005480c8400010394200404031140b00c011071a285c1001c41080c2e02d40544000074040228240c000c610511441050740d034403508041c48c4900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 214156276 1250 214155026 214155031
    0xc0303200c03190807170d0b0d0201080a02090a05040608031b070303050a0c060b0d06090203010c02060c090402181e0108071107031e120f090b0906030403140d090b011805 75
    0x14590040b6040f00a500d800c80c040000442c0140c103081c2c100406036458000091001d14040c240e418003046180948896005180e840e00e010b582c43c102039400e980c000b8000e1f07070020b440d826a090300810711107050b84410001c40000e120081042c030020b03554a04040d102d62001c000302c405689008444906004000354075011a68155520391501c8a1300f4412161420010000c454503a211410419660b0b921521009114091000060800031920401d0f0856150741c81040541d04070701e00b000245008001a251825816100503a8510442c0c80078541304402c0c440803a48007040394030003c01282000d01c61901c4107030070380783c00f01d540d116041e0544408503c45424000c40d03209040a1001404244011840d4040a1403411003603c00342d4810b44440c01304411200000d5520703052248840d4131121040042c1001c100d114640781c01400450b8030340c80010b0015040c07241c0c80714103010381c0030b41500701c410900340307404204400c40240c500340117850302c2841800228012845000d040c0750302882001d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 214157526 1250 214156276 214156279
    0x615140405030d0f0c0c0e160314060118180509190b04060b1203030702151008070e1302090109090213020c060f04030509040c20010207080a0302070f0c0303200c 71
    0xc075460140d0880c0c2c1080c40000000802170602140000120b00c114600064400040440c0340f600d41200000c442c0d0132116080010141006104400442d2504c0601d0300300c2000c0c40d2801001e002c003185403103210350303540c00464804054100c10300a00c0b4540d01c0540582028000d480808076a42d10f46049a0031450f0050405031080300440d002440c03d501601e4010400b5140c0340362190112929800c5802c06c5403100050380000040a821285c48030400ba80710020307400450300d0074140040305e03a964069005040035440b800c0e0201c1d035090b80c01020348280a9000700804819a103440f005000b420841500b24000e060400c0e480c1d4441c01c2030b0003a078514407504001811640d030381c155007a85142c0b0260003035044c031004102c1442c5036182c0d4003414045c41100d48403000300007015104455000d24889103d002a4414031000000070443c171b0465155410300d180250f16451070b400c02000304142240014801d418410000041542114050151080404802610703056003008152142903403034486 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 214158776 1250 214157526 214157533
    0x510020a0203030703200a0807030f0e03040e09010209040914010b0f0d060f0e030f070212060402091b040902070b1e04080d1a120105180a030203030a02030604020d061514040503 78
    0x1500191080d402480c01b62202506a5420070786140900419440121030380006118801000072094250103042c81c100103100c0e00700510400000226103d001700e01528040e11250004203881d040d094055031040034008204010080e038610b004485c906c2c42500b0a4101d5007015018081441c0c20504079120350405020b442c4564040d65401c4020b1204003111000c03144d44081ca040504410005031041411843c0d8040da00e04a900403c8440d004c044450301036640a0010000162148000c19030001c2c5c9000100c1c7d0000a00c044015450103140c000d40000362001c100001071010f1a501340c0e000e10082020307109581150510003506031800c49014183c40010040c00003151240d90040341005040b4440911b50041c050003e1402152040d00080581d150002d0003512942c4940c4503516079107100c020206400240c0d0003a403240802860511059400302c0060f490380c4650701200c0a901850718200a100e17115010781c1c8801c6c0e54228540d001a00300101c0c0002031102c034003110103481005004 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 214160026 1250 214158776 214158781
    0x70221030f0c0114010611012a0e180405150114210102070204050108070602010b0102030a020606040b220f0c02030f0306040c09030b0403030603050c0105030f0f07110d09030510020a020303 83
    0x812100d42c4203109410680d941d42c0c000c030601d118454201d901801c41603494220741c1c04140c020a00303490009520719040303a500c94500d86110501100701d9448410340c100303003c0901084000440c002003e0030743c4c2c00c0c0259018104001c06c01e01280440c1c10b4078a030988600c81e640c8404602042080001000b42c00c8a441d15180d007c84078584007c062032040c030400585481d20642c04a01038400a900052190b40f10a01c00d1000c281c0a020300b0400c0c0c1428030045040800c0c0b1030000b90b070380c5006403c031070040d56110300e10110703600c1e00c115501178845410020700241c820511410003d04400070720b035074050315080c1003002c0240301204441111070b0702400c0070b041d500d801d000c00c402000b181d10700b9010700c00c18850000006d5403030b8082c40d100e40c0c026200010f5003459420000c2c1007202600c611810044100200100010200e0290360807124101100d11030b5500c0c2001618400d032488070022051154606694843e94003c00503020340e07100b01d0580b52400600204c0c0010790140244c0500542c2082c0300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 214161276 1250 214160026 214160047
    0xe0a020a20150c04050409030e100e060706020307020307080705060402031605010504090f180804140603060d030e010c050106140a120b2d1e09070503190204021201080307022103 78
    0x500a80064100c103d051030280c0d110300040859040c0d410071004151031b01303029801032174108200b0051a081d400d00061520980c1d0001c0d40a110b12500100b85a40c0400030030300c814800c10584000c10340c0054426a106032a0416907a9444212400c91007031080841080e81c1d020103069220490b0010b845d00c0d41040d047c1040c1034043c0c29210609607600369148206c12016800100010780c0724003609007160340341d090091100601e000e180c401402850b0400500c03455844000c00d5100032609840c148100810010040380c1141300000060125802d280c0302240c15081d00744002000801101d80000c0255212425602226500d0b0044c0c07501d081c500006440032000110800900800351000461007586038204a50f1403055924401d1901104a5002100402200f03103410110240007040c0003890000069076541e4001107048003894a9901c01c011502c440d0140c41201d003d5203480300c0356684403c03c2d2030340d036041000241d100303d034008000c01c0c81142c034a03040d0705008007503009140380c98140311 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 214162526 1250 214161276 214161313
    0x1c1b080a020904180c06020d050306010c020411120c1c27080409050c130512060c0d0209040207150b06070b06010503041401020c060115091d040c0e0a020a20 69
    0x80442e0f04a912a0b5800303007001c02a80c1d0118a5600c04c1c444e62100a0a00e9002440d180c4a061341c00305018040050110740d0784c0001c900c07500640e040b140481c01c220f40710645034280c040c2d40c480408001500c401c1c00003054034000a840e030071340000740321000010100009420707a240c2030302540ca005451080d8260500310410345502c5c4034018102c5504e41030b91011b1640813980100e61544074000701084424540140b554000700824045801d0218000040402a00c8080160020304108000034004075900201d40551b0681c01d001801191038a00c1030604030901d010400481d08800d03d04800703030000d40b40040540d0181d641140d4244015038030403005554961020700156088007101c0088a10981e00f400103100708520071000c0c000b6540b4100d40c60170000458014201030016045051004004a071080d2260b1800c10f2080d1450f41c40b039050040390307541180c004004411070142080306440c01a0010715042803103580344000015040c82104520159600072103c03a0030049107401c0c44400e51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 214163776 1250 214162526 214162537
    0x3060308070b0c0f070c05030d0c080d1a0307080f060609010e0708070212030a140106050a14070c0801020a081803030c091012051008060109110a140705031c1b080a02 73
    0x10f22a003464070070b40d10703040c035034507005040c007182c2e180740c1e440c000e11950909201d62040c0ca0101d00304458424602e0b40d601c0c2c00341c01901c003c0550a90741d200c0e8001520503000b50480f2003203018064511941e144c0300c5064681e8a02d80c4c10a002e0b104d40d00c04290310f410503014290498400b486900350ba0340b140e40c4102c1c1c09074400b525190031845802214400313011010015400303050341d0240083c00c00500c4007802100c203c164001010b00c04140541c010450300401d405503005070901106560381d80034501524590010b4208541544c030208042103001d402c044628001c4076101840020f4200c030003004e036907a2101301c0d009041040248003800d00b40c00e000000c1c048284036030030301d943d160103003079640c2d0111603088a8640c2241c21402080205d0303802803000c0303409005003510510502c1241c03d0701108a21038050b10904101c0041000f104642d14002940d071000c0d80402903c3d91084408030004444c03007118210603040e49410002030103200c42500340e03c0320b0101901c48a400d0b40d14144100029040f0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 214165026 1250 214163776 214163791
    0x80f1c14030903091c020f0405040c0501030e0a08040303050a02060a020a0e13090f0606140909060c03090f0d020133090f06030501020c01021902070324110711030d03060308070b 78
    0x1d00046003150f80e0101021000b8203410780d0740e403880320140100701f1507000301a261805039150200b88004540c151850b942a07813420f003804a80501c1e049484e500e004034004001e440c108010401208241d800402052105c1d52503003111f4841c3c8a5907042022441201c034428081034212042c0d84080c24075100f800c0030907000000000d2400119201c0c0700340c450003400d044400e19070b6070409002000c2000c0107482c000340c054500850034906000007603030b01d50300079190000c81c0c41d000c03000403888101044a100030307003082c60aa40c860f11107140040d01030f000c8815038851030084880c04a4610701c04021030341b10344c195110304104941c40d2100c003000a02010640303042c0c1c940ca544000c40420300900041c444070b014100016682e0003008d020209107130303c03020744204540004400300045540290044e04040741c0c0d11044522140c080c50050040c0140940101d54440c080398100601c0202944400100015410f40e250519100030450850b50940002028043c0c240600c00c0850f0649a06c0c079404684d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 214166276 1250 214165026 214165033
    0xc1206011514071a28180c08010b03100e06060d1b030809090604020901050706051909140d0e1005070206160b01080f011103131b080f1c140309 63
    0x11444100d02254840c0d84240c858008220134450008400901190701c03100c1051401408204800903420141c4007041c131803249622180103540e0600b1100b803520348641c1c00401011041c1d0707611203e41c042c0c003966511511a00403071350344a041441c2d0b4000d203c1c0c54010b902c090076086d40c0f00c8040206640500d001500c9810700c0e10303032174241030345e880300c01001946c00799803943e841f4100718003081144a4010056130080c0d00611421743c090b6005000d0310500f591205010907640d9a040b0340b074120f00e41070852002c0d00c90410a100d401d010810040c4440c10120130140d4404a000f140152074441054600039082424181c4100e0254411809403030b42d03a1005054600e40628600c4110700c1280c40d500aa0700b0005000040114240030809242c68198810080c415003c40c168040c10318000144500030810407402204208441d5243d1501420110002030a115440e000255650760180610384500e114180c3c5030349e0407800300d50700104503141d40d0392072240d900c41841040016030005020542c0a10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 214167526 1250 214166276 214166297
    0x30f091009050604090f0b0d02030304030b070c020a090207030e0a051c0f0515090d02120306010e032a1c150e030409050c070b011e030209180a0602030601020c12060115 74
    0x6503140001c4c070082001010110f84882d00103a240e0444420154071840f17400440010001603e000c4191000c80343c001003041000d603144c0c20b00751035080e00000300960000003008007243c0da10a40e4040c0803114003c0c2d42c1c2483c0e00030200140f2103040c1950240361b6000c6d501c2244141c0c000354021154801d40c1c41940017408440d500d981321850841c403a1107091074400d0304800c000111108010341d0b42a03507441d10003044000c4c4000880b0846100140c0400d0400c00d03121803900194804000e400f901400e5203419040017000103242d0300031840b88118151251400d6403400446590240c10302008035000200850280c800c041024010038159816107000d020502c00018200d42c1441000d1042c1800030565035546100d11700010710003c160404010310003c00181045240340130a418192039050300e50403410349901691034407001d06d0840050282c4105030780340003000400e402442c0200e034281c00301c502c101100000c10220038441710000016601c0880100031b441318a5038a031032060038030700b003440c1441d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 214168776 1250 214167526 214167529
    0x60715051f08010903020c0307241e090e06030109020a0905040f0f050d03270311100221090a0201020a03051e031321020c0f030c0d0b1008030f09100905 67
    0x84020703900001c007a0f51355000301014143c05003d01e0f940c0d00743c00c40140512904149030043c942c040e030005c01c0840d20b014400e8400242c000d003d500c0004e130000f0711f0400b1804400c02c0c001c14a01d82801404500d00301007010070351034141401001d0106600402c3d0942942c01c0c00790400050100820a94800b680c904040020503460303150f0309601c50040014280c0001c1c0307190052306503100c0321601d80f440610400c41c1c2c2003000074440c02440859142c50041c0c1c00c0160341403424079003a03411120415003880081d91001c05444030302c06500c1119421420703100c681e0707445d0b078964a030100444068007503000300b1f0f06100044d1240c070041003a030b045210307a00c0c45440400d10464150b00121240007001e000c05090406100380b81040c0ca102600007103c505441c8805a4000c0d02e402542000602410f40310000c030017103035002c0c001e0b6004000054008a010461820702c03402050050350b045030400500710020800080200403074064142c0740c90900c2c03910f02c008050010203c0503c41d101c00f00210f000340401c16 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 214170026 1250 214168776 214168831
    0x40b0a08060d0803090a0611120601050c010e010501060207050a0b120403051e12060102010509010515011112030c121b16151d16030b0f06011808011a06071505 70
    0x1240c170100200042038440c5000c0007147c03280e8000d40d164040500500316100f140d590700d55404002840c0641e01c074654220481e014055002d01942c095090000116016a0014507907045a104507100c0d1790342e0343c0d41c41d125801c900c11200c2005190482c0800900400d0080b4008c100c0480006440b0505581d029850406a04640c0d81030000c2d44c0308100344441036a0901a154000305110000c10680c01c0400850382c0d4919007240c214180301401124040080040c081c4a548a540c056013075a00e180680d40044258018080034498031610303800f0641248841d0404480900c0040c00249040c0c0ea22007445280300c1c8041084550b028a60100c03004841d0342c0c0141041141c2144c1d6003e452003055800c14245500030407400101c098400d001c00c0860110a070380d64008105d0000e41405884410040300c445100303c80d100f00c0d440d12440c00144c038840c150300903180100404403002101341c6007010400c061003000405006400e001c00c004480000350741c4443d8105028070082c0c00c041c00480e001065 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 214171276 1250 214170026 214170031
    0x30e0709020708120108060f01140109030204090506100b04080307020d11030109060504120e1f020a0813061218110118090506100305040b070318061118010302040b0a08060d0803 78
    0x20102400b15940c0100e10708000000e0240a0707600103002d9a2a0486601426290511440c00c01d85170300c1078204ad1590003098504040d43c0c002e00180301e0030031242401c036074400058400601e0394a131080e000400c6040181030307d040ea104d11000e9482c0c1403140d001c0200c1441c01c440b055a40445000e925a842d0b6004d2044049140c414540072036546040e00f848102c21290344d40090a11052000071900f5907200f059800850180c0c800c40c0b0421030030340700200e183c07807070001000302041d1000031039000362416008040704840305995030580c0d50b80307100380030780a5402c2d0880e5001c00d40001200700300002c1200d800081800018501400949804221020f0341c908940c44282401e65410520a690a0090b5a8004c000341800d0900480c2042e42e944100d40f4001080e01081640d10400f115200c4a407a41c0f803126280c00c0030041c004490318103511061540400c182c00806171a4101504a1307500038000d8804503040480e440342050b03802c68064441c003100038001d590000d0840d042c0d9001030740c840080d50 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 214172526 1250 214171276 214171283
    0xe090f0f01030b0c1c0c09090b012f07261f021c0606030e060f010303051608070f080306040b1807110304080304060203070507060905030c120312040302060603150c03010501030e07090207 82
    0x3580b0906c03180241c8840700381d4110101c82424880d11004998018400d040c114100101070000b561f2094041c444100d80c061190f00700340900000004c007100c010710724601c805003070b0201040c000c0c41c162400e071380c0722281a80096196480c520050444005034043c028074000100c60000c60ba040d182c0300d108603030090b0401000701c1e07170f0752034204803038a8200042a488603818891980c00c0d4115200a01540a070700d0b41d60701292003488141d400c0006050541c0c003210350215090360a0f42d114a04611281c0003103480c01d00803840c2815405031480d002c03200242d91030881a955030180c03200b40040301c1d20340d640465807100d44420000001c201e40108003c1004200c1d6501554683c00e45162180c18a40e2641c4a1400c110350500c041c4244d66002c2400c0041071422984020006c42608651b41580607a0140001c5c2074404003c000605802081361442500c01b207066610f2203115080c0c2082440f801d4500300002d01d0188014403695000f640101c00740300d1500211800f280d40d9040f0751003668010710046 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 214173776 1250 214172526 214172531
    0x40501080706021e030304121e05040e0702011a01030e0106080604050f0c190b030a182003010207030824060a09051509060a1d0409030e090f0f01030b0c1c 68
    0x1001259418030071466030140c6407420713031003100d841c041e038503544d02014001a03c1414840c600d80d828501800010001c40c40e040c20035043c2c80302c0300388080e242d600a44a40018801c0d0200081d009602c10f100f0140040b03440c3c580c111100070440d004400920030750b003a0700307025982c901021548080030040c9600c1507106100410341d00c03100000c034500f402002181035025541001c02508000d042041000c103860030f84a0240d16503030703100c0f007003c041c1c140001c4140f18411883c1d100c0040c40b900892201c940d04008081400c140c103030350103040c200e1060301300140001d000280031440f940780342508089201c500d61b0b0001490103131600080c105034404132010300801c000ca00108036900b00200c1101c21080c40034500d50800e868140840d11070302c19140603404101c528809072000105a24542c2e0004001034400c028041c0d1910340035140d103490015007031150b1041070000e40c00600c4544227501c15041c1000145e95a441c5650f0008802c2c006003590081000c1804101c80e036004038900074001030f0114002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 214175026 1250 214173776 214173779
    0x31b05030f0c0307050c010e0303040611010b1e0a151403062b060b03061b092404050f0a030512181009060809010509120c0c060d02130b0304020d02010c020105090405010807 76
    0xc0c0c40c01006d040c240781031100b00030003000355a401105403002c84074181891300c00c5000350b500d20b5004000030f000c20707075104008001c080283d483c1c064981719528000e60740380200d285c850350752002050080041800281010358640c8641c8000f0001d1900300350f0140c5040d00216000b069628450040c030a5416118940d00000303060044078010746006250540c0984050b0600c5074094148034400360b8040444040040c240180703485008a141417440c103042112034010960f1000b4415a000d441511f2080e89064291f118610307000c9442000c403035201b0000e1502e400d464007020300640002c801d03121032010804129020341c90744400151619865076074294020701b4200f01502d4060054041c002a84c50038003082103240002449401c00b55003900e01a0322400e8080d0f00a103032030b0b05800d4098100c0001b02e1309448801060300a04026220700550741d6030552541c018080c02d00040b54003070340c03051150110030059400399840326042d03801850036034600120707440410181c6100380d000c0c45007548440300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 214176276 1250 214175026 214175033
    0x40f030308040524040206031e0a0f2a0f050d060b0409060608040b060114090d06060e06030a330e060106021903020a080a02150a020c19031b05030f0c0307 68
    0x2c0d04d040d000c213010060248460f03918806200c1140100000d002d90400000310f0b8500000e19a2040c294000c2c280d0440c003440d1545601e0081c005004803806c180d0300b0640c03400202010315940064001100c000107145004c020411100c0005103e001c80611004120f0304840b01181e004030303000f500740d1034181a40e17130b0300c2d240c8413604444d05540480200a0108240000206507107105508500e09107400301c401c20b030820141d0550300c60382d81540c4d48158030890000c1041101e4000104aa21900c0c0004542c0c3d0381105040d261416440000c042c0742900800280c1d51a4007000301c600c08030041c0002c4070301c9001903071110440d0710350118400d8075800080104900755040104044000d501200c00d10242c155a8019540d6900b000b0000e100003004102d05940a10070040b040000c9103416403003030503040c20403141000703600030542102d00e4000c0c030707070154500c3c0700c104a81100309a00d40e640d0040c130380c003000440c000b05401c40300464190000f00000700b5030a20190150180f04182009107070384820a24 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 214177526 1250 214176276 214176283
    0x51b0304050c13020a0816090b0c010515011e030c0903061a03010c0915120f092003010c08010e090703240516050a0f02010207050a0807020907110c100302040f0303080405 75
    0x8550f0726050040156000d020713809000580c00c000741c030303481441820703042205440d00c4100760001d8a0b0360402045505051a05400c41400780103a04102c08140080000454500a00c4c0000e0b26070711350f0481031282030a100390f100306400b0700d1618003007060701d460340d8480064070800750505c40d030318501030100d800c03514081c410003030b144403503040c100c2c80b00d40382211340c290f502144c40c2c905080c820701c4a2101889400e90300301d81024002c0d031100704a41003051400364800d5944403403000d0f103250020443d1600c0d050520429a2050040d114091107030310305920700c046440700421040050003003000002c001a21070384804a04a0010070f0030402000112100302102e4008141015107440b000a44030401d070071401700d5003c10030a01e8002d80c040003003502607000e4071858100901c03030f1143e00c612100344107400c000f8100e100c0c42101e0030013a40d16250b80865500300c12444c01c44040c0c22240401c515490213444100d4000c42d18180941055551000301304122a10b510517004900d1304000c10040001c2070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 214178776 1250 214177526 214177549
    0x515090c0409022103070602040f0315020a090e15030d02031e090f0904021f0c12020c0117130503040806100e070e190b0a020c090901110d051b0304050c 67
    0x262400c008950b16a000108030039a44034140800132035542d031003140098144100c407003c40d0022030941d52a1b03645c14208458417003600c8180c1d0914040000c000c400604c9000715a6100709070b0355206007050402d81c0304461b9120240c07108400901042c030021903070710144210300d11030b840d0b90040d60312600034511a80070100c400c14000d11040e401c01001e05e55036642d4100105025041d00e031405180e07110310214500c4103c044442d03141e20040c0496806503540260f020f11420b02c10b5900e901d6a65403404182e9031001105140350100308045411326040c8400c0c00e0303141d0700c0943e0002448141c0305c55220395085a009400002c1c080d004030302044544048400184014a8030900c1203059181100c402800344480c1d0440c6882003840500d11031200f41c0a90000014001040d00c069481c40909006507170382d080500e605010345c81c1680098003c220620035040854203034681c20b458100700841c0d16004040051002c0304422003007100e0302402200102941c4110300c03c1c0c000304441c0f4005030401ca01d03c24034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 214180026 1250 214178776 214178779
    0x20418120e0102030717041e140a0e04030806031e060f06060403080d0203250201091a01081b130c050703030e16050f0d0206030c091311070b10030515090c 68
    0x1c1101110725a640002292450b80d045070440c191200303d0b002c0c3d00020301c1030390702a25440740c0c80c1e1861035079102e414500e00304039904140c0c44448802e102051103004410340c0f04101c0241d03c004001004030b0701500d0850307480f9000600b9141c2e1002c0b5021480110701d00c40030425400d0740300324100001c030348002e4081900b140045407000e08152555070361100a110380807203d00c1403500880480d0760301c1c1c80785240c102310701150301441000b601045402402050380300340c141c4c0c01382c10401d0b034241c0b103c908221850680d103c80001d08102d48000114000104600303145940124a81c0e02101903010240303c0d1703a03420701c1255903096694016003002401c0e0740c5030760b8080d03146404c8400004141c1a002c400c0700308852040c0c44144030112074000081e8881602c10000e50849000000c1180c039814401c01000c0019086940c0c01002e411858141c04851280c106002c0303000d0204008000300e0348518401c1d5000e281c00c049904203544a940300741c1062910050540e030004040148001c041060101000c038000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 214181276 1250 214180026 214180037
    0x1503020f0312160507030203070e061f0905010e010e06160311030a08070e030a060516020d03020306060a031e0908070b01140102060a051b0c070f050d11040209040902041812 76
    0x2000500c50081c2c421030310f400b03812032003001c618801c10100388180d10086400034217440009a4466440e1070b43c0324112000d40c400e03282c460b100c031500340342d12401d00b00217201a5a052f0480f8203000056600c00075050807513041c005503a071040740a03661a4018410321117000c541d449440458031f0040c00601c001c0040d030380660014010065820781c0076039001c1d4052800c0c500101c0d580c0c02100464203002d00f00a010b803c09003401c08001c2c00021310380b01c840380000c0b00d5081b95036a40e2000811801c0b808191015a400391040040f0f005645c8a5048042142c046055036010b01e000301e000d48003280c204a80440c1d00c00000703c0d00500384081e541b01c80d80180f1003504130f000c4030810381340002d495481c010640e14100b0b5681020600c064405c4104202c00813001160ba5960300c1e059043c10764030b010b0b070720031b10001207810345020031641001868450903903840100c0c0e070044140541040040c3d040b1003841a00582c0d1440b284016035141c0c050001141c1ca0107100300c1c60b240003810405101c1c4070380c8004105000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 214182526 1250 214181276 214181293
    0x6010903150b04091406010609050415090b1810091a01020d08040c1e080708010b0303160510110c07060f0210151e150f0504060c050c041503020f03 65
    0x340399458007215070480c4600000c0b40301c0c081d0001002807074031010260006409021031a40a038000518605843c3d4503101c4000780740e0340740d04000660307004203503070f8842d032244c0c83c1c040003094603903007184164040050117840706103602c01d40c1000c4900300703ca030580c80c804142070821001c5e40510500e40d032002c95011024860a43d0f00020f580c0c1c690840d1604100194040014240401d0b11640009018002c82403420131f10384a44040119810303000f047c0c46070044241c0044d20402c1481480b1000b03070090003941c249a0420901c841903441200306880e030340188025803803040c10f07a100b00d408411b4000310540d180c00e060b4022178074000c03542d0880d009000031980441400e0360000f44491340c610b0503000110f020180b030b03a01c44202842d198400294100d14144070603543c618640c0300301c02c0d03c1844001030711000310000d0841d0008000000d50300410310400091019900c1105581505401501240e030000c00c4400800c0445081828210440811240c140214a0304100114000100320010110f14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 214183776 1250 214182526 214182533
    0x1306091a0a0c03030b03012903030306150a020f1e011503020306061c0c0b210610050a020f0d030f060504020414060913050703020a030b0d20031002070c06030506010903 74
    0x1841078a18031002d0101e09079100c410180310390004040c2800240007400510984691804095a50a011800d0640740f0310401885e08000003540e104000040c95622280417000c01c4501c01d40c002001502180584840007950007000c12043c0300d84942044e8905201800d2040306084070729071040f100700450018420409031b034001940c40d800030411909503212072160549812031209502005000510716100090503418000151412840c100504110a940f401003a41c1411007114040e42c002889412080300611504c0075002d9000180101c80082e05006002c6242108004030000081c0d00c500f021014211180581401014259415420179040001d90f80c041e80441d01c0040c0251004200e05210359242c039038400c55182038400c204000e06010600401a502c070000801c0803a08000305440c85003400c94602c8006500440001c291031042000c90446501c1c107040c1c5036051068421a644044607440141300700c07031192107000459454904083c0990b5802401d46060000e040401c0011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 214185026 1250 214183776 214183829
    0x12041b0504091502030c0702030105010e0121030c0f0c03050a0f12030204060504051302130f091103010311120c06120f011703040b0c1626011b080c0906130609 70
    0x3480c0340343c003026880b65510030b403d2440d0301030f400d80a540740d030034000005050080d105805046c0d42884900052900341c103140f03924000200e550080000b41c0c80211007020075904101c80c18952b02c6100500700185d500d0b00c899181180380c010690b50020000008003c21103844254404850181002c1d800c01d841d10402a02c01e0196225140c054801c0210749002d500e100e50449152055001800340a2900d680b0500c400083c0c41c01411310f09441d2040d1000a1520002664100e0303500c1000c080b003450042040c002d4400d01e0265401c5c0910405003c00c8550380e520000d408205400c4980030041e1a1110400615501c182d110385403a01145544020780e084c00300456059541e080000c50352900c0450b0114944401c412018030140084500890780c0d01c0401c0e00c00090082d001d041103c2c040d43c03071003a00d0072603001c84c0100c0c0c214048120a0440c0c5070142c083c00e603101044e03091441c01d0841007404900c4e150b01c465109820404e00b0b00701031180d01d801580c2d401c00f5010b8141081605007032803900004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 214186276 1250 214185026 214185053
    0x30f0b0a050603040204020f0307051e0403150e101b020705090405030703050708040f06051918051507020306090102040617060307030b15040e030a0e0d210512041b050409 75
    0x6604000300090541d1200d8044a84058a23003404958a00e4100c0300246103400040f00f581048030703080030b0b440c40507002d07034143c4050fa608900e09007201c0c2030040d2500000c0400801c1d001441c00340d00c0b140c80005202c0c0c403c4ea1079100c044800b24045130461030009003004010340206110303280b6802408003043c000001e40b8019581030a10960b9a50300741800d540718000c076400180340c2d16010501140542e0300c071020303108001040781500318810140c6000da94081c14441003214912942000300014900303049202411074803140c000c1d1074aa060340119080040448086246a40001e020080c07164011400707092604401e5981005080030340000f41c03128841e21010b04442c00f0751022802080e100705920006a60041003003003410f0010321210b40f203800401d138042c081400001c045805040c5124206600303070b8421403403213480c00780d83c8400345400715035107820080100034440c0100c409210700b0041d005070b00a01c8904092300b140320f20303030216000a8015900590070610008006200d0031103280 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 214187526 1250 214186276 214186279
    0x50a1707060e03031201080a02100201051b0a03140f01030c05060a0507020405071e030906060f1410170405010203060924280b040e060604030c032012010c030f0b0a05 73
    0x1c00c0c403105040001c1c9980158900081070705e4660f800003903e403800080d05101d00c0e100745c0300301600d52001d810580c200c800031201403c0b003000344400c542c1c0d0101140002c01c490300c01c0b410f00149041c00a50204415101210404002c1071440014424020780548100080000f184c180b880d0440f030140040c518041c0140c003c0c040c50b255070221300498010001c41c1140024050750303240106194100901805070700c2e02c180c0c1c0d040c1c034000012440302c481c018141c00b03a400c84070f8240002c01c042028003a01014014000342000311100304180001c0e0304841d03580c01039008034000368607070a21104001900b18040d058281c840c4200490700c06080084501e00010501180c0c04045800300c1048101240b45100d00158801d200308400b1800c500004058010390f1940080040584e1340c09050207040e00c2140400392101c0300b4140e04100203594103400d600d81e4980c0d90041d138010340d000740116039119005842101d00365101c26072401169454410901055482d480038880f4410500204140404c0b80c010603 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 214188776 1250 214187526 214187537
    0x6181a1c08070602070204090602090a05010f020304120519050307140c0108040b2814010b0903031b030903030a2105041e02010201020906070606030308010b030f06010e030a020901030804050a170706 87
    0x82c0034000d8644c103640320f0700c1e00a8030a20445c0324030300e456002940a1400e8a02ca42180780012a140d4400c01c107038101d4032140e400540c503081c1483c4000360b08048040003107400d44213004445a6203030090020391607807849078009588076007140c54203001030403160340c40c50529400300700c12410303d07030b44900003503001900444a0442c5854130b03016a40c2540d003480502c10030302420301108040802c0d80e0b20294240450825800c8681d80300d4007040350354814012290f905600500c0804494642019034650891158046a1070a86400d003c83c4c1590408607600011400010600d807801c00001c00300c920006030441c003080303d483d003580c84244100ca01c1403c3c600d28203042d0703603003c2107900035412900fa51b50000c082580301e900d00d240c51300142c1660b01044000070340c0791000150340341d10202901e000b00181044c85149a890400440760b401452415540c0340c41070341d02010144c2c9071a000d075030185000311009036032142054103220705480e840d4011012145507483e990020038002c5000410341d8080c0c50329 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 214190026 1250 214188776 214188787
    0x2090702010c0c060b190620030306130e0733020a0f0305160b0c0307020d180302192711040503030301120303060e090d180e15030106181a1c08 63
    0x446c40d07003043e01580d0303410f008580384040b4000c0c3e00301ca2144410710a00c0303e800c03410442c101001b0741380d001c1642c0c0c01d900141500400441c20115400240d07424410384100c0300d019031b41710103400c0b5a01001c82c00241c1c2c00d0903103501106003002e50010a1000800b40010904140e6966941001a0703a41d00050200440402e86414403444015469022900591120110f090021610302c1c11350094592102600c03628030258038190040d410080381202014404110604c0c43d001c2c420341c0d611600039546c629001000126864058a0464880c010360600e007424103e030945103081210031440721701100017802d12007040103541c00400c50313040d91b080641c0c810707000b00b1500e02a0f0140403907400c1070707240b030551a040003003d40d0005241800d10030079035150b41d8100000c18101521411070300442c6900708401000400390f00301c000200d40c0c1c03000007800009031740356510003100c40c0d0324a6190611413076488000c601960160300c2c1d0a4514a0421500e51668546000404c1d40b084071501d4010000e801c007190 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 214191276 1250 214190026 214190029
    0x2010804030207121416050a1a0f030f04050c0108090304210f031106070504050a050402030601020f010e1506030d020705090a09020604060909140103030914060403050a03050702090702010c0c060b 86
    0x6100040c030080180300303044442d501d880d000e0345d42035660b01d443e00d03c21070314099060310b28480c0d00700c1104d2014014080041c20000381940301b001c4488200281003042207a4240650321b90300541c4074030400c01920513142440d00e029410841f906e0314043c10481d240c001d01c00c03200300100c1110200d403072441c1440304210541c5450407203031445160282c443c0d5405901c000515800110300c60300058003805440640c0e07189142a00c8034000c80c0266078120038030300700c180b125003069030007150408414011a1100701c5104046801d6074901d6440d82c0c0c0b1074111a61140080519821864001004a0103003e41103207091000b50782d180707a40315507841105808003103080b8038000e0340951035403900680385507501c41e01e810014007138121601c10003524610b480098205504030f121405d0503131740c3c5581d400500078940382e12140d03c0413464803400d0b0700c514200800400204104060b40281d8441c2d140c0c95120982030042007550389008000034250390601a1115216030300a001426031640100000390340401c103130 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 214192526 1250 214191276 214191283
    0xa051b0d150203070807091a03070509121e06090303070f12020a200a050c012105040f110d050a02060a0309120918020903030403060b041107140c04090807020108040302 74
    0x5502070040c818a5801a90081c219002544105055201c4510315120718504445641192080c1101000070009203100211150f00460704a94185010b600744000c180000d1321141c2ca0041544d05039000484012076007071809040c1e1040803810b800b4049034600382d410b80da2248070041854081041d0800101d08860040d0303925040040e17080c504645651040300051b090000c1c4000c14069840036090030048110000340b000c1040b40d0000c0a045402e40410044d10070340840744280041c070820981401c0400428443d4038800c80c0611001e484031402400c0101c500b900740c00c040390068040540c41c0313021580001d0f00700b0215505070780315a80e59a5120007240184a00d8800070305a0f4040300d804298158015048419a4400088114010307400e04103601240b00340b85d0843d0301500144020008035595600c036540b2000b0251010031101c880505a01c941da05c0500110b502e01c1c0d1a01d020010004100013000d4113140c2520100300240c1c154989a41b2402845002810080d50b1000a02050710a1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 214193776 1250 214192526 214192549
    0x90d0f020307080d02210a020a03140d090302010204030b0c040305060711010b040204080a140d020d030b03150103051510030804030f0f060c0c02090a02030f060d080f07060f0e0a051b 80
    0x101c01c0e281c0010000b40000e4a5160002c071515103012141400c1b0380d1050364400300e03640f18038180c0090861880c1c55600b9904490617800c0744070b5081c6c050000b9400c0b0041401b45003400b40c1b02e40c3c00166100d0444c0303031002404001408a03010b80c0010710040c070000c1d100044498005c00c03281045145400c0c080c18160140c840409040d411500204000a400d000014000c044506c02c01c0482080205581c1e03481d1f4440e03503032081c0740050340103140031071209000f98070003c0c2248024050303070b862020005003108402420307401103a056014244031401540101d4078107820030006148120f206145483d0884140640d00020340960180c170b03104810442c4404507a10750b140d00c00d100348407903011144094500000c0c010264011248840050500a03061080f04d215407814005100c071a220b007014003401c1d004600c411a84060204034121504013004050324800c0d03c00c4e400400d12008029180054541084080398940d01c03407845070f0006174010650941070103451031210700303502d10880010141c2c41c01 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 214195026 1250 214193776 214193789
    0x30405010c03140421060f140a1a03030c0c010207140a09050703090c080c12010b0a03080319060e18010209010f032012040b130b010308071103010c0c0203010e0102090d0f020307 78
    0x51811000c08040c0b004411045c8500600082040d01c000019290688510b840c40c4036240241400095088009900865100901040d07944800240c980842d1450b801032540070041d41c0015414540756904010002c06045811305001d400c8551802107000fa442d02c0c003e00c8521522200012800c0744203a06c10602260405d41d5038905030350b1002155140d046440b4100e00502c00e051980d40c00b28814040c04081d00701c0030307054080103482c648880800e80c01c0070b01035040010503010a00c1190b8058001d1201410780c1070201c01701803e01c214071086010341d0000014450f4014000004a42e0300f01040c10760fa2103a60401145030041034540446405d60001400070180002c120b00b0b100781d0507203210522a92240d0440c5005444032850301c03809a807061801080200c2c01401800040d001c04041e1030642c0c4164042c408280801002a00703440d604c0c0310400010340e0104c2e0210540ca400d0246901d80007201c0c0c021460300d841c84012629980c070900015000c041012000e604540b004c02c0441c004007c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 214196276 1250 214195026 214195049
    0x50109120638100e0303070f060e0706030e1023040804090f05011a07050319090302040c0210141b0c0709140a05072d020708030d06060809030405010c031404 69
    0x2801c00581c00640c203100e002074040e58148101807003c074000c054076008504018000c50130f148a5940c1c0c88414444910b00301c403d245c4540004503409420000580541100e490116a4074440002c0510b08440319400d1125181070000c2440295100e840286000009032240c000603074441c10070178050310032544000c10f06440d10701d000d040071140f50b201c1070690b0305d6211061021002008030810601422001a080d5001000500c606894501400c01890850305242520f140c2c0c07a000101100c00c0304a480c40560002013002000040c0341c80781c550380e0b24082035404d82d0340c01d12024040d0340c2c400300c2c400c040b000c1c84000340d03403c02540b081007200020706c00d91800748030400c4078404000710000e055414520160924011641040c096001c8404041c04e01c5040c218911a0701c113170640c003440c1c80c03150340154002d1800200300500203000070882c100c14403a002c100c103880c1c59030050030140010300d401030a0700180700a009503a4040c840d6440660107180c03a0904891a01e40c0350010710035640007441696 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 214197526 1250 214196276 214196351
    0xf240913022116050a0b13080102120105040e0115120503070c1203110a0222021201090b0a05040b0904230d0f08130c0509091002070506100501091206 66
    0x42591805000c08a90b5019107807040022610303210400b400d4004e050380854003800900c026041403000e095404a074440300c1c40c1980c2c0d51010701d4226884054445d0031b0b4280040140001d040070300a0f0040b10755244000c00c44c92840c00444081d103c00790051016500d81035510394281f1a04200342c4421580205a84000380c0e528400a03680d140388070411400b0610490040185040c046003c40c00641c000c1c103002a1105120003039040c0310101410b03080c65540c00c0c0a10010020070321407884c00ba10400400080528001041080202c415402203114904290005e6426110317031a009401c0b0b5808917960b02c042d0000c482211008400348010781a9124050024140d070760b1003402c3c0c61001d01e43e901c0c3c0b01c1c207603292046d0365202408420009480d010154504000c00d00300340903119840492070040d1461000701130f0030360f0184d0b488040c0568440e0303c0078091000c40c3e0302040c0007200074402400c01040315031404400d4038400944000c044c0000303a4950101c11110050900740101059172641c4940c150b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 214198776 1250 214197526 214197559
    0x40b031501080c150a08040807080309071406130b03040609020d03021006060306061d15070317010501030203070807080421050c0f030405030703171605060f24091302 73
    0x1000d2040400a20a00c1024111401d020b43c000183c4c0315103640203441e0404180c410f481c40340d40a001141d84140030404c89010482c0705001e107000c0c40d840401382c400e05291608880071034a1580380d5512800701040070820b0944042a1501200e810002c50b58803039680342440c0009202c40d08010350018001500c010030140d0210f803c0a030304400030800c101c0c5544030302c4200d040f14005d0250304c001c5070100c0c11507039505c01c110302844420f00340100009039281e043c1d42c1036100b540207007504401040294841450b1459085401400751100703181c218203529080d03000a00182018018078140188400894240407074405481824201010f07000070030107001070002c00c503510030040c003c00f034003840401940c1140040111001c071000240203011850440e00c03100740c0b600b08200700c0d07219444100901074001440d5480020780700c9c0500e01400c0c0d60314001051407001d11004000b49940003c0341440002174440709815003d15006690b010703e03650703070780103041811300b00a01c010703504c8043c8440f24000c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 214200026 1250 214198776 214198813
    0x3070f090510060f180902040803130806070e0607050106090606080a05180304051e030f0706140f0f0703020f06240102060c030406020c1e0102030106030606080f15040b03 75
    0x3110503240d010800d5a5a0b4240e0516640e40c5002d00e80002e1103050840c24200d02c9000c2001d004008a00b1600748a951112600201d038415404000c03e6040400c44404000150f45081b008000e104060030452420781c0c00240441000e669040c4a031744085680340501c0310035803000c00980383d001404c101003511924081e0119804a07600310940e8101000107002d50003100b030b032800203030b0041e000b981400c1c05c0008221802c420320304000200c0d40301c218540c407640c1c1d003000107003050034814001e00340c443c1c1400c2008150a48820b44080702c4407080002440f6071000000325811403203145aa90f40310b0956160807400d0540d5010f11803400d02c91481030202c199981d4411100351343c007450804544d01e10103801642c0340c0c40201c0303104010f000b0610029000c43d0b9990006d054482c00d42c0c09032500541d840508009480201d560484169070110061010759018410100a048203041160151400121155440400405003400c0d107420318098031264660341c115100c00a0010103903406035241c4000303101e8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 214201276 1250 214200026 214200029
    0x10306050a0614030d0e06070c0b0a080108030f1c0b0301150503060703140f1503060412170103080703140f0d0203061c030c0b0c040e01030305090108060307080a0605060a0503070f 79
    0x41651a02c0da000401452030000701490b07480240260030122800c00056a4034001039280d9038010f5804c0040c600000e89801044015000c04c000f019103d122070b10006104003016004000164020009050100e240105441c074080502d6a83e04c400d99406003440d01500aa82c14560950b007040000d0380d88560341c02440d81518010760440c0e45650303656900f2015128410023403041d0402200104036400384056020743d0149120a10015027009503012a06d000ca00b114243ccd0700310900340d005c5448581c030803c000b40d4000c00e807400f0072142d411602c41c0c0d580b5109010300281402100002c21101711a58026282d5501070a0100368942894100d940c02030f510440d00c1c41e20820208a041d1401c002801c41e100350580c2540d01d9403002c4d0141e5440c1189400301520100c15008140000940084405401c501039803082c1e072510b07184d122200002d4055000a0a00c074440c0c0c001c00801e0050075000121382d40608d030400d0b80841c0d2501c94801103250219250031850b058081d10a02150450420b00500c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 214202526 1250 214201276 214201291
    0x5011508030702040c03290301021b1506010e221b090603060e041e03050403020907031a0f06030a0b040b0d060c0207060e030c04020a030b030618100905071e0e01030605 74
    0xa09001000200c040702c1c600000304040d26100c503004040c98442078100d061200e80600010b2030300c04100030bd0004502d4807002c1c19001e03804240b5a0f041070780c4a00300700d1381101d021709114502c40c04d083c2c0007e501072034440444e2500703500041c02c1a1107540e180c001c07805013191900755890440c01e400e8001e0030003d5038047d101c0480d08107040050107251681346c0612030f41e00031991043c00081e5452096100c13540310b00c00d80030400c09000100160307031a81803581c090346203510000340034012402e00001201000b509103124a0b000f4180e1413040d142c80e01240d5000a07000c2d0300103840c1c990b100c0080c000b8480407518a07006001c0103007520400c50a07620260200b03035a40c0803590540c0d0745034402c948a04070803070001d0301500043c005d014141400d80252031041202c0c240400d0124030b10021a14000f4200c032440200d0350f00c44010b508008042c000305203190398404060240d4651a220295104a01d2060850919240056507150044002c078400a801508428505540d41f42042c102520082c0ca400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 214203776 1250 214202526 214202531
    0x702030d090b07090812072306010b03100902070f020103050709080f0d030e0d0203090937050c090a0e07090e04030e010f050a023c060108011d0a0f0501150803070204 73
    0x10901e8040040c4100121500030707521b41c5444055554069603840074074021041c1c19040e0804902c060b03050000902a06485903000c5d242c2c60162040140501c031907000603080b40c0f0402608010800140072441d2039174080c2000f24084d12201ea04803100c1c00c040d4000c0b90030b0f0040d5000e02610f82c00210321451444440e03503062280640303c010f960303100c0c00403c0c5100d01607842005081c40508181c140c880c2c0c407885000d1a004100c5400e42600e00a0900071480310902003002d0100d59880500e02c100c54101e0001420700303003003d188001089901c14603005254811054500080005201c2c81d00d00b4041c000d903074244813041c245403501030b050548512045020540f0082181e401622410680e000d82074a0360051595025840f9a4004849000c0e00e10010b00c0c001107444040b100e03414010301100301da81c002025298541580a400c603200e00402910140f041394601919030700c00540c1035030868000d010b455481c041450600d006141c7d6607004110440a0140001c920201101801070365000b600e05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 214205026 1250 214203776 214203779
    0x60f0606020105220312050c0a27030b09190507170303100e070c0512130905151002030c060406090b070c08040605090303070206181c0206070303050702030d090b0709 73
    0x5030b00381d420488032103202842c040800c903c00010041c600220500a08000d003107081003075141c00c00e4035411101800041000104150754983c41002c83d00f8000c43d203007161200030360b0700480b4495420a88400f6084600c00300101d40120310510402c84e40ea8201d03010f4558411091074080e49400840c4035280241884c8031901003118004000c403032081ca44c2c0b48100040c141441e141d003c1c542d2000d4030110400443c540007000043c0c0c00c110740c0c00012402000706480e03d01c203521014261039141c102c0e8040a0404041c03244010b0760000b00640c00104480030380b140021703014101e10314041c41000e2007036807040005200a215a561203074403464000c000c0090300e951075003015140f02c815001c0003003405c1400c0004004503403146d0083d01a1000040a89192107225000129030780c01000e0307e81c0b2000c40900b960342c990315101100140e27036a00c0d0341d00398100c07100b16000241240500c0320080d007030640b100c0014011610034800c46140288450080144140380d0414084906080714850041519546c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 214206276 1250 214205026 214205039
    0xe010e0c030112030c0f0c0902030a0e070f03060207240203070306050612061207180608011d060103030305190f0b03010f020c0604080703032901020706050702031902120a060f06 78
    0x4036410f80d24840002c0003c01159a011a5104034008003616820103120180001521403411704008200c81e000c05a00c0c0d09010b0710754411503201825194081d400403a0070420194032521031000c6a41024005840360f4460070034091107061100a040e01450002601c0c6c484d2190b0381c0039601565081c1e604110b007545500600210340f2a804507a40e8001080d400902c0e28580a007403100e0400010317080d680081c0d038905c4060303040e03200d2041c0e4000158451206000c2d00710300b48a0a86000300615541d01c0305840081400e4803076406000140815403100000782c640c6131a0783d8540c04000c94074504010aa0411072803c00515007164818030030b50030700200e0240d18446000341d503001410b2801030070044e00c60340e43d62140c507885044c084003851780f81d80c040d0080c14500f07441030741d100e460040c0c24004c00d0036810009060124030f130804414420184140c00150301d0018946801c00d2075000702040090680c000294002004103842c0407030300c00d40605004000194006000340d211500042c414030341c5620 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 214207526 1250 214206276 214206301
    0x10b1801050708180a080a0c030b0601080c07030302090303070c03082703030a03021602031606110102032203020708190c09060b03130c1a0301030312050c0301050d0305040f0e010e 79
    0x10003510fa08070521840c0d400c22014444080071180080110a01d40e036240c0e081801c001e5403003816144107100340c2042007403005002c80140c3c441c00c00d1810b06200e140004996850340540200070f41019800f24041e290b64808008032000d040c1c00c40d80300540940d4a1620368280d9021407941e99161541408010802c0c0d01200d00300e1070250001d000d0340c1400301c2404110004d400501480c0d06c50045902c050707002da1420f1000d900014580e4402c2800343d814030754054071804105282000d142c4c1704204001c41607800e005914103510a80c5501984003645040492a085043d0010390076070055034007100c0d0015000e80400c49261003030340300d40d00351996124080110b031018403803240c800504100286496801803c8902200e100740c10300c03a04203031109284202402c112000c0068410000014400c0c0740d0860158419081031760f006012134505550b006030103000c107201c0d10740200c000030748a40030980070f6001d527406002c184200d411419618200101003800070711035103410700ba04070301007903011035541c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 214208633 1107 214207526 214207537
    0x14041a0c0607020d09050423090303070906020a020d1e0804060c0611070c05010e0111010e030301031a040b060d15090f030e0d0507030209100b03010b180105 69
    0x40060240360040241c10082035502030020b070000c250740000c010341514021f031004039000c03d800c0001203040d4000380d00348880c0400c000400844160000145110300103540c1e511030b010b80e07141c50903a2140341964000c0c0d003100031550114003103084515180c0042d071000f5104840d030540e40d16846442e40150b08940d0004002d51008004e10425015000204ca4820601803402e62140c1d1041307242406885000d040c05101c0100d0380440c2c0c0607843c040c60601030240240704002d8a0280c9940320341c824081101c0c00040b00a0701180a0a602d5411384926413050500000d61540402c002900c600003000711090501c01c0e03c030f101c0c070b80c1c0d060094841c0c0c40d1054015601d003920b00e1030042c0043c0300300003400e4001d40e4141100400300300002740500c100c0f60180c030041c040b41c507544040700c00301d14590440811001d00000004046032184000c0420a004500f0424034040c0704004540030b2050 = true := by decide +kernel

theorem cover : BRFrame.Cov 214028776 214208633 := by
  have h0 := BRFrame.cov_init 214028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 214028776 ≤ n) (h2 : n < 214208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
