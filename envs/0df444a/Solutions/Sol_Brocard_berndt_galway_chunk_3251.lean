-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3251
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:06:16.678712+00:00
-- url     : https://prove2.me/submissions/b612268f-c770-4484-83b1-41c68a1432af

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 584532374 ≤ n < 584712230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 584533624 1250 584532374 584532383
    0x21602031617060c191209380f0a060e04060c0f050304031b06020d15080f12090906030a020d05100506010c241b09030b060108010f060c0c0e07020102180303160f 71
    0x548060460f10a91f008803640144910804604101410318090720b84071660030007000300104080c1902800039189200f500718428140700480c0713848403a401000f4000c00c1d04880e190820781014030041102c141c0c0880803007583e607a504d8031183c1c1c0d0313442e040311180302c19075007e000606900390400f900b004001e00d18400d0352040000615004041174000d02381d801c040c54402402460711400c100c400c00600036445041100340241000799025400c1c1034060041ea000e69000c3c6100200180013070301d00300011081a03800503d9000f01700320038a001640d84050340700e041d9415080c040407a42079401815804801ca40c0300081c81e000d0441d940091003c0c40d5014242c442ca50389803005050480011501c001c1d01c80b40a81c2c88010301030543c200801c0285010f8038250421404100401001000300a03a2099403007a1038029104812400d0011003080103410000c4d0038244c880a1009550b01580140181c80c6000d1a5100303001220003010380b0b83c050310200080718600b211302d00000407141c131040e81e5074074840c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 584534874 1250 584533624 584533637
    0x90c090403210f0606020c040b151803070909050304060311091005030a0603080f0d05060f06040e0a0207061517070602060106030e0a06020406030b09011413021602031617060c19 78
    0x10f038511029908a50b100345c001d600004000b12903420702d409030103080901a25609040c107001c42901101d4072418001401440a1884003a844c2d903040c41800001c103041e0405202c1c07034000d070a01580765403081c41030102103071a207502c881c5c03440d4200098611108004005200c4040b00d0f620980700c60b072008041481c6d1983d10400800040d400d07601030070a004400410f651110b40c940d00070000c503000540b02d180b00d8075050b00111601e030384100c02c40702920610400c44400c0d8440c000210040c0c0504100189800c1c00e0007042100c81c1003c2c410181211f0000794051020002c04c03c0950711081746000380d60050308020014481d4a0294011491600c1c40e00c0c100e6981142685845080f600646c0020001076114003203150117191010150380076100c2026144d000c0c0d94000002400070740d406a9101403c0d030003003000c00955a00020050400d6006003d58a00d0301403a10b0440c3d95250a0080765580e01003840c10050000c0009122482001c1500c1881e1901c011030311810342018035210101d007008007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 584536124 1250 584534874 584534891
    0xf070e13020307020d090302030304031410050a141528050604180507021b0906040f02030703050402190303171b0c0a0201031b0c11030c0402040e090c09040321 70
    0xc0d080003650160510340001a12403d02c50402411706a00b000c0c00001c01800703400c01e2015a03004401c84040b29400401040d2440e01c1030b000c10b0900c05031035800702105141208200c1003c586030021a410601a540204580e07280100c802040034540b0219070410000621900480824116001c5030b0071043d082419036555240010b913a80c2c410f80001d001c030100f07203141403a100450701a01d03801100b28000740461400c107455041d41801070400091080d030703440c00032070540d8403140d1203401d02c00c40790b2000399520710b0481c401070007802c402d41d0120700130200c1201c00d42040e4040701c20b00042d00e074103903250b0750070070303035201c0780f0190130f80050100c040050203d5041440050b180e0700030046508480098003030840c8a00000d821950f43c11342c05800b00c50b00c0200c020350294030002c8061a01c2e40b014205a208603180c011919000505000a801510001c0c006c80d004442841399445a042d038011141141848414011702c8841503400034003040d2902540141903d00c0e2100414800050500103500d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 584537374 1250 584536124 584536129
    0x20f070b060f03160503010e1c080a09022106010603061a0702061209061008010203010311040c110304080318030a0b07050f0c0732010813020f13051801060503060f070e 74
    0x200f001d018003119151000040005c0d040078000c0c8082400d00364090300b01c43c2031000c6c440902810b040c01c070004100c03800713000992800c0e0325800641260340103040c040b801c010110030f2580360f00344000c000d0381c144905400003584034824007600c800e42d0603980300c4110507020700d8030140e69070300900400c0344c0c0030b8010b02000b4071601c0b00f10f034800d104c1d10085d4020301d91030400d0203920507401c0103500100210703401040180302180c080001962865026200001c0d98a07911100700c88030780c4482e440000d9400700080010b00108000040e0641100e5400d90388a0495580209569800b00d004010b20b5021070343e00141ca042c0c00340d405080000d042d103440900e001c0d0b80d20441c07030400c100d940041185200040401c4030a056404000803811003080e009020074605000207040c220004200c0026230424811660441d11200742c80c200c1e20202420301151940c600c2c810101400d402c9400c1c4c210200c00c02c0c004042a4814082d2000b1990040c010f8101501c0350f110b10301200c0801050103040c0301400d800500244c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 584538624 1250 584537374 584537383
    0x4082a07210b090303040b010e10051002031905130501180302101e0302040e0c030f39190203130b131203020109031818090302070513021c020f070b060f03 68
    0x30003201001c3c41d45c91405c1d150000f061030041e0014030400c0d41d06402c100586042c43d580300d0595000702d851403607448903c0b5040345541325a9040e90030480030780710812a81d07a0490060803001c241501c3d5181010749a000445401c450010503d4020101000030000f504101e04420f00c43c0d201450104450604d06044082c00d507400d020800004c5d600040800041080320741440d001041040e1261841c00e00140c2c40b15003200c090301a220190041615100804001118944c0d8003040c600c0c040c0c1c1001d0f0341c00c107560039400500b00c11943c02c0c1030801490070300784048102d62210703208003900c29036641013402d0b520a9400c1103c2c01201440320b44000300318104501810040700c1d110340c1c004108003010345002040b170b8001000384901695200000d1124a11840e011307154a40600b40002d11041d1030b0a00324a0180c550b442103822010404031001c1150b441d0b0014040011000d00f414120170258800104a1140703082c02001c1100600082d00044c030280204c1d608424024010210400808000b9080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 584539874 1250 584538624 584538631
    0xb0301020c0d08090613020d032a061e050c040b03150a0b07020a09150905060613080604050f03090f01030b0102120d0f06140d151404082a07210b 64
    0x124010f9401c004210604000c115408031900c2c02c540d002034501e41c0800c03565600390200030f05000844440c69003110080042c80318501c41000200d50038096420300100804642159007002400c00003085400101d42c010f050066004c1381a080c90503140038100302c0160805071040340314003282c40c0d02a0031707541c07901c0703994015020740e41b1003076500d401910412400880503402106100e041070382c0049052051103680e000c0320072507400810741c3e0340c80e44c4c001001d500c142d10700c0c0d42c5920351000020842c040001207151003a481041100c05131f041c846004c4d0303500d028003008240d105001aa2000c07540d4446d8110210350034040c0103c5814920b01c3c0c01c0c006035900a14510200e00e581c0d103030b00c42c000039028000d030b4000340b84400350718100380b4008011640c0d040801e040030700b1f03000d04c41c4045442c1c000d6130340c0440c4210b41c9540803003800341010300d0034584a5221480400500b030200301411504080c054280004d80101801020b03030740c0c586084180710520884401c1030110700c1c100c0f44800300f0510000c4520 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 584541124 1250 584539874 584539877
    0xa06050c03010e0601030e03090607020406030507080c090f0412050705011b02030a0207050603090a020f0d0519151505010f0e0d050304210b04080f04170715210b0301020c0d 76
    0x1225810000201c103d010010503084c1010f00b4003000c00324800d00441160440a01614100d0b924060381c004200907004903800103080d0b11501d00700150300080815a10b807a10401c8614108030b84881c000d070028001c059a0103000f03a000e070000030903040d000300020f02c00b4034426800402d440c0d0f003a0030614012084803078500c1c00b40e080002c4520a00760306000403800381c1030485030181075091035070206540b440c1c01071000303005002148001c919940e030340f0440741c40a41c0c4903044400d88507030001c5072104540d0408081342d50900302a0140d01c00c3c0c03428050041c60b604d2030140d003078400b4681801161100610086002400400c1078800c1c043e0312000007500d9184e009400542d81c407894003110f04030242014803040d04010500c0d0b160800201400395054109401c0001552183c4024490920702d00c0746500804040502c403440070181040403030345000b180c80c80e0f009040d4003900c070102079980d110b00748051112000c11054285103001c503075118100f044406030005090140e0350082500c0e11104100d400e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 584542374 1250 584541124 584541127
    0x80c04050a142e06020c0409020d0f03030b01090b213102150307090b13090c120506100f05071e0b040501200a0f03090c09020a110f03030f090a06050c 66
    0xa0409800e41e0100300800c3c4903643d1001801e02e130000094581d40c0000000303205985902a408c259a28541c0c0c1d084da00b80c12120031520f44802e880c024000b810b00700100381c040350100b0000601c1d1040901a1010b040148404010001590003074a0460a004050152603011046e5040f0035030ba039104a0402c505491440425200c09401000403841d0700d80210701c0c0c2d15100700104005150b0180c440411140310362501621a03100619400e445159a04070322502403412041c0254194000003298140186100801c00b039242e030070501c030510680902620200d21403000344000e40e40b045004080417030150008200e2055100010303e072407100c0b000240c0c0c00b104198284002d202080c46601001d50307401451052642001200504e2030040149101c20301998056040040d030090700078026490b4801c40325031a407505c8a0040000390880c03010306c1c00240350142211100c10001a445d0f08840508000310308541d1801c1340843d905800625166480c02441140800070b451401842e004050301c10109 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 584543624 1250 584542374 584542411
    0x6060b0901080f010303020a1b0305100603110a0302101d03060f071101180201080c090a0b0a02010c020303010e0f0702030c06040b04140303060a14150d051609080c04050a14 76
    0x1071414502400000c02043c20f50300400000303400045182c07400d40c5c00100f022900d44507200d243d03c1c21074150310150041c0500b0b4441c01c081d02540c0d1103103055070311071100d0120350480074040c001c0c031510301d000003500a05107568110940e4001c00340c88011940a0244120504002d8086401d03d0800c1c1c4160740c2881e040f1040c84007560304402c5010740600d81500030804c8024a00b0045003103405110060305110090303004c42e601100143c111005048050401300060f9555045454103a0102e135032200154070705413511026600c08412641261424400f002d0192200c50b01c0400391780c80035140d41c040d48000c00c1540043e00d0280007441c820790103a002051240b419041580982e40b403000031541603042081000102d03911601040d080e1015550002100f001110106d181c02ca41c503083c680300400082964550b0b60965045248111601c0c2c00030310b400728030404150340240c0c89014240b16038025807010140750030b15620195000c00c5d41c3c0400300300010544861600c04a00781c035042403a104402c03a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 584544874 1250 584543624 584543627
    0x9050712020f090c031501050c060907050a0f062a02100504091a03030a0f030b030304090f06080d0c0f03200a03030e030f0a03090c0305061f290a090306060b0901 71
    0x10319240400382c0b200b12851410740f44000320b0703210050180c5001950315006404c540d124105480c042c027000c1d81103d41c039003040002959201200c1c45000c1c82003040c10008118802440ca0380e84c02c07105207494119402d0000070400904201000c8040304500d1a00340040241c0e5072100424221400f58441640d9036090600540544030444443c61100b00d80d000705d4211358400208885000c1807918141b078000030144401c4016042115049074148000305d004140b030003056005002d8151740c80410030030181e55030303607441e1142d400d51071000220b02c08410510105001003003504640e84285048900014072020549171908501000140390b405444441c0c00c040c1c00d8420321005091160003075042a00030504120726210f40030f034410802d6100e0f8500402c20000c3e09848010350b612106850007450001605522110110003030b038540d0382402000544204501440d00110641082020552103a04424041a0301908092003000401040000410100e1090002070a9052580b035a17074030b1240f00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 584546124 1250 584544874 584544889
    0x18070608101410030e101e05010e0609040f03021203040303021c0926041809021503040b0a0b0f120d021203100909020d061a0108180709050a0905071202 67
    0x40a00105950080050705a84100c0981103c90f070038070740400d400052048140c00d1481c8480c4841104d424210003600950754040e003803092240811042249a907581c889500d07642c410341c1d4541d004840c0d000810080b9405100b051942806401250003d401050140e0416481102e00340c000035408505a01c0c80313130f01e581f48e1507407000c205030040c0f2406555844811107400c6403120400c11031407070042450081065416100142203e00c1c4480030501402c000301c014180140089104403880c1034102c400680d1002904d02403074100c080386c0d0301070f1b13140c18101c0300505807864219884124410060b2013580c2e6800a40440403400c4080c00c0603a5401d40040c1c40c00d45952031041000c07405001b0428004900c18800f4201c81440501141446041c00800e5031b41e034400d03001a001c03c1c145054170505480403940c0c0030070f075030b0b0a0769628000ea841c100003501104605003c4100307a08842c2d020400003145402080d00481854800100d050a5568651624685078000d402141003074000d0404c0d440c0501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 584547374 1250 584546124 584546129
    0x509010b0a121e230c0307080c0733111813110d06060f0e210f0a1401060611061b2104061a0d02091807060810 49
    0x841103030605081203000703000e01c2c0da54056071003982d607203030b2007070b2848080c4100700380808085481c1088000d10003a00d0801024041d10040c05681040011818405200c0b040b6032041c01b055848020f107031541c0b0026040b41d48508000e070b4023506500c40385884010342c0070840c46025000052500d41c220030400758400d41d01c07203441d0200400c0091207400b1981503500d4826481090846400d9405c1c0f00e03000e500c100505940c080b20b0004040031030005800111540f0483c20b8403003a445001c1880c21060b030488180c616210f00d96044804020001102d09031510b1401c6400a400c0949a10300d007100c002c0c078a0034021720419149610380071340b43c5070034050a114a40107050341e850105000c0d01b00c4154165950000b0f0204842000741d00b03000300d0002d100c6c0c07090310007000c0ca61900c80c2440781e4202c07940305445400c0d1016115146004000804c0c003407403010100022030b02800581820651303408001d0240c1d80182031403103816152400c091080e1050100802a1016031958001402c012003210030420098 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 584548624 1250 584547374 584547389
    0x4060215060a0f030b18010c02070303021b0109030f030e0402030712110301050114031012080405010201050f0105150c010f0f05040516140d150509010203070e1806120304170601050901 81
    0x218800d01014a43e40c1012040da0742201021429031200e2040c2082d0003440f0042c2d030819440c1c0310340340240341c0d80892075004a0380603900706c03074a0340c4607440001c4042c07010b0f8002c1808201c0100c1c041001882c850007c80c4003901904100d1004042e9102103000e0340c4c01150008001400c0c40b1152384401058032542c102c507000c28490303606544c10500040e100c080003c80364003c3c030038044006410030b800031906c00042d14849642e172209044c24070b04540131780c000703000703050144d42000000743c1880384241a1504a030002050400360f0100e03a8103811140c0d10110081c082552108080310032000c01c0d0164102091a413440080c00345840d080c80c82c188080c60080000b01031014400700200322a070142d041b866102200ca150380c00d0b903585450340b04840c114804049150500e41000000301040d13002c4c62080d1001c1e2211a40a4180c40c200400d203082049200c200ca00d0321030200c2d00c0c609101c05441840c8503402c040303914194030b0300c8d82d8856002d002214803100340d010340c00500c401d08007881d085006110b41c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 584549874 1250 584548624 584548639
    0x1d031506040f0e0604030804050715050301090605040903120e012a02010b10020601140f0d060501171203190b0a0b0d11041d0424090203010c02151b0f0406021506 71
    0xf0020050f21044064006410800c1810101c1d0034400e0603c81c88008086058215099100c80308000e41560002d01c201c0c0c81d143c0c50600c0c000f1312420540212801c095240c1e40b0104149140c2074808001d1540e010002110b641c0c840541031501c4d801909a00c41704070484207221b0f01021a00020700351002500c116016441d4912003107041c41d000225141510120034240c4941079407034012604076060b07a204d95620000780d254030014805654040e41c1a04e000c400a20604201d040410355196003034038041802c5c00c410400038005140e0f1006864040b44030201c0030680c40c5040c40000c4002030541c0208000400009404641c036642e0b110301c0e2049031804d40300721700341882d0154a1001040d501082160610010006410094401400c0c06450701056016054031601e4107140010445414101d0096103025084041c4500005e448410f01c5900d048005a40c1e80e04848041426825541800b440d042442070100185041c0e024102400103940242000b103024040f28552000c003a004901030401d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 584551124 1250 584549874 584549891
    0x1180201050301151b03050d05010503070b0f03060406091401092007110d02040c0c05100203040b0121082b0911120309030109080a020d0f0801061d031506040f 70
    0x1c018054a045805180380412480c02400040d0340141c003503280d046900c18020400c20030184c01c40040d0041c4501c1940405c4640c0c0c851040c503517610181d02500402c0102440001c0c240d003042d8006541c4140041c0c400f0410310b42c0ca0004000b690390700c9007005084000c5d07400612040b0b69604c42c6c404500c13a4a400405002c43c0c1c0d40c0411150711503a0b2001c0c10502e105440c02c0343c0e07034648442401c04140e020700b080004a041c01002020042c0b010400c8a20340524504a4403030116030003a0384c090341e00700e54400c419920303029010001c03c81d03140080380c6075204c0704520b001140401001d007001502c508003520304141c03030280003c9101e5123003440b0000c0301c1c504801c2c400480e02901110010b81030545d80310480303e182c00410f9186014009203a6415800c1010200402c41031001400040d0400e03002c4402980e841641034480c01103450400300081c0c02003004000a5100b01c0340302d402c41401d55805d2882c04a5800031a007032031288080e0260b001010350500c0302c45d04107486042000d12440104001c07a81c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 584552374 1250 584551124 584551127
    0x210090c030b090a1406060f010e030a020a080705040605120d08180a030926061512030301080a051c0e0906040204031a0115031109090a2309061b2b180501180201 71
    0x84c03030b20365598100100682ca440040e1030421026000ccd90300240200b80c03c2d6960400a80d4601d45030180380c0c000c5090900004541c10401440c81c2e90310314907405000e160700c01d03820448040c400100080d01442d0140d00810407000248455005107003e9a04c400381c1034100418103001c052551a5883c90311414100c0b00c0a601b008158650040046d510031800f665814000481039007601440394628080000000369a800012705000040d100750251640c58450815042c49624070500c07284c08258810441001f03444d190341020f900440c010301c01401d0903280d0320b0302001c4400700342d561848100c0f00e0005018a004e040c1c5e4440b80300d0100d01e010300402d0491090181d05000d0301440c2405007001e1008541c80c03c0640d0442c0301c07140d45c110300040590032428404250950150f428141d01d004d0003010070302c01182c04d0300c82038030f003110318100525002c06280e4540c4040714020302e000710b082c00030442c0d214507034a50240c20114842d46425640c0d0800c3c81c04e00cac500319061820b00440d15075407444241d0040c4d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 584553624 1250 584552374 584552389
    0xa0b0a15081611070e01031502030417090d0f03110f030a05090d02040e0f03041406130506180901061106010f05010c0f080706060608011409070210090c030b090a140606 74
    0x280101d20b1030b124540c0c0c440030554a40203203284180c00d031302039284080380c0ca4000c495101e040324042c0d90304548011800c049141240304c20754014206040851101c102d0b110fa1200524601d64060008500724070940c541c004a003c10071800c0700010343c00d203110448403a041200480c0d144000c00074500e00540ba040103003c5208403800980160800b459810940d5110380c002610445a0070550301400080340340d183d1030342c1c854020491703000c101c0c41d000b05042c10483c0c26a511034112040300e14041d414003080210030f4000031190300c090903200e100f02070704c1d89510702c0d047d000b02040e4031000d00c0406600c12030f5040c144c0c140c024031822009000d0411040c0e9010603050b0b05186c00c170b2600b110300495420644002d03c40c1c0c80002e080c1504045000440c2c80d80400076078121002c885803138021240a20412a4010042e19658010f0340110111000c03501c2130303401120410304c200070520703502c4e64030340d1121506072040742d44007000d03003101e861030050152010f4041e54403905400a40800e1820b80d0005450 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 584554874 1250 584553624 584553631
    0x702150c12280c09080105010b0a120c05091c050d050406030b01032309150f070906020c030a11041d0d0801050306010e04060510050319020f04110f070f0b0a0b0a1508 73
    0x3040e1140f0085401e41c1c0141082d001030a01c03c80207112075a12030010348903c1c0d020b004203400050500050082c0305810f880b55400d0407000d6601c0e280b804210358200000c03040c120f41058020088182c144002a0301080231014003175080e25915262468480d01030102c0da202c1d407965061608054a29882031034962100c00100e14100b40300d000368483d00001803402d01151000b07980f4001001c244541c0d85a91917a151154000360b0f1480c2d00303d40c07500302c1280c40d03070200c051042d00360780219142c4000031105c030201c010901024000013145814040c3c45089403d031142c40202c2038100703002d1015043d80c0810080d0140006a004080355403501c0404081e04200030006040c0541d103a01007004907030182d206400511000381140c210413032016a146000d0b595140803803003018403c200388007505050041070440240c00032018104010054491016845038500f20303000405032401000080c801c0d10304030700450002c007000910341e40020600140000c5a00850102d0001c45202c40307450b580a03425660 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 584556124 1250 584554874 584554951
    0x90f0306020708091206040b060607050613080d2301290a0207241806020c1c120908061302061803010924180f0b0702150c12 55
    0xc0c1d0300107600340f15180d80502c0445a034004c0141c814451407400024440f030056004185201d540e4960804200540c8031760117000300702d5006170000401a0401c8043c0d41040e9009511051511098152801c1103c0c440204180007003024080d5407820f040304031209014000e0440181891854140306508200000e4150307010681c0c0002e144041600c02d002c410b004045212502d007034045042000d44546440b03d1442c00054288091585480e0304080711130200e41c0d00f42c0140800780528018803a507800b02442c52143c0d81504000c20300064402d404842c4030301b800340c2e64000c074036041101e2507040120161581c0301580f03000c24030a000da6550000c0341d480c5200d02030048849824040441d000d0001c0c1480a03080c440b1544d207020382040e6116112402da90b000c6801c04c40a80149240d600325035512101905030a0218028800a00489241d6800545a0048465070b0480b040145a500022a650010104049480800304118450741900880507009904c502264008840340c100c944910000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 584557374 1250 584556124 584556127
    0x111120705070c03030e01270b0c010e100b1c020901050409060f050a05060414010f0312050f0d020702010e01050a0c11041103090a020906030307151d0a0302010c03050601090f030602 80
    0x22035840c01401140d803502c0c0e100400b0340e5001c0d0389041c003900041c00001160302044000c1a0041402040c1c040207160503089002d40e20700d1401d1030316070381e0070790090300c000d0029659a1140e0341041c003080200b0000d01100d07001c0420804d0311001413000c280f03100100d0150410b540c01074078005075a0141807030f041d03460660f0f00049540890501c1c2d0050941c210340d00310802d2500e0281302b9042d01e42e40140c1e1141c50185c0702401102041548a002c100c0300b44104881040b102c5020b0002400c042044c506020740c40c50a030b810403220b50103901d2075070f00580c1c4402c002a4005100802c40d40c01c40c0e1112100d00013400c1160502e07041d41c0e0094000d1040040c000d000803074040170524181d54603407240c42803501d2140c0c056160300e003250900350782c4c14440d00f01741e00c9404400000ba9140c0741c0007044034165580325040815011990218001410400f2800c01003080046296084a003040007454800b5000f035001161400302c400c000780885401410803070422000d191f05208901010064174110780e485600103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 584558624 1250 584557374 584557381
    0x14010507060f050703090606050f031b24041d090c1201060f0b13090203010602100506030c270106031803050924070c12020901120507270608011112 65
    0x41c009110104a41c0d80c001c0c40c00b4240458954558001744a0b20b1188508001803511801040a4002c47c50001070380b5078400080c06625040c0e000303500d03100c41d8001e040816111803000520205240742c4241d081251030128040006541001c610032030100c103100c1c510501d0500041c1162190510a40c0c58001d031107100451403185000d600c2807000b00034002034a11469222021a0142d038403501d903081c080a00000c011920030503034821a8122017054009120403080000c4c620003600f802010961f050081130380c3d140854440419224640d5100010612107901040c01c2c00020401a0403941c2090310340080c80d0b414002c2084501c407981c0e0103003001c80c2c4444c07480d000a18072032080c00a009074444464988a003442406014003c000d128041c01001c45c0d0701c803207400c2c1a8070503140300698000c520100401c4081450000b26540074091406c4d1100c130b5858034000c0d0401c003192000c1201ca03100210381020405818032400025028100007032045281e07000b003600441c0100000c060a60500c01d021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 584559874 1250 584558624 584558633
    0x70e06161b091505010905040629090a091d0a0809011101020409090302030903071a2b0e1c020c060f09061b0102070c050118030b0601050c030c0705030d050414010507 73
    0x58200901001c4024440070310343d254281d0450007103100c2c1e9404a510940040f50b240b03454010702007503443d190000e120301404100b0150f414501c04a04c00c010890802c1030890700e8840c5049440903002822000c945444419681d00f19800000ba80000c90381000d04400c00051200044410041007480c0140d00e42c220b01390300e40c0c024812540300c4613200b880c24422808264011010b040030041c220240c80c00565038080c41c1d01c2041c00a0800143c04608214445540204000401d881c5141d81c40c03180b0000c0440e0f10303507811250030820b41c1000da40f188802104803c0240020041022248054501c503c80c007008900c0074092044054029800410300c100c0c03d03110715059820041c24003d44904004003400c07203d0003580103140580300010000b40101349035004012a88456417400d00c02000e040ca103032030301c1c9640c00d405441c05040000401c0b01012240c4100040c16440b0403c40281c40541d1500e002c00d07140032280c3c0b4090003845014442000b24141004050f982d4003028280719070384032050f2a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 584561124 1250 584559874 584559923
    0x702070509100302010305090f10090c090f090606050a0e04150e06040b011503020a1709100213050307051504030f03021e031b03090a06120902030303010806070e0616 73
    0x221641281d0403204002104204540e06001c481c001e1b24100843c1d2141074485481d44c103900400301465011140d2042c3c3d4000c41d62140c65424020015030451a89071288602a070f035420300d4109080b500c4214500502036a440384900a03c0c0031078001e241d4500d84510308849100090028100c41e40038039180113080780c01c1c0c10101001c0010303000e0300d1311842c0c80e2800e0300585000b801207094100b0240341b0900903034002d01c201da4108000351500c1a44104004c8100a100c2c401400041240541961860a5840b034005010110742c602d182d00d9145082c1782c2814070f0320318207030302031740c410f00d4203440241055415800701c0b000d40b0b8100711034814002c1c40342800d0340380c10500101c1c03082840c43e904e4540340c0910007002412280c040700e40c02550100b0280011513990141d03d910031b070b00405450082003498050002142e805c5101b100c04150007800340c000a095070401d0307214040540101d000c014869071300ca03804003504401120154288500c0312801c562080001c1703001440254059a01c104c040702650 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 584562374 1250 584561124 584561129
    0x30604020c0d1e0c020a031211030f0a020f07030314070614041202010e060105031c020717030903190b04060c0315080726030a050f04031712010b070c03030305070207 73
    0x20444001020301e5400078040083c492040e616041c1048090520900c203480500603107800816102c0d05038110345038502c0489001c80030006000c80329100b0300f01e02009101410002689800c05a2500400c000103806c2c140d00540808541d04450030a2000940141401c00e59082441c0080d07141c0d100391400f10010200140058400302c805010031041041e010304840c5200c1e03ca074002e00c5a4840184080d81c0c03100c0a00400d035141c1c01030341803007004601c0c1e4a00b20407000c0c064070455901c1c59843d00944203803842800f950813142c0000410041e1401d0400800c0160514810b8483c00040e031611120401600507200070141500c5612444016120b0b4100a0000106c030452000c0c00d6aa000c1c07031a500c5a05200311010060b110303a050001a00c0041842c100c6a0b4040296262486402c801c035080d620008822216800620003c004285001403180708543c82c560381c141d4845106140800041059100900e000c0c002c1003540005041d41000b4001c40780d25050218076a144c15000b0303800c1c554030381c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 584563624 1250 584562374 584562397
    0x60c07020303130f0315090f02120a080d050a0b0d0c0608131e120e06030103020d0f08030403230a020a02012d02010504110307050901120302100e010e1c020d0503060402 74
    0x1220118403a8130f13556400040340d10414620703070320104480313402c010f03581c080c1c10242002070146900005420400302d030509881440c42903038011072180d556611070b608074680e04540b443e40c840030055803030214880c400a1120480341243c80215682c0c0d550481a00390040c0c90810034014003280701c696181106802c1160b1091a50324803d0342e14121105004e04400c041d103900a40c24540e02c1e2280c05451015045100601554911b070b08540901004100400c030440c0c404011424030340200b07030030360080d40c042d5100b60fa84800000362640042c9580300e04041403a20351208000d9100d1258002034001c01255082c200880708500c1465028010015540c10741e88091001100c0c2c1220760303041d07200e14411172081002040140c0508140756540e1041c0c0580e90f00441c031400107012101110200c0450740c1d101b4030445070304042c400c0d014815642c40c450581990b039120090490566018001d00080304d4041940c080454a0300e400259a0240c0010301814010000003040c1c45880e00c0d0100c54180410 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 584564874 1250 584563624 584563657
    0x5031023090a0605060108060a0e0414010203040506040b0c0f1c0902100c0203100b030d081807060e13110d0906020f0301030305040320130e03090307171509060c07020303 75
    0x3549026440381202d0300c0407030f0b16929201c00030b02550300901d001401900d0180c07803405e41900b41010000e4101c6c01500645402d1080041514466000d00042d4410f51042c0e01400c1c4508061804c49902074000c0d0804040d10414818140510258016503009182040148182044e586400700042c070040001030b400c50b800c9805410100d41001c2810030581c0300340c00f00c0d0784202414807400300b00e4100100e4142d043c1c2000420441c094400d41700a604051b422801e135023031100141e10245810902d900803001300303003591804001c40c41d020641d21418100c0030814043d2243d0002c00d800c6070b105401c07400b1071941c0d640c08000c00784020f03a8103481c2d00100e40c40410750389503140d0030040d00d03d80141c84211044545808140e445d8070905254445240001e0320146400e1030300304548000e440000c10040c15071006000001859a040190100401d030b01c254480f00700710307019101801c00c1c6107072b1240040341c0003600170b00071612000076006602030b10b0440c1c000c1d260541840000e0662040d07240c1440c50020 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 584566124 1250 584564874 584564881
    0xa0f0e071710020301140103090c0b121006030504020a060f09050603040506180f0a020d061103070f02241f0f08060105041a030309150d061202040b0a05031023 70
    0x4241e02242200c64001c022074064007001d0364080240e2009008031111890501c44411880d4025000031207541c0c07103224401c0034991501d075011b0160b0000700b101d0502c552000b041c00440e03c0d0900f0502c000d0301c035524040c0700b1480e042d000324481c9400352040c0d008005420340c020403070b035100300000302c0a040d00030103503907807404d050a000f0755030001680e0300007440700d0740445500318000010302d81d8403962151000c0d226500d02a001c01044070310190041e6501e58440d1600e90b04007030203400a5101d800c4a0700c605a1400340c03044024a0b000c010741c070350400300041c1511140d51180c1d156450354003681441151041d1800f041e8051080121a48282900342c09804041560340c4007061881c165842507070204600d0701501c4094045103d07041c0c0c0035406801c100a120614104585084040214026450310700700b09900c0c445c0450b41980c0c00031b011642c05a510800714a890700841012940c1162000e0f00c0604000003c3d46485440000000050342d5a1210185c851065050745080203020a0303072000d8607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 584567374 1250 584566124 584566139
    0x2100311070b1806010312030c02010906020d0e06060406052b080c06150d0308070e030a1506180c08072d0807270b090406080d20010c02060a0f0e07 65
    0x2d02607070012801e8840c00610454040b0015110b41203a801501d803a0682c00841c400f58005c0205104d25421552500d200310041010760008020211030600c000650032200064141003040251105100d41d0030f000040086690300990a0360f002030b285520748000740e110b44031000000500600a19009010400c402290404146c182c031a0904030f02c003c440c1d11400003007009050340c03940010041030342c0304040f907045446084410380e41c64024044a244002a4130380716a80340310340c00c00900706602c4440900404560959100446030000000d101d20701880d407000d000c7d608018503950030000e2060384420726101d0740c1d2100c0d0000300041041850100c4002c40100800c1041324007070f010036201c03200110f2141d01c0701c41c0c0f5651a0154003010a461341003850038200d5600408840703500c1512000e010030382d407070213010f865000315480d21610728145602840503044034860350042203507490141d42c1503040c0d03004a20749520a00301c4d400010b62000c860700400041006035040c0c183c5102d017010114116 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 584568624 1250 584567374 584567393
    0x20706090f0c1403070303140d1d0c040b03060609061305090d0e0906090f07020a05060a020c1e060703020904110c010c0908011116031403070306060f08070c0210031107 74
    0x540100c60000400f80c40307190120b0300042421401d038040d80141c41c20404a4403130340031008545142c1c60110b24203007841000c84280d80c10841c54601640e40340010501c400d07002c0002209240c41607805000c08007001e0000303078403940010852802000c7d450006685944c9801c2158003061095908001c80c0c28a14806541d50091420081c08900200312104651405021041c42500c2c000c009800b55603400100b03205418000d00844194800e04800100280052100b140b0600034520b005850300f0014101e00c2c40c1854640d101c043e81031003461a494040300114105501001c9401c1c096540d2a107400484d0050000300e1402400010100300044070722011340010300d10103003960364072011a407110082402c9804122806c00301100c100a9090304d489020454901c0318040d0804100340160703080002c04541c0704079020b5000a90b50407060007503541000041200c0004c3c0d18110300700d0301d41000050f00103100c2501c041e00c58080c0340d070365441062180d040600407440741509179403151124174001c2d241 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 584569874 1250 584568624 584568653
    0x1206090616090b0f0c031207200a12020c04060806061c05060106030e0c100e040e06070e0d060930021f02180a230d1101050304052107030f0206010b0a030f02070609 72
    0x441c01d0044220242841880e09250f00809c1c4c0a4420f08a0b1a40c6250440c00c0c20b0300440254000c0c44001005551180314110040c49904058146440c1c06010010640f0071250080da160308120100b00108100060407815a080380c100003030786103da5441246000f200e11101d81d4452548034036012400d500655851116009039410f009120456241a480750002c031060400100e603001c2d2400c041c41e090241c0c420003809110300044010540c0c403506141000c80015500c400c108102282403015640c940444146d01440a004c907240140b04800c0c0ca409c004007000302040d000301d000074141d008554000c50300000208407a64482c0d41c2c142c221850b4003204c400c5112003411f0050703125a0708140c29007260142d44400384a5204981100650351900050000c0d00d2038416003803014100c0e4204ea40d000a8500c100340c6242d26401580b800510080c0c03194006411508013100401070000d051040d1500d202d0b260401180a00504041c00c0c001d01907440f000c1c1c441c9042c04071503800e00000400c42a032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 584571124 1250 584569874 584569877
    0xa0210091e080c0d0201031805060f25050c01020c010609150b04260a0609060911100e010f021510030b0603070b1e091206090616090b0f0c031207 64
    0x903035007441411040407a0203128040c0103420203c4039060928003412181056403050400142110118128080d901d000ea00119801d500507005e1011a0f10282c0005500c07400890001030741c41c660420f2014080c69003982d0405200000c80d04907900d0400390191001540060020481c2076030b20703610310002e030202030b00d200c5c2d0000c040c1a01185504a440455054411034510000f00c182c42c154030020b01c106000a20b40305004140f40400000d02c140250702c0101d01900011841d04945d05000029481c8000898868094071010626450b0021000302c081ca03001d080c14180c1c500381542c1a030510b5808800c0d6a00c5045c0c00007084003414403c81400103032400741c400d0710707442d603950b00500da5101c0540c01b444400710f2081c0588400e0501c102503040c03a003e020000c590401c0030b400003049403040c441214880903000b040070071142500c20401c1c26400503c5a042110f034158001d409001044a4003881c0d03103248d0001482d00c44e01d1001011102d007403601d001141d40c4ca000d0403141070380700d4406940b01070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 584572374 1250 584571124 584571149
    0x10c0f090501090b090d05150c030f0f160f090f0803130e0606070f0f08032701060b07020105250c0807080d0f0503040201030603020a0f050f0d0c030210020a021009 72
    0x10103510800c1c081d03058450404e5101d151074411800c11140d00c2148900300c0e107600c210b26001d4481c02007441c11f20301540100743c01316264286504054a0400000c0840c5100852402000f014000e140d00d445841c00403810441401c10b5283d00845403000b05070061a4101000a00011041c00000040c41030203295030525201035182c08440080140a0366031590004042c805000400d5071109141c102c544100c00b00302440082d0b03592002942c00c216601e940a0051071100b414008440e2100c060f0701101c4c6008100250070012400c603280964580a4100706003c140401c011190640300f1400704441e06224144005518241e13107140401d0050b03407128002c08030001100348000500e84a0160030703494100b442030010000b190590801002a4109501d8850010150311501a43c0015182d20000c41c07042d942031800348140790020300105030080c003281d00703103202007280c094a180a40398116464608041c00200480c60700c0c00d000006580000120180c0c1c2040b82c001981200300e03130301002c2da1f030b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 584573624 1250 584572374 584572379
    0xc0c0f02211506062a030d14070e3a020a12151104050907031404050f0d1d0f0a08060c090a120213023402031207051504080c010c0f09 59
    0x109003030017809014031002e100300c022001ca020f00140b4411042c03211303000710303400e001140f10808156171a400900e00392418040510012540c0200d804468200c10f40b17241c608050342c60b030803240c115680f00c01720f04940720341c0d0a4041c0c0700301e41c4601c0001c040c0d00105088400ca03107441044403007400d045000c03164220f83c13050780c9075694964040c840c12003c050003181d05040c40e0100380140303004024031000800d903441212040c038500310008103000358010001000c510024240d0030786002d84405c0740340c007070102030507042c2c44d14a00141111070170001a500341042c0b10181c00840e811007441c3c0c100d0440390007403008120304400418080c001e2650102c2e484540c40d585c4503417865001d0b011100c042d400c5802c17201a000c05013102e40040c400710811000300c000c0700030081c103d00d02d00022800382e980c81c0e80801c0300399004e5250401050345c1d441c14460120346000019542c2c941c0d40d2008030302c07840322840c1800002d0300f8420400c0c180c0b00c480611500901c01015094002040400c0c0410208007003104004003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 584574874 1250 584573624 584573629
    0x306040305030714120414010c05040f05040b01091d0603060c1204121107030302071e1d040c0b0705010e06180a030804020a081203011403010c0c0f02211506 69
    0x15802103030980c0300c49203551280c1d0300c2101c1207441150600c442007010440e049524400ba600d643c440c40c002c0d25070710440c0e94001341071400d6821850703a8004214041c017091092040341005602120f90451b400281e20100c100141c03031036003803940030b0341654400c20180c500812074a240da5100701001c40590b1200d0ba14803d0a203094000c1814a40111854800040004002d080c020f0000e08950900e0301c2a502500f01143c40d0100a400c2140107030820760b4100404141101083c9002100d000a001d80ca400c0ca144062130001c614076084040d84080e0224051000c1e400d074403c0507203182310706541e450300c450600602900034410103260a01c82d0a00044584210f5001000da96203100060b11500840340c40454404901901c1680d01c0b4820504c00180340ca010806ca0840080c0c40a0a0784c496160081d4000b246184900c04bc1c001c6e41412100c054440d401420040d200d43d1200c51801001004c1c00814a03003800c12800800000c121070040010442c00501b0000080b028205070440d903031008203 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 584576124 1250 584574874 584574883
    0x33f1c020a0e122b080f0f0402060703180b040e100302090c07020a05131d0a050607111906020315010e060d0b01050f04091d06093418050603 62
    0x3080000760064120400a02e00080044020352a030400c4402d00e0146000444c83c200152035180c1202c0090390340c0c8407100e500008003030b50144451420082518103030b10700049581d40140b0007440340400154040405000d1300503a0704004110100c8844130b51100c42000d019441030140c2d600503008400040c24100002e031000307003070b60780c041c0c8901415143d07044c801c01c2c00e401c1000106d0784445000d002040c80e440350108290b10b0220f24001280480c90103400100d140b150382d1309407106802000b04500418000101d064100805140811900e170510034841d0600c001400d4003103410381d0001c0400e0900402c0e8000d98000c0484030781e0710445d11040001524048074004103150896414418404210b00c50751120f68081010705001c1d144c0310720098001d003943e01c2504070105546d45d6101c802c080528817100380a07040300e00300082086091445d503040d6200c0c40b5080303100b032036a90401d5903400c82340c01c40d03115145989a005941c600c2a100d210100f030030900c07204030310442460310b00018424540080c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 584577374 1250 584576124 584576137
    0x1b150901020a02070504020f040e040803011509060c080d06080327040903021207081201081c05030f04060b01020c0a030515070512071d0a0311090f0105033f1c02 71
    0x4000f0804d5601c0d1006220194108400300151607005010010344a2402c07400e0a00c0380d40f00e00b202c5566503051519000400240c03504280030410458030501150b50001d0300f0b2070f8002c1e085805661500c10310500100580082d803c81c0000d4080840c0038900304100120020413a0618004502c1507001d190500041300c1d00754030058010385c41030035030340b8041c0b8042c07000f809881d000f2071800d0700d0102001d004400340c4030280d20490555005e048000318002c402d03000e4144142d014a0614039500b040c80c041d00c0c1844002d040a0f1889645114a6503281c0c020040312440c1040a0800150240c1e241412519022910702d0012903807041c0000a070b0044c130460444248048091241d4505c3d15000310441d00d5217523840c6007404c180310200f080c03400c980d242c45203000110b104811010b452021a418001c2c1c2440142c0560701c1e40003a180107100c140d4000c242064204203030540300c4210b00b206048003158800380680d900446007940d01541481521100401c000000184424080781c0140b15880492042a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 584578624 1250 584577374 584577377
    0xb0f0f0105161e050f010b090709030b07020709050c040617061513090914160311010302070f080307260408040e04020f030d02160b03090d0302070201051b150901020a 73
    0x402160018020b18a0b0010400e0f000d031000c1c002484007402454420107881100792015804a10100d10707620090080850b4808155039500c0e2508240d1f102420b0b60401d130000500310240d02002403106442008000e0091241c4c680520480c20503103116403059205014103c0018020040d008a540f00c07250814050440a007055060034481c44850503260081b52f905c011000b0a80e000003030130b01a0303000b40d4801c0d50240351040301c00403034822581e141464010002c0764000c844031041000c00c2c10002d40b00d500d2082802c0150381d4a01c0c038904942e01000c81c010051014001005001c452540145c40351000c0781035070328186207901c558036131343c4002400301c5000388081130400080c0100701c0e81c0450250400c0c40030b00300d1110350360f060000034208160f44000e0401030380302d440c42102000b0307610041c4004106000c8a07614500388215030b143c4841c84000703004185900001c0080442e4824001c0f1790309030900c2101c4090b050100d0503525203c51000358580b00b5224108007061a0b804184215041c441c0745 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 584579874 1250 584578624 584578627
    0xf0609020f030a05072007061d03151e010803040f080303040b16090509041a07212a02010507030506040204080604170d180c0f030515040f02040204090b0f0f0105 71
    0x90f0071010000d03141c01010700d0100412000c401e41c41d45101c40c0052940c020b0000901425400e090000f801620510780b090700e40c0c5aa480c00c0030943e01e0204541c0d030380b03012000034070444d9521040741105101d08064490180380f4000d000091600c40480944283c4040702c060748142ca40e95180355a6170301066401a00400703030500410b1218001c50459000089a8109940695a6100000c7c0d1150302101e00390782c00110b07541111020700321010007075402109070074140605407061010314507030311400040c0c5003140e40d0382003032015a004800700d00c0d650440403004000c10804000009020b040c007a0b4070700000c281404007146a601d401d00a44056131034400003400140c1d5992140c00b9888403106a4402e0344000f00320f00701c030074801e0340540300814038142c0c60443c42c40304601d000500a61694410000d09100035401e100042c000300f81030701000c1d180d40c40f61405440340e040c5200303414002c4000940c40351002500090327054841c0c01220030490308485205600c00500d0a012051a8031407065000410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 584581124 1250 584579874 584579881
    0x102030f010932090d1e0e130c020318010306120b0613050702010902270105090406060504090c050f04110d0c030b040903051909051c240f0609020f03 66
    0x440f07502207020b030f55180301886100b001d00d8105041030107180707411403440c4154808018a04004101c69410701005180c0504401e9040c0050b013000241220002c00b0082a4050b00600e603a459452110001106000300601d46910f903019503079038041c400c41900d01d1484481c1000541c004e00c00c11003195102d04680550301c116964414819000401955001c040e80d808502d214015210b024032404182d000041d02000500402c040c81035500c10f200d84043d030002a0390440740c5400c0d000360440e0b20a5070002183c2d101c40ca481d1010b00791030b401c6075820a213850000342c280800170381020110342c02902c500882d4103248080c0401c1e00d140100828036540200010350074502c6990142c1e110011501c0c00060030a03140c0c0015040d0b801d0000c041e000548089034804603446c25401c0c2c07401510301800c0407245c0c50f1802e40880c1d0300007040504442c0960045002e40148080c507911140000c40012601990300c441648070b500811020150702d111030320301400441c1d82c1c0107a1080718060b041c0c807444282140ea = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 584582374 1250 584581124 584581139
    0x1150309050703022701082127060c1005070909020910050306060f0d06090518070e0c0c030d240501210b1002030c010b180a0c030204081207020406080102030f01 71
    0x185180c40c884807414400f02170031220100c01150182ca180005020040d107400c0182d402d00d01c0e03c08407810300c660100032001ca5000000c4000318485024803003111580800e0001a140780140c40c0d09082d40d014990121404242a50003244a20203c2d29444079a0303407920748210490117000c0040341c01c020f114080c07840c020f0240f405550b200000400443c50700850340000030702a0400d8400b40c0e01c090329058148407400c298000c0c00d6200000110000b0340c00441b00384591b4031146446018020000080810ba9044641049036200440380c0c080702d991301ea02c56118001840300f41c40b50941c486110100c20400d4a8182400c01210030585d112140c5803180d1007a92a20100e119404040d00e99a1440d802c440d16840603490108400e43c02560303c82c1c50b644030203800c1d107088201040c45030202145084559007844001900010011000685c046002e0401e038024421038202003614822000341d6008a0000402092040d200742d0301400500d5440704414281d0009840c0c003129801c01c2c000621500 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 584583624 1250 584582374 584582389
    0x907260604180503091c080f0f0702100e0a080619021c0903120f0b130e0a020a0b04170f060610020a0b0c03090c1f0f1e080115030905070302 62
    0x11000500001d00100e03a12128030100c046160220390fa0b0700f0206020003185010601401c1c0c00e071200503a2110a40150f07a03031821803094246410101c000811545620b240b0329064808040c1e001e0f00d240d05400402e01c015040c43e00462401c2d1245004082c0403802c11070220744503004404401c80fa0307246400e41c00e0782d88081d4103c54010f110381da28406c20088044200d02418004900070340301c6221100004850000341d411410b4881c1c030043c1020000281c1c0d8841c1246100484030314440001d44000e209206030805000000c069408403100340b010810100c00b00040085a41d80c8030803403045691a41c000741c0710718010500007441d030071480000c0c00c14107000380110880d901c40c0c4107aa40c0d40825948484499406031060040c040300401008140d1504200e0081c20383c004440c044000c1c00100810101c0c8060f03000100d080000d80c4c0e500295417805a40810b0944042002c410420100f1500040418100b442410000d440c00c01c6c2803600705002e4172a0701d440c2d42d04500a000c2c10b6045400703001c00c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 584584874 1250 584583624 584583631
    0x120c0f0f1909020a090902120121060501080c18090601030807020a03080a090303030b030c030a031110061d010e0c040b030411091f0f0e010e0c0f0a0e090726 69
    0x2501c08802503201c0807600140c079020780b480080041e214005014010101d4426400888030380c5e104005075680c10000528050454200c844115611002c0712101c6030803464102c0001c01282c10403001181500000c00c41000c081030a40302041c1e040341c2d10b4070941d282501542c0c010030540040006001060040300140314aa001500d07940006540e69100300d12540007a1054000501c1000184100351b8107008014210000318010401041d0400020741c6174441da036401002d1080714210300c0d10303c50040c04038502d2a81494401c01c403555a64003684084100640ca00b62440c441c100003141900c007403140385000c2c0100704803050030702d420b1144403030f0039500c0034201703588080c101d5140440d41d6440340e180c140b00e20710100184060f10031504581110f4580307500f200c3c42e91107000302c003840f04842d030410b090b046502c00d4800c0071b41c1d911000c589540134401c05200303540380c950015544602d543c02c00d4044064500603158405140d5070400700f219012096200c06155800000041900d41c0582c091702e0340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 584586124 1250 584584874 584584879
    0x40311030c030a060e070b030411010e1527120601141c030c060e06091917070803010e0109020906090f04150909031407020f10030209090411120c0f0f 66
    0x10009032007000645444051a022500591100d890030505c00702032182c08000d05080a0441c00e500f400e6840c800308641101078141044140d90144409965145100d0f8000c485010540c1d0399001040e44c0002e02004000611120030403c075103040d1900f4001c410003903491107000900320a0f402c10030760025103000303640b000307074400d40103003816001d001a0600da200c130520036140c070070104407149000e4040c0e500700c642c0c3c4641070700a041000b2065001040343c160040c510104040c107010350b8905501000d15000300081078541c0072654208200442c401503058610321300300f10b0000d80ea541c42d000180e1041e0327100241c0200d428803081e152405c0c0039500c00e005034002080403400380f0303503039000c5068403180d0381c040b40c1c81a80720104642071607042010740e502407a040740030619004040e0049a07460003910100d5004080c501b407440b01a80c403c0e410758000c18402406003015007498148003114030b0450100a1182100c0034924144140005650520b0840a4698000c05880408200e030400700039050300d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 584587374 1250 584586124 584586133
    0x12080c0706050106080117010603030915020f030d0e0f060103020105040902161202031308060103021c080d380f0405070e0d050a03141c02091f091a040b04031103 71
    0x241d600d0040314040c00890343c0e0030340d00f90f16086046122640307a040c0a24640d1422005201007507101e0a02d405442070940101c9520706c2d03110f41280b42490000035032081d804003081082c001d021071f4202008100050040f104100c03c26092992601c200303100c0203000c03440030441081080119000f42058803504412140c140e40d140e01c0c1e6480041c01030700010016040099a0850704000020141c00392113444028030882d0b045238041941020f8070500c0078a5140200500b608200034141294000c80d4101d00034003400f840b24034004031000e414840035002004c1240d08803401c101600154080480c000c051905501c0b0440a0000501c3c000e08000100a1031400060039512070009064034103205000510801c950383c18000c1540100140741c00305200c0400000300000601042c000045808400040c0d599110400007050700d81d81e01041d011002c03820915060140d0480d041e03078115a101c088100a40c519021980c80038401d034010707a26502d10034032083c0302140c80c2048800b00038001504030b9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 584588624 1250 584587374 584587387
    0x3042702070501020d05040c0f0302010914030a0c030503190318060903110118060e070302031e0c0a091506050c07031403071e1109070e0d1104050a0b0a050d12080c 72
    0xb5080e41d008140404059480d14140000c0002100c0d03040002d10361101d54034501c07410355000800940b903501c138004d00c402d801501c110695405002c0f402c00c03640e0054450443ca5500c3ca480d549a82207890031104111901d0f0200030120b00a000e401079102c03d10001021005595460300020003483d48280e041001c0001150780740d90003442004030803100350390708112161151600400751040310350010042c1d0021002000180c800140240c188002004120240c85204070401e00e481c1122609541c002c604450026114040e58880c8564500b080e1240e61078545800c016070344c034402c2c0e0101d80d600351301101041000c03680c22000115030703840c42c900b9245801429119061106007510200500000b04007030403003042100b0300c201700a01c006440d900c80a00d0140c3d005031428030404042d0380100344c1c0456500402c0203900fa4401003010040041003281050701402006010f5819a50f02500080502180c01d1a00b0118a100075034004512101d0261a0f40308541040313001c1c100910089060040c1d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 584589874 1250 584588624 584588633
    0x80f150d0609150609201b101404140f06130804080102030c0a0801060e01080f0c0702030f070609060519050a02071a0a0e01030e0c15090a0905070905030304270207 72
    0x41c9003000e5800f21002c902d845c10845008215000e01601c42412110700208180d05a610070503100c188010340a04c1d05101c140d40c807204c1c10803002c1d00c81e060f002c503d0117400c1000d01c041c03644064000c50003a4031800c02d412600b4510340e951300e2070503140e2480e5440307900050b4880743d00340703107070803401e441030388198102a5141c0c1804d00ba81c0098840c503000501c0072440324561903024030341c1801081a4600300c00011000400600303200300181c030820341030380000c000035450300f101000c5880c0e8550103030455501c00403081d00b03940c9848140c00342c0c2380091a01c00001030900d2144058070028030002007141d6038041c0c00d1000740d5140e403110850209501800f1800079801a100c01c0c1103e07140c0d0b65030300080d590f0f80e8000d00208a010f0180001d41454a00041034905d510002010b001056095132140c0700c2c0f1820195a20300c0340180e5060315800f04001c040030903840851340020b4061600e5441710030072103443d04101503c0340110f002d00d01c001e1030748110410300e0800088900c81d0002c0240001442d00032180c45 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 584591124 1250 584589874 584589893
    0x306010306030501321308070c0308132105031803070b030901090c06050301061706151303020f040c02250902030f060a150c0813050303040e07080f150d0609 69
    0x1d11443d40201850845002c804ca58051141c09005c090101c01602d800340126642482054010342550800301e1784400b048800c5070b0700405550841041a11800c1121080c5040d44090140300e88442040100703480c01c0c2e00180d184400290301102031410500300032000c0070700703001ea10502a07140c410043c0010b1903144540c01103014400b08070001c80c00300f9050510350403504d1341d42d000c40c0421408000411100e81d0115001c45260741820403030070f00d074403000300040040e028032000900c9400000307221810940030342000030840303100755001c0070300d044080104400ca540e0a00e0801c0075070055150704503a5042036a0036851081d0792110111a0382d25200c2c40c904907003044a40010f501c1c002000e1001501d000c1c8007080040005e4110080faa003480c20004001c0407000c02d00030a04c030400b180c01035406e100c00f05120040c0201404403030b1601d41c3da00300029180015190500450010b40c0840c41035000310241c6485480d10f6a401d00351243e8007410300440c0707800c403001914030980d01d80c04817000400c41c0f030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 584592374 1250 584591124 584591141
    0x3010501230d0c18080d09030f060b04020a09061806090e040c120f0614040819020c041b080a090f08162001020d021c0f0207030506010803070c05030f0a080306010306030501 76
    0x141c54505a0840d680d008030000529007018420f0b60201000c4006c5560000320b001c140c0340d10040b4030810504030b15042c001380c200d07019116446400031030640c41c20ba034040c070364070b08841e50b65552000340b0341d10b030b403d50303924601600480c0c0c0001e48403403048c0844016000501d030000d1046202d030f00060b550301c418100a100300c890484518000550101c1448000d010b90140b140c1f4084c00620700b42019624090380c0e1040070000c2c244000905c40100c2114002d102c0d0405004000e1700620840140c1d1741c0460904201d6000400441d44606c0420710309282c0744612705105601841e03038881944203841e4522a034010203a5240034070100c1e0301c14800651891011000030003241c1c0d10041810000c0000780c101404601060115440b10b0f402d044146540f0680b03810a05640c05c14081e1001d20300340890030692240c00140c502d120307400000170361060010051441c180074951403003030a5121420161248a43c3c4960203003580908a00b0b0301050030307400110740241c01414002403440e9295109400d491988 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 584593624 1250 584592374 584592377
    0x61e030c111b0a14010e21030309010e19030c11060403020402180a2102040b010c1712010902040e1b1b0105040b070224070c150b030c03010203010501230d0c 69
    0x120740408500f01140803001a004c4801c50b41161481d00000900744003075422054450740302400024841d0455001620b580358521003902c1d62443c19039030036406030040405644461003600c04140d0542654440300c45881d6042d0345405101a481c0ca07821703001c9a51b5800564010010000000181d03203600c01031014a050f68002c50201c03401e84c08010350303145107602884040c103201e950034450300c12010801e0069541103c0000703103c02c01e0401201c0d1076045260003031070083c1c5011010000e01060780604819402002c400125a8880e8180c0059000350320540403a4071690022030605031680080301c03664100200000d080103801002030400a05505409519956036000d20041c0f09036500d5503540240d4500087c1094041c40c500c1c00e49200400c40405440c02c0032a0124216500c0780300361142094201d44c0c0d401410100b0082da4004185904011713129108103d0000d156080c18020f5a04885051711524003c0f0080c400f6417144006007101049407420411024640d92040c0c459046a1184c9 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 584594874 1250 584593624 584593663
    0x1226070210020a11071a091302040801090b0a0c090e040b09010b040c030212010b030c0301170a06051e10081209040605060a080105010909060312110c0a170106061e030c11 75
    0x810304000d013000d4045d00101c9051b14621414590b006030102200c064080a403004007240607400c40c980000d0046400034480f0b035003012040c4e400d222000c0d060318015801c000701003001000031081600c00c81568451704d40c01c084540001000b00c0c15140d4802e92003070000c400803925100c035000040449200400000200c2c1d030100d0b4660021508a07a0103014200c43d9004601e581800110302120307000500c601c4c0c0d8580701d5003280e0026810244140e85110741d010b07800b4800c82c2844980e10300c10031422000303d0940010040082c58543c142595201154090030182c0758101c40f0b02011000c0390710000196400945505000807940c41c3d0500a008990b0f003969402519414100010030003802c42d4814020f650030040d00340040380341095400000a02824000c018100342010070341445a010040795001009060008410381e200480c0041d0074041802040080c0e21084103030361003880c500c50344030303410650764080e82468002d03401300b1039600090800008410308440081d24042c1c5170406c102200d0310 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 584596124 1250 584594874 584594897
    0xb04060e0102010e03070204020c0312040c050f0d0c21020a090b040b15030601120b0d03080603120c0a0f08040e01060207031b1203120f06030506041226070210020a 72
    0x203000203561400c200901c0280700b512642014180e0704d02803490007078820365002550040b04102041120041142540f10040070b01e05401c00c0d0301074420f039124150003002e218001a07124505000280d0304107034001011060b540c01c1480611010050b0745101c0b070001440304100025030340e078141401c010305040301c010901c0c034400020701041d101041c0006008a5091304c1c210000e5000005803540f01d0400c1c81c101811190b84a44580500032049403160420154013031881410b0b8171030150361040390203400f21013680408000c0b1140c41e02c59006403035090b03001140061b0004140b01c0c3e15003400d50154820034101504c500c402c04003600207a00c4900564001d120800030045e480300714035103000c0c0d0401800411864183c403000303505079a20340242005100205540d0802c002e500440ca400b04140301003100319144e01d07007582d44600540302610a5100d140b03d00150500c120003280f681c10001c00030785850a020061526850b901070843d000b5030088030f40340703500c10900784081d01d1604280c0da101440d0f1341 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 584597374 1250 584596124 584596127
    0x50d0f02040b0f03160c08180a0906120605180a020103110c1c0e041e0b03073b1b0d0204150e0907020111040b070203151819050a0303050703150b0406 66
    0x317041c0070b060017800801c080580c04286560155001c80004082d940c00c107514020000f0850103141d005448514030704000860040c0906803c17080240c401c00d01000142c49100462104485d4000440b1850307203c10807550055100741c0220204401c0c1c00c540c103041100e00041681817400c0c0c080d1210740e040e80002403c4040340c7c0010107440d80b010030703501001a02100e42642208421110680001c90784599500b0f000da2010441c0b40d000300001019501c83d0591000c01c1210803000d0f40c03428080f442c4501e4186810508a030045000f04540c070492b02003800c902503420090f410001c1ca44480f00d5091100080001c50340035180f07203548260303031020140a01241000b10302c5001909603802c580c980303180c0c80c2030300024000f11415500b80c43c0849071544c46510000789401c00002c0300707400510b0050306200c4414420306024001e03800607001d455404003003004614160f80d40c94800743c11a4494010280400d009a000300e8000c181b51130089409942c11400e44182d01144d8800391003000300080410005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 584598624 1250 584597374 584597401
    0x1030803072304141c0303020c070906050f09220302030904141005120115090f0c08070801030f020f09040f0c060207030206121e0403050c010b0a030201050d0f02040b0f03 75
    0x40203000d2440000001100d41e81686026030f02030b00c4102104044c0720121580d524802048580d03140201100c1410546401401b070741100b88280254419030001045154482c0111001d44201030f11f20f1180301801d004214000b200070b80840c10340303040004600207641441d802e101c0c1ca1406a001956181e04001c02d1004481c41c03034054903404490b084c01e0001805240910314200d0740c08441111001511109041c014828480492404c1c05502000114048160046040250860030402801034103072000c0c4c0f06e2040c01c541d000001008130b07005000290703030440710705090780c0064519462600d5080c042140b440b0252415102102520030a00c108240d03041c1ca14042c0080d88040c0480c01e02e59030105020f8003603551000c0003104036800085042c0c400c07900a0350880b680f0b07910403584d414141405041136100d201c81b0fa4065080075078880d00307420043c81e884102c0760f06960342e40c6041030034418903000701008401d403000709800304030026243c1e01c0c10001e0400c50400c030400c10b54a0070545c9040040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 584599874 1250 584598624 584598647
    0x30d050c03030406050a0b04020406090e010f18020f0f0703020a0605092d03190c210e1002011104091a09040f030c0f050a0b0f070207140d11090103080307 68
    0x1004000c010420301004040262604981d100f00d000c1510384401d02c12002600c40501d459801c00e01c040350006000ba403040c500342c2141c5024500440e140d032103041d9150100e04501403442d4400e0140b0f00440b12003106c1c0d006207803a170300c0d642625040c030030f03010700710071081e40160740950050b4040343c50801400320b14400c1c2070708410902c2c01010300a00200503d003041407102c503071200485040924a000307401c00c0c012a05041c141c50341460b08002a5a00034000d8040c3e14000d0ba28a0350b1030003200120400d00940c0c4800440a441d4140c40035030007410091030745602d000c410704554a40b1241100c8401c544041e0001e0420a0004181c0c0d0b81510208028052143e213044d200c0ca8440d401d01c404202800818900c003901441c10b003000c000c0c07504200c00500c02c0414024800e2007510380301014001801e008900454551420180310b48440104a070f8461883c0203443c142d07850320010031000c1c5402100401d460384102c1c0d42400d0800003000061221409074825685600004100902154094508000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 584601124 1250 584599874 584599877
    0x2503181502010c02070501080105060d0209121c02010207030212070203010f0f05060f06070b060d0f05030a0f090e0f01181103091005010b120105150c03030406061415030a05071808010605030d 84
    0x1713a071a01000a1003610184241409030f140010b08603404080c640440382203081c00703854501010403400ca491741e40c03c0c1c81141181c03100d220910104c100c510600031034036030941540c000c0c80d2401001294204d103a000741d5017282d0543d43c4200c1c14514444900480081483e0700701c00003044d01d440014030000e015001006845020100b181500280f441d0700450340140041d11818101c00662400300c004140c503004c0980f6911020a0b00900a41d2103421410000225600c1d01c011555508400c022000242d4110001c000310304014020092440030301400700c0e114010124400355101c50415059109030340350801c58000191540884100b802258014881c1c40a07007032914414003180b00b41d0141c1802580d110301c078444150300d000c81d010070039520f0126500041e02c1d500d08203460000c00402c21031140c03040760003220321581094500b901d041018030f4003129103e0306d5642c0e5400340d075004042c01410102444a9652414881c411012903640601425400000c00c98200010507150a070342d10381000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 584602374 1250 584601124 584601133
    0x60e0105061009031703101a0414040b1e0a12050606030609070810020913020a0806030d030c0f05070212060403180b07170a03060905160305010b2503181502010c02 72
    0x85c401021401c03d66814102c0d280c403034480912541d00f9200b181d0280d99108001510b546c1d68440c40c1005000303c4c3c000c0c10b002000c20020f0024001070315110b0ba001d59000709510201c540c1c0850344e0071200d041c4140100880d00c81c40c0c803035141d0218100440c10584495011004210380340c1020080260445103450051074818030300103c05035100c00e040c0203100340503004a900350f490b403600100b000c2c241d40ca081d4150b40756000b004000303050a204451031403091080c000c480c0c4015000303124056442c00c090f500c40c0e0442c1c0700c6a9082d506503101180480e004401c000300100480e1041c0041c2d40600d10130356130340712034a450714404441415680c01120040070100701d000000b4064681c50009000c150112135160b4946100c02e80040400d40d0140303c100d800c000811074241380300314800320340184c1d58408102d142d880320b80115042c0181032041c42d540d03101c01d4858842c030808003001c902141c071905e0410058076500d0307292110003155600000c4038032441d0a088444a4080c041c4552201e800c0c8000c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 584603624 1250 584602374 584602379
    0x20606150a18030b100504052a0d021306120b0d05070506160503040b1b0f0c040c020c040c091508010f03080f0c0d03140108161401090302030f030301090b150a030b0d060e0105061009 80
    0x2400b5a80c2740f0000349004c0100018030b03c01c1c03a00c281e0143e03400178030402c84102c0341558a1001800500151421418481c03421804804034507007000d038102d065400000800b55541020240035140e40a0bc00910016520200303d50020b1000c20051000d0320115550980f141449110034540380c0d02d55002c3d09035900608a4441c042c1000583ca04a4660458001c5503d901c0310b2000ea040c200e6249403550002c3c100310380e01c107009422049500840741141c000c40c2d41401111022135840701d0a0141c004030b13031032903401040418090310103401c80003800f07034260b46007043c004020fa25290100c10f862010076151709458000d4079615220600410641002d001c501c00e000d8000c010002c039601600310707028982d40c50807a0320303403142c4800b0002d180e010f0126000d40d0104100c00c1e60340d80007441a00d100500b4024641c1d482c0c10502209030041110641c01410220980419005001c00d0320095400100c01c00d040400308410f80954404030382118000901404d0603024019840f5110030420184000b26804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 584604874 1250 584603624 584603671
    0x1006120c052b030504050405073f0905010b060301030c08060a05070e041d100906060f0b1c0906060e04110108090d0c0c0b03040c06020606150a18030b10050405 70
    0x5840540c65540c1d94419a0701851605441c03d000c1c3e901b000e6002843d0208200c4170540215484405001c0412490111180d03006e5170501003440c10341140d00034140442501071030754103400c4952418880e03000419a1010400420840d810036881924140d05902c03007040b8800082c07010a81050380c0d103000b0710030b9103004c9030094104017064103014041c0d0b94038240301c00311751000f10210700710b01541c8043da03400b0041741071400041c1c8a000c0090341d00c03901c0e04200003a0700701059403000455030a000660b00f02820858541580a24000c0d6800840d1f211000c540000700e25120322000ba2620300f142c1c0c2100d080c2800c20b000200345144205041c0300301d48051020306140040c01c0c2688844070728103281d07084054502030f000341400742e100f811911400300a220411081200e8041a510740b40c0c2169030b15a94003040202105044080d0201c4500400c4001c4801e07220340344462084204034182d61107156642e07a500c84010080b40c60741c40b8480e8a80041c0a20710f0030740242741e08889200007486c0e40000398100d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 584606124 1250 584604874 584604919
    0x201060b040b0726090906090603070605030a0605040204060309110f060f09270103050f120a0e011e0806040c030902060406230a030b12030304120806031006120c05 72
    0x141041500085800b404024120344000340380444c8a400901e500f015144401ca030b50040000a072140140300b00090070f508081c81c00504c96800100144100c078036051050359540c3c4090011f00840381c0342c0402041c1d5032036900090001345030faaa00043e680d0000d007004010515006801c3e4400d83d03566011444d80c4d90b900f0203940080b061a100c995541c00c0e48400101d035a11500b07444034004e803842d00248407102e403c14085040780d004009441c64442d11904581c0c44886144030b458140380180000400300340b18415a0791a4401030500c4600c19442024100c11400c000003682d0024591408001d901c0c00d00d809a04010f0a030750405101030031041d4005405402107001d5081080702c054a14400415005109024545850000b03683c03505038100040281080600403070240d030030650280346001000045902c602d412015117944240c81c4201165610740103040958540300d000307550742d6210560b201e10f00c0106001e0004001010f283d2070105003402041c0e002c40d2158055a450a060140462 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 584607374 1250 584606124 584606129
    0xc060609021303020f03030903060c0c01060b0c030f0a030b131e0b060d0902030106030b0f0702010605010806010c02010e06040f081606090e0f0a0f02030906061f0c0803250903030f0201060b04 84
    0x120000c05e9a2038650110740b9601481d4000c55040c4031781d04c20701c440b45140030010154010540024800700e41c032030071800d00500c01c42142e4006588200060b030020000780014180c0081545800b050100002001558100240512a10709907540320040d40e102d038002c001c105802c0100c80240480144c0000203003042c000d0b407000305140d688500850341155420751108000d0f683c0300ca9001c1e158104101901036075031088a01030055843d2800c04646580910a55480390070705a4032801001829401198141c1c4020b01e52900808144004600440b980306a00040c0400100034400009001014101034010354448428812102000c0c44905a00416030750b00c001e020004480035110000a04000d0a81d002c3c0710201a102000340226004003090740d900501d000c1300e030003068699404401c550380540c21360345030121711180c0c681b900040d983c0c4055540300d40407a5152005c0d203842c1c260819006c1d0b00400da2000100591020700415410075141000e0f52441d2000308001303428900190540d220303e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 584608624 1250 584607374 584607379
    0x50708010b2208060c18041e1503151515052b02071a061203030610020a0507240203030f0c090f04060603050a23040308040201021c0c06060902130302 66
    0xc54000c455a00070051034070042004800700c1c1d619142a82e80c01c111500158141c80486c0f0101c81505480d10341030241103103100040b039034000d8030014142201c00809840c2000710340094844000408510300f51524022441c01c0d42d8003041d0103070300320801c0b1001001c9820240380058070950009940798000142c401d205500905110050114100c0600c210030701000b081c0324a00010300002005800e6030004c0104203054030b800c00581360f130020480c0c0341282680280c070b40d03401480003880c946441241c05040c0303600d074010707151045500e4552606040240d001801850800340e64200d240c4d040c1d1101d0f9000d441c40340301442c2942002000d884680d20050501c0c40034180110300340b05160346d0181c00320340ca258001c00c108403c2da134406000e07001d800121003d8402c1460f00740000c00000148050a680118601111250741d444da9415070b141c0c0000340060381184900c0c14840b04600412750301940488103500c3e1480300e03c50a00d0300000b69849900641800d40c0180f0141441c180644086000e40307604 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 584609874 1250 584608624 584608657
    0x91a04021c0c020a0516090608010e120906070614041115071106041214060105060c1002131d040b18060f060301022b0b0612360d0201050708010b 64
    0x440d0b00403450301c20702e08006881030040c0040b03c00c078090040080000c50f40c402005206040d42c40d00c2c864201c501d0124000546d4000440769215501142c0003000c0c030450060007581009050303221402118210f41c141d0b884e150714842440180416241005c071044801ca03041050100031f036003000414082e00000070213a820008154406a481c901540c01801c0c406004644400740c03414420341ca600303041c14000550140304000320381c0341028001c42d80c0703003d21341000f482c0d00ea803a828214000c1d0711009481c0010564594046100c210306600f05921b025041806002801c00b402e115540c20b40c05820441c41d071360901400e8003134a07004544250320400c0d042040c509581c820001ca400380c4103c458801000c000b0311076551030780c1310281d665403000c2e40814081290301003403001e03c81240306082000201d4200076002401410f40c0c01144048100840c00c4140c100c1d644000d000040301c03210010305266040300314000740e2180c0c2441511b600103001d15110702107500d40404554280700d102080005d8548 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 584611124 1250 584609874 584609891
    0x2130c0306090c030b040e030c03040e060a03050f0a0303060e0f0a020a03090503040f082103061e030102030c0406120522030504080703120f050301141216091a04021c 73
    0xa610401c0145442d082c00d000301e4040040080044c071040400318402d621300040100c0c0e10000209444246074450020f618003804c2c03212118141c90020b10880d4442c8800c007000c00054028000404486c1c1c00e540100b01e13a801514015050760005d4000d00a0b24403050b04018214015140031070304110003a0300181c0e5495010f03c00c6014068032500540b4071701c00001c0001d0740500ca075915500701c480786801d07582101e1740580c01010081241003c1000b5400030f0000c200c0314a03004494000510000c0301e98684903944001080c02ea0300100d40e0020b1501c8049010090711b0307048007500d82c40a008042c00c21241c900500e280d005500140380300340e509004107400c0c400f01800307101102c014246105c1224115035403407601510300014100003000185901c1c1e17201500e1401801900e042c0e031103230050700c06009540c205000030f190021503900f40b544205140d03101c05000c4029850050841603401107810080705048a00c18000c801b46a801103104029131002d404400000c10030100005001042036003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 584612374 1250 584611124 584611127
    0x1308071a0708180a030c0512011406091f030602250302060c180d050c030c011e0c03050d14090c0a0803030f0405030405150a091a09012001060603020d14010302130c 72
    0x8621401390850121080031007880107003070410f03044a4081340e0160144405000860980301c281d48407402032920540803c42e03601d4078880303686d0b000c00f95000c0e00310381065150113145082c800c0c5c0c1c0103a071724503170010f403c084501c44012003540d00c0803d070740642003030102507170029070701e0364014603140c0e62107400300d030454485118000490003c0001070085c071070800241042521105058580e034401d108813000d400095000c1c0e00054a82208200d401e081c0c440e10b090143c03010900d0480c11000c2140c20071140c0c1c80650a8414811100c665400c603824524280010520384400c8610941c402c1d10241c10801c1200c3d030000807650b0180d40c3c1c0d60500303402d4443d80740051450045230000c030ba00c0829103084014112104001c0c00350f94900f80c0e80c104420b80d0310820102902c000c019a00744901040100340d88a500480a2940e605810840c07448849950381c80d950171500d09402c040e0020b9000244501e000134903000e14130300d04144240454013549160300081d01030345450703030105c100c031703104c0d20f0508086 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 584613624 1250 584612374 584612407
    0x1a0903570111071805010e0c0304140309060a030905070602012f1201031a1b0a050c0717070602070f05010206270106031a0a0b06030a090f081308071a0708 68
    0xd9003000c044410325a2104003500d114501c0b1031344903000900c0c041c000100c40d1201101c0310700a1101e0340d140b0f4a0b549560b2240328014464481d4455184400c2005014035180d2800400255013a581d0004d103039101498141c2c00d080041c1d21940031681042c2107040f0112a540c2c500c180840b01c0c20031180c4442d00300000751460301404e0040c80c00010680c00000500000b902d44820608050300d41038401d5483c0c3d0758005212036502061840404180803143e04240610010300c1c258200b402140c9800f1b641e4002d242e41c00b0302440884100d900700120800c00d080d01000182c0107070881c802490296800c000c0000d59800c0f008142440802032500b2140380707042c091000d84030b140011402803207041d0310381c106601e0b22202103010007081d11480703000400304121445200d106c842d0007447d60b8038540301c10301207502514407a5815910754500041c22800240c0c07020040460100361542c40d254540317080e1900d42400c5295100d520000b54116291b00308980c0407003100c01559004074982d0321345d4105200030422 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 584614874 1250 584613624 584613647
    0x61510020703080d0c0206090f070e060103020c010507030b01020d0206091507111c1412071206120f02010f1d19090f060806011401091a09035701 64
    0x1090004d6040040c541640086440080c07a800311011600c41c6425140e80720110071220f102d03600064418400e00365041c0e480c9402000514001d410040510b90003401c5030f0050718100f022076520810011503503014000d05c0c0c0340c03032500c0c001b500c054a05240300c59241d038034101555900729100d10000d10030f5805410440c2d03184042c84121000c401d4140c06c240d10921032151401c0c080b490001040000b8242c00c001c44608102c6034038410001d89814506417400408003111407803654076644041003c1585860a0b02078600074080843e00903d14000503110101c520841820020100f0444250008050300132004213415140e5100d02caa10071880c003451718440c0c1100306000d0500c05c04500744000f41d002803059a244400742d808590740d421103203820300c0c000c0b1096030100750002e1080148600f44010a4683c0c40e05038103551801c481400040d050079035101210070600441360300c844240300c2c4102501c651005403516040d00b141046603050f00300100d842c2403800f001b041c0329100ca00d6485070184649 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 584616124 1250 584614874 584614883
    0x3070b010806041b140907030b0310150b0405310c110d032d110406052d0f0304030903170403150903140c0102120a0b1002061510020703 60
    0x140d40c5a0307102584498050340c00b40e0704518036490030580c41480b1880101250412441d000c4041d540034240218900000c000d4007d0568661100c034194500f80300302c810344056050001000c20940d2000d182c01c5101d07400400ea042400d1000f07006c15180c0210345849038040c5400e001c1c414421401d040800841c02e91845125420a029100710b103402c080c0780c1c0d030a210b0203015103100405045080b01100e07003081c41071111400f1654410031081f0140b111142403009000081961940b03100301000b254040d0b404030b400604009401d00740500031006210626507030350041c840b00c46c03011008051500850850400184001001ca03003010300407030310f210003564000741420300301c00302446d0781a054201c3e02c0261400c0c100a040003804540368800c8002d502d07810349030340c421168480d0720f182c3c03103803c03525400c500742d0b600b0851010300d1480d071610b881c8643d03409031020800b07107040400d109a4480b000305200039540f0440600a07854140f5110038140340055588961512001900300c0c5402d001c0e0780040c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 584617374 1250 584616124 584616143
    0x807030c1103030f090906030f1c17010b0903070e1b030a2003072006130309080601091a06070c210b090102190203040303080c0d110c01060303090609030209180307 72
    0xc20b80c0c1c081010340310010080312001c0e0187d6810003899190f03440721341804025041002d0b500c1d0a000d00188184241299280c15010101020040d0f0490502078002045903c00412002d1407841c00b0042e460140c502c0b400c07443c8560502d1038106e0b4010005540c010903284c40400004c3c0007650f558014071001d00711440124601400c41214080e43e072095480d8000195080448404061030324040384100d01990000d00300340d41c1d403560f140100080e10004074200601e46400041030380301085800e01a0010388000500c9050010700d0075420401c849009024003010b110b514007144415100e141168104803605103c101e4614000c052141b2410004048104060a1110742c040540c00b40c00743c801142c01da028032854074101a80d890065100040005402d60000b0b074001c0c0d454400307000002904107000c50705603102108140d8642104960142d260b550340c00801c203156118500500900d15414204041c3d401d5401040300100010901407041400580c09100382108004503084140c00240c801c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 584618624 1250 584617374 584617387
    0x30b03030711040e011104180e060702070e0703050603060610110d11060a02040305032502060d020a0e100903080f070807151b0c0f051006090c020105090a0807030c110303 75
    0x142c0c101c46410244600403807500403a007455100520407005c5144e041100a410a8030309074011a40001d80d07000440419110006625600010040d041c01a08190090056141414071584030032000510203820581407800f481a01d440c0401e0b1242c010506407440e00028a040b030060300c01e418100582c54452007140f040340103440e417203031505c012894120250361141e1100f580d0380d8143d0080c0d0001402d503400070050250311a1908108003000f114600c082c00e075404458001403641e0b0001015061100ccc2c0000d150342900d503001e140400c0c0c0320801c540c1c2070001d0f030140ca8002c001c05e9480c00700400a235000600c01810882007029151200d5102480b1540c0750300360b1811f110955155030080d044181028070a0455036980d072a202c1c1051580e50b5040309c42d00042e11034004804820071b003550103000d44650080311140900480004d0044450044ae0108040c0320007401c40780024281c4405410a00007400010030700b9044174038031034161600e02c11480c0c290500d0003c010075010a207500d0b1000080301c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 584619874 1250 584618624 584618633
    0x15060e090123010311190503061503060a09030f0f020304090603080406020d0203070b0402101b03030218030c06070b06011b030221030411120c0d0c030b070c0b0a0507030b030307 78
    0x2070140010900b2220a11a02c0c648080d4071514084c00000c1201c22044041c014500340800400d2001d0580c03a001a20140e8620201e403d203030041d1122031000161920071202404c1c10070500b6000305a10808101c011196180101b0a081c0c0310080030810250700445417016200f00251005460080410070400c0da0717910b04030b07082c1c0d44113114100140c041c0720310101c0c91900200945d4107654000350000b26036540ca40c00c0040d480340e40024281031000300d070340c40c9042070210000449024845d8600507901c3d10799440c2504041011030300c0314031a5001c07080010a648640f81070b05c0380b4a500c000908841d1f00c0f210010303105907a5141820410355107a06205003031640c00154203150595105080307041580c02101d8007803603c07003282d001d400c0720101d1050005500340b40c2c01e40c50388841214180e411801da0741d0001885840840c00030798071880c2440080c42440a41134055400200038100413000803816a903140324a000142955101c543d81c500244449020360030003100310500901303032503840826240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 584621124 1250 584619874 584619881
    0x14010e0f0d0b012c010b04151202031305010b2707020f0d050304060b100f0c0323040509012103110705041b020d090f090b0f0604060801140402120415060e0901 70
    0x1200d134207042114a030346442d04a40794103030f050b544400c09091800e42030030707820002903415005a8042100509440c0d0108800784003550041001c034003540000d071ba503814070b242034507003058034244100c4403d00550350780307080600b090034103809000710104503031307142441a42040c000c0180074500740200741922103182e501c10005c510551081204201c2c1045001c1807041e880e00128034030307021400c0030703c03c01c403454010116040e007a440783c80d0469600d0a103001c02c0c80841100200d0706000180850b003803240b4540b103041240074241c0030121041144041041100c2082c0301c0c480507050003042d40189050300f01c244031890242901030418842c40c0e03079903842802c050035600c82c600010301407581c50300390151054503040200c2c1c0c0c0c11002001c00b14100098000103210f91104154081d0490703240011680300c0e48050401820700391658803640d03140c003041034600500451254400c030b2040010030b028025491805402a4108101680c28010b1480c40001001e00341c220425080b08031040003440c540540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 584622374 1250 584621124 584621159
    0x90c0509010c30020601090603030806014d060c090d032607031a0307152a021302070b010902180909010e160e0109020c03131401080114010e0f0d0b01 66
    0x1403c42c5d5840e0307a210810340032a000e600005000070380d08004520780398410040010742009400c1190454240045107468080c1c0c41c038204400820302204100d600030409210090420008000d84040e2030840282003075403081e1895948980007040040007030510510440300f8040245190142003150030001004807070084810f040001d003001d5680382c240e107184000c02002040640104009400c1403022200000300c010070300b0402000c00c07402581038582100102003410a0348040108400c5e90040c041402114940e0240b41401080700c90000340c00820014112103040c0310068503003007074000c60130310805100401d0b83d11084034420b00015420640c40504000b821804a8a280c01c007a914464003503003070b115100442400c03500420010040d03030004d1584000039402da919242e18181081d860401d0707501300103030000403804103413402c0d40c00c02d10003800f43c01c0000040111080280000346003800d20b41c04240140c0b40c40e01c9c0410652200b0359624846644070341300c00d0042d07031500c400d110070340441d0717 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 584623624 1250 584622374 584622377
    0xa1a0109060501170c090117180616020348010c0c0c03060c14040e071206050306150103060504060b0c0105070504030b04080306010504031a10090c0509010c30 70
    0x700c0000c19600031500000c0b036001d0460050420b640b2001103c0041e005101101c4c1440b40c100342c51009034411041151094240082c446900d4924410300d910b44a0014440038101c44191010304040b86c002041e685001340208007030b5801645407021641d011144086171000d0095890165824007a40003004001c110820082054441c0c000048886d01c05410000e410060a55024030100e8450703004864441e0703407400d00c0314010070245810b0580340c0c0103070720060f082c00140301031040480d840514806550300d05041072211504020001c1c0d16103401918050a0001588030844564080d8020000509004208101281d03540854441381d41c80040709440651802000410f414002d1003550140c035081400c103100c2c3d69696688082c194409043c1a043c00070900001001821842041200d119070102d10b11705420503500c08005140310303801c914115410404104401684034040d40c01c01142440c04d18045125030420b40e44030448039a5004406c5200203904180c8911036200040b0701156 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 584624874 1250 584623624 584623631
    0x3062909130b090c0a090b070602120c03092e1a0307090207030219050604030507140102130e0a0524010c08070f020a1203020d050f0c16090e06090601090e0a1a0109 72
    0xc00e640d5145501ca60030175040414410101409210355200141000c0c51050390010f140501300034041200d054115034031801d02c1703800000c01c4072003802441484c10b00211041800955603c02f00d00c40c54002c01100300c035640a50f0340e109040d0b5900711010704c500caa00c3c0a405e44641c0d50f110011500a5445a00d0540244c03050385034070803c015014480c0c06480e5085130241085e902c1d160344c121b0741c80e40000c400303031145a242101d409004800317200405040780c1c96111008560700d4800c1c02c88010700001d255000c15441c000401c001003003400d00392035804040c4c41104d40791000701d40040c1e51040d180840900032032400f150240400242540714040f2500803101444095035610304a5413040001e00000d0058020840032440e950081c1d020301000c00030b84124504142120005038600080c03003030400d40340e2901110030030104041d80302d0240140007290190049142c0501d280c0d42e01c100c10300c03410354015503078080384840c02414040c1503801988000221822401c2460340c500001080c056262000c0c82d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 584626124 1250 584624874 584624881
    0x803010807060e0a0911130b09040f0b0f1c061a040b15160201050d050702150a02040320150a0216060e0d020904020a090207030203130603062909130b09 67
    0x10701c0300000f0301400101080502030070031907031802404c076100c01000c1e03480040c018500c515900503a0350000e402c00d0280291640f84550402c003e8030025220b903915103140050141ca0750b2a0300c84904100281920542011140c48052812001c0401c0d0302500151030440042032942c4444002140c402e0704903811302000020404200c3c0804034400302c00101c1d07404200d0400c280c83c85804014505005041c850709080c4e40d03460500580d00c0c00c85641d00160041030041080c0e024683d45140c0000b9840700c21421300e0f0031666001808441841800c0569200301c40c4040d4554540c0803007030315108422003644d200c0400c1e00000c2d54a00f1003241308036020b19401c1011420510542c80014001d00007895079052043e65024443d8810340a84280d030005000b0101140c0300503680001d04049103c0d5008503902c030001098041031340b84a820000425080c0101080312412030040c01e4a03280069407203003603004a0703072601d400c00d1003041003207a081104d0242000910505a0200402c80c80c2651031074429034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 584627374 1250 584626124 584626127
    0xd08030412090e01030b060402070807060b0306070e0604060e120a0c030b06010315060302030703110a05121003030c020613050a06051c15060c060b060d0209030712020931080301080706 81
    0x1182d602034001c102c481e11004102103400e00d10219082800030700014508039440d1114401640090000c0da00d1301c1d102c2100c41c103e0305040012543c01007061902c4081c0f030001030001805071156100c3d000030410740039000d1005556407030b02c0070150242d4a0848210000c5032070110310300c402c144410740300d041641000450300d50080c0144400c0c20341104034445600d0034100e0941c000d42025041c1070415607295240000e440020000f005805003d486103030b11184400103000455200402c0c2d540c01d0300ea40c07002040002c1c0c200f500303206440c0d8122071140e00c03221026588032072500c1c41da0090307600031545c101c0000c055401c035008161010000c0003003a000040b140c1a18203036a030400e80416048259582080205e00c60040841240d1252402040d8004484000307040c40d0490300b01468a81d0f8001108071413440d0407c11280203100104400520749407540000b0f181e0403009040c003000c142c040c8200600550b41046110003585040039600361b1041d1030401c00c0b5940c00074001c842c200c0c41a9030010034030b40d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 584628624 1250 584627374 584627387
    0x30d020105160f05090307060201051008150714160818040203061f2c01030c0c050a02060d0b10080906091644010c0311090409020307050d08030412 65
    0x19101d00180344101070b00784400b200d804011040c104200034003407252080d155014080c500007003000d0350020801d03007801c1d010403c00e02020b6020080540c000b907520b642402150513456401401c42c20440b141c004022803070400313441240003070040b6000a40b07181c0108000e0001401558140800d000000a00041030000700d201c140e56442e44041000c0681800c801d90007403c0345030f2403041c50146260b5080f201210b09113210f03860703e00301c251020460601c00d07581c10720135109510054504240b608140740c443c141c6030141c0d844044c1c040c070f60004101c1e030400d50300c0d00406070901004d486500307062400d440c02810f40c001900c81011900640c000700e40cd2610009000c00c0b030380000c051541c0c0780303854484002c1e00305c2d401d1000c1d2500d0303a0917800259226170015482c87c80c3c1c0560702034156a0010b003100039500b16000030710010103152400107032a205402c00b00036240124000e960005154500e800007034034080b0103500866100712040b0115041002d6100590300852040190b941e8034207800398183d402 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 584629874 1250 584628624 584628631
    0xe0f0708041a0406020904060e041103060c160f020603070c0b090309060a110c09010b030115080c0405060904060806010906260a030c0309080303040b070e190909020319060b030d020105 81
    0x640075400c40146200074402e050310b030828402c00c00140342c00d00040125040e41e1241e8800c0016010000c104002d020004c1180c8a480e00c044014120703524020300c0c1182c190241a16507908814079918000402c10491032070441160002c061588038a0000030041c03920220880844201c03142c0781c04500c80355000829904a900e00a20203400d00403207010032075642952007100003c9104940355641181c6420110ba4081c00142a48a540c3d40c1403c1d22650302c0010081085c0401640d8410410b035600124156000d6030700849400303582d44c01c250001009005141c2103d841b0380200d400000d4285480d91284084078594425900fa13400c110300c03106049402e8941c10402500b14003061000070340706480341c4140034030905000c44c7c0700ba10b41151600e541c00c102c1d4216045141c500a00420a820020744200818120f40c200000300c1480d80f035030a030a801d40725141c00f1030b440e0003050702150b505001c80d690b415506140040d07040100e05200b0040d0500070f20986c028091784c00362041141c81030042510 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 584631124 1250 584629874 584629883
    0xc13030c1e033807030b1507020f06220f2603030402040e0709020301141f09030b070201060504091b0f0b07230a3002060c031b040e0f070804 62
    0x1062102c10000300110762003050f03024502000b90300d031050700400f03a050180c018036103590000740c03100009080c400803080d880c115410803c000d11464005079610702e2182d02499055845541b10308502c060007035110581c241c00034031103010407800308100040001e031004441941150601c5003480280080300c6101c41c1c420518075030000c000040150401e608412080f500807011100c1c0309540d100128103e800c280c00201d540d4151740dc110b02e6518200418500300e09181012011041c0b40700006890742c0601e01c0001c004406440000704260300030740c4580000d2401070028000ea400910b040d140000c0c45000040c1a00c0740700d000454400d01035a40503050f0f40260140501e00006070700c40c20400c030024a0310407100e80b0200e05044580505100300c9460350701c607007200c10581e803091064143c210f04c441404410014444880345051354001842c54110401d504002d0760b0b91200320040741c40410303e09003110312542c006400111800c01000f194481c200c00010000c00d501e40e820120340200303023500c0140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 584632374 1250 584631124 584631143
    0x1a0109060c05150903072f0402190c0203030912060103062706110f0f130501030b0d02060c01060e0f040c0e060d12020a020909010b0102060112080703080c13030c1e03 73
    0x3c4001c40c03001d00c203030030019078401c0302d04045c142d5644085000712002c244940c46442801400d4102c20b0b04260030b03a2003030484081d0308266500602005681c0010341484c10040340c881500150b440900c125010080050400360070380102100780356451100384003c8030107500c1c00000005510302690070315444005143c884450140c1911610040c0104014520345008200700c80481d48190000810302d181e034580075182c50f51034078101c05403101042c1d0f10840c140740c1014001ca0301ca954000202e9082e543c102e0b20b068503031280402c010300510b031315040a4015091803060005040701a00c03140e210f140320f4101c5220840c0c603211941310580d03083d01d00c03e802c085035140303610020b1211507400d01c107903030f0600c1102d42d0410141c00050344944160780100042c0d5503001d40c014103503414490213024148102d0201c00c4d0f003c50b543e072094544160f60029081101d498041045182e100e011901080d0144480d400d1840c1c403810300c05650b84851003140080c001d03901d00c03450156001249030086039040314544 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 584633624 1250 584632374 584632393
    0x62e0f1106060918070f090b1f020303130c09020c06161e0807030e06181b13021b030c03040e0601021c030b030c120d080f01030b24041a0109060c05 65
    0xa001498070401480302d41e01620ba800b02d140c030001c3d1140300080844c40c2c004a140c004060034064080c00d0300709e8107603501000303104c0c40c4900c98001089a0300640e00f245004101411420100e00b030061a8010804481c00001d24182d070181c0000c8080c02415213441c010860784417201c050300d0b40c14084020210002da000100d84415003d282520340c062030130305001c20201241e0001e0740c20140d08a030402001406040c0317032a0510f038200324402c10000c01e4010708204507250000603ca00d1022413803060f03001e8000a0340030090040c0b41002d118401c1c08030403280c5441c50006242d441f50041c0c01148806048a000540d5a43c0b00041103c4250805c00703182c48560100c103802c5014025840215030503104441d03018545403034020310000741e03074001c8002d46407205002c5c030b008200c00750103010810620204401070020414080101d6004100000c420340003140b00001030f44151283c0e800968804d1500080b651201c1c000c100315115403401b40d030741ca411540c0345c03101540c081ca40060064003962201008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 584634874 1250 584633624 584633641
    0xa15060c02060d0209180a15060c06020f07020d06051b0405180603120d150b091003050901060e01030f050601080609100b0d0f031106060604030b062e0f11060609 71
    0x52602c0f0b82110801340c5018664004a40001d85101320399100c00b0b1103008109032600e181c804e02004030800c0001c90b040d18a00b40c00107000c1c0c200c202014020550000e1442c000388144000c540c00c1e907501800b001e58504480c1070400c0205401c50303241842c1050b0313045044209849004442c1074840c0106120301c140b2511800b20b14a480041440c2d81510401d0b040c0742c0080c615001074100c0402861010034008060786507200300134826405164103400c10300030016665030f494ac44007000c100c0351500003a590b90703001c184c0e400b5140d9030348110086c5c0e000307030000300138004802944110103001d00c2c22510300740d80c1c1f881340790b07a80c007012a458102d0f5009000c0301e040c2030344540c1201004c41002001005454102c0d01e40c190b82000141c800c8022034079541280c00060000d200ca240d002034100d54090419155803544003003000001e25a51149030600030b11205030b100311040c101807072403a0082e91900e5041e12400740070300c1c03980d00301400800c001c04540300c2994000a111032044502401c1c21095032a803c14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 584636124 1250 584634874 584634877
    0x1030f060513050316020a170a030807090509010b0405010201051e0a0905011b090f080d05030a0b13090308060a0902272205150306040c060e010c0f0501050a15060c0206 74
    0x4802c4401c2000d1501800300d0800c1000c0c10352540302081c84a02d840281c410442e0009842e404281030a6107809415111070300855041421505810110925036403c40212801c00301508416817003101c804c00400c0d800d01a40c007801c02c5d5402a0001c004507141ca2000c03540307415a0f0940d0050348a0600c3c0020000a61038001f00e86283c400e100102e4824000309001a40360000c190b100002101e512040000101e0b00d0401801003035640b02905041c00f000000404502c0010b040d03000403a00c07081d50800e90740b074402d80c0c5c54801c01000e400300000003551900402540c003d070348880c403e440c08040071a140046100301c0d142c1d20b5007080884440e4182c1441840c5c80a101c5110326409079115691004c03481040302c0d40c440b40303240064000b034586041c2c4110003625504841c664000c0c4c0c08802000b0005021520540c10780c0c008d410038462007013484d401220100800c2c50010b0040b81400071020400205405c41801484e00d88001d0150707217911414442d000005110302d000140b42c414144025080610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 584637374 1250 584636124 584636131
    0x4122603091b12100e0105010b070b040b1b07061d240705040f0e040c090e032b0c0e0f040b010f030b06090604030f021003020a0e1314010807080106050102030301030f0605 75
    0x20403070b50002401103421428200075900e08129940c5414010b03008070003c4c4959230240071100350013030500c100c075191034800d140001c00081402e036104003c01c2d51220120240210300c260481c0340d660782c0520307141c00070152003140614098003d001d404110001d002181241022240c0490b5150f00c0d50f400b0040d5030750b07001c042c06d15014820100700204034845100310400c090421900c1d1140c481c01d1520341091104491350103042601c0c90402251640d900c08012070b051401410003074a0f0305400401d0000820700490809108185040600c821040d08050b20900d14842107442c10400c40c038110500c030680d038003400c0c158001405944047c00140c0a588220000c2030054002803c20004501040c410b80c4a0703003060701c0c0c6010098010b0210301d13000030f100810f840c461400707600304510384001809203035140580a1040c85101440701001d80550702190b210180f440c0c8090103960b55612503502d8400502880030b2550803d000410654000000c41c1d040720740c44001985904c0290715080700805016 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 584638624 1250 584637374 584637379
    0x305240d081902070f050405061302030405011b0309030212030f2205150f063c0d0c05010f0504060918020c060a02130905011203050c0304122603091b 66
    0x2404103032049240d8080b000342c000340c0c90300200390301e9007810ba070322000044640c4001d100314140302c200203280c0c4411074000e101c200190300140e00ca49881c90003034050300300b0001e01d864a48904442400403585508040c00c40c0340a038094442d4001c114144050600c400c8a0780204c581c800c40200701c00e0302243e20903140c51406407201e1000c0b10380d50365400b0304000c24a040a1250015007091000c0310480d40090f0350041400c035814100f42b003030000104507150000c4007005001d40900c0e0700c2c40c122484007154204403c401813001142680f1440e18a180495074012180020380d00c005541c1110701801c111000e0710499100c03283d903e0304d0021503090381035200741c4e00d20f1452340a012030040200c00304084c0d4007461408001580b2581384c40e410f59140240f070350244031903d09200040001e25010f96a9410b0030f5003501d400b6540d042c8e520516031562049601503c4005081d40c0c1a00601c268840c1c40111036010150015a10441c1c0c40c05429a001c01e454441c4c85801000703403d010302c142c1640360b5030104400f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 584639874 1250 584638624 584638627
    0x80705070b030a05160e03070501110a150603061404080d090f0f050f0f0123330f0d050c010f021645050406060b04060f0305240d08 58
    0x21a0140001d41d003058444040f955203d0083c800f04008a034203103061000c030303840c041e01c801c084c0f00d000940d02c00366032240c00c0c103010a207074150060a40c103101c00d60034036400c201500030400400e44080300416952205413012494594090700c502400f80005029035008000c1d00e0404000c4050200100310401c030884c0c2420b44003045070f00160041a45c1113a16014001038414100d2182180303007800c2c6e00c511003c10b1030b45030510700c4245110154070308405130040601400a50356584103000710440c2c44000501c039072000c0d00130409040b52080540318044040d03ca010080c900ca0003803140c85201958000d201d600071007241c0742c1c2944221803442c00410b0500c1203d007003103003414040c24280f91542204c442071070304208020a000e02c01210103a410141c6a007800b8a0030200c0300a030001b0501030f42d80d00c029484002240501076107402003009060a45215a074072507851801415421007a0f1190300424203040014050304c42c03000e0306014141184003017246c006800c1d0100141c005000340201c03240d060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 584641124 1250 584639874 584639879
    0x1e180c0403140102130b0a020703110a0302061c15031a132111060705120c1903021c09050c0d06020424090e07020318010e0312090a05030109020d08070507 68
    0x720044070740300140082d00040c1e69010001c0e814406045d15000500c00710303810055030b0759135a40000e120040f02e802250909d466120a0001000d843d29580080c0d03200c0004500c0d103a044ad400348402c4d050720390b91801080700480603016184103e04911016114040703008482d1110406c440849500000304200c4004210782662000000c10030b52105400503080d00707624070341c03081e0480b00d80110316103400000c0c504d900d00150014a035200301840f686031050004003044041d462401951409031320b6420400c040c0c840d00c0001002508280d07902102c4c00c15070808003050100501c0f408440c25000f0f4081c24420a40c030342400100c144029048070150750030000010380c014400c00d208400c0e0b180041e803030041e0464800040800d603540c1c0101e868180d00360b060000c101c1d000802c4403030364084840201c134002d040e000141c6903241d210300400d425000c0c4502c3d2a40f03d56424000749011f01c401ca40281c441c6484070181408c80f072462000940149c2420442d00c00305014a000d050054801c80c2281c1490781c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 584642374 1250 584641124 584641133
    0xb03100f021908040b0103060902030f0114150402070308282a051201030f0f050d030603060c020c0d1403160308070219050606190b07111e180c0403 65
    0x10406504051015400b05600d0312104603490007482c4a19503107011225420f0580341e0f480c0c030aa061000811040d620b501c2c41c021501c0521175031410200001c000c01944942d921160140181241c5641c114046184a103000345450b10a403842c3e580c1503034800005903181e00c03132071660703240101c0802100b80e180354210112001a0003810310700c0715046808400480c1034010310034004d4400803100305124042c44200b116030710503499a411a42c114400d80408130181c2046c0228950340680a0160b0250340c82200e11140c040e0041c0086a11507075081005c00d0045204980711381510228a90040c12800d2000101c0e160b2300c800c3c26400815400e8074540030741c58840c400c80b1112039608a01141c03550041010264041c40700644082c15136080340b11903161a0746081e268100208818401c85c0d001c10042c0d031850401d4a00c0003d8071800309010740c0c031142070800200714100c2441062003000b02040c09080c0149031071440fa45400007815400d2a102078040c50121080000c0c140ea900081c14040080880c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 584643624 1250 584642374 584642381
    0x6050604120c2117070c0e04050f010c0f0e0a08030c1e0c06070b0a090b130b10080703031101020c0607030603050c030a03020c0607110307030803010f06030c0504090b0310 75
    0x1401880199001d80c1d8603842c0c41501c1080c1580400b41001c48000385003d2140000d64a5100c103502580c0400069030300c0b582d110280c001d0007406004002e89280202d0425944000d40740240e01a0048500d81c42403818124241c60003688250b001440c0d14250b20082c50084240f003400540c014420744440e910703003903010b10f580c000e100c4061301540402000801c5091001024880c64601c501400b40608401e011460710b01c5000e0000704801c8003040007523009181d030360205a00540c04105000d031418401910151107031040c9040c2d03195a9001c0c00300700a0b4603845030102c201c42c1054043d02a141c17071914169200040a0341c084015502086034100301e44040c00030307500c5024551000120070381541016403030300b00c1b450300c45806540308000c0300012030b40014103464551400c80300c20f5a564101c0c42c004820045880009401d40b041600110400c1410b0703001e581602c00080403407503116a038050072002d8032500319880d40850410001885606000c1c0c0140e1202c0c03002500b1500380384645800003085 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 584644874 1250 584643624 584643629
    0x1703070f0506191103010501120e011109031203150d050307120f090603021204020f040b031212070207140904080f1309150e190b06031f0e04080a080a06050604 70
    0x740d41005080004000600d00d800000e02c100050070002d02d02c034040c0e107035207a21041c0106810b10042c1c0c0e042c41440200c0760040c4089000c024000e11000c1000070214103213400080348603219020310903000c514180400e0903031344110544500700d8071030341001d01403108500c031044094903140020040240800d8003c41c0d0810740c80019510304c01c89100c0c0c4d020040c000c0e507054009808050040000129105890441c16042030301110ae0b01e622580310800603006203207031000142c060007650002d09607150580050b003911840004e420304140e4400702c040f0380313035006400741507201044000003031030506241075001e500c140304000141ca05602c100c01e40000307800c8800b40c40c2d480a000712081c001e000542c02080b540a1856000400c05801c1044001c80300000400701811619140c80d100d5030302038180c1000585001c083d0500359682000001c002d0a501c0d009400d503151040d60000062140c9403101403071040c0d400c480c0c0c003802c000034078404a81c031b52405444d420762680c844d440407400d9600c01009200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 584646124 1250 584644874 584644883
    0x20f0a080f013201020115090f1104050d080f280908121b03130308041e0e0703020903070f090f0e03030c0405091b0d02090913020a1703070f 62
    0x20149480342412400303030300581000201c3c3c86212a00711840b0b501c1c0c10700b111a884284034441d00c102902d07004038010185124101c481c0031164400140910345a0710041445101100600c207407911118524020b07c150700c04c3e181c000b40001164408150040003400084940400880c80c1426012410384582e052000307010023108044448458207800200d450001c0c24034001825410b00c00314500c03501d03806824821104940914a010084001841101d10340d110303510116108648a0401d502c5a41007401084180d80c40440010071110a58883c04e00311415480450300d20750b582c12048004e50484d08107617415200d0140d000c1082560403001c100075020440300008d8800c01a09800191000700e00c0e0002c3c41d810410610000c260f101d4111801c1c0d03a401d98011289490b0780e1325201c0204070002d002008060080342021601620703800810803802c086030200015285d903a032001e0742a40c00031009500c8010700b141006541580c0702e003000da8210b010252030030080d03503442c2e02c00c42c903030591001c44 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 584647374 1250 584646124 584646137
    0x50a090b03010e061c051908070803010806010f0801050108070501050d090210020f0c0d02130c2d080f131203140c040501030c02030c0a06020d18050604050106050d020a050f0103020f0a 81
    0x1313801c1c030400c20301600f00c4680655030b5000c82034403850345601c3d0414402030208003030744071002030191040840f40301e10741c080c1e62075039250783d40c682858a1340c100f80103209402c2003804002076410414081c1e00e06941140d0007600640307140c44010354059022040c00303901540c8a0440102598452041000000040e0007030814070365031941103030522080038003c0d48160300701e00b246000340c4c403810350254007030500035070010300f00d85840810794210202d000d005502c0c4130120000540c14031000e0302c3d2071002d2510307103c04015480c1ca51440f2100e0b0f5045a61705c1040140c40400790100c0c1c000721500f4501c00c0527003030000b0600354a40200280ea00120398161501c10005410041542d1510a02d01f110070726101560408801100c4181c0b82d0f218014050829600401c5024154400741d005aa803041a601c1d4132140c0780803440d106490750300c110740580b402d51a0100002d807034100030072400c2c100c0707034020010610142440c3c01c100001c007401044c0c03810981d0a0040414225100c0002d011498550322003e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 584648624 1250 584647374 584647381
    0x9030e01030605040606090509180a030e03060f0708390408060604050753010902030705430b130f0209060d021504080f07060f050a090b03010e 63
    0xd07041d500d40b41c0c0081d01940c0b51070360400602e0713400301d691001e448080702c0681c40d98403115181806004c3d0903400c2e1199000e40141c072800c050b00089040780c3c060041c3c0540d101681c400d4030013244000d04035030780008100c0c02400544694052810000c1d4100c01c5141403040c0c200e06002020741e9002100b14800050001400b84140a4204540f580c040011a002c0c882442e019400409c00d0b81c0031850050740c1c82d0011501200c00d00c18035100400f55446480c2010b0320a40c0e0364078400f071016804240502c141424002180c1d0400900841c3d01ca000e07980c454924051a2203522042ca14000407054070030450314518600303a40070a041405c0d100410300085951030f556041c46942000081c1103040f6540c2c40842d0403002495034602e400640d501201c2c00d24080c1e0f5884049070907004001c030001e6204222040c0214a54140310203401a50f60050481d01c004010540140c0d84201e64060807010406481c0c5050185201e83c0041c0011096894006051903450403564626082a040b0354100c580030000c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 584649874 1250 584648624 584648627
    0xf0a15091518090c020d050d11032401030b060a050f0408032101080606011b0302010b03060f10080a0804091d012a030516050a111e06100e130606030609030e01 70
    0x2c2d800980302051041220340c165610181d41d840c84888400d052000100b441400c80b402c560054440724111013003d0303070b249001000400d400c01c1c0005d461001e540c0003146c5a000e0351180c841c542c45000050582ca00c1c0002d5010f0035030312508038800c001e104000402002c01e90700c0c8140041e00c1c40200300da0f59801c2101480302d04040c40076050b003101105078491000c02c240b6a078030051800300c0c0702034008000320f6140d841c142203001d030414680f040e400d88a40c10a02c030302c2c1307200c4220580c480c8280e4946942440d803038050751038030340c001030b803001c0c1c0050000c0c0002d0083e0300300c0364841c8414480301280c1d03284060300380312081e0a40c0e900107809030729084040c06541800074030701000401007016203410845494601d200c00011144084041e040100c0800c0c20240c03240a162012120002d44048134020f00b001007000004025440079540300e40104004100500c44a80ba9507080d103441c00d4550246980e1441204075141d0341c581c0039103025031100400008504184178036100c4500941ea82c0040c100b01100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 584651124 1250 584649874 584649917
    0x240717040f201905041d120a090819140d02120d0b03070806011505040303020d030f020d24060503060a21140606030106050105131404020c120a08060f0a150915 70
    0x1c00000003249803460040c4c0d480115a400205050081c001d807142d00010741260241001d4101d10740c0351090054000794540d45100051b03019205440c550703443360001c600c3c0c039240c1340c0c0b00151070050707441001c0d0004450303050409485001e10a170f10001e103041c1c2c0000040d20b004525070141c1c3d9a900118014000c4138140200303c4d01000aa003402850302d450341e40c00940e207400d07040403203013055507071941103800403070a030100c07003484540460034001809010104840720302545e45102e01880031102c0080c449008200744c0e48035250041038019800d20b050b5040300380d0030680e2143c10943e50240d2a0000180500c0594000944c0046c0242090b00d0300c8404d0600f10b90081c3c103d54107205007480f0b4071384031450404042c41552600c81d500a102c0300030701c012070301070300a901d00e10a0b240103810b42c1c0e0408030150030180581c0c0078941d03103000960b115201031003613807141d1031241c1d5001a601841848484003460100000a04a00e007131003040d42d0340d08649541104030398581c8001015815159030030015500c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 584652374 1250 584651124 584651141
    0xd03110f060112080c0c0907050a0207080c0a030b090109050607050307110c10031d100519020f1603050c0601151815080603240717040f20190504 64
    0x30014440c42d41440010760420034080002058103400140c3c5400004080c8640349404401030301e0034645040a80010b03002d5000b4444180047c454480006103402d030028582100c0716003d07000650071070840d00d0b840280403000305040210741d02d42c44420005007040105500c07500d403996a0544a05246100038840140001d0002d165407140070403080f5692040f841d04000c418074100050950074201414150030308803080c950070f600464450401e400301c580c07c1140724000c03142d4101c0f96001c880348107070100e004500aa00c0f04c40810300c4440700801c80c2d0450307000100d000341461803c0c40c40c40d004040c41c06500b41c12403800c0c40c008503007606519402c414620304030806a4041d11809050081c103280f2814244014820000c1c0f0101107011510180405a1440c1509030302008440c46410202c002003010b8401c7e030006425545c0c0399400c2c1e485c42c10824029688000c1ca12405000b0b91241c1480c02c6499181c10b880074200c01ca40c082a0340c2e08003440c0443c800ba00c0110503281c0c9400100b208990102 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 584653624 1250 584652374 584652403
    0x4080a03090f060f021002160503070c090b2b0312091112030a02100504020a0509070201020306011416060504141b191d040303020403061109030c1c200d0311 69
    0x6460650710f1940120761900c88000c0d1000043c0c9900c101d10000b80c883d90010009409c60200081d04400e00112454100645940c800700340503003054101800782411040b13180400c9514480c1c40b24815103100042d941c0c1481c00380c07600c5e410030701542e0b070f4181c12100640c000300d03414050101d40c2c41c034608160710240c8584604c5030185051805098010f51911034200340e4481e5140da440c0094219a220000c08000d4440038080714514500528041c0c009d50040d65140d003ca40c00c03c0b260020082603400302e400041440f0007480306001e4130f075101e8001e0301c405882110000c482034000c801e01c0f20300300050404001c44140c0822038041c0e0b2800c0c000b0a445245d49400843c2ca21070081c41400310408a4500d1480000010201e596070740c00c0890081c02143c000800240c00c155010344800c0c0309030054031460b4411800c0d40c680c40c503c0c03003c005000303000320f00c258820300c4503062079004030b03c5142950b4038526203544000b0301100c85400094521800300411004070724541410110240d00300044010450034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 584654874 1250 584653624 584653637
    0x60907060c06050a0e0a0b01060e150a11120a180e01050609010c0303230f10030b0a0f060812070b0c0909040209070309060903120c051204030507050304080a03090f06 73
    0x10520000c2407000c4100000e0400340d11a00800c0707002e95607038010301c91810803105407800f060852402c0d20404000784160701c002515000c54071070b40d260840d030640c40444c00a042d54508100554155000181c141c000a4a03001c0e424225a4070740c9200020308081c1d80d40d5844107c0c0b11014241000000c0360798000c002082e510800500c45034031105c00b25000c400f02402c1c40d54101da0503290440c00340c454a1a000400d42400c3c0d03000c0c4802c200035542c107000329800646000b00e80da0f01d02e0901c4180700144030141c0414410408600e00313041076440321078112461000410361544540205151515500312802c040e00f0005001c8140140901d00c2d6411040e43c901e8245044260b4001824048010b032020340300314031704008210f1040c043c0d444000401d610070700500c820084e904000e00000500d0610400c1c036410b01c40c2c18140d4074450303400c54480312074000c41c600854a40ea28100d07110b41003442c007160140310070000480e20040412140500038420b03562011002d050079580e80001090f031703010600340040b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 584656124 1250 584654874 584654879
    0x904020d1212140c16020d170307031107021003050c090a0b0406030c0212070b070309300207030b040b06012703050d030c05031305070f080c0a080c03030f130b0c010e060907 76
    0xc80c4c1d02110060380e40030442c50303d001550300020b02c0319011040000c002c020040c040301f8441003408040c500c2020366490800c070301e00c40308203164603038454503500030b5000c0d034240d0500310300e42c0c000c0d0b01c2a900a007445655504003010341000c64682e4602d03400c5200d4800c4082010050117606015031400c200181c80a07040802081c0c203000c40038010840000c11000700500028020341c0300e81d205455585d0440c0301d46203540700804845000000b51900081c600990380110002c55000140000449600c20b190191a40c3e4a480e00c1c10140d10291480d410000080c01011405000d0142c1001d90101c100600c0c40c41d9165140c00362402a1034070b181e80c1450b04040603018000e410006480d44000d508010b0030b41c15000d45442c07824801c00350040e04c800f4074003d0000c6880c140004030680d00481c02d44100e48544e464001e40c66030745207024a01035259108210b40520011058050202201c0b18296184410f0701ca01c2d14410541180354950f40c03503035548600703c4440c81c0801550790010605009800a0360 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 584657374 1250 584656124 584656141
    0x503060603030405060a0e04181202062d0606070c080d0f0c0804120c0801060909061823010e011a090708190207080d0c050c100b09060904020d121214 66
    0x11070040d40300f8044c907c1d1901e01c41d521140c01010801036030100f01e4165a8003440e2084030809ca4050b000010300c1544006a0008640c02c0c00c1c4022000c0700803e0500e1100c00c802c0c0c524008801080030385c000206100c442c0001c0c00901c00310015049150143c104c105240200a02d14100d00a0500401c0400c942c00c4010132921001c82d42502c030340c0150040704925030f0801003510390313840c1d004440c603618004001400b6491980418800d0f40714100510101d4128100301040c080038680103003000b00d80c0c16464480140c3c44d00c11b585016840720010584954180350385086403a1801018248020043c080c0210310340040c4140e4440d8241c1000052130a00c2c03414003e1340720b208c4121649141e40000c000d801d100c40d24041e26050402900140074807252104020a0f98104100800441c0f0a101000e1080d8003140210f600c1044041e01c4585150303221800c10081400c0900142d8100d100360700c2d0840464066a0069000d20307140d2104000e5918200410302100c110300042c0d0501c6a011050000c5070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 584658624 1250 584657374 584657377
    0x8150901030209090a0218090d020c03061f09050c090112021e0a030f0e030901030e06010b0d110409090b060907021902040c02011b09080106050411071b120c050306060303040506 78
    0x120b405441450b0a0740e640902d281c0703015030698000e94405c2c03840440b808030000301041c16110703590040a8440e1001c02e9001a40da0340900300032907034075801c80d60000f0083d6801d1100d2100c4401c0c1700c0f160107821aa2201c5003c1110010f46080c00c074030b0800520700c881e95822100c40300c0e8980c41d000b000c5140ca0714000d040c070244080090344203c182d0001034440a0188660411000844001800c003d41200c011005960350b102e2201980030031305020001c41a4540452600d040300c00301948103140c8810100d900004041e81c101d01300c2c5511050102140c450720a1145030325261280021405500b458402c000c0702d01d800400031800c550043c11850756114a8049120400c2e5056802080c3e4030900c840580c058044e1040c0108000084c003c455410307980090b44400310784014000708071a42e2600b0034403080e18540075040c1e1902100300318040000b03082e031500d001001c0c1d03820888001103407120711a81c503854808400761084814032505001c246024000c1907003140e021001189820314050210303000c3d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 584659874 1250 584658624 584658629
    0x1e03010b09121c0c050c01050f0d02032502153304020909040503030a0c09060c1e0501020f0702030c0301050108120a030e0303010e09061536011508150901 68
    0x1401550b0030301d88001d002002860030000c640000000e03005484a00100500700c109400e0725540700c1c101d06803038554001c2080740e058218100d1072a01d0140f4131420f80000c3d52020303114032103500c40050480c0000c3d0000c0c000841490280d4064030b465080021070400620018003400503206400b6060a01200c030500841480c0c0309440314500c100d4100c0000500a00600c1103080e00310076000204000c014010005604c21100340b1030400900c0402441103d9800c41409080b01081c010802d14012600c00c090b030003001c2103030f082402d00c40708a583e12103099030046082c459036194003180d88000c41c03409104013000000164002c0142e585001c1440303627522654110503030140000100300b04003d1280d000701c02c203824200116660ba507508c2d414a00c1904080701c5002440c0101d0010070f94240940128120a81009208002c0751001d030740340c0480d40c01d82404084929001a0b01e400781c81c0820940a03000301450b2486502040150b040030f010950024110100d41d0702820440400d0b9803000d130144d05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 584661124 1250 584659874 584659879
    0x507020d030c0203160602040504050901020910090806040305030901020714010f0e03090328120e01110d0804020111070f030c1707030317060a08010f060501090b0a0801090b060910051e03010b09 85
    0x10451740509016000303101d44d40010760424103003006c000b0303401b80540082028413005c0d41c04d0541c00310015003c4034141c0c02030240f00910340000011801091241000d10303004000070000500e040100d47d5410741001e660f9807201c4e03059466042010320440e80b4801c0c0700c41d10b01600095440c0400d02400a0384900700642c083c50311515035800d9140b9840c4d00c0c0c90071a070344c9510a404642d10860080080d120f01c1b40584a18000307120b10790030702461003020800002514807625249940c0e201d6030700542d82c4040d0246201281d01c107070180001c0042c80c4100d00c00096001d001c081403480d003440660b040021802200308003652200e0b82c03c01c0002d0344400400c0c41c001c07040d03038554050740b00d242c0010340b1284035034400c0e4055030800542d4141402c05601020448500b62112400b2541e070341c038030000c1806002281c01c00704100c00010081000c03181c01121040300001e00c06850540c03103400013913101e101e403c9040000b56001c500303200c11790103a08007a074100120138801411507142020901d810b1080300c10490 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 584662374 1250 584661124 584661157
    0x3020f0d090810090302070b03070225120f1506180f05010b0f090103020706140901060f140d050703050607050403030e030604080a0c030909020301080a03121a1905130507020d030c0203 81
    0x2401c5c14400e218960140c40003d041907500c0c207180320025a59250f59070810719000e80700c2c9030f888510080103116000c540010032080c06d101c1035500d4843c1da00c010200e040d1600c0c108500d50420704020303071140704007814110350011a0095004003000480c0c0100c1c5444e01440c1c40d00f0018400001c01e1429120324103410003546070303a0003101004802a01490304000c02c441c0c100134250490701c207040e07005449680c03014020401c0664880c640c0383c500002c1d219201d41100303605040700700c90500c642c920740301300e01503400c1704d0f0000d59170790700c1903d07000080311508000f170382c0400c06004040e88030f00c41c011891800c40003401d550500b601c0c2c003012881151400300070b00000180002c01c150152001800800d0152011034a0390707980c2001c00d2311542c1110049000942d00d403c01127104129214040f550f01880d240c0d2044250003200f480f100405204040031499048000001c41d9900c0c0f044203000e8031025040031405040560010303240000d051b000d0020325013481100540e883d40042619441030900a016 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 584663624 1250 584662374 584662391
    0x304080c031618140c091309030e12010615050309070e070f050a110f0705120109080d0b061204110405060d03210905160e010611070501030b01030b03030703020f0d090810 75
    0x700010180c0c40f0b1440110502c0ca4100310b170350003800000c2c1ca0b66a00c2614a005a2016134030b40c1000c41b0f120040086c007103844440d94507114208404070403120013210b00001091500c038042c0c8481c00c1c1c0c0386a0394000150b00041009082e50301030000c00003c081c0113100c24828117100301c000c3c004400902d04401045800310300c42950a202c2c0d00e007100000c5081042d41d400c200f105041d0781c2c58503114064070b8001d40841c513480320120b40500c00c04040940020341c83e42803030b00307440300c0710301070011401c41c60b5000400b40064540500080400e80c0150f105800039050b00c0d001c601440107440005005034424910b2650080100e0b40001c43e40d034111050f041c036218108045005070707004100e001c00150040c407490000c85500410700d00300b14140c070040224030b01582c3c1d954808030350035001d11b0b100300b1440d08114010032465019400c01d641d0740300d05060108800c6030b15404245182c1020f40c0640042c1e0003041a0014000c091008080302c0c5060302c0e20f040780e0740c24054032540d203154520403107808554030003c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 584664874 1250 584663624 584663669
    0x201140417150709050603130503071709030106050901050904020d0606120501240506070b060a031401092001020c0f0607050102070c060e030a15020a200304080c0316 73
    0x215405440c0580340e2241c40c00d191800d40b980c4403000c1c903942e0028400240400d218500904814084030801860781d49182c1d00c2c401c0c080d0300c002003202c040f0f455110501030a40055484500601a40c50405001e0703200d09001c0205402d60380d89030300c900d00512680005102c99252411181c0c0e100d40c05840c41601404149400001011540c0c4007419011800e124042005010340003010303200c042100314402d02e40c0600406030f1109036841a50380c0020b080240f240003c1400f10703d50703401640100010700fa01e5403a22000e0340c0c8504029006001d0350b5401c2c40c00d0400c000007800401954225800180400e40000007075568465001e14506c80e4582c3d6600845958070702040380c03113041c0d010000b503407030703c0345460501d0880c08240a000c003c629100d08001d05070a0004a00c000150010b600001c021074240c1074400940c008405102044403d10283c046079981082c1441482c0c650300045070341d05d182035403003800c00304c10086561080d041880c80c000700400c1c0b001c20100391350075046c40c0039010220f01d58 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 584666124 1250 584664874 584664877
    0x3181b01050406200d05070c092c010e0706050a0f02010b090121060c030b0909060403020601140d0501060609050a0e0c0301060f020f010c0e0109060305090607050901090308120a15030f020114 84
    0x48100c02c03071181c1400010b015a06c4070192425501c80e9800b9030f031081d1503810f842c0c2520548a030001d14071201c41c41030340902800c0340007064446010400000d82e0042c801c401402c141d4541c00030030204100168240c0865808208180c504801e407000b04402c2c1c2a40340001d07841c2c0e030181304101121000740325140d91800d1200141c1e00ea560300a40402002e4172a01019010f40800301c03403a807040d214000000c211b0a1301040691007280d041e4054180c42c0e0070841002d00c0e0004600b0b07100d070402c03000240d0100007002403241304003800094407180b211601e8a0304000d2909003580141b402c80c1503a4062007190700410054905640c040e09211095094840c0c08a140040c00441c004d400e60030f150005401c507410159101215000ba03980703500464440038150192242660000c0840d1311480015240e184a440680309030401450801100d603520f480c0d8035400e403c1038640c905454003030b10521501032010300c142e00030b01c1c8840c48003005807482d50700c421203842c0d02140080e0501042180a07c0601039640 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 584667374 1250 584666124 584666177
    0xc0617070e1f03021606091202030408060f040303140a05100b180f0622060e040c050a030504020a050a0b0d0b030c060d0b0406090507020a050f071a160803181b01050406 74
    0x40c54010f0405e1907040150180085a00960381a45604041d0710164404401c580070703a14600700030481500e505400c02c141c80b41c0180280c3c2010340d20040b00100003000b4036004d00480d03000c0b10200303031414908510f040c61304107544820b404004c1004840400700c0c06800d0b66080c030b50126a1000e02d16819800700b400b40c071a101c0c96503510042c810349018004003400c50308059030720035a200b8141c255a0414807003180c02000244021580600c01e80710118466040940c1c050301c058100d007081aa220082a110400e58100d0040c150010540c8882c1d102544208204100308030018140290441c01040b8944100c210500d00e0b103494000c04005901c0399009240145100341040060f450724800c025141c0d0080e40d002c40301e5018101d4141c8403940b00003000c00c2503514000b0400c08070490300c000502d40368450076286821888004035080440c143e8809075100301c1d208040c143c0c000c42008410b0b41069001e004040c0d00c2d0002612400c140e9034040140c40540c0c000d810704024821001c0380c191018802403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 584668624 1250 584667374 584667397
    0x22a030105190c020307150b03010b04020316180609032003033c031515070f0210080702120309030c0a030e18130605040f0c0617070e1f0302 62
    0x5090059010798140c0207200000c14142c01c0043c015000c1d0220380340d2045110181c011000f4030302d40b40c144c20491303006c1c100045002380005a240c4140011800380d8000704c1d0725241101c032160701c2d001459000036529050280010464050f282483c5000e0310864460001500c620600e80641100000c42d070b451006000e402000c980e25800c00030384003a2442c01084a20302d03480c4e80c11b003104601d481c04182058801c0201c0e0b044509680d61091203d06040781c9606040c0d11044d1a50702c0010918148002e01e040c0f8003441e20300081d1032250060203181120b107040300007000015020000c05950120703881743c0031034501d00b00303a07604d8584c0781040c1d1650064000917169401810200d034101a0049410062413109450b0207201c0101d102141c08100421100c03c41150721410765003000581e15030040358001c1c0309590300165031019407101d2041d0703511034200801017131082100a0345031206a40f0709512a00510740ba124400d40301020030720550740040720a07105444043d00d01000343c0607405485440e04207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 584669874 1250 584668624 584668631
    0x5070e0324160c080403050102030106110615040b0406090207080c011107050709050c04050315010e01090b0d02060a090b04080c0f091315200d1a030322030f050a03080a0c022a0301 79
    0xa07402c01f94001e42c001e00c180c00110f05a048030410300b40e400700c1c120b03205840d150410360303101440000340005021501100c5900594550002c550070180c0d2000d010705030b000e04450354451072481c019a0841c0c50b00207015001d0502070050b080001c10024030b03031007500e29400700840c3e540c441411180b002c0c0903941080342d0500656042d920100f048219140c1220a00d56441c551a662000960120f0304a4a01c0075082500040082c0c09410800b0041241501910341850b1042e80c440100d2840d0b005500052420340040600d4030b40c510301445000d00c0c0380c0302224061340c281490500c00810400311003000b00325000c980c1101000c1c4a0340e030f02008c0f0300d58014a14481c40031b420401c00c50280d002c44400c0410034034210150900c402c001c0b16500c0c1641d005001180f52101300d098032100d0800020320440c00400110b800b000103202281202c800c10300c608001c24511040f8640500703140710080026003030614205500c41403950000703420030f02400d0b0900c030500420503060502d42c141d00c0d030b0141580641c01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 584671124 1250 584669874 584669879
    0x31815090807030c05010501140303040e0c0405100206070f1716021203102108161401140a0b1002060a02130509070e011202120105060c1005070e0324160c0804 70
    0x1009404c11540e01e21503c001c100903030b202c0440c032409043c0a4812030b00b40e841800b05000d45800380400940001c00040c0c514200f030741d13420000d55144800200a40140c0040382408005900803100c80940c8030182081100c02042600520107600010700d841e00c1d00c80740510b4601e14074000e000d04400204e001c84000d55a14100e03240a443c41d045101d542008210031001c81e00b01c44558060303001580c1c0c04800c1c10314094495601c0c0720b4030051070000f40c40184004401d80000d0707030300744200411181c19485641e210314000e448441207544132200c5034010751614064210740b03039012804c01d510012107040141c5844254480c4594442c1c00e8021070740100c84a0240084550441000140c80b0401d0340e945654050050b01d240c1a400396080d50034214181800602c40351400710b02130441c01400c0e00031618041c85406400c0162901a680310010400d1210b80b0201f074142401f440c500c5a1401c01d1102d080150b6142922078030328020700484400c0e1704004418012446401800c24a50b08a001c2644494 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 584672374 1250 584671124 584671127
    0x80906030a0f0e031804110a0c2a060813020109091a0a09050f06060a0903030c1a160e030f0a060504020a08060c0c010606030c0f0309051e160603181509080703 70
    0x41c449040f4041d000300c417690307069991402e402042001d05001348401c0c2402103206064910245d410800c5803601501e00d29a00f41c00c10343c00c03290010002c01c0c0114081145440801740580001070189901440240750742000340c0d0300700b0301c030030205c44165a0004079101641c041208251041c3d00f07543d0310003070b0400002014110764010f503000d000038028044154880c18100f203c4d034445d4031142c1e00411030b0f0480400110b8010042e241c80c1c94000d44011110625240e002c100d8020211213600c82641c2c260b080710355117075000c540450380c600d054006040740300c0d034183d0040c1d480098040040ca01611040003030304549030300e00c41d1402041c00004450700e500303203c420000540c0186902c24181e610b09680002d40328464010386200300c000341c031000d50015044c0003c5002d0000e0a0003a40c00f0701c2455208010f8040408401030b080d0700ca00c02500d41c2700e5a01d010300d00944041c0c1d02000805091008522a49502d0705046802c1c3d640728000201c1c00340d030202c040b00074102c2040302800c61103002c1071180505 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 584673624 1250 584672374 584672377
    0xf151003051b090904030806150403140723040e01060803300c030a0f0912170c0405030c0d0f0c0e040b06010212030a09020a1728080906030a0f0e03 65
    0x91021602e08000b161600c241c6000d903018802c0041c2d8066107250108020070f020300c43d0290003002c041c0c11803065008610300409564841e42c0f0440d2803030500100400824800d00c000340240441a128591581e40c8000845400036a104254880c90703882510301c941c4002540a200281014030035292138907003004110410b080000c805000a408a101008994440a110707600c14a07003030002c07605603241e900002e0020580c1c510074404941d40d41000001290500c09504050141340d5195040102807007849034030351401929110071014184800d10459074049a50980c541c000c2c2c41500070b501c840c0c10803000100040300f000d4240e20a1304001f15610183c80803c92003503008030703010040c548800c401261f907001c0392070070216040303000c1c00814400d03456038000b4482503000911341d20307145403911104188400c1184030140d10703a104c982031101c0d030034001043d81010b28000c2415981c0c8056500d0307a41c042d00c100351502d84200c90020004200700205d501080500c0728819040180000c40283c640d5a03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 584674874 1250 584673624 584673631
    0x170703050726010b0a0329010f060e060403050c0108060114040e0103060c05030f010303121d060a051f0302010311041509050910060e09091f0f0c090305060f15100305 73
    0x410681210500b8001c50502548081c4840a030181c1119032075500d03504c8040700b0010118580100e07100a2000e8860b03491034042c040c041501445085034509140034004c01d400c0d03140c19002d040f05200030400b04202044130907170201c007828854055a43c03800101c501d60050006543c510002103404104074960400701c40c140c1e403144d4000c2082850303401d016105c0d808101c50314540f0000d4440107000103889581940d4a00c0864140840c140c240a01116013a54400010800a5018800700800540c15018098100c045214400e80300710160b942961000d54134003020b4181500d5101c180c450880403402c4030028003025013001c2d1101c800d2400104401c000e0301c24241301e8140c0030042034082e141071284108442c5035840780444e0baa0454280300310b072040140001658050640b00c4401024682096a424020240005800c561025600c000c80d2144c81105080080700d075030610010b02c000404a8200742a040c1020065981d2907603420030024902c51580c001106161420400707400d81c010500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 584676124 1250 584674874 584674919
    0x2091801060e0a061d040e10240f080d11031308030d0e060c22031209080607080114010c021f050a030509010e070302060f091903060b0f03071707030507 67
    0x1007656495104641001709840288098010410115050319050740101440315040d800e450140c0400c6031103070119207803510721074015070b0fa100d030b50740e021444c104440c00940704100850b0f4a05e03003401300e80d5550f61400c0c2c285c1420302c10019101c0080f06802c000352101c8a07030004481001c1d6480710b025507181c7c5c0100190201c50f44c00c000564029a4000c11064498036450740702500b0100c2c5080394040c1d02e047d681d840701c004803c03400084080b801e0440c00142100b4079407240740a107840d1140140c0303400402420402041110401441000b0400341c1c0710040348024600b201d8581d0482c00003d40700b1107504c1d4882105c20896a034442802d07002800b44c41c08022540301000240e4a0214190a84c1d180c02030042064105107001d20041c540000584001d0018040c028180405440850711b900007100307a50440d00e486480400401041d40101d50200c0b105680000e451485400800c2d034806a5000d813543d4501041c070902411074042184400075900501280d00107581e50603000030641d0036422021 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 584677374 1250 584676124 584676139
    0x615170705030d0c0204110a0c120509241204050c0a08010e0c040203281a0402070308060f22050f130b0403050306010c0f050c01021006030506010902091801060e 71
    0x10011600850a20304903040500540140c84840c402190001c1210b01e04a030300a030780c0e4000203c04507100028012a101d15112102601d240b8100401c0c9054004490001c001d41084014400e44888907840c3c00200d012070303207034518180a4000e0102d8002d0000000d2145921020041480f80c0084c106600341d030203603099100a91543c44044c242c0c1c1c0d981862009552088442859508040c0d00459000090148001031691802c002c02120080e60109001c1c103602d40c5030b861441ca012040124404001720b40451420006640180114600600d454800c40c092400042d194455031a6520001c959010301da4090856500c1724008001c2528034148001c01d03500081c0080300d500b005258000d400c52848602c42d075039558121140c1c1d000401150410038400c40c6840094100808900c035284100e01070082d190901000a1078030b46440440103090741029810804118042006030648150110141e542d030802000b080d00d0300340751006c49140c200e458000103605a4040907440c8032000031030380c00e0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 584678624 1250 584677374 584677409
    0xa170907081c0c1b030c0b03160c050c210105071b0828200309010c0b0c130e0709091b1b060c051209011103010608070504030615 57
    0x59510304080c05440c1e016801110141001c80c0d40b00e000703080c4002c041c540f4242d0a001903a130189010f1124504e1203070012101800d01c00c00c148004180050145a4034550a51610701c94600352641010180c1090026291410701840b5080c414402c6404001d080c00100e400c0b01d1a41201703104010031680342d15440c007030100c0c0b520340c41186181c044c09181200d04c8400b8900fa00c400f40c50f540000719450340d903a0750906602029510151605e00c802080d2541a2401c44001c560704100070200c1c001c600301c0e0010004c038a101d17a0043c500fa88101c2d004a140340d0a56503206040d1468402c0e541a242c034040b004d10f0006050380304004003880b4105550703c02407601d641c2c203910010ba40310000580c001b03400c11901d42c2e01c4903101d03a501d0107026100e0380480800d20580d4541504680b10002000f0004200140d0350701e1820b171540491b0f40021100c4000c01010405c180302e60340340c2c04180a0f0808006a22001c40c419a114501352005150481030030003948a5a01d20616054041d2281d0800a0b6502128 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 584679874 1250 584678624 584678641
    0xc0112020703020a021507020901030807021002161e21031704240f290a0806070f020322090c050313060f1805012c030d0506040603080a17 61
    0xc0d103400c60751680043c1051074040d406c000184c0d02103801030b4180c050a10001c005a641c522032a8025405010025030b102c0c03036401403241d500d038100702040966029a8020398990b22150310801150342d454040c0c8510300c0560002d085540503588032a031000c92040100c6145c0740b0003446041014403d80780d46180f065030841c0b000003040c080b00c1c098084265001204c0c104014101c0108506020f0310b07000503140c62910400302140c0030700c42d81c00c6100c10001d9800703100b182a2001400c1704403040707a80361011480c101e40305642c3c100081524040004504072a10028020801c2c4c0b08080c0c030502489031040343e010078202c1c18413440d00c41e4245090034680b2448490f40100110b03401081e1514240c0420442c988a42d8040c10507468104845591111100384030384c40c401c2d901060511810021800c01208140050440c001101c814a054440400030201c40400412030744a14010f1102180716610f100009000b00102c2e80082c00f5090005405804982e00407920002c2c803007100541c0070035454a184 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 584681124 1250 584679874 584679877
    0x106020d08060609010905030a030e0310140613060b1c0b01030b031b01050d2301050f01050706230408031f060f03050a061e06030c030209010e09070309050607020c011202 75
    0x2030800120340c886000c9009400c1100081461078018101481ca490303880c070200c0d103440c4c500b490580000b0701c1c0304080d282c40c2c5014003114104982507070051042d405440c488565101c00070342498401c10031031852304140c02050708103600400a00c000c20b51100c00e41034a07400380110b62a41588070f14640300300140e5540c020f10800b007290a01074000c02e9040c0503c1c55408040e048101114140241408202142d420350b000d00c108096002d40b80040d55200b620201d4911344041c2c102c0c0340308203007544908226903440001e5074117054101e1008581301c1884030300400b44203120386060301504c503960300304000d00c060080298000c207840014480c10b04d00c2c440d07605150080601400b40058080300d154014140701e9041503030081c402420006003141ea4020301141c0c083c10114240c41614002020005241c01d03105100030150a42415807a1910000000b80011548550786100328084008a000c2c548207a00441015034000e089072400d08001030060741d210001d0011070700140030b001003034007810581d00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 584682374 1250 584681124 584681143
    0x4030e031203010b0a02070b0f122a0307110a030c140c0108161b03030509060f060d020121050f060f010c12030e150103030302090103180b180102040f140405010602 72
    0x8030428103513420106240d049030311010b00b40c0214841c2c0340000c42c0004451008001014081181d07940da240784251441840b00700030581c15a46002441000b296940a20512444020f03524039564a60341c004003521544c080c0d40e400d03005031041c900807000301600030820054007801030a50140801c24458142d6407950b00040040c001841400071540ca000080c024120b08642803c00701c00c40910402895400c00d00307846c00f6030009485006000449006100558000310582c01500d56480c207a000303d80780d0404508000e04200200c4141110924030704030b41103201d0300c601c10501c07a03800c080c0c0039284149015956940701d0128030b00031015540c01103034a101481c0c0e100384562131034011078100b98001e147c40c1c0e0140788140119121240740c2100a400a0301851007900c2c010b898051013400103003110740141158030350100c13500d22100856005200d29900000100000541c0501340c4541d07030290285d40c0c8080180361101a0214403015480e1720741c0000c0200740d03410040c903a03076101e040381c0d140942c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 584683624 1250 584682374 584682403
    0xb0f1215030a021003060315051e040f020d02130213060e04020a080630070f0f2d12060603020f010203121801140c0a11030c0c09090f0f030304030e03 66
    0x21102d220050800d20b00107401d18442d8100003074031a940f0b4440c03840e040e20300995070510903904c0c4200318254a0020901ca08000c0c40c1d1400c58151802e99603250301d4030500c1303001a114150b481912011551009041c811a82100c1015911a020340030b81d001181d10a004001c0803401000240841d0708140c426900ca0140640d03c040350b940f6542e041c880502c440e12068000c00750410300c1807040044c5042850044c400c1c0c24020700c841444d03e104003a0004442d0012a280840407004006190074078501c488085e0040c42c42c240304510048026810300c1595020000d00d0550070800e0040c0500d0742d00040450740241c0e4601e805442d030740e0049840e4807030403484c1c0089000c410085640003190114484044094400001e000d1150100c411121041150401c100050004940d0207456014240da4096110070004509200c010106640ca460b00038002c01c3c094145200020408101081a1a200840402501d4940000043c1c1c1e5840ba0300c100c8080d0080740000e0900340e05810001003030380003100724 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 584684874 1250 584683624 584683633
    0x51c060801020c1b0d0813090207140105010522020c0a02040c030b040f0603021008090c130603030f0f050f0c0312070c03090e0106020a111305011e0905010803030403030c090b0f121503 81
    0x80e075a840e1694100f07410340e020511f5504d80100b001481c601c010003080e401b4a0500e05d403410099540fa0075900141c00c068010041c10354801903074803046c03100342c40076640c1440240e110484184007500d4041280b070040e5001d42400b5402c200c29030150300c0b03400382e0542500c0621155801350350400c01d40301e05202c0250020b030581000a90188030381c1c0f449810030312010a840f030441c0301d00001f07150045050340100d41203654010800405400072070441c0f600c1d1913070038400b42c060045030018003140651380b04c0d40300c400d0001a215811000600440f015955260814541401c0200c802006481c801104401003186420081240261000064101c84071075004140003401c56070303005100903004071010303004128021241c04800050160a029101070455030b102440e01901026900040f980300341141d514001c0140406c01000c001c4035031041e0142070200d011007074500101d440121a0340401443d210214a140d40c1a1801001302201c0160409409540d1109020310b00101000c20526070705610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 584686124 1250 584684874 584684899
    0x16080103081204170c060a050601210b030a1b142e211e090c0b0c16120302150106021b0a1a03100e070807051c060801020c1b 55
    0x80c1040740c580d106211382d100b80b0503602c503400c011044d6000145070782601c0e0460410003c1482c0c8512079a54044030900e0622100d0307100d046d20982044401ea002c0407903039100e0f0055806604d003040002c2003545e00c0784151680a03c1e0203a500f8100000f4003419002d1202c01e03039417030701510380f000408210022600c0c1c100d516a040d04c0003542142c044504a10a10600d10650040000703c4850b081541000c00c0c00880c80030348500202c0c12014500440c00001e80c03901c500b04001ca142428580d0556039040c000a9480007000001131628203401440806201c1144011624000711029403030281c0c070075000c807071942050000c0102090000d010b0100103030304c181e88000c8811103d43e165202a9006000c800a8544070031002214004115442c01914000000d001c4410251803040d40100140506202c2500b00311100602482c4094a607000300000400c07589031250f2802036a8014000c0b12500304030195565212a010f9000842d6802c820700800c00540c0040a040c4405940c1800c000c1c0303404510300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 584687374 1250 584686124 584686147
    0xd020c0a1d0a0e19060507120509030405120109060e0f060901020315190801020d0618020702010806010f022e1401060806040c03020c0a0803100b0a140a21051608010308 74
    0xc8074503040500c40c424095a010214894840140900e010f41790226092030080000742c250002d102c070020000b8500010440940400300695003501d004903130046941402c800d156014004600000e803885140503c181445d00000a0301005075464400340c41c13044c1c1c1c3d01c0311107500700e00048808264101601c00f9454091400b016001105103e200c85410010744440a00b0300b203800130100b900d032040e50f98209004242c0305442411020350542020351502d0b85a80c0001c02c0d480c8090f0400d41480f900340b2841c1a9207000340941e46140c065080c001400c3d0390340110b65941d224462502d920050301c6c10b400c914190b480d00c0107440c141d52054031014940e03140c600c00d1000030585e602e810ba080550074452450115400d00813420024003403032040740c1300e040101d00d1010f01c142540c4241a5000304200c5011955007101511805124040085441c1d0101c04070581d8483d04404030401002e9a00c03a41d01a118002c0d07008500418909a203c802c099006506503018082030002808104090041401d0312 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 584688624 1250 584687374 584687381
    0x16020a020f040c0c0b040305090411090607020f0a3302010920181003020f0a06020606090a0b040504240c0915110601030f120c0f060e0c030d020c0a1d0a 67
    0x302507071030302c04d204c440f89854001240405950440000750002030850b49031070b282c001d07004c02c1491900290b01d040c07035420005009100c0c804000740145004138108130560b0b14105e0700350040c121450481c1400c021501e502e00c0e034521011302420800b208842c16644207105104040005901c02890319504038050498119100744142c520307841400354402c643d001c190300401d02e0050031006280c811031821441040746420220303002c54001e1b9100d4008020050b03000901e260021340640d4100303210740310a8040c0024100307241485d90042d0410701404100200b140340341c00604518400300f081b40300d418160000b520034480e4400005400804140704ea0000411403040d151200c0c01c0c18900b041100d0f0500341041c0c0240d0095070b920301011007040c00d00001d001160350501c0c403403401e0646914140d4505108601c10744001e0103580d9524500c0040c0a0100070603106a54010100d41d08901c041200a5903000740c1c9040c1802141c507e0400070b840200300d000014001c8440c01c032064031303a9520b0300c100000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 584689874 1250 584688624 584688641
    0x60f0308030a1109180907080102030702060114150307050304020415121b080a0f14070501050403030e0301141005030c060c06040b0406091a180a02010f03110f1216020a020f04 77
    0xc402c029212a6503154281c2c1d24801000c08101700c80f500d00042c41a003012040c1e4020b0358582d004004102c180303a404510310341034a0034680710b038902c040041c0100707510410180c00d0541d84a800028403c401390030401951180b8821201800016100d00c0c4428403d4042d101d5202030240071642c810001e4003040c0c090459030030740c0148a0100b40d9603100d0500d8480304140944100d84488000403d101085185440c5c42c03014000503c107140c80c11700000d04900c900e12015040102000b10540995000e4002501c8901c1d900b600070103e043c09030703240203c2401c03449001d210748034404402c0043d040c20010740e01c0401c0c031000500099a1291a84042d1040013401280d02d0355039a4240c1000400045401950300d0310740c8400d80030791800d442403850440d9080b540c1c02c0158082500c9100503a44842c031002407640b00c1c274004c1036240041200055a0003105102c081451b000b244131740351100b2a040c1107109001004c0980d283c2d0350361807410313a1611000c0801a4000502100b0442103041c0354005014 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 584691124 1250 584689874 584689901
    0x15040608060c160501020403030503091b010c14010f060f15020708150402031c080406050f1b1c050108030702010e0613121110020c1f02060411060f0715060f0308030a 73
    0x391901c40d43e5130682268844c2e00f00b00d003c20004014403010301b40411410f4400e044410b241040b42c45a10000380c0b045004220041c60208150032240100e4000e41040c3d0585101e10420b000c1c1a4607041c542c510300c0054040d004909801c0221a0740040c030002d014021507800c2000341c2450b070000c8824801c43c00c0d0003001aa05440b51058005c1c203442c5210700348802810564951039035040c076291010543c0c901074098543c1740003c3d4188400790000d089091458007601c06040d944910005031404e01d840d54441c0140c1051030800002007511011005103031442c401d90314012708a00c0e503403c0001600403501204c4261002cbd40092041c40707240500c603141c07035024104040010024000080c00100107401010050700b24907a40d80355810314800b010400e0310030b08696078640c003030440001d42d0b802004001500c41c90034803040600755240c1400319102540d100c216180c0e070750024181482e507000d00c3d03807015013028a40200010006640807085060382d0303100b80f24600d5900c0f845001009081c410704500c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 584692374 1250 584691124 584691157
    0x70c0b0a021317120d050105010806090402031f0b0a06020c120102032202030c060a030b12070b09191d0714130e1009061508060301091a0c0d0c050315040608060c 71
    0x2c1301c0107860030182c200c419006801007410360402000400d4544054212800348202c0340c2400016500466110001c2c0147c0c441c04c2c03951003c0055000103414000030142d00480400b40100f8066400300e100b0348014025107051380e49a1400c203071b136400c0b4032040741c007402d041802150a080341071136011603581d803600040c2100c212804203c0011b8060f4060341024011a5481001e5000c5080c400140c1c0308410004014050309450020400c01c14418014224030400c1400350307042e410b90a20000350042c0035182c1d5100d0030801c402034144520382040c3e4441c0080341c10401c0c8188904445411201e0707010219100303050aa00c1c00c81c2c0e0000410004d02000a41c412040d0081281c075a5481340c0001060345003c0003110031454400500880c401401041c00b0f070b4101140c40010030300c0040469080006040c07c44800d50341c40d84080803902410351465566411b12500c4c4242c01d5001010798050445a00f10f8a20024030104002c211030191003103c605801c1040014054a800405810201012a07a40 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 584693624 1250 584692374 584692393
    0x141908060f0912040e07030c090e0c07080c01050c12010f0803191e0306050f09060913081c0606031b210b06040e071b080906030a090b070c0b0a021317 66
    0x1014035081038112445c981100d808201890b80d15001c0d460204c41641050305a00b4205800d024075004000e0502182c0701c40000d40d0010003100c0f034211000c01104900801180c180051000001e80c0a00309030702d55000e1003c000305265841840d0740d001c44003440300031460001030701000394000018209601c103002e80002c42c140000c464081d9140b11801c960340c0000c50701d05083c20031181400010354107005424a108208098450b0300c0e40c160410b50f04181008628250301c3d0a0031b01d0b100780102111034928203a0381104111091701711601340c03280d40d1428885004c031301e0000d02c03841c01100f8480e00040c400102c88011900ca080e00403581c000150408180c022650300800d9407544680d200c800d0819039442000754032a44400912003000300707802180c0a042d071544542e8aa40a5292858400c3c2000404140c204446611951400c1c1e401018501d1a150000000d0b198088080054403e221030000144d1a20061700c21900d003d2081c81c4001d00382800d00b2604038950022158881680c030491021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 584694874 1250 584693624 584693653
    0x5030d12050c070b09060403020d030b03100902121203010806010611060f090c151902030a05190333061b241401081b061204060b0406141908060f09 65
    0x494803504008000f49803c7c10a031030b00a103481d82d5040040205494905140e07269907000c250300340c04c2c1c018107401003484505400015100101f142c002c0d581d40c071681020040070030090010714102d4200c01d042e6400c4d681c1c0d41c0410740e0184005860701070b0b280c20050009113079403144031466030000800702c105c0352162180404543c408061070001c2c5295031001c0f0320036a002800094a050500c0b0a101845c200b40302c0c4100038115000d40d00c4041c000c40380c54401980950710a6106480311701d0780300c02e5210b00402c1d07402100001c01808031659205205940c1c0071490b540a0141014003101d902c0026070503003680c0e101d140940b14040440401e40528039625420082103005030501080d0f11a5070b030400754901203445181000d414041d00c00d0004800d0b007507440350b94075002d8030302121060080300f000e0b507118a49080180040e070b4882da8000e02d004c101243d00c540c00c0100384401034081e1244035405080702080c803503400700d900c2412140d034045070028001214000106820180180c03c1312100c110740c408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 584696124 1250 584694874 584694893
    0x5100e13080a05070b13050a03120b060d06090b0108060a150c080a02011d060408030c090301020c0f010b01020705040e030a0c0516030308040b0a1a0105030c0d050108031305030d12050c07 82
    0x50200020f140842c10134103004480180340c0d01b00a926030741c1c010180c40c03503403115115034030100c0c003406100016400076610790445d084a129110014080f554640d40c02c081e43e40106401e02455074801c0c03030701d40c044440c1e50140c1a0030780507030b100030b00742035425140000f115150074a050000040082c810758100003d181c18016101700c552503000800d64050a009140c440c11594040700b007254841c40610000c00c1d146000c0b43e0b042614401e00320b59030880003022a01a1103610010b400314403a140300700d007500406510080304050300b40e081d1103456988804110030f032240d46054408a400404c617040703000b400390820501041c416416920000141e400752840c42c03a8961095005c14007100400c8104a1240c40045d4006180c020130801d212150130060b0101c03611070031a50502c80000040f8100344401001e40303503030b828801000d00130340d0303150501c094503038014006204402c101200003050301c0c500421010120f81c3e20b41c1d41c00b8044000000540c001d44005400072810010810017400420000c20 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 584697374 1250 584696124 584696137
    0x803040b03040212060c0702210a060f06080a02030304090b040b09010b130b0307080a09021302132102030303070e0105090405161106130b0406060807080a031205100e1308 75
    0x240ca1a032603107070030700610545007003084583e15550021000c100c905124041903d5140c0c1d0156003064103e4401500182d41d2500380316420402d00c030705640001080025080000580c3e00ca95061048950712501c05580f411002c070004c0d45034005110a0200990030b5224610079600248080f400d881c0d12001729204120a800030450350500062082485a116151400800070003100902c0c62404041c024100c10010340f04442d90740d110f1021505541d50b11195038204025424119a21074045041c1ea40c0032a0783d200c0c20352302914000655445900c14141911300e1a00600030390714640d00e004086401c41c0c110250705e818004180300081c01901c9922038148600300c64120085204040000500b200000901000d9181d004030700700811407240442488019074800d1105031a0780321440c00401504060300640000d00c11408001051036001456400260080e1110390311010b0100340c044c256502101d050401400c043d01c1040f04500450500b98404003e84d8a8100306460b0703903e4191176031012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 584698624 1250 584697374 584697389
    0x80d1410060905010e0a03080a09090c031d0c03060f1008010f021c151404020d0e0d09080604030813050a050a050c011713170c0d0c1a07081f080304 65
    0xd428401c5a8201d41c0c10005041c3c00d00700001a0301c0342c9000100d00760034a0000808214011603010f418500800112000d0940c00f031060000c0350a00d140280204403110380e41d0001c050114130079107485000701c0e1105d100d0a020b8007070401c581e034041d1044c0004402500e42000110300a00c0041c191000307200300350402c40004405a55407040015202c0b00c8600d58219020040c6031010100c10444880084422101405040c802d00224080020002d001d1520701400350b034140a20940c079072402103040403500300140c5071420100d45505196542c1d510850f00140800c07a4035021901e5481a14407640065100d0021503000310300b99504c160400221183c2110540c2c000543d00420f5070b040284c01c0d9020444a100121500c0e082040110110300b0300d00150200c0c0e824000f004144400c102101c0705507601404613501e41680303540081810404807000d48240d06c50008108100c0c003220742150081107542e442e51000d880d080e1043d0030030103004008501c01001c001c0700017400e40e41400a0001420f58 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 584699874 1250 584698624 584698651
    0x40b0d140a080316031d0a061109061602101d0409170a030b04062306070201030b09151c0b0714130603150f0312050c070906030f05011b0903080d14 65
    0xa13030310050243e90000084200c01111038089248403480062205052500524041400c2203803482100042c0301301800f66030031079000070b00d0640901e000151168898800c2d6482450761030302c8035003101d0081400c100700000003020300c1c1c070b0700043c601600400c01c581d009601c2036040004005030500706a200c060810082a00e0320420035040c035092280dc00103001e4a8404000032011441d03415a01d40e5041885101346400305568095901c039a010b0f041880b4060480c42681c10a2117420886500c007c9155210384500b640b4608007864100840c80764980c00a46490b1546419000341c4491440388600070503042c05015441e402c2a441c404840103002d44d403000074030748140d411060780196041e0407042003091005010000a40410000f4411050034541941c4986491110600309500d03580700a40b22410083d020050121200091079014425030082101d8110380c40211030f140da0903100500400c0048404002050b56103000700650000884009031000300c074510011520001c0e61a078100d00203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 584701124 1250 584699874 584699911
    0x1603020c0a050619030f1b020609160b160f080d0b010909090309060c0f060c080723030117010603060c081e06060d0b04020d060303030b0f040b0d140a0803 68
    0x1808079800c8082e1505654142c038007081440f541c400900c1841000c3c00b09a9981d418110b045030680c460380d618410b010003052a0f005144000307607101c00903203540b452400703110486201020904800ca0031030f0081412541800c02500c50200b861800d0902514501081551640041d0081004101c01c44486400191800040000604002003034001c00c0d0b1235440d2006100100b13411401500c101d450600d8000848003541c0780c004d010a9045100a004038103103d02c0a94058001d15098402e980c56502c490204003035404a6640360b0300d4507140310840030108018415240c841d8400342d030110f1403000100703c15aaa5842d03e04072104c00c00384c04006220701050001400303514a1103400c01c17811481c03c83c0f83d8108400001d600e03104550016841550790000d001d80ca4856405441d84070b0f2103000108821a0390341005009030107898907407071044a80b520a41c1c6146041d210380910300310050303e142400070259488400701c044000b00c0800c40c0c030915040d4000074104400071840341440d0401810f0300b10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 584702374 1250 584701124 584701129
    0x1106070302150c18011412041703070203090103051501080f0606072306070207030308130311012904090b010506030406020f041404060f080a0f1e03021509010207150c051603020c 78
    0x2800c4ca200710f4104040301e41c050040408207000c4c0c9510000f4280c019199482d513152a2500064104c2504191000403080194580d000b02c050b01c0064401c3c0c801340281d542c0c1503410b210304002c081405000ca900040070400580d0710f4000300b940407101501c468a0420203071180c500c60034814075810a10341d080e00001031044001d00c28503801035040d000804115003190386c090001d140051064600c0304200b83c0315000d140c03060b428200c4003000040200080d252100707132b11041103400c43c400840c1510b00d5400002a0500d4030500d8069900726106e540c0b164245402c11281e030740043d105a80c00e64092100c030b400100b64500400c0280f0780280200141e03503c1e1b00071f0009036910750740140c2d00c07101d03581e40c1000340240c0031520308101640001b16008214907460030060114030300d9901c0842940b5800e400c0101078000506e09006803005451495139651003580c2d90070307845030b0070000f0901c10442c02d0f01d03c282121904420300a8402e03007001800c0403042ca8621911a4003000103400603441001d49800c10b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 584703624 1250 584702374 584702407
    0x61a0706050a1512050c0901050915061c0c0807020f1f151206150f050105090a1e0f0b0c0703200402030a0f0e21090f06040602070614071106070302150c 67
    0x301b800e407512801503241a001840141c00100ba042c400c0c044241c00715819a41e06046070088011490030f00c0061010510310b070010440f103c041d1000c503004001007280c0a000003440000a07008000808040c10f0a408003600310700c0842111001e141c482000116151000030084050141c0700782d00c03648005c03181000029141d1302c009403099141c40c0c150901442520600002c156042070910640e5139502c40082840e042555014160200220791614014102d40c4408012a0580c0b101c80301d0712a01d614000400e4030070300d40000116440018200b001501680390000001024003115400d08405000700e026684200c0751040c6403a560780110100e503480b0301c100e410391001c000081c4800900d0541d0810b09240c6882c1d04410b484000c41c428104e6038903950b04050f0705101503e030685403565140080e64440040c040c450104908000c0c858034441d035801514603160f00201e00b81c2000b075000080c001f481d0303c482016011802088050101c001c8890f401d50b010300803451950b0f1380e0b0030f07030700380040703004c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 584704874 1250 584703624 584703643
    0x14070303020d09060e01050301090209061309020301080f01140708070908120d1404020f1203070501020d0c080112030c03030f06082a04060506031b09090906010603061a0706050a151205 81
    0x1070200e0030480c0b001c17076640072040d6415280d800800590700c0030450700049440c05201c454a520841000300491007500d01c0e00034504960540c01110304956121414074265900c004108110721b0f280000559120301c22414150000d000381000c42a50791102040c90030403212500680040000040c502d2012180b80300d00308280c80c0d801101d40d802e04044d40000c00816003c075803144a8035817035501c2c01c02503c040c0101d070304465010000710340d6000c1412064000c0c000142d41e00c008101000000143c0003060880c1c4d0841300d51540e41d1101c882d09540d0150000c08100700c0700c80500356a000081a40281004181440f01c140b800212400e0190826a1481c1e404200003501a42c202035003000745840f1401645d40140485440d80c0d000014615011102d005100400380c2c0061000c0c28001446400705403e4180c40c41c41c1d500f48400383e00d8100c0c513000e8030607900c5680c040300020812000400c010354000c6400644550303000c14000400a50760881101642044110f00019440f42c02000802c1110340d50 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 584706124 1250 584704874 584704877
    0x1630030b031e15061309030909050a06030510091b14150903070605090619110d0206010b030a1d100e070519060c0c0905010308030105182214070303020d0906 69
    0xc0c0010040b8010b44507180070495403c25200100443c07a540e13500024850600410700080000541505008000c0011f501c5204566460080444c03041c0b01d003802031505903a0420004c0c082d81d82010704a200504400000b40ca80340e45010400d42d00310301b070700c000c00018600540740f440080d02178820000048003186640d2180c0d0020009164aa200820781c00200d0b03049081c01503c81c1081004101c480c07042a41014421520f103101c039004640000714a0715030307941d440443c0c2e13520720140c4090760b64600030701400e00b03d03600500003d42880100d810040c1a005551000f100c00045072030424035148a94001441d03158a4860202024004009070001003504903401000b0070030340307403100078564900e000380e00410001100b0f06041c4003108081000610301c0100401c219a07607410b0180141e00203014240c480d81c400c0c3c1c4c11994902541000324010415001b40042818800100070074164a4002c1111405110054444140307000c1c040c0da402940690040c060800302024000c24004080c4c11080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 584707374 1250 584706124 584706163
    0x90f04030f0c0b0c2b020a1211041809020a0305010b030d1404092403110f0603070e040506032104060e010206070801090203070507080d1509021630030b03 68
    0xc1c00b040208000607004a44d000140c1d98440b08046000d6030b0b1035080b202c801080340503402c0743c0d00c51042a401403000815940c0d6a108500d072a00242c0b058a0351080030700c151810500c000d00203d207803410003501c2500700f080d0004055245502242e000d001c40d500a46040e5502d184295030f42c14180001101d111003454410566522119809014081c0b40580748000e82c0c0c4040503203408401c04003400340300d5a40400001115681d1a1400300030310030b410402d0003402e9071040881641845000d903400740fa1113490f4819010284014031006000080c081941886050030b0002401c114911304005070700c1b00d4102c103070b40d1802c20501818150100d000707030341190b00c4138081107070721a4080b0310141035a03401030000d42d40e80c032480400c45550040300400f411002e0001a400391084050b030004c01c0030908035100110059680300c9000c1240904122111901503074450000003540805001144d6041c42401255650502e0801141d0001038066203020030380d0f03660300c07101c0f0746410018940803462501c1d800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 584708624 1250 584707374 584707397
    0x207020105040b03040203191101030f05070c0213110f07020f0d120813140f070f0506120606070807081e090a12110603160e0303070f030f03060302090f04030f 70
    0x700a4400c1d0320889610980110100e4115034051060b81002811035881004c04003407810511a00030f442c011980c0840e10f0034203c0c24222800d0b0081d5031040c043c42c5c84035200001d603902440540114400030440c0030b0f03a14075881c1c1c1d81c440708170090010100311001d865102d20051040c09a0070001d0500d0341d10440c08044580c3c00a0300d150041700641d0024601102940c903540c0044240e0000302c04c004192818480749601902000551071039600c024030b0032500c1903540c402c0300107001c0c680340c080c403500007404204000d1840c0710f8004c280d82180016201d1031500c1d11035210f2000d142c0100d8002c44c1c8000380020301c00f6012484020a200d02c1c007445400741e03d00458a000920040d1680c8900c0002c078034014000b1041c410f01150550320003101810701543c0e4901800d07c0144a14840d0844000c1608045260700904000040c0c510407a03022009225024075501c05130b4558409015007020151180c0001c0016100d0035002c0380980021010450b01d820300d45005400c000900703904004010000069 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 584709874 1250 584708624 584708627
    0x1150207090908040b1b0a1a0f0f0109090305092e020d17191103072304090e10060902042c01150c060213081207030207060806010c060905071802070201 67
    0x2184d04580c10f03022282c0d624440c0304184072000c0036000b00c140103809020044014000c101c12001c0404040c07000705011551303000d1112009240998074945841c08000041c4a8506d450b40324054040c000c0c1402d80c02d102c01e201c0000e007641d010f00c1d401c0d6002d00e0113070114070540648000350050302c0d8260010b4440030549180040404a0290031011451034240c0072406400fa103120100e03a07510a403800303002494002000c40d800f980169038038030000c1d0654018031061074044143d003101e409905c681616041c505200071300504950368024410b030045002c0208030f90f44070301c105002403103031032000340c3c8640c84d21f041030b4412000038a00801d0101d0100010522510070248281502c3c41d0440103900070310304502c00c4400307141c5600010201440010780c400080c555040e02d000f103c031920101c5404440540c01101d160107111001009680035900030310555002d5005240d001c441031410b6074140e00142c0300e00040e501020b4040d104d58114050500844406904008103402103d00035882c00081c2c1d0300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 584711124 1250 584709874 584709877
    0x1060f060206150f0913150b060d02031e090a060b0a27060b070609140a0f030c1a0406020912030408070e061302120123010903020105070201140301150207090908 71
    0x70000381007a8440f244116a0f031044c11034900c64030041c1c030b00d880b545042480b031403044a82c60005e403020301c1400a1417240c0c06090240c504070b680c0280445042492481c80f08000e5040901418012907841780383c40c0d030210241403038610565054000304010111410a0800c807003248881c580180300000c410301840b41c25041c00104106a072920741032241040305820003e00c09a002022407030000150780050100d1034000180701170260421083c152840030b40117a032840300000044c286100f072a1a040400c6c09424004410760103000103100d001c103003641c603c4101c6021541215501d40c080350007c0d090501c8410080c00c80c44007002146000d003072400460384d5924510440500c0c541c00000519591030b61154844000100300080d911506400d80980c0381f00ea09010b20709000115001440c00c101d9126100151450b060b141c00003101e003150011600342e03104103816810b0088024002000100040040d4002c001720116012201000c00b402801c0203415441618864141031104d004615503d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 584712230 1106 584711124 584711131
    0xa15170714090d0c1a12240d0609080d0c020c09062209480506030a0209210c0307031112120f0909090a031e020a0605010b0c01060f060206 61
    0x90a461408904e042c00401d5054884c00940c408c0c1850703001210518020030020401034160380342e13a107071b0760302c490070700c844c0199102c42082e0459810b115050a440085800c0b07500d5050071b40010b43d0403804c0007074000031041104140c0e04410540c2d44000043c0b80c0c4403442210301c443d0101d241e00f4815001803081d00740b410315001002803141041d80040c40d00803904004803200c0c1000d0074420300d504020500300c0081d038204040078181e6150314600320f80841079401202c0d080e82402010307041902d410710f0f8078040e900c044000d03c009680b0020010f80715400b5500d0b1012100c85100040c5068000c6181d5985113400240d1024418581d000500400d00c090b6001c01b5541c44418a0565030340d0f40c50405000502e241460710b410390b6000100f540c454480f80304482c020b5400e51174a0084940a078400d00c0c1e1403030300284a80d20b040d020b005600052000c0244081c2007441c2600194607010002d = true := by decide +kernel

theorem cover : BRFrame.Cov 584532374 584712230 := by
  have h0 := BRFrame.cov_init 584532374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584532374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 584532374 ≤ n) (h2 : n < 584712230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
