-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3325
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:19:49.023961+00:00
-- url     : https://prove2.me/submissions/8f9ba887-e377-46ec-94ab-b2b187f158bc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 597841726 ≤ n < 598021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 597842976 1250 597841726 597841729
    0x60b07060e120a020114060a0b030a0c1e03020d060e010b090d0f0b0705030405070e060108041e0210030209040b0a0b16060b030a0f0b07030e03090103020f21010303110f100902030c 79
    0x243c20100020025035101c14030350040c400302a140310303400344003210202a42031900e080d16805e0311001d002030f038000381c803141c4203041c0502507490044071024202007a0200c01c0f05140c0100250000c05c9021811b80c1411000a844203503007007a18143d4290a0005240c141804d04110500074484012200c2140c03014000e000301d4111240300b0303c00d5219469841d560700d011b2030541e040131202c0d000a44107100e040248542668440000f0394402da0002080e2600e00071180c038071002404003480298420181f85544201981c5074014018030882500d040c1b1804142008100c400122401400c0c02c640341406402e4a10030f8803020f085c0494021000090300c0c5c00f549000ca410961058019100404200140e2003001102c84040ba400b1459140800c0b001c00100e1403d41c8070f120701c40c5614100b54000c200044200000e00032600d0265071088072150003000c0303c0540d44400024401130f404145074403500701011201051107030707041117044054910381c2c0c51440c1e07030801041208001d80c0c25105042403030b04c86 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 597844226 1250 597842976 597843013
    0x1602121e0c0c120a05060c07030c060e250b070807140109060506120f060601261501020606031b0613050d033f02030a110703030c0e04060b07060e 64
    0x7020440c0a00307001c1c2d240b1000c0c410740d443da0649821581d40070f240d0000104002054141d040303507810440c0342d5540120306040f038003c400d040003c0d11581c58400c281e031280d80700003204c0e8502100941c41c3c80c16448800350389001d12130188242040c481701000518005088007009158aa10850702c039080c0c0d094000d90306003161034514045030310568507020300142c1e01d85060941120550b080042c01c0ea80010090700d034540c0d801405040c103024030b4080882d010308903406650071440c5203da10b00b01d123103000b994401c040700a000319103000d40903500128060782804a00c450011850580401e411800b440a2160942c441c402c4415003640c4a80d0200e9159203402e0a0228030340290f5071012515010300d04d1402001540c1000304150402c0744a040010700c013a044c55090103916680180ca035038030303811004050311601701c080030f40f1400001c003c002c1580661101d4000600d0341e4030040e0410014040c401101e845000700c07001d1300310a003c3c00e00005c5598102c8103844107014107aa02e008030b204000c998 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 597845476 1250 597844226 597844237
    0x15020a0309080c160e071b0201030615020303160503010806150102100c0816020606130906090215040815190c032a12230c0903061e1602121e 62
    0x440e400c4018000c56107032134030758100b010302144610820170781440c20004d801019500400c046900910f90b81c00f0035603000c4e5200800800f404d00c0088941101c1940080d101c1c2d100700e402c001c0f085401003284298a101d04d041d68180c40c102401891162900c03c801c40910071020f03c014110710801c2e04900703080d24940100880c2a0340382e241c2404c40d040000046415100c42426141190b00c9001005080c1d6584405014002e210600004030022507042020140501c1c401c00381d082040c01c0c8944420040700f50003041284c0d044010780b05826112121500c180c0410f440002c44003100648000980d002988605030b250341c582030010319a0140c03841d80610b48001c103401030403440b4420703090104503000480380c161b80d01044004c2003420740ca5880e841d518180035114a001e80c00c1140043d4204025100b10380036004010202d890380e20302141211540c00c00c00f41c914458021440c0443c0c04000c44124400c4600010b03006042555880046002d072500405c13904040503411030b190001801c4200000c0c1b1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 597846726 1250 597845476 597845497
    0x20a031b081314090c031b0d060605070c0f1409091515012a0803040c1205010203040c06021f05060a0f03050c01021e0304050d080c010e0f07060c15020a030908 70
    0x10704480c5460804010f0f003c1c1180442e00500038101004080000030080301d50044c90001592280010460a00303498001c0494103425a07280034404243d054002c006024070324481e10a0700740041d1620b0541c841e240291060f80c0740540300815203081843c0560f010f40c0c0c02440281100d070f15480d816581000d415040d50007006c0d40c10315400b1710300340d942d0119079030081002c3c0c440c03403c007620304012810502c01a01c0c3c03c003400311240800802d040200d80c0c0466002401c018106100141440c10018000d40c0141d070f00311444191981c000036110300104102903000300c400619a500c459040c0311201403c4000e00f415441580403a010032146c50a008035809103002c4d400600320075400c0300000e8a0040004041c0300e01e10074500311080754580000860303098502c1528a20360091080c6810b01c95402164481e038000c1d401c080c2c40c0c25804e2070000c3c40004200d000d4044482c40f0350f803010187e03100001c1c40f1010f080c3c0001c1c0c05114005005030b4004140d80f0b807961034000f940e2041500d404c480c58001840f0b04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 597847976 1250 597846726 597846757
    0x18100c02011206060903080705071a04080d09050306070c0201110d020a0c080105060a03030c06020f0708030403022b030b0612010f06180b180d0b0106050417030a020a031b08 76
    0x51080d56441000304252078070641c010002181071200c081d00d40d9003e84070040020a000510404000d03051007600000e099101c064914404800c030031610a811600810101d81311321050218218803c180c01d008452024001c2c10842e02c81d5a803c40d50707801040d81c283e0510140350107002c0c08000c02c05c80407401004542c0541540801c03840c01d5103650409601985007a8188003d0003032556a55130a40100c9034581820942c124451034020081d000d08050003120500c0440d60b10180500d33031008520032803203a400e80e017243d1894804882c07400610b9072016540c00002d1034508060b8003030f81c00400e9102c1e00619050500e000f0912144a554090304550b1f01354600c00c00c2081303504c1d00306035008051143e58050030724041c2800390181780760140101c42110800c585011040c80d803070b4100d041780920f8201401c08250368503170388041c0c0168490301c0784a2030034010a400e003510701404416600c1c2c440d0306502074451282d190320119070122410502400100c1240740c40340019800b00002e00203160036240c00d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 597849226 1250 597847976 597847997
    0xa17010b062101090908090d0c1e050f09101a04180204060f0c051c030207050a2105130306020c1507090501080a2a140408060a05011a09061810 63
    0x1d16042d40040c0c1c0040c2c415801e00481500003003102c1c096415201e030582d03400703142400d1406c100040502982c00210707414413000004400055090b0450140d50095650060744110300c400c1c403000800480e107000c0d08104004052003642140303a10604510f104070b10b480d0400d40c4545c441903d040d040362210486540c001003c2010079000320701c0c0354a5a51a0800040c08101c6445940d150700c030a240000c407d415001a10090303038040e90581f8113040d044004ca4001c102e507850b005000180795480070359092020b080120312a0300c2801240d4495200040c08001c061550b0749420180d04052140d000c41c0c082c4001499114441d1000c15106189030340e41c090b2030500d003600140075100c01822102009040c02c201ea05040b0007881c0c900b5a044071150003103055074103d0720403030b03071001e100d10348907140c203000140055690400030303440303001c0e5106036010006643d803221002203840140c110000740640921108525241010142881c800b8094079140d855003a9000030341c1c1c20f0f1780c801c290804110480c11 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 597850476 1250 597849226 597849277
    0x913090209100602100c091502010c0e03011a060c0c0925030e0a0209060319060e060c120f040f020a0905070f09081908070605070206010303020c09060a17010b06 71
    0x440340d007242c0700311101490305040041c020748400300610b01801054484010078251403046143c1fa0080c101e01c90124041105003400901a00ca140c0414000130440c01d4042100d21f8188204070307900329001c92400001400b481400016007005420442902903a1b5192600d0b0303e0300342000c4c0c89510b405056000e540a24100100c070042001180d1042600e003d59070078030000c00244054116030102e941700349994943c40002d1606400808112448046c12521020408940c110142402000e03082d00c26a45d43c0440210040c00f444074104580030703404021070a1100440c21040c0c2103402a03218100381607498012607a281072542c00b250000e80d80f58200080c0f40e038810a20100c87d8401d00d0b04007051454a2007a9507a0050030340628405604645003d0802c1114411180c0665003c03034288071030b1400001c06901d0701401d10043d8090700518800d034020f842c1070a1814071a030703402040200d40700e00301560030090f003d141d0341342c0704559030f900d8504003544c0e83c04010700b00c0383c40c2c46802302c00e0750328542c2c0c1c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 597851726 1250 597850476 597850489
    0xc0f070e0c0a12050a0b10110f060c0f0a1b080405100c0c0b1b0106091401080111030f06040f09050304090e060907060f05041d0103031d03060c090609130902 69
    0xa11055101800340b0107010101c0c2e20641c0c0c3c00c600141000b021030980c4414240344024000000d640341d10041d040e5884583c641c1140c504a45280c1c114141c2d03001b4511010010740b01d0b5800c640b1014400c0c81081440c401d00300420181501c00d525103400750310311003e40c40380c890081250350152078a20000c1800c21081c98400380c1c2c914000e1141c605807451005980d80c02c94022600d002d80581074202054403090b000d04000d0308401c0c480c01d840280403480c2c0d903040c403400034852008070340b000118803400840c00302c005004003100711140441051659607545a20320205d6400780400764466101c0390030101c8426240100b07804640244055170382c0d5841e0042e003030125509000340d0304260700048100555402c02141c0a41100d031142090794030100b80400171030b103500c1030b504455803a001d00f0310861420f068040e9418140d03482611804098507003c08400c6603100001c1090794903622800000b507000c20594081e01590740f0262100e030802c0c00305400281d555140f6150550060703030300c40000c2c06501d0540b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 597852976 1250 597851726 597851731
    0xd062003090a0c08031c0e03072018090c010f0c0602031612090b13020d33050f041101120222120206042709030c020405100b0a080c0c0f070e 62
    0x541c0b4103001d081440c80303103a01080d450000d687d9a0b100e4050702c400d0600445400765849908105110a69008004920f4001481a002d62010303045070407640401d42545000c0c1400c1d50040c5400c00349100111006c40000342d034401080000c92201000901ca8006540550301000021203000b0403100001c041e40901d10800c680e060034082c401e80890a00344810390040c00c0c03e841100e09a40a0011552416000a0080c000042d001c417069080302001051140781310890415520391003000c441d0002e0310000c0d1801c81c0c03001c40721004500040e0404600d0012040e040c104000d2124a00b0144c10482e000b8840c5030b06071901407032846642d800f0394080b21000d0720034900411034455103900031414a00442c025800750f40c0070044c006580605126805007000b403ca40284401d41c00da2400428078141c2c10001c0303008609140101c1c1003031041c100024182c03112005a50f00f008140202282c902c2005031011101c01c00c00c10030b514801000b4840c0760355503c032050040091a142c40d581c8200c4c5c5000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 597854226 1250 597852976 597852989
    0x9010e0102071214070314060a0606050f040b0c1f0603020f0a08070611030d020d1a0f060307031d06010620010605090402060912010c0e03120403020d062003090a0c 72
    0x10b40428056049055403250035190408005840056001d100c5842d0030b00340d070809810150060003102c0c0001c3c00080c1c0a1107580d400c101400025a1414142c4031401961243c0801030428401445014102c00240c00c40c0e0b1f42e00c81c201c4103042686d001c0d03c12000510f103004000f080d114142401035041612031400427070400d40d40001518036005256071500c100e4051442004124003c52401190400580d00c904a045100f19901c1040300c010070014480f00c40c26008801600d1660520b034074088800070680c10010b400c03289180e680610850003803001504140000e00e503000d10340b034164030400606000e09541d0300c801544d014500086040302070152034002060b0304008050010b610750702da010350481e60544400780c072085400002070040514011680c003545c80c160328614001d03403141e00b0441d031030400c0d01594402d1020064019880c4140e00010b50450f820b141d5010018100f5800740034050540600990315400001d042501c690040d5003091050740303c1c1885a007440f040416540040c400b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 597855476 1250 597854226 597854233
    0x3030906030a1107050d1d040c020606012123060603040c03170c0d09060f09060206011205190f051b0f09040c080d020a11010305040f06050705090907030209010e0102 73
    0xa20000940c00d44002050554510740341e1880c641400203800569012591000565542840c000c03002044032030040711071801c4004180600752070b03007094482c1c40d5480089078007924041c0c0c3e581005550701c81d1001c50880d102c407a624070030255807880344202c4004051480300d9038040008250740e0b420242021700743d94815442042403100140c4025042c0c411a68444c412601221401c00e03864841d0003851300315001405040300034085554800b9485040d182e854548488802020000301c588507040c1c000c20025134084c0c00140a01c203100001307501810721903007c0b100c0711000f00200b0440d20030408403c0b02e50490101241d020080c00f400120724198824112402000303040c000a84030900c0e00c015607001ea9001c0c00030405000700c3c81d042c2005000c1c00d0044a1421010810003540c61400301002d407103180203500d441a080d8407901a8502440d000f08240044588903240d0b031000b0600680200c0502504004903070740c54450300e00c5c1038400d03c1261001600e40f0000c8001500c0b04901c0c030799aa04640 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 597856726 1250 597855476 597855487
    0x30105010f080a0b0703020d090f0507080601061233060305090604120f09090513140c0d021e0a09060e07021c0e01020a0206070507030312090224280e0303 68
    0x1c4000800303400d42134210020000c662110b40040e0028400d40503c07010060800e1940c03818800301c02110f841c19849907003243e680d40c1d52650083e03100e0400380900ca000600e031802c10b000c00f9616400c400380121025420b001c034a00301c1a03c5034944000c0404a000495030410208001d0341c0620070140c0c81207041002d052107141c01d1f0f0742c04c150001c0c1016100e003404140060301c3c03411407050008402030281c2000c02c000320b08042e00c1c2105c110765142c1049400c0042c00d048081c100303c0114004094901c060b042c0c6007008600e03803c10041003002ea414240c1705200354803442c3ca660300d8003400001000f84000009065003445001d840c50742000300304100f9544180001410102207005000f1054541d20300501c40a485400407800c003040490080c2d48440041140320074041c0100b480c2085a1003a10f174030420a404014040980300c4908002e5404048881d00000c2c031342c00c000b041c00b00d1444400c102450811004c081c0c00c0ca0320030485550710860041c0d1200030107030360058020301da5294124000c60808 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 597857976 1250 597856726 597856739
    0xf051507050715050c0f0c03010c09050a0302060c21031605071a0a09050303012409080601050d031e12050a02040509191d0c1e062a0f010209030105010f 67
    0x1100c1a01c40c28103250407034001c00c000c107445a82a1104060450180d408040320f4825503a42e40070044042c5108c0d502c1e1040012195005000e40800c03103030042c02d02080c7c00d20310f40800909800601000a45000b03a941d840342968840c0840035400d5903002c6016201e04011000c0d074102683d611440d010301c142002000c0c08580d155106402c0e0003c840c0c1c400d04a6600c902d03118010341030a820080480c480840082034491400f007840da11450700e18044c139010442010229141d070b84902c501da050342c0141d001401141007004520300800c1c040d0030040a10903c40100d245914550000c030b00024400d200d040d5480101401070f181c0007400320030b0a41c1464100000a404074102804a4000d41101c5180c1e086203140d90300f106c04003102480c003800d003803160041c0306c80c0c880e40d008070755506c241000c141110000090b48840e02400401034100f505005642c1c0342c004c1032803040c02041501003800c0c851451070000406c0030340741c0003d1142c000340e00c403280302d400d0600399001038220340100b90900740284401c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 597859226 1250 597857976 597857983
    0x7050a0821042705060906091803070c060f0906020c03250b16060c0201020301120b1b0c3f0f0708070803060117160c020a050a0f05150705 61
    0x515500005030700c051044400c241052141e54003001900e8124010400c20940e0203507507003441600240180455561201001542d442c00c80d2015406007404000c0746501d503204c150000600c241c2c0046902d440360a403510600450f071039118000041810103181d00e04d580c46901c180003007416000038030140d0755102c0065180c030b5550f5100301013140b110aaa620007280780000500500c0800301240d503c0d0744960003050640e04113201980d605003000d00440c107892051080364120b80700304031514041c070820f5480f9a01d220010b000b208a2240035994401c01900c40350042c22281045001040c0390245443c4420068044080d00f1300b442c50a61500c10700d040020a0402c0c554040c03101d0b1640d40c0d01c0c202c6c40b01c0481d00410801400e05803010405000f0880084015805200d00341c17070300c0301006800b9824001004044402c0f00b000385490100e5076120b40503203401301c500c0388024403070320403503071590041002080140e03c4602d03d22a6140100305034209844e0101051203103240003440d00d1a50349869a4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 597860476 1250 597859226 597859243
    0xe060907120203340806091908091810050111030a0302070c0f12020103060b1e0d0204030206030a020304060b010c0b0106050d0f1404030e1e040f1b0c030207050a08 72
    0x50650458503100719034050081844c04100304042032050682c40c648904514000100f003e100303504200085040c0c43d000994034407aa0620b0000c0080300b2410500c2101a010b010003201e0505007800325004680c0c6034042c0d800c1a480c0e1010030301551401c0360950580151581c03080d410300420b900d070340003034910100498401203054140980c0d10304040c03800d01c0c0c5142043d44044442c14071400c02203500a4a141103d1804d03000341e80a000f40c1f0303101e000701d086074441c80420500344004606001181c0a02e0000b610a040c1d80706401414542e0302e40114045510072100c50881c01e0340001004100125482101c040b10020701c3c03c03c80d00b009655650b02807a00601580040c84404158040102081e03000030440351885001032200641010760401c6220080d50100c0100322401000300b01c904081d011010908009402224101d51100500c40200b078a007141505003a141d0074000c01c0b640b0307810710503600c044d80351743c520754600305c2420000d00385084c641080e48500c040e00000c104910700010b4000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 597861726 1250 597860476 597860489
    0x703110f09091807030317070f0815010509040c080a0f0b011d0a1a0705101506081308040b040f08010b01090306150801060605090a090c080705030709080709020d0e060907 75
    0x2d60686075283c0300c540c08072400801682c1803145010100406501602c00c0c2d890b40d18025514105444018050354021000348001c0000707490400010103442d036502d10110f00d2241030500c0c40ca8004850085800d4070f20000c4642c0c0403440b01b6060019524040c403900100c1800b08000300001001c58000070b10603012840b51748826202c0c1020b0040666507500711500500c10604d42101c112400c000074516904190001d5170359010340c06d00b40c030103003c5900402c1003030220090326182450501e2000c0d40da43c5806032071a0403100034400541c001900100040c006010701d00c803080d8440b07140c6400020100d140e90000b00750390741807140740b0302642d0300070002105995200d0b00c0810009000b486542210100b130703100d08010760800000049141c0c10000030138001c2002d03286005580d03110020720042d0713041c0d80000d9001850340c0700080c031058410009150882c0305071400034000d0783c0d90b80f4550300e041c01681011038641c2d80044c030000200002d1081d09003015500e005040740e0f140c60250507407940464401c25 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 597862976 1250 597861726 597861739
    0x303030403080a0209030604210c020a0504090c08030c0708160b030c03040203010212070e0109062c01090b0a03060906050d12140f070605010807050604081209010302070b0405060703110f09 83
    0x5900c3c55164040e590080c50240403075480c0c1c9002d06103030301c0d840b0618101c41c85540c009800d0a000703501c44c8007548a00c50300030b0701460b800d610307000074000180b00c008000d8841303000c2c10a000c100c024081c8010704984e10914001d01400c2e0030103c0c020300301a00c0040c1007000c6003080c003081200d0181001542d07413200c00819000d46070765441c004280a449200c1c0d0f890020840101000b81c0d80d03402c1050b03e10704580a0341c4034001262074910a80303001e948902203202c2c01d0880c1070001043c81c4105c0f001c0c51000030606d03252101070b0350b402546426030460340e4444042038540009000020081c440c50004040484501c00041d481d0744968500300792446420082000c00180000c2d002104e40031169000600030b5480d903180d9141c2040f40040000307008120690142020000301c0e80361140544045e80d00000180110760349000c1102c201e40e2107006054103143e02440100041404030300154480e50040c0050000c901c0c29a0740102150122288280010014003c0581400d03404c0181c03900f50a0503a1030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 597864226 1250 597862976 597862981
    0x8060c0c0606040c09181d0102070203060c0313241a0f0405280b040b01021f05090a060c02030913110901030915020c0304060806090708041e140d020c030a02030303040308 75
    0x484105006820990340c03c0082d200b2040b18401b6903100b10070380c29200e0244030440381030581c000d00f0b07481011000382d415440400402c10003c0d51300002e540105410303101804441072a80da04844203181d01000c4520307982c00c29010740300d810030700840780c0748814030340c4001d1508480310002d500b00b00e030040500c2c0203030f603110000b1302c0034401001a2690300d00f0740d19420305003001111417200034002d0039600c140214204034801d01203500002c0c881d60b62900900c1038486800d03400c82c8044c01080d0081a21b9104e12034211084040307015480342000c10142d90307024550301d600c00028014802c4070403580003070792441d00c0100b100005444043c0e5000410900e40030406c0c060302d00780301e02081c200c41c8245803218400115140400c40000c020800c403041515075020965070300c01017042c410005c40c0c0c820007250801e4002400100018054070301480103a03d030301c0c0a001c0c07a884021061201030030414071917101c003110300081030701003141603a100030460050035410015030119480b0300000c0d100405000e0b20402 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 597865476 1250 597864226 597864251
    0x7110d350301080c030106090213050d0510020a05030103110a2409171f090f0b1909030906090504150509100803030403050a0e0f0a2102040e060108060c0c060604 71
    0x40400c122410801000e4072543c55505407a1182c0011136094400c0d8a00840069408980c0c000e031000081070800aa00962601042c000346648880b0111030032b0007146007030207000c0201c4c0702420300801503913100d17a04c940c114604000000c00c4140c0302481a00009030402c9101108514200c401f401c212031088030a80d040c2099403e500c203038104aa070442d001c00074204174100090046c0c000c210600f00100c049a509215500b129002e08016001a03034088420011604c0b40716559081040f0340501d1403110740c46448031044580380041200081c24541c030402006a0100e40600030700000c40c1d04001600107062621000c44c07141c401e0324010502d081c001740c3c1090082d0b00900040ca19901030300e03036916042ca0300802d60350100c00d00501141040c40080e6103400c1c844c40f200340f505c1001c1c04100e84103080c841103001c0d0050340360b030b04039181100d100c1c01c00060b259806210f501d9000500185055414101e00c1ca043c02002003041300b881c0d0040c40444040c0000081843d000503043e41c00040c494800310 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 597866726 1250 597865476 597865553
    0x20d080c15040c0b0c0c040c090e0a05070212070503040303031a04020c100b22090305041502010606030f0c081915180e0f15090a060501060804110103110405011d10020307110d 77
    0x600030090a10340340d00700b2a84101c00e03041640305007210384c250381151001a4403cfc85a0185c0c410180c40da90052005000081c0203900150070351050748070900f60b51031110300040a0380c0c405180800355030441000355901034490701880c2110700d4101c0d14420712001d901c0c188480400740c65182c46d071441c3c031358880006042c000c008413009040c1000000003c031011600c080d028212034415100000c2c036024991a001c4500e02c10020400360365030b03030b184aa4540c0000004125914542c181c1040c0d80c2c0d031003034075201105642c3c0100070451040344c051801a80300d40c403404c03110489600d01fa140c10038015800f0380980403c00032000303915141d084415440304240d40d498490311442c010207203481d040c008103005800c04680c2d8400c2d84201000e0034041e00e4040110b0650300000d580d0800b04100380414045c42d802020702044840d410070142180058900005250307064100404015800025508d42401a49000340c0c00314603040da50300801d040103641d5200c50b030101c001244101070012030790390b428142c0b18 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 597867976 1250 597866726 597866729
    0xc0806030c0f1c0803130b1005180a0e010f0c0201061d0105060307020c030601091a0a0f150c080a0807090906141509030d09150813020d080c15040c0b0c0c040c09 71
    0x64640b6482e468014030801501c02007401c2661f0380d010325000112401c0c9000407550036560007608a032036040c203000d03140c0116040600394110302a203909428010034402d11400c2090410a0b4001c074192151480103406c5400c00e8001003540f440307100b0b011040741110b580709411075170103650f01e41d540c4d0b86056040b410300c6454080f90342c1c1344c00789200010301450300d03400041002010074540c09000780f9100801420b04500d104207a21040d100350100501c1e040c000031340d1002642410507005a03681a9500c840643c4540090800f1808010500c2002e503445240d82002c0c6c0200c0404101c000c0c1003408141c08207903809481c501c12100c4160b8580b511240700d055841051002d01203407445081c54601030000000ca0092a80840088403c2d10117540f040003001d0141c0c41e5040410b80c420740315000d210404001d8001a87c070000b0810010103601d40401c1000481110426801060f00746494114440b45055100a441c4041070200520706040820203c20441c41250002000b040307401c0f054442e840c05 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 597869226 1250 597867976 597867983
    0x507031a03120901140d0605040b010f09060827030c0708030f0d02160212010c12060f0e040201021f050901110f031323010e07080109080d0c090b0a030c0806030c0f1c 73
    0xf0483d500111503d070000c006440d0109c130203100303d011030001103035140c0c0c5400184001520342c0c3c2c410401140a10111a0840d001d41f65001010714541c4150040c8601010740160a0f070000901d8140008188107120207400c802002e5854400103244002c4140506000380c10342c10f038001a41c600e160f0341917030750400040d8080c109034400c1414010041c024100781c0031240109000c00c070030f03844c003100d14814503080e1070070041d40345081424000760240d403010050049055100301012400c4000d541044000b021200c0580884e03d8503184c22154203483c00800c030644201ca0500500c030b0035010020581c1e07402a0023002184c0980c00340c0c1008254842d1184400c184810403c0646810b41c006400c9981c0c0000c0450031200c20594980581d402c0f10308081c0e01902c0c5200034030185402551a4001002444042c548040070316207408102d035103644503400136404283d9490740365003e035402c5500c240c2e2000084011f01407085e8185c0200d02c02110f00c5038907a10504441c40c42d203444054032400ca042d015003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 597870476 1250 597869226 597869267
    0x1e17041106041706070305010e0c0708090303251103010c0e09070309021003020405090f0402030c130b030601060e100206360303010314070b07080f0c010905100507031a03120901 78
    0x40519032121000c5c1c0e00140001d00700000850017044d110b007158014036802e54000e2030202c103511a00419048031010030b5050004010280c407283c0119045151b81c00c6803039980700b00421501d0045030552598080c41d01a03410104601c911580107035243d18095020784d0b12807001ea403001c0c1c2c02c0b4014401d09000a5014400f4540d824500d0303403603405003080d6502034604903005d40307541c0c07200180c12000311002580341e8480f44105140741445504c640d0b081c9003c000204400e40000b0000e030078032400760030007000148400003804007450448610010407450b8000340040f4104075507003101002d501c010b5070b004d14201146403100d03070b0210805505008514804d40761a1358403813500c00c07511689841d64041c076100308000459400c0e50030003202c4110341e00c00c0e00103140002c6e034410284a600f01c070818944555031000c880d030201c1c0040c00400d0034080c20001c00201440d2040b0b01508a03a0b281c410040540c4860400702d6003500d00089078411080045010b5840740c068a0040301d50400100700754401e8038 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 597871726 1250 597870476 597870509
    0x52b05010806150102011a0f010909050903030610030c09060e06120108031917010e060f040e010b09090c01053403030c140f121b0a1e1704110604 64
    0x180108502d401081d81c40010b00c19001c0340d4004900703881081103000640303a0042400b410b945000c0c55000882034042c1803506101d50340d000c8040440340d003180e410100d40c000008000a602e80041c0500e8619041e080400048826003c01003080d0b00c0c90146400780300910540c104540c0d5214140d426a8481942c022401c1da15819555203941006040c0c07240c04c00b803905d43e01f00c41802810301c0c00141c105200741c5250f581c0fa10116151801010300700c150000c4520707440f035045880b40e0250b40b002c08050030002c10843c0052052000d8224028a68505a000148100e101d680d0040480304000c10502861600001e00d40541c502e5041092544030f00791030207903a240030141c25070045818026981c54265a40742080c904141c2403048002c1280078020402a468007a280304402c0e640103a100d03507030b44084540d050a010384650128220102103110b000c0020702c440785c550307031402c810315481c41c1110b65540d08800c440c03124080070304010019100b00364502d0450b120041a140108103d608504052 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 597872976 1250 597871726 597871739
    0x603121b06010f08030f0901031e0b011404050307030f020303090406030b01090f110403140703021c061107030813141e0c0907051623030a0801080c01052b0501 70
    0x4969000d5140309000700400090500108041841114442c1c0081c40c074190104811640a900462001e03041c150740b00215600b20741c2c2415130502240d0982d8002807074440e8a000035000300c80c000004000e0740f0381003001740039a44010035903600b00c0f5030100c801000441244002402c50044401035074005107050000801d101c0324911aa04072080400c04204c542d10040a1070103a8007640701c02c84441d14208400c0000803000c00d00103e040483e002178412440c0ca0f580058805041400212410b0800596a00911a051048018980480340792901d440d46030340d4050b0200030010100d010003e884500034041c8203149901940e22780005d400e690f0541d9030f00a8941d40c0703142c10550342c000b5209100d180d05450901813201c9000c1e03400354491908246480d04440c0304540c8004d0201c0718008030091600320a550900c1f250400b0050f14007035a110454850000c00c0240168000b40741644942060b0701385903007240490ba020400d1107031002007035155140301000d18005003002c541c2c040c0b8040002985 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 597874226 1250 597872976 597873007
    0xd0908030405070e0901052203050d0510090c08090a081b060702010c1e080a05091504080703030b1c020f061207031a1002070e06010c120c05061e040605060312 70
    0x988911014903040f58841c0c170900340c00c0b144101c45c001e440e5551107007081c000c803c00c0d24842040324804d103080ca151070041a881010b4030b0040d900d0381d8010342601001d0090103840d024001100030f1a1400c80c0903881c1c103403a000e03a1500201d4014120074400a4503c0305a40c107000246480e1200c0700482d4068104064001e00034190b003080940003510f242e425800b02442c80b0440700f40c41c5115500c07804952a0a40300400502014119074110710030baa02440d020544502c00340c0c0309500545219032100560300340a015140c0e20b2403100e1044850110084600b0381030018907010b5501542c8400402c0c1000020036402d104c1c150a4509200031034080000c440d9254202d60350340c03441107400104c1e440c90581403000300c1e19139032040d101680161030709100d00000300b4103441d8000c3c0149001100c0e5010307920b0f03d6020301c803480d061100140481c0a01c0c000c2c00010400c0581003290055800c903401501113031480c01c5240034000074a41501c49010528030b5508005614100041b040d00980d5500c004480000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 597875476 1250 597874226 597874229
    0xb0d090b07021513151d010905030705070f15031806060b09100504050315040204150f09050c07030903032609010e011107110d030c170306040b240d090803040507 71
    0x31600d60800c0000c42680500034035490240d8450030103482a2002000c03071018041b01d015210300c81e10800c484465042c800d00074121034a0162001c1d40d84c607040c906026043c4081030b00410001131500104000100c60b080310340002c841c1e00e180001e58850000c000f44503800703c5607005450385080000207c0e510481e00b0080ca01c3c11011140d280b0701504110b4265024001d0b446220341c55005401c040d0a02404002043c0d40070744010800100041c0802241701d1030000d64000b40e20102a540003072056a090340710f0707503030045841e00142e410840140c2c1c2c01400c0c0480d50000508000780919155040402844130400014048400d80d081e4504056424003d141010b08089158203000764065150f29003411503010980241240c2810700f0224103006c1d0302c0c50446402c40030803030001c510381c000c503218400d04100c0713801b105070307a40c0e50781001c3c000c100956441007400361040900d010156640d410480b1184021140d0362215500e0301c4610079400010000410302074503170b00c400020071040100102c0c4210 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 597876726 1250 597875476 597875503
    0x30605030c04051005130207020d060b0909010510090e0c030601030311160302090a2c0106050909190308062202040609060504030506040807020f031b090703090803010b0d090b0702 79
    0x7054400c4540c1048243d8400b500c1010ba100344040060069041c1022400d02561409101514000c0640c0c04a40a0822304000382c5500d90b445810380b03540d1804200c955040700544000788024105240c17800d202081c40e11803a40740c55600c1c98184100c41003031100505000009090b40d415695a04016200380f48498042c1901c0c01090741c04142e109507881c1c2c09090b0303074001c1c00500786070382c800800358002c01906c200c1c5044021600030409607070888402501080c6075107000410060319107410b0041c0034601074000341c42600f041c05000a01c0d003070071046030216034040c501000e140c0c8410011500c0304c41080400c8441d0b0264190500502c04550024000c0b0341e5075545881842e959400120b48600507804000e00da90454008280443c3c40800942001400201695151255540042c0c680781007009407a65801c100346082c4500c2c5030400540e503104410703007014060174501c0da07a55401840140510301c8080b40102e0040c0344ca4145030b000105a90340800c010407103007030030000a543d95070460b0307201 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 597877976 1250 597876726 597876733
    0x8060f06120138062106010302090f040c03110c071a0c0a061e05190c020102031302190b0703180f0b090f13020f0405090f0618091c03060503 62
    0x61407401c0144102c00e4101014000d45050041101c0c42d00002c01d0111508803602d402140c24061940d01c4100070242500c86080f0220b6962284403201e85504009145505241c418008000c141c0c44a8808884000f004c650000d8810344054007a0000c0c1041d526112800c4400b24649040c5000003500b04240c80c000405402c0004d04103180c850f0b688140100e460302900160946800078100d9000b03014031925088405005181102c3e01808440048900c40d080e644844441c41000380c480c0b044803410601880290300d10300e400c1e00300750350724880341c100240580d0489210b01950002d203c25030003d08240396441e80d5803017803820004d080d4101801a00300c400c584d098005401e500c0d5481403c2100c0300401080e003403024890802000103c0124610b0700001010500d0099282620090821740880b401103a212401c08050011411000308410403070131000062140c0c959480681c116031001203040c81001d51742c0c50285604008030540c80501c00030002e400d001c2c030142c154000d4829620203a048 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 597879226 1250 597877976 597877999
    0x513030b270c03030708131503060611161802070803070203120f040c061215030503041d090a08361201050f1f030b0411180708010e060a08060f06 64
    0x9294940035010042d6a0540c03003041018005103081c4094030314491071030200d008066030b413010301482203651101c00d030000b99240424044541c01694008c40c450150780200350301c0e070085c2419840c452980c010071030194908a09000b4402d29501299510356002c1080c0b03803070b424240c0004c0c0d900c0e042096100045070403080000d0b084580c6071142403050b80c00420490303071503103000801e58108416141e600c800304c0d114402d680c07000c464042000000c40c030600041d5a43c9140c000c6440b103081254100300003c02a580a0041c8c0507400100390310400e402400055550040444800300400c035401040401c0d60300e0144140b100040840c1d9586030b5400340c0c1c030043c0e502c540c0c42d501e900301c030000c0f1690a91000603001107841300762415080b403c01184040001c1e1040d03125201c466501b5011542220b010084407070000003820500002000400903c10043c2b2505200002070301a45050107400030100b14100040c3c05643c51054540062600707400303449035070a080030304204070700701102d40c94022003a4580 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 597880476 1250 597879226 597879301
    0x30106050117070507020a0b130819080712090509010e0123030307030f11033601080a11090409201f110a140a030219080a0513030b 58
    0x61408030606290b118007507503030302c44082c0c03042e401000c0166008061300d0408102081e8880c014441c000e102c3d480c0c20b4801d841c0500e5240b52041c1d0313040e03044091351000c9418000420600580d40300f0707944a040c080d4966402c5404031030105156000562003100d440c00020031000f0184418182c805030f929203000041076410005a00d200c01d519550154130410803200030a2107265400050007083c43c10284110350308141303070b107940c0200391080c5907005403810b60703d440441625102c1900c0c110750030f00040c0c0c402010000e0007000c4010b007103204030760f121042060221020313411070321540c200501c1089003004500304280c0400958580b2301c5010380c8490003000707900e0301b00580313600e009a90311a10701100800710211042040d04101481c0c5114a0b4100400181d4481c1050031000c80340c40181040d002504000b86000340601400e40a40c2250108801180b0740381e04a0350984400e041c855030b14003441c280703a400b181c000e07480503148400680c1400300341c590088503030615400e40245020a184440c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 597881726 1250 597880476 597880487
    0x31e03020f12040611030c0d140403050307050a0e030d0c051006080c0f0301090f110a0902040308090105160501140a060b090303030109050405210d06080102032e050d0f020301060501 80
    0x9001c862840050019510084025410542c030620403c0049600e02d408900b050003904207031120510302c4004a003c140c0340e002032080e922183d400d176003401c005041c183c9000c0e09520015203000c040000009614400314040c450041f0301d805c000d4100c841c0c1c1480410010921a0701050448031030040c0f1700c00c04905001801010181c1e40e41e20054400a42454100011010180800c03a015501c0c1d940d408045070f45a81e00c2140349004a0501048854400812000d04015041141aa88184800e001144ca50b405484010300282481c582c2e031107202c4001103c210304000010b01960911086034610720fa00c0c2075040c01105000405c0c8019504c4411001c05401400b41c440c0e010742c0148010003410403150041508038ac011000e079160101c014007041581e211000400c2e1410800089110500407103100d075800a00c0698000c50460401d001d00c2000c0d8608c0554810205a02001c07244c0d825240c1032204005010017000c9040c2c6000d2031620340d802c501000e400740d02c0780d441c041e03000501c1e50142 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 597882976 1250 597881726 597881737
    0xa0804090f0c0503090c040b180411010e010c0c050d081605010f0509010e030f03061512010e181c03110a1815020303070c0c03080f13080c0a17011107031e0302 70
    0x4401918906c2d4940301800b00900140d03005992105108810918003441c040210340180d004034009003c0b400014005001070400c0c480550400461452080105030010494015104100c0e0942d140b07030b0142c20103503038502511240c804024020001030040200543c0300300c00070b0780300c0790042c44182d480003c500d0881e000308030281540c0d0010048008880100c000440d407107200105118110402c80310210b449070440713a9a5002940b1740b10060107041c80c1050929400000489000e00051040041545070b2241c40001c090a0101501480741c1d41d0003600200380794014002004e481d0f01e5070b10b000a10100e8881070b0600c1814440401050382c8552800000300001e80e900207602d1074544e40012140300884a1080d214580701c04000710014401a00602408035208010368a9000348101020b4030301d180d50000b43c030365000c00c40c9207041d41c4400b0707213200844042020000c001000440b2240c090003d14200c04c0200c0c81c000703030000802d90040c1e41d0065882901c9039814411101b140190200c0c4240d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 597884226 1250 597882976 597882991
    0x130e0c01080c1912020f160b06041503110414150a1203091a09040218041d0712060b1503040b070906140d020c102f0a0c02030a0804090f0c0503 63
    0x43c80e2400c2c506008640c0c020095400020040c50401388000344220780d0001e4207403c4260300500e0320390301408240500c2d2604031504690401081e0340d803154480c41c8100c64400100300c0318940100d200c0e180d88550210f00406150300000b0100e00d084220315002c544480c440501c20b00c6000c802041c0034010540364070b612541501e4030b1200b5404e00221703801d0410340340d007003a2021100b044048040d031207900203480c1e820070f5503082294100c038520070003007520383c1044102540d40c01d000c07085c45818400160002260707100301803030304154158101280684000c460341500a0000503d46912034041d070001c6104d00d000d00c1c83c04041d5100c250041303403c2c00c114440d260000d11815000000d00e01c1c1074000744a0400c107654010319064003104141e04001d9012442c03a0095a1182540441c030341d022100e021306003a00301c54480001500e41d051085011f400448020019641000340854a04100c0780c0e0000e504241600e40343c2d50754081d03c20141c240704808074919800d1044403030016000300e090347d020712103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 597885476 1250 597884226 597884257
    0x40f152108070b0405122701030b0a1809080c030c1212070516050105070c11010f140c01090c03080a03140105010804060c02070b0a0306090b031218130e0c01080c 71
    0x4103503d4032051203201520580d00c03400382c90140da04a04110707000b41290040d42d1120201c40340705d00f80140c526155400802c1c14141811b8440d035413982e032240302a06940e07900f401010800b20407240710009090118004150580c008ac0343e07002c100000002e80540f40c40d110460780c00b55100b0f4103d80c40b6010384141d1a402e042e1010104024038016070240400c130040d04240403400c0e0503a02c600f803d684003910f1940106454a14030018072076001400400b2100a0805141c1e004407100000c000d80c8410403203c105150101d40303045030040a41140c1e06a9401c01e461900e150340301e040c103c10ba40d202c0440c0c00c0210340340890803500196015141c07030403200d05841d00311199580d51143c00140002350490703030031400b4580307000c9085981d6802400405000d6500021a281400f141a007200c01102220307100354030003d038802108400404035040c0785032039584150042c49080205514510000c0440aa5410800a06030fa14800505100d85000903038500f49607840b840d0762244980308011030040e1344031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 597886726 1250 597885476 597885487
    0x150f030a0903050f0a030b2d01051c06060f031503020603060d060b04150501020609010e070302060c0a0506010611060f09031902070302090a05042001050d0506040f152108 75
    0x40c258001001c05000c2d00706a07107404100340503050369500000390040800c0e510010101d0a060440d59031020100041a0300c2200354224013044001c01898100350410100041c200044c40b078011807415010004802445016190380c406000301c0c00c215680000030703203401301c4910203441c00c407a000116a00074298130b2840d25904180100a5080001034400ca500d586046100d91030f14800c8040c958030700442d400c1a20308100c002428508040c0031340601b0707810081c001112400200b240d0080301c0e41100e0303090b0740740b05010b0700900740030b44480050705a0040a00010310f4540101398108040001d8095038120398904030b201884c0c040603600c65a055000340641a00c00310f000094013052030690049441c520360740e600003034004e0401c0f00c403081040d8886050100b004100b0005010100011025145902e003080c002009405a034813050b100c691070303102082d03581c1c0361039100003442020004241320f03c007a03a8405c4220003c0314459189008140754004661025404401c484541c1c403550703191410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 597887976 1250 597886726 597886741
    0x10608070f020d0c02040522061b030905061f080f1605100f120902130b0315040b040305070309180b0a0602030a0507020f0a080604120e1f110c030307030e150f03 71
    0x102401800858009401c0f0723010000c515000302c6007078007180710300c0010807900102c502403c40c014003103030480d00789401d01d25010300182c004240250302050071079501c040401980001085884e042d8440103140c050028030f00f58080d404104c0e40e00c0442d042102548c500e07a82c0040c0241c04000351074a800107000c44d008014450f1107142d80d1043c6003601840451003841275000a20114100c9000040003580c889650017241001e11402900c8582c0452150407464282c68114a0f100001c00083c10010005158001c043c0611401c0c000352881400c440c3c03c02c0d41c250840d00041140d042d44500c501040328001405906c0041100e400701d60319a616030600d041c5d80d00b8000030a051401a5502010a40e000700d240e031030801009200f40d000b41c0c820614901015009404018090b00c41e90069648008a82910909111a80480e50540ba11071086c01100c054542495083c41906134907001c0051900c1c24540d00c0040b00144000458035400034981d0030780f124020384920700031503450303080510008108 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 597889226 1250 597887976 597887981
    0x30705090f0604090320060f0c03040203030712020a141f0605011215050d21021506130e120a030e06010303020d05030c0d02040e010e0901151401110105010608070f020d0c0204 77
    0x758402d040244042c1d02d1141b09421018400030031100c181d0280d0f0030440195281d811003508103503880c0072503149d4181a00465124400e519000c6c2c096552081e003040c40c688200841c004d16078001900382d40c440c00c402c9440751110b0703d481d030554400d0000001c6142c0e032809807140a003241d90503114081100704000c070b0340003e06440030000e115000c1d5108002210380b509203091070204d03c00c02c00605101102a8a40070000c440f002100441d80702014003285070264091054000c5011602d50400000c100d5401010b010030384929213a5000c4d03c2d05c44405c0f80d002402400d048030040d02c00740b1210103a01d0425550742800d10002d00160321803105081800d000c0d900968200c0d00026515140610210360f640c1a80c0c41940542a501981001041152890381704540c014007210024001c42c0080c40300021880c11038010060701c890005100301090b03025804070180710856600030f04c9a50b94907030010340f0140b02242d810300829022116a000c6c07070300c08101540700c03d1464a0300700e04003050340c090000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 597890476 1250 597889226 597889241
    0x5090705100e130f062903150303091002010e010c080906010302211902091302011d040627050c0f1804020412050a2904080c0a02090405010506030705090f0604 70
    0x40103103c0e0801c240201c0c2442c01262030b8100c03101c50108500d440c1c5554440014090480503094106412110a50f941c4010850b908001e80d04eaa041c9101d40c01c5000034207502c62400c28640c08503210140b5207001ea010f4018408840305c07007000b0440d202038004190f0b40c0010444054100c0d4002c1d10043c0700503e0407450003503032070030208041c2804481c1c50200364949003080e190306204100d107004c1070003145445824a076001003014001c1705112504e40c00602054940c28440310300c17015034030300342c03e4a803a180e000307900800c084240300e100e05508201d51142c502002012101c0395040c0000150321401d420203c41c00c00040c01601c500d082001070030412844c3c2d4140c003203503000380c003040009520400080c88118050149001c0c00320a41d5528001d40c186600400384954801440c4c1003c0d030300715a454000e03030710075002821a5615044a4003941c1001da2130034009503c040418184418048154001ca108402c15800c0352050398443c810005140d030100c0e0524100348210f80020000d003042c2c1c0200a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 597891726 1250 597890476 597890479
    0x15020702030609071806150e01020f10020c06070806060d05060a0e24030c010f0503040204150821131202011701141309121404080d030c0305090705100e 67
    0x50900165a000078180350003a80c44000c3d83d81300d40c0c0c0c03c2c4503000e410069501411501c007410400c103403070450459280c0701085c8216040c40b058845000b0140d00030300406403054840020f07505a8604806060001c0d0481c4080c3c0c1213610034070001800326030141065901072040142001d0030035039403989240151800511480d08240ca500000409800425401d07004401c02c00b07040c9007103560490300c0300034510f140241c3c5111b6407110500c2103d603600841450940001460155a0307655580081005410410789520003281c810324005110000880d0a414031a0705070b00700b22a03500c00102e100cbc0180250020800150350703480d0100a400150560100414418144013220060181421202420980c0841c3c1c6169803164400080e2400040e80b101c0c0f80c182c10347c104081e01990304d8501103c0e40c00d04d40340b0300b400030304031561107009040400d40e001001c1d06000c0b125462160803004002c1c000c80036015000c42d04220100d43d46c0340d004940c4034141c4101034580c41d185004030208a68458504e1442ca = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 597892976 1250 597891726 597891731
    0x4111605030f040b031e040305040504020a1b06230f06090a0b04051602010e0327150a030204091a150a1b1101020c01050307020d05030c040503030706050402011b02010c15 75
    0x103a07000c00b800c0584014412465016102d2500b41c0144610488180340c00c1e0410144804010029421405547c2501c5084e90b005858807a0040c2c00d07545181c0301d201c0c2150040614411004008082c3c00c10400c0003240e00040b89030b14841040e0180c505001d5400c40c1d0700c404d6a20005949082c001001580040140d0000c40c401440c040800c0c12a181a9002941504086010390801740c09001d400c0b005242c0c00c0041d8504140701900ca803061200c00c80c020140b15074202c40654550ba0410000400d20110764150ba48010102c00a0001d612600c1801480d078100540209401d0410ba04c40304001c1d005408a10f415000c0c541d4a001030303102480780401c0c05900145288012035140c461095544141c4800b0461700c0d004001a1420b41a0305e0303c20b040210400070050340341c9d03022608500344242c0381440da031240c54802040743c1c20b001d5900300704c1e010310002c10038200380001508010f014038004c1c1c84280d140d0012641c08940c60b505070b20060f001ca0304201084c000075480720f602d0070b2403150b8103200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 597894226 1250 597892976 597892987
    0xf0d030225030e04060f12080a0e0a090218102003040f0807030b0606030c07141009060c030c180315020409061211011b030f11031909050411160503 65
    0x1d01080032a031001540001c1514010310324505143c45088050a480c640a60300713103260407040c80c030140201c04d0040440d0404030b030341002d081c0903440741c4000340300041888441946600360b8100940003070344074400c411002403010140303040003082035a00d0400ea03034034040284107a4442c41d03051000561b004449100820001502070000c0c15800081c060500191004506e1410104030000300a004244a464100140080074290170103d81a0a920a181300402034404a89030704104e00000506552401c0c405800c041041c694081e13440340e0010f4030304010018500c54200c8440c0c6401207000e0b04208640400c2c80411781c40c040d0900f2001524001520f003944941c1414191042c0d640400144c031a100325420403c5400f10300c19103810001c1c80e045081480943c8102e108034460000074040c03000b10708d50101078900c00c620f404640340c566000c90340c1d02c4141d49040c0c1402d5075040c1985000601600c0081003502c5c05026103503205624154075800c20b111401006c03d944c1e9010300c12201803008002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 597895476 1250 597894226 597894277
    0x30507110f0109030e04020405012f030d06030b07020a0201020607200307050a05101103070f020c0a24140f21100e1e0a0203070203090a0e09010c020f0d0302 69
    0x1614481c21003420000c00c0d48074540c030340a844402c0300004c0e288941c0c010701082c045640d01000341240040e208031165001d01c104091121060f00b031414400701c60200280c00c000700c64040d04244222882805c0c41d070110703030f40c0b07010490711000380080090040e004070300031030115403040d1a1482c0c4c0d603400080f030308148421040401e203598000b0400301c6080c0c0000044105214050041d09800070707400c0b1003030064041c100c00040680c0302c001c040c0c0050042220405042d075200f040003020f118806042c22000c1ca88031210700c6041c030941d20348000621480d00e415603134207200b0034444004d24410540f280c1400300e900d40c1610741da0069a60340c4108000310056100c0d0100400003180600300b000005041e046c2081100703000c41000528100e2188100310b0b252f803440c54071208441d440b40b0358241c0107031242c0324141d049056114181c5040e038010140700001c126030428803c00e50190303103200005c03c10030106940c01c0c1d8955030110b04602244d040a2142d4600342d0203074001b0100c0011075170004040281100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 597896726 1250 597895476 597895483
    0x109080a060501060816020c060310050402180406053a0f03030506010306231e03030a110d11120d020d05010b19080114040917070807050c0d080a03050711 68
    0x303040d80e41540b030b0001004415042000b4681080004154288002154001a540700d103038080352806950008005000e800c0b1020b00342018140c0204103540d0f6505006011480d0486c1c080f100348228a061000a03980c9010200100d0000040c809182d510640c42c9000d020200d00d0795014004400e8a0000800240240108545140300b6100081d00d81002000101101c0c07541d0800c1b03810709260045945120310718560740c8440c20084548001081061200d004542100c030b8940c2d400d80b01c042a50101d15400100311840405180c00f00c1c2e0400090b4107084403a4251b14000c04040c0d002420b04a8100d4560320003024000074a01000d440c01ca603004081080364426800700342061000b05100d42c00b90b140c0e0407175003c00c7d282c911340303207100b9410b04441c5a8401d40d20705146200e1030340e0340c1403d02005007244454040020280d007a6494054a0602c12060340c001d0304200c5240c0507890360300d5032900e8220419441182c100700800c0c18904600c0041d0b000b00005050603041c4504403450703048091041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 597897976 1250 597896726 597896743
    0x313031e080a0c050127080a140a030c030b0910030308180601300b01270908040303090b040602070e07020f0604080c1b0f061c0501030b040b13021e010908 68
    0x40d0b071104031010190820601b1030303035102410749801c0c0070000c0e01802c2da420483c440c414690080070041c0e60f0070410b0b605030350b16000c5240c0e82e011500b000c02c00000458140e4060364508419850078050075a0b50f404215610008540c180c500c00d00c01c00c818030100b0320400708994410440c0004c0340a5070440b020341d51070b00100f43c0c0f11102080840c84081d842441d8202c2200c450104400c0c075a00d0b0712b0a40e500c2c5405864140208002a40c100c03220445000154010010040d0391030703400c10640c0104d00f03200e43c00c0c0d40640015408609004000070700030705144101c50842d211503014055150409004000020025001004600c100300381004a654184827182c0501e1040803050355580d40485c0e0281050b01080b0540310034503c60100a441d62280c6507904000c040440d00c55a40d00d4521841c13100d4800340c0c00303c040105240c040040b040144034a04540a14020520300c00340e0781d6080300d03003243d0440c118402500a000b244016100190214018021203414109505030a441e01d04152030f00a01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 597899226 1250 597897976 597897997
    0x61207170f060a0923091015140102070308032406030a1b030207020901150201020c030a020703050c060c1e01021c0f0f05090a080f1201080c120313031e08 68
    0xa000900c60140740c440c0902008050f44d034000e12888031482ca040c4103822180411756400f01c0400002040c030364041c400d4414000e5404407c1049092134201803a40840500429000d0940703900908400e6000081a80440b41d1040c0e503549107565041c00e40f45100240d203140c0083c151100e00342152a40c0b040080c6100b000d525400040c184040aa401040a610210f080606204000a1000d6107401e14201e054445070300080301c1440d0320700000c90091051200d00d207040d00001c21300c5820f080d0b001c18840d00b01c0703014400f2512844481c00800007070784540311003291250b220b0301000f14104054242c4000350b1800ca4001801c0c02c10103899080380d0503122031040ea1681c1d456003402e000c40728612274035140b080d080c0c004201c5480d22100351a46e880c3d1101004d0507014000c82d00c0300da6030800c9000c0324110243e20883c2d50055a40c1c802042d035078084801e209204000c620340461010900105840c0c0080c400c85d1070b550400c3c6580c03100400d98542440040c40e410b00c51910b400451801001000ca009a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 597900476 1250 597899226 597899251
    0x11060405062205010908031b0f01021303030e181f05090901144615081b01050a1b02041d1c0518010c0203070e0a110906120717 56
    0x1c100b005016480329801c140e041c0001c51500b8001e00f8800801e80e04074030720132001d0b6040500c6200307015144c260701070a005001c2d030001403419000c48a000202d000c0340d01c2500c442003842c4c5080100801c50700c50840c022511122140000d2141808103152014904023461400034103441c2c101290040c44201d0303426502ea1344640d8007448400360a00c0715540a09043e0110100e510171b00b2085555200061505000c41c28881c0c48020f40d40050302c000b41c000c07000c0c62042140c0080701440c2c410140391845004a14007440381072055001c0120300000328004169606850900d001400b5101100410300f1000c482d0580b044560050301d6a10030941b0469911500c3c00c005101c452840303290038603804070496620f1035101200c07030070780d0400b003510240207044648034902180d40d00103c41c20300100901a6251042c40b80024801408c0f400c00b901a070034000302400200103801c0e01d6070b0607105840050b5000356003088490011144801c41d0f40d00540e807498603200c00d4007a401c84030300d040c00540c0c40340c91564 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 597901726 1250 597900476 597900517
    0x20a0b0c07141c0c050a0303050c0409020406080a0b010503061f02030408030c0109050c0303120105040f0b1329010509131503082d03060d051c02010e25031106040506 73
    0x1810318031041851060780c0b500d044e900c035150b5221900e8040c07200c0000c060540746d0012230020f688803003d44000c0c1020000464503582d039410028410320003964481810780c5841088001c0754480d0040f02e2003804081c029241c148291450303900702d1030f03448065a0440c0020321002c200404180010140130340134030000306c0c50128501300f280c1044030400059200e684104003da00403120074107550304550084400003003013050740e402d07400500f41a00c00c1d182e04c000201503c0100c1410380e8041100c4000190040340c105d51000030141c0c0c3d0600c41810b40c1e0104002788590101440c00c081200c3c8a074841d4003011034030440441c040e00a61030183c0080703d040e140425a02c1c02130280c101f030300c401d805000d60360307860440034180306036698030000c0c0049004058955412081c80f008000001402c4079541e5030a80304401d41c5d42c024024510014005500e0040d0040700840c8209a0411206035a84598032418a0718580d01c03245a0002c1d400c04903084070381444000b802d41d903010050845550b03a51000340000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 597902976 1250 597901726 597901753
    0x170c030c1c03050106090e1b07030c0b0c09010e060310030f080a080f06060405010c030908071706060405150d050106031a01090b013002042102031b01020a0b0c0714 72
    0x6041441400c1c081601d080c00401a01e54040d024a0441d0b603a03118442c2c0c55101c100c640c000308203a080c40320340705030000182d0740c041583c07200682e080f09008035014281608da60400d5546441150203060003c1c50f00341001c2680d02d000d00007141c1000302003201040c050750304c1e40c40c108800c035840403e4440c035501140c0c070441c042d0051000fa502583e9010000a14076180d4005081402140a00ca04020f000c005034420180200d0040c0d0150040c0300441d20301941d950307250b52000410007040c54241c040c22020812604090060f54001e0400d04a0001c40381004010701040b018819425100f41d906c422001004c00d04010044102c1c40315222508030560400c51180300307075903902c120f090402206521014200b1043c0708a25040327007481031540390741c0b808000c04101a000380e40060707003003904460326100030010751b140c22120907200ba0b00342c490b034808203040c0164201006852710b0240c0c00100e49c88000840400030303294060841c00f011803c1942ca6100d01141340c011010110013644110303142d0095 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 597904226 1250 597902976 597903013
    0x31b090409082503090b0918180c010c050601060e060d020309060403110d02070e090f03030c040806060d0c0513090f0b100f0506040308092e0810030f170c030c 70
    0x751501142c041c1c141c3c40c5030b507006118103001c0c4101482d04d600400c00072101e0b5280c401007001021004d00700d440d1030400700300182540c64400303150580c80c861000704400c1c65019084004a0325045005480242c0c0b030583c05a03030400c0d1603080550300000070000b803440d2a00071b10145004602316001801107140c203240c040c000c00f4400710b0007a882d80c442c0f583c0764450f59000030035105603102445408019154202e034585040070018a0a103e40000b00400c10501147e5004e0700c04c031483c0303000726050345c1c0b0b614050040c030300c04600d0040c00901844a05100c00d08001c0070390303c8200380c40c40340060403849035140c00000100c0403c08850b6110307440280b19aa0b40b40100040250120501080c621860b1030b000410340d120318031008142c070501244115490791741103010582c010705110a03105003681d00d120303500b112298030044404618402e0200d502c40710744544040583c0c1d0f0240200100b1441919100d210040e8404ca05452103030420044403000004d1010f4000903c164008000020261152066 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 597905476 1250 597904226 597904267
    0x3060204060e0f0913020a1716210303090218040303020d050703270203010e0a05030309010c1d09090c0a1806080a0209071d150901030c1103031b09040908 68
    0x203d505820449a9181d40da0052950001030b20621018580c0d864408107602c180741d82c0c0031000c5080984c20b0b0218110000c11520545810740011842c242d4460302c203c80c08452029850030013507540c04074400000c1c041d60184c0000c03030000f4041c01100000070130078141d000e400c03141203000030340104e4406203e601034058290011554107052082c00009902d6030301604640300d10041501800e0402000d5403029485841105080d00c1600c07070311002030409075a654010f0325900f17881d600c4c000300400d0140c822003c420200240b035902c8108442c0140400013400c0004e0040d0070a8003a85c4400341e0b0b16651541000001c00d01c9042e44062600245a980c0c1220050303404090250406020305c40142d0707480d801c9517804401801c3c08104a1a00070104140369400603101c0c0e00305000c0c00c4420540a22030003e410586000d0b6030038018003c0349441203c603524003907481155a4414000300d40b03100702901c2d01020600054003160f041c03288803030008042e01c015200540e682d81c00010520044a4290a0800c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 597906726 1250 597905476 597905479
    0x90f0d12140402010e04021803030a05090118030c05060a0315061206050d02060f0a0c0b040606030c050102030a020a080a0302250c0b030c120604020702040e010615020a0519020d0c03060204060e 85
    0x60a103003e4001800e00500c05078168440ca600081d441040c0f25045800206c4110150450f6160602d07444054107070b51100350040d0202d8000034108011084551105040e0303030740002c000101e9464a814085d094000b43d03040c40900d0b4450100305c140308500e098075001004a0780c2e8000100703001307945407030450315170360800340c0654a0402e0881c09611140100c0300d50b889111716081c1c1e81c06043c1c03001c03200039030400c40041c408900b020a00051001540240007602c2c0140703448130380e480d66407005a0b0f5038407030040700ca0050707045039141602280c20303840682854001800c1c098a024011144a01d11504410081500d003d0485950b000d1140c00350807071000e0904202010302c1d50900b022261101e010744025601c084070850f002a481d44c0720303501900c0c1020f03130181c01880600c020f081c601e4041c1100d80070f0f1080e2882607412245041f4800034403442c03070641140c0a484596101480b40e40003090200d416a0064203040140002a000c0540707100254060303c8010385841c01e11300000c0c04400b80b4840503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 597907976 1250 597906726 597906761
    0xa0e0409050607030507051315050408151b04140f040b0607080706060522020306010c060905150a1b0c02030a1a101e061d0303030114120706090e090f0d12 68
    0x20440d03a0a1090342c10340c9c03001c00070070231010303007480b8101c507103118680141540e40110a10304403178070401441c450040c024052104040fa00d0354060350003034040c038407810070807408e010b1003100c580c2003d5011040409000c0c02c0403444142d60320114000303070710440d0704640310800041c00710280045c502c20b0034007410041b115181d0784400c150a01040c0d03914004183c1c41d495001000c04c085a000c0e548442e81c140d84200e051200b001c26082c060344440c6000c094241c10510440007401400941c881c4403042c0103030070303100c05286001e0030084501c000301c154202d0b010300c500960b04000c200c001c800c00c0070400c2c01d0416100701303280004a040c034407500355009a90000b410400313142c03410031080d01e9800b541c100d894050b0946240b0f140002c0150403170090300d034040c000040042803a8800300341300201c2200230b80790006000c0f44011460b5413000c0714400c0d00000780500200380103118112070000c0d0800f20300011a040c10101081c0d41d13090505492010000c144040c29807a1a440701d801111084010000013 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 597909226 1250 597907976 597907987
    0x41116021206151009081204050102010506040b0108010b09010302222402030d38010f0810050906060c2b05030403120b030a0c0e0a06051e060a0e040905060703050705 73
    0x900c11640c1c01c00f84207210fa1402c64012560301e2080360700300c0060a40e10102d41a05480c900f40580702d80c40350054a0055003000001440d9080a0180910402d03040c0e440381c40c0c42c0c0c07800e00c130100d0075004045400e040503001c00840780c0452400f00400022241a40c110034224134154200700c14907103407994207115580c440d034043c1c043d94002c0141c030705e100b002100c08030795103580f007100d040c03405c1540c5d203081c91415026000d0952012410602c800442083c1c8500301200b4803000b060764407820846503081000c00c01102032010f4144992030361340101000d020705d4180900c60010a05004040500744e040400011803c4d85501032101300b003078030710020304011b0300e10700f80b5031001800601e04c800728180254403061030543c2510200095010140c11100b082011901d4514068080c801078600e20a4241014004100c6240c002142034144c00040e608055466100c405d01006802c000000341c00d12401483c18009a1501e0060305032492141e0043c0c1803e107840400602203c00240c103060410000344032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 597910476 1250 597909226 597909241
    0x3041a13080a0c0309030525090b031b01090b070f02030d03022a03130b0903010c03020405030d14070c090902090c250f0501150f0605030f0f0402041116021206 70
    0x4a55103151035150040c040c1030181410b81d00d000c417961008001e4412180407246200c19002c0250350071001252000b0566550381d00c45e4181e9002c4400745605412a00d021460102140480110045e049c18044c10559546d8902c1c03001d40c000e00402e54a86a4161008007149414028100d60382420b040442c280b0088580541c180f5200107054150300044100c42c6103503140400548480300e0a03040c0c01e04105842e0120b104150f00301840f25400fa41c00c00040c22a118001d000307980a455018000380502c048002c4206c9021625051400a05804005081c0499081400f51000c0c041c041c0340070501008030301c140041108014551001c44205200740b080400300c4a01500e80001d0b4151540d4880f00e20741001101c100444070000c1240d803900f0b0500741c660000c4007040e011540f902444014960b40c40809486030701c01110007a011000b250000f070b80702061196810303046400030b0700010701030351008503481d40c550201d802404060000b146078000c5103004001e01c048000e5003000303410741d41050007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 597911726 1250 597910476 597910493
    0x110304051609060f05040218030f0708012a320307022104060507060b270702150609180a0c050a080c0f102709060603050601020601032603041a13 64
    0x2605d441160001010f000361340c2c0c08208041c503203000034262806078079150300803980c850b09841060703500d509081003001080d030b48240d1b540d043d200c4040110079000c01c1c00421a45124003071100d0680503400b140c5a18044048511290b004180c4c007100350384da007130110000e8600900c0080900d40000001c2120340001110030a58040f501ca50815580794099032a1100143c00c0211780c0e20b40100e84d0b41c00c0e42014202542240c548810700f288401d98079255071100303d8130b070800c80824440c0c0919040c003242c131310b09201c00302c030364002102c0b04294080c2800408003030801010070401e49911405640c20321070f07403070008006030003090001c0081c941c3c4180c0402040c080d050030003400d03201d184400900750760b29005481062580c8000c5248030071340010507006014180d10380c05601e80c920300d4800e010a03594001c3c802e990040505800a000a80c603558507140c1c0d090441c0f4030b8031040f00c1480384140f4152080c00c051401184921317000c800c18945c440c50002c06034401420654403c1910002c40049400b81 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 597912976 1250 597911726 597911729
    0xc0303080a02040b0309070303110f031e0d020d0c12020903100203060a0302090103030c050c090402090f1b0a05030415090c060302090301110408030304020a05240d110304051609060f 80
    0x14109103400d0350310000e48400a024582c00480501000804c004a6510103d9008240e030300ca40c4480c0d422442450720640d40d986e5662041c0314660003045000c0a4804845a00c6203002d0210b0070301d842e144100541405a800200c8207118181d02c603841c846400f6003080560a0540320344508500381a83c2c440065900c00706191140c7c14031b9400408074000b038843c2094400655005000031f1a99656441d00806415103204141c41e41d000d64505020f5a2070700751445409207400500c228403d4443c0c0351440520305000d461204004210800c040032244080058000c544207926800d07201d00d090304003070f14412598408442074602e410001c20000710a0200101a5031444c9070041e120040180030074010940c4e030098640144002c580054080b41c00001503104504c07d99940c0d04240d0380748184a5540c1100080e10403001d003004c2071003007030314420001c0c000d8034080c4c06001c40c0d250b00348240000554800e90b0191290b402600c0c0f180f014000300c141c42001082c0702e0004201d642e1a050008144140c40d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 597914226 1250 597912976 597912983
    0x7050705091b0913091b06080c1c0906180b132a050406090506040b0306061302070c0504140f09070b0304110d02041109122b1103340c03 60
    0x842d00c401a602e8070111200d40040d42c00c3c0030059800b6600b005040ea00c030046c0075440751814607002143c0b00307108410030f5010343c0c00001000e0a1007540e6244245640080b034082090590311840c0b0404031307905002c0c56100401d0114455106911400e1500c180030f170003012824560f048840c6080000c084014a0040c100321800c6504802601d40b00b03152011060f0740807507800707420001c010541903100d9000d0b50040f40c0445040100e000e0440074103442e80c40c02c440c41648002d50042404041003640c009001d050302c5029402c486540b518000740460341c4c2d034290510043c200401b009401006d100344140c01950740c000812510745401c14900b00b40c880240001c01032420100c54040b1071711908800c41503d035005009001800828000e01c0498001e0001d01c3c0c4540302003007204d48100130208054050402050b06000304903000030000c600d802072074101500300100e060b031006a0305414000350200c0d890040b940c0200070070305018041007141846813540000b00480700c11000030a0b0451400450741d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 597915476 1250 597914226 597914281
    0x319111e1c0e0a050d05030f150f0108070903050102190e0108040b070c0c1503091e02130b030c06040801050f01050f010f030c02011118030d0804020a1404020403060e01020705070509 80
    0x7039442e880d0b0a2001c500001085845200c0b402c00c1155040405140b0400c6482000095581c88400490107805030362441c42c1c104c061909144a6035101f6424164400054101100041d07980e075251822130380b101d554030300c008810203061000940d00070200080c8007000d103040c80031400e207611010250b0034060030742c00034414a621326030100905400b890004003d0340903c11a4444546400350103445007450840c0d040b0700d000d0082038800140c1900703203a00d60f0058078038060002911031400007001e01b640704070380c14030840d0342044003070b500c90000304050441c0d40c0c004038881c01d1a00d10780d4010803040e041030381314003034016096040703917440040b0200116481c5000b0602c20450302003a401040043c2c141100c0710030004860000155042180c0c10044e0190111000014510821929110203031802035112411000800c200c0d240320148003800140100300500d010b5903952048110361007038040d040d81d0b03500441c254092000501155008080907260510b00740381411601105c81c001d0010181c1800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 597916726 1250 597915476 597915491
    0x60f1005030723130c0e01030614010318050a0f03110118060b0d0b01140102060a020c1207030e0604030605010302100c080d0213030b0a06030b070905030c060319111e1c 74
    0x40103030704148814240038240760140d01c42d601041005c1c00b12000240d0114611100e1410070b0351291243d042103c540519040c4003820000045015000381082240241011002500468414400e090b0041d118032850245666913160103020860384084e05c160700d924121085030410101d901400340305900c00030000b84c4a060200040c228040c10394080c00251407540080382d6405c00d44031210303603c84244c08983d03142c1c2d1101484020f074401c06560940c1c80d00b005c0886000b8009200241aa05200b030511408036015103005c0f0b0025007041d402a501c15031224010020750a00007110441c4034420320700360091800c1c0ccd480b21420391148142d41d00105a0004c0d4141540c00c0000c0c4000c05107038440f802c44006c1c05c01c00343c00d80103408a40000e0701c2980a0101049a042c007501c002130031600050003400701c103d0034a00300941508000c141080700c0d4450701e40650310b405a480f400401c40102c2d0b04c12610340b001034804003203002c025849260800010400c52903054043d5003401244041e003070020035080d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 597917976 1250 597916726 597916769
    0x1e070302010c15052d06033c070501030c020a1725080a0e030613060504031106090f0f28030c050f07090c0f0c030311040b0705060f10050307 62
    0x80c51142100c0b0519180805001c02c0b41170300b1045501c2e10795107400388801500f44403918094500141d492aa055010007101d00c440748255110002030310030000301e446072111890780c8446915a44400d901260010403050004d980c25109001c1210014802481c51941b185e82da030790350114410010000c0d800114112414a04007100c0c5c41b500c9400c1050b0260407951460484402c1d08250300140c0800d503402e0403501581000151640300d030a41d40d502d10941e034003a449120083c00d01800c1035003044a00f1880e031181c02010401d540c005d04003c0002c01424499440060800700314600811854015255040e8200340c0c5641e44401d20702a001d10780011240d920701520741101040004041d40607812805c0c01c1d048010512000701c60b840d020501c030092001104940c01c0c3c1f41e014821010030390062b40c00020038031035884000410794941080c0d242c01e4545030041825040040e040380c181d0721000400c818154000b540035000b500c80103206403101c0c10710000070f441c1c000500400c081c00074204403440c401c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 597919226 1250 597917976 597917993
    0x61d0903090307030c051e010206070302071122050a02130303031109041119050703080a1d060a0f15080d11070902180f10120b01091509081e070302010c 67
    0x10740400030115510b007550707440e0503040e10100c0c4c4116840b80c030f0358040300307080c1440c12508a290320310140d010b40125503c0302002e500035041400c0560307131401071050340c0e401600c68100101d01038841e00441c21500a0381c8194805460000340500740c028018031058140190f001b40580c1030701d625080c00300c0d02800b04084400c0c01e018808103164850300308010844200700810003003c0ca1704076040c000320603c1c2002c0d010354032413065900040004860300d00284400200e80c2c060802d010090f01d1881003c18050713401480c00b441551141c0744a41e1381c41b0806d602008c50302c200c64102e0003407038081c0c0c0740510704000d443c2c4070f0907522002010f1002c1c01607001c4044030244481c8005d0242520115181d122044107849000000c6228074041c5100c0445510745180165034899140c01d00d40d00c1500c000c5800c603201015061032803a041c14008071503000f11b00000c400b818080700040b05c1d91030001c00c0d454520ba907842c22045840e4040040c0003a42c040140030400b0400c4001d882d02820300c50031003096850700318907 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 597920476 1250 597919226 597919237
    0x6011209150618050601080703020918010608071805030304120804090f0c03050c070224090607050a0302010c3207140d020705011d0d02040e0a030e13061d0903 70
    0x1d5500325190381034004650780c002070a903448480d0640600320344583c403600b00e4509664550100708244002903000b88a9001441c0c3c49401401e20310090502250020b0100c0303007a0010804a8014420424042e6220784050b000c202c803101c1d0103036814503103400701e138481c13107030b4090f0144218048022000380444801194000c000420307003000207040000006c4000c01c000110000040d04110204c0c060680c2c58040da130f01036800070b03c00200b40200911044001c041c1e00c0c610a0101c0b0309103da45280e9568a01030900c0900601c0503001d1840f00d40b40007401c54528000d00403d10040c2c4201d010400003510004091042140101900d14032040c040c151070301031564014003105039201c2202c0709000100380c10314405e60070380803510000d40fa800195080716200d9800d85003032a035580b11170b0305407411000110b01d160000d070000920840c00760a5a080c951184002d90100307291003801c524070304007091900b03284e0590740702c10400c160a0100141c1030b2180104151400300354800130480c454003c0c400c179207 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 597921726 1250 597920476 597920483
    0x6050d0b0a140907031505010501020c0d030e1503090d0801150305130c0b1b0d0f050904090803130314070b0f04022e03150e0c03040623090606100806011209 69
    0x42d441c0640c02070ba5286a0341c00100c4204000c00100310651600b80641816200160054108800c03500c0501144203c0040198104a504030710450f440d02c901000014128000100b076549140c4640400e107028000c0d02c0010810400c1401000800c00b22a46101000c00c3c0703241c0429107132500c1c0106c0360380c20048140500b80d00759440d00002e400045000621a404a030400410911132414202d92a0070b41c429a460100b10100c4050031514071400085c400807000801c00280555a40c580480035001240d134441e1034640b112990b0f050580048407100403820398003003d482c2004655a00c5d00f021405803609002110040118007199902c0c802c400c3d1429203a206044542404a404018410303070780b0182020920703000501c400000840f0320318080c6d420f45444102207440c0e18050318103075440108296102651500c101003140c0200c2da109802d4000c50f1078460007402e01200040c20031402400d040d07c42e0300f40503061707012950031612072a40070301d09003003031400c00c205048404050503103040001d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 597922976 1250 597921726 597921761
    0x30601020304060c1a150913080a11010f0510170c0d0f05010905060906100503070e27010c020607200606060a0c06090b1602030705060c1303060c0306090e0106050d0b0a 74
    0x14646c8026680c51024800072140c8036000c0c0c59811200c000c0a42101c0301034120003041081802d00c60181d0040a942d9032404000505041c0350074080b000c0360800e0b14425240d00b4007290800540c202001c0c0e200d9004084c2e0041c0c8214100840040c240c0c1c2140d0100420a1000414203400c2c040c0a50140032340541100680f03900b40b520690040e00c400c0c04541070942d40d4110a4085010700303000a00c94103540030840e0001342521243c010980d2004074200d20034000010800c0038401490a00802c0c40400e030702e03002847c071800c0001000d0924006007000400c0180c402804480d45480050442d812070815600c903036840340712200848411221500c003921160a150f0745008000b4075141c924410205000940c00c560010502242c0380e1107241400b030084c0e4080c402203610304000900a204560740300c48801c480e02d58035542e00301590108240c1101299a0307040801080c00c03240201c950485421000300002400c1a000840c2c86071030700c1020b003c000559001640e080101d901c40c0807491041c100b02c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 597924226 1250 597922976 597922981
    0xc0102030709030c140f2107030606420302130e0108060a0903090e0709180e01050a110f031509160e010206070903030c0512031303090b030601020304060c1a 69
    0x5812840d8912007140c41c0180b8010000c0d0036501750003501c2610500400c00c2000082080400484103441910100c1c030403000c2000800140303042204000841c03144902003007151410580c07040301c0e21364445501c4bc115906003080651000034207100c13107002e80d05014620044210004400a0041600b415183c465944010500b203408140780e604803100603046600b10b80d1403041c0402a0703020250001d0200b200c9410030f01ca01c682e8040c4840c0c0c44405441c2c603d440e16610100c51009894000750b9442455888860344410b0300203000f0507030b1003c0003842c24071040408035420403d91241d1465400d11040120119030420003142d079000101c0b000902c440018103080c00080122443c0224050200709040c010039100e50010603614410075540c0c4550046a10310b840c140c81c230210140c81141c0c1030081c085d035a4000e071071b406c001d140112884107000c03120820342c1c40c001c1c2c4061150740102156800500401006030303400412241550f51a1030060300e6100e0740d151000f540844801c041040d41c19a104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 597925476 1250 597924226 597924241
    0x60e15011712040e01170a1709011107060f050a030f020a02010b03061308070618210f0201020f0301120201110a080a080c030f06040b1212090406150f0c03050c010203 73
    0x82041c0d18802400c151039018400d0a541d503010b101c0d601c01c00d8851452500104803403410303161249034074154001139070030719946983e0b0050020f10b100001c0b035080d02e000c01c404107203582c00400d01500020200c020a070543c03d007079010380444202c6051b80300b000780000d403140c50306210703400801c92070307084082c15519903c50b01c0001c1d0103090842c1d1001d000344a680300040c0250400000c01c00441c1c4c012010a151281685885c3c01a02098110321118004100c20b20700160080088031040001c10280103464410b8480091230b8802d0001a002160b00500065202d14031070022603046070240a010180c0d280c5903c0161081d5245c1000b0201c94000d0026003000d1003e0741c0e00070003540b01c00d552200a6682c841e849124a0b01003503ea40b04080104400910b990802d6132014040c005e00402e0701d8185c06408102500d401800c0d070036070152680101e400c40c400e00306406400060401a1804c3c04a403805000040810134904101802c2062158100c1d06050041003150034a41c0440000c0d5580e1400a4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 597926726 1250 597925476 597925499
    0xb12062413140702031905070807021305010e010501030b280503120309060709030b0f0c0d060801090614070f05030601030603080c010213060f12050c0909041a0907060c060e1501 78
    0x2d000d0040c0c0e2401d4001458075403004c03040303c01241000226800e0940c142c402215550003003501151489010445003000d80c0d00d00c0009040c246043c03070301040035030404004000001060340002d040c10700b8284100300c0ea5460744121003a081c071080c01446180010b54420841c640c850b8030080d094050380c1ca08020030341802c4010340c4901c00500071503150341c4031524201c41c418000d200103400e10003610041050901400e14040c1c000c1e83e140019811b0203c01c440c2001259a0765100c000ca5030741d18030f9130404210650184006038021100e82180d0361030460005040080703d44900010400c0000c0054030985c02607000c2d40203103402603032940e101c20b000302c1201c0c000e5000b40c8024100101d2100005140741c8114009034090780150348401150b140d07078440f400a80070181440704000c505000b5251035403620f04909200d14044c6864207110b40041100e00c1e0f09000142c41c041d260b802456040c001c60780c01c50041c025041c1c1c8024005030760000900d403c0d003000c0b00940030f41c8140301c88100000e2095101c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 597927976 1250 597926726 597926741
    0x12021507080d0b0f28150203040503061b0702100540140f030a0519030909090f020907020a30091208070213050a0603060b12062413 58
    0x40c00c041004a085500700041c420100020503413140c4441407584e401c03a96107051403601700110002541003922a1520b60302c6411002000c130042c1d0001c2401c00181c03408000850f0402c00310311000202c0800200010100d10400c00040c5c040c01050502d500203501c11402c42d0400045a500c49943e0110001a2185150b81d002d02022090411035a000c502c0c601c50a000b0071122080c5001d45000b0005040c0499045207003000c07036150084210300c0021417014000182c9104100090325030704021450003400824141d00107002c7c8500d800e41c0c40000503100000c0f070b060190100e8a202481c1d986802c224a04500610000d00c04e00c0d09200c101905842c178464180c00c6203006101c040d04102c0f0540072640d0507142d105049050500c1c4041c00d010030100340007010500d0008c1c084c524800d41c00303881c2d80c06031a030070745502c124a5500c00d0104240003c07031103a581100c0080300c41c00300500240c25203558403a0058076400a03800080b41c145c5210000111000e04400d02415480031b208261000a0081684 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 597929226 1250 597927976 597927997
    0xc03180d140d140c250512060a05010f1202090a020708070b010501120e06010e09070b0c0c030d03140403110102040f090e0105180d1d04050c1b01050705041202150708 73
    0x5925250701684200e0252218034600718020290f0307040c950002400f8282401d20f141e05490170180119050301d0322400240000704640003085203040c540180c1d02114016440350b444102801c8082c07040c1c0d420900107004007501101c5a20f051b40720a41003100078410a0b4004084135000541c600c100b000405480381294000d0300c0d820541d00e5449403450540c3d200c03410304e20560300942c0041c072a0001001011350400c0e22841100c070941d44445900c40c2c141d0200c44006007607400100c96400c9491f0401c4610883e880380e150511140aa0144101c42030b500504014240200a8201040c0503800d40c142c400500150200ca080903036142707000c0c4024060310f140014036500382000600f082c071907020f90703200448186000b050043c14085044070300d0b401c02d40c9525030160364605120025504c2d0301410740a08c00b01143c007650750050302c54440764180110380c0c0b003c40380d04060802100b150040150b80c2121140d20401e00903c11510005400d540d91703c0c4007955603100032613401c0c24400004044d10314400d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 597930476 1250 597929226 597929237
    0x60902040b010503090304120f0206030106090305060109110a03050403020111041206151a0a0e030a1a09070609090f020c1e1203040f06022d0316050c03180d140d 71
    0x7120030045403140310403983d4841a03402004100242c0c0d6003409a058000d00602c0501141c001940c0000d8256000b0781c04600050041502031060200902200b401490545000c0259103868900c0031801e001e00540384050694503800641858001c0d000705507140740c0c1c400c58594032512121000510002000290b40240c07420040310641e08001001c00151554400d100b14818441a81c3c0c1d1ba0310380c0f11580f200100510442e00b02c159403410080f9024161254581054480442102d4a00c0000081414101e03920103803080242a411011120642e0940c00d0b001c06c20f00c4210036908064491000c04000500c1032600c42d41c0840f200b5444a0038442d180801c1d01d028140101d064001c0e0301042c0c4010f04121511821701c0c0024140c2e50040800c044901301003850300d084c01c20b20301108501d4410790380048000000304215051070065170913207200300e400c00301c0c00d0500c0c40c480c0c82d64034081d43d5001e0000c0710040615002640e01c00154a1005501a411060b540c4e0040c021548030b0b124820745030082070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 597931726 1250 597930476 597930491
    0x4021c21050318070e06041509050c0405121c0f053702150c070c090e01050709081207082206050403050106060c11220903090e09060402030601090c020c0d06090204 72
    0xd001041100c11204e4501401d85c458968900704001020041c90903040003100d541c00051410303142c06868424040171b840d898550b0b2414051011050700c0309031592240e04104495180800d84007a10010481145400424010101c02c155998815501040400d40898a55507043c8000350204448004140c0081161110640090b0fa6074820700c8000038070013401d4030000702070390980005011442e00900b03080c3c61441e601c17540751007101e01c800c0c00b50b56165102d500300b001031a0000344150051021130002c2050100c10554010140540c180041c0f040100150200206c041c50341c4204001c9004c20700791000c107035500c0002c0d105074032510003180c070755003031090006403580142030300507001c0c1d0400c100c00000d11610081020550101d9440304c10030f007040c4141c910303091183c442c0440c142d110f07440d9500f6850428030340881d100d500801c420100c0d8443c600b088016280440d109046030701c141d40c041404110014241c1c00e003039030b06105540082c1601601000d00c200358009902c0240290741c200020f5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 597932976 1250 597931726 597931771
    0x4060f3c11030106030203040503070618200f041806060e071805010905060c0a050106060e241207022103011d0c090f040605063004021c210503 63
    0x3280d44580c0c100c4070400c203100410809000b41c0003154000d100d001a00c1c074215240e5295002c407035108850840d4061035810500c1084591a520a0000825402c0210031201000090790303886000302441d006940f501e0140c4180d4404448142d03d20b640309100340002c5448241504144004680d424000b41100401448440c000c0e20308806840c0c0603074034403401364203180c18441958890050400070b84a452500d402041080c410100030307240c075a540340741c00c040400400a00a5650781030b0980e100140c04100611046d040848980510304058051540e60b44802a8100421440144541e0b0b5000300c0785040034240074011410b8600000c80201d0034080502601110a8211a040c1c3d000b0b504202d140002d180c10b41c19044c10700001000810415220004619207800010017084400150492802d4100e03110312096100c1022801d619894034003600003a071f04410000100203688c0b250284241808007512608022002e4003040002d0709820381802005c0303500403103441c5c00b9261084110503a1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 597934226 1250 597932976 597932981
    0x6030d0c050a0305071b0b0406110114010e090a0506040515010602010b030d0809070803040315050705031317160c0f080c010c080d09021201020717040e04060f3c 71
    0x18941103001812103207103e80e0f00b40c0e0144d002450035101e15802945002c8802d501501c000e0250080d07448840c0c54910f050000360903090710621026059040c1048a88411040c404542c111101021140410340310003000c24201304564030040d10a0241f00100001e01c080007803c0f4003020740c0d001240c4040da84c1d840049080b10800f81c8081d6068002c451a8410144108946a045298001500c4071283c0c0ca480c440d141d0703442a80221070043d4010010302c5030022034030440e0b038058080c0c10710710314516001400d201d4038011031500401c1480010032021521045a042c1c80701202c0ba003c440300c2c4180c0fa402d0a81c20b9014912846480328034981c00031400c1e280100e552200081c060b12201030104055a5111003904100340710031103169624022400341e507840c0b07154041d00c03485000042c2d030350302c60341051901910460340c80c0d280c40400300020451080741c108403aa02c107422a90000c0c401180c450b496002e04410030b44d0403000451100c409a200c0e4440d484460b044505041800d100c4850744040d205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 597935476 1250 597934226 597934247
    0x40206040b070812100806070e270a111321060c030e0c060c12031b0a050406020106062d030b12010b04050a0c020a02010f05040302090f09060907050907140903060a0506030d 76
    0xe10f1f0b040000440e01d1703d4019041a0400c010007440780e0340b0001d01102c0481c1011144480409070a0548213110420b80c0c40d219031003200070f0540301d051600858010b00305100c0c4261044440495000001c05060010407083d00f185c00e52020040c007030010304d11001400390a000402010900551030101c10520349102154034024428024050b810301c00080c074a82c0d038200501c010309014520a82501036501c030402002e400c0103d07243e940c0c03a54180741c0000d00710b5185401140600c405091804090303c00c0f00034810f0b50148480e0000c17140800d95000301d0140c100c0e00c0780180c100304050140180c0318410340041040035010f607020002c640e9216403c00035600f80c10301e03070700150308013003000405948500a441030340c6040741410361a041c1d4075030110f4083c0000715081816046440c041c019008012b1099541050107040101189810040010182c0b44007400b81410702044514490702d10b02d024098550004005059a41910348180b8000240c48100c0d041d900c039000d11054036254601883c0c1c000c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 597936726 1250 597935476 597935489
    0xf080f071b2601020d0908030906010618122f01020c010212040e0402150d020a110c03100c030e0109061a0d05030307120e030307111006031703040206040b07081210 72
    0x10468a0301e842d612001120081641032655000c0000c885010a14001e60a049116510640ea0b0349042c007030050400b88103811003010004047c0720702404030138440411041c3c030b5150100740101e42003440d02480d02000c411100c07030030880d201a914080b0f03580400d0100003d1081c0c003034840d002009030049031905201c00c070484803060b050006024040e00a540f03554854406840811190b084102c0440c00350841c2c122a12403c0d000100c00441a40c8420b44203101180000101680c1800e82c00280d152407407004041c0083c2e07a84c844900c0d400384a038000395100b0703050038020040684681420005840c15140c1250003540c4403044036003904140304402856070b00000a541142c6500c1d0080320003940380c110050701a07488250040b0180c10600003180a103010740c41e282c04140a2000b200c1c00d02c00320402c1c49400301e250003000c00110f5051103403188040c5a808410307513640e4851001800030b000b10380020141d504041030300402c004948e03000301100c45643e0862030080c0c1c1c44555503c00d1000078001c11 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 597937976 1250 597936726 597936749
    0xc15090d080a0c0e0919060648110f040e030904202a0d0504030602070c0b040914010b090105090d1e030f02120a170421020a0618030c0f0f080f071b 65
    0x41c2c907270200f030b2060100001324003005808403680b02c070050010f0714400704c816076040000e00d5041c4143d1404c4250420715000070746050084200e901c44094880c0107200c41140110340b545880030031b0b10110a48500c810701140310094540100740d6170300c17542002c90200c5541030741c0d1684100340400c40c0041c0e840c00058031759840c1450700d821540e0f0f0602079000040201d404505500c0e0104040c15604060800b4000074032000929001c804540b42180b10180e110f000040400c20040350966804812202004020754000f401c991152074038200c0c0700d11840ca20f4640d8809402c200d010564495005501d940e5503a08903903e45000082d210201d10801e40200c0214008000c9105024a4462015800790103092001d061903801000c58803410503645802c00160022407080003040150300c500140a4500100722810070700e0781d50050700b02e2031103100c0502005040c4524200700001e40c0c1406010313a5024004070748401090040000542000000b01d03501041d01034510389124038120040119092500715 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 597939226 1250 597937976 597938027
    0x91104030311030906040b0909161b02030a02060a03020702030706050a051e0d0606020601060909020c0712230d090e04051213030204020c15090d080a0c0e09190606 72
    0x1900c1441c2c4084203141180800e110b501da041e564940034100030000d0700142c0d42d440310a80108a00588000e101074900c4e0080b241c2c841d081c0c0d5100391110081043e401d5012416020b1b400002d03e005070014000394440c50000b0310640c55941500030f410200c0c400d81c00c4494075600c40b14180c031a40160000c0348005042441021100d02d080458002d031500ea00d085a86841e0a0b10341003010340d41e190308000b0245e8002401000b03040da100078410000c0c40041350460401e005601a151a40100e21404d00308115122400707062120404807510f04a03901c2c00804407201000140d540c0f52482e15040201246a51a00081d008802040e45106561200181c0500e141e41d403a150f03080c1d0042004401c0d0b44484400220043c3c42d58401411912449401000d0064101805102c0d0880040c0902200d4011101268100d50044c50858020600d120b000c11510041c0760115031b00200b190000c2c0d4401f0707000040c0107040410110b2601c500d5200402844219181c8a064031103500c202d8400d4204a0041351 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 597940476 1250 597939226 597939233
    0x122111060a0b1c060c020c2202090303160f0605011203050318030d0f02091f080705090d080703030b1302160b0a2004080709140a0b03010605030609030702090109110403 74
    0x200b00c2400300001c03d0880b04620785076a1089200d516501160110b40c3c5610f070045054040100541120080311010309041040003090409258400c0d10410301c5d4021030003520343d580a0040d46c101c809810350b09441403002d400d1070310200009503401d64015242200100709001012031019400360507840e02440d544804035245491043c921048540740410b214500861806000300c0709041c051210242e05c50000104000002564900d03045101d007001e040700320200c0d003140455034006038a0074029110844107000c030f542d0000580d401005040c000031004109900340d40048a643d50a5803c03814404081c04580203d00c40d008400c5e40e102a1b85419400289440c04001e41c403803032203200070588820482030b400404500c1a0b1010355000080380034401504100100d000034403e100c82800070008032a2400080c00d03001d07019003c4d035a02d560401506403825006500282406070403210b041c42c001002c03a461381c0110900701d1045103070500019140300300c1d001e0401c10803800e80e485880c2600d10340d0b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 597941726 1250 597940476 597940481
    0x15010b030c0f1303060f060905090312040b0a0615050c010c0804080f180d051e030406080705160f0308190b1819110702042403060c0207122111060a 65
    0x201d043e1145502080100018005d801000c40481d0003281c041400d6041c004910142d95000f005080981c0c81803244914050b501e01400b9006a000100800540c9610f540c00010745446e40109600d4030541c1c819009030340d8030100425200c400c40008003c960766a1302c044825020035100603040035400d1005010400e11103005118188420120031070003c1c0540c0413231f0700c00e1902e04007611607070400942880350074104090420380c0ca540c8000b0f54a054200080034000e40005400f40d010000041407601404241030351800742d0a03048195010001c003c2e103001040910100d0b070100f10443ca000300d0301c1810700302e8018502900402850707801040b03d0070a8030094064028410a8103e014078008e51240c0e5a034807880070016101c081160340c4500e07500610041d928a021031909070704106031502c941c0d151000d500c3c000d50342d00401c040b40c000031580b000c038038100d00798100f460903040080c0c01d030702000034070084481090400e9005c0d500000401340c0540d2502100314400c4003039000900020104601c99 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 597942976 1250 597941726 597941737
    0x7120f020703080d240f0b2712030d050a06091503080334020105070503130210140a0903050d080417210f0411040c0c0201120b040e15010b030c0f 64
    0x31100017400d0307203000320050140031348052124500c0d480034006000306c05e03041014201074100c5c1c0340302500e000900c445502545000c0104030b111a80300d500941101d6540d012401e1a459001045a071101d034000b010000901d01620703c18009032500800203105803145c020302d0034030841607840068451544d250554603510052043c0d00740850010000520b46030340c0210000421603180c4a001d02d00c0b048800707400c6420203045003091060510400c440c5070010a02d03045201c0e810390b0b4040340e2303200b109010354800116003007802003c50f000c00e01d0321007142e1100740380040b280903a0446036000b010903801d07074601d071007524044c280c907031b9003503800003882d01c0d42c402011803211313107070030345d00241c01c85401907540d01030030303210f414452042c2c105210a004011079040c50030f0408440400c18130b40c616002030400e804150009052041c0c00e074612500461a81c09101c4140303010b0014081c00300e119402c117440300c5a24464600c900c860030004500903103004280c0348102c101019151402018101001107074001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 597944226 1250 597942976 597942997
    0x9070e1003030e1207030c0311220902030f062d0f060108150a1511071412030c1b03061602070611010f140a0f02070b0411031c0507120f02070308 64
    0x190807842c06501310402403603000b50b000d418091102411850100203040007036094921400400101001010450751200040d8080400000b0707540e036075101090405a40da08810454000d02c0104108814880d01140b0350490101400c088944000c8208020180c00c1e6100c2403004007641c0056400e5008014954106440000000880071b8807070000b0443c2100b0b406c2105c604510080b0000301c1600002d03104500078113400680304407407e107401d0594615a100030544500714410002015030010710440381403000200503602c2079003201c64094401c0d6028900180203204520014011650f80c20300b151603246241c1c00b170254281740100031120f022540d1301b103103299582c8850074480d0480d140310740031021401a007501c940746011014801224084406d400079140101718840001d03241041c042e62013030340110504070f41e0304c42c000481d1414103401c0d072102035000c00341040300041d5000005014501c0c82110981c044801c800c50880c1e00d00c1040b14400b015910042c030620004103848080d0000101 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 597945476 1250 597944226 597944239
    0x110a0b04110a080a1b05030309090c0d060503010e010204080c03030a020c0906010306081b04240927050f06100e240d031106070810030602090402070602030f09070e1003030e 76
    0x44901074070341841c24004c0c0445680203070880030484070340154526001400201c0c0594103003d501004250300e51401030080005000025440044460310b0784440040c2001400030042c2d04c440c0790646000307610501442255218a1a00e0030b01483e0000c21101104142d07409032004a50b0901072000aa2014107001d06150312020086200d0340d04000365101c00c10300300010001c0700408000d000855610048810901c03040c09040b1849050010070758045942e005000184100b640d007000c46c070f041d07110200b614400341c03298402c010f0100000d4400c400042c44419200b964580188803412034603039104040d000070f070300d0340001d580050214030341c3c6801024400042d0502500d100007507508682500c2100071640340e071400821410100984c540c441c46c0c600740000b050400c44042d6041c19001e01c8001c02040d000240704030503403101d0701900c04882d48640250349034141120601c002c00740c2220700600ca48250100080e0000c0c1e1950040d0154444007200d00803e4103545040ba902c1c1c03081080d0540010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 597946726 1250 597945476 597945479
    0xc0e06030a1208062409060f1308160909020a030206070f0506070f1821170f0306040c0305240406030b2e060504060323090607110a0b04110a 62
    0x95090000d6003100c096941c480d0030521345401004020420395460350300780c19008642020080b0b102c1c040b0740349074000311911600c0d183c0300c01c0c030b0306160f1041100804100d4040040060140400203020741380d107124082d1403910a84070803d801c202c0e019488040d520000e289002c20240c1008001401c8203406180705001400e61521082d10f091416101c000014400c031000d840207503400a4440790000041900f11711507840c001c404e0011034420b642c00c4001ca11407c6074001040b03c17038641c0d01030501450703c0007619500c200030039180641084400e2406241824600d843e02da109104140c482d00f98203c0c450703122360070484076000341d140c0301d041241c01a90307600010011842010201d44520004440918001800c4c001820040000c94018415405000083c0202500030050324103031030b458980001c030300041581030442100c469115880c0d03d548001840010480442d055100d8089511071000300b440d40106a9940c0d49220380c046c080410f6140800d0015581c51444102140000c2000340d425 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 597947976 1250 597946726 597946733
    0x903100903030e07060503010602150402150307200c01090e0402090f09010b0d050d0201240e0a0216030e0a0807030305070f020109030209070509010f21050a180311010f090c0e06030a 80
    0x880d090300840041b80d4044010040d0f16410085e020707209102c001340407020308056021951100d041030740110b20940c0440020380c1c207031007444240e946c40000c0d298505910081c000307150b10b5480301d02c0740900181e0f10a0700420340711610b050550045602600801055840202201c012007005d8203564495484003502007540d65004981005030740504084c0c001d40031400320280c21031f403011100c0040a04040c45500c4410841d0b4186012103041c01d1640300603640302c20b02140280f0407402d2a800c41d101c001290b400b407551004418041c21800c1d00c00105091311307058400c0c0c2e40c40c014800240024030411040000070103030311810400d01c0c410704028040e6070700c0b54001020380e58111404000a1400f28580340250392107c540294180203042400382d00b204d008100f0300f019049040b9614150716803021034001800350f4003d08011519004400c1000c0d00d44c54010041900e82c00300c400301c0e43c02c16130080c000e100c5034401c200402c0c0d4007240c040c00d442d2802d5405031483e4002484151716018043c01940403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 597949226 1250 597947976 597947983
    0x9150516050f0304030b150301110d0903200604020a0e06061b07210b07053103080a0504140a0503070e041a0406090201110d02102c0c1201020903100903030e 69
    0x91031180086d142246002042482d20312100301025200c1d82c1469003512981a414044a85480d00e601000c140303010a0b06050310b80d10010310000c1d80c02000c42e642c80c007100d0380c0840d80e01e014034030859204103a1952200c405034510025108154420b000300104a00e2245241c01084041d4404064940c125a9440501e04010310784041400b01800040201d040110070240b03682d01030b5050800c81d08214820542c1e01c0354220b44280c01200300100c028074542916180040e000442c0c0c400c0d5960b9960343c40420040440c4c00c948913044180092240032400c1d4608121000241c0300050010031040d4030b03012900d5000b05d4003400075a080c456010b00200056061294288070703d000304004560b0501c0c0d4400140744240403500356110350030010301c001d4099401710324403a9204141c003003c02c0c05046a0040e0304107100c84980b01400300c003c0d0003191003103d000700c0c1064603e5011076054000e070480e12a51400d13842140b00e0190300d500005100c1400000560140c1400c2e4024500010141000d4031014075 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 597950476 1250 597949226 597949229
    0xd0c0f0b01080102130b070c0513021201060203190908250b0313021f08010513060b0304060b0325150c1a19020c030f030a141609150516050f0304 64
    0x10540d40004c0c0100e200d45c0c42814400003010800407461406203240c48a82c804880390182034401c110b030728848001c881c4503070190790840321004691005540d4880c3c2c080d599600020a5440b0b0100324600b0382c0d01140196500d204591159000d06a1100d2801030185c500e1a06900c05103e02444180461401400070240d441241148412641141c2900405c40c000411030710f5982c03505029004510569400300c04141141c006445100c10201d042c1c00400203040c4641041c111100c0c00300801003448181e41044580100c1a4240c4441e0300368801c44402914183d0310580601034103a004101700b403100408810300c0d02e140d181c00c1544213030390ba40e4000b1400a00c65103101421405051024007100d00042e81c4d611714039018114508003044603000d480740140d84246000c0705020000514040c1940c1168220742d501031000c0380e0b2494114041c407485504080c40d0000964103d00224802c8466002210302c0c0006846041c00e0107490643d00ca490302150303900300c40720f000705040b411001340208040d00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 597951726 1250 597950476 597950489
    0x1b03020609011b0c021002010b06070b0105090a09080a0804051501090203040507050901061403130b01030c030c051909090c17010209090c211e010b0405010305070f020d0c0f0b01 78
    0x4450404800c40d41c250f84507900044480d03410b001e41c0394409074020910a030541d0b0705440300035032031511660076030040034a05500c680115000903001c08002501030914180d0b0411110ba00140e2140e02d1110120fa110300002031091408011480301c0d58095400303254018401e0084542c100d407820303050380c4061f40a9101e000c5ca42d40200501041080520030310303003c5c00c8155600b131015817501d80c0042612000d084000c0c0c1c90b18000021691103d20b010006a00ca50011102880da59407440c00450740c0000f0312050f11140c46c007079070100386494142ea80d55021202d412100200c1c5007001402c100801509104441d13032454001c00149442403600504288094800016150070501082c0092020010a06103585400b004200700362000d04840c1d0340344403040100350701c007955200407518070fa240d918249218800c02c0d400000c1c2203a5694010300503140300784d80a1000c0d448942e01503845903061102c0780f016030404803140c40800c1c0b0a00002c102c050140c4c40300d40610301e8548500b036901d642a0401d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 597952976 1250 597951726 597951733
    0x50d06021801030c0905010c051204140901060f0c0602090f030f0304050415180b0a1802310324050a05010302030f060c030a0b120d020a02040b121c1b0302 68
    0x1d0741a00c07909000c000e8800a0070140721030080d03803400030103040e894024103050004106420082c00020001c1c04100d003c0441c40650703032a16400310745222400300030300e00d02c204c11046c004070700b05d84101201c203000d082030b8a9844902e0040e41e110350103904070024594105180c004030401641c0d0070401507440d42601340185d680d543c00d000c00d010030389028002e98003001d60303a400104000c2c0d40a00c7c690314030f282c0a400004800c01704c403000400c090303a10b501c110900c2000340c00383c044849280d402081e25080e203c0442c01c1101d06140d60036190350108404040400036600108017040445010582180ca030416130200503078011118800c81c0c4064170364084140d5a5001801107003810070010307201c5103603440240028680504407810301d20008208004c050b8a4904074140b40d1154407001c8180c5100106580343e44003060340c029a00c4060840c141d125030705100d2501c0f00c0c0e0070402c00d14200426103030094003541e03c41c0d0a4005c200d1b00e600b50914100014009003440c6039041c6080c1052481c400d5028 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 597954226 1250 597952976 597952987
    0x3010f050604051018051b0a02010f060f26012408070501020c0a090e1014090c0a0f0e041403040e07080705030f01030b040c030606290c060f0a06050d0602 68
    0x7440203e4500825816050a480c2c0083c0b014444d020307200103050b40390b00d5001c0f0b00790f61002d00340802c00c40c3c04120190301d0f10010540112098040d0450412050f40201c10030000395105815400317004944254a080e01032804464a040074412201c0c0307428107000000301e81c0031002c00b105019035021701c104007103004080300c0600c012841404800002c0c0407d10040c1300d10f030000300000b84511300c503105000d00d00340c3e58014012041c5044c0f04070f9421002140b02001000020714250708112011100818207010303d000d403200601c0c11307081c2c100640d0384200050070580d00302a504d2507200005441564850701004503142002001c000a2001c1c01c00c81320f10440700c0c103003280041c01c00030300030384a0003c0c0701c011310070071a004844a00720740c1145d4114101d02e03520349590800d4014200c441d0009072495003842404100400ca010f44004280008900c034409106030310001790b840c0c0200c40c1034814641010300411208084c5500140e08011000f0000075002d55a10010f4040c0c048000200c4da0550045030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 597955476 1250 597954226 597954229
    0xb07060501080d140c0f0d0c030318031d03010605040c0905150403080901120b03060405070f0602070e0105010807200606130504030801050405070c171306093203010f0506 75
    0x3854010074226008100d0040034030000740c20b01581d40c1200c0ea4185002c11000310000c0100b080ca503440c12900f05541040d40d0580c4001c0480d45004030a0300841d05104281c0800b400c000d080550305d541503514001442030213001d00800d0010003107507a600d0342d280c9401040c5a40e40d44502d000c00d41480e02c903405100d1810040c00281d014502c10341d640b621040c002000440c0b09a000c54918a1092810700c00d040700140c0040024030503c00c02d20340601c01c13401040308001c4002058025a0a0040e108585981c2c48500320390342c0c20035009440a20103000010000b65005108141d00040d250921402c0081204142c898090704100742508a0303001105104107804c0250708d4140b00c140c01c00050183c3d10305902c02801040c818410700d40100e6940001485003449941e900200d180c3c4503030340b0943d00781310724415501c51304016800c404002d8140e50004a9902413582107007107403110019043e042455243e12266409002d410401d4100e01000050031580c0c00c0c802c0210003120440700007009d090150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 597956726 1250 597955476 597955481
    0x807090329060a080c06030712090c090f020705071e0317130909021f140d06050f03010506090411011e020f0c0103020310090504080903030f0c0f0c0f010c1703010b0706 74
    0x1401c00e405681c0c903c5082c8140310021404100101e015280180d8980300c00c50200d07045000f020182c01b0003460424590108151080000b0884003c0780c8103015441210178200200e01c00d07007500800542c840001084103038000890b00e050498000700030310001d40d1700d45481c0709e4000c5072018290203504c0002d41442c9119032446990150156903020410410207901003880c400b44101940600c480f003008903071441c1e22841317060071500508400241c803048904021000307020030307000d054030500500103000d000e420141300c0c1a100c0e4100405130003542c0c8494942250454100310498100410321b100c04018807818030302c00d102c0d91060350080404104410310701341013400d100741700b504250041046c00921803500054100f510904900010652150302d0036800707511680811540500000c5440310f407181c58540603200d801030318400c0d200185c21900f449620345000f40ca0003540445412085151940305800c2d030110740340b04084114800000c1b01c9150b03c00d40090380b00d848803200000340d090402100c0d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 597957976 1250 597956726 597956731
    0x605150706051b1b070302130e0c12030a2d0f0e030a080306060c0a140109032601060c054209190507031b0e070e090402010807090329 59
    0x190809420a01d40b1801c8100724800d0024901070301c4102e08220240d40c4085c009880190360040c504004070317001d01c45040c0038003032051000f6510b008003e4440428141b00c4050605020400e01440c5010740420094982c400302d007450180c0c19551550704007517010300c2174448900d1004c03521055643c8540c5ca10042c80300d010801c5190090300420042400201346209407500714a003254040d40340e05900b03140364904400420f001c1e2185820800302103407950190310a42d020b500980e60703018405059403100343e1108850054405140c5504010808948200030745d09059205109559002c0995410020040414074402d40800608d404034104589182d0800d0b501d44d80b42e0041c410103152404040d41c46440c1e40c442c11040841c01800c070f00c00c10400380034201c0034603031100d840402d00611b02c2c80543c8001c0b090092283c403410a80108400300e001c0e2108290182c002002143c4c0ca5645038011500340c8001f8102d8818484008004030001e001c1584220b5581c51084012a0300c1d201c440109a40b800c02 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 597959226 1250 597957976 597957991
    0xd0501060c020a061b0602030126030406020a1514090d0219030e0f06120f1512100e0c100806040c0c0b13051507030f05010e131104060515070605 64
    0xc1251600068681d03c1808080b00c899050603180e19959500b00d200b440d42d581001000e0b10f10020010806024030003900200140580103440c903800c41040e217a50b00e01c40d900a06001d47d0180c401c1c6800075a884d0141c0d0090100d01e46c000c9042441e0b00d00704800c7c65020780301000c0c01d40015000c40c0c015a81040410544528907040c0400d010311618041d00c510300c2d85000c03500400d884513040a8540799482100c03001041c03082841d81c180790004e844c0ca8100c40540743c035101c800198047c5c03000c518051f55089a00303004100175100f40301c50302a039400200500d032005921801402c420501079a204607022040c0c5003c6e884c0d040a0349441c0d0100011900c1e06040e410038001d0440344500420010240d003a07109c44084a5415a01700c00e00f041c83c40e0880505050710000d14100401c03000c01c1d4180c00c04001c60754592010700c040c7c0d072140058484500120340c200b00300703007240c100c010200c0d8440e000c41003e50f0010f040080c03000d0325040490170030780c218003210404680c001070301d2080203424810302e50702084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 597960476 1250 597959226 597959237
    0x9020901181a21160e0109030b0f04112d0d03020d0507030306091104230906150c1213141f27060908030408070e0415050c0d050106 58
    0x9058402da0b0166820301100e91080c004500c402c051000c0c503410509600c1082e0a0381030710700c0c0c00c00c2d188400d0b421040960000420b22940114030354001c441c1031703050f80c2d80030031444844c0e50740702d1910f91020b02c028425200e43c014407049080c151541409624120204145036000c200702c01c3d212801055860100c1d4080e0344103400c480c0109502144030905140d691820307903a0f801080c10100e000d0310280e04100300040c03400440b1840409000000d100700c4250034040b01041103507020182803c2c00d510700141d00140c074030300025400e2920704100d00c1c5124640c000719040c4211b40c1601d034640159540413054585001504410031480c15021800909124140010146c5100c01186074418400440a06903807805080e1103480c0c02a980c01c2d000c491042140c000286651560200a070035030311850300455500c200210704500003204807801e44d5003a1004141152a1201c010309030350340100283c0c1c10350070b50307901403000484c940245800340d402c485016403650398401615086030f8043e40070b40280301 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 597961726 1250 597960476 597960479
    0x51305090c121f120c0911190201050601080601020d0207060f09031506031406010305070b0904110c101d0a1209260c01030507080613201e07080301030602220902090118 74
    0x4a18010585c2a944085070110341a41042c54010309402405401002481c03c0300340c0400b800c1d4154025032050009998a40c5283c03183c03401039031030359140c49507040103800a0000380019070180d90301c00064081403400c4140690f480e21841c0c0c1c600501e4201c40031f1a501c80c0010410b1200d100700001111107080b01600c1c43d945550382d41e40e6100c00700c1c8030306280e102002c100060b1a60307459100d81446000005174541c0e40320080000d9849076181c40070782040324603143c0309000788a2446100040680a040140304001c0b482d1500d00802841841100402204482c049000d40b00c3d0b07014149601c00841c44616001d000340141c80c180702c04400d5060405282c901001a015030208031181c04c0034084c0c0300d40f51130607410041c1c8005000010040c840031481c4044610800c050400201011804100740004100301c9070381e444c0480c850094050034020b810310051001c00c91690091a1121045050b0080c60b031810307050b801c00300a5a44500b050990108008405580109950407800c00c043d170500d8925 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 597962976 1250 597961726 597961733
    0x40c0e03030a031b2a0609020603070e01031103010b070303110c121b1609021e18130b06071e0b07030501090e070501050d09030215010308040312051305090c121f12 72
    0x1c5c1d40204800c4040c207401a107500600030190b203c0303200700350080c0103542e4910381844007401c800320142c3c419000170710702031450002400355801d07641030722902c2c0c0030107282040d1910210007030000d92480001456013088030200004041001020700542d203e0304648581c071012504d42c01401c07071700e05825103400000584401c004801c2c4004240e8030409801170700c42041e2041820000d469034100240a000000c00480545940d81e140700c1c0048211109140144502d100109980522058580002051088400140d0080307003984109a03e000450001106900d41c0c0c0e9034500291148030200f507a0314014001e102d00350007a403440c17540d5030006003e9640741c41c0c0024010710542c00f0b054402a41c030b16240303081610920034064894200b9527010040e5851381003a000320750261001310740405031822132034083d0740103505649100c0080360405040324076200911007610f200501c2503441401c00c100914480300b034200410700904d40c1c9810b004500200d640c001d2000b00e1107030003e0080c038559071000b0000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 597964226 1250 597962976 597963017
    0xb090a05060d080c2401090f180201200303040f02120109050705040203070e120705100815090a060306140106020c1816030209030703080918060906040c0e03030a031b 73
    0xc19030001c1695034800001806606041c58105c212160280c1004440f115000c001c2c1c03a141a103c0502c0c0070814444c1d200414800c50384104003c000104071040c150001d58010144400b540c00b1003500d071404001150740f0141598011203044544282c45180541503003041c0a204001901d44c0000700240c07146500c580c3d50b94000e92003900e101341e40000025210310f201d801e0421100b2405455030b04007001541800d510380d415030140300c0c0540c1c108000591b049120b03400d046c0c02042c1405200000c0398076075007480074200004200b16501515414004005034680c8036180100c4040d0810300e5155062400081c10b1440e400d24180c401c1310020407408810304820700e6542c1180803404250452201c06200f640070780038041c0381581c1405103600c000b05020052006241d500d1085810004071f54124680e038032005401c3c0ca40ca500020481d0019400341801d80c02000c0c2d400c1981031101c580285a00080d01c0c66124060b0140000d0311081141c1c030501c4e4801e4614030781203403801c142109400360814a0728 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 597965476 1250 597964226 597964249
    0x1091802030a120302160c1a0301120f030509150c1c050d0216020913061104150e0a090e07050301050c090303071209030c141f080604020901210b090a0506 68
    0x781454a07110810041e00030750459815041040d0380b6031b03408034141040540d040f490712840c00c4205100a98003c0b4014071021241643e942e030a103c50040e00b0354841c4031144c940c8943c11000c0c0101085075400e19520200b240c0f00e00c080360004261740d6420300209a00b080b20000b211107582050a5001003601e80060a6800c3c0d070262000068852601540128080308403003800382d0021203030010321002801140780c1e41d22090050409000c4c07407100500c480040d2146120342c1030454407074040a116a440b9992074924a4030081003c00c0940c0c440244000f00d40c2d510301d440600380d1020800300041c1c1000c0c000d1a03405075003c40618249540300d07020035101d100c3c40b6001070640a0488100c0074040c040d1b20302001840d003010b1030000164840c611500b18414441005205580c4e4541040102110701d00300c18180c100391359072040c01d40b40c0406000285d08204205414800701607800d440d44c142c44c01d080209a168414081240319180b01842815031014180203a1142004100304050f100e000c071151 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 597966726 1250 597965476 597965483
    0x6031203060e0106230a0512100509061005190f030608030f040e0c0c0111070c080f12090301062c060d05190305093708150a020c030a030501091802030a 67
    0x5104017290703c0092003e58020310180c08283c001c18082e04055021020303216043e0b603110401c030341d40c0b5192241401d40c40301d0f20800741d02c0f062440002e405800c0c0600e0010517030259041450400290100c0d1282100f00010081c0000b809082103c200d15414002c038001005418007840c501301020824128610650040d00c0222003000049109568407004803089000528001c000342003c880418055034041030060b64108007454020031045070109034201c0320038a000040c441060a07c0354484d40360000035030300d5819503031200300041c2101c2c840400c4c0440c001c074410210400481c2403100c072402d040900702c0e41c041c001d0392285000040c40043c100700100e60f08a8040303a02d5190b8541100e09100742d1140b0742c2c00c20404e0241c1c540b404030001d441c3c41c10799030506901240a01241032403161504501c40c40880d5408081c2840c120000c030340e80e0a03082003100601520300f40b0030140f6a0301c0c540c4000052000659240c00401c14030280b4171070303689000c0c005180034040030101c3d000640c1e9181c4404014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 597967976 1250 597966726 597966737
    0x1f0b0f0d0201051215040516020303060d030e1306081005040816020a03020a15030e123103150b010207030308160c020907020703110603010305120c01021c06031203060e0106 76
    0x10040da0f0244041c3c9881e0f03804140c6201051404820700c4504411101405001300c0c107100c0803803650040001070800d0980c00b58011820341d0b9078802004511071080780300f0f40a02400c5001640c154031019610a8500589503000ca6014940840b241c6019171007400c0c103000608c0c0400303200001d0000c608a40d1550f2a10b50302009012960000401c03034a0150300095019400341c10009500e1030609520b042003007503881c1044108403403200e494589500c0401d00742c0351740d420410780d12101ea0030703486101d40c1302655881c4248030f40030803000804201c05400503a4420256aa0103045003900d00074095040b03800e10280503118138540d0040c0c2500009096004040315000011407664410316004005507001402d0745c07014101000c2c0a07480b0706982c04155160b2800440e2090320b8100242101e040b6a4800014000d0018a400c0d44080d5000340c12101d8195408100481800d103515151004031072040d60300003152859850f05128402d080d84005c018542095070030001454103006450454602d170806 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 597969226 1250 597967976 597967999
    0x9010c030302040905070903021e010e1e0301090305030f16090e0601110a0b09010f02040b1b030c1b0913050d03110d05010306020406090b0f04032d051f0b0f 69
    0xd4002e80940d03005540c00d680303050200884035600041c99021a802500e60529220b0141030100585405841c0b250104615194110a17410100f9809000124152042c2c0a10040d5000030b03003500d20f44042640021030201c18005040c4200002c15001240070380d040e440e0720030540001d8040c1030b0f5442001c955180c0b0700c001035083d9000d0150001200c0700c40041d01c0c440d80491070596402134050b60b11400c81d42c40e011590b080d03031580384221030680c3d1580100301d0500d01007200881c04e08540001d0907809000620210442c1081004000c54100e0704001340c080c0310344484240055100003c20b20641400144040c01c0850350200714102100c0e600e103408503d070192503d1810f414441c03042c00c2c001c0545400d0001040c0301050f8094404da0300b0390703034a0900e0320360b61746100c005c14006d1140d107500c541402c200401c0060300e00d102801c1251694421281c1d54116110f8056001403104000e4071290000408244136110700c0b0080c08640050746800c10203c0382c410302148407030704000080b0f03004020300540c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 597970476 1250 597969226 597969233
    0xc0b011e06020d0225170106062a060b01020102120c0307020105070305070e0d0203121b0105060103271e08070204420806160f0c1a040f0210050a080f0601020309010c 73
    0xc0240141510301b005140f65449120307840c0c0204864425400082e1401c0680746144a117980440300744424105141c04004458807007100a252012409066660801c0080400003141c0d5405100d0300950404030707240e181040021342528030040400381050b11f01801c10001c1a04900e890200d420280d0796030031041030a10110b40703441d05a9601038080751012504411500703050120030300303806e28800244205e403100c4005405440c075900c0c5404801d913503c60606c0c4010070141c002003c3d20f0081c008030014228400ca65940340c200d161058550007400265001941014015080207001001032800e20407155128608600c00d0924010924034502c040c00580e051414010009010220152502c900b07003000c4805036040c4c58000d04011650442d40103144500400c010003000ba04010740116019a20814030318800000307004035180c845181c80000542c0703844001882c040f2598135580c4e540d09040ca009018030304020418031100660f02d04100c0107990100658041c0c0400382807030359401c2464903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 597971726 1250 597970476 597970543
    0x10c0b06121006031e03050403080a090306061212091809050309040c030e060921070302011d0610050a0b09040b0604031709010f03020a021c0c0b011e06020d02 70
    0x9140840728452444000360100c000e5100300112403180b45901d20b0054035070904d80401c0466000038020070304c14003003000410a80c1c401005060124603080500c03940300d0303807054100da040d5042441c400341401000000c00013000d040c40d14001c1c0d030f400d050402a2900000c03c01040d07001031800d107480e03281c0e9003a030104001002602d1014034028000c0c021221034950040051289444050755071217980085401080007181903001c495103800d0254031407482d800c1d100001d40c4000790440842d0342c5e030b00a18aa041018000000c2e80c07a0500c090207450600e42800b07400c2c0c00d2a60883d0f803158600c2042001000803030400c0701c000b00c2c003e48012802c880e12100052031401103500140017225084210a04408140010080070800b621072046031603c0400440030bd0140c194008056445000b80740d040700440f0301600d1003203600345044d4080c04407554500140c0c403420790040700d0710b40601c491101c042c4000b01c00c1c07501034200c61008002c01c0d40d00c00802541c4031041400701c0980840820195160b04a10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 597972976 1250 597971726 597971749
    0xa0b0111070501120f02030a050f0105060c0706030507050f1305030106210b04020d02180601080a020403200a0f1202030c06030702070905270607030b0901080a1b1502030c010e010b010c0b06 83
    0x2c5c085459203071a08581021b03140894101e601c148072400007050394a1300070b0541d0b0b00014400c0041040034140325090300184400b030000d01c01d2003030500170051003212040050451420120041c0e0442e4542004d142c20348440340c100910241c2d40800d80d81c1c0c8141c0540d511240ca50304904099101e40356400411000d90400301d000c1d401840071462204c80765203070300f202030080200ba40e406650b60b40360108070080f8002c5010040203542c00141d96041030b040c9034411103980d00d008040001e840e03524400d480d60185117501009440a403e2a54415490305000c2c040034003030151010352440c074044000a448884900075201101d03555408903134180448207821601c09c01030006401080c001d519003640e104000c44500340040d04203101469981400811507040740c006d14002d00501455503a50b18862501140d640c0903a40b40b070368002088600503d00da50300d003007180c02444c0d03240c240c2c0209601350f8154a064000c10381c10050311413040c0e68010701c0105c000c1e400c10818055500e52400160044544 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 597974226 1250 597972976 597973001
    0x62b02060a0f0e0f060702010806040b060c1608030f0a0c0602040e010f090b0f132a0903020102100e0a03120b0a0f08012d05040302240a0b011107050112 67
    0x10900042141d00002c000382e200550b51039045010100c10200b00400c51500902e5130840d800344514030041d40582882c0d41c01007001040850f5030100000800c0342c03600450310f40082d5600c21481c2251449109921001600c40d01010358542400e800c00300303450b44038501e0702c107041080d4800c0e0001403000580c142d4028007914982501c0550713590220340c15040d00ca001d9080410f14000300d0410b28a05200c82040c14000901610300407000000ba8400402868901e0610440c0038058000740103181158459580a0368035114400360460000918040340c03c505906858509032540992220000d00c2140e51633240c5402c1082c100b0703413071b2254003030940c180c550358000030041030115001040020503029102100002c004042c0d030310283c1186451004440d4050500a0700200e0850016030445548180030b80101c9001200b15402c481005002d040b5030410071b000f600c1401040ea40307901854120200c01d01c3c00039a6000d00005860300c407400e0344035a40c18081880140c40348807195800501e5000c1d031 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 597975476 1250 597974226 597974239
    0x607080c070b0115080a0912030b01180312020d0c17160519050c0d0b0604021e0f0a09090507200127020f100c080a0311220b03062b02 59
    0x3074813020101007031860401030001c554084005203c0c2644d5104212050350804180c10001d161800181c0007010b000c4602ca0400038403402c550300c91220041d41c50700941c800c0f8002d4118a841e1000282007404682d03411003003003c0481ca01005c078421612403c0782d20354000d003150f603944129103040d298240d4604014400d00802d0391081c091003c0c0106020744500880540d55440f4030361042040c2103200500003028600d012010961900b410341c05000d80c0e001c08071546141c0649105080b03120f8100800c81841c06000040c6100000c0c0c0c400c1400c80144402078081c8218104400c0103408101007000c0108410200300112311012002d40241804401c0d11940901102d8051800c0b16901001501030340140820000c0109600f410503240d00034450300d03680c01010402c160b0b83c03d070f1940e1000303c28200b0991036500290f05000108020045d484031207e00e2580306011214049103048268011502d10700d05004100058a900341c149a071103801c1d003e04840d1101d1500d0300d0800c2c0c40103001c069001700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 597976726 1250 597975476 597975479
    0xf0e0a110625050708030309121b0a0b07031a0117091c0c02150309210d060b0c24070f02190501140906090709020918040605011502030702030607080c070b01 69
    0x7400c0d030400d071034103d0041c0180c83c1d029481e034101d16036034802920044020303804040018004016a07001c1d00300da1003100b00044a143c483d8400300d1600c110b0b40c4003070701c84a80c2c04050010f4280c02d4425240c1c04c0031800305964044000e000007074070111000002c196801210030001d140d0300024800124001d4036400102495650210020562006e1172412800780b42e600b240d0012081c100c0060364070a00c440343c01000c80010000b2201c203c07a81301031034000c0c0c0d285e09201019440040740102c802030610031a9803070315602a00107061a001c003003800409401070300c0001c0c80c4030040d003494507684001141003070348444141c028100d1a04110640d880d10f462044040d4200300401904005503022003540c1d95074464076025507641d241c140a4800184a900000c010000d9011a030040d02e6903080091a0040302c17028444401c84a10085508440082d41c0304010312009182400300c61081c002880107500b048815030101340d8039030000c0d260405201c802c0b4001458503c0a2040700c072410782c083c1c070000b00e55 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 597977976 1250 597976726 597976777
    0x60315090403030f1812050a12020a020a0606090218010e060904140723070323030702070f0f0b07060e0a080a1d0f031c020705061602040f0e0a1106 65
    0x2880c030f00b001606514104546107110b401d038020000b20158106e80c080311100035002060780c541d48014030001c01d21034600000422640c061014048030345284c1c000d0300140c2c84030301d4420700b01d0704660040758807a0b03c1440541e44100146044403181c03407007070a10f54916110a030000c3c2e15402044880faa2045c1008850301c200316810b410107006190640311b00f000c07000010f104000c039000b10500d080701000140614004244140d00640e074404210380303400b9000c4d061841c4805075501c100d4072400560b1044204102600c40003803042c6c000d018060f10311452908140a030741d1144107504002e8078030b544600d0586101c20f03091018425241d400590725640d020301c044003401004030600070f14881440f9800500081c2000d052103800500c0040141c68a80860b649058118620500740c2d000c500ca41c8001240c00c0d01c80c200140613190440c0d541c0349030142d2a10400c402d441601c52403d6919080260480d070f050000900e000003298010b4105844040341030105665006262105200303a0305440c1ca425203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 597979226 1250 597977976 597977981
    0x50d0606030926030a0b041415031b0307030201140d06120b0108070e0f090a050f0a062016030c0803150306090a0b1611010606050c0d0905010c0206031509040303 71
    0x914415410f0003003040c00c001000000c011a101c4038400c49008000042080c40e01d64800040307420005e0000a030358040c2c5040c0b41c80c520048604054441d4000051406450300f041105112191000040070520700880031a480300310900c4024144a01d18a0112440070680d0658100b00c80c8154204006c0b0750300c3c8860000800307030001c151200c0d600c0360004220407101251410a88218000c13600981d120200c80c5a45402c0040051035070f80544050040000c03414030949404461040040c680d6101c1410054102c400c8428070307800c0f00b445241c102c041c501c60340301541c4a000c2440c031071481d404002e041c1680d084440c4e82e40100340460020800c01014929100103450501c01e038102c420a0740e40c4c0c840a50340300f5541034082c2c49690b00360300003200740c5070042c046210007500b854000c008456650000b42500c3c0c0c15040400820404145852840000c101c0d40941c14407600d0903083e414907000c00070b800d1148600c00a8003925001000a50308004003501d40300700e58001d85203100525050600400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 597980476 1250 597979226 597979241
    0x6031e080403050d2001060501020a0b15031c09050102061006030908120109091e020f0f0102100f050108061e011401030b03030a180b0702090a05130c0806040b0127050601050d060603 80
    0x100c10f4201700000660014843c074403d40b60181c000b00384941c10358550380100302c13008041d0400c5c0c1040301d95184480d24103001c00c00c203071910b800300010520742861018064540c1600080e04540c0604100305250b012a40710004540e90740c1000601503102c0e080c040b80700d104000e1040d0255844000020380454281d2000303500600442d0f4001e8071090000341c00021441d203e4002e544041103003080d40103450200f9001240100500403680c2080107249000150703040405483e00b0aa60340d0010001c07200240038013076001003035090700881ea00c6400d4a400a00606020310803007000d0310b03401c0b003032540d0081d403050baa401c40060460b51221a00c0c00c2c014806042d6411f4840007849403040018405004410750751250360050000003203983c0c035250075009100044c11440c09580d04014100410100b090800191001c4405401d541c6420b0400c0a103006042c1c3c0411801001c181d0000c1b08803500c5030b04810440f2444a0110709078880d00012035180c041c0b000140201e9180c1640011050303010b84c012003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 597981726 1250 597980476 597980507
    0x31103012c0d0329190f0314060412030c02070515031b031902030402030109080c03190810050d05100e0f10020406050418060b07080d0f06031e080403050d 68
    0x58490380180400c600b43e030910202c1c000051300d8411000344101c490794038080d03000700181612118081005074403040900540c031011a20715204024010b0081d0120340084950407200205000d003815a42d0740c007120303c00e030304520400d0b542d43d6111600c14400e001c40001000300402001c2c603500c0d030b206c100b84c50307500a403a0b006890840384401d00080c541074054174403640f0803a0321044000e08054000c00650b1004008907411f550f80c503241c0d400203514002030000e11070404000c0d510741082c0502d00d01e84111001d40e0700103000342e503c00c005d1080044801c800039220240d411401661407481c1c040d1500315a690815011810401c28420708c1400051030b0307480314065811075512013032030000301c4100e02c200d00400d00041d1041005100c4074a00c00d0030350751a1003400390009060b699030315450030b06400c00e4408983c0320200140c0d035591441680a40c0205030702000081208070314507075030689400782c0384820740c1e101030081c0b06400c2404101e1082c0c4000b540c00409640c1d148501d564010403c604110828 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 597982976 1250 597981726 597981733
    0x106060f020c0909072309040804030b130f06091a07051806120c0c16060c1a150f060d1a0907080c090402070215120703050a0c09031103012c 62
    0x102c10300d00d8410980c90113120b4040107441840c0c2051002680e80d062006005c0410108800c002083d446010071540f14a000b02a100c0c2c2365070444c6401c08002d90040c0c00300b40319400c00042c04020864130300040d104103500020006044401d4a0300141181c0f1170142804150926820080403607080030040082201d04111001e06030690703402c1003002d020b22410388080400202c001024007158500805003504040229020680705e240da1141c40c4582b60400e100094a003084002040b021194425490301e410b1203c600303515201e802c101c540c80144a01600c1034000556502c040c1e103421003200c14000c80c800050150349501c40300c0b01c4010759a08007841c060403082000540303043c400d002950040041a072081c7c9002d9842041001070741114200b42da115000480d1030400500540c000c00c001e00304000a0003c918100350054100c8000070100b4140e642490708452079a40d100014a041d41c2c1d1011107103441540c400e020900400b04500c0140041c8140143d551140c1b2920040d0b60141c036080c0104d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 597984226 1250 597982976 597982993
    0x1b1b020a0e0f100b040e0406090c05090403051804020901320403060506030c040902091303120911041109060a120b090f1501021506060c010f110d0605041b080a09050106060f02 77
    0x1540d5403840340b1306c250b202d80c0d41c0071404100005c01a030403180365140100214100300b0b445400207800110300b580c3c104c0c0420000204142a80410701d0b5080a0000840e01141014010340000c1d000031020fa601e01d955030170310504810f642e07070620f0360301401c00700d803805d06501c23192079151120040c8400d0b6090351003031284010a20340c910303243c000e4440741a030103010100252210001d542c00c10340e00342c0c0c00300c050008261b0100620007d5103e1040824000c140c4d0802480140e010f00c41103552141407500070f030b401007142118644071401103d001c20701600d81520751980c001c606500500b0782a802990040c0d001080c021640400356a0f0782c0035821000d504803503220341000582c0c1e2800014107141c0d00405040008800d882c00c0800703040074082c20381c00801c00020600e0200c088a070644100c0a002d8004694003403c0b8000340720300809450300f074074100308002204103c3c4105c0b5044103c1030f02003000803800600008001e400c03510205500030024004a51604800361110f0040041e0100602c00c8261 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 597985476 1250 597984226 597984239
    0x709080d02010606110d090e070c0501020706050f0f091b010e0a0e01081509070605030a0b0d1b0b030c09090c130f0e0915010312052a011b1b020a0e0f10 67
    0x406c03031100403039900e0b203001e4a07252014038100c4260050002040c44401c98007803010403000c0c00140301580c03081e10b00203103619100c0303501e650507480034000c0c0c0707039440d440d40c20805210b4000a20100101d00740038034003c11010500102c5580c100050344503006020300100043d500d4501200c541620510001d07101c1c4034500c0d03030200705402c0003140c1620441c0e0111004102e214012802580c000003140d81c0425480002004558400020b00e412181d0416007a210041c0c10341c5000048042c03c1402401480c50500c0e01d10b0480502074144500d1103030101c0c6000c960228034080071144000780d0b080320443d0361965000449402c0d826403203041520100180055412280468802012103000c2a4044240d0031915074400c036a0748240c80000380181003103d1180c6240200c2156003044007109001c1014120303080d0a820f40e45600010700700142c2c0c280a0f0030b8110b4200603003548182e00300308801d2145a07540002003001c011a0f0194103005c1d8040240620404144202c901c036084041c5400c080668441 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 597986726 1250 597985476 597985483
    0xf030708070209040f0f11090105120a121107030302010204140a0e1302150f0405100c020102250b030906090f240903070203010c120510061202030709080d0201060611 73
    0x580050030184200081c4005281501185410034001d4079441200882c81c1c2c3d60440d020315004c03041e10062004a07081c68185420281103016140c1561891450000700c5c00309692100c05c0800201000c0442070000b4065200e1980090700d80c07038102c1155101c9a5170b040c040c0c003d5000c1c2c00703010200350013202428aa802d10210040c00c0b40d0926448642c1c4e0796501d08569410500411300700d92140400d1034400b042c0c2e06410103440300d8034400401c1a0f6070392524042140c80e00061011074103000303400c800c40c3c02607038002c210480d00d00c0032400707640c22612a1112044c15803959400c0304181d0000070050003502c410005142d442030704000200c03401030091348180e41d903800c65109802e518100c0b21003000d178102d1400b80ca998000314140300310b0381890800d60000b429265200f054030000340e00075100c601d8244041c02a542c00c0001d8550102c240380c14000d00402c20b1080e4040c02e03009540000c04103c0e030718810416103004248060548c0e40540803810003c0c0030708014401e05001692510700e2940d24480032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 597987976 1250 597986726 597986737
    0x702011e09050c060a120612231e0708060a05060f062104030c030f03200705010e0709090b1f210f03120c0801050a0302010309020a0801022805090f010302031f090204080f03 76
    0x209d501080000307695a0b0408410804105c5e030060300640b0b441150118105100341c4040d589180034110b01d500346402c1c0f81c03811030020b001160280c1820700740b10301500c4000c10843e882d80140c5490f0354a403d0541441d000014140d03c016052903550100000c0c90b50042450a05604c20764690181448114049050b03c49035513110011340e080031b48008a2410b000000c02c032a07445100042800d010710740b280350508620341c5c8407000f0703035864001d403200300301d0441511940090700b00203d210041100600f0142c1880714080c0d140178041c3c007502c42c5000049040d04030040c41e1b001c408403035401006d140003080000d001480722411404c010307511507494010480b0341e040e00e001038407a0041c01d107980c00440240081d0340d400c0e81c0042c042c40c00455030f07040a0004101040c400c182d054402c502000341e8460004005000d4000c01c042800300c16019038404030301c1c0c401d0034024603000d6140d4640d14400c52075080715103c8181c108504100010700c4110603005082103410700c1d0252000110720a17559a00c1c0c1c03041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 597989226 1250 597987976 597987983
    0x70309090506030717010c0908120a05071a04060b09070509011d060408030f0c0d050c06131106041410030507022104050607060902090702011e09050c060a120612 71
    0x19000d000300a15a88020342c002402801c40b10600c0d80c840f1a00c40d041380a0190321041c1c4d44400000c80b403a504000790100030f0004c100200740850740c1d0800d442c610300460f000c1d04204800000c0400501c082c84540c40c01070f042069a5001d9400c0c00d1402d03c009080d6048250f005052180c00030b203410b0300407819580c00b4801078403440c043c4224684460f602c00c10140501d68003007814480880c030441d003007028006440c1c1c0414520703511485031103403a2404d08044045001c00104002a005404012030850340190300113400d03d89246080c0741080025003c40149a04080003150002d441c5000740d00f518590750046e15205800a4104400c905541007180c400c80035030312021888114904551003074000c12104038046003002d40700c600240301c50740200000c3c7c800302d8682604205600d82140741e2170300403107240000c01602e50b205013080030500c9d03094030000c030309035a0b140244203022040c81035400703010000b00140d507281d16041c00a03100c694842103456600749001000302d443d450403c0780c0744607240c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 597990476 1250 597989226 597989237
    0x51b0c07090203040614040c0e0603060c04360b040e010903080414030405091501021027020301110d05090607020f120c0a050a0b151507024506060703 66
    0x10499403038040d5201600841e00140e44000c0311940c0440c40300c22a0050b44940030205178235103041c9417260380041c040d1441c3d220350808828002102c6031203080791b040382c0d0b14082c1c4c9100110650100400021000503170b0600d601000c4040c0c03031081c403d502c4a220403108a80410206410384609800c0321511480200400c5000f4003140124003606101400c144010040340d01e81600d800100c0c09400c03003174429a002e0986200c03481d582e5a0107100328040701240050401c45001c1803516284c81101d0600d443d1410a581c10b607060035501c00b074110440319015034018030740d59196402c241005000c110f4200a407401501c0c00f10b41454030102d0758402e5001540020718001200b1b0840d25400e41c80000c0d00e14a510a9480c2900000d8080c0121002039000355044052490001401c40c0c4586030300b910341e44174842c07140342d6818000c40007043e01c8503d50140e8003070845103c01038078042500b0f101445014400c03403004d801910142c000c10b110f007030895808281030780c0d501d56800f80031541c0505030008000c900d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 597991726 1250 597990476 597990479
    0x30e0c0402090a080d031b050a17060a03050f07030c120804050108060a15110c01093506130515040f1103010b1302070506060901081f0b060a0201051b0c07 68
    0x54181c0150041d918002c0207518140c0d40c03000c03d246024400251840800d440b80745000450b1506c0400030403054050a00310304e01050070500501d50841e185451600c0f200042c04120b154540f0032000d00a19070200442e500c001420170083ea40e40242e12080b6141a40f044001c20301401d066003032006590303c604410705103800c1000644403958000d1145070030102265000520700f1101c42c2c0ca80714400b00361600390400300d00c01c601c182450740d41c0900d5410b020215500f0044003e806900d4512101080704940014185200101d03800d00b001c0640e400e03500c0b43d60180560108180310440d02035203e08101c48001080780c0014542020407507015007030800e203100c1d030004145e21589400c0d101c64000c1c00000c1c00040740001815001c05003200304400c2d64041450300400104121a80d0403400c00c44441d50690324121580d99a800c42403032440345040354a0040620b44a030b030b041301e500001e009100d5900e40750384040080c0200000c8a2101a000c40c01c40755021004543d82100d1266054401801045 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 597992976 1250 597991726 597991729
    0x90914010e0d11011103040803100b19030906020409150801050708150d020406090606031a060301030b04020616020d150c0e0102030d1127032802040c050904141006030e0c 75
    0x6443c1010148495500c0310718410b4410b4a19004603c90b51044003800d0f01e03428000081e192201143e0031240030064100400c060301d000245c1c0c5902030350b00b079142c04940c441036845c00001a000319801140040e0030120b80e1000740b0b031000070704800c1d2140d401c0200110364815000b00c0741c4a605403009155000d8486905100b8100000c03440e00b400d001500214400d80e54020903800c4600340da1160f000203540d03911a8030040c012080294158108650203415541580c440b45024100640b00038400c3c0000201810142080d002c1d10301d80b04e8005000700d14030212814852110a240e841a640c51860108021040d03401201419000c40b0182e000f1801d1040244a1a000f4188a4461000000c0921103e801d440030b210b1445804030100b00f151003a004407000380b52400c401c403c0710485820200180000382d07142e95002142ea40c2d012900821180100f02007a031b8503100d81501c1580050030050188032046142014038001d1800007410070b00d456a0310808ca0032030f01c1318080d0b01050f810034102c1c3c0209 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 597994226 1250 597992976 597992987
    0xb1012080304140d09090b030a0b150d0c03050d1b0b0c030910020d060e06010815100507060903090509070207050108010b03101707090b010e0904060c02010e0304090914010e0d 77
    0x410f2041d000074100021a003003440c42c02420681660003c4c4210a00340081403a0b8001d1a8a402c000c1c0c0040c40d03a000ca41d65020000d0703100501080007000d00340c0b0303241210740e1200c0c1031a0300c1982100d002c103081d0361a400d089803103204100c05400880d030282e80c5134528580c0c00301840550782d0400c0f903a078415150345856011992001c2d00050b603d100d041400c041c94201c0d84020710714120940000030f1018600046101c8042c0000c0203941840201c1c001c110115110380d58520300c01504441d5101c4d5444000e42c10b8802d40110f94010700446d01d070004d10300070150004518001d54a040f110681c00b41d41310f00040781d950f01940109800250000010050440d101c1c1c061600002545109180307103440d04a9241501aa00d6102600e43e001031002c010041a81c400c48008030402c0c40e0602c0c1c5806003c0228507401409000208010703039400207050483c0c802e6000c041e10362804800e69642d95512200754000e06103144c2d0a5450740c0300c22845a10030700781481410782c0620700398090302c801000c0e12801c0c1ca4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 597995476 1250 597994226 597994231
    0x9030901080406022b05090102190e0d060c21020f0706151d19020f07240e0a1103010507020d0f020c092404090302211207030204030b10120803 63
    0xa49503000c0c0498050700c200c0580c0d0071a01074040680205c00801042d1841c107464001d088080c059104001041402050341c0000b41d04510600305070078a80100303800318a01d6108500090035440c6801c1ca60306025a200910a04003e131282c01c10213012038040c91042244a00281c48440800804c540c3c4005041070300f0807811014066140d00710140c0d5205080302e540001c8001e440000724400400402d69851100d944074400413001c00c6080001e0780314102c40780d11801502401000f41d50a545104100307483e84000c017a10918000c1c00341c00800d28210307a6420051f1000c440104200c00c42c0070450805100b4640324444642c001c107808070711180c056131817030224801681140900380d1010f4040d11480001400b0b5950401901943d1000c8403a200384403051011461095041000c80d602081d030001d0018240f50740c5611b0b10340180701d10101c00f03a0521900b00146000c941c81401c114031960168081c0c42200d014035040c0f082079030740d50845074140040340103002d420102c02000301c01060a101c007455 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 597996726 1250 597995476 597995483
    0x604090f0e03030106020604020111010501540606030902150714011109100f02070e0916090902010201060506120412200c0a1211060703030222031a090309010804 71
    0x450744180304889086a00981010015a0243c0d0038081156070100c00000c45c1c0300d07050000c10055041c0f00e14110210f40c038000382e0a61070031054495246021034050905410105031429810280040209221401c5040c4032071105103411000a8401d000c1c0c054403005503030003005501d52646404c2c03011010307040420155648148a44005e100400074425011410010341351280c446002008200c0780c903004044460070084080a401401500005c80c0e5090f11102541d481076580c0d0403106030b250050144540511410356000052040510340c0008600c5000381d009020158407403043c00102d2151904c40c8040e0741441e0300080104c0d01c0b80c1c80ca46500b881c00d01c2c000c2c1e40645030180b6020445000c80788800304ac1c1212a4403030b0585450900d0100501c100c078030700c03458604a070300c0345140c00c0000744240340150340026803403080620950441340d142c5c88151240c12540b03141b4030700c02e6140341280801c41d44d40d08065407041002c01c1c00a106441402c0840080d0700d8240c800d00115641e081c00b0304203c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 597997976 1250 597996726 597996731
    0x60c0e03060a0906020715020738060102210d0c1b080f0702060c01052a090906030c060c060708060a0e070318021e1801050d020108190c050903100b0604090f 69
    0x1b02c00081818a1480103440040c0d0050707221021401c08181002424524207010200781c40c03000b41c01584540600e0900d400c05001e00015690040140e042c8070b684160340303c22389110b9640e910000c0d8403002030074456240d8842013040c05140d80040e5294101000700c0740328080c1031012000000c00c10f800902c0020305240310b482c14180c06030b0118040c1d0b040360140e10143c1e51503000304241600c4101e8599850074180141c44a002222102c081240c0f094002d05130180900300005041c98074108603d0320a00006010749a4409841c00e40d1030300c50b507040c1e034501b001544c8036010503030503d099142078048e10040201555552a010016030040c42c1000b615451100703454002c00260781d0319603d480451509900110381041090300704414070090b200762520f180210001405152144880000740c40da0a003082c05203511085d04500e0ba8552002401c03048a06000715200c0c00c03a4403074060001800113804690710100d414070030701c0c240c400d980c8074990000e10030b002c20421144642c00c01c3c3c034001c1008000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 597999226 1250 597997976 597997987
    0x1206020c0106120302150c03061302040308070503031b03010312051c060b0a03140f0103020922050c09010522050a0b1315081f1125060c0e03060a090602 67
    0x100c40c00e41d40940c0c05040380700e01001e01e03001490780520014030150b400e88003100561600400c240c100e4000a000c003806880280d00c0001c800d50568129009103801c482220385544492403c0d0b5500e40c0201c0b44052800c80b00107100800401010503a4144c076800b008842c03000250640840e9140c203c0421200103807154108941a011284a85400b6103c2d901010b5a1080c2404014080d21422115054401c0c801c004000c4c006030242c205506680e811603040b0442d449400032003507a0036441581c4c07580955540c40e0081000000100d0703003000e80e825510741803580e90354810030000d060651a441583c0840071008003041803160311466004000b8400050508849008182132203411500340c24800c0d41e441500151070794211601005100000042070159003041303d00c03d40c1c218595101c01c00070349645035080d0150303042054484510140408a80d03000c02c2d03803148081c00982403070549036036203000815241544501654026004003400808481d1a010350403c02013011280580300b01740e00703008 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 598000476 1250 597999226 597999247
    0x18180e0708100f0603020d0c140111070302042d0501150813110a08010207050c132d020d0f0f0e1c0c1a01060c1202030304020a090b0a03050f0f0705100801120602 71
    0x71845951f42c02440600c84090926200601079420503004506111080f401148121030000b103410030b60340d0688000c02e24605004407011008065030b0304000701c104030340d42e182d072a022540c4150304a80c000d0786258030428078000255011903084d1003001030380700744103d03900c0401c5041007140c5814070080c103030500b07c0d0795440c5034500f2600034403000c40f1305030010030903110315180810807040b03681e00801e000c000301107905505100c202d004480d0100b60202584820018100940c1517030780c0f0034007030700341805044050b030107180090500600c404049494003e40d500085c50028007113070324050f94881c04174801c28205040d03850400c1032600722106d42a11a58107160a4807043c01070080400d516001010383d900d181802501150005107400c65009004020240e554001c3c20400c4410403c80002d4145444020a1465419800c0581180704140d8a4083c002c80010402810080340d0140d030001d0b0344a404110138242400039040004444200502c01044200f0b29079542510421f001441c0000303001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 598001726 1250 598000476 598000489
    0x1612090305100603050105090d05040e0c070c1d070e062718070f02030a02150c0918060f040b18060102190b0f181c18180e0708100f060302 61
    0x2000c07602c4580c03180400c00410200340140f9400803a1040a049031315924000100540900e11492070116440d20100e006420880c00b10b9045035009540c8150260704d50f110700c000040f110303c1d00103907050000001407441c2c0c82070400018403000102440d18210582c2402c4030201c1c0328075200c56002c02e004401080315a030f450300c56a0b0221052048810a06d0583c5010b4400e1005c0d07144107003950010007482c0314059010500075500c80c0b175006054010744a03440c00350000c3c015914500c1e00804e1307441c41d00507a05074586080388540c0086601e40300d0841d18400340815a0780000c01550400c101c68002854076504d8241d842d071221040c0f0403184415105990102d40d42140c0c14152001d030343c0b0209102016228600d0300703500522103000100d0b40700200b149260303110750320310f11016112200d00140d01644e210f0098403442100b540f8040e40f1b00350b280c04d100003400a8030480040300b0303442c0030b20199801d070010904200311520369000d00185004800b40b03102a000031207001b42c98603610040400103035a4407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 598002976 1250 598001726 598001743
    0x1509060913060311101205040c09090c0515210a090803010f050103050a0b100c0303060b0d06090b0d0203150a1407030b040b09060d0311010b040501060f02010b061612090305 76
    0x4401080c000d00c0e6003006848103a5624006000e2003404003101105504445080421b1001007400a595629424030207d06c4410750401c0400340d050440c0318040c850a440e8807402e480003124081001102c040001e6010300c10f21000d462548121034000d0350b1207070302d2001150f210000d43d50209082503540e88030a2613900907080ba0180b81c42d04c15080c880c95070b0500c501903000c06642001c01401c68040009000d00c0181c020707690402c00b0800032a0100752003500301340002c28400c41043c0c1c075280c50700e03100406008580104503070b5071324041c4035500c0e0707182c915452880d564015019003842c01c080fa803240440703540103000d00700d656164280301003140204012540704010725600010040d13030206c03c000607664442951442004071106000c0789580742040c0f910500d9050424103980704082c1d00f41800340c0401040d25a01610f800c0c00060a1a084481085420242c0d070003000f0000b000c03070400c0800d000307884900d43c43c0d01c100c01d1002e0000b180d25500c00381450b02030414140950780c0743d43d05880c1c945075 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 598004226 1250 598002976 598003009
    0xa23091503010303020606090402060d09020d020a150e03031e0d060806010902040e060315070c0309090924061401030c050706050c090316051f0c14031801080615090609 74
    0x400604d907041c0031494110101301c81c0c07030b4910b08040e00000c0c0c1900484100b40019a642c4514904554030010145166507000d03001040c0c41340e0b9190401b03501c8108000000215034144000b840c41d18010007180c0a0210350031600c00038203405280115250085a1400c907285e65401011549402c1080054005d00c6200340c0941c0d60703030a201c5090354465014280380c0c0a5800000c0d00c0807072907030b0341044a80c420b0b0305144c002106516810121120b4002d90302a0480e00e203041031072001d201c00c20031280e00f0040507204003a031690401185000721202c07445101210300c8110800e41c1a98420303000b410a1a07075900e005803c1c915141c4030340080390016101400c11010024112200d801c090088400001203ea00791100f14600808501000d0035480704a01c0c0482d030303111800c5aa4094120307c1d255540054482e000521205182c5590390312003d0040b0464038a007404211030340c454006684250000b030840c01c99074444882e09006908040003407640401c050280610607250809020890547c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 598005476 1250 598004226 598004269
    0x709051009111e09010c0b040b04060b01020d020607050f0415030c020708010c0e0402130806040809011d1c060e0d051209010204030b150411120609010b0a2309 70
    0x2a00752500121200d50702c0d50400610140b2594400d0400200c00406450310f554000d5aa41e61010040f5203a040c03401006140269001c2480207205c0b15000316807085102d840d08004070003000005985ea000710b2100f800040c2d03c2140010001071042d07010b0607061006403042420b281c3c0f140d40352190114407958180c0000d64a0f200204401d50401c1441c0003400d00500070002040c290780020300000012612901903034000510f50b00303007a500c1c00074400070040705064400c1401c25142403a0140e001fa00d500d80041c2c0304401c0300004070040075401c01d10040017048036056201907000d0b0310304a680201c0030780d5081c1d950320160342130103c18030500c15807503820b0741d8569503800e490b03040b0701400d04064401a41c984c41440300b40001010480c2c866000108100d000c4800400b05000a02920241500d5540c0800100701c2c0a12400c800e100c00f8010384d000c64603410b10307a8035212401d8080c0212000480062800f80240546064018000c078028404520051404c041c240c0440c1811114030300d08544840d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 598006726 1250 598005476 598005479
    0x3270a12051203070509040902060c060f0109060503010c120f0b09010b04030201030e0111031305070b040e04111e0d03170c03040b1b0901110309090903030a060506210907090510 78
    0x5050012071241d00308060b009081d800d00b410300401c58000c0c100e03a58000c5603a15840019507030303a8010764210902c50320031134081d45400c03002c2e070079142400e2003802d18041c1415008034503403406001c2d4580105050741c070301c0c00e28001c0c1060303103014148003000d400f10b840d81e80c1d10401860300c0761000740b8042c201500015a40e9865880010101c41d16101600100d034500001104001c0c003420869400524850305000050348a0404500f408060741c400d0204a000260001da054041000e851046000f4411050200711540a2100c030040c9043c130a00c102d805001c2c000701e00c0c9403e00d00449428000d00e0141e01e084400001c18440c20001d40e060454040040100010000381e0810349501c0407a12100000b00b240030150100c0d40c2c05180c481078180a61403000b204040000c02c161580542d00900c103050303a04200c081c4a850742c6c01a6a0407a509041c44008038050401b4004c03510510103050400e00c845001e22031030441404003506d148800d00801400180c14240c6010b0107000e5400c1718548034046 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 598007976 1250 598006726 598006733
    0xf050d0c020c01110304031e05030c01140109111602090a02070b0c0306041b0509130f0f0905060907060e04020702030a0f0b0f0115051b240906070e0303270a12 70
    0x3422000303c903100d9600400c811f00014241003401d0103804031000400b84848813503c2d1060560203034900c040d205618014030000002c011710700c001d049443c075110800040000840d80a0a03104480ca480024440c05c3c2d006401404d10001c480c0d44003078040ca0050a1208075600e07001b039400d00380d03480b074007402003c006c0c03040314500b500c81e00301c41c85000403020b010046044405800d070300901c40700e83c0c800c5260342043d00038034185401c00d40500070751030820040e115823814144000c00e08090203440c184143d0000400b084000a512000c1d28100c2d201c030350343c10042d9010040694000001240c16016440b00040084c00c40d21000240c50301c242401e880070f1a140d00d92140d000e105900804010050000024400e90041d080b112071880c030004440203041d054907607a107406485501e046560450f681d0b0071800c1e510440c06140940d80142c00c0e15030076181c2140c1203a11052202c1d03490707032541041021800c80988810b600c003800c04102c40f115001d24402c00000e01c0c0c65101e80c040300d40c11000e4a00f19042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 598009226 1250 598007976 598007987
    0x403060b091303080a06051f09090b0a0b1e0703090e0a0203070c03051e040b0408070e04030e09040312020d020405030f0607021009030c0c030318090b100f050d0c020c01 74
    0x252600761081126803a00c100c1e0030741c429594074400383c00d024000010078650303481500684050480a0b0581c0d00e40c20780c90320f070220710752038000d10300300000e0307408802003031040c254000d40400000050044440301d04200929500341c0c0002c0480108100600c120946201000301801c0524080d0700c8800f031141c41c0101086900301d0060219901c4c2d80b040040003801500000c24041903909807511540b0380c05081c154021031405200b42c0c114054001c54001041c603001c00c01801510141c10a0703441e855134a80f4600d22210b0309840c001c02203100403c10040d1750034034481540e40300780240b401c040c0c00d42800d101030040703a0010740010b4000b900080c0070310441c00c08010700d065540020006010750b10b40000001d40780d0580810720b4990301d442d595202c042c140b19000d422a03181c0c02c134940f501410354915005e0500280883c8510020b030b01e05800041542d0300340b04007584504c0c0600502030340c1187c04422560882422078400500a00b0704c007108204c106445031001c0c0c40314a4000b0708440f190301002610307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 598010476 1250 598009226 598009241
    0xb15061b061603181419060b040e06010e2a0406091431060911090109080708281401050613090f14030702090709031502040305031204060f020708040306 67
    0x51608140344c1e081c1852180d50765080302074120764450014181d01450700c0c20704030100001044642c00300141410300245034020880c01408490401800300b1801843d500c900013407040401007201440000e40261202d002e0441c3c441d480141c2c041c50458211a01070a42c0007074218400003000c0782c1050291302d02c0684c2d0245188011950504c0c04407032640000c070006103445030825200300c481418130030340d0403542028000e080c00410a0217400c0101a0310152500710000050004100300c400180b90340c0d01089003025a00740c1c1c800342042090403c0031250701c3c02c1c51950500c2d1040344c00d001201051141038500080c0d0752240010640d400e001c810418408109150f0070b01c25840c040e900300002d001c103404117040c0b80e4030030740b1a0301d1003982050752402c6005854000c0e401c14221002c1003e0303650311944d01420340b881456804500c402c026011400c90042d40001070007a881004654407200342e500b4500d901038031801e00850711840142060042c0e03048003408850058010a040c01000303c58000c805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 598011726 1250 598010476 598010521
    0x1009060b03130201031a04110c07150c060c09030f050105090c0102010e0d030b061324020a122d0e03190809010c080d0c05120a090b15061b06 62
    0x3070650504100481ca0860b00100c002d0525030340e10128000c80c44000c8084d034a000703001300200180c2c411042c4c420215400429001c03914041e5a001244403d0f01a1200790345131001d039513026030380345070342d40d1200102036091140c0240402c06800200144001c050b0300911486640041110b007880c00e04c1030f281130400f1300e14a0559040010b1700a0b0b070300c00003810240c00501444c01040141403040410f20a11640c030040b800c1c540180340104040448c00f02200c19001c01b40302d64028549080070483e11203407442c3c07004090710601402c91340d043c0c2c4140c40e1001002002099200c183d401c0b082041c0c0300908140d0000040380000702184808d2405110b55002818482c60031607004641d555481400d21038800c00d00d06001403039849200348800302e0242c4107485181e40003001810761241016040e600701d0741c402134500d60300400040c0c2000d881d01074031043c2c0780d012503011025141c01c9110305041d80262a10358001c0e00c14030102c4500c820a0304030ba882c103060600903000c14100220003035081d000700c07540b08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 598012976 1250 598011726 598011749
    0xa0e0a05030d1d03030712080a02041a07030314070908010e060f0f0714040306050604050606210603030c060f010e0115091a09040203100f05030c0d02040902060909100906 75
    0x2004107403008500307020601990b01d40603e40110411000c0034480041c1d00c900d4051001241420800c4050305868a4000d100e442d0200c141e6104042c100c207901ca940103600c602d020441140c0307061001a400343c46454070074180400c1250040b000c0c0b11200d00b00300d4906e800a007958404000a0a0a11403205000740020240c0000d00d0080045130141d9406489110b00d201c101d000141c505108400300801c44041c412050f544c0e42d92810080054841507582a1040c1e2409000c9401c42c50103a081f9a40100200501c8019a2402c1c8070505c0324a002054203405000410a0001016042c0459441241012100e00255041105415032004160007405c107030402e0400c10441039802070400401c40701c1c0b142030082c108034840c0418103a070164000d000d80040c008005e003e41c8400c04002d00702138640d14001d82108960f9030b420580d455142c11603c94022507003140c91409400c1a0f00320004a5002620300362030525401e0114692807412159100200074049041c450801507014200040c0381e1103202 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 598014226 1250 598012976 598012979
    0xd0b040b240711060f0c0d0e030a2d06020d050703111801090504050403120b03011505130b06031305160302010e06090102070f15180311190e07050a0e0a 67
    0x10000e1401612800101c59800314812041103071062000c1e40030781020382555141c1c0022020b584a40c1c0021060180500841103406d1032540b01d0b80340c2103d02d00d00200244140a1749071622084010560001042da90450003410825843c0c0e00004500c58412000140c0c2c811000e1880300c112280a044001014140314603114100e4244050320b008810b44032241c141c43c2d00ea400143d8400c9015485650490b0400d0100024035070000c48a030b640741035500d018042c506a1500301400c85041084100c00c1c0380c101c21041c00076083c5040902141c40b42d400c400515800080001042c542045803001d1040241041c1c03201000400e0242c40003542160310044061811540064405550781450600035000031903801d0741d584c42000550001c1400e1921210019100d100c03510540036800828004034449070301414078050003594040849811015081c4407205420401038005035082646602c41c40c031071004038a2003003122a0601030910b5448103640c0311424207024103a84802c5105910031072513401e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 598015476 1250 598014226 598014259
    0x100608100608241f0201180201090611030412350403020f011707020f0f030c0607030506061b0c090108010902010f0f050d1503021908031903060305030d0b040b 70
    0xb06590000159155504041030103029100441502c40e10503034045400c4019021000c49040060010019503009102d01e80c0f6040120b0740c06811130301e00900240d58807804220b014410524010f0b00302c0800252840d0940c2c8518428215511030815280350201110752203102090804890040d007204036800c90408e84900100c2c45e80c015440040e0046a0f40200526180e05c602c071841e400301c1ca1642159110305248100943e520840039848041e4420ba4500080b2000008162200c2c0642040103248540e07a50004802508000d00780075000041030018000320b5403198003064104400000030001d40c07445200704000b4070320683c484551645404070440c0540da201c01c174901d41c04424100003840c0144200708032002d21071621000c0c0103c0c900458041f541c00041081401c490080f6050002c65000c422001c0c01d5241510803441c03d0b900c200044e280201d42c1140340b9060744454100000d445d03580f0b460345800d66201400301040203580b103900c0d40c06403400740b140060310082502c043c5008040c086 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 598016726 1250 598015476 598015487
    0x602031f230a03210809120915090d26180f0f04090312050603070e070c03090e070206040201020f190303090606080d080901200d02030414061006081006 67
    0x203808441d0030914081c50303201e6840e14000030005583c00600c00c3c489200d01c0003450f41c4029410b245070006915040891018500002ca140369000c615030340e6441c2c4001c0c6003c1080c042003810030030b08601c07070a001c952269554182e29030b91040c010019500000c07402003010340310401910803a0510041803000c0039071401d11217454882044203651290003458a000090025400500c9596216082c641854101a4401010020014994028013050311414200f680b17071062802244881c01110001a1a0a200c0c90f400180b0341e01078100342d290151280c080d0841c0c050115070720005a4040c005110440d64100203821001003600b01800d094285c1844506098800c4800074081503150079841c002d100042e40402c0080c43d50108543c4c242014000141000100316103a0419520306142ba0f0340001c0c004101c0515219008109854225981521002508090000d46102c02103161242c02c0c19410452540111104d6105900903440c0c10002080c0c59801401003c1d07a0351410001c0180e1500075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 598017976 1250 598016726 598016759
    0x51503071206090e0a020301060905040f02011b06060f1508160509030c03070801290607230706020f07060e0306060607030c060903080402040f05060d02040f06030506040602031f 78
    0x146060000540c0358509031002d01103a8100b41161494030307000d881d1107071001a0b841c1250748203500038484a076846198800701c0384100d4026003000703110005840190711511703081d01c03021088400020352070301c2c81e00c03210116507083e084107544c180c0c0b103202444007202c50545c215801000b860310741c070f0700c2c070700404241c90003080d214841081c4075003c01e804004d40d43c10305ca80700d0091800b50440b00c0895403044111701806035035a131a1030800c1c01c0104040e80340007003c214004042d0103000c080c90000141e61b500070100401c200c44420481484204030941c1c41400290010003096004040d00c00740f0320152030402e051a070000c01400001c441c0d41c41e0644000c01d800794043e1049806030307100e882604060382c406090f044010140c601e00461203041540018816001d64001c0e2010070098040790303107020844205845443d8460704140c0c1c1400145440d4200d64032092080c08003040f196039a41d80c051a100d030549084410640102c00c1002041541850511942035140c008100e5413410044103401240c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 598019226 1250 598017976 598017991
    0x109030e040b0321090f03030a0c020d080c0d021e07030f021507080c070914010303020303061e0a03081b0a0209070804080909070e0a05010e21100e0a050601051503 72
    0x5941c11805660340600c03003842c0c80814910304d0b590158904030001070075030008181500c19010080340340e6003401d002054602c0f6200e1510307112540295078003042040200c0d6202188c02c014102301c080700e080c8052040540c0c100c1960000c04d01e0101d4402035080e145080c6042480c82d904c0f6000400219016000300300816070107075072074000a0a448030001c4188500b00000e013400c0400107000c01c1d484c42c0016250b00329031010301d00300159103d400c0f80c02c441c02403e00c8041c00503171051000c40c44a182160103003030301c40402c08220340206a2000407c00f090156030042d42e0342200844c03480320002c00e0700c001041401e490000f600066a055002401c00c540203041c400c05c12440800050400042100704d540313007840102100001d00c4d0018000f001041708078070040c080d403001d040004295001d14101d01d0000001043c2d804c0d861080d01406800c600c103014124514441c0321080c8641900a10030110326404c1e03000540000503241c01d250303140290690000340520300d120003241c092940c6005603070300a0700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 598020476 1250 598019226 598019231
    0x1080c09040b0d020a0e010e0c040f1404140a021c020f040e040503071a01050315060303040603020d0f110702030d022a040b032b02030304050304051c060218040501080109030e04 78
    0x10480085043c240d04410f00940110032203802040d1504004809412640e40b549002c07110740d60f10b80811486c0c003407403099400c04240c3e546d0512680c0c40d0072605000d100b501400010b60100d1074a403802c02e0a800b56140a81305074006183d0460700061001007200840c1e0101c03d628015009410400c40e100d81e10505040401450100f01040340600440300f03410b400c440700004101d030603001210109000e01c100781c0329104980c041c0351681171201c006e0b0b206403001000b42d42054501030301980030354071051400074a15030314500312010303074079600c191000c51810764402034a070041071043c1454581094030311000d660001c1000301411040584105100301c5000705100d403d0542408540900010705001c0d9050280c147c04074100e0610007110384020003212400201c032408010140e0310381c4401c2d00d000e23003250400c0109210600b030114861041e01e40b1401c03c401c0001850302c40c08100d800c030003034036400c0e0a250f603003038a014a000e01030309025102e84c0c0300803c60a1010754001d0300c40c4d55440c40c00d03270042c0d4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 598021582 1106 598020476 598020491
    0x4170109020a170a060618110f030a0f06090f0e0607090503030909071b050a020a0f050117190207110406060c0c270908070302070501080c0904 63
    0x640141c240c10205040031400355151640341c036030f0b1075607209440e1408001005882010010105120358206041031002200144e82c06500c0103103048005000c00b0408840541c11680c2106910200140848a1040002c094526940101001442c0052020b942181c50f085101254075001c180e9071580e45512094603541c00c68001e080d0558010b100e02e0f60301d030400c001c455070421300b02c9c104607240940011003d040e0380080c0e4000c1754180c120b0002c03541141852000c10000d07195075403c082c1d07210f0802000806005078001c000c4d003800758650110f0f01da079134012202c2d6100c48502e43d00b5036a82c1e95600b0300d45151410b540241e40601e180100000d1410b10035041507203059030110302411854a005130700300b802d0310304800c0c01060341c000349080304030308000d0302c0b900c8000c6205800301a101d503210708002e410311910358045070602001c0d80820400001407400c5520354142150001020b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 597841726 598021582 := by
  have h0 := BRFrame.cov_init 597841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 597841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 597841726 ≤ n) (h2 : n < 598021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
