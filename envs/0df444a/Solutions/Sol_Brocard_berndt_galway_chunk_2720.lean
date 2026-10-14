-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2720
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:32:37.268777+00:00
-- url     : https://prove2.me/submissions/497f1566-8f55-4007-91ba-64906c05d63d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 489028776 ≤ n < 489208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 489030026 1250 489028776 489028831
    0x12070302150d0f06060c060f15150e04020703050702090a15030b010503060f060901060c0516090501080d0519050306010c0b090123040f1b0b0409020a120c08 69
    0x51a4040c190803540c4001400403440d07604400b40c00b1020605103503800003211101e100d110700300c0701d880d601c03103083c546d554452034001d2080d070b50941d0031941c840c0ca04040001100000b0802400c2c158034161840c04040401041c0402c1c0309145032149004001c40000300784e02009031100c0940480c1c10002944650403402c0c001d101c282c540b090a210070b20400800c1c4400704084c0f40c100d680682c1518000d40d02d2070400c1d050404111002d66003c111540140301d0f00c0c1c070031842c40c0c007910b11510031150950f00114080b011801c1aa01c80f0b038000d61114014402200c0c06d100314070000d480e5080080c1000342c1c03070100c0d030209a16891503508000c40800003400c960f00c100402c003605074000c441c8003031505043e070302d1501070110b00031079400003038080010481c0c00f10102c00c01403140d50094000e0845424036515803a020a030030f80b41d84e0700f800c0198800b1408500d403400a00040510100050b0340f5003030402d0190804d8100104100b8142c60028070050b015004100c203070b0320010600c06250050b6013003544458 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 489031276 1250 489030026 489030029
    0x1404090606090504050604140f0703090219030203070b13210f0308090705060c030f0f0909090604051204140f1f030207060608060c04121e1b0b03151207 67
    0x1026414024009a160742000c0600140c034404d0f5028455507441e4403d01050381c4a4044800c00c40c504000040c0c0442c2d2148082500710804e41780c086846100e6400299101c80208020607031104049020011031a08100000042c92915001c1703007440868044214003070141d1144035003800c904008443d245e900820f012240d2a80304040c2d6401d11403a040040a1910880d001032543c071408401140780c1c07801c80c068030301d0340c120000110302d412007000f122501a0800210106000000e00020074942c1d40c1080b041d01c12000e950041c2240c0c602030401c24030b071603e0000d4102c2e03030020401c4123124101c3c074890081062a015503003912142d01c4003010442800b4450350542820b81880c034000505580b42c0c0041181034000d45060244a0710b54400f2500d40c501611186580b01c010802003041e0400224000101c0e409030402c80035004030081040700328904004201da060102544c41404541c0040c0803c01401e801c5038880d00794074000c5800c8040444a403003503072040340c51903001804a14200300d10b00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 489032526 1250 489031276 489031289
    0x140402062d03040b10080c060412020a1d1504050408160f02061306020c0a0b070b0c040519030b09010509210d1401030c0e06180a02091e030c010309050c011404 70
    0x40e0b0340d2405040c0001c100005a8104a58060391040010010400645610b0401e4003d102e14541458500f1200c6410014001240c00110300d440c00100d049100708001c00b50411452241c0e42c51a00082224041030f010199610031841c0c2414000424075503000e507908940c05004502001c1003031b0400d90161801c118000303501c00000954212122109107080040f90b41c03603021680780000d0f10040000b0043c4a006516a21106001c01004601c020b18425004a4440b0505150a49400200c1e21801001004000c0425400000c20401c5940d5100f1584640d140d8000c000d9420070140480d02d412490848200c0e808039a507400009000300011179240b80d400300d0301044080d40d9a40034110b01e0741c003440192035210919030300044800b580c294103449410300038140d0b440c82d601c03412154034852015140c40c008507403c0c0302072695911064081404034020119500351100c6003001c05203803000c01126941054244811940050301c0080c0c4804815401d00344000c4c0c5001d84c241403143c7d030140d0350100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 489033776 1250 489032526 489032617
    0xc1a04050d0302030c2b09030503120606190512060616032109060b030601080a0302070e282c19081306090e0a0c05070f03090801090b060414040206 65
    0x2c006d001e0702d044005608031103003242c003201018501040d90480381c14880540075420030407880c0d07500c2c04c8008400360702020007400c040c203000207403150400c00c1a045a484c0c0c0450030019601e815581030170103150780700b002241c030a0310f40484515025000702d20318800a06000e10004041e0203100c8032280302c8004204014200002c02c0e40303090100c0606000c02100d4080d024150004c2460701000c80e1807404182c0607001041d419203407031424401018001c0c02035038a0981d00c0c0e00c0c070182501d0384c8000b10505845400208110001f030812031100003c0050120f00000310031400f1040c50b20128041d19025001c0100e80485022414580c0482c0f1460740c0c1102c0311842e6040200380c02e9001071031401503680599009180743c2e01c0381c010f0b80807076801d04d840391f0200348207004440000c5c2520740b00c40c1c3c0c440d100340740241100d940d602c03e1609541d0307040411111600302c0c008000c8542441e203d254035202106031742007841d003050b030007244041c422800d034507448003010081005a03001c0e0884540c104580c1c1900e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 489035026 1250 489033776 489033793
    0x307090e0102040906051207060e130504050f010501050301331d1605070f0809010315170f160b0c0304050d060b011706150c010e0102030406090c1a04050d0302030c 72
    0xc0394001e600a00030f880e0b030140351800124140c1854451082000f40540040c18961300f41401a0748091400f184140c1c0a6940341a0207800c1500e8003565014503c1400144042c50841c0051400d469050704040c0c041d03850f11503400f20080b00314004400e41030700915541e0b80412020000703e0028115001102803035180c4d03960307072005056185c045106038180d2681d00007a000c109400c03509442008405080d83d10b80c02c0080c40440c64450040100400c14140002c0711803001800c1c201c58801c2e540500041c030b4a507904298246014841c90f020080c180d400703042d000501100e20071409043c1d006061850001081e84104500100100d80207070000800000000d030240c68900f014010100310540002c410300140c0c1844160444618056000288040781c80c82c1c3d868614001e0360016040701b54250f4903030100f90b100d207500380300640c001c50054801107070400c510b0400084080d042c0e40031410142840386105a02038852003590181c0f0001c803940e94400302c02c0e040c1285107016194502c0018000c4185 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 489036276 1250 489035026 489035051
    0x3010603110108130803071115273f1303060f020909061c06060b030106030608030a05030402061b06250207031502090d05060726090a02040b030709 65
    0x401c20000000b40d840030000d0365140203100e002103c220380217003c00000d00c085480039004070741c1c0b1884900c0807011154500d0320b2a0180c4a10300d000c2e11902d5003810039107080c0c40c442c0090026078446190000c0103241c3d1218412109100d5081406113544140015114000703020344011a4070703188401c4002c441d16150031986882d200e400342d00c8102d507624030f000782c481c80a280c1da009039a0800c600800685080c2d64000c20b002c40200483c51a446e0b000c0c0003400b40700020401d1050b40044c041310304285840351705044019080b07401d25002400242c2c0300b17110403400b00754001c0c2200d5116905442e01d0342c0314900016503410b03000400c00d040e40e040c0201c104004071009081400b194060705404414500c81c202c00c0c0c10b9807554114000076000e50301d030031140d803007402543e001050234540c0a04460a00c10301515690704003941a101100058156000ba1600c0d002c001410103a585030411680603605010101a03950310660340020b025035203904030455039a0342070010030002d18441c00c05201c111800403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 489037526 1250 489036276 489036293
    0x1207080c06011401210e0d08010509070302250218010b0c1605030a02150910080f01050f0d02300304030201120b0906122823071a0903010603 62
    0x55604200d210341d200000307400d03000084a026844060712804507800320081000036070070f0b2240c07000b1009502e034500c20703400d00f41c10400b40d0101412551052201d5042504102c60740001500c58010140184000584d40c0415940c503541340d41004034807a001c501900c0404c0d0002034031322002051002c075800014083c1002c81c010314088500800342c0d41114400e00c3e045501c1201d9005040c0c0544c04507401100505100a41e04545030004c64035a09152100000504004115082e07a002425141c14000001e5800040d940981411689035030343d1824003022826012404501a20443c102c0300c29910388400460051412107403a8203200e1900310744800f030b55603a0311512003240068000c0c54000c4140907240301c3c8200c66100140a2802c980710001044200c80d1030080b000380ca0f000b02c80c0c603401c4c91040c40503107100568040022011140c82e6080c00c01c1c10003a00c0540444414070802010400e00c0c0200b952419035441a8540310910f400c003002c05000e0007002455074042d842e114001c005d118003235 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 489038776 1250 489037526 489037537
    0x3010203011d10030818030a05030a020d11060c07081c090302071706012d0f09091a090c060a0309020303030f0a052202090c0d02031003060b0d0c09090203120708 71
    0x1440108120f071a5540310300759089241c4009007107007405111310201024000036200c800e130b01c0101101d015409540b07039182180d22810490300968495481c2406164224110020b064000b5018040b0392603c0d921035070b450300c10004c000f0b040d09800245a500c1800b109038440c1c041c0054001042240c5042c9400796440405000d103183c51081c0d42c2d00c819010100007280b5040c1c58508244140c9440141150744408130450681724503109081c81c04581c01010102100080c1100d05011030011018144904480000c0049201031700f00c0301e0411400d2500040c03143d001c0103050340e00c2ea07a00d007100caa0450060401d07200081d03040c0800000c0c0708100100d489001d005400c5405d040016881c1e06801440200c86c02640030034100602480348098a480780c40954008804000e16140c0740603424424100d90046805800070b01d001841481403100030320800c180800b00303079000030300d440403a25848442900c61142c03110f0651150142c6085481c207200b0317003d40e5040007001a031a08101d2602e03d45d81c0c0c100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 489040026 1250 489038776 489038819
    0x30a0b040f1401141e0f0d050d0e0a0603181103011112150103091502030403050909040f03110304140415150c030e0f0603070e0d02130b01090902070503030112110301020301 76
    0xc84580413441d2401e400402d4501021200c0001450355003c1802902c0d14a410035aa00070021480c503004075409105c4107096124681c2e81001c1043c0070410028041e0190300301354201480c01060f107484403541c001d0005c2e0b00c0d81003e541640030311301c82c0c0002c0c050980d0303120109081c00c02086180614015040d254000d001103000301480004a10044045903440f1030090700720f00e0400500402007200360300441d08030340640790241c505000c01003c28240c80043d40c08031038001d01c08020b4001e06030302011901d99011034101543c54189000005c110519500704050300c40d03551514440c804044110412005040080314455a40028040a4803240303100006401051008429401ca0314207000c00c00c1e40400020520360071034988407800c554030780309001030035000980c5240f40809607864010404010010340070218403800d08400040800043d03501c0141f5040c018407245000420200c1641c0c1075655810528924441ea8141070a000c070090b01001c1c0c00d94800800854110031011400300b20054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 489041276 1250 489040026 489040049
    0x9021c0b18070f1812140610090c03020c10141e0c091804050f190503040b07080d050a14061221070606080c0306011208030a0b040f1401 60
    0x11106001804100a0480103800a41d80c001031469000d00788441c118051464044543c0c1006011224001016001344039580006042202044000c822842040c50140b010f00660f09000d80120154240c0d8042d06c1d10300b5490300b11700e500b218865410740e0f0511240100320340e800510840c0410003044460008027441104a00042a200d0000300c101410a2039a608103250303030782c603200c0d101250498805140d000740c0c49500e040482d0321401c2c610340510301820203002d03c1109180700515005006906c031400030000d18201000c01d4020080e43e003206c0d407e19185617141d0440c901a4510320030352a408108601d88000c1c0700c0f40110b81d80c010010380b00e1100300010355407110401c00400b8002d011603141685c2c04650150090402481c0010000311040d05060410032260f40301000e40b9420f8205485c02d90114010055a1030100a1140103010388000d40b011031810351110710140c03000810480c016030700c6034426401c90315290710444c400c001e803400c10003442c3c07482d0744032900c0940c080c41a1000c080f0b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 489042526 1250 489041276 489041291
    0xe060f030604030203031311040c020114130f020907021e010f060f05130903020709020c03190504080a1403041203020a020102011a2b1b0f08070f091509021c 69
    0x40028441d40142d030540c0003141507580700002003603502900a4200c483c0c040100034400c240c0c441e402102e207014030680003c6110340742c030814040f02000c01401441d00040819401e0082102c00c0002121281c040e00e0340380080d0346960059180680640d21190024203124004d0314114041d0300c4408101c02240080c0003261756a0548401c00707c0364050140d100c2c08040011100101c031341e004041c00c80c4680141e8102554a01d1007001300d81140b166621765410004800c2038000308403050100c1d28040b414018101824035680c103584465114005006164010180c55401020000d5170001c00c44080c554040c030b205460000e456007581d2200324055820030750320070305811810703000c10612940601020134490080380d84a0301c90068018080e041849880303403501041d1000300c884608015007044510342480c00d000450000b4581c0d00c01d40403070b00400300c00d121020801926508a464407900442e050800c282110320a40c80c2e0351241c60160703c0041e91000c2903101c4264117625100700c5900700080c9 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 489043776 1250 489042526 489042529
    0x50414040e0f250b030106030902131112250f030b090106030c0305090c0f01050a0c0b0108030a0215130b06180103030206160302070c0b1b060403050711040b0d02010e0103020c070e060f 81
    0xc009000b52030b000c4e030003400140306292103603000c1512079000401c00c55040030443d40399006c071940e110520a5180c00090459680e60718072150b0358000c200d0807420114114a900e45902400c01c4840580070404511140f201ea64030940012080d10340090074900656503e21014000b81011b21101d00400e0510f00092080907010403807194282c0047c00c0031040c2c070422001101c640d4010248641849190201040440e00d201c8031103020303105181c001e603501c504245002e441c3c8104500800d0840304041c007084003001d00d4542e8044550342c00041280e035a112130001410825a0317401000f40da000f820000014182c0c0080c1640c000c8501c0044000c000c00c031180200c041e48901c9102429101501000708101801c480c014450001042c801c22405400c0d8a500750400b40d00b038405900040000c240c100600801c02c02c000c141c0c4104aa0400045183d0000300310181581b031f401a06000c0390b85414015071b4000d030115815403030090165101684c588081c9002072105540c5240600302001e03902d00d06 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 489045026 1250 489043776 489043843
    0x403030b1207151205160201050c0a0c0609080c01150e011e0e06010c0f050102070209070309121409030a0303091505041a0405070506042601020a050414040e0f 70
    0x4841c80c005031025600344061046050303030300c1c07441c84100701000c0355502011010388281e9002c0d545510744172000413440ba100070300b5140041c0203240f80c45e40400140c055503812240c1c0b20b0b00c031540a5404200f1031858100329509000302020600203508100d050035401c2c3e04806110242c441c890720404080c0d884070300780031290a540400c200d031400c211300103005c10154004015441001403401000b0300c62aa5103015800c4019001141c6507900460040110310349104a10391010a41c07404010f015007544449801e890030b0040ea400380300007035043d0751620350400c0c2107603150300024040310603400043c40c00800802c0c4407401510200c0300140181618800360052901480d00f060303100342c050550039008180780c100a8412682032252900003d5240c4486000d4001800c0301c5110044000c82c0c035000c84502660010044150f0f4410090203446039004000e0700c0030703540c410303881660711000c80c0086001003c442a0701540e501c520600319610310800070b05550300e0001e500030901c040c80c1200c925400b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 489046276 1250 489045026 489045049
    0x120f0204060e0a1401080c01030b0312190e010201051603020c0c041b0905040b0a05092e060e0a030203030d09080706020f0417030a021906092004060506070807030c08071205030403030b 81
    0x500e41c0201c691f1301f01035846070304070b4488848024140c0d0000d103031920100b00c09621170003034504c400a451807541010f50b04608440100007080c0000e101516094410710850a18a9500e070f080c5a804124007840302010090040314a4015004100210501611400f010a0b41515100140c58602d010406044c03a0250039518040644290101c0303040400304940c600c4d0061903c00100306100d882203540541c40c1504014007000800e1059050420390b000f0664650300c148940100380c0c40f401040142c40c00021100705102e40d410000c1d20503080d00e84003449200c0c010016010600201e510460404030100800454129003c40a40c10680301d01d80e0303840340211b04403c009604000904000e011414240044183c0b1481001440e410103aa40b00c140300d451903030740c00010401c025514140e041c68031070389025001c12500c1034100410b0b982e501c0c10754800d0020003020080300c0c640b05c0c41049522406e64030302e030ba0302c125581c4640d4051200140305420071601540043e0034028030b6850760034921420748 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 489047526 1250 489046276 489046289
    0x914010c080306042007030521040b15120f15010f03050c0915040507110f03040305071202040621060f02042306160b18010b010504120f0204060e0a1401 67
    0x508543d20700040000800e1045441d00c2400711241c1c550003072461031002000b1031446516296142c5c1d024a9521421007030004185520040b00c00611010510380301c00940d003d002c2c9500c0384400d2042c10080f0340790f5280100145031611444015101160700800c40c950546031403905003440c0d0b07a90f03103a00c0400741101e100c0074180b5044890038103091f007040d04066030b12401c00c040c0f402c1c030075a842d408241112000c640810004461000303880c0d400506000c02c1480344c18800003141000d045817036081d06c407a030501c20708071509061004a811526070b074000d04010420000244404034520510840e8880341200c1221400c1ca805269500740000b442a58140c500302c00c03425416010804100276144201d05403240d101000303114941d41500c080684107034103449071003220014201802101500c888800382680345074100140e040d0326980c44410780f411203001040d00d881c06080ca080c90500c02c040c1c4c002c0690810300301240800c141d0701e5045d040d80101c0d42140200100503611f00c012109940c00e0113802d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 489048776 1250 489047526 489047543
    0x60305041e1a060a03020a0e09070608070905121005011d0903070c05040c18090906050a051627060504141906030e0708010603030c0212010506010e011214070914010c 73
    0x9140b420601c02516400340e0041e00b908aa0380e100e800241030001958002c01d205c100c01010000850000e010150080405060611403420040710141c28010a4040c2500420b00c421152003100c90030440da003540d00c203110b010850755840d95400b2002400c0b40f40c0d000342070200701010070200803000080301e00d138030b4220b1a07441139141040204000340a440007514204405412054180b50307186420000418101d107001486d52203034507014042c0c40009241c10055840c0204000300c00d40301d400055500c49036407400c1c1201903550b0b0082c03018040c401d0141290411260b00224035207400c000140180c40c110301180440c0c000c00b20801c030444080f184c038400381c414461820020f180c040d4000299040300745094900c803030340341c4080350308458040e0310540c0003500c2030f80c1c40300c15814032207240c1030f074001710300001e1295103803a00002e403149e41600e4015040042040300d00d420743c10b09903c00f031800603124038115042d09003240c00500691580c015290441b68900341c40320150300480181d121030313a00c2040d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 489050026 1250 489048776 489048803
    0x603040507050a1e090515030d09050102010c0c081801140304050c0a0801021309020a0903050f0303011a070c1401170f061005090a03060b010c020904151d061f080304060305041e 78
    0x4c0c006003602514404030030b0080e60012584e0b660032702c0080d8000c4226500c0d411030518240c002425139a8046a180a01440d222640d010500c110219804003489400c0f41d0540800b510040f900602074119240407154040140b00c01c102d0b0108070011108422181401b0b01d40c3c80f0711a103400c038407070200c3e000d85c44038424004104c00510ba4001c1c0041141c80d091500410365661695401c010700014a5541500004010b11201d034561446201401e604080d01e400d05003075549220020b0982d01400c28101080d0440103000d81c8501882e0003a00b81005d0013070031a06040d103000b4645903082e20728501c03d22600c040210801d1286003a940481c10003024145c00701d1844d1600c000501031084007a041103556100c1e203000d610b4105070319010314420510308590034100c1500780120340d4118801c1d01d904ca401031130104160000508141c000010300ca070b03100a152800d550080079526640085002d02001c9400520160540c4c441485913000c1e00740b040103141c40000546a004860700000c2541c000100c9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 489051276 1250 489050026 489050039
    0x50618040b06060f040605190309021806060f0a050325090302090a140c07052b05090f040509010e010e061e070909110c010c08071e0e0603040507050a1e 67
    0x5020b07004400501290703d8002c000268007020b0344030390845408243c0008007680c4150410100c1181d0003070303d18040007030302450340c0003c480010400c00c545d2420005030110300241da511341190080308100300e100e95603070884030000c0c041d034104403895008207143c42e00b01d020700110206088a03400d459515032904034110703401c0048191000c1d1421880c0c0b503503814046540206030322194011402e1040301912241039260007854000513524004003010f941c1d008001c0204044002d41107c001420415101d4606502203103008a0100c2281c1e40326007090f003804648003042d4486183c2521400003030201d48411428190b59007825501c44000d11842c1400c2041c00c8038002e91a42c00c18803520345009200c3e500d00120080c0da06c07942c034840825000107064405150244681700380381d00c907414543c46031f1801603006032248401201900c2200740340d602c0328041c2031042221100c4044000c06140d240d007024102070b0ba58010034000d4034060700c2c0f0f010000c90355010343c00411703140c044d01c004c0c0403001a05056 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 489052526 1250 489051276 489051293
    0x12050603060c0c010207050a060506090106020d0f1d100807030f090c0506070c12031701150f050c1002030c04140d0b0610140d0c03060f061205070e1503060405061804 73
    0x49580f090755400d10403440081e42c14030100a445003d03410104103401c1c19020000441010ba1107c810343d80b159020090b003540040c0d51202951490528207101d42c4c1e546500c00364490081a0302d41e00621810403101c1c4950010001c0e409140255010004083c09000620458400050162034070040c0720040140303141100080030014480c1141c0003915582d0031b0341d16400e1044107030031008960048902c05d012404801024010f001d21201f00040c40140d42c2c0280c0b03400780504030042007250000342c0c10a540001c0006846110407024115541c0c41c00503480b54003034016014105500000b04521102031030300903242055550400c9000c0820740fa00c001b0025081c0060010400740043c038600c0e1840307166298041c04528010050101e11008030b40001421650150082104440c1c00d10382401059030003115240c0000c1003000006190b200c08600303980782c0e45044075403640001c140e41101000c0b01860003030360141d40300362003e1205440300c0041001d4210380004d180035040900001030082005d05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 489053776 1250 489052526 489052537
    0x3060408070201032d1107021c061b18050301050f0a1a061813050c16050c15040306180b06100908010507030603030221030f07030605030106031212050603060c 70
    0x50600017904100100904400710b101615054211010310805820a00501603030041071000c036881c43c50202c196000440036102c030840c0c1c0c1d201201c09a44582005070b241c0c884081d88423509800340c60304000d5040100810491100c064074015203020005940c1070500410b8000c014a0303010300c03020f94500600000501ca400b07102104007180a0100209884040042401c007140034100b42103a000d40040c02045181d80d54155055440c00d0104003940305e80905031205000f0101c10b81801007458207140b464600301500c825400410301010414100d00c10f4010002c41c1d00c644403c1c00812075106024078070100840000d00035540e00d41c001351003450f20310405650210141403101c4110349900341c5070700b1981e0450783c00d00401d0341d0380c506109140c0c04101030306a52800c202412005001421600e49030f0001a1039441280720840200300d0304c9000342c000401612001e0000c01c066566070403c02d041c03600c8880b440000c0f4241040301d02611403c1d01a081c81090050001c10b01d98861105020315503004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 489055026 1250 489053776 489053779
    0x80d050f03090a0c030b0717040503031816060c020909010e07061101091a01181a0d020a030b0c03010f0605090120150a0c020f0303090d0c030c0609030824030604080702 74
    0x101c2500750f000481c4028210040c600854032204145010140900403003000b4650520200302041080005540002240c3d802201c6602110f01d03110043d00315894440c44025000c012500b0700c4000c00c40d15800201e440ca00342c02141c01642c0c0323488805441e800c9440207003004809070400403060008900404030032954000e4076000140707030103d540314544940c80550f4040c420040c040010440c4103a00c00404905480d0b04d0003c2040e900b0881c0c03024042c1b080f14a100f40651000c10358901995540e6103488021500822070103028546a038818855502c01d0090148421030310001042d0b09100b40103840d000441038540c106604110142c2940d400e200a91900c0c03d4850040c140d840102a81101c60188090402c0030a124554450181c1090300d1074994204507070080c810016440b40001e0410320317240d102d003022964066641000ca0304010710300d031302403c1107003000e00620800d0f5010040601c11845100c00b01c0d400c000740d0306540c12010030b4100c401c0d81a0b00c0ac0d00841c0c08a80c00c50b0080008a10 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 489056276 1250 489055026 489055033
    0xf131a071e0c0201030b010509060403060b0d0b04060c0f03052a0c01060603020409180206041406121603050609070207031403130f060215010e07080702010e0f0f07080d050f0309 78
    0x54841d11000200c079a00c1c00340006640041d0b00402c6580501660403000000d0034a203042810600204007103000d03501c009841c450301d45028079515100c09081c0c500c00c40c2c01000303080b06441d00742400f0f80507040b41c0300340e140040d107840b00c0344c940c1d540300340f140c1c03801050b013042881e440308500c0d100c20050600c1074414400d00e94080244d0440c2840034400c000c004c20036a00e0260701c5030301d04030700e510455110b18000c030341d1008030b441040016500c400803a4140c55549480e0645107880c800411014080c1441962146407101c040c080c006600f04508884081260707014450f82c1d03550400d200380610300303a58240c09a4403818051000907000a040401c0b1444401100c1c10080361410f41d40c0401c0840d8000100b0742c9465505200c03a6034103212004080d440c8620900c3c05502d00384552440300001400e600c1001448808180b40f60701c00c2d005030079012160012984076508143d486500c4100182054556201302d080005034680042200c50316a0320f40c0c1c0b5124140084000880c210b81d0000307001818600 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 489057526 1250 489056276 489056297
    0x5060f0f0112080318011b080c0a081b0d090f02030c030d120e120f1c020306061b1009050601051e0f1504030602030c0d0e0f0703020f01090902120f131a07 68
    0x303030300f44510064030707e4440105182d458008405090320001805003007030246c0c01c20a004066410502441c0c0082c6007041c0ca951401c4035600f4180c83d8015580c2c840c00181c01e00314004240321040d086070040030b008a0580b4020451070b010156900060021032000c2081101004038505041c0d000c16400c4201d0800d03a480700c2c400da40c01c0b070096407007806c00051800021401c54901a0a034001000d03d403003e010452a40c01d103000083c0540c01400002c03c03201c040440d0410b00a1024000f2a604c103546c0d4505000c1c1a6140c40c025494403401d00800340a105111045034040011824a40c1c1006020704000b01014240c07003400426000c0001040d5a11010000040011090701c0158422070307460007c180c0380c4101c15449420f0310400d02220300c0590040d0300c9170905007804520340048035811206040b00440480c010f80348078605a001101c01ca00c0483c40340284103224807154030402c03010004041540e2040083c42c02c0000400016007544020f6814044116500e40c015402040781e0404180a5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 489058776 1250 489057526 489057571
    0x8031e030c04170105090c0a030f06050c0d0f0e0f0705010518040b0904030801140f10031509020c240c040314101d0c0a1a030c12010305060f0f01120803 67
    0x182c4070f441c1c0f6071080d80e41d40c604001e0000b00601c09400302800c00c88031003210750324540f1114600b40305040041c02031591500440c0040b03620303c1c12140d40d014200f03014446001c00c5d0b0050401011803160248690088601004040a02140300d10641300705850701c6d03041003002201070045010b820501600241c2c0c601401350543d41e079100942c4914465a01d03014558148401c0b82e1a00080b0462030f406014520104e040702c0e0307108203d140074000c0ca8071300010341181110340c02c102102158071060840380f0004006000b920040391039158851040004c51840350590b0090824070811140c2e1000d00400340000e10001e04c020f480c01986545c00411945074030202c00013802111a51030454540500041d230a060f000018803a0b914400741c104d07000c0381500d20344000d01850900c81c55404000c400c000002692100340c8c10203403000640c108110f0243c0e50307100d03c4c01c682e0f07030302e81a1107541c0d60915500001c1d503400324090a1344d05903045042141c80203140380e41c0c1d5500b1600042c0403a01000c030f540036840280c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 489060026 1250 489058776 489058799
    0x1e0203281b08091c050c04020909060402030a110a030e060906090304030b0912030a0b0405070c12030903110601090b091f05010807050c0607020c10020601052b0c080a020a08031e030c04 81
    0x1350011051500c00c02a4a00d0007a1814030041c82c1c4500540c01440480031959420380b030198810000d480150756a610f1999034002400d10310b00c8030f0b50b2405c0c003049642600c0d916910030a03c070301d501012990705840340110b83c2d0381d400040300d00d5096603000b000140f0014181d8005d0b80d8001850500302c91402c03414840001c0c150304100c4a08000c075030345082c0d00c1f0003441c2c00e000d03c0b83c00012606010075500344544a03541c1e80010300510300c00f131585400c44041010300c01c0b20f9038036050200009403900c03940c5880100020b0005a40c20b94424141034010444041d04481a9082d0840b0040c011561624000055030340c1d180c010280c2040c400d044c080c00141b042c080c00010300c900e07201d5018203d981c56101c1041080081d070790060085620000060015403104070750021600052000220f1103c0d40351080e4000b03400869005250303802e045000514418005a0340784810f100302c3c1c03c55140f40e01e81181d03d50301d0040c003240014040c400c0c4105181034404000031a00044000c0709c0c2e51900fa12100461700 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 489061276 1250 489060026 489060049
    0x6080906040f1b03080a030609090209010308091809030a030b0a2904050303070b060102100207021c060209120a0b010914060108040606050a031a090703030f030b011e0203281b0809 79
    0x141355a0003e106c1808aa140c40b50001a00a1b80030401c20b9440a4001c141d691005020040014400003114960741da00d6a16446101281640c1401a440c0169995840b03070403290100c1c020034101076805004d490012202001d682101da00c0310807080745120040d9403540000000220102c00308004502c94801344020121075000f60f2844100341040e400080c035041e0b41e203c07541d56592042c0680e030010b07038541d01044c51814203050040256240c81c18100c00171b1254000c0b250b0310000074040b20301c4e4094081a80f02c80c150103110108820b03039035480c40341d058917000340000c11500c0741e01c0006091503005a10850308a03018120003c1c030b0f140c0310300208210341904c2d041910035501c1c1d00010781c13105c0550b11400340d000000d000500100c4c1e00d5542c024040103081c1405109050315039660500320707407051901a04640e030241a06100704050b2401075140d41c00010028a400b081c1c0c00216072042c4107050160030360b03040f51f0702c403180c40c8640c1e0110306002a0f4408100c5000e8010403d01920350380380803c644 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 489062526 1250 489061276 489061283
    0x305071404080d170105010c0212012706051e180c031b031b0604120f0213060503060604090c06110f06011502150702061b09030f0c0a06080906040f1b03 67
    0x10f950160480050b00580b404081c0c0081e001c03071a001480144d80c010102c640d0154169400241d01a226034090b000d008c0300c4282c614200510301e0171b000090703200c074505d1300d0580c0101010000398403070510220165030100320030070381700d20500003142449000829110241c0d21541c155001e452a480c006403d00b003000b031407030203d40100f00c41d45e1100d1400b400591705500d070341000070000328810742c0070450f20300880c4a90061504a0817181040c0b140050391003991981c010207032100070021801801c010041401014020b2295800007105418107100b0044042c0e08410481d01441c90824210344802031070903031074150702511500b00d0302600300b0032038180030701000f0034111070840031100001e01c1d05200c90850581500790005120b0025008142c0c160804000860f14081300480044402c03d841001c07040c0b038240c45880c00340d45c501040402d0508010b02c0c01c0b2000c1000c25512101220944403d594000450700701801141c00a0108052021040d00c1070741303c8000c8205045030320141c80703038076801038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 489063776 1250 489062526 489062533
    0x60b0310020c01060b091011100915110c1507030e0304090b0f030610060806010c050615120c1e18010f030308010f150f1103071a07050301060f030507140408 69
    0x41c410750004e005110240c00510861820300740f48100091034400e4840c803507000e00a00c5812031892450512058050340030460040c0f003044118030704900303041218000d140c036640c58030300342c0c1c3e1740c03a0002d00031030b0707203464001004101400284916001110340600000145551540420101802400913200070003003090001058180b4006000702e01c05c80032005c911a800000c20004c10f0454165441d05851301840e00c840959640d90040c4c907201d01d442ca0180c828820441080800e100f91880d1910444054a524a0400d544080542e0f04c06440d92616807018040c3c0100500340d075040b1950400d0400241080c10f0706504d03858065003110300381c026481101c20610240189901b241c0c2d16070041c19202d50b41c0189600e05248003419883c0e911030382c030811a402c1101021a4420008541580820b41c01d480d591052890850b80ca140c2140411107565044000a0503d5003d4016217048600e59114104c121041000880080ca4010084811700c00282c169014021040020f00040e150b504000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 489065026 1250 489063776 489063787
    0x5041d100e0903030106180905151201021303030e0a050409080c01150608010b030403030e10020702040b03031305012a030c060b2e051c1b18030807060b031002 70
    0x805203035002030708074010000340c103014010701420010481e41110781da481c10041040d5000d41114080a855100342c806909082c21f000c001241011185191041119004103100070388202c1400d03405450304203890b101d043c0c5002c02c007090103500007000490f001004104c120b40c8540015040716070800c800d652400d0b0102c2e036200e404800340304150714507000300100c0010601e0242c0040c180041400f5850403603c010020804150081c0c111588800c22102629036903040040c1100094002e010107174842c40c20300005580508001c01103800b441c440c201080e290500303150055960400090080058600e48101140b02401d1201c03e8250103100780c2e41c50310014418280001900e81c00c44a90303100d500b540c408405c030340001102002000005078407a103900001d110040e2954001d4840506032002c020340544581d030360541c0503007407041c09a0990144841070040803904001b40321010030742001c1114082c40422800700103462072912600022460065100110b81082c991811150030a03401003103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 489066276 1250 489065026 489065041
    0x1505070302190209040f1506032004060b030703020c0a1a040201031b02060a0506030304030501050c090301200f07111905040b01050a120b031627050403120c05041d 72
    0x1000c00e20032402c8040458072045900010315072800640000c01c94564100442c08000404e00c13204000c80b034800d41001034550305c0c101118801410082c0080d4801000c4104401d480c192143c0c20a541a42174801d0940d51000000e0340203501440c11801648070b41c0d910300c00050601e40b0340b00001500d030024815981498800074040e100b1450078a50313007d15942c0c05942065001034100d9111400043c08540b03500c600010130708601c1140c00c090400c0d404c040400500040140090526100070fa0080005155894031003000c1104141140d0b403440040110791850001040585143c50266000e900741c100308a0005120030040f02c00074a406500500400c00c9103494468641c000400382031142c984600703084e0042c6030036044c3c401c000805640f0004500715803410041d120119402010081000e07884d9010014600c8101400400f400c040b4503680000e58544c0c01000c0c012a496194003032030b00803004011003d44210b200c03980802c80284000103080030704450303580d100a103d0178400000c0c1800407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 489067526 1250 489066276 489066283
    0x50d030b06040602060a0c03020906040b0c0c03010b030601060809030d0507020a0507061b02122806060816030b07031415090604050c1902010b041406010f090b04090b0105041505070302 81
    0x15169108034014881000f003960082552544515650000264031490f0702d401c0c0e000f8080c10310050703000240401d003c55644100ca00800246c2e2807e4110380154035460205800c1ea90100360043d055081100100000346c0192040c580080fa5202542d051100c1450900111001140d4800050f880214400213010041c4032800140c0305604c4c1c881101c015441042400407a5044001c1c001c4001e503141c0300c83c0080500044685c0144c22092000424000c400940441a4ac407801d845091078048009446000010413280703481003841c5080c442451500e84007840340004142d0018107032034903034001440104101031442100c04244040724442d060090142d4070710001c001c240240c0c039242c2400084800c05095030800d101901e20114400e58001c012030161001841c19900300707040c40a41218541c1800c071704d82c8107100070303038a507641801000400c481002003841040792219040006220a20f100e401c1b0034480c8006040440c60942ea55141c140c4040000c01154001000403940804043e03051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 489068776 1250 489067526 489067541
    0x501030b07110d0c0c03080d06030c090e0c04020f13080601060f05040b090f030a0605010608060906031f020315030f0102030108070608090d0518190305190f0f050309030703050d03 79
    0x18680288184502c550300c0c0c0e5208800c2c41c41906200440044d00c0400c000c800d882c1c1c0165a01c4910b181c0c4910780400014050700480c0021030b1140074070701c004240d0015601c83c04a00024800c01031000c0020441400000d51081c4042e50700e8600c00c0110f0070400a0303812404000b0700c0c8441c002d104030361510703000a02c241c8003900241c00b00482000200004004002528184041110504081031311080060300e403424440c001007d03a81040d0000030380e10303040030700c0a1155605840d8a2122754424041645074030002ca0b09110902140daa2100700c2c81d41da5002d9a030014072900d094a82d8092440060300e088041c001c40e46040e90000300602c4450b500f4041c8200501140c10711000a080c80c85c2c0e12600c0700c6d000c1009004001c00450942481a0700c1090007c101f60081e100503540e0803040f191006a580b07501054816101e40040f03010b01c844000d020f00e44107900100700a24401e9a0b694031070f050020382005a07000d21041c801221240e905101c0040214070880c01884500340d600720203000d44204 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 489070026 1250 489068776 489068791
    0x307090311011b080c0114070203031f081f0f02070b09010b0a0b031b04050406080d0306050105130902030c0d05070f08060a0315200a050a180b0723100501030b 70
    0x50ba50344100c107008240c1030710070407540100c1091703c0e098148100e90051040410101e8568948000e002145801100031400361136000505a51180e400b04000001d141c18403501e200717a401980c5c02c841c0a0700b42a0040204008000045690400c0f080c844040c3c1e0004001910b0034004070040c00040310092003051303c044800e5801c060385d58a480e2000c030700c0780002401200051190703003210107400300480c216000390900800800c0526204c50707110780c0d40d104cc1c41450001c2480d01e0341c003007490741c000d42c1569003034a00303254840d1046003002c444a019400140000e2940c0c40c0c00c1c001042048058061140701e0011681c3d01e052800104000802d4540d01400c42401100040c60520120700e0002c6807400111940501080380c000382010050140182035001d0855480071403c02242d44d0310030014050041a903664805516100c0e00b101b54880f41031040c10301aa1040140c0c000040d40803030402c00a002c0d00ca15a651280d2120215003408901c01c1c0301e002950355480144100704210011541003840d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 489071276 1250 489070026 489070037
    0x20a150e0a05090402130b0919050a0e03030a0207030915170c070b070c020d02090c0c0705040203090a02010f02030d02030a06063e0a0f320703030f090902030709031101 74
    0x3030074012400b55880074001030b001b032480e0400540b07030010541000c0c42c00040904030010a14100030702d510169242022507030000e00b0000807913140700c000c0c0641489440f40318061840c60b210041ea030030080d40020b5049050000c455000101c490034003031000103841d15030301c40241c0c0b01c00d07030019103001540003000a12500000d10041700403843c520459a8040c000c0d00306211710108500014400400111009602074140c1c1d0800401e042c10a0182c80184600305c22140c0a5032500200800ea004c00c0703894401d96400159803c0140d03200d1074140c070020465005807491b2405d043e103103e060b07038411203551401035202c1c482042410346c80340c0858446058100815144185000d4201c80c170a0454085200300102c00b0190620200c140034a0b03007090b922a80041a040d40303843c0010416200c0b11404400c1000504800d2100300ca0080510341041c0708030161084d2030569a058500040302d040407001c01000703080108001107144000c46c080c0b60141c03030340302940f40f40d031401080410014441c9410442c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 489072526 1250 489071276 489071279
    0x201031b0804170d09050a021201110d09061d010b130506060306040b0f03010c02060f090c01050304031b0f03120501092d0212010609060e03070f0509040f020a150e0a 73
    0x15030141c603050b0000e40c403030040e403050145001240c02e24020490380703006540c80c1914000420a00040d1001c440c1c0c400d40d01c0e1a007031098400c03000c0c01c0700e0140540c24041201000f5001e044042a40483d140ca8882d18001800e040d041c1e00300c4c1c02c060910a0607a003940c2d510708441c10b4610308802c001a008190030302c1030103940340c500d02280e07079808040c209600540d2100e498005035901e4010401d80c18802030020000e4440303030303400251b42c0c0c43c0694085196110001c04940103040102e4100390060301a19258070b180c4035a40e044424810000c1c0e820040c01000b900c00d000103800b01c00720204140a50342d140d4003c01000c410000b1903406a1003440c510303140903100a00f001c6030302021020020038561400280c090355070b04070003030b01c201c0c0448201c0302405000490410307007010212044e00e11300d5450b2981c1500131024103503101a1406080d08292492804100a141450100340d00521511101b01c401c0c1030707a4007041c00742031150401d10540504540b090380c941e03800b06401080c41c8040303d4401425 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 489073776 1250 489072526 489072581
    0x160c120c0303090e101401020111220f03050a260a08070f0c030e040b031501030804030308010e1e040302100603060b150708031308190c120203070b1f0f080109020103 73
    0x45103c6c880c3c000608000b6200c00002da00070340c0114450f0301851039055139801198007032410070b00a00659000c62500701d00100b42c1c1829514442d060f00c1c0d00000a01c1103407229116800002c1101424101d03000141c0845c6a500c1c82e56006444010102d4450202078146424094200016052243c040142020380b03a0301082c0e010240150307500d01030b20006400b8000c000440d083c100241c20700a0361160240c00001080070b80c00041040324000e0780c5084543c1d8031502a402010019121440c0e019030107415581c4a4407132114454216120b40110351001001100c0c01c010b9034555401500c0140c0e642200001a0600d210380300c038a01c0051030b580381303080400d07a250a002d02019041076070029004440c1d404002000007103843c0da10700409200260344030b00c1c00082520b906140215140b6030b501d101c0c000d40d2400001035500c52035100c0c0c0c0d000c1c036a585c0c03102414a241c100300702040b11800c403000005008102104400003406811001044000c014000501500c02c50001010000144d01f1013081c49c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 489075026 1250 489073776 489073801
    0x6210604020f09061f05040909050f0c0616110d020306090106090e0c01050712021e010c0e0108160e0609060a0c0c050d0506010b0a050d05010803090a080c0303160c120c0303090e 78
    0x201c005014171070041804950121810b0081c2d0b04865405e83c6080c1c400c1d02408070014082e2070703c0009408641076010036000f40001ea0181704659007419810f1082080060000e01c24403600d408040d207c0c0301441d4942c2c00080c0703015816a160f00c5565501c1c441413103c081e290180c009200312100080c5054102e00300020b103a8030454602501d28010540b00d80c2c01c8034070a200d04100c0700d4071039050001d080440104035000f00104181240455140d003e038014a5005d2031106104161a014040c16404054002d5510344c54000c441648030f4401c1000d100c099443d0f201401b6168100d41c0d811107029490300d803503100001c058021a1042c80c220003000005203000800505503506000115100c124076030341070740c15010f0b460651109504203000450f240d04004040c142003c401c541c0405080c0e0381c0c1c2d034025100c00410303003100d4141e041040302e0803810582560900d04984100c0b4003480c0141d58968180d050a91400112144101c0c800708205260740308000d4009040003441d04280b078204041700c03400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 489076276 1250 489075026 489075049
    0x60b120d020309010c1a0f09061f050103150f1e050312042102040504110f0a06080106140d05040503190518120a1709042706020306210604020f0906 65
    0x100b1584030480b2003007100b0386c042d07000d0640890242103e182000390b404000311108484100035481240f0000e800480c03248900b0001c0c103041060020500d0030500110040c01003405041d01c582d9a000c40061030394403d600540050511502095280a120483c210b4002d800e600c0309202c0d81c04240c050065140d80740440381203403e125501124480f1a083c0f140e000e1542180c0a03510502e450200014480086041c540945084454000d6900c92804100003090940120000218641d00504c081405029052481001e0303904407810103024454060660310116004c40d51a000855070030441e00d50300c05868860710317042c140141860b800100440070b040420304994800d8200c007071100001102070043c02483c54021400f48150300300040354480581c81407080c0f90003989050305440d0002500702d84001021070402c4800e0784401070b511103034042d403c0680195480544030034045107c0302c90b007140340341c40701024001c1c003100c1c502801000465410606103e028004007404c000c0c0c0f40d550804181c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 489077526 1250 489076276 489076279
    0x1204090b0321072a240f08060a03050a0c03030f1b0b1909030804021c031d041407030605041a0f010309030e041404060f0c050430060b120d020309 64
    0x19200c50f264102148082d40b540404000441c0c1c815510450b8248903104005413100b0801080c80f41c00300080d00015040d000c1d00450000c1c0c11b80850306101ca11442119803c5100140348510964698031600d0900741c01010440d82108094030410070581c2140c17101580c48a141011049007400188400901c1000e4900070125072200d00000d50030b29118060044402111000300040040c900c1e000c1c03e00030081ea000d82c401c01c0f425004500ca440890052045258143c0e16955130444458944881c03058110090b0b9005840d85100c503525040100b00030300c9803101d07540214400303140c2400c1c0422a5039200e0428a21140e8040c00d01441e224880d60320750410007864001080b08203810101c8000303d880384519881414807007071114440d6180c40080c090b6000d10b1003001000260a03c0310120b4141c0c00c046030114005102c204400384491024510006d015180c1d61010f500c440304c0c0749040708050104858850340c3d9200e454143c00c000344900031030300c2850020446001103a4019699000300348650307 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 489078776 1250 489077526 489077593
    0xe181e1b030403140304080c0709020c250e040b07080c09091504320f0115050a02010906020d020c0f0705030c0d0f050d0503060310140a020a02010e1204090b03 70
    0x30b08142c8a10900c495500e1000401c903180c0c2807038070b1302c0441c03a4051486032846205d401400300d645d258034421140720003103003001010700280b0349540a4404220041509907820030300d00014681740307220504d51081d031141032200740c207140001c00074001003005450896022801d0141c00c000e5121441000d40200c180640004118403800003d0090820328501a5071006000c00340d4100d03204041c041c114070300b80c87c07000c4040d9680d03500401c04204001d1290b4540c490400340401d00b424011802000781c0b400a100124401449407142d0b4160380c0311181008040381d00040f28000700d6024007402000b809500007501e282440c0c800001d039550bd0305118284203103030454040e8200959410742251441c0e000050302c1c84405640c1026180790812140c081c028000c0c080a0650340b082072042030003000500c40881810380b0b03400c01c18070082d00700e1010341040d5035849400c201c120070201300e000c039980002d00c4034950340c0f800c1c418204242c0c0d84c40c01116011381e2002c1c82690486418000020103015013040340d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 489080026 1250 489078776 489078781
    0x70f080f071502031e0907090b1c05160b190e0d0501090501090b010807061707051209072c04080a180902030a1413020f010e181e1b03 59
    0x1103040a101e881001000b08414109030304450b100c0f900510310501d0800614500b4610340030000c0311100c0201c4044007aa0484003080c08282c20302e034088051340701d003e031140f40da0140303201c0c4285000c4411841a80e00358050554040e4032030100d2a02c0340030b4125400fa9604081803035408190341021036480800744140b041010300c403a1145000022a950024000e020951142c02d20034028090040103564500c009400400c0072180011800105c0b81c1d696191118803507410b0b4030111200000e0442d00401a042040742e004000140c9014000c0010740c0c0034003002071420044900d64030011502d4042d000801c5d10100a46414244850340690800b00a6544042d000822682900070782ca402c0003034621400f000c101410340c3c0d40a94841c0504d51410098040324402c1d1408800c01141d0404803040298070810060402030719140b4221010b0400c1e854070505500040d01a02e003211042d841281c0410810900030425456404500d01c15400c01c0c06601300708111414440c1c0b40e000b42d03112040c00002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 489081276 1250 489080026 489080047
    0x9100b0f091c150507140f0408061509010306090807020612071106071d120312090f010b0a060c0c0f08030d060f060c0f080c030409020d0b040b01051b0c030a05060709060203070f08 79
    0x6d850340203400000202d60358101a112054140c1081c01041d0143c81880006202d010342d40c000298108402015851581e28603076520010b800c03000c2003203a0000040c014a801a00c0300001340940c000100ea0b160310368903021000074007100c40c0b4a03032000c282e40700c0c0080c42007030381e0801e00455246801c802844002c4c403410b03001c240e441c0706a1107130003d41e10002a01c2c0e01403800c2507078042e0069000074107507035580005503888bd00303881c0c40200c019400454084100101e40c041d003001010303184640a0854030980e1618000c1c078925291b4018a0030b40c00026150442010300d12440014100350302410181d00d080403002040136a40c40310040030034042c1056038007070203085801d882442c190350045944d070741d8072001568041d40061680407809800c2403803648043c9007a00803000c40082c10b95800d4200072444601d40340619011400318010302503000b400e9601c3c2c809118031022035001e00006c22090078807910052200300d039030f4044011500b05101440010787c041600e650b809401a8155844810444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 489082526 1250 489081276 489081287
    0x212192d0902270c03010311090a090b01063b01050c0304030f03020d0311340503071b0605070b07181e060e04060f0509100b0f091c150507 61
    0x20398000d4103440c54500c2c0e50f01d50b403904201425004511880fa45981820f01c0507400280401015140d54008407810390804502c080d900102802001c5175101d41ca80f6102c250f10820703040107001480c54499546200042c1c01c0b141d104080c0c601c12099044a55041d44076040841c8094030b040240000c0c00d0404482c0c20419517020396000030400201c1034051070042d40d50920580b00f100468101502d01141c8200d91054901800d05a03910850084841000343c0780d65541c409002d1052019040c40c6010450401c044e000d15481581c0e0921540890425030440360740682c007203001c2100c10403030000068070542132503411201d2403c0030b2080c0114030540c009504102d8202d0b1401004d0040560848084202110129001c3e42c440100c07240748142070000f84c2d91507000b0016052685181044582840711050350b0183c1c1e0211868441d607141c1e0f29540d034541c016143c1390b4400401060102407882c0440d0310602d050b0441c0700342c200404840d50390303046502408400c1a101c5a44e4800680790900a2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 489083776 1250 489082526 489082541
    0xa0b03040f060b0a0801020406080708042001110d020325030512151f08070e0f011808240105030105071709070e07111603170a030207060212192d 64
    0x1309190003003511462202c0c000d400c80c0c0b050b90b00044407030000c40c100c640101c2c0010b014a4214003191846e00a2241468105048004a50400020681e107204081092011042082180d0302031030782c4158500c000041004100c00f0307081d80d20080c0c2001030000b0f03048800c4450030200186110025900c0070780040d00070140b800ca40780c00c07580e503204c3d070410524240782d80c501c8400f05880710320458480351022580505200d55079900078110b54000402c542c000c2c0f45e031000c82c08030640711100e02d5407610345050400d40e0b2200b500305103031855041000d4604295100501410054008210501e0300c000c00400e54644558007004800c2c0f00d001081c1c1105090041c2d102a028401c4050650300b4500b000600c8055200c03c01d182074000d0a40102c0b46040c0d10380003008032030300507003407448108011428066a50014241c007003030560800c02c06001410070700142c00001014840752002d458400340c2400744030045a07140e1516860010120103c1c0c591691006003078400555010b0990b0f80b4282c0c481c000c0009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 489085026 1250 489083776 489083779
    0x11103131106031501180522060503010608150a11030a090218101d04020f01050a090305150415020c100209041805030310150923060c070806060a0b03040f060b 70
    0x410003041c044a0141301240300030f81c1c601e41d0080c0000c1c00d1528000c07150052541c841214102e40000c100d52074842601e203c0144000110f46960760002400c4541e1a804002d0a800c20080203004080c001500ea078000242d1000340a803030382820070010300d03101c01041d0100c1180e85010402c29500c46042c081c10348a014404103c042c00c103510700500c241c015126200d00da030504205000c0042840095901071039000c3c2840361184214001541d45401594114082140e00d00d00080402c7e0200004000728800f400b540c0300900705410b065031500743d030011000f10b25004100d485d0358028005107590600182c0d0710b00685814407074000501512209202d1405030303e14448503401e014010000314050b48035910743c0d01403c1e90700d1594001e042450000c05002c200d60120800c03541500c608074000ba0080c08401c0110340004000090313407900451804851366008210900668000700943c541168084032215201c40c030300140c0c1091488018802030100c0307121420319040055507003248005600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 489086276 1250 489085026 489085039
    0xa0909051008120a09031401140114030709050601020c19091a030c04050106051603020319050304060b010503060d11150c100612020904030c05150a0e07080111031311 73
    0x5186240c600703040c805010b00c070305034001c0340c010b4a44810b10740f044402c83d0399607490303008020307145848100c00850100f101e090155207414640306203000404070a40a08040f0840814800f541c009040c03a080303194024400311031503d014044a682c00081d2901c1c003160846d03111081e8010202d0a1508118683c003100300241005624151102402c1482c1071040c1c0581c111540b12050a0400042da8428410203000c96401c22449000309040340b503500905000c1d004803840c0c0801502030b9460300c08508600d038000303440031040c0001c00003140200c0b22010403d10b0f0650460a0034000158001040d12000700402c16144001c012501c425011004e500588488961180c1241d0709654441c80340f03507070182c0094a001c0000c10b2841c0c1c00c0000c0f200c03542c0c002e03001c0005952141c1c0c00b0303201b014403880c0c01e491603c11200545034040d0f98081261080a2400020500031494601241703040d44503040f00046034104200504541c6401066a80c84082c2c003e0391003070303000141000e911102c40486501c2d044007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 489087526 1250 489086276 489086281
    0x1201030b070e0a18110310030219031b031a220f02030d0201050403110d02030d0e150405030c010b270c04030b0a050114030a0213110903010612020306061f050a090905 73
    0xa00403007054800c1e803807540a2040d441c0c084010210741c8421287c0501c4c04640790018409410003070000806400402c3d60840c034640c5980382ca16501e500812011607800600c03400b8020071050086015401c0c0c080ca0b6554007500b420311403d422084800090f07183d020080c0300d00381c00d1201c03565413500c90a80180035110342a0312104000d003e860304840c00d401140e4441c2407203400300c10008014088400940c0650300b04159804c101000c0c2036801500c005038415150b41c40703000c18100445030300440c402c500540c3d480c841c05022509458218164910031aa1803500c04020240720302c441640032242e07501c120381c941d0b541c060a8154010381d0400b0381001402e03002c000d10009070340e120f14181d5240c0745406481a03280002c155031960245002904001007164070022869980c1054001040e6140d441c2d0070039600c0030200e82143c4c181d07441140c140464414440c2942030504c030094110105540c40f0360740001929400c0c001c42000300c040410801c3c00140b028a00e441080003002400b58008188020b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 489088776 1250 489087526 489087539
    0xc032a1b310c0f0f092606070314100e041e1707020411091f0e120a02040b0d120503060301020906070b090d0513050d0204150305100b061201030b070e0a 67
    0x42c828040e180000c0386100c072080c652a40030740c2c0903150381c150960315100d246040044101151004801c1c0b10b80300f0b220703216880c640b0701041c00340f41d02ca04016500011075882005070007142d440e029095260b9641803500034040310001c110110b030f0160f0804c107c0b005011142c6c41509818030aa080a040f2142c0c09603c1c0d80c00311510b80007060240d000721004e20520340c11400b94070b91032290900a59104180b440d4052001c01d500c010920842454107100c00c1d82c401906c04a03070890540b90711110740e504070386000300440c6054414100240d80540c1c44c040d440c00c0300c0c1d485d400c19500850f29103040c8071011000401666007501298415900a01103944421540c9448284050255101503640c00b8121038a46894031400c207032405107040605000e2480d24080c1489029444410282d0304251a140024402c0300d001025800541c40303040100a0034520300300d01700842d011000b44922440c02041b80c81da540d0b020842c2181502e07046401c49c50992034883d410f50b94051411105500101c4500000404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 489090026 1250 489088776 489088781
    0x200307030b01031b0b0702010e01020109120216170705120115120b0f061c03200309100e01020705090a02130b09040b0a1214030c032a1b31 61
    0x100ca12600c0c0c05030b80c2d10664110001c04c03115900940e40001700621092025621074410a141c0c4001800005440079198403501315021203020f1a401681c0820702c43c0d4a000661048040180200c40481c200740428540054541001c0d102e0079204000820500700e24076001c0d4046488291a040e080d8060755070b620318100524181c08040c0c0341079541d400001c0c40d1641941146200384c6000345014101c0900401e60388070410055000d41c10050704104417500c0d904500600ba0041c0d10b03110003151144512000c0240a242c07403040c0034100540d00080c00c0c1140d0700001c0400540350f0440740f119460f41c645103075000038080c0d90602c041d020080c80001aa681d1b913140100000c000035101400907040d0305e002c0c000c100c4068401c0403c80252040d445001c10b0882002d90042e102c25010f581c0741108034030b030300d5240d5004103815003201e000003c0c269114117102c0d807101c40300c1d4a124000d0b100c400e074041140b0000c82060880280104402e14203050b004821074420340201c00031040e502d11241c2c040410030700 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 489091276 1250 489090026 489090029
    0x2070c18061703090901030b0a0f110417240712090c050307120503090d051c0e2d120c0a06020604020405060402121915031a0f0601050403200307030b01 67
    0x104502502d422004070303140441141d11402002d88010010f91966603406c0d02d80c2002000c80f48059916201000e03c3e034010300480410090b80c041e481c0d121410882d074042821a0f0401c0100c1e10740c0800c501d0800103102101d041680c04070019440d015a03500c4006842c40d81486003090b044a02d4443c4800c1001300948810050300c10640c100c9121546a40c100c08a9210051001c1d042c0d5000b403004030b0251915103050441548101c081c0c0d003141816403074640c803165207101d28601040f40c0000d41d41440c1001058180141c4200c01c3e18111401000450034401054503102c0b401401c02c144003005004082002800e4054080c0044071a140d80d818003e458800a450880c8280d0411000ca00117261074020390344130111400a41d101c035101d40c040c48181c2d50340340e110604100d80b100d00004c0c038034000019540056004074400100a504051015403144c0014009a03401c1343d14014044541d0b40030741503c050760303401208607901c0718084210700742241c2014441a0700d441140808010440346003500b90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 489092526 1250 489091276 489091289
    0xf032d03180b030103120906141804020708030c040e15010504060c03110f010c0e18240306040c0302130509210c0706030c090602030c03030415090b070e0a0905060d0602070c1806 78
    0x19a003d03100c00c4116030b603610f00d500d0344109c100140100b51241401f05694428020002c10046c41c1c020140e9a014260304215203500a03030102107010002504200812a8401404a131448802042c00d002070068001c03801208208018071140200b010b01900c3c0903200c0e296005d0885102c903445204150290802050b490005800c0682000450504001c94035008892080d201040c0d40e550000304000c41121880e903440e0b511105558009031400d2041d54007403802501080f00047c11401405030401c402c01094683c0c91810007003203040f107000b01e45c0165408142144640c000d488a40b40c800034040d407400e001003801928000116950542e0006991140c5626000283e40d5610401d90310b03801041522111034204000240000344030b0700c0d200d40d0b02a40500c0c00642450291a00442e4060803a428000b00e400340d01c1b420810b2034145030007001015100360501c00740c40c103980801c07905003075504014940c2d5004100704042041c004c20270340150103880740c40b0700d070540d50040d0100600424131816 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 489093776 1250 489092526 489092537
    0x1020306030d08040b150604151e0c02030c12010207050304083a080601030609090f03030e0a08040911090d030e1801060806010c0c0f0f032d03180b03010312 69
    0x380302c041e002e50b0801c0e1049400c00f4652603d80e44505509511400c01c441d400e5000008000128840700c00c079660000041035039403103526203042c40031100210400201c104c41480040003844006907400505071211030416070b00003844c4409a002c0b2030180c003402d14002c01902011401084001c400170b10a05040201c081d0f400e18910b080c0091070307410f040740f000216410303075451500c070740580034103d40c0307030441e4040c900040d8490355101030008440c000b00c0c0071a411800d100c9007905040d818000e0700c5901522101070500c981103a55440d100e4461846864000c640b98401c00040e0300c01d440c16902624409800444440318034030300144601126080c1501c64441c001249068451490119058a4454560a0b81c44e1944001918426070281045800c0410b0780400300b0f8550981400d84010074003011585079041c194540000a050b640e0101c08600034904190f00450701191761900c0c0c880e82605050f141c00e54822448542160143c200c0e070803080001000108021210304108500139159461 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 489095026 1250 489093776 489093793
    0x409020d0e07140117060105120f15060a090e04140102040303080a0e0c0109030b0604110a11010e21030405030706230601140a03022d0c07090605090103140109050f0102030603 77
    0x600f038101d052807000030b0009051680114282140e980311940210050510f14203142c0c8900180640d980c0440b068130310000c0c201c09124590300344900492031000125110713414030808d4040242003a0140c851040c5242c14003011606004a5543c5210b451020074029940c4644a04000d01485026100d0740012441c202030015040d6000c540903407902d00c16581c160100c4c0c9180c032808001c10004d48115405aa985c01b401b003001c003118001e200805507925070844091050740f04134211203e441038000f1a41040020049d9000c0012208a12018212116440b9191410080d103135010756107000300010f24006050041000484800003040710420000c1d07060780d601c1c03004640c001801800f600c0c00311014414040d260b8002d030040d0640306a28171111408040840121034070721040981c2ea00d5003640041c440d8041c113000e03c40400a018922418402c03030303280c08003041441105110182180c0e1a07840741e000541c83c00e402060350250040c0840e1220103880c103906001754402d80c0d00500c240706803801d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 489096276 1250 489095026 489095039
    0x8030a0813020612040602090315450f010501090501030b010503030a080f1504091101080702070e0a1a10120b040c02030d0504060902030604060f1d03180103020409020d0e07 76
    0x401c016250b010b003c5600b003001003504003100d007001400803a00c0a800340300d20340d690b0b02d0070400700d02104c0784004000c1d00e0f400e080000c99000c800c0740c801214480c0d4541d0703005200c1580540305500c0d01040782120803080f6408076030141400d0040101700195400c000c000620500f45402845c10380e4001e0600c4201c0da41d8139800c15599201c0c625011020491030301c0000c3c6581c03071204082e94810f501140300146085041d0008080358441c140445418048013090202940c0c045181944070003280001c000c0b42c0d00b02400c580c0c00f201d004100304034068840f0b00940081d070b0f00b00d00b12a1640c0c805008038031070f800c1c1070310040c1103c142030240070040c501c0c04480210600c1c0c039010390602c200c856000745141102c1c0d004680c010303100c000c1c416610f00e82c460082c0c0c2c0c011703201004001d11690280c040041e1a41550b42484252658014541a0010410b02c0c041d074000c0301100321280490075415419600740402c3c01a0007900580e03120310105440460750041c504940c1e0800d00125001005407011a5161072 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 489097526 1250 489096276 489096301
    0x13060e060406120b12010c03061809020901031704030605070507120806180c040b0309030d060e0705090d050c060a020c09060d0308040206030a0902040f0b041a010f120902060408030a08 81
    0x402c0000007030111503246110140c07640011503a840140100c0031130610b04403540d00b95890309000c0340c0041c4d501c50b000c00c1050319400c018030414140c440240111089600042c212a038180409040e040102802d078072400302c64400c0310300850380110244514500944050a0342d080410f09545140c03540440c0c5020307611440000780320360b07801040079050b81d01409644030281002011604190003c0002090010a070406580f05503c030702c0055550b01d009810003026101c55038020705030800103905200304103030448283c41603032405680d0500c0080507410aa1705e480c0f80d603200241c100383c0008490040c240d0208079442008019a107007803041d03d803201480700114a6040107000141d14601140051410500440c1c21040c0c060012651094030f40001d003c0300e0981a000c004540d5405103038849007850301030105d0784000c0004120900582800180c4002c0d8440c0258003048244008803241c2812540501d61403034001d02440e4840d6150912250380f41d000c508200c003c180d808000030360304044e01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 489098776 1250 489097526 489097529
    0xa0216150807030c05030c0706020f0414190501050901050c0c09070807020d0e0f0607080d0c03090c140108040201030c03110f031b03190b1c05010911060c0307021c0813060e0604 78
    0x1c1c1d442c01d21b543d4882d0100744854200180854020350200091041d81d242d0340b0190014280300600070039a02e800d0410407402e50a141c8103e045e40b1003220003003203241c0e00581610100c00b02070810321f17500c1d44407402c1d06082c10442d0042d00d0780589220107103c3c025070700c15000b51141400b42c080ba0300b0140c1d81d110070380d01540846011030f844451800040000d08000c00034000007441401c1d86410200c03547c059105035800d140c0550006941e5002002c107000c114104d94005000350389400b090b103104030300000c0c0001401807020341490b40703d50030101554401d5110003494a0100c421702e85a0b0f00008035900e0a0344243c85040e110320406944600b48001901200d01070130400c0401403580e852001e010b409000e00c0c10201d47c1c80741302103039400c207101e50b10380d02802650300c10000055203070041d1400e82c0020300e4080303200380220f0060051000000001081310512501150240084c0c040020401c480c1500c00d5801410780c03c0204864078001d0710f402440381030b00c015460300c00c0c080f520b50f82072141038040ca = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 489100026 1250 489098776 489098801
    0x50604061a03280507080319120618470405101802130b070b0c09010903021c0f08041505160308060d020a06020a0c0e0c0a050a021615080703 62
    0x10048000203000300341003c068218410029a0500f554031039040d800c6400110140d124074a0300011160b46e00e501c0310f0100c0164514200401c181414500d803556056010500d001d041136a03582c0d504420b8000d50b0396801907207001c0808840c1003415541d04628400c0c0c08064860403502d0099000304c91516026241c4141030000740d000003d49820b040d124154a40e154864025500700901010416545241000f4040c1c843e405940c0302c00a203841194100000c20130f1150010a0021550980e801001c0310100c940440380600081100446070105800000b001000300c11801c000a0810004802034001c458080408000782070345024280d40c14070512200d60000c0c20505000c90004c0c1c003e1502c0e40e008a000741928010001d1075002c43e1252100750800805a030000d035205c020030107610f074184040c1400742c1d0749514604007514420194040ca54000e8203200020400c4a0f83c0c80c82002001050103421507c0b000b165030301d4160094401804201c00c0005001d8400100c0c414024062502c841e8907 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 489101276 1250 489100026 489100063
    0x7080c011808250f1d1b0a0e01020709020a030b03100b033403030306090f150e07140d02190509032a09090c0307050a030b0109020a03020403050604061a03 68
    0x2076201024016036650042000c40c15070640414084c900103200d10290441e00d1510001002041c80525100740003021070000e90107440c2031407180008030041d46e42205480c10207007103e07060600180c3c180851070b045015468804980350b20315961503000328131034003010303807d450304185032071805015900242096070b0981e01c8420710208009a8004103505500c007240303030f086054a40788240c014a811030784264002615004140407082c6c541c1310705008518024010000b00c0700c0154009000c6040344560750004100100003200c2c64015098144922080c1815175a0b490802d40f2080080d04420605005500680d804d000380300e014004868803d10014018206004100f010741d00c9000a48020654020580c4a41d0341644490350b43c0750249a1a0003d00b0704034000750141480c00306594015441440d41c50010400703c3c6400455905465a614002d6541e580b581c0d002c0e4003074411a0b0000380184145820801403200a40c060103030042e0241040c90ba428940c0c00301640c0f20009a12082000c2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 489102526 1250 489101276 489101293
    0x9021203040621090f050a141f050a020f0418050606070f060504060209120304080f071523070501020a02010b0a0b090906120d0206010303140307050f0310050307080c011808 76
    0x42050300310540803000a80007146151456480500e075417032256040b145c55010300118420001150301000390701c2c140000134030000c95002c06004644940c0351510345400d5941010400e01900d03134044a290040c081032165407556100385907958025071640310954146031002241e0a45001400c03100819003102114070240300323035102d100040401500489500e81d0801c94503441d51104128080580310301c9000c1e503107a519101c002410428100f40102003504460310134085055404900321030061039160010002801d16800000d006001c031f270f00708140b20041006020048150003c040c0a03c0c250b00034016140d805061000d1051a0b001d0002d806030240185501c1f4149040b046512030001802000790900b40c01c0503a0a001d1032240150060300004014010300d82c201140d8864143c01000300c0d459071602d014000c02c140180e0082501c018000800301c3c4023410fa61102c1d4001d805e0041c140c8025958031000c5650303801c0c1e00303d90075000c00e0f40481107840d44800344568600b1504c10101800c03568 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 489103776 1250 489102526 489102557
    0x303190c09053709060902071e11092d010602030a0c170d0c08010b09060702010f02100f02030115090b12060105160c05090a090c05010809070810090212030406 70
    0x10f0b0035426803150840c0c101003010b40603821408140f4901191004107843c40d5081103210030a0700d806400107100140100004d00003c0e1480d442c0e80005801a1150038281c000c0346000600300800c000010750000c2e00101b844002d001c5641d0381c00860000d1003a00780503180d11090404098400d225801c0540c0081c4102c0c102d242c01000541039041c82003c40226140e200c042041c1030b0f4228800c1140140c1d075458070a1046600060018050004a04114140558100001c0052240c0500241000b00d01644040030314002c00800481e16601c440a0100e1001c03005207100a420034030400900040d10300d00c40070114000c544034010b0ba01034112503031030001c6415103502c4281300030b024a41040000c100401c200507000002d00c180520401c0c2240e10f00e46403a042000100380505a400014988100c03000000c2c0701e6502141121400e0825034440d58400c40d10314206100c95210740000c0c0a4511180301e9404190300c840c04080c0708580103460b18940f180882d81d81c1c003403400740001041d4550300c0c00c01030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 489105026 1250 489103776 489103789
    0x3150f0f14041205120a061d1302060d0b061b0106123507050c010206071e12021c140a02130603050a0b100512011401090303050c0f0f0303190c0905 65
    0x5040306070804a192005030041703c580e24504542c0342d6030b0195100c900740510341b400400302c0540f0002c1c2c0342c03482d070300d00f400c040d2440c1c0c0a1030b200d4001c0c410880000d0800d0b0100d01c036044040d0f04080141110388031515030001128540d0b824400e000c180d4031f40740000c6400906840c1220040750028000d07480003000c021402c2e0b400351052100c0c2800c40517261100e2a144982000746499841000640122541040060b24142024015800303012080c068141d04030401186503031418482d00e401e4002e070204a0006c0c0c028440c1e00990320500021316220880400c0c0780c0c10454030401d0410014480e903a80e03031154000c9014440941c0c4041d80c02c58000c0040034800c0d044035412150802000810001003c0001d4081030401a0300700071400c04101e44c40d1840c0300b07113681801030183c00b009482004858000800c0380c0b08902004003800000301e450b08140344108500418441d01c0d60888010070440a1b200b40d42e504211070707d01031400c80305400c0030b05106501400203030401a44940d183c02d030404042000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 489106276 1250 489105026 489105053
    0x31e14010608121303020319030305010605090607080304060902090a06050102070e0606030f0405100c110c010c03090510170c090915010e0904032303190b130203040203030403150f0f1404 82
    0x50000d400c00110151fa401c7c0180b101b001c1400f2031040340724200c9d01c0e01030706031281680800284007040c084c20a0a0325510b04907040c0c0707503000c56078695035925842e00e500100300e03650300a0b400c080000b04004807004588d211000b6200700b6001c60300e85594039150070501c4101140d41039081071003032020074640ca80c4149103d07041440394003a29904c601e00c84114044414112070000014548a0185500d44044c407015011710000c1c0b034912a540030544002e00440240c0c03103050f0080300044240c2004e18482c2e0380500c044130106541c8031450030040a88003841d00000c0c0c00900c98844003001c0307200840c480144171001c8d64103031a2214401c0d010010400c05040081085d0240715010900300922020b41f61800d00c0c0d2150a0019501c906110f0600c0c2c0003010700001048007540340c010b000550717581c1c041500e080340310010300159a07503840b840400d0841c02270703600003403c001045002140d01d9100c0c4c0c1002508954101040104821081c080303c01d8076400c1080030910403280c004200800d81201d80c42c0c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 489107526 1250 489106276 489106297
    0x40b16021507050a1e030206040b0c0c0a1506050603012106090b0f1f0812070203070b070b0618040323040f0f03051006180f06031e1401060812 63
    0x1d624030609181d103450751000c0d10854454211520600410000c003084040c3c0d51019030000e40c045150f035401039903032003010f40b01410307009171000003850500340c110440311086803190980d0000c010a1800400c00c080c280404098641800e10208050806d001500c1c1203480c410b581280f030041c54400b4561200503264107030f6059440c0e84030b00001c80c0d503a80d6003501810b60b0500d051076500d049000c030308003e000c500803050038080c03070345d403c018140d0001144101814860308866803205140b00081c50481150b11402e00c0000c0440c0307100070703c01e0121040e44101c1c8140c0d500022009411600d4150204c11a030040200c3e450781c0000901c6000c0d80c029030701d1034410200b19841c19842d1104007100d80210b07072100200c00c94441080c03040190502c204040d0700c520b0f540500901e81010603241018002100e05002d00742d40b603080100504250304010300a44c5c10650782415014803588008040c89076801c03da800340c0d04455201036806051141c14115607c810240481361640201c10105a12a1080c2e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 489108776 1250 489107526 489107539
    0x60609040c0603200c1b15090f0a0909050d031b050d0504020f04050c04080f0706170702010f140402120a030806040b0d050f0c102604140f010606090902040b1602 71
    0x11504c14641400800b03800381e07514010b00c42080000f00c0c400c0c1010740003030803501520140e000d04044518220546400c203500300c80d4041500d64240c003150031110710f90b00c00008a801d000c200002d000300032071401215009541c1c01c0c04154024154001c240803548214030006004101c40c880004682c0d006580185c40209009c00280848000a0a0b00d2040d1251002c1241c0042c04005000c1d0403c0308200350340410015000151130500c0103000d4107401442c1618401090780094040d0340700398000c00d02c2e114044020004030344040840d40b112801210201d000f00c00e1107480070140e103400034054944076450365880800340e85580500001d00070000e440e0750040b000d05481c2e0002481801a10a8038034288000c04610880d0030800c004480c0c6803020806103c0510006540c1e60015141d0305c13200700442c49404c031181c8031487d05500ca0720420204030b009004140c03001c0003041d8190003010868800703a6a200c3e20360789a4100c0001c80c4620b10642104140802820003c642c0721b40740342070780c01d0009100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 489110026 1250 489108776 489108821
    0x309041401060906030e03030c03090f0f0c01120219050c030f120717190506010e21100b0f0d032102120f0103050d0c02030f0d02030408060609040c0603 67
    0x42025100d410402504644151005001c05648400b600000308103c2c90140300034440030840380d85a00c00900350307141104000001810f4884108100c0d1500d120500031034507900300d44044543c564440301c0c003484c000b50080c040c0d05070104441c02910711001d15805004c0800d0b40030351090b241c65004490310341d40b50106020040d05d00801001409060b4407968248082c0d1509590042c4005a2016405410740076203013070000f04442c0d21030006001c04805030004160711218010788522035200c1700f1b1a13020411030100103050002a00340c050301400c200440300d10b1200c91113802e00f03840030f82c810305801040507206400e0f24906080700305501c902038100380c43c0440c600e0301c5584d0188145030102c0c0c0102d40016540030205500100b041d070080041ea0b00300700b554155070351180ca86c541709000e0401c01c2000d0701400299682031004048a0400100703d447d00400100065180e422a01c2001510700485000540e1070401c20382c03a40c4501d41c005d101ca040c150424071706030000e0452b03184a0036401e4040380d1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 489111276 1250 489110026 489110029
    0x9041a15060a0503090f01110a050a0306171510080a02060d02070813030c050306010308040b030910180b0a09020d03050c010f0f0f0507020c090105060c0a02100903051e070e090309 79
    0x6002c0c0c4041680c9040c1c0c0c903d004240700b441c1844600d001c1c1e409a02d0702c4005220040500d007914600c900a1034140ea9551821404401500c03007034214403810000004292801c1d81c00080c103942e0340035050b080c07805e2940c503eaa503550302000d500c504145900003024040061414200802c004003d2000041c10169151100100742d081403001d251841c02c0170360148240300d4140700036001060200c009119560440d90380c44024041c0d4416190190400300229a01c0321007803104400c9042280710802440c52003421903000c40041c100c0603100113600c00c020a0380070746035002c4c0c08000f90f005016541c01a18aa408840303507070140d186854295a51020500424180d014008856640030004600e503e038402141c0c0413624060264015503101041500d820344503804007604403801245c43e9902c582590040d1404c0ca01501c500a5200d80258442640650840c40c00c0c401e5074069422030300440310390918041075030080c80c5003d2056100080c100541d401203000035911402c0c0a0690b0300f003445010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 489112526 1250 489111276 489111289
    0x30c1209030e1807050f030603030705150604060b0f04060503062b020103141501051e030a06080f030408060406020904110712020607030c0905040902031218040b09041a15 75
    0x380120005118503441244510b020300035844070b01c1c15184440410300342510040d00b10310034410040044040030000071034a5130103105491a0b03907003000a85011401509072210151400c80d0014460342c5000c00115403014901c095508260141201d03a140c40d0420b00103542c1904020316403940072501001e00301c156104815406289001c40801c140c40d02058400902510030708a52010000791a50401c0580701140d040721003550001c0c00c2581d51003402c2400740c50340741c40d01d0540e0714203004000b0900034020f5041e07201401b2140300d2001c1c0d0310022003845039903449110740d01c0f594000f584505d02080c0480c0d46a0700a152030b1074014400582d0840b1404010070607006002e050710756010400392481c3c2182c040c4441e030307800089860200300752000058050314117001e5015075801076566230005411510100050450380b00c041c121035440711052280400740258850a03180240c0c1000362034106814040c0b030141c0102e030b00010f506854030300110f60003094100240603079074a01030b0550700416a01d915 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 489113776 1250 489112526 489112541
    0x60f1e093706021207060e0f06070e060a080601230c060105150301030c140307050a0602010c0e01030605030a08030c0c1603060e0c130b2d1207030203030418020d0c0302250210030c12 80
    0x240278013410b00d0b26203006450100000c0102d805641c04100b4510100d5000302c00c154082005d080c0303060041c59600c0310584006100c00c1714030503144001a4600f14400c0012441c1c100c400440b6a264103c919840318400c6000c03e1100520b0088404020300182075040312020030303050090112800b550ba07820010720080e54540c000405030759074402241900b0303401038880c0c20b0b0520a080500c1283d2408001ca41d4403803442ea006052030a0210110300c203055040c080740c81c110f0084040301c112520131078640f140c1d001148400c4a000e031510392100c41e1040040b40380c4c4100000100720341285a149900c2001070481d0080da942d10400302c41c49203003400d280c1052004c08410b0f1780d80941c00c0c0481d220510850442078034021110340d00074501000107940002c1101c0c1550b0301011f141582c5003803a40844082d01800c880100224100f80311104620b07455130140506810201080c00c455214510341401d40d0340464000c0d40049104805850310360283d00424019045403420112501c0b40d1010b0740c0440f147d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 489115026 1250 489113776 489113803
    0x41203140a0804020f09010812070201030f0c021e060108060c09011206170d0203091f1806080a0f0207230a020a0e0106020705060f1e093706021207060e 67
    0x689043c00190309000c00d1005040c03200781c6140f481d550600302030541c2c0700c080c16106072041030000381d21000c6900c00c1c0c100c4003d41a80c14001d01003058207500103034841da184400e600c652001c07080c05032101500042c40c0c0c1d041301e03592400307070019403110020300c4281d50114401c141400036042e904012059507205034001841070015510790303040304004d00e90500880c00317044011544140000880d650302e40c0802d240c400900c0c4040e04c1d81c0c20030700b20240c03201070040701d0400c641c01c032aa500052503900304012510401003c0410000d050140c510003040b03020303116001d00680314030b5030311058480303401480c201c8607034188080354910002640010080c440079002081d040752480010011207804001150180008031a901c2c00c1540c04503070900c0d540104250411314901404084030b202072203400310f5540c000c3c050f001088107040010320705e9140411500303c004d18000c506444500ca0648804d4006139841603010b0244540c6204001c0e05c190030125040c0c0e41c1540d11059185a14810032100c480c0c0c0f0f55 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 489116276 1250 489115026 489115037
    0xc081e03130c060507030e300d02010501090501030f02011119140c03011413020a0e04060902030609070501020703030e1c0506012c07051e0412140111041203140a 71
    0x124686400551500da00c04811300c4070500070b403000690055172031071020fa03080d681c0100b9018500d105520084a08d42c150306c03285100e107190358682601144207014080706800030b1203117903aa12003200450f502440302500c950360711000700f001588103c28005001030600119243c0801000c4c00708041100b8150803610b1a501c110909540318090080c515528021402000812000045200c3e0031000070075240c5030a40080d005011903884044850141032140d0300829245070503d0070100510381020305a00c6071081c080002c00c16076001940d0001d54006a0141107500d02e03660307040c0c40d03050315030b0140c561000b9081d2068180301c00c03260b10100c54a0050000302940e524240d520360700d0081c480403181610310384005a0508880101c1041c3d042141b83c03400c56034540c0c1c01d0030340504013481c00d50690941200041d00180840c41100c1803140540a6516a00c2c2e01e200c4ca08070a00300c0e0075503490900703900402e210030081c4c8a002155029494005e04084890442c02d0000040c2503000700c00a002281 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 489117526 1250 489116276 489116311
    0x72301180b1b01020c010f1a0901080d030b0d02091f0602010501030c0608041b0b040602010617071205150405070e0604020a0206010302060901031103010e090613030c081e03 76
    0x103034400e080560582000301014001400c0007400005031091900c903200c030301808201c00c504900309604480307004203c140204016011a01e004001e00001074461009158010343d40346549402d40c0c0250407501514014061007950702802c6e00500b5900b95155844040c2c8244a005615600e601e184194900e03900d044d00080c0411032101d00a075581c10a10441e232400c001480041c5004450750251100d60a011905a895241c417401d00840b00095900c00240800e000507240780e10350140007561841e4000f805000d0300c03408803a1301e1006030300646510381e0040c0010858080807074540d2801c0d44c040c205882284688111002c0401c070192000c8036181c0c8000b9040100c3e00c0d101030840d800410446080d441c4c201e901000035079070f80060001034421200055942c4460303002c0c1d0300c01a51409841030080c1c50390303910b09104030340e520102e03403801d6640102000035210b640d50301c0b01821410760644900500c440c2c035803540c1d04240c0128005c418503c002801e840c2018201c10003451051151071017040246 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 489118776 1250 489117526 489117529
    0x40609020a060809060415020f0a0c060f020a1205090f060f09060c0a17070201150806090606090118050411130b030c030d1b060f050f01060311030f04080c0723 70
    0xc01c20b0388507408220080f0180120b03000701241203600300d504a6150804054040305680080c4a0b0041d509003266001509985503070308500190348440c01000208807a00150b8100d9046c2d03c282e00904001841601001030203070950380c846600103c0340011119100c3d40108902e180010030749070b60000d8802142000340e5103104004807544000f10000d00ca0414a12283c00b4140c04c03d001450903038200320900007810581300b50b00000c1e40c069017111292140d907030f0b01996034403010155480c0015004640c006045400c149980504a507005140010340f802040d81d4080140406081100c3c503084444601a00ba81c4103007000f0100105000c1c00a04189910105460000041321090280d040203090f60111a04202450f800840489201d05511100d00c4c0007402440590300d560103e03441d10051205000d0400440c84c16649562010040c7c8203c045041c2c0040c08100c0742c6840400400c000100042e00302000380030310968450866500300c1d16605041315600c0e45520501030008007541c0c40046 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 489120026 1250 489118776 489118789
    0x1e0a0b180c0105091804141002040608100f0b18130b03010509010b060d0c1e0503161d010c11180a0b1206040f02060409021201051e03150c040e04060902 67
    0x8210742401c2681c039100c0d43c00003103940318881c52000c114404600c000030301484043c40003000340c02d000c642a03440c140301c1c0030302c980000d421a001e0000080c480d50001010382a400000000ba1000c00f42c0c078012061400f0070503a000c0c3e1200244004c43d025501c000721040c1c940403e0344000052509020a004041c2d405060841b000201401041e0703042405001082e20784008035a0041103844011401c0882400240c9029150304100c0044c60f0340b620142c01c500713900101071809440ca42c0d00101c4211650f132411070b000d160001d1107d0755180020b180500560040c148a1035080c4501d118607070307010021000801005c8208540400960104100b00403c0300c039100701c80c104031040300c4e0101c0001d1800003556841d90001d000804019030503500380300359903c903819200245400d8509660320000c4200001c0d801200303115844c0181610071600c040514106c0c0001d0703c60f103015004000e5011421071404100070003400300300040030308010204489500301e86291186019400c041034011851060203034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 489121276 1250 489120026 489120043
    0x703200706030e06070c060b03150f160206071d0120010606141303020d0201020f030714120f0904090305250b1006020a12020102091806030708030a021e0a0b18 70
    0xe00780c0244c0c003004183c03500b09000c0003d00381c01c04000294401c04001280c600300c2c0d164901c122510304101042045d41d85120b04912902032070888107400341c5041803d03640c5640c1618428080b6058102182c0c1c890100d04160340c036100c051600e00492280c8c14101a40c40f014040030301c04594464200b4094250000c00307414800300130011042c40c000600050140d00403050200074440c44240400f4800d6a200304010088040c0540c2940c1d541c100514001d13030441c0c06804034108030300031012691400700c281d6064854030741c7c8c6404180e203840c2d01202004020008458100d050010500460358407020322030a01c6140c81003c001007034500c03040d040c1600081030046c18040e85d01500d641c103110061380440c283c1162607201842c52a90490070900381c0c0a4002d60460035001401e44c4406030b01e440400c20420f0099400341c06540c00350741c980256980300d00c501e403241c102581c018040725048440c1d10072001801c58030f800990340340c010640c2d59660846010b84140f02c0c401038000c90100080424044d901 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 489122526 1250 489121276 489121301
    0x5090c03030405010207030611070c12120f08060f031e010f1508030a0f0c0501142415070f05010c020f071710091a0708100504110906070320070603 65
    0x5080c1443c040001b0b41c5c0d281c0c20302005250360784400282d052040c0d170704250344429038808a10713078006407188061140c1c0481503100344d908008650364a4000345c090f4850002d04081a03680c240996501418005015a0039001540500c43d40c0200d004100244414204880a000003c0303000854104241c054403141d802e2644014003195040013007038000021030302d1645403400c00b030ba0081d2020701d05450301001414050180d500b03001400d0265038012044a10440b0301562807000d040100c410380c3c41104001e200c41c1c1c0c100c092894a18024410130b000781117445d03c21a640c4120b85829034555013540c0c005112030300542d0203180800900f1400f841000c0260a6258204000d9580b500c0720503950340040300e501c108103544500d81d5060100e96031500000642004108900c0d0600d088014a0300504031540c080c3da41c24a4400301d440e01e8640182000c1d07102914031030b400c10b04d18004025023a0320012040f811700c14050030000da0014840c0e00301d05030340c0c0580040c00303c3c1d0345803640c0030701030354a00b02054 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 489123776 1250 489122526 489122533
    0xb12030306030d210c051e13032003030d151e0504023103030e0f0a03110a1a07050d0801060f2a0809041404030c0807050703020603010905090c03 64
    0x25042e10001501801c08403145040319144014904000e082c00e00c1d07000328000241440340903c00e00360054000c150058071384504030445142c448254200d40160049030440c41528034040010031401c0303204005591701c11300045a42480d11000030714540c0312581000b1540d8403051280c07150740c0c00003803140003410500382414010700045070096941d801c0c0c0c01807600c150303030110b034030750f0038031050034107203840d000120080d42e41e105040780004d01012091100b1000510455201d40007424905011441c418000d4150302c0d40d1411540e941500100d04a801340e008032500781d0010b94004400d400038a05000c800741c0d25a900e5803400d2046c01d00c0c00c0504003505110841c8010004554400c52400d0510301d1440c0c010f9441c0c107140000e0070940d840448079140f4408510b8454103204501000b01040f2908490800412a00440100c0100400ca0307000e000b04034840c10100c017203040c440c000e1501a11401c10f1313803261070b100d600240d81d0360001e030004210b06a0380c40c100107280030100000c081d50b82048005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 489125026 1250 489123776 489123781
    0xf02090901060c030909140f1503121804091211030316050912060c2701020d180b0706020306041802090a150f14010207060906090e0c1b010b120303 65
    0x1050310254184120010403a92503024024140301d5050107014100b0004280020400e007044110b10901c16502407a11904a1001c100a0703a0f40815911300104064050a120b8007d0060800300da000514280500c0c0040c0807410b005540700c0c840d040810b072242d00d1110803201403d400030000d5680044031131050707004006000681860003103410302c0070f119162055031980840d010443d05000303113103040385501c204d601748800c0e07100d000050260300780ca6455035981c0941080d00b455529500d5601540503802c0181010416482a128401c0001d009602025101e41d07400044406a10404041c2d450b03550100a22030907140501074561200020a0000000b00094000404101000d072400c4007440d555850840e910003008007410042403282c1d442c69010f66500d030059204916444218014094060301292480c018424003040d138089039120300c0320a08160308900c04d00c00240506a6070002800f28403110000c5480000c001000d42d000804d000c0700c07101c18000030000d43c0c0c5040410750414800c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 489126276 1250 489125026 489125029
    0x7300507200607062c1204090c02030c0d0f120e0c06030604060801050c0c070b03100603020d060806070905030111070302030322050a030201150506040302130f020f120405010f0209 79
    0x410051540c0c0c1e640a424640c21400107206200740c0c1d0f001000c0c0b83c00d2400c00940c2c14215008030324810492102d00702007103035504510f51280c40404444000c01011b01c000e101191441d1302a03447d908550040705d242c0310060014503d000e40000311040000c40b002c003280f010a43c400300b00e000c200b42e080d5040c08544c08007161140c46001c0060068064100070001a0741980d5607085400203250000c0200010b0400c8510889070364010001d03200f55101d405000203072184a0022a1b00c00c0380f01c408050b480724105001100a5402030001a4030301c1c1e110000410258820f00c81d00740900601d44031700b801c00b85002c2c241420341c8c010381e180c1c0c1c14008041c060040442c2d004000c8a03407000501d114925050318501504512820344400a40305110b1349000303504064055201640c1040d0301c00b0b00e000521b50b10020480b05200ea804000d4000840c046401410301c5d940c3c0140018411103480941444803003010911990004c3c0320701c83c0c0e9411000c040c801481000e2240b15a6a40f10800a6241200704c10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 489127526 1250 489126276 489126293
    0x50c03070b1c0b010513090b090f04050a1502040b030a0506030c03010204050604090f0204090204081b03060103030c0b04061103070203041a0304031e110a0602030406050601020609070b0f07300507 86
    0x166005603d8855200c1d050f0f110b00100c40c08400405592100039803141c00303c00040542c10102405080e039000443c03110030001124501c00c0340c1c008020203203d43e060747c0b164001800542e200b201d254092001040500240001e035110301c0c98814006001d00d040c004244c03910506400c3d042c02644100310500c515201d070000c0700c069030800080482e00181c1d40c40b500000707200d158401c182c1941b0104020528410116a0450300704444448691100d031400416881d480217100c02008030f59005081d42c001415042e44590040c01040c000500a03610802802c02e80e00072914400160400501888036000a5a00304656030100110714158178040d41c01a06600d2102882d540d0740d00751101c92906284034603101d00003660b01c9029100120000e14284010f5001a90115895414400014259440000c1d607511070400c4400419482c1c0c500082d0309043da0003480c241e4110542085800041658040407060724210a040c001c88402d2107152506402c3e140400c4074200320742003240101240294 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 489128776 1250 489127526 489127567
    0x14071d060d05061618030309030c15021c05070501060f092003040206130305030f072001080a0b0109051f080105010206010326072907022a0319050c03070b 68
    0x1074202c10074039000c4c65050300c408a400b00040c801102c0003002008043c6d1040c2c54004483c03041454985143c1c582d158015402108010032005070702034040421084180d0100381800360032070400d1480c04041386c881e2425282660020135103200c803800b00b00183d800d00d11442c41200f1148000c0004500190410034462002800191181902080055001d80031801030b400943d841012a69600e00794500b68220382c1111200b680c0700244020400810500c03601c0050803100142e5944240f03540e004141300c000d0150581050401140c2c80021541d51500792000288181400e0a00034200700100700905030034051f00180d0454105100400c0000c4c40860380089440f1010130081450f0401108441207000d000d4001c0c00340c11039240346030184101514a016410710319210010725a030f03212401c0c0d98442c4103040f10104d1003040c1c904803000710840c00341c01011480040030740d8800c0140c12503030101c41003400002d850f260002d407101c0c5014070701041200014824203540c1402c1002e01841c04180d5000ca = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 489130026 1250 489128776 489128791
    0x20703031b23060402031005010b0702010c0606172a10050c16140906240304020a0308130e0115210f0f020903060c0403021c14071d060d0506 62
    0x24031004010440200c2151581c40b00c52a0000000c00c0e045680d840b0801e44041e40640920401858181458040c0b40d050b504c2c8103400900d4101298011100800190750076104680d481c2030100d11003060360101c1490354458001080c1442003031050303502104440100a40d08008003104080300d480d2101e00034030424003804d01d961a100c0d04640e00d420714448400213418400f03014030100b0340f40301c910702c4104124070a4600414a982d094180b262035006540b152114450140b2504c1180d00420003c5a000e40301400040300c09a80769294002a0000b850041c1d41d00c0d0201d1041c043c0f504a00c106a006140a60501060202c50070001d0101c18510300c1600c0d0341d8080750000c1c6122202504443d0403041400070401c24041014032410003500030001a5200e8090600818800d0b0b130030750140d5040c1c030380090007200c0c1c40d00e4841004141e1045040202d4503c60300c1030071001100c100313102c0080109507980d002d0407025403c4821441c110001440c03544a072a403503680d60b001ca080050816800481e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 489131276 1250 489130026 489130067
    0x1d070201090203071d070e150901020a02100c14010908190c0b0c041406030c191206180506060a0c11030a0503040f060224060405061f030603110102070303 68
    0x110104100e0241031808000381d05071003400400541c0b0045504101601c4842c40c00c0765850f900c60001c21030301e0440e1200042e03400b075035038191010301f0100d02c0300078006400140120348aa4146e54080f075443d104070354242021540c125500d40509c01509882c007a03009142d0007c100c0b081e503da60308046c501810240c0030b4088002620401c03401d01802c0b03214030a03904a13002000078601013990210b0703603100b4000c10f429220850202605070901c0d0090702c0c0a0b042c1004400c2c00d2a01080c800500b030041c01c0f13804c1041005003c1d81402c10800781c490701c030280160705848120160400c0ca21800c0c0c4070080c00c9a4007a250400400c01d01b0766004151449072079201c11020051040c1c100003034902480c1d480c0c0a41980800140058410b04040c4004100e8056400391740d90030b207501c203424404000b81c10300c00074660201c2000401c50700e01684500d6000d480103020780000f080b24400e40c581a00301182c03941c0402e0340c0700001e0080c041c44840440341030000f440108146c1d41503a4000b001400300550804000d034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 489132526 1250 489131276 489131281
    0x80301060503040c080303090109121103040e07030b0a030507080c0a0b120c0c12070516030305070b130c03050102030402090606030108120c033609160e03010e160906050a1d 76
    0x441081003d00414028003160340780c1c08c00a12840c000c214040085921400000f09000d0320307400342500301b40600d1244050b40c01c0519003211200340003802090364082564402c440e15003541c0354200c2c0302c045c600031401000c056003030054881c6800100e048292251401c0f010400000010408464042e8143c0014440319241c941c5280d84601803080301d1400c1d40076040c88402140418805011214090804c031040c0c83d42224495031400b036140805400501b0810444010411000c0b1254010f80307007404014004090340c68106e55190303d90021982a50004188000d51404050303c03034008004a581c03514552405a0b40d80d9101d4442050746030385040072030065080c02e41070080e42d40240007610b01d05600c00411100c41407a511210185003c45024140200340d414040e0001740f1071100000180303000c40e15002c0554040c40012202507040d92a00342e0241c40000a001d9944103c4082c0c00440800341000e41001c1620300941009004c1c0208002c00c0100c0d6414a40000b01c4414005000c1500d8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 489133776 1250 489132526 489132533
    0x120610020109051e060105100507140a0f0b04050d09060e0f03070504020708030118090c261002041401020a0209070806120a03080406051e04110102100e03030105040c020a08030106050304 82
    0x104002d440140041c01255165541c0b40720701d03251030f04401103075015160f1581c0c0b56000c00c009440e0064014002410901c0b640000a52690500e42140d01700411190880e20b9a6140f20b0754000c005801c0f103d00c9051030a02041210400942d25004402e0400c1d00c4902c3c28200c2c01001c00d808180d0141c86850400b810030100d40302030101c400585806001950385203040e0410441e40d9000b886410b40c0605140340c2c03848045014814001c4841d800146402c1d46403412482500d0355001e8620328030030b4058005841c006000c10064120040d004210242e20340385031000d1003501200300154039042d074002403090030059030b604041070f50210490900c0e00315031300d070700380440ca001c3c490305c1142805120342da048800385904070741030f188550321402060002e561104050b04503048113048690246040343e001c0380009041c00e03044012124184101d07040e450f0f00c5c00d0704205079003001010300025040040140007504240c01003e014820500041c45100a2030340c680b00307148014032820040180100104040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 489135026 1250 489133776 489133781
    0xb03060a11040b0c030c0f150a0911090709050a0506040e040b07090f12050d210f0b0607260705100209010311031905090d120b03100606020a171206100201 68
    0x242c106503401e96264007665201c190b6a510030700501b0b0031840b8a809821000300e000402c12481c00302004107506948032242820060020904100d844e2010340051030400d858100e810b0740308980a9841c3d40c89549410103000003110240c00250045038100005c1c0031761011200403a800c558400d00c0b01000d6682d050044a40318940d0300a822442908000014102c0b01c000043c1c0031503018900343d940c0900c3d894010740c3e00500c1051507940364101c0003c0b002018900f640140c8900900c0e10020800c5050707200020441d81c441902200c0407010b42c40280c64034000ca46c02c542c10301c0140301e855803a00c0d9441e10792a0307503003840f50010071809400041b0b0711516407194006a014030500510b0b10b41340c0c00c0c1000040700034035240b01c003001c3e942d19110000e00f669400103100d0001c4181030f02c85d100890328241250307003c3c244813131081e9054400c2d0810050541160701c9280700900041c0e02401010780b43c0e181029108482c007010400f00c0800b440703216024030300126000c1d0003010841c0d0094000906407016800f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 489136276 1250 489135026 489135029
    0x15020307081303170307031a0a12050115080a0303231b1c0b13092d020d080403020907090e16031409030901140c07090e0304030c121103010b03060a1104 67
    0x34481c10010302c1001144d448025500915041c0c80a2110113014070051100c501c64aa080c2e030303c0b042c1518204000c86030200001101400348002003248603259001c448984451b5010302029401101c0e000706142d810b00c1106182c8182e1825545290745000b85103a844001528085e4079a140c05103619a1940803000c482d00185810100d805040140b85000d00a00e90000c501780510388002c0791b18140c450300d00c60244001e5001c1300d140342e42d6400b500c44d5800320a07810010075440d40b1840181001d659181c280c110403911500549036203c1c11813040c08000b00000d0039040070300421910502584c0942c49140d6072102d84109518402d420203007003103001d880000025400c1186040c140440c042d8084010060403000382ca400000300a2010a850140f00e40d4141c00c50507004040c041c4041d4109420006c1030345200d5049074200380e140e440b504040e60b2507038040482c203064480c0343e2080100f01e80015203085c00840c000c000c01c044030000f20f40c0381d40c40140385040041d61031340344201d042604007c2c1c40 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 489137526 1250 489136276 489136283
    0x21504020d0632100e0712020d0902041508120301140f0f190311151b030405090109061a040b071103010612050303061219030f1407030806040615020307081303 70
    0x7400b0992407158010625002e50310000c41141c08040030400032030b10b07041ea90041006641f010103030410021901e0017904541c00c1003100ca5140c60034580075a40d24040c800700503022390f03040c40e07001c0d00c1c1c0328800b458044000a0644c1940c401d0004000c1c001c140313101c05181744011341c0e20300c1c3c41d091040d000500201c3c0c81003807242d002c051440140480342d540c6802c4010350b44124100c1d10b0b20109a020440350b441000b900d030000c141c080001070240e2004032601c00c60a1006c1c03088a0805d62120005025008260082c03204655180310030800680910801d440d0001e40c0c000140c034050519003200c140d40314030540078000350b0315031a000754640ca003544194010300b4a182c2d02c40c203201141c942540c42e07600c02d8921030b00c1b031480c00c40010044000412005500112210b4900d55840c490780d00307a5002c0300402541c0c00b07000781401184030b01d150141c010103182e4402d540c0c040f26441c10000308400c82d2025005410741342620842044c0541e00001203410554210b16440d1301d54841e02242848080c0d40d40005 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 489138776 1250 489137526 489137591
    0x1201230c0f210a0f05010819020120120c010b150405012d09060e06040f0e0a140a0e011b08130c0b0409090201021015060503071b03020d021504020d06 66
    0x401c3c403283d10600a9004ca80010300459a0383e072803865480c0051680103542c954140b2000b4010740c0168440e030000d00d445084688200c40c03a5003007600707001040001c6002c501d07000403517001d540c1742803140200f9881d080701c00d03a4240e4501135200480303000b1406030780e040c0403003031449585a03182c6080d028408100a2445540c02c68490301c003d0503009503100d140c0120340407888407440741c03034032505440070382d20705540e40300b00702c0d1800c10343c40501c00e0090a603006403962210000101105c4c80901d500c1405510f0000c2030a00c1c081d003c041c21644d107500e07444501c02c00380810b421000e60060700c80f60086c0803007040794520750031030a1640001c41e045d440780c0c01c00a00090009001c6146d43c100c2d440d940d000b6002d4845400700104143c3c140c0d00304800401030700280c4541400100e0068019607004121868005a91401110700c29040c4505000581c00344e88070707040320380a0702e50401800701034000c140352134034943c20594040f17001c15900c440005d0159803201070300c003000070200100b14200514050702 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 489140026 1250 489138776 489138781
    0x109020a081b010e061603110106080d09060215010621020304050c19030c05130209030d0905101106010b0a020c100809010501141c05010b1201230c0f21 67
    0x1820769912220b8a100c03481d1085124054141d0302540c0f10500400001c0d0040f80340016050041c00c5007031030401c0890a10040390740f06440d00750b00f40329078009003400f07200030000c03400302c4070010306030f50b40716401740d003c40d0f00c0b51303401d02c4080010003c641e044400300c0c00d040765000540111850300c0b41c4809510074203284044108000e108000802d140160304c1640c4000c1141c510301007090b4124a50b0101403d540c1c42d19100304524105403142e001c229018200050130503100100003420300c6501030b041c20001d401d2400600540c0b5180c50007100410040c108101d04107002c51a09407900c0d014810140703e91008105030300c00794028002c1c0040b03001f00070440540744080c0040034041a800390303555902c40d0b19050000c82e42094030011052003c600034140b002c039100031000191001c44481048a0a54842829007807a860766060820b8400003640045000c0c0c0b600203114000303070780c1202d00211004c101014484c4d03071105a01160840328070060419901d04090600e8455807503900c41ea02e0400490004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 489141276 1250 489140026 489140039
    0x60903010c05030a1503020108070f0c0209010303050703120203060a030f080f190306050405010f051207050405181513020603150916120903080a0b01140d05040b07090806070806030109020a 83
    0xf507114030031105040051030440c1801030010b41d03079400003d02044045001c80d8440e03018030011442c03d071302440c2c480034040965010031800792080c0e0045000c0351001c9400700c10190005c0201c031031496440c404600b90701d011310010750015494440604405840000c070070074001200c0803604003540c0382442503512662420800c44040442d6240342c0000d00c0c00101142514250007014125030384c41ba414034500e4105800c220001100144844c11407103468000200e0351503d004a9110350f5045220b0f001c40712001000c941407916005600c0c0c81141e0010401c10b60401d0708800161180e010f0f140a51291355080c5207240b941c503081345441d40611340d14104507440000f414400c80e079005540d2045000741c9800080300943d00902c0c0e000300410a10f0000a1604030240d0001c2c0c528141403404694580308103000450b1607005c0300044480a80310340c200424488104860307030b0000c0283c5042c001051802e24600c0e115800178103200c1c10050303214085185960300350001d403180c82c3c004000020a6a80702d9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 489142526 1250 489141276 489141287
    0x121b21060417070503040504020906070c151209080313140a29090624060d020d0e2103042102060906131104050601051329090f0d02060903010c 63
    0x85044411044140da016030818034031090390043c40d8004000d60400d401d10302000082c0d0868182d00760411012300c80680450b01c12181d42004000540384040c019425540c010095501d940c50030080604100c91341e0300188a80040313950080d01240c0070f5a542140e880d200c4040c1d003500d95404018842c903d0158240441e01d8070a4046500d600840d1120703503081805081f030002c0c12074008180c1d4010600090b160741c80500815211080701c1c1031409401e90040c0012030076048840b040840c0341c1e000c40c030302400b50302d02e10070362017091325410040003281505a02c15041d00d1803d9045162000d01001081c200100c183c2008280d44180c400b0700004003580e100250b031800c0481c2ea12400340314480101d43c511a412580100342c0741c0280812010440c408144005004064621410008100240d40200040001203000341000c0940d05000381161640c003080d0751001601502480001c01442120390b0755080c41c0c00348410203031000c408a00d114000101e081c010815081d40550030a000398014543c4038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 489143776 1250 489142526 489142531
    0x40b030a021c0603020904030e120d0908010f05090607210c0201050604050a0c0906050309120a02150606090d0605040f1401060602070f05010807050d2003040302010506121b2106 78
    0x5400100002c4011101c042d110b0611001c0d410603000c00104020922481601c0400c0c0006007034074503441444a801460b041d041d100c0c050010308194014030041c0820b00503003030340c210105428452400e1062103661a08406032006d028000c014140d0f001c0e40d20071641c092540e0141c418100480c4002e948040d019003400c8920302d00c6680b070030780040c1c5140b580b8030808945402d241c0c4d0b8031b0304090030507109503860f90014181c1032a910a401600b102c2e803c0788001131152880d254060403602c2184100c410760024050400c0f80310b890140700d00e40031911070420340c1800d241c0201022820740c0780d0b428540551040180007610038000704511704030041d41500403134219542c41d402c56203680d079110182201d100c100c2c010203002036400300104601d43c0c8030364060000100482e600042e07980720140d00b46032011805148000102001c4200010f044e02031080d1603018070156035415100c191244050344401c4494414020410280903480241c0c031060703040000340140002c45590b031000d81e681103a544508 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 489145026 1250 489143776 489143797
    0x50f0307030306061b0c060315090c2706120c030f061e0e04021003022a0d11061e1e010821121308070f03031d070605070b0705040b030a02 61
    0x8141c5d80303c0d5414802c01002c1c4415000040ea909141c03c082007100039080c20001c45184954803d00468140d03014800ca074080741880c4c403a4629111920040544004445e40140381c410301c2c40c0003009182d4000c10408550807080000050050080708154000c0c6101150900d406141000104205512485030424042484021616150b984030754800c2070b101220000d42156a030841420701c60b000f50060180700c5000c4030780003185140e165841c0b0b0fa00c00b035011056900e50203d50707192086500100031030094944c0030082c2055180041050131101da0980b0203050904840c00010412145074040803402c9200303041ca0045942d403014925a1600c0707081104080303e1034005020300305a555003c84203229000e00c2d1081c00341e41e48c0169a01c02c500d036844151041101000b0600006000c07105d51040280f007a24006071070100c0c50b64144031174090003858105980301e0301040c0310840e0084140e8024135445840c192650791030700070444850081d5031041e0070360880401800a281c1c8160080c0c03610440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 489146276 1250 489145026 489145037
    0x3060e060105040f020f0d0f09021503040c051507031d0307230406050d1b0306051e010609050d06020d11040f14190e04030309050706090e06030325050f030703030606 73
    0x14040d01344c1040344142c10340c20b266080104680003119005802c21651209141c1c8002200d18094010401c0107541292207981c01034000100000c1140c0d1540c0c0e20081c010546078003511496221628455110748a400b070140b00850741ea1b0303000403d075010400c00566000d415103d07d40c0d66001a1303603490002940e120b104083c8101d00551a09043c403540e001c0381c80050003031201e13079225102c40580404803c00b800140c51000720102c0400e8203401a00c1c029170400c00b4040c419814520b2511100a042e00001c04002c441c000400c072940d510100e1780b020903001140180d6800c40e0000480080150f0401010400d001090000792a0307080b0800508a918148a001c030001d256800c00c010480d0400c01b62840c40040d0b48140a903528081d42d0992080c0300e401c0001d603140c03664940d42d2500350f040c0c0c07003138002034002d5106110702d10112035900d42020082c4d000710b0a000601480031011071085007440c103e40346d03a91041052160400402010741083d50981c1e40c0d074a400e08005000e4038542c0943c10207d103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 489147526 1250 489146276 489146291
    0xe01080a02130611010906060b0417010c0e060d090b0406020c06070c050a08070203031c0b010306080a0f020f0102070b0a2a0f0b130632090c061303060e06010504 71
    0x203000b00c0d03034406800110100d00c241844401d40d1010b000b0400c2c805199a101210b2000444920440c40541380415009032501d103005416559440450391042c603d90420540d4461a80c01c1074155091080450382962150000c01d0140c1c0105003000010300060010400d10007031040c40e03401080d5040140701901c4150b51901001d940160041400414a501401101c8040386645000d84a42c510003400c0c0e80c41e00701c500c0b547c241e01900a14103a02d8880d80d48001d26659a01413081070001c01c00c031030183c950840355482d0140c1455003018064000c81305501d1140c210782c030900407003000d00315110700982c1310030190340c0c000c0035000d4462045051864400c8080340385440740f080c40c26a584e00041c0c180c00b40e0078640e184214010b01800c0701e0201c80c44203400320009a0345005040d40b103420310f110601100a204108408011300310b84074100c0300003004c14002511408100740c1031180041d1203095486100100f40c117030144844d800034040038509408494105004140e00b4100d03142242e0138080701 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 489148776 1250 489147526 489147541
    0x3050105120715270503010501060c0804030809060910030e0618061602030d0e03030402190b03181e010504021002160509100807030506071206030201091e05100e0108 73
    0x4034a51112600300e6402100c0801c440c0b80c82c3c80900e4404040da02d803194220f94903084112007444266800021800010b0060046050912459005101c00e02c0d00100c0c2980c02c0d1103085061180e03000242c890100024844440d07140c1c481102c4000d4405800e43d80b1680325030f00300900038020190242d041d400f0300008211805803861104880a15080c06030003661109900e90f520b601901202d44154001805101401036075031040345916940923002c1c50752071420344100032501204a038202003601900e00c0500100300540e09030b0b540302e180b4401c445400007013481941c4c40d03d42000c501c2800795811400344070490740d064100c3c0c1d0169100340c40104103040c4221090381c5500d51006140889001e814041140e03161102c40190800c0440c04646101502c5d806140d0400c00a90400c0c0c88a40c40f0100b84400154020082c40351403103003600801c02c40c2e04682c0020130103801c900c18103070286820020004401d609800440c010000206420340c1ca2100903009008412109040d5003c66074410005081 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 489150026 1250 489148776 489148789
    0xc0303011701060b030c0f181f031b0c020d0609023604110d0c08010203090d020609030901050313030e130c020d020601080717030c01020310090c02030a0c0602090d050a0605040303050105 82
    0x1c2c1032828078060909100100741440c51308258000c030380180313040ca6240c115403200401e044050102c12744400e4994000c03580507084e5581c01600f240078605c1c00b00c0d03808546900501d4211010350444035500c05105508141303000d021b504101a510070400d0301d0111440607581c000012010301000102024081c07000784c201c1d80c0c001100c000e49480c000f01807540ca00d240c01c4048020040c4a5440e010540da02d0740034190072a041115428072582c002819554000e40400006500280d0100110300d00021000000e010740005010001403000e01d9808004260140813200030f9058041c0c00b00c201030a0300c2d80700d00060011a03030070300050b014240b50800c4e42072000c80c0444c1650310400040034480d242610743c1140c983e41d50700c06081c0d80814854101450300c04c2c00118003601121802c00d009034204030f408402ca45541d6803d00540d030040141c02c44003908a113680a0a58020f100140c44001180100780120702140340140355014a10a00c010000c184c0e0102e402140a03035010041c0d0703a01d6000f807004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 489151276 1250 489150026 489150031
    0x7031d0706050a0f0201090320240402010801120c061209080a0206040c0530011e0504020f010c0b070804050309150d1d07140a030b010e0405121606020f0c0303011701060b03 76
    0x254107050303080510000ba1210045007641c10301192126032b411041004446061114280261480c005002c155039000c08814051701c0102c95000003c40c0e10382d20f602c000d102a1240c0c2e41484000050400328040742e40c01b0548198019500307982c2e405040c50000c0d180d0000b240e040303450150000c80030501e414903070324098000000146040c1c244200309110105030302c0345450164250349503901c210003080740480c50001c0c1c80c80c0000c08151070030144100600315120fa10643c4c104444d8011300320105050228090b007110309414401e016480d1804d02504500c6480c0320383c0e820641c0d41d004041c0c0140c20400030001400ea00008000225800007030318151103492005400540c4a603d06021042e1f9450521480ea4001440070509031342d01d0303880e4944840c0c240c0c4240110722104040105200c2c05200b4400300414031411246400104410408100611071002c0c14140e800303d51609448501c504a452110b54207045980b290b94601e030389503440c000201c50200c15403d0a400103206031501d420b8a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 489152526 1250 489151276 489151283
    0x60106050f070b0a150806010e0702030715050403230a0815030c01080a0605090a0207020f0109052b14011508010203010f060c0206090d06020d061d07031d0706050a0f020109 76
    0x30302c2d0035025240c03801004009032800320b2080d81c82001c44041c603c150520340c02400202c0191000d90714114500d1020a40280b1540a54004000f2030340020013404010b448201ca01200080075111420210341c08290310f1030200d01c081d01591140d01540c0c1c91009851600801c1d41d40d40020b030745e030502d6200203600d03040000d605944454003041c01e540c01031041d02d511040346d540026890340d03102e000648414042e03480c06246503000480d1070175400d10400c080c482d0482820704035405450040031680f107500540b104210340c1840002c46000320480704540032400d811494003403400c074401c0c0015009203d00310001c0e903103003c0190005054001070013940e04960755410312a40c83d0b031502400340e0f000c0505040032030740004100514111941d412980d1240d8038003070b0b200183c91303803001c0341340701d040310040e030000080046d840b45082c004034030360aa035942c0a01e5a16010490b18a08282d0101d000d80204c80010700b400b0303120010070101d41c0036018101d01e042a999151202c4078445043c0d01301c0b43c8158010303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 489153776 1250 489152526 489152557
    0xb0a0506070803070c0f03030533060f0706091a010501140d09030311120105130e0c0613150503240d110616080d05010f0b0d0903021e0a0506010605 65
    0x8501040711032002d03652213043c03401c000030b0780340281e40c0d0150001401e01d0300300d0100b1396520900140791042c28540c41c0d01500c6090701600081410b0102e6502d0088141052242c01d0000705d0007403c506500c1901c00d01743e444202400206c0342031800c200b485850340c3c0d94520480d120710001426602c034000d81c603400340c0790f902c10f50325000034803000c0006085940401c1d8207064035003c03182048125800200903400c50480444140d50400f000c1100b04081d080f40092a507007071000c070b10b03101d20b030104091801d0f0104440c42c40c0c1d2241292010004422280c0c00040051a108074076450290418000c40c420400302071440d0b00400121502c42d8140d440130046034006400340000000100e100b1840c2c49000401001e080c2806072044914800c0040040708441890001c40c0900e061342842c02010301410380b5040e40c0c11014100180b18010340200400c0351a040e4642120340c0031b15000b404103040c1c0c07001804286094098030070304907a4907110510200d40c98459100000384007407041040e14055209005103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 489155026 1250 489153776 489153787
    0x213020f1c0c08040b070e180106020c01020105181b15030403050a080c12151906051c0608120f1911060a0606051603020f0109061d06070c08030a090501090b0a0b0a0506 74
    0x469510451070042c9402003138071001d1306188c14110782c0171802030a040c0e00910803d41140002405d590016055402001c5003114902624501082e05600c544001c140555424041c6000410401c0303200306080322104000140420b040c2d200c0010001c010345a00d50906607208d000d07134440d261081420982c0340070507a4011507409100b144408001d9400204101d001201900d20402032019a03440140817400003d0b812000400d130030950240000c2000782041883c0c42c0950343c0342c58180b1900b0f09651044001103401c040512902542ca01100d001410b032610349454002801e002c82125550103144900000508000007a001d840180d0340159542400c180c00c5c40031052040c40d44400441c1540a04603861169000920481079400e0181c40c001c191400ca44001ca0b448064a00c4848010b42000040041311070304258030310040d943c0114800e40d203544418958000b01049100189a542040400405d03c02900080b60003825036a07010420312500804001c0c8803e0f00340f00301600103009124 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 489156276 1250 489155026 489155041
    0x8070308070807060609060f09110a080402010c0b0103030323060a140a0905040f03270b130506030a0b030c010f020a020906030c06070303020307090b0f070213020f1c0c08040b 77
    0x207480401e1040640e141403030f00c19074075102540d00c981c120805855030360386c081040405000136036000b4a1088001c2100c0109000b034424a8881c9000100900000d14041021a4811940c03030300b046030403814114030f650f100c0c603006010340080845008102603420100c04181070301c7c5030f014054900240b00d0301065203804190313200f004000d00103550002c0d103060009641d01e540e00503548100e01c1102c00340d604c0c1c030080c900544a04034a84508111703c0001030451010305050301708030107032501c0c4641b1684a980c0d403020782201e126241c00c020f40011010041c40401d0441e034120040b0390004070f040d140b210000760011100464640810b00050740040400c40141c14584c0c0040d41044000e410b48000740e001d0004269550b11821080b030000754008100003800394481c030f002000d490030400c0c49190a80c068003511490007805400303032080038110000070010840750b0440744450701001c0b01c0d40d1070b03010120046450112001101c2c060b103080c42040032825200b4803d0f54890f960000f46121640c850b0704 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 489157526 1250 489156276 489156293
    0x614010203030f0621060405010c020604020109031b170d030605012307050a050d0815090106170711010501080109170a230d0516110606031c030207021002070302090f01080703 77
    0x410607600440a4170300101c4086074020b504810074150001001c00f402c04e443c0050840d034800c52240210342280040c0f000503a40408900b080b26000680d55914807202103020b0f14400d82c50780600d8080401251850b1000000f04136151007400ba500c0800c40565108015101c3c00004556600e9942a0f8070a40c01040700f007202800001e4000c00031901f4481083c0e44261030b03c516500d43c0c40c0801c144400700071214140d1601040c21440a031100052545810800b4010315070344069031410007590300010309518450104d00f4004041d08009015a581d1202203d00078001e03108244d5044540d03084500898a140c3d00301c400101c0329680f80010180c5203008001c110300c1030942c5c00700c40d070820442804080010b01805004a014101c0308500094444000d032141070078000414154002004000d455503000c11540800c1c000c4100168419158040c1100240704806009520039040c5010360945540010300700d05407803094982d0b03007158560841010030170700e091081071003540c04118184002036201c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 489158776 1250 489157526 489157531
    0x4170d0908040806190c02122104110411041503151806090e0a0f0221120403050f1f0c030b090906090d0f080a050403090503060a0209040614010203030f 67
    0x51800040355001075803551081c2d8003e80c4620815404881408a115840111841070342c056410400041580240294a451b041601e0000c07404010500d204911084a01c036020620071002003003442c03030107180c003103090700d0058151401240f400c0380c0303100f0b0f02e07500030121002d4541005000701100440034044015180c1a10b8103007400c802c23480c00080d0314000c1032050010700c0d001c0002042441c2040c14940485008801040030360b8042480400801e04110b0100f003600d030199a4410105c1000084e00020400c80b4030032040c88c4102c00042c07880402007805030041c0c1c3e11480a441144001e107107081da44422003000c0101d00301e610341d1106014001c95000c8041c04802d4103000c5010140003000030b032480f208a60103000c80d00b00500300205d182d02480000d610300c200b400c00030241d4202500c0182186001000102074a940745d01080030b1502801d0040001c207401411500306250a514501c0603401c505031803405907040100c007150701d004100f11000501b5041c2d006504554944650301c0385650003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 489160026 1250 489158776 489158797
    0x51303021f0204031a0403030c03090b0f04020609100e100e220626010c02010c0e041d0607050409050603122a030c010603170903060402060304050c06031e0a050417 72
    0x8100000004030040d2174031440022600001e0b4441c41c0a08001c0d0507549140f40d480d040524011204002440c1075011580042025030402c8040e43c40c0d00c0414031620448818a40c084414884160708507802000d20340b0302034040e1510220041791305410b9843e100c140203540d40c0680c02690320a40307141c8014a11000034800b110101d8590703903034840d400301c0324041c003a41e100c03089000c4c0001c0c150641c2401401d4501406100030003215180410092048001200701c43c8140e84600a220f21b03400c08003001c0340d65481c4402941c4a50914180c050030700c3e44103200301c800e10340c28500020040c0c54042440c002c41d03004d06030000e01e0400f40c240c014401c142c4440d4001d860200007401041c080004201506204c80c0003400003502034110b041003681d4001020309000303500e1040100d0010f944010541903006075054814540f00d031a10310f1f0113810404115601d503007103c00401000b0685500c1e03400e0205408002c1c8401c4450744805810340141c40040f42d0180c0764042d032041503800008940014a40781c40c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 489161276 1250 489160026 489160031
    0x9040b0a020706090c170f1e0703060f05090f07050102030d02161202030c010b0a080d0c08041d0106030605010309051506060d1a04290f0111010f050a051303021f 71
    0x2c450b50b40900b110700080c0241e074042480b000c180645003008030b4100094070440028010390a0803510144d4071200000020201c40e0440ca000040386810024140510b0340502c00b030010821055021000703000c101d41d400034600c00c0f40806501c120b0301250503415604181d02a40c5440000441c000181d80078440320095080802400008581d61a40558480702075501039552440c240952034292200c00d0b030306c1403003030107072039400c105520002400b516254040c1c1810b06210b0098141080e0b6409036030300000340c2c0070002c03174060541c01d185030315141a503086032403c10a490712a40110704803020018018456404076a0600204482020055028100134401480c10740a0000e1605440d51001040707122441020071412514081c0120104200e83c0c1401c01000c01d10808085001c440c2c05e07000902030070085110f091036920810000c103060044800a000c080f900c00a80001420202c4101001a00c5c0501050388050801061074416415500408810380f883d000b605900180d0419000142d5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 489162526 1250 489161276 489161287
    0x1200a020a02011d1305060a1509290703021f062102033903030304052a040e0c010207050418081b01090318050907050f0c07090614040f090209040b0a02 67
    0x342e80c41085c00e080840d070100417407182007140911079131018540000040501d0320061039202380c1c1c03180402c42111113880c00c0942d010500121002d090b490300411109601c400699841855000240381c1000032a5100e8034001083c2c170b0b603120781140c000c2e000d02d40e041c52080560180b0122040740f41c001c01400201a03e2609045c03640c40703124103011400610100008031014400360b07046a03042c22080070190080d51171403815a64081d11503907240c07a0701080080c407060a5604121b2a200e1068040014004110032050140e070350356640147e55140c1e0051040c2c4901282d02d060601036165006400300092811600c580d8604020340c2202035001c0c00c00d031321160760452900b0240202043c2c98000d469152102c0d003510240c11549150b50401070041d9441400e014030a07038450204e8043c080020103403526483c018100608001e400e9100c414440e042c050007294121089440f66102c0204480801281d0800f41d030810135114180d80180d80700403c0030000f00400d60128555070310100c440340061929 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 489163776 1250 489162526 489162529
    0x10903082118120301031e05120f04030605090a0c0611010f0603110a0e0601080708040503160303060f06020111070f080d0501090630020f15040801200a020a02011d 72
    0x49004464696500c940b03a01e40624002080c002c0300030101e08406980c0c0f8660554880c0d10710400340c0210707010900f1450f40d425007440b800380b180403901d485840c107142e07480fa4400301484d4150050302040e900645064041070002c0e200182140a680d0b100c0001d410b6a803900c2c5065485044892240308255247c1d02e84200741216486000c0c091031289110b0360300e00c0800d5003800100700b034507009005103080e49001d0040e030760381200c0215408a030704e00d00400551380b0780c6401c40c00c41c0141e003030591018a403183d003201011f8240d000715080c0da000a080700001c680d070b128105e0990350445140b510400c0c0030400100452207004110000600030385400f841e2842c0c5080d0201101ca0036800740b1441e540d030329400d005119600e50005000c045160900080701c441c3c45082c1e2807150a0fa900a00c1110382900030606501c848481e1000140181c0700c0d60f440f6a40c13203c80a000e05500c4d81e416004c42455800b41c032240350f42200307071180c10100f0780c01001c1010b500d44c0151254885606041c83d1345078500b100c60291b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 489165026 1250 489163776 489163837
    0x4050a0609060f080606090717070903050604030210150e010b090a0807090902151804050a0b04090b060324010e040302120315190b090f0d0b2a0901090308 68
    0x8000310f903004280103280c284002d08048010745542d20800140051118459005d0140030012100c1c001d22101c507116810b05803012030032742c1e01c001c00034001d05042005250300882c000c0244020324401f4000d19907800548a44403005005503024489194010711a40c02c00c1009040d04c40e0303015003440c421646403800c0d28546403103503100d2a089516080c08004500b0041868074014980c80901420000b02c00010b83c406442074142901031540d440000e886541c01d50401e1482e4640a001080080d08604050345007841c100c503c64000d08c618801d02c000280c803540f5082d05a110514054a00c0e401d1060f91022a00041c0c02a0114440e580308070756012901c0d80158000c50202010f040e194401006002000b00d810500c04036a210000d000c00c5501c15a00031140060411603071607022200c580005010740d0b24a1402420030400c032000c10842010710304004224121154007080e5407074101c40a04414403c01c2829400900f80550400004080c403001c0c0203003030b4003542103207180441140b03101003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 489166276 1250 489165026 489165029
    0x5180304080a0515010510080712020c030406081b1e040b0406030b01031b020601061b1e0213020310050d0614150109120c140a0f031a150f04050a060906 67
    0xa035000802e046081180c200011003960b10000740c40c0d100f0b0f616200008041034001c0f4503070340c24045a1000130700814802c1c540c0a001d42050070046482da065009400c0d503e400c01c1c041d020100d02801c01054101807070304400c1c0c1941003404440ca18180b003054124400d0b0208d1310100200140a110100300e089400d00540050481f07030b500011030f40b030610001420f5880b002c0014495861070103840700308a9001c100641900c20604202e448005c2c90810307040050344000c0b01500320b080b16032543c0c802080300340c0e08101c4180225020940e410450a0090892200343ca030490b0980c0c0002c0304000c941402e801380581c0e58050080010360086400c0c0b13802c05204102d0362041813030046c4020381c0301581c010640781c01034000394a0810706611250389200c6000356034080c04c805803414110901a80d9140c0708420040c1c100805100901e603601e00d0140f000703440c4014902040c04010001882091041c02804005000242101c0707841481c030090200401000d01003442c0740d52686030100e0320700c2d49400f0303410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 489167526 1250 489166276 489166289
    0x302060304020f21010b0a060c020306160507021203070b0f010b04060807142113081b010b060a030204031104050910052e1701110f090319031805040209060d05180304 73
    0x20741e141b094080000030080c580020040c8442d555201d0056140055a2644100e03502d0100b0120525250300351002d000d20b0034000e40c40110340c41c980b56591404000340172401d125800c1e110484d1036810001150700000d0040244403c0309210800c2547d2140d81102d410804a04098580e0500c1f10002540c9a01007402ca40440e000364007801043e0030304007500c55000030898001a005c080990320303101c407441201c5c07104441201c03400700008144008e500000d8100d500a151503a95022101c000c2d019400070320003a2034810b10940301040c541420f002e9684150009001340403c0c01060146800403c0c002e4991281f981c10141004400d00e8018540c0c96225510002c2d44001807403c9200b059240e02601095030f582d0401c034882d1340310208a801e5484c0a6021007009840b1a00c49000c03a140095010010040e00e90a130041018503401000411002c60509101c0d00302c42e84840078402a40714203841203400042c00c01c0301e4031152085070b00150b0088001d405000301002005000c41c5580c1140c1c00c1031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 489168776 1250 489167526 489167531
    0x50d0903080706020f070b090a11090702030406030b06090d0c0f15120207061401090605090c07020109061116150f02120d230a0b030d0807080105010309030203090a06020705010e06040302060304020f2101 89
    0x40ad212480303103030155909085441444500d401d0500039164010f038864041415180e12a01c00b0981d00c020607600c0e4814060f240c000c1c104d130a410700c4c0a111a051142803080074000601003421a440c1c5055010080d040e2980d85988561800210080d440070350107445442d640c885c88480000581000d6000340741c00d020114800741810108200c0c028080d000610310401086600c0060360410451030032076009084ca12166000b1151560904022a001060096560502040c0d0300c40c80580141414220359410401c0181c6400680e80d8511240071038048003401e1044140d006103507001800c0380380d103c41684043d05a040d0b04044540c40550b0304a044d10785a030784910403400c04110b20f450310045071826080328204940301030b28100c010f000f0b40e41015240c680007402d150080044800390100600300310324003540d0341da0003034850200b40141030018040391001f801900d004001d40e0280c2c0c0e001040c203455038686900f0840c8403418418100e401081189404800170701d041c0d0103200076510000003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 489170026 1250 489168776 489168793
    0x60503060d0f08210405070302090c1903090c0b0a0816030b06070803060f060412080a1e0c021918020c0a020a0b04180e0c09090c100c050d0903080706020f070b09 71
    0x800c40c201d114154400c1341e0703000c41801c11010900c001000c10840341c0503a0200095242d900c0d84d012184924080c00c0000041c8001c1400c0b800d501d40e218080050040340810013140e00e81009407514442d0302c1e45000007503485004610301407049602c029254809050000d04c070749010000c100240c10211055400701c1c001b004102d0f090500c01880119004215406451319050400302c40241d80b0680c0082e0a41e6001b241849855004021481001d40c40c130755400360040850b40010720000b49054224011321500d12401100c50b044211038064549600085031095880c1c5104030094116010b0988540300310a580b00240e110000c4481c06480320103444c1e5543e500f40301c0c19811482c2c1903841501e034140b41140400125401003821609080100c039000c41c1921060108c134944800010130607803200c103c0d804c0b030700d50680128042c1865445401a43c0e24000e03042001d44070300d03150b0b21010b44444130400030b44c000586268000c02d8258115400c45080030056103c40c0030103441101c50038542d500c180b07503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 489171276 1250 489170026 489170047
    0xf0e2205010605070209040f0c0b03040b1e0603280b010807080106050d15200a0314061e12120409090b0f010f090e0f100501150c0804060503060d0f08 66
    0x50329025002c00c3c20454038111440d4089264090300800c050a2400b14880080400202041010041114194554687c202401c12040da5141500c907489503491102a07440700d00025010b291040e000180a40300c1c0d0075420030081100b071039a540c15050000916900400195074039080c0307020342030000c000c065403410301024a084407901c0c0c10042c403d9040d040d0380e00000e01900001c0e4010300c119440460705882c020500c00100c0e5040d5404801407001003030741d040fa80d40c15404280c2104120034a5805521000103001c0c00d0140c401400c142402d02408461180c20066240810404518121076201c503002072440c140d60481d41007100e040d80c441e591102400a9409695042188035010106a524220358100b0541c680e1081d9070116466000c104c00c400b40520802c00e4681a5034182c41d94466841310080080c0b00902841444080b546060f078662842848110036855000300c4c006d280604187e03068800341c100500132544078080304502000215201c184104aa100300b080305c1e1075208584 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 489172526 1250 489171276 489171281
    0xa14031e0d121e11130b0919030c09051f030f2f04180203060a0212090a0b04020d290f09010c350c0405010201110903030306010f0e22 59
    0x41040394040c2881412007144610140300395140d40c5107040040d50070a40503071601c0c207000350003080218032850a00001c00c024020010304484008032307083c250710081308c8070702082c00c00e1078000907180400596060020800a41c0409e4000c02c181e01402900105030134601c100200321380007114000482000e20b0100308030060081d4030480c2c001500d100491918540781c8000c1c0e400c0c8506c91043e5196100b0740da41c0d81203105c04099a94002e030a44120740752107240d04010750300c6072014001840c44500020034071803000c01c841010741da0000703420050741c0341c81e020010b140349020425100c06014000c011510304403c41d540340011011200300e80c3c9480c000608000458000b0f22562086c0d040840c05804140c2c02591007103010f00380600c96154012825204c24404e03220321009000c0700308031061141d69220030340a00100d40003607000740070641d1080f00c1d45010340146940550554800c1c401302c0d03c99801640c1008000050340b50250465800000140c040300445034081a40940114280e0070b102403070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 489173776 1250 489172526 489172547
    0x506070c090c03050f150103061a03091e0a03080405030d0203010617010501020606152d0d1104030b06040905010f1811122107050703030905030c0904020a14031e0d 72
    0x1428208101d00d400e45c48003800480c01003081d910320100c00009203690307009501200261808130004220004180c844a03400d03802030b0340d003035100d01c50300803000c00702070385583d01660302c000081c003500721a0400e981c2501c01c402c1c0030704122860f010520035010048186e20140d8000c01e641d41c1c1e1034020200407815148400d0040c1c125a0464219400300704490320740300d880d180303c54030540e402d9035100400c40005800d4544100500d182d00030110b604241118044027609420503c2ca1080103019415844d40126108038070000b40480c0302e00001072003500d42907005500aa000701d0000c61034030503021b40705040790520f0301e40700250100d4220319403d01443c0110310840c603100380e41c0d4404c07104040c4140381d900c081510f001001c00c0321030580449035103802e406444626600c030003120711850702d034940980701c0a0103019440c024414a081d0109500d03200c0310040c040c980140c8510021400c11460440c0c031074200d58010b0b010301c80e88904807020315040c2e810406510482001d800c4030700c80c1d40c4000b0041d5124 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 489175026 1250 489173776 489173801
    0x80d08040201170c030c0d0f1515170402060c030706050a0f0609020c25030c081011030402010903031407020603180c030318091905190e0706091a040506070c09 70
    0x2441c200200d0b07513846012603030040e02201c500d940f50ba01002086c806804800c0d0100981d50a11200310700742e2220003a99030035030320b80b281e1240e00443c44a0703044030359211511319a50064402e0300410090f050450082c5200300303d14042e689005402d44800301550001d0392002c242c150384114100e6149060720416015080c1c46101b903243c1042c000c001aa29110b000410440c8100b0010440307220140c101200e0040d41c1c40441039042d1580c0340b010684035410280c46c003260fa41092105202400742e501103c0c85103505841d601c078882d055440440d0107051500c80c80c4040c110411403140540c0d56800503520580c1c51a007802802c03458501854280301003100510b000380d109020003a9009080180000c803000191030b50031040e61804003540700300d905500c140e04921300d424180400b2075102105410f2000b4000d006101088006038500d54a202a100d808001010081d007480308100c41035841d540013000703001c817a003840d44800010700349501148040350340c1000cac120200881c510900400070280407 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 489176276 1250 489175026 489175067
    0x206011a071a09160501080606030a060e0415050a0605400b28030b060109150503040b100b041412030a170708040b04120210020a0c110303040f0b13080d08040201 71
    0x18140000c0c0101c07c000e85281d100d20004800034190030710a07070240d0014183d611429051781080d0414145d0142c1c81504901d4044c2040d00180c910a0680554011a080070780049503242519007203000d690780e01e201524040302d0f0074600541d42220301c0c054040c410440d0900040c1500300b0380400c00d100c0c0c0001d28003011960300701005580c00350703109101e204494208128185c0c1d40d403a0001200e4003815034000014140c100030103240150391003400346200d240304481201450711280b00740760b12071200d0300c25408044401c01c818002086000c0184004074006003040880c1420810810f0a54100010800000e80007819403810034280e254156000321090a10070b40f00c2c24980c0342e1b2480940c0041000c0c01e00070500e441c211529100b0800102152000c1c0c00864403240e003000c1c003e10548503c10191514030380035408009905e800f008907001c8580c41081400c1d110318003205101560000b0310410311100341c03030304002a19107040c009a6510b45e916036031090b00703203810320000d40307041055140d0002288 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 489177526 1250 489176276 489176279
    0x14070203030c07030201150e010302122107053a0302043c0b0a020f0616030b01020307080304050105180307020f190506040e0103060506030a030206011a071a0916 71
    0x5401100301d9820241c2a40c1e41c0ea52400142400da000d49a0b4025021444c0140b07030001500301d181c610005e050303d00c2214100220280140280d5469080b40780c40e200b20040d94208070034441c2c808009080d603e1190087d5175080d448200c0c0c00d80c0701c89039045400701040031041500d42d24a6441c884000b5403000d400c0450901d400e202212034000c0c4c803480d28101402d0808806c0510407241440996043c00c2c0c211342010481c0c60325010880358001104074000351082c641d00105c1030340040741461123032505441c02214400c100d0011009008030700d0085056000030070480020500513401544103901540012407a8107280026118070818040c0d05070203900144804130059a40900200170300600f140e07550208819000d4907150400c26a01103544940300080024165082450a904aa00404d0100505d548030014151299200180200181c115800511101040b18852000352003c0700342e080c140005030341e60b000024510091402c50307448003810810802c2c400c000c04100340b29000303811070740c09 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 489178776 1250 489177526 489177541
    0x15151002100f02040b030a06090608031222020603040b0108120a170709050303040e220f0807030e060301091406060406170a38031605010e0414180114 66
    0x14552180c0078154603440b2103282841401c03d805031405403000001c007690707a050001540300184000e00c1112465400c3c4480000c01500c044203550107655405807080040c0d80318403000450120801d01400c5010412210201507102c2d500036500c103e104801005003941403c0308c46190414000e00f40030b10000402003c0e0000b540120b40e030b240e440c3c900b03601c903401d9281d14505507159001908880d0309444003050014218216035a6076000d5100044207076815505407820b403440f500c0c000d50251000c90540d1045000464050050810034000d10340407034810401c0000801c0d5501c2a0b002c0c05442d904e95035440d86007085c3d001020382218048800601c2c0c10729103003014012a030f204901c003000604a000107640344100f40c0049001d8203481c0c900c03101c00105103840c1d6441d5094860700c1c40b0141c1c0508004079003030600207040801001100104c00c9000e1418004642c0308c0307090700002c0d40058a0300a4104d0b841d24030401d1030302032810311501d413501d5140c42c6005401c40306040b042da00d00c0402e503410302010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 489180026 1250 489178776 489178783
    0xd05090108041a2809030c14070302040501030c0e1f0915030506160f0c0506060405070e042f0414060304051e011b0206100605030907050315151002 65
    0xa5090070700307000c1c12950b00c9081484651240030400c00000410790b0030495031012003581014451a21801d00c115860364850305030842d54403080040220b041c1424003004a002115042c14000c020011101c449840361f0200301a41c0e02a8000c032444030081c44140041000d6030040e50303001840d071801080182d90311640954200300740c45081c2050b0703919110f080d0005208403200018540200803a0401d00b03016481c6000301b0f1111810f03600061200c980000401e2040002810f02908075008061700d03168001084014080a00607206002041920004545540c094000200d040d42000c019400c590401c41c0a441286800204400420081400404488840c02010203801e0316001d40300d503030f42d01d400783c038085c8200c20b00c8028910510094102c6081508880c2000041d0822840c0102c80382c84180e0307036140306130380c015140d41000c10b09101080c0304070b02444d400014102210052550344000c01d00f41038424502440d45101d1508101101d62a111881120324041d5800712402c003080394000e49 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 489181276 1250 489180026 489180037
    0x1b171605191e03060e0d03150f0b0901031e0b010909140a0e0a05070f180501031101030c05160b0a0e0303090d0804080702090106020c01120c0e1c230f0d05 68
    0x414004055002c0151164000c081e5a100f40100404c4201294280e5540303840f10300e0b800000d050544e4801080f01001100d401c07039040315801e03130569052221800c0250000c50400b410141d60303141d2003855580c070448800b04d00c45854030002d03140c44044001003a00300d540d08400b00007400c003110160004100d0101c03075480b03071990600081c03d003590044a0704084496501074007500c00c840c0f0108403014126000c404450400b041003c3c40ea0700684050b0a1b00c03000d1101a01e01d2380d0146110030154002d410804901c1c107a403400314a000986c4002401c0c085070001d051f1842c510700700c208050040c0c24032821854405550003517041d498440b005650752603494140c032041009060100f410044003000390303441e0b43d90052080c0450360312042d000b5a92a54021703414001640d41151307241e281c81303e12074140440607650341c04c10a004201d05015800f640d4001c4110021814045036021031031402107203000d040ea071001e50007868001035203a40340a40685019800c0c0c0c015100c44610207410408940 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 489182526 1250 489181276 489181289
    0x50709050f0d0602073903061808040f0611120301060518031e0d08010501020c150c0f0106030314040f091a090c031e010b03041b17160519 61
    0x9000414000124081001c9140b005040500100c0d965040022140700301c2210701c0b020444140104650540700114180f11349401045020201d09101007105500300c1d4121060031419040c0704c5c1032560b984c00742c076801035001c60900c0c0002c00c020320446502c030010719958039481c1d008000d900003070201c0281e14031041c40b0328414000c00140c1c035090007407042c005040e0010700405942415601040c550306003070768071034108154002e41c0540c0031403033f00900300e96040c0c5030107038002c005080f026402d0101a080010403109403103014400c0050003801000300d0242060140000320354640b851501822028078403910440840d0103200034459181d07003010b144111401a04040b034005032040070100400810002d09401241c41c10401c0303d00302c21130300210b01600032481da16229454020501038241028000c00411a8080012501007210344c201e00e140c070801d103508440d10583d6041801040030469107002456080240c801d0350304840c0c4d080d850f000708020741e1040c910041c100b09440c005200382c025003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 489183776 1250 489182526 489182539
    0x806011a091c20040e1209060d0e07081905191a090a0309151403070504150c0507060929190302070c0f05090f06150a030e010e0105070905 61
    0x704419511090710114241c6125a8903000700c0c09414111189101152001c0a0b16a00c9800e9082d82c00c0520138010350314903490140c00042120300d2030b13104903441020007560140060250b00c451101c14860405460700380c400400140e841c024440c1d0a02442400940d002c000460b07141d80800c4001c0348003034008418080700e00e0040d21603c0d0440e0744081070b003800800b01035000100310205600095040280d802511025101c075541d11018210781050006100042e2907100c1c00e142000c250800b031074200450b41050741c10103403640c0c0039075445002c984003c400240f2181401d81800402e00082002d00b034079261444000d41406806920114554000c4034420704042c00c42c803e80703c101003914401c0031540c00110b5940107954005001e500052130030b44403a05034600004070744404e01d03080780490b0405403145036143c0d50384028880506004041c2ca410500041500b40c4000100d00204990007a903100012045241161982103880c0c804405405030700d000203000c0c2198014640c00102c8a007202e01 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 489185026 1250 489183776 489183787
    0x2130510020d080c070f0803060103050603030c0a0605100305030703051206041b0c052a150a020d0513030b0103080a0f02070b1e223204090501021b010c02070806011a 73
    0xf4040d540700c0c05c0c50151500d0000810901040103007030040d8060740007683d00703010b81d072107103401c142c0c69104048030f05c81154000c090700710000349250402d0341e100860400c01070307a082c1d80c2c0e1034540c20350b4043c5108400103030b0000303140c40c0a6248844a140c1002090701c0400c40303040540d007003100b4400000c2580007030000c540062400c00400b00141160303050b00803241200102d51350000c41240344000c9842e403041c0070b500810074003648010151203007a12154003c02d15810307900c00554456100c906035600e816120840030002c00e07411200c807802148141d400c0c6640d080710030001410603291030410011900018400c2140280480a447c60300f60420420080c01c00000c80c41e0580b80f01d01540d031303d82540070304003244a403046610000708a84039040101d00c80040e006031060b0800c1355202030f940c442e8030030969003840d0402da8401c2c0c03030641c402e1000501e0061204100d210032090204d030032207160345a80e00580e240750b0600c0024020403903032000788419410988023640380c00580c103164050010101d131 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 489186276 1250 489185026 489185041
    0x90206070212010b0d0309080f011401140a0e1f1d010302090703241502031918120f060c030903020309040e07030b040b10120320070b0c0102130510020d08 68
    0xe41003424005c1c03540513001d0b510b14014192040320310070364207180202007003001c9050b4180100201d45011000100403a0b083c4240d500340d95500c190b0490700844201e4010034005006203143d0f0040e80780142210300c10303c070041081001d031001e8001c0c284143c0075812405d10b106166000c0c605480c0c0c11214800507079180301c0e08030010682c1560f08a45140b80301b20018a40744d5201e101015244840c101071200c24140350180d82d0380c072030100c04000540c0d4040c40344070245c2c400e0a2842d030b10720452540114842d6078510003400c0200f07584042c0c85800c03031450401304120f07040c45aa040305500c0d04003842071580744e440c003a4588c029201e030300740115111801802002d03018003482005c2c1d07a22030280701881c1418282807000a81c00c40301146180308000d004152007144895803c0f075a03506076680c43d01c1a45500003510300032189410784a00707115224000c1816000b04002e0101c16070a5000180c8a10010700040100d40b0341c1d600044c0075500070400140342c235501255203034080005041400182c1c0b203426 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 489187526 1250 489186276 489186281
    0xc02060f040308040305010e2d012003070306080f0304030803090f0a05150709030c09020d270303150b12100b070c03051c020d0e040207020d0501061809020607021201 73
    0xe103840401000180100030041803401030800e5034000e8008008266145842c0c0380d8504140c0c04421000000e80b510b6000c012000302c418202c2c100c984000b00d010018252000c90305120024486104000442040601c5526205140061075054020503072003400111040c1c036441580400b03000341400000180c9000010401054041c0c03554007164086034450400507202d50826110526259450380818029882142c0582c245d0742c104103903610f1946020341c13450081d88200702d003600c80b40d116802d00034402300080c44844d58071030114550814028a01c2c00508695201c0c400784001c00d09020140240401c0d001629203a07220001c00b50300329100c1003941a00c2d54900c4d404050303140e000285240c1088a40c44250007101c0c824800c03203200004041403d448410110724040040e84515203030004203108151210001e03c000c1d1005151004540104180100b071705402c0c0d5483e0344540381000004c2646201a544142d12a010807200d0030035030006496100c0d200c0060b1044940340e058206800082d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 489188776 1250 489187526 489187537
    0xa0305031b07020a06020109031d030c0d1e050303100815070e010908011505120d0c060c0e0a080a0c05060a0e010305100909140622020d2f0a15080402010c0206 70
    0x4004c089102e13a0313010000e010782081101200081c0000f084034004c5000d61602802d074800040151043c81c4c2c0407000c0c080040d103d083c050b41c2c20f08c14035a28030705003120281e1191405000f500a07550300d150014001408100c540d121031a140e11800c8400f003480c0c000d00ca201d800201c00e1600c1c1660210340c000403a4080c215800c038140d6546400050300320b0081510101045407000e1b00c2c64120744407103400294882c03a2500c8000007050080c03046000060495108014030300c410700340340c02840581c40102e00c0024442d004405160b2010041205004218503110004c1000b01c0c0c0b200e00e050b4440ea0010440842d20f407075541416182d04c0400c405801ca143c8c2d0070040e00c60b00b44108084078141c02e11072050036000c0e1000c45035009940104891203e554581c10344510b2500030078001145a90903c11403020b0100159020340d440c40d441141d4500412500c130310032043c000d400945944520801412854940c8940d880e91406002e00044075000455a84d1154090900521001d840c3c0003140007031145 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 489190026 1250 489188776 489188779
    0xc07080f0307021b060702010518030f0a0b0a0e1216030212030a0b1f170c0403050d02030c0c0a1d09010e0d0f08060a120b0c0c011505010806030a0305031b0702 70
    0x1004005001c0d0380080c4c107030f003500c0718003100601c226005414400140300304800a030002d1020021425100c002e0180d424034420007400310f960151166030300d5401c2551146088618598100034401501400e0007010a201680b4001e04000384468851400602c102c16400760083c0d010700c02042414024440a02da2242410a01c1d9403072405607000f400501186400e0b500c11507400c00c0100102c1c4010f000c000d03900001d40c80c0c1c8100042e98076100d032100b20b8014000008004108408400150107024009403116150010b58a800e00241018280b50700143c0c0d060040c6e520007400c11103a250451071046418104441405135100d1000c0d01740075006c3c0d08902c552078440d40719030b42d0b20580d01c000c4040034500160b5818141e40c4842c802c10071072034094417903c41c2e01c141030041000801c0c140c0c408250040140d50b4468a0004068103450951341668117080c080c0c800035038104229604040c0c0c2541c008000c90241c0009105590090014040a0015001c4c074005248032001e1221070700448040300e40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 489191276 1250 489190026 489190057
    0x3150403050d050c03011715061509060a0c021c0b060405060d0c0605040807050a080a1103070f030602030402010311070c2c090c100903030207050108100308070b04031806080c0708 79
    0x8242d004c8141075803080c85120807625443c8180700070340d4000320f400280054480c1806e40d01d6182d1004002c2e460305009840749102004020004003507a46400401003c000b5440c3d20202c019540100301e14000c030f10b0403e410600c00380c0c0b0400c001611000031154810b608690009054036401e0100c1c031903822104000b0401c504226001c2400c0d40c02030060310440f00003000b240c203903e8841d018060038004902c1100340c15489600c1020000340040005040ba00d00942240e280c140ea8408a5454032010752007901d01c258008284415940d243c040d101c40e40c025180c1c080d2070401e107a503c6c00580801c0d840b802034883c00e81140d190144401008841c0342036071040860042d400c00000311034070cd10f20f011426120303844a41090900300c0c003c0c050380d000c0380d405030050180985130400544010b40010095070b182c1084110100000d03500802502c500341c003c821091551038a86405882c001208489001410000404015240d8002400c0340c1c001510f9a00580300c40e020f140244c000c0c0215107681a0282 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 489192526 1250 489191276 489191281
    0x50a150b120c0f030f070504022b090c0b03011206111b010605030f0c0a0b09030304050d03020d021506060f0705010b061204030801060810060c0c05130902040b060903150403050d05 79
    0x940010003100c42d5608a6501c1d0540300f100e020181d1790b0440ba0040140c540017407208010305c1c0341c654058001070ac0403000040030101e488450b5180c107903035200e88007134850742c1304610014801c5404071140130300920908103140d541008030012030b6012211000300000d40b030301d4203602420444070540300d0707080e81c0c10203541c403503410191054007809030347c01500d01a1203030300c44000040c1c0c40043e50120302c04001c0d254003403203410224040450b5006e000c505070103120070080007556890780003244120780c1c040d82c0030308051388807401c000f4113010f101a00450000e180342d0610009580d02800c450204c0c8034907001c030307a48030000e02e030003805840f9221070641d100c1ea020a86800c64546800e039a032280d44a03580d50300d160b80e21058283c503030030001d850a03131748107525003028402e050243c00055203041c05800700e4884242e990000841009403c881d5804080d05e4442040450070103016140841008a882c1c1c0d00304007021003c60fa0b5141420f1512803c00c0c0c103c80402c3c24140218100d407043c0000c2d907010710080c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 489193776 1250 489192526 489192559
    0x50f030105270c1b060601170907150503015a0806090601060203030907141210020910090320060d060e0612010212012d0e0105040e0307050a150b 64
    0x5400c114010302075244561302c9440c034200003003006172061405842d00c10b409084110031465500b4028206003207881801c00c0031403000d0303c410074201107080d03955510355250704221191038641c2100d10640e410103105c40c40d00c0500d40c01524450304070401c0745904c0c0602102050000241c0d002c0700c0010980c121002b42c0132030751308000b0074514803604c1c2c20001c4882c16640d410302281c0c0e9210850340c81406410182050100b16103220a03a20319840003403007404121007040342d01e810448440d001d80c454540c0003031103603101d04086612581340c1c846070030060300961442d03d036914400c20303490000e9801c00041c5080700e89541c031201038440c550700601003040394079207800c9000a450420340c0d59030300c12890120141c2590105000b150200c6200c0c440d003c03c50b0b4600300c0c02c43c481200e040c002161400c070401181c0c0c14009501010001441070000c840d075203516040502c000c64041c041480740d241c10810161000c42e000054000120368810955954458880d00160090a84c022299401280c01080d803842 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 489195026 1250 489193776 489193801
    0x210091e0305010b010c21090b0d0b030d020f06162d0909050c09150903190b0a060303091e050a0305010506090c0a020703031107030204060602030712050f03010527 72
    0x1902d1081000308641c0702e2940041d01c0802c84590700600043c4540c0c24030305000101006410080e2050900c0c0d41520b440e0704401c400d5420a90001944c0c0341c0d5012490641e00c4d04210182031040180054089240c445200c240c441000601c15044a1416052180e101d0300c5000e181d4014900340800000f071021280c54501d5620118414200160040c28041852490351282d83c0c00390200c4401207141c0301c0800140050303034203068410168118180004a4146c8007841010401c190910444611100310320704001520000742124102900d003c1c2c06000282e00180000c055405034507003071618941e1344084044007801a0031440d0020116400001001415008580210401c8a00d04d24595034640001c2d120f0244450160040e4003120040011a000c0e002040080e4500b4007035420940e2240c001c03a05840f0f142d80712100580c0009a40c200b071040c00040601c000d80f591904e146084003400c031410b04d6001c1801524850040c9290710742c508218852402280c20702c00e8020282071501072000003c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 489196276 1250 489195026 489195029
    0x207140f07030b07030203010b0703180b040801020a09090902061e07061b021b011d040908070807050609060622140c0903010b19210f051b01110a0210091e 68
    0x803220b1050010490017800390081d80e0585100500f502d0900e0b9035a20f0071980f1014002441d0160542d6203401301c1c04503070050041001c0e141220026903210a0b4442c01005400c2992118503814035080308140180e884c0003c07182d0071242c1d00d0180000d100302e079400e4401c41c07040742070003800c0ca0f00d4004c99003003500c2d40c003d5450104d580d07034003076441e152801120764108a402c02e80f0103000800a904440c0c031255010700d0b02d500c803c0c000e040001d40c04e81564410314554019882528540d001140707042c1081401c0152552004450014003c0c2e8140a0042010b8140300c10450003026514100300c01c4060f0581d10410030008010b11400141c24104440e600c40e5000d079031000c2c025406c0810103070841c213204e0115140001703054000481070389030414a40c030740c8141c440851fa0f00180e1071210030125100c86100b029041c0600f000d45294000249140311182c60042601d0504c1070542010764400400700340314140c550141c0303240590564441d0111000003554000802d030782000b40c20043c080d11459910030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 489197526 1250 489196276 489196283
    0x15030a050403030b0d15020a030e2b14030f13050a0b0906070507030206011a0705150f0f0106020d0c0309080109080705011a1c08040e070c020f040c0f030207140f0703 73
    0x400c80e201c06090012903809848068109640c100c0d43c2c6c600c06400c1d90081500e03803601d10340014507989030a0810b0030480101003044002d104c01003800408411407501c00110100c03810003031815002040340d00c1c26404018050400d1003a000005081c0b8140401d12680340e0340c0c005c09a802c01203a9140088128106503640c400764820100001c079198001c1040f540401d82607001448107a20702506405850348a0380c004241c1d41042c026180090001c11003403c01d0380f6030007000e200310701d019072414043c120018040102c0489500041090365004501d4206042441c0380281c81d01c20380b07040130384102c40b840d031240f41c40e98030b44214542800030f15030190a44520820080c07020781d5440214840358a000e80885034003900700a000e410043c651030390070b0b180b2841800000d040031b594068a54003900100c40f502c0200e02c12a180c10f08528040180f199406421201003051281101c00281950300d6401c8060501d41c1c0002c08400303004400046200000402341107070818901e14003415218030842c802107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 489198776 1250 489197526 489197531
    0x7030e13050406061a312601020f07020904143c150a090602040e0a180b0723070501020a020d0c331a030d03060e010302060915030a05040303 62
    0x42030b41c44640b64250842c010558109007004684c00d1914012540704a5040075185541c49403c454039032820904000c0080c502188050420070340d02c15103019402d41c168847c0d910410007650000380380340030380c5e0741d480d0140d60000711341e07485243c80d501e00701d0301d01441d1141e0310482a00b03100254140c1410400300c03580da102c3e8000d16559003003014800555100719140364005041e249040c0000035621135000f00031400c0850402d500e61910400c0f6480754100000c050107100030000c0403034140c064110900c2040305240c1205080b0340350480a1a0058051010002d850342d0392040f0089420710607144030080444250390714818a441d5000b980a900508050f014041c90380301418000c04611200c84c0e005420582c0758488054980c585101310b450b44131103110881241078000b03c0368800d11100b0025004604d01e94600e0104041c036202c9522402020182007110074405101410b0005045a5060f10b40344e40303404044000900b000c0c01e03d01c1f103200900c008010050a60540d07041180524060b031000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 489200026 1250 489198776 489198779
    0x12060c030e07090203100f0f090504150501030b04030f0203031911071407050a0e010b07080f0c011d070b090105090f0105160c0510110c0d1e0c0306050708090a0807030e1305040606 79
    0x7040ba11f2540c5206420a010103a44200070f0483c65800c00c90f4010322464404044031190910170701155400c3c0c00550300c0b0000101000101500f1100c405040f4902c0d00045003585046203251852540c03100c402c9403041e0b111164451807260003000d0711696070744075441c50348651503104455503d11240c4110381c450420102c1c005031250740c414040c2d06036507003010880c0c5008469114203442d5801100d121030040c500708142c6491007428401c81d020005a4010905110381c00b040882c40c0c24225080018200c0c01003003800d070583e80081c100d07884001c0607100ba490403e80740c801610740e80100864480964450b98540040000302d2100105070391302160366500700504140111650b0300d9070620700c10694040c0020007014034110160034407e500c205081c0111034510400c83c070300320300040011220406040d1042c400c100351809a0b0307910040610309030030140b6119620990310085840d003d04400d400040807400c0c18842c200f00410610040d0501958406204800300104070841701510101e2a0810 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 489201276 1250 489200026 489200039
    0xd0507140d27051f061202010e03030705060705031009060f260106140a05040510030201051309060b0406110d3f0b030d0912060c030e0709020310 64
    0x508010320095200d40314184031101070903100801e0442c1901c518941c501c1c601c0300010702119520805544584040c08280c03980e02c11441c000e04009040708040c0d0b007030210600c007440c00c0050140d15641c09191540303010601c41d000c00e00b54401d044c0090040d004100411916035003200085000b0700c500e1514201e120750341d02d51201182c056006a580302200301c00108110b04555008034110707080c2c00d0001c0c03128090100100e017107074050b0b400704c1039003180d1480000c15171900416580061100352030500035480c0039140038a0f01422400001d05000c4045141a0340084021040024141500302002090b4644141420940040c82042c0001e18546001140d012020510110340900d984518400c89101014100c042403210402c0c046580b84c0013801c102031140d841800e141e101c1b000c00000f000240c14007403504201c0a200503909002200d4020071030070501d89501d0040e02c0e00020001075441304200300320041e0501040300101c1c0c3c42140004a0314001c180c0c000e42c06140c0300740044c03400e56074414 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 489202526 1250 489201276 489201287
    0x7020f040507091502010e06070807031503030806041d1216060c0c210e040209030c0a030609061b0e0409061d1621021903080f03070206061c2d03050d0507 68
    0x4e004040340d023101000c9000350b4022501c081c3c01c4080350401280007000c400e012081c03524180d20507400180100b00b8000b45043c28800e03488142e0015400d110190703400a859944d40402c064440018480028450a04072a4200c51407089920a000b400001708001000740450b2040e031082e078002003ca940103843c521204845503064145803164100094080c1c00c000094000410b007607010700412865040940c1c84400c1030380610702c580400a1030380100c0c2082c10131035103182149010121080c0a448070aa040010341c007529104070760204624106150480141400300d40c12a600302c280c80c10304859000116085203442e1074840307640f004594403002d0b0040f072500415490410039901c6030b910098240340d94036002d14000d95041324074050390380c3e441a44590101c9100c6204e241c0204c1407003591941804080d07000391007210720101c1d0702c0000200d10005140d44000070461070808500900081180540096000c0c010760f9a00c00300540b81005062580100e03030743d0008a20b0140000c3c030550003003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 489203776 1250 489202526 489202541
    0x120708061f0504090c030e0d0e0306011a0403020a0303020307030216060c03231c05090102070c1503090b190b06040b0406200d0c06050f01031707020f04050709150201 73
    0x148512100070403040c0404901e01000d209004210b010080401c0c003254500a8484107286654005245126010b1960410b41262411000c024101101c0f810a035800038245040d40c65405488084031880d08207000035105591000750401e001d04030000c28103130040042c0419502903000e07650f0a1110300540c3d034150040780540b0001c550790160700d9000c0391080054010400c4c5120222170072842424040c8544e8110b040381c801401001c40b42004000c1450144c01d400060100080d41400e215a841c41000c40041c00303032001c50300038940d181181e00d03c0394200c04049504105a0006810160350300861143d031b0b81420045182802482c0205040406c01c0720100c0c0c0320030500c1410b140c2811401c44008070100c184500511341c000d0112401d81050055104d80c0703540ba00c03000c0040045240400550320014242c64145c1911801040800c600c034070300e410440804181c0541d80c0001e840002c05c1c10040300c5100d03401a18210810007010341265001c02a2007031089511550065450124240c030f440 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 489205026 1250 489203776 489203779
    0x901090b070302090d06060312170601021e16090524030c040c140c030a0e031606050906040e0108012007120c022205100602010605030303010e0a1d010212070806 71
    0x12000901d82032295001e0202d1400003414110312079a40e89820007503649540080d202c2c40004060790f80456003240308001d8404c0c2c450151182464050000f0307403102050b4074503104958080241d2211484107102201e0040b0705904055070103500e0744000002454222200712101c0002c00e070040e43c0352500c280c0d02c3c079850001801071109103c17002c02d010243c906a040c1500b4448c09101c00400c1c550482d024042050348640115155805034400420800d64042403138004c0d0041c011040d01c6108502c6600151b03801c5042280e594200030010662500c29079120f010307a902d01c0070001c2480181900820b002045514614164064154a202c0148030310342c4000c0092032104440c450b020f000d150394180d55400148101004c00060070445a08c80ca070724400b08e400c2d40d40e1020495071102c054622030243c5064402000007a041c0000b095aa00c410700490007050540d2000503140d0195401080c00500e540d41c01d010701607034408006020b50898041803520065690000c0c001d90300c40d801a40c0315060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 489206276 1250 489205026 489205043
    0x70909020607060b150406020c030616021e120406030603060501060212120c0d18021206070914031c050315010c0b0402060c160f03050c04020711060d0f060303030212090109 76
    0xc950f5141e4004007000001d0a41010030040c80400b801c0900024100038800b503001752030304400a6080505000d4014109030003080e020307130340607200b5a001540d0031880c03c5c0c511440b5112080146854541805903034407400c10180014085800c80d0306401c0602280d1180e2410b0010341d07290b64003a84c0f2401d01c0c642600c4001014000c40c0501c5148601407a080007184081c2c1e46801604140001950045c810340341014098510000850429100c41c42c4440c2690028100a003018100140360304110b2203001c000141a18840c403066605201d020411040424200c0c0000c400d1007010b80990811034181c26160080302c0780030400d5004544c09000b40d644880d42e135129a031141c0c200052900b201404401a12800f00c3c4240300007520000f1902900b510710001c2c02c16407079454810314103a64107800c180118014480000001e549112100c04900200e9032540c44480e4040244000e01d624411143ea50342001d0000040c560580d009080700c0c0d40d41103811a0b01d58640c02407900382c6400c40401010100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 489207526 1250 489206276 489206287
    0x108030909160c0f06060503240a0504031d010311040806011502071a071e11030c0f06090d020102030c1209010905040c0c06020904020409050108011d1c0e010522080709090206 77
    0x5140b0b04d02001d155101d05800256651500702283c6005a2002841d104c90880348224120580c0e0500e002c3c1d101100880501082c0790036034004024031005a440031643c075000c41d000007a40e019800c00400c0d801c00720109926182e590458650310300c0f0070300c201d4040c1c0d0030791015102002d1000c103030101038410031940180310300c0c82d8509100807a13001074404d4448044008401025030740644201c044a4002c4546103e590070341c008240c1000c00202480307100700c203a078444c03240790340303820040e145900402c461400303003c811400140d046110f4100003401c05d010ba40301022a0010200c0545100c580a0360f1f21080076490b00180b104840c624a07503400822003110f0b0000c001151500200251500a400541010350392104441a18001e82101c5102d94554403440e00c0704120790044182d041f888401820030740501c140704000383e05007624090800490341405c100c243d004204540c203421034442c42d0914503e20300e10700703d003204080c0102480c5004440c2c0c0000d114002c0e0040700b0109400410706864403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 489208633 1107 489207526 489207533
    0x405220605031902150405090a0c1b240b0d03031b09030803071214150f031b0d0c080604051b040203010303090e0910050108030909160c 60
    0x743e100300d010801c5202c181d03000c0400c10307030161070401d4410503880482040d845282c220540142402d018400c2c1688247d20210440c402580c0e541d005106281811403120020302c3d026201015201c0030740d0f051510740070349220070440035000044220b0b000001c1400800b418000750040381e591101d0011038910481010f0188a5920b051000241503541c0d9001d503000280c40d01003007006e0b8855031420418070307030f21004540b44101e20844440c40d20300b544025801285d1b01c5d0724003a05104504030100d040014a110400b01e070602e009061031261802d00011120448d400c1c2e580e82c031840b07000920f05070705108450141780034901401c01d02030924074440b0b40e22000000350780a148101300401c041707a403200310314041c6e13078001124047d1600d81c580440d1900100138040c90300c04e1f00d45000000c1003080000202610a01645c034041c040c1e03034501c45148240300c81549000400c00c45c0c601d06000 = true := by decide +kernel

theorem cover : BRFrame.Cov 489028776 489208633 := by
  have h0 := BRFrame.cov_init 489028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 489028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 489028776 ≤ n) (h2 : n < 489208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
