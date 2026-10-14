-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3260
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:08:12.880323+00:00
-- url     : https://prove2.me/submissions/74337c73-205e-4954-9c58-4562fc3c044b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 586151079 ≤ n < 586330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 586152329 1250 586151079 586151087
    0xf0803070519030e0a06030c080a0902010509010f02011d030c010e030f0d090f021002010218031b01050f0706051317071703071e0201021b0109170318011409100b0a06 73
    0xd0074103d09100805944400c3c541d0b17101003000161920390340c00152184070b510010594030b009095003a080c1e2a140341d410140c2da0020468114007001e0a100c46900f003000700c00c0b4010302c41010b121039001c440d01c92182c60010080010b0906213100402070054a030f175200d96985034801c1c200c41c0c80c98414100404504202d041d045101910700411004a11600c2900480c15803640c403080d04005075400121344141301c010310402890440280d005202c0d203d1001044415600a800c00c5814440c0105e02140c09016142c1215451a8040d005010a04281d0103140410841540c115411940410200241d1001d1001d85546a810000405280b8088a180141948040d1504042000c4143c0391303100aa4800060b132a5080d690380010f0b0348018148501c007400c1480e500003a4644d0500700e541c00802d1a0442c00030b151a2006240c954a441c3c60b070400f5001c0b1004841b10f080c5500341030300c65000c0c0c0c403007403200c2c2c1c850782064054602d5800e030b5140b034a040381c14035a41941e00020300d40c8180503441c41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 586153579 1250 586152329 586152373
    0x1090b0609100302040b030717070c08030a0f06080a0b0108100513030305090f0a0c05131b05030919060b13201b0105010e010602121314041407090f08030705 69
    0x12070704005240c503868051541b450352080350303450007180300780c40366000802d145c401d40b41d40481c2c642b0300411a200640d45088043c0b1015040803a00303501c840c1c0400782c0314099800b60000313051080413100ca0748194a8401c1c41350f182441100d40500903100350003138420140c002c5d6485025590080c070811601d03550140c00416000c2e10f020b1051191569010440c10304219034405a40500e240e1412507190104000b01544070703540d9411054200509a40d00c1c01c80070124805d45071070b508103a41c07241d40d43c0310b0700c40c6800c100e0703541440070445030410310046c000c0c0c43d4440180740d502918240f540f40c007848185016a44080d2110b80c0d07226400d51440000089600030b032024500544240d100803414840c51808d5881c281c11003031007175001d0001040841c0d010410401d103510080b050a060035000c0e10060301c54030580c49001841c062860603ca041c0c0c0d560703030004642c000c4000548010b814100be0080924034540220702d081c071644000460201400000d07650825804402000307142c103c60384202401c0d013 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 586154829 1250 586153579 586153609
    0x20705040c05090603040b160302090105030a1d030307030b0102070f06082a0c03030f0703060503060f0402060d060b1306050327030d060b07060c080c0f070312020f0403020901090b0609 81
    0x1405000080346684c2d00401140294020b4042c05a1810501026000840c2c4440e0780c00900d071040200e40760a98108041d0fa902c4213400341c0006080c0254070702500a8814151082d02c1c601001040148954045d0300c4078501420a0f130890b0703600d0b40c84107044680020a401454041000080040c44902d0785100741e41c0c004920006080c0040d0244005840c944c02181d0040f003030f904044200520105101c502c02d900c0b40891400380078a40c40e2001080d10ba180160045040e500213400107019502e940b4121000309807901001c000320b90b640c1848034001d402c0240000003002600d503001070007038894010b890142155101d000480d19044541103101117440000c012180014020b401142102d4030850004202110703c89a50ba0101c1c942581100e42c0d0711001014048414140505134136250b0554004410b82d6903840d5584556003000e580040c0c80c14001402d00740005585205041ea1402a00c12244203403903a400ba6602c9880f0701040e42d4407210aa0b8204005008014441c0b0313080303034007480d415 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 586156079 1250 586154829 586154837
    0x70533040320120f07020415030209041401140a06060210051605071704080303010614131523040801141306181e021509090c091c06060f1203020705040c 67
    0xb0820301c1110080b44c115244884184401150020a50800d4020340c01b40e458151203540925007554005510440c020340081d00199107120035040401003580401244c0000502400f01480c2898501c005440039024040040c001c04226112070016070003458000ca049440c00c00c003480c50200112001d800588050380c0601b10801c1142c90205454010030160940340051543c80d81002c5c8040c01074111104540f000380b500304042030041c4800e07900c043c151800101d81d0303c0e100c001c0400c2242d00600c542c403003415140e0101c03020315081722200024000c0304c107454020310040d001d14488004120f13080b41c09412207045201c020000510700c1d4080b44640041d5181880340540d80d4031551031040a00304c9101e9050340c61100103055241462507401c1c6500010540c80c03902000d980400c40049000e400710600c948041003070307100c581c2c840049a00002c8a18041c40c41c814150400001400301032045140c0686005000315205044407106290140c041d0000c1a98514120500c8002d10942d41d2860401c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 586157329 1250 586156079 586156093
    0x71403042006070803041227030204020a211a0a030203071703041d090c0d1214040902070302032206091701020f0c0d090501020c18090102070533040320 67
    0x16008901a40c05103004528900141041440c043c00c80c042d490101c4480b8203003041c423031341c001000050340c0f415a81d0588000d030700c0c1c0206410503140c600004224000900241450741110242944400c6140e03040c0e41d5040c80d410005020301075041c0e524080a0f4254101007400d10041e2001f41c0140d041c1e01c8040c0440e80f41030394401000c9404400c404005005405120a100d10354500704088907100e10101c610103001162960340e0100d41210ba0106000e10080580030356030f00c0f0014050341d0041c00704020543d42d5895529009441c2d9000d0b0481c50844061100e0a04211121149200c16144143c8808503002d00b040602c0f10302c80311042c0c607000a903408008040c00d0003662400341c184100020010800d108100d41c0151040c40250040c174119444510032903010f03a122003102243c1c4602084515441d05c0b40007016000e4814041e0181803841440d0300710306a03100403100c07089081c20301e6040b03440e4451b10810a1034646420b4a010b0001903400c400340c0e410f00c400424000d030b01ca90502c1181d41c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 586158579 1250 586157329 586157333
    0xb0a0f030b09102a03051603180c0602101a0109050d0807020316091a0f0d032604051b032a0909030309010605120d030207080f04030b07140304200607 66
    0x75640b0203481c40740c1050480303901e202e50440c6030244c1402d180480c24148460302c3c0209403110320140703895001d03041540b94840104100742c1007120381c0c107450704200d006124944501019544d641008284d800f8030385040e45e9848490807280c41500345185c140e4405840f0b03403070f0500b00450780400c2401590605801c1000000580e410000e118001800c041a040103600d4682c2c80411074480103803100d092603148000440b1030b584c091002e08216000c84d203000d05105507040032540b100400700d90902d5031071500c42c01181c814404600c580f0442c49101101ea2848070400214000f00c0448266a0168001c0107000c90f801d01d40800c00c12815030509800303815480c1003002030352205041ea00282d00380c10003c140039801c41c082c0900320281206560304280e425907980c03015541c141d55144c07001015404a165010000400115100f1100c2c02c400c0d10340303481d12410040c12207101924100c002c540d00030501150298445c1c03d803807040380c0102000a54144000001628204607101143e0001c2d0030411000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 586159829 1250 586158579 586158581
    0x50a0501110303151302270d030e12070f0806060f030d0f080a0f0f140a06030c03020405090c030a12020d0903080d0507050c0a0302150f0c0a110703060e06040201030b0a0f030b0910 79
    0xa40101008400c5c0c7ca1200160102c0c214614121007090080c403104003800c0101760460b0040345020b00076a28024030382e51044aaa040002c590801190b8850b038903030003d0203440015483d0b01074642216440c400761101000c041e500da800007045400f1803403446141c41a030780592000c0b0b60101208202055849903a41890111044444440035031940e0340c203104840780c1e40c1100d5582c4402c07a0340c020007916045444005c0070041d80d01c0003d108a0f200e90014003a0074051101c00d0403098054102d40004600c0e2070500700b00f95100954200600c1003050b0f80740c0d0700c1e1003180240103c2c1d03084440c551803c400103000c40054180180060240a400c10498520040411800007002d00036405403082c120040e4036403000d508081c04514040081c0010721404140160850309022400c1c01c000c5441047e540400c0c0c109000ca80c00600f802c3d14041f8240b15400011030a14400e6100b43e0f0304001d8101d0744c01c1000214142801100301c010f60100c814400290400199a00301d1100720445148014110040b4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 586161079 1250 586159829 586159837
    0xb0a0906080a0f141812090415050405090616050a051c0608030f040e010b071a04170a0504080120160204090605010308070311060c070605070c050a060501050a0501110303151302 78
    0x40c0d003c441d00030406064203542d0310317002000c40e00f409004021181d1040c11414018080d88501c0b0301c0d62003056030400303e05600e8400003800046e0080c003240c9080900075860b18001c0b2882d0281c3d80c0e54050301c0c006075100b58100c40c90301413191501030501000c50250a00340c17a5031300c0000f2049a5804000c02c980000300050080c1c150b00214103035030b4a04003c40e0920203103040e4091300404030306111090000386840c90702c0340c14400c40310540d601603481d170903c00b501001400c0590700d003040015100d103c00758048010000d461258000b4410500c51801c540782690100010142e008020b202c0150903410700c86015001d20300091000c1303260249078a0f1101210b8080e0300460b280800000e00c2010180c00c05111821100307205c02a02d0b00b8949490140c0440c802c0f010002e00c4599070b1030001d1019400380d0700c9285150740000845002d01006e1600b00001c003403e00030705120782600f0100207034541c843c131a40d21440c1047c401440c01e42d00c800c031910030006000f840565000740080007080f400362151000d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 586162329 1250 586161079 586161101
    0xa06060b04060e0609090c0306150703030c0806181f0905010b04030c0f0e0c03190e01060608090d0203041401030608030a0804020901050d020306241309020a0b0a0906080a0f 76
    0x18541d52481e02e28040c1c82802a650054015501800243c8840d591030001c158801c8038070698565a03500c81c40007461030380c4031200d101401013002c40e0305402c0c10741c9030340220449829901c1e4100c9a8403000108103209000c800044d0844105000203080d514450078540010407008a210f44070f02e45403040482602c0c0b00740c000ca6081e1101040400030701c05c0c1d50500720b00405c09032410070812414041d00c0311860000528411000000002081d50f80350400100035805100c03900400400c0350500b80b05000e44510b2044900003900d500218508980119106107136100980042d0b2a080c03030030b2141c0c98200c01601c401818950b65103c0010100c0c414001000d074032a195030f4409030303403034a8410024400010f820030340c0034109031b01c0300d5030040e10005407950300810380a24000342488000f042e2080c0c1c01c00115842c1c1c00c00c8480914061000d01600b002c102144202c412612140d1245020004e034014808034a0004107141d00c2005694040c1c120b5503003110b02c402012510412203030711034058480152030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 586163579 1250 586162329 586162349
    0xa2307060e070f1e0608160e01020a02130f0c081501030b04110406080a0c05040f0e13021c050601080c2407020301020a080106030c090b0901030c0912050a120e090f04050a0606 77
    0x1207083c4c400341d0701508041c01300c900700610f090500300c81d05d070b010300c41a05486080c48110014803031240c0c0200600c441450740200348246569049c5407075405004a0b240c0280403504003000034072414003178200c6a210301594021b09640b0070150004401500146403036540040c0e079003240c62400400500100082c5c052520741640c1030401d29040341c2180e00c0081598100700d001e100038020210f007010510105c0758441500601910350a212128407445d00100942c01429034074a0008040408852880d00e070268007550000c0c0e9803a60300a8561040022190b84030740c2c1c0c9184a180c1c0c100074240404034a82c10041e4901b44221540482d007241c0c0b140a50f10045414000100302e083e5060148510180c200c5c90184982032074180e13101d0440c015000468103140c0c5134060742203820301c5480210002c004000310000d0315050340c2410340d100c2e4985101a00c3c0036081a815900041c090703094501e400e140038144403015a030308600034007ca2030240c0100c2c1c040c0500700c10540800e8042c000d24000c0c08100d10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 586164829 1250 586163579 586163609
    0x20c0d08160c0306110a090e04080301060c0501020c161701050c0f070c03080d060f1e060e0402070507090204030c0b04080d0f0e0d030207050108011e05060d02041a0a2307060e070f 79
    0x80060001d050342e520050545c00e123802048005000c15040e00e044a0803130906440400b114507000b80a40103a400303070380e6507104960403031030348042c40014081103c01040f445015a03d220103800c0c01d0700c8044030800a01030b07003000503a005403010001003c100c0d016031000c04105489954560701c40d44641071510300301e0744589080c4200e811100c00400208000d40e0844482c064842004c510300181d0321681e807c2c8400001140760b107844580442c0d05840d80301c01a110100d41310101031000b500180020340b401c1e400c0d8080421540003440448061b5051680103003180d400601041b00c4c05220354104004100682c0c44403a0541c548001d0003000301d109802502d809402d210005181c440305a000da4900d000d100c03601c003007880f8030769000d105846081e02c2cac00b5900c001282026020384556404001d400206490000c050f54030f190151101c2ca8465441d024100100400d00c0c444600c604580700d01ea40f030400603800040c41d6a4061000d4034215402d03075007100c0d0303501d20001035546e196000c2c07810110419 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 586166079 1250 586164829 586164847
    0x50306031203071b0203190303050415181202071d0403110606010935031e0708030f071403100503011409060402060c0f030415020c0d08160c030611 65
    0x101039801151200401c150640c40c0410000340803441c243e400b464043c44400c04403003551402e000c4e103026010f01c906105010492883c004000b8001110280c81241e420524a4040c128a000d80a03c54060601c002d0600c1091b4071602c25010511460005501c540c00000032004424414841c5803c0e030b0b16a803900d64505420701400c6c20301240c60b0050103400c280200107503070381c0205190083d641400d020b46120840c2c2840c140c0079003940840440c560703406010783c04c207208001004001500c0e1403000203801d5081048100b40720701030100c005110840c18400524a86801400315034840340624000d0503215480c2907200070341d0300548820540320204a028401400c0c2400b580c0c2c14440746e01007856042c54807000302034661401601c000c1c0f00e6040050365000d5210100320f220207136809401900e586580c0e41c00b0701c64525181281000260050300e4480e41c1c00d00c1c1c800815132000da002411706241c240360700e0440041c40c2600c1000c0700c04010300c036030200210b11071744141d000228440201071b035100201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 586167329 1250 586166079 586166083
    0x1060521040606150311040b211303230415050d0c03230c18190603060314150a05190e032113030507080d1404060c090b0304020f011e05030603 63
    0x1083c5000c10305d0f0500358440321110350001110100d9440e03004036502c50413000492060040807900010380c2d01032080c1807101c40b085d0000d414881900c40d494a03d4200c0030300c00e225810110420040d240707604103200030030401c5400c0340c1d010280d240a01c0d00d01d151a40080d00c0e60100c5d82c16000b90000243d80d03603101304803103101c16000d14080c088171842c074a03285041c01a501540c80f4400032510654004441c42c03000d9111100c405072110040c07090a6611a2139182c010000c00c01803100743d45030212100880010f91020503402030300c0b403000d40785e8041a0780c0c031001076015003000f034100e07800b088031020700031034050191241882c9050500080d565840082a00c039440d00c000160300e5210b0481c6200340314840910000515001d0360505120b511040719080c001014026411200030050420043d0182c4c134404100d9140318520860782000b034001c4c440c400301c40c00c0d0014050421003000420205015103480c5011260801052400d2800b24040141c010b100c4c24110701e090b000b003030010050244519003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 586168579 1250 586167329 586167359
    0xa050a0309170a06110f0403080901030b1e01111002130f06090503030d0906090c0803031906051e03030c030c0601140f0d02010e03010b06031518010e01060521040606 73
    0x20180007200c0040c80740b8607621900021001018250344000056403c0b1881003a80c400c0342c00880c4042d21145e0303a051520301d5500145003580000c2c0344c0f401c1805a031a21065441c041380704540c4910210003118015501c5202c600c154541078490104207119032500c07070006020844592041c1c240c05860520200d0a695407600b000d414054469030601c1907440000644208040100003c203440e205810484003e02d408140a00351100b03c000100e40b8400000c000c0d40a4007040e6080c0094066480300d81045075514018181c2c014a14a903141419070051045080c1d084000d0903240f4000801c2103207491940209000506900000010840d11500120304000548152081c16082c40200c001031841400c90b03a00906111800c20600361544095200c1213240b01c025054a0b80ea0415080350740a042d0903504440c0b040c05040814400201d5010410703040711380000301903a0030390a100d001e603001d41012540520904600007022011004584040c0c0228000c210008405081419504451348 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 586169829 1250 586168579 586168589
    0x270503120c0303070f09030204110307121a13140907061103340507260c06090105092b0605011d010b130801091b082b03060302030a050a0309 62
    0x4090169001c8200c011048940c050030519210404100d10343c1d06490282850f00080d4100f841e040000c20390301042c0c802180605c400303803034200c1e1030701d00c03414010280c413071b84600040d200215902c45006c908100081010101c810130000c5000030480840107800101102c59800651003064201705c80c5400000340113050100d00e000c0e40c5858140e464500b030110111f0340200c0504460001480795605072441c14883c91390041c140e950b415540c200c1068024040143c01904243d50302d0031044000f40015078452006015001d14103003092400156550f130820f1240c5034100c44010403101c40e41c0021141804440000c411024544c916030a040341154016040300b5403002c0301000461400803030114490458800501040d40c40422402c600c044a50329800001e07298201954441003003601e44c1956020380030b80491101d0302c0e54480d10259105503425070084070302d0301d8408620b0f0300c00401c49024008a0079040c0031506568039400b280ca000f2038408241e503141c021440b10030401d0340c00a20840186 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 586171079 1250 586169829 586169863
    0x3030e061305010c020a120c09050c13031b0e01030605090d03022109010e010c030218010c02060d09020415080a0b010602060114060d0b0a0312020f030301060c08030601270503 77
    0x341801e0744444904000e000da00d040c00555001c800c21940c0d044c0700107002c0c1035503107404c0c0d1604200703280001010780da074056042e840782070800081d00d00384200f05407810120080c007031088103850b43d00c0701d103108007032001450030925042c0c5d404240b125100810f9030085201d400000354610b041d4042604214944212608050040240a80e01034201140e44162100303001031204903214800e8003401081d1208030750b02d19508000c0c0c03520059816501411011000d0100015041809001120704102d840300c001d600c42810b0041031003044240c0c0c4040e0034607101410000b101d104420044010030705983c0301c00c0d420352007804d5010406c00c0a8001d103006003ea800180000e5043c0f00d01080c21140081f0b81e01d0040d14003046200ea50141500301c1c4640340c0d40980740ca10040d44030705200c1145043d086106d00548100b260f8000b062030700200f240d048941603914640041c0041d5101c0d20141e201038100703410001580f80785080e814054003002580b011000810100600d05020305041c4511583e0600f164 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 586172329 1250 586171079 586171087
    0x23070603051e060f03060115090f080303160302090303031303180308090d050c0a080a0c140108040f0807022e090308030403050702031c090f08030a020a150603020d060603030e06 78
    0x2440a00c40507100410b46035168035950740366804207810f00900040e1070f0749481800c0000803580c00045a01d0b0400085555524915840d100000001510741c850000c90b644104001400e0700b142618015081115103005464a490680020715542050341e80010314105401540d0130560461200e2100500c02c0200b012118a5525243d52070300510307940901071445540414204031041c815400862030040c00301020a840303c550941d500ca1802084a411103105004100c64005552003411001c0581d40c03820140c0e02d958450906034040d10701203440e0756052201d600140e0321103401c281c8101c600c02c14061a690000307503070031240034881c1c3c0c59400d0000b40d0340d043c40450021001c8942c000d4140c10810f99418203407002c0381c07404401e00c00d03c04110550a40544040343e000c07e884007140d80110701c048155440f1050107449201d010b0b20680035900042041000804120311008801880080007984945e00e40100b521000f0007202110110b641d16000d000701500301e0304006201d40706aa002e07082c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 586173579 1250 586172329 586172341
    0x3030f0524190b13050f09040c03021c1a06041a180c0f0301080105060918100f02040807060507051009031209060204090e0f060718060311072307060305 67
    0xa201041071454000c600b0300000d841d00d8540e4019001c0104501201c6036a02c6500d4101e07800855224020740b403050180021121841c5480d031102802980c03c90425000c00b8510360801440c80d0303038115501096255601c800c000704100c90340304d0180c0c21294400070250700e00b801c1000216220308420005840d143e1210802c1d64440350301c1818005145030b40c80f605034440c06000d4055000d41c030340c14500031000000100b0010010b4209900402080d02c1c248003548445141100c509034a4500002d81c0c1d022051001100d138041e00222a20a044080140342585840c455410900150000004030741300281a000f0413008101f007051441c1c04010400004200d50350040a00b203100740142480c94490356103c081c8140d680c1110014861407034104942400c5242c010f484401002c6813406500070840024080b6000d0340c1c038280c194907031250b0780b00140e0504000303070f00500d011501c10007024818008080040c981504c0481e005582d480022100710303031240d2052608103150083c0307007050308010174814 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 586174829 1250 586173579 586173631
    0x507020d083304020f0a050a090f1d0601110d020f0615010807231204051b010203161e08040f09182004050109050a0b121902180403030f05 61
    0x38500000601c0c042e8046448030004029000d07000b24461140d0002490b002074a82140040001542c581c880680341c81d55154011030070540c0e0710400100e032518083c010951601000a103600c80c40c1410a02d81c2c1c0c4c48001762051130210300c20502c2d000350f4004125a03c407e5010040d140d4002ca550050701042303484200000c100880290211041c01b400300d51105210300d4501d51a16004001c400d00b540b00d038030058010784225000e5074256054069480f540140120401059104d804d040c0c008510b0545061002e0400c02c010540903280000910820b050394168114032843d070740e010b05803040c0c845081c1400c1c0c4903404c1c4690300243c030007860900f43c506103402d5003a00940141d0071841e442c9820404c04654890354400c0000382e40d0141c6404004200702020385c0c011800307280c612004000583c45901072008000e0700c00d070701c20042c0e070208841301c0001102e2844c110081d88041c05681030000d80f00c001c0e403440302c03041e034049021030380f1110b02240c3e011309445015404200c01d032030810300c1e0200d174500d01 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 586176079 1250 586174829 586174891
    0xb091503091c05040b0f09040614090c03060307091409010c0230041214071514030c0f070b040615060527060c010f0c090e0109020c0a060507020d08 65
    0x281d0ba02907940c840d4030319805442070b81d000b001d601c044c2940c2e03800c84c400c94407082e82c410030010384680c0c90101d0220340030740d00481c207140e0201c001c0c1405149884500b820655500b000349400e03454820401c01284504550048081c03901800201c040c0d2030902800035800c6d0740c040900b843c115480210450707038820074061000e0180700d4100d04074491520b0310240d0a180e110781d410003000300c5d108a400100304403040100b0003403040d060065070201510360b540e10503018400159400051089123070303400b452148100070358210000302401c0b8500605820108551b0300420740c182d48c0c0844800c10801070011500074054425603550360861041d040c1400681280200e0761080c1000c0301c02c00e01e0303501c2c804074406603d080100007001d50307803603c0420300d40d213010344021855007584604120301c2c0500180100300d544266281c000072814a80c2c24000001d000750800e14144900d8805d2403501000b00e10a0b00c608c50080a0b20744c040c0076403180703802019160740005088999001f40c154404034a007103042d0840 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 586177329 1250 586176079 586176103
    0x60307020a03080402010c062c070b0421060617011b050d0b0a08060910110403080417010204030812040b09161703120a0b01080a0603030507111206010b09150309 71
    0x80c045071130303500040782c2c0054556001400545003c014030101c0c6038440c0308000310f107010402e0415110810b203090f42c0341c000703238460008002002d100c00c2c08501003a00100c80ca90003c4062001510341540b03c46050b14440e82c0421800e820302245403580b81000c2c00b5526400641d11070a400d0710002c400e00800501ca402d0000b0151682c0d4158202c0c0c907a281c0f22103100030102082255a10b042c8481511f449600710502e18003034901c0d041d180323030f8038164000681d02125084408642450301e045002e9107030340309484a00d481550f08110100001d100c90303000e4401403c0d841403241c070a14041c5000c08210038087c0400419a10a900740d44d4480c0280e0740c10002d44a42801d00e000361040f04110f50f03e07500a486040c0c2659111108128450140754805441c4d81401d0740d44100503144c8101d4002154614007010300001d400b00001400b084081c01c60043c00c01c4090900e13210000051400d0f41041001c0c0c00828400c400094044030307915210102c2c1c003080ca01d100281e0301e94107100307078069605c103148001c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 586178579 1250 586177329 586177337
    0xf030c0b13090f090b0708150409050d0323090a060b0105030411060d200d050601050a080a051305030d0606080a0228020a02090a06180911010e0303130e040c05060307020a03 76
    0x42c00f03001d100380d030440c085440d4004805106410842e030007524101c02202c40b440400102e41d41258240f40074042e00c08101e410001070078032365445100c12000b030070601800c5113403884400071313030381040d802241d10300e2152083d907005d88401e106a00e042c80545608600321810072070300b40709102c007041402c0c4a0b44003851080340c180b41d4800303490861101400c110306801291006d40d4242c1c0b461240032000500070002504403c204c240c0d25103005480c0b42c000d8220038400160441d00140d0900324940c08180c000c07e4079140000701b41429980e0350301c0d692200c846041707140d441c0c10080102c00d401c1842d00760421141102581003c3e841c08a207103443c4c1c50b01d6494004002c00503442c8802c40d00910080440d29005000c07505103141c9000d5103800b801a600c9801c03020080300c4127180d40c0300c1c01441103079107045e40700d40003040d0302c440107004485000d44801b020303030b050004005110188901c10712034001030441620201d02c0346880d0601614a2810340d00040c0914020010001c0359580898500b185a9150130 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 586179829 1250 586178579 586178591
    0xe0306070e03031b160e0a0b040c020604080702030a0807060f0606050307020a0b04020d140f1b06181828020f0f180306010b180d02091602010e0102040f030c0b1309 72
    0xf80313291420609500200c410a0710102c04a051032001417982d1207aa02d585051140fa1558070501003212005c464440050f0050b40210300003414101c02001954002011a649101d690b141c20080e5070120008a8106540c1e0300080b110400901916000340210304080c0c0c00c6290102020b51078501c0050002c00c02a170344800142155a02c9074516911500314404208060500111954600c1c52103190329140c8240034208401407a12038402c0c540c0310700640b0160a01c0340070b408041d030184c2c0d08400c440d48401081884404821503021052040400d80d15919005026642130440008520854a426401009410f880302c141e11304031740e07800340d02450740da540e0f80b8094103110070302c1681d24003280d040c090200000340c05001d6402804014a0b40100241c56640450402486006100c0d0080d00401c05100090005240c044251041103079400041081d5030780495071401c91707010b600005200485c2c0c580500521581d4000354000d08045c40c1c0c11850f10110400e40350300d51200e03108060803d42c40780 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 586181079 1250 586179829 586179877
    0x10e071209021f09210302070b09010912020111060408180d0c0614130f050f0103050906010302010e130f060303140c0304180f150e1014041d060103030e0306070e0303 73
    0x780c503a500134500016441301d60380704c0c0c039540744440645c1041640103110314040800d04031560421224100f8058507103045d0350386081d41268be80200054103a05000303400d410003400d000103010f100d1040b0710508049988001d0780305950003140103805454004c1c1c0760100c06000160140d428402511064240784082c0d12415808505a21a07218000c0101c04c10706030000e40301d21038000b10810740c0e40c03c540103008981e09070011000c0b28030031031f00c96030f00368000b10040016500400c1d102c1c1d140c845c003400c280e01c0d142130054a041902d0b000b070f080251441d0303600402c209241d8410440c00c2a00d003d100114a00414480d00c0c543d84d0040b03000f0740100000e9000c5400a446440d8408500c00b00b00000c18010003040c09048074141c84c13244034028000031100d00066505650419590966003030003034039a00d9198110500000705004161100f0032001e40c0e42040032040c0400089009520aa88032182010030034180742c1003050150080080c8096140c0180113540d0100a0302c034420140c5071000c010419174 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 586182329 1250 586181079 586181087
    0x2031504140f030d0c030203071b08040b1c050109090201020706140918070f02241005040516031a15310306140403080402090a14010e071209021f 64
    0x81c0200c0c0c45442e40d00c0b0034010011001d80320000c2045410045494800070035000c1e4401294000c3c002903101100d603010455109407003000300c1c00f5010081c241f50311520f40c4200d0fa40402040300c0e42400d8440c0355144d800150161601400881d107003070000d0071881d030000c0e41c1d038a154025442842024590040d11441078001c2c0c403101500185080984956842054205a402c1d81d12800150010301d02c6401c050000a01104221004000141d500c808484400401e20090000704548581900000321945c50b03009440c014031a240d520380c810580007601070100d0f000380041c41480b0b2600c6225404645d1910b4089079160007a0104036036901000c9043ca14076514807424051135003211200d5451102200342c00070a80703104000400501d0b090a14403006000e04880003000201e0220014006007491030110703400100d24100401c40c10b80b112180d020f0b580b42600321440050030142007007000d43c0d00221200745100c40700c0f42040003903455004541d544841000300001000701d00c1030080c182e482 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 586183579 1250 586182329 586182353
    0x702040e010b180714190f14030705090609100809070905010302030309010f02100f0c20070605070f060e01140c030403080a0c05070b130203010608280609021023040302031504 77
    0x11036517101e507032840c40140c8080841701a124490010740307021020300040340111200410141031050340da041d940c03040001c45e1340d644541002c0383c20000a10003ea103a4403024814010514283c64984040c42d00342520342c613010083d401200c13130178206401040503803008421264130481c01c1ca03020a8021800f04280d180105403000007080c940303886c0031800358501d00d5000c03020300b05166032400d88914540104070040800c2007805c40068106003070400516005600a16079203200798007622010445460f050201c1e6000300d40e5101c60703511000709078101c02801e1001d0ba0b20244210000e070035030505840080213040700505902030140d07a4402480414040d10540f140954401d00000d540c0c030300003860403003805410500300d000350300b40344d0041000d5001240c0840c410b0141c010403241d40c0c030b4814a510b90016165029100590f40d1400c07200584c03240308035516400c1c440d84423204629601014a180c0c904025a500c080c1c4400340018001030383d000c50030005c0d83c00c0004280929845034140f10848560b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 586184829 1250 586183579 586183607
    0x504030504031a0603100209060405040b12030c03190c11090c1b0114090628150806071413030611090a0303080403080708060d08070510060b0702040e010b1807 70
    0x848264840c0040410503144135040c150309890b0141069070b50302040e8003174480c01e594440c006000c184400d0519a220142056000709107420b14000400005c2c211707400798103000c0c010741000546410440d2041081c02400040c0c0c6051040c00505846086034036407a520304074071a5002201281d40c0001800c143c91b00000700b100c0f040400b9040c501c1c0603000b0040c40102c007a6400300c040004846590115840b48140d0f242868a4288111008003081c8900614050f003030b0765139500e102a0031200340e08400e402030314144001304a0342c01c282c5000340079200d03034144c4020000000c001d030b01d8000e808649030f00126a401803022400c0f80d0425190034050040a12480d0000c4034041e00009050340100a40c1c0158003a407520b03034290703c0300c000031261400101c4034550000b011902d0700001500020080c0a01800b48080d0f4480f420f01c1800c440035108140c3c409100c54030b01091810651402f40b1860030541910700c02040200c00071400b107040e95400c650710500d484d45500001d86128043c11041c64000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 586186079 1250 586184829 586184843
    0x90604090c033809090a021005070b041a0f2502070b0c0d120203090d2d08070f020c0a091e0c09030b010605030603060c1305060301080a060b0d0c050103050403050403 73
    0x1e8145a4025220000302c210f0b00d150101207000703250607007005075200d40144182c07005005c05980135024450891482050001040703020041000440c1c89180c45c07074001c51040c04602ea40c07a9014080c600704103409080350200703080712001e1203000a802c1440720001028003501d40c0b1301070064081a42000c2855000c900000e000094101d070b01c03c000b00e1a070fa0320042c56116901c020500320004003c902007198424850342c495200030f03ca160007944000a030b52810b142003040480d1024046610340f00700070318403000c240440240114130b038100450341030300c1c0070030b100814000200100044050120344903a002d11581c0e03500c1c040644050455031450003000071428480e03000e000c0d400411004e1548025540d0140190011035001e1050301264080c3d03600400912090322109100328003a880141c0208402d00010000103054503030b02d020b14024035520b0f0142c03c07402220300b040001c2d140000d007168407544500203c02d0018032019100d0f0143c2c5d2081ca00012160b44030319042c0c0740c078891908090014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 586187329 1250 586186079 586186121
    0x51812100e0f120c252606070c03141e030c030a060f060807120204170c19060903240f090204060e0c07020607060603080c030301030314090604090c03 66
    0x100c0e01c001808007400041008035024241d101c00c101c00789000c3c0208400c1030b904020f407441d14a10000c04100c0b00742c070078844c01c285980e9807502040da84561014080b41c1501c3c1c0f81811108070312050044560208050405101e1707042c0a681c0108560201900801c03060b8001c101c00640010007001040d007210003041c22642c80c00c00490324030540d001141c03414901428100c0100e5819005540c003400c07240b098607a40c036103460343d41e0240c940c100d818441141155092100244140045502030105049034000e090b104410809014900d441000c54112070f02440c042007005c240c5c0007242d0800c898120a80406032450070031502680c0d0412110424800d0401c049040000364680c000b0080314400c81d0104491a56408101d0000c50207c801c100c1102c814058a405814024000c0a5071071045000244a545079a50075000d070700805442842640003100510405070843c200010070b100c6c084816080010b82c80012300903109900920103002d860300010720301203003c1d8102106041801d000e201e08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 586188579 1250 586187329 586187351
    0x608010e0d0929090603090715140904020c010b0307060c0c0503010209010c0209040303021917090c03070611031923070b04080903010b1002010c090501031a06030603100905061605181210 82
    0x5294101d00540c0b209d0100012101070441c040c1c2c2500103101410b011081c1480500740400009411018125040d5501c960065081c0d40d4180000c034058500d0b13441e8801c020b200c50030300b8440745100d6001303a4004d030b10400c440d40050382c11280403881d0396811180e03c88580d8840c54101c010740983d9590411a450f4030a4403181e0303503000a6489420851540c440002e0f694007013082e40d03140301e01c0300b1050301600043c0e014821940318003590a100e0803280100c0e4640301504021811f482c490035a00720014101820a44205160010301c1d000200201e00b51810042151580c007d1b07071501170801080c2020005220340751703440030740166070032000c010850f0309000c40c0140060b01134a07a194544d000240d00c141c000c90658080d21999010300d24403038104400c0a404014030026900241c0b900d030b810f200b100c20345032880c40607002d02101e8034442c501600d124203109241040c003454031407990051107030601c44000c100031050f2405102500495551000b1001655100c0c10902c20f801184a071500300765550b01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 586189829 1250 586188579 586188583
    0x7060f020307111c0f14030c0702010905030a080a0c0c080a0f0327050622080a1e030c02090402041d0303060307053007090608010e0d092909060309 65
    0x4450840c2d51a002007412260040035144da4a50040980c864900c07007515040512542c01d0f407031720001c20b08201185150f21a0749a005030012191241240b0000a40c80111750b84003100100802042c0e004081c3da9030030f03035903184031406010418001c020010404109110091004130300a00c40c95094984220940c103012110065030343d000e8001c66070103402c041c201243d13010024083d510300e29808100b00e05000c1003010a5100500070128451001076001c64881000140b0004000250041c222a81140b80c50400c07000c141303c00e0854070300f043d0071400110390441495580c0c2c5078111100c061543d61440060010101d07800000262650407141a549000c001300440c0160001ca0445507030b181c4e20303002c1009036040020f40119071142640d111010f01c101124150800154400359580c441e100d000b000100c4013994170101460307440d256801c1d01c0c2c0c41d00b0301240307030150800c0ca0582c034030070f04140f1460f03000c5081000d00091143c400303010b000c03124045001e403070040b00002c0c0104da41c0e041c04c0700b15036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 586191079 1250 586189829 586189831
    0x22a1e01092a051c140303010602010606051c02130306020d061701050c09101112031609060f0c030201020d0603121409010c120c050d03020307180e010509060607060f0203 75
    0x460014400c02d02200165007240c41c5944101080003000c1542d007407500303018050210690b408089081c0c010040c0000d90107400481c4e00d4546800210785961404800909603242d50b0300038014004200020101c00c100f990900000c40c5800d000941d48030250030381c03002500c0040e130000d0007151010512a040c2d00403600442e00701c1d410700040e0021383e00c18280d024200c40003a1161000701a08100001071400c0008541928041c5802c000d12022608000d050034042c1071000489082000020400c003401810386000c0782c0da60b1441c0c4003010700e0130007038054513003e064042c40301440030450360700007014800d404035004001c0c512414400305a491034505100754600348800e02180b10043c00c2e9203900110003d59811800580d80c45c01200001e40341c600c80081451681d01c20840720055240120320204082c0ca9400c0169a0040e500d1070b244030000d1070055400140042410340b0b51080101c00c0a604407541510380840700c14085031981000182107224a03c0010100307030400c0103d01070b182cbd460303021b9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 586192329 1250 586191079 586191083
    0x80d06081b01030608033001090518010b01210b060f07112403150306070e1c0b041104090c15120204031e0809060705010504050d03022a1e0109 63
    0x591070110518005400b6103485001d180010303407040c0300a1400030310003261128424500e0798205401d401d48013814071f035018260001c5010310385600600000005001d240b0000c600c03014000c200712030101c2c000030100e00c82c107940001d41c130400d5200943c280c03c440d44004d0308940300910b03c6548038110a00f0751403d810684060f220305e400346040426504001a0243c00e907000d0401c150788142090300c10070501d40000d13201c602c1400d070703510160f5000c1c0c034100513081c06602c2170b40302d58800c9011308003008141d102d15800c0d007a0041001c0c1071000000c03240041503800c6580301d030b841030006034200e02140082031070110180c150b1100d920b00041d10409021650300301c1c8071991310406640e20f5038003420b05030702c203900c402864042c2241803001c3d03141c0101040c0110501c911a814a8801d900000071507a0304508130a40301d503590340d41030104100080200d407800030010305043d41411186403009980d46039240102440a648180c07024603001c09100099995070481079240045c0940ca100d41e00802e011042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 586193579 1250 586192329 586192363
    0xc080102030108030313080f1b0106061d0d110a0e0106021002070f02040207020307030206040b0a11010b0307120503040e010b0c1605280305100209132304080d0608 72
    0x4550104103008a9041c3e030060001980303142c84074000e8050704120048142c42425081c0714454114191500414840d490110000c66624150448078210307000350303200200307020410740d8400041c82817145400c0da00c0401c03503403141c80380903d007040500049600a020340c0a003030484041504220010322078141c4040c2c2e403c4400c03040e00490440704030b00c90903001909800f85801020014076140e001403000f240b01605642199949a000c2201c03500507800075080000b011070314104082d4090001c062420a0074001e000110300900840d840c0c5419001e2143e40b1200300403140d05010003042203070010141d05600021540c3e44240201407500b050151410600807130560030141425108000207a40000300609044018568060000b860786428070300751810080b8000081a001d10a543c207040e800e403c0942d41300390100400a8440245515401040c42d0481014582e00600c4001c0e000d505984070422040c0c03180d00f0200c051b80540c08034814503070b041c200701142c04040400c84110840b00900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 586194829 1250 586193579 586193603
    0x1306031a040c080a034b0f180308030907150e01080c090a0902030a1104030c030c1703070b04030c050d09050312250201051c0b0a170303073504 63
    0x15441c0c840481180140020b220024400c80d80e01a50142180d111307500c1036009629103c41030440c51182c406c01c10308403141c045c0c21001451035086961080041d04c076251504500e84440b6401c0d084d03070190b00001c1e043d10004000030700428010806040a40202001c4001d51010b600d4000c2600f52a42e00940c001409000880c2445580c9420f403890210000c148001103030070030f03004000070b40000f841e00200076240c0d0700c5c0300030b030b140e4a40080000c0d40c0240c09800311142181000d034444646540001035134001010a103000400110a0781c8420b944000909030984650a007111800e11006011b8083d01502c0d1040340e050341c00114040c21224181d05541d440440c04c010b0403040e020740c034201c3d010300d0f20f8080d10444403d000740d883c0078404d105041c03003030a015010807080700b940c014180180c115a600c08100d0359924105c0101001400340e075042d900f40102103504c690b220300000c1d210b401407280c903854000c40c01c0340c028604152000c80b03100110a410005090009146043c0e4041d500324401e41c3c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 586196079 1250 586194829 586194839
    0x301050f0105070f03321b0309060a0809120c2a010f08060d080f0307020105060619120f050a0603020f09010f06211d25051306031a040c 60
    0xd0654240075000042c0b184d4003915510107a0b500303050142003140d02c6240804032940b454884000a0003540011803103500c0e840d80401c00e10381c4140c250142178803503000784500746c4650f60701c01c129800b0250a01d00030b281d40e210f42c00500d06d0f0016411342c03c0c10310341000c070710f000b00c441002600c41098280121500e40c00c4440d028803007088510000c103e03001030b91601011103000d0080c186a5001030000d0003070680c0da480c94803400400d42143c1c0484802e135900009011801358240101504080215941441d00740d4182c0000000a0104080e07014492044101c0807120402d40c4034258140f0340d18405d00c0b072442d000200301d004260074001244200d4126558034490304080c00c03064140d522114900042505191058a202140003c81410710800d120140d20400742e600031005402c060f00701021440b04e0b40030141d8108624016100006030249041800c41c0c52034034543e400300c0740300740c03040c102101c40e800c100300c081c080c0742e040071f00808089500041a0116040c0b0f0900c124091104a03800c241c4071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 586197329 1250 586196079 586196087
    0xc0e100e060f070c080f0303040308010e0f01030b0703180c0f29161406041e0b07030e07080f1b09090c0f0a0806190c1418010509090c0301050f01 64
    0x4000e01030780211050203644680001607005248031030090f110715501c1981d800080d403a121180c0300c1da900ca81c1020090204250b04100c0f498090a1080f00019562503c402c22130000c040c140b00244c40000780c4c0c40840c00040c0250301810306009000d050100a4503d0305100d90040894481c40d100e84c1c042243c000380c49001041414103064860900c02000454800078070086e410900c0c11060003d00084400300080c0d40e48141c0d40041030100250419240c1410080803004011508110305801d185107200003451800300168499020b00740081c0380d082030a9542d00e00122a00640f01902c600300728001250800a01d04100f0343d030342c800d038422060081d0700703009403108185c8144146d940410045a001c2c90b00001101c0c1c041c0002d40110105943c03403c0b400e01d080b1050f5045046031164072440340c003c5286000300c0c0e02e83e80c070904000c0c010100c60040c80d1090310400e00071070f8506907a00300f4401320768450340458045d11401000c45940d42041d42e55020349900c00c0c42450709c1440c0300000c142055000d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 586198579 1250 586197329 586197347
    0x510020901172e0303020c01080f07030e030d090c080d0201020405130515040912030b010e0d08030a110a09140d1203150305120d0b040902030c060d0608010c0e10 71
    0x6940d110101c0614000103404032402038442e000b119504a0f94a29010001d10140c10807406541c4403800c96140d4200030341086400014030b0b0400400b4010011040c0490100d02d4110001e40741c00101d03000142100390860090202103007001317040100c1c00c008e1040b5440c04009a4088030b058500402c11b1401c00d0b0300302d11491044541001c6074083c0f80358914125400198802d4001e400d0290314806807001400300c0b028448200c41070020000c44000c0c5e0380d494496a0603102080c00d0044c070301800c842c0007840c1403d15810042020000100050f01c1000d950084090150f00086190721a50f8940c009810b0f0210340c02440d16030020b502022a29152074500410250703009052240f48941c02d41088026001044001e01039071059800000010700800002c10100010a9617948458481200d402074a034001c0500f8070450520b90304d107000d40d03000714100300100340031034035140e60b0300c030380c1e034030803024041541c040143c40d403814140603400c642019610041401c1100c000748484c06240c0141e5000720 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 586199829 1250 586198579 586198597
    0x910030309171c0302040801021903140c091309020a06090608090111030f09010209030a060f0f0b0a09020903070824160e040b13060b0c070e01060e0915090f04051002 73
    0xb00c640760f800b0700045140451540030102d483c001d85013030b4584017020300b0799100d0141800d1540b041c0510070f03c1c00c1da040c03055011190320501ca1030080d0524480201c00c0d409642c0c1d0f054450302c2d0005e54100e81e40c903d44c1c015515194003130907195001e503403240701601141003880b030701c000b14134054001a4001c03010300c05e8108082e040072245040d9216a01011a54031000f400c900d140d6500300403031a0380756001c00c94809958401c4101080d2101c4c41c20040040c0c994a1b00381a02c01404d00c4804585a50754002080903540441d80040e207488480000a00c2d12007694072080301805615114406a003028012003011707850104a15480d460301d0130b00400d0f0740c030b40441d4030000a0b210486c5c0072142c5010b0700315940390000207020450407260003d0b000700b1200e10f580081500308001910070410201488414000c02c105101c3c2c0c1e0341585080c4015000003180300c8a0391081d164007000804144403080300344820740300074060400c0b91070011b136014054181901c0c2960903106540c2c239445543d00c4c60084071040301c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 586201079 1250 586199829 586199833
    0x714070b0414030d0506150a08220b040303020a020c1c15150e04020f0d08030a020706060b0a020d030b031f11090619080705120103021c02091003030917 67
    0x1859a1181240080060070840c0c5542244200c0081c8501c00c002a0503240441c1500245c5810b2030030822100c0504100740081c0803400b4010103111035045010980c0c85500100740d007500006203500e0b2003410070400c0000385081640310911086c0350703060b8054101040203801319450340964008126620001c4404c10b0311003d0039008010008100c3c00a26506010303c0101054285484408444418454104480c43c2d00d22070108001d43c9810b44969041010545600306c0b5818161699803007488000e042e282002d8000481d002000850344c0302030020000010b8558403140c905000a46425006180400080c00d14420184500d00403522052845980c03582d107582641188182010b400c034150107880f01d403410311014107292200d43c010302c40c2ca000c03070b106540c00110320200a03051142c060301900070080240400302001c43c13000862070540c0d80403a12003820108000132601817202400c8000d4020303908a06010b010652000c05109072403081d240c8410240e210094401444041e801c84800d0b9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 586202329 1250 586201079 586201087
    0x11410140301110a020a05120301030c1e081b0909070806012c010303080f0a061206111606020306130b030607030b032407090501020c010e04020a0c15090203060714 72
    0x403a034540d41941045101500102d91200b445050182c503820500b400340240c1c00c150080010048213200401c401c603001c041d81030a6504584072455404480d004408008904d04504601c600600c00060700610340642210002150a581405081c540f20040383c01000c5800200d00505000309030310064030303a8900200b96a1f031030030803410589000150f0740582c1000100100d60507040e2605114044c6009860707100f01814018241404164006d0542154a1401006000340d0b40104000e174401c54002c0000325102d588041c181b440c074072620341850340a810354001c070010400240c025522840381201e02c500c48010503030a06065481151810764181c200e8000210030030f00a0317100e1040080003401f00c3d261080e012984000c0500c0215240c0911511501088426a80a030000300508800c2c0b01400542d00300700c0c00a0003030a00d04d509148680d8012a4089809100e03220000a0300d40044107258110401030270000188401c10303041c5d01030b008400010b00c12901586441c80c649c061200000c1c90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 586203579 1250 586202329 586202339
    0x90c2d030b0402070c081b0904050a1704090c0c050d092d08030a02100c030c0818190309140105071a09070306020d020309010c111f0605030a0302030c011410 69
    0x107122a609895001da0300340000c03000305202802e100d002c0e01d229001400007041c01940000100040100030f446040b60900300000940b0120b80400700790391000c0d030b0440c42c10303a510b00140c040c02240c00c8889074514290642c4441070b800410b800c0c5140c05038050b540e00742d03010380c07007142c144420780240c0c18914980cc482801c2d4004044000d8580200642d0004402c0e031624262411980115802c000680c007202e03900300e1a104034403c040a100d5142010030561985400160034810011b14413180ba0110000092030108140540c104001d01c075005900c1c020000c0c5005881035001c2d0003018583c0c0351080bd081030303a50080c0100c0d202641c00401d80301ca0798146240b401100d080003030800a940c080c207240000000c0c0c03117002501c2c015001038005130300c07880c007800e8030b07400c441c4d1040728a001c2181c0c0819404101102041d004c4040ca001854030205c4076210203048060300040d0303c11600741c40382c00408002e040d808406440e0174124103000b80500107106107074200c504001e80e40e000b540f0074034000400c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 586204829 1250 586203579 586203581
    0x51f0603150506031e010b0d11090108010302100201091202030a110705150d060503010f0902040e0721060e0307032c2b0f1110050f03040b0c0c0601090c2d03 69
    0x1070b100e60b501228941c001045030805c5c0b25040c0c2a0b00021a518011416000420250040e02080c40505e0801c0b81441e4202c80001d04407201803102a014210003400c14030014030130340003d0142500700c030202d0b41015810800030f503070781c1c09402c1c5440002c2d00440b8046c2c070200081070880460740300078650010b440d01e65500124a034003142404100c140c1c3c8040009164500703000700075911243c3d810000b46400d09006100642d41000405040364002040034490513095031048a20f02170848100e9051560524081c0001d0941114440e51880003003103550416600500504100ca60a44084203911500f41e40000480707060450035440750700b0b17258121200981d01080001205c0144409044126588491100c5541807206407021102001d8032455400c080c02c11344003034203081c03030480e1419950809030110350002900041c01d042e070b40c1c804204241d0310380c012f4600c50450035096400c0e650303507904020014441d2890800202c0c544002e0031034050300e44401d8003421031000010400340d60540e44220 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 586206079 1250 586204829 586204831
    0x40b0f090c1b010b0a060e010903140111030a0b031615084c0315150e1303140c0a0b0a0213080a05070b0903030a030f0f051f060315050603 61
    0x40d41c1600203101c09192203010214031180304260000000e04440018288104c0d580385070841000c1c0100700d844040c65036801440403084030b8014460f03450000c1c9031903002d400760801140d8200900d0b4080207002124100740d01181d55480218211540b2422241c403110402c0744a2082c00300740d514018100028501a07500365911111b0300e58200c810049102d204248042207170600f582c41941c2c03580d00d4040c03007107120790403040da111012034401651035079803102058844a041030b40c2c2143c0b01c04220b0110f10002d01c10b50054109004800124504001c40c09424040244d0940005608071940580301c14030404540071300c0c1e404c1e005041d54000c2030700c442c2c0050502034038007945680e003000842c0311888400503040240c00000060b103114166410b08a04d000345a40024614010401c8259950759000048a0a00382c0d2428041130400d02c0361560270003070603040c00e001c00d014100340800c0000480f462a407e030440304600d841089a480705030440844140810591904041d80410b105034548030002e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 586207329 1250 586206079 586206091
    0x503070305070609021e0a09050903091309021c05010c08010b030a181203020703031524020712080405010f020d050301060e150a030b0102060c091c02010c051b030c040b0f09 76
    0x802d0468250740400c04460401c6d00d44485403590044220075441e2000301003005100284007401700713050160410340c9030301c00c9515143c8645160202c1c0d0030b008119802600745950024406110f82c0400c44a9040404455100b11942c0d440d00d010701c3d80b028040c00b0058103031030280c01691705540d100700e1003c005110720b07001902001d1580402c80c00040c1c4192700d401171403015580143e1155064035019054840c84000104170000ba98018820983c0c00e4040c202e11032501c00c6d504905800560b0b00307034201680d5800101032942998803260a11031030b4030040007207460070f90340d8590009a02d43c0c101e8451091140410000742d00700010000944545040040110001d250300320340d04040741107240d0760f40040b040a002c40c1d00d4108a18441d078040c06565885200e0010a500d4201c5401c0001d540b14540e1a41d5500c500f00b94100c3c1c030559100e011901643c9500604803980289808000542c9641d81881144030b4482d94040d800542040e024a40007910080c0801803412070316010013042c400c0c01440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 586208579 1250 586207329 586207331
    0x706020c0a060c030b030c010e03030703080c0f040f140f0a0e091e07050a0e01060c0b180a050a0606060c020303090405070c080a0801030c1706061909090302060a0b0d05030703050706 80
    0x42000c42c0316481002845403413524009050b0002d5000d050900f003000d0142c078180406407240e0025520003000311280395034145401c0c8d480343e0700e0b004001d04034040ca0304001040e24000c680460281c150303003140000d4482038004103031049003602c1040801e1b00c0305200940c00c44080041041900d00d04a4100d42188031081a20040c0840f079094070026442d201c0c3e0f0b6451030384003150030015402c00d0010200a044c0001000c1082e60400d48007900b060120100249000900c00024019074500c2c244021003c515030160313052000d85040c119903500161704151981850000700240340c5028a1004428650140103141042841030800c801031000400d000c0a00160200c0790740014103a900030000c04600b92202c450650540c10b10f803d1240e45a0044840c00340041c0c01010420300019080ea8044c4049841e8060a0030710b480318100701000c0d80c0a0104107080c007528104150b000318003244142c080d12800c00000104a00b0008041221040640290010455600481e2107500105251401484 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 586209829 1250 586208579 586208593
    0x29040b04020c120712090b160c051305040c0e0603070b250b070311120604090201090f1503150f06080705210a0b010201060f0512010906110a020712080706020c 70
    0x9600b410584004803910041d200020707800f08100950000001000c5c5501e494400c0504182540d0340612404803144c10301c100d0020500d00300101441c0c00d6014220244c210061000403006510241c03009403802c8555801b00e000200701c40c4140e1003000d02c1a0801030040c803190389003038014080e0381c0c4043c80040c40c820161030300c0100e8055110440d00d1240c030810405c10b040c90000d4004003154182001e030600d440c4200000726200f8142407489801060449000070070005c240f006941c1022164424010030100c0000050b543c4224405180c0c2c80880c0e880c02c0c06003c0e0514401644101140903a40284503400304c24004a4810b051441d800429418a9860030141c0c0b03030345446c910900240340c21417a16000820081c4280e601840c42d00742c0080c002880240d081064600400c03a1602a050140101e050708107882102508028100c6411440070020340030000d5861405601185010025208240c1d00051400780724410144a0390417030381140c10210a03940316000307036022541036901845020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 586211079 1250 586209829 586209847
    0xd020c03040f030f02100c1703060f18100803031015111002071a0f07030e01090b090105010e13170f0c01150302271302031e07050429040b0402 63
    0x40b500c1d0700914020101c241c40d030b1060b0b104100741440c0781050302081050f100a01c0b0005000c60040d041c0034024081c0aa84070350340e40000c103400f902d4101410790300100c43c40703104084200000249004050346040c1c4101c1c142c903041280e82c0ca00c030a072100245002c0b540d00420050352040b2001d400b08051f45041407040f920140702d5450a207000c100360041c1580080c4000c1000004140c5040506d000102110107181c5001070390402440100924185511040444101c0c031081d4400284243d200d01c2030f080b9410000b2207140240801d024403e0300d21424004075030003060401081c00020f80c03202e180d1811a5503100d41e10000e400a0003015807111007130000d031a100001307006030314401e82c002c0090101589503004000318004400c002030418404c0078286042c102c0c143c42c045038065880c030101040c1603141e00c04240b600c0000c11a80074000d040003041000c81c075003c510320040700c0701120103003e9001c4400586410021245a581c13030040419400e4400d42896004040c48602c004c10042c10074000c0c4e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 586212329 1250 586211079 586211099
    0x30b0405030c0610050d03030f0216050102192124060e030723190b0406050307171312210905010e01090b010b1315120e0a0302030d020c0304 62
    0x5a80403201038101184403840500d00300242c3c1e034480342000044481c1c914042c049890360f00070381c60180400d41c641d4942c401030311107030b0100c40450b420386030707588601d50050a11034002d4103c603c0d90421758085400e440711280c86885003132182040c4000081c0c0111420341d007200103000000170780d0240c4006070301c00740a40701c1010450008140d152181d50000c00d480c3d00f00340c207000603508144010300d00a951032680c2c80c02045520f1010a05859400c0881e00c03910b8001c040740b80541c4084040c040000c1c000c100d9a6010001d140184401c0d00d4403440f0030101c0000e1800040202c414224140d90481c029011400348050005410154100414030108074034080000341f040141c4550410340340c0c8903050402c042446804075001040000300b1010015540340c44080318117104040c8184070114005003809410100d05005050350710403200409840d07140a80f00980a00c1044121803410300740b0013400001140c01203140303a069001c0e501d401c60050b041e000a41000d1845000b912050002082408803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 586213579 1250 586212329 586212331
    0x50a0e040302150f04051527070504090804050a061d040902040e0601060e011403190e030c0115060311190f0903050a050a0b090304060f0e0105070203010c170c0c030d05090106030b 79
    0x51070a1241c083c42c29003081b910703001598403041c9500f2803d004104e46600070840100f021000001442c0344100c10005903844c0c540d4075082258031600d0104a681001210b1000708102c0740292401c3c0d01039965040c0543e8102e105902420701d034038405004a5051600b6409100081c0c4010000100b00501d00c5030103160800980080700412082020044650780000c0000c0200012440b8246103107041001841c528500000b00d45540d42c4039080f052103201c00f4030540b200a40d40c040200519880c00d0041800b8418a2240c000841c0c076100c50f0180c5440108200c0300810203140d602d0f10200c1521504407100840a41034104100c059400403002540500502210600580003084001c0c443c0c113000303401c080041c1c40150107504c20041000869040510050020078a0404c9806c01403c0340c01612640b0500790300941c594a4849450382464100004d5139020850001c070b01c905664681c100c50961040c010421403981c414000c006920030241c00880e40130b5a003000104106980741c0d03e0050801c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 586214829 1250 586213579 586213591
    0x703030519050d051f08240c07050f030d1506080f040c330905150a02010906111e03070e0d02061b1e0703350d0c0810050a0e04030215 59
    0x29480b170390383d9001c1448100d003000f6044920241800c611000c00240d406d40c40d82d00220b0940701c4100004101c00003900c1581c100300e8120040da282411200101a12a030121002ca040b0764a07202809154a18040c0641c00303403190741c2c9540354162604800c00d82807940c0104100e1b818800c400c00801c000c0f07802e40311460503103100c20312101c07240303c2d5503005143c0c0d19500b01038804200282504005a503124201c01d012100c2c2c00c4001c0d580c98160580c101c1c050028140080c2000c0c0c2890640d0342c40340c1c1444010000d5000411004070200144500503510344419106400081c01c4601c1d40c01c00d82c036101d0b60111003584000e26903881c0c050071002401150a20140841503600400e15600d24240c0c14500c07840411040da0145c01e107141159920503641085170600d4030702c0324169400090302084909400080400908225112005058150702400001c2c80c0c2e8400500058042110038513100c1078641a1040242401d10300c4c3e040003103108107407500820640c110b100c0c0107860520340c405841f126000300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 586216079 1250 586214829 586214851
    0x13020a0b0406170c09060c030f0403030906020609010e060109020c0f010f0203011706060306070e0118030c08100203090d0507030909020f030a1a01021c0e0901080604060b01020703030519050d05 85
    0x34030b00035000e0140c4406021989100c100c4404116501c00c001049915803002120202d0310b403024041000d1550158400300041d030400050302000781342d0001541001c0f030b82a82e084030010f80d58041c111b0300b03131407074455461f076164801780c01403101c0038068002d8031310805804203c0b07080701c05c00c00703246003520080c202e00891550300100620442510030034909001c203503400184828145a07001c02d41d00d1000400080070031061080d0300404e603100e02042d8480101c0c88030324440c46e0ba180d05000d186410701d4420141c06103d07000ca00c400c2000d5a0007924400e1180501401203189506410b440301d5012580441c00c114680c070000c50403110501c00b40c41d0207400084016207914000090302d00b02c48280500c66031501042022000580e40046c03a5690000c003001001d82d10b019002c0c09907441c0030310050150303100c000c500021035801c3c8002456407269019080a0001d201c01d54016600d60300c080c000900010340411443c100700c50048028070b0651000c0c03504920340302d2000c04040481c1c0081c0c801d11480 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 586217329 1250 586216079 586216087
    0x604110f07060c080108030a020a0807170a09060f0309050a170705030d060501020705121e010204090e0c030601050f090a02031b0301140f0406050109090f020403050307051e150a0513020a0b 83
    0x10780c4e48080e809016019581c01145800000d140c0a9030742d007174401c0024804800015464108010070b40c0c0e0312900b0540c0002241c8075030f50785101400c041414001c00001034180d030401800709100b80101c88000750080040c0081840541320b607109185070101c0036401000401072400002c90070001800369840441c40001d50314101000203040003a5a8003003482100c4d14a01c0114a8001241c0400d60742c10104c1400d01508440200720301a004a034003d050b918034dc541501c0d25041c000c00e03040c400e94021029200c0320383e01da504111500d0740c003880c03444d0003c0040e00003503410381c59940251342081e10303805040d0b55010821408c58150740f0903002466601055600d68000c1c0c100002d40d006400b8040343c040c040e0500300300000f04244464440c00c000591101004520820143d044070003841c2c0240131b0b41c0d84c454446c2042595554014504a82c03041c0d10031460662081c08511040d058190b0540301560703449494003103016050140410304481a82405917005944400e0010001d007861181c00da25 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 586218579 1250 586217329 586217351
    0x50108062b1109010e0f0601090e1f0e010303020606151e0703030e01061a091c0c0e0c0301080d12141009060905060a03060e1009060b040b060903060604110f0706 71
    0x42c00e94035401030152240d00018000e24440320680d550020050301d0320551640e0b0000100c0b500b007416400341c240c911141c0c05100c102249240c0044040103512300c0c1024a039910305500d00315000c2448003a00503041307400070030325516294400b003641550801516013007151444c41c4030301001e510000c140c0c1c21100001e40720304044e054028448403021131002004a2446c1005601000c900c0840500d101c0c00000b800300c04640d6401444042e0000001d5560381202440c5060380541a40d40604840c40c042c2800082150420104981c1a9403c500191020400541042e035060042007040340c0400c1d1900c4040301c04a84015074a807040c800800210921031800d4149001c0741d910b50003505046003480304118654075150041e4040381c0d1300180000e800445100e40f5820441060300b03950301617040200902c1400045d8210320440300d0112420001c80d0b01c6081000114410300b0101030301a004078001034240c3c501580031010040007140c1a628211602d0350402e010741c0000412503000f9030b5000e0f2010 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 586219829 1250 586218579 586218593
    0x9060631060824010e130609020304020102160b070b0a11070b040209071107030b07140c0106030507090504020d11040e19062004030b0c04050406080303070f050310050108062b 77
    0x5005201042c646030341c0e0703ca20203030b0070a405544003440d041c041028481092521264504044161918010414107440c0d0200780e01075030054505a00511501400c80040e031040044a4225503a2001d8bd03490510150307918440414010001c681444e602c1040c10040300c5004000c0002900c241a524040e18080c4104085003801070312803402c0000c3c40401c03155000000500c54140ca4210700c1100e04c036680c000080300e5080c060b07911504800e00200c0c1d00c1405d540150411404c0e680304c0d00907034007143c0d16403c4400031075404803006980034000401e0b11000c5a20703110320524980002d440400c1d100601540702e4078004401c0310a050450051358140203000d01440346030845948003c0b002c51030344944803810300a015600001c1d0105c0a080003280c03c03113018200710740040030003900070b115450b55106025144d4204030b5114010075440f03146102c00f1b0744250b013140c1c8a6408048150026400d0000460743c1550082949800100c60ba01c9880e503080200c0c0e01c4040c2210740900c1d10210000361030882c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 586221079 1250 586219829 586219831
    0xc03041b05030a02041a19092003150d020901120606080303070807080a09020d03050c16060f0e0301060504090f0507120b16200d0905030c090606310608 67
    0x280389200d4501007030200740e5000c070b82e20300300130740480780840c41d113104000304410040840102c0d80e1010b035600b803100d0000030b500b034000d08031903040b002000b2014030300070000b05c15003107090303086907103002000041c80d0150b482500700c81d946400303084005d1810555020a51450342070300150a030206140f040000c02120780282c0c005090307118091811400c0000016000c100c2c0a0104801d005400e4000380903c100c0b60b00c5026403035002421100120300ba410081c1065001c01c40c00e0b4540d00456241000c00304103811032404450099641ca00304045001040303650a10b0558070952554030340d0800180760b42d5601441121034002c0c0e032030703805a00081c600b503450714200c0d5010302e144c030000350100800308007841c0310360b0b6000c0070461040280895503070040301c003c58581d00b2940303140c80c240c5503142800f400051481c124442074a030002c40649520805031b464000c06aa654009041c00000c0d180d800c0010103481141c240404402c00070b8414000f190b05500200d51041d46180d15010401039668484006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 586222329 1250 586221079 586221113
    0x70e1c14070f0f05150c1203070c030e010c0201080402060d02090a0f080f0706120c0c081207020f120f0901111c0315150c11180103170f160c09050c0304 67
    0x40441d1030000894017900054103c105401030200b280c0c2c00c11801070050fa085111003448581e40c0380781c00e410141000c145240d0540014841c40599103280d4040da18030100349805840b9010541c0d215070800c14503030b00020fa040f05840e003c2c00784100c0390700c03070b1000d01e40502041000c0204090601710038619010020b80c2c142c14030b80c081e00003005a41e070492031800840c03003061300c04107c00c07103d528244c80c1000a144018008800064403e4034000700c900064016000c540c01d403100d4450861035166225503502100504030b108204000c01701c00c0320030040c40e415906062080103c00c02c0c0103550705007124810b614140d80f810300014000503170705100b104010300e80354040c549090b0905003000d581000704200401030000c0d841038481030000340d040141170000c00400c15070100d50740c01501651400c2c02e10003240d41400e40b603035090301c16550405030342a0300d0354a0211070038090b001d41c00c080302c030090700f4094424100481c00031446105078004d20b8480c5e000201059580e09092400114040044280f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 586223579 1250 586222329 586222349
    0x190903050f070e0a0f02040b04060509120708120c0705090f0108062401110c06031003060b10170c0f030109021b0d140f04120b090d0503070e1c14070f 66
    0x90007102c0008500075008840c00710005031054210741541700a00ca50341019450740340208001401e05d9011000b080d01210a9502c009543c02c0c1c0081c0c243c0d1102c10780103445464000391003a02d40c8031f00d48005480c00c150b012049a661558643c080b4149a100b9500e54240450705070040c803000000f084070075088600c1c11100c075525000005039154030680d05102f18100003031009a1800d800b41001121141007004000941e41d0600340d183e203219006521007160031604000d051a81d0b4030702007110200648464548017100000f40c01c0c6a420340c0030003420500c0d0703048140940c2e60425403100c080c42c060401c0c404016610900c0f86030401c500801c002c008043c1d944440c8100d405158810303c419440c0022200941e114904d46d0a0201203024a400c01a0300b9448207071000203016861406500682008081c0d0b1008110410200c0c4c061208807070a4021440442c40c1c4045802c1038000c10102c40b86141c0701031004680e030780e20010b1501001c5121300c01607110410907c41c4884c0404404003c2485c07047c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 586224829 1250 586223579 586223593
    0x50418050d140a141209101103060d0605090a080a030204050f090603070902160f050d0906110304050906040f0c08070f03020705120a031104030606061713021005190903050f 76
    0x4035031810b0b1007194140410001d204a290311100440001e03514441407260b1181028640070b0f01c6d1581d204420155820b0381d03420100241902010700c1c040300d0203440c001d00051441c843c80e840303c0d0040c1001421400c1c40d4401e01d18240d0102c1c034441c018200980d00c954001d66a0785c90001080002481d65400c5403068003804140041560002002c07001c50b94070304805a1111110744094130101e000407409014015082606001c004000c1101c12010102d911190307c442d484180c22102495904600c0c000c56108000500c01e0746880303405140e000b45d00502c00301d921030381c8402440a40b98940003000200d08030720107010107941c03c110841d480d4001841c04604140f0140c9607a551030380041d00a0494203000260050031b0f030f1082d0000f01c1d8898411108554541e541d1910f0f4000306045e20a00f40041c0304000c2010500540045481c000d60b480310140c0160025a001c01013180d4214182505000c1e0800a10030f0a0039405036503003890b00f080d2203902c099440c500f442c82c00c0c42700d08800e00e01d85070040c3c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 586226079 1250 586224829 586224857
    0xc03020309060414160803040801060f050307061d04180606080303090a24151403150610030e06090304061101050405060c030406020f030c21040201090618050418050d 73
    0x50866010350004c51848080002c090703858100018415050f44c0074520000101e003405002005100f2612100d008200d02d40c0c0c0c50300da0842e03520741409415416004698108942c62042c0140c81c80f03111000c4540c08924944400901101c201c0b02c102d03113144141c0d8405005010321403051600800030580a10710754a48150450f89800019500070580174000107895840e500c043d151101503040302d0020032505561030480d8000f02c1903442000d4101c00c0c90444103c2074180414001c40110110784805101e85030001013181d00c0e201d000540e4105079451444540044c41081f91a010b4002c41c009155640d084c420003c0012002200c003418030f81c1058140000220001981e95100210510560301d9840780e252000180c070410f504084aa44003100f8005a00025801440c4c104d0170090314040d0300400d074181403821041110701074003083d11900b017005018041c02115021419840356010b290b51660005021528445040701c0c8a40d0704801c201d00308102000030fa8003140d00d03403d100c40014204 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 586227329 1250 586226079 586226083
    0x1030c0903110d0503120408030136020c0307050d0e030c04060b120403020a0605040506011409070807030b0d060f061a0423010c1a04210c1202030408070b09040c03020309 75
    0x80c0450b02d0090303e00750051800d20006005551412000000006482c202030510021070340080c081c56809480d0021411906501021688145411030081004c0c4104400072400203401c92134600c1d0940c002001444000b81040c00100d0348564283c480c0211344c11414203140c0f4046075a05800e000f0b0b840c065041c4000724100c0e068a40c61240c0c0410071010b0760701c0741b404a051800b1110010302300790508007408204007001c00e00e607041e00c003441c0300c0000000c9140d08001040405407410004501d000c004600041d110360000b03200007101070840400c00c842e60b40c8403011a28204044060365507141000e00c042104442000e50200303c8400c0d0354140760034014a0151520b140c0f44602461052141107400390b40180611000e40303412521340c1c500005c4001854030302200c100c5045841d020600341c4000403442e28001c00d00c00340307080c0d43c6200840020341d03501c0b078280d460183c4113000c0d448240300004800c4c0c4204020000343c0b42d0a1807160325001c211080c08162008005408c0a06006208100302d070710340 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 586228579 1250 586227329 586227353
    0x405131a0f090a110d020103090b010b0a020615060a0e12030d0b040b010c0b01060318020a180b01020106150c0f050313090c020109020f010e0f031902130902100503090c06070f0201030c0903 83
    0x411031720f0f4501c28501707100587c020200c9000007407183c44085d00010b020310081028240c0c80b000d03902a5190350362000400710864a0166801e0307404107050103200402481078000c0c3d45100d2020300300c2d90181441e100c07440d2560700f22020b54040d0a07111440f100150920f8019801840000e08085411000c2aa0f40300784050701409203c08060f030b0f49441c9018851070703031803010f070050f001382c15682401d4036a484401402200761000d81c9840c00c2800004480d44140700310011030300800c1344665400300d050380803198040c00c950241d442e110980e080d03c0205005100070b00f90714110b10501c040c0d02e4548007449050b9400400c00c0700c00c1da4500016040580c40b10100490350b44000d00c0c0240d41042c000001804050114543d00e07050310896000c50002c1401a90034001d081c0202d94200c0e41d0410907004a06403110b55000039000803001c22441c0525001d000515000368119041d90b08020b02c61021036101d03040024203135411204101c000d0199605885640b503d19030910700540180d085488851156503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 586229829 1250 586228579 586228613
    0x10207051c120903150204090c090e070516020a06030b0a1217091f080a11090a0302190305150109060602160b0a140304140115140405131a0f090a 64
    0x107030030584042c80070303c00c010407005198030a80e03070524040c14804000c000c5d005401140000e07840d01180400d80c9000c1ca091404650740d416195840d0ba41c0d008040744c96411555800c0c2001001500a02c01641c4040d0503e0203040780742c1d40003410220550404c0031018407a03203d90208060100114080b5403920302271380007a02c11110b0a6076410140d000302e414400a0500d01c5030010258000d1181d05600c4880325000e100300c50360a1081902c1c1001c5041e003446007254250303010300050030410050500500e901d900c01d0603001d1117200c00380e0300d40318a820004019402100248403c0061040380140c0c42440043c02d094401004070340914140c0d03031140c090b02e00584942d410041501ca10045c4a401e0702c140980020500360785a041c1440d005292009005a002071035003010041c0f046075030800b41050440b100100c40d0031a260502c414480107140180840101510544e26540481e00000d07503001945408984000b05242904498812150151807603910741c00c4541e500011400f034503e650450f007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 586231079 1250 586229829 586229843
    0x3070c0909022815120c020c01020c0303120109050c0c0303090625200f030d0b041d030a0e0d020d0f05101e050c1b0703060e07030807150f021305010207051c 69
    0x1110145c1d1549405100c15242e1030078514080e40035503001c41d601d90309401c00c0c2c00322220744c003440007010745034000e407100308802858260040042c0c2056030031050700b1100082c03980303140c0b40300c280204e81143e104503003602d403ea201d02c080c0203a998050040c9041c21035000018031115000304802040c81c2018a03c038030808800c01c0c014644c00b1001d01c02e414101040c402201d6a90800c503600d6805001d07620b203600c1c0319a1170003990304403490324225a54100719000001e94500908481c00343d034840c4100c8030060300031400d0207804005031204000200f6042c018030406c1d41c122030520700a40381022a071090350f0140c3c10310b21a5482e2090385121150588208840030803030340d075030320340300407040c0521041c004107490f40030b11003108060041035040540b40200012f100800300c01c920b4030f654400c0c40c4001090040d08000c06030119151a02007240041c00c1d40e400300e145441f4410210a86c2c000118061005030020300410041d0b8040017840000c21040d62040400e00d101d07024205032003058200031b0044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 586232329 1250 586231079 586231109
    0xd060e070923010809010b0a090914030403050309010c050a080d2703080604181719090803030711010f1a1009180203100b04150e0d0c150203070c09090228 68
    0x4201c07e4000c450311003000b03800c10305025030714186880604003894007074451f09086030802d2114840072044500352904040103520b014001c80c01120f00301c0129000780e81e1030041d80312030030001d02413100a0010400141000c2031f444010707a0b80d25001a0b18541c4260a07031f65000844d00069080b550b440d034010401c94002a42250041251940c0100ca15008140151001d9854110b01e41400580380514102c41800110300049400340c0762107100340204462a0300c288009104548200600c844000503140081929000c5400540036101c2700e00305141c0d414421100036610f030400d4050062084c0c1d09180c200030032031620302000e4034105c045481c80c103c1d5400100054000044541c0e07400105801402165900e540703403102004d1181c540000c03000294001c621030403034038020700a80c0301c00b070700001d21240c45458004c600904c0c849481000084d4001405928089502e841c0c2250060005c0e400124646040d0f10400107221100707a045014000c800d841e020742c0a011840482c107a0360441ea9020b08 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 586233579 1250 586232329 586232341
    0xc011d0a030803090303091c0e240324010e0d110f12030306010219020f12190f020a0929012c010f02032b020d060e0709230108 56
    0x510032680c1020308015000014480d03103000000c000d52160a0b95410b90307450303001d090007090408a090700c40c200000c0e000441c41e4418642406080c8250086440d81c400d03d0400d80d0780310b0f01a81003203421008503942e5115240789034949090304100e0707040920740b18011a406c80009140e03001c0418010382610b409001d803090907110755801040c24000108200c1c0030f62103490f10707256a40d0044030094018000c1903200044a41d05034090070016a0040c100010880f88505100180582c8048a0304070310a469401081070600d000e5030040350301462074181d00ea403660050041040c0280e0110701050301e480841244000c3c00c130441881c511000010061140c0e0000040ba45410780340c01d80b84c0c1a20400c0f40110030100c02c0401610759010a0701c40110f1315000b02e805903202d00418181081c52902828460212038a1620b0902400c1c0291001400c0c415584002400c481054000340d4900e0240d000f8440600e8200d141c050052100055400c4d00706156500390098000a48400341805000e0001c510 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 586234829 1250 586233579 586233589
    0x2070203060408071b1206050a0f0c052208072102090c072603060105160503070302060708010e0408040b0304020d30030b100c1e21020c011d 62
    0x51a40080407148942064200f0000a51141d03100710b07040d092581c0103011040c0a03034059411034022599844540301603849610207404028010900c6660b954410000613805110312400030310307559291501d501d04c5440c0d900c2018405401c41004d1280414200100400003c01405858647c003c2e40c40080c5200c2614030080f4017658025400200742040104030b03411107014140c201e00480b0301c1c03207c00c02c410ba05140f1030081103607080101e190400000b00e81d940503d009100190200760b010365603c040c0d0702e99a0444d0003402c001c900680102e824032000c20350080c0d03c140074200100100c1803504084da035400c10391082c1d01c1840e40040f00840014213650311960001c000c680c00c8a00b28003c0040940f401540d0011840344500310b90034480030400d414442c0c880d07840325002c040d000314000c001d8103a01b41c0344094592002c5840c071443d030743d0980c5802c010780c030288415482201c08140c3c240c0b004440d040580001422281154041080200d81c4e0786d00c2075188801c6040704d040c2030108152132010039 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 586236079 1250 586234829 586234837
    0x8040b1b0f030906061804110114090a090203100611031603140a0c12020c0f0415050d0b01030606050909150702071e0f050f06040b2101060804110114180402 69
    0x1803200a008020803c100c0c0300452554070955085a074150201c0040f01c1400c12582c0589010340800801555200da0794001d245038060341d2004060030b42270404c0d0f0800108120195080310003d1600401489a124000c10600c00a4811410890741824044000903503900451802c2c00b284000d000030724084c140150b1400c0f18002c00c02d034500350b81e000c2400000e4594406010200d50b0b41144000000d0020320103d43c031044c11000a01498401e03881908001c042e20803e10440c0d50a034904100240e142c0c3c13a43d0220309090701c52940c0b207526600d1403c010003240e0555000a0080032040100510322101158044042da84c1d69400802500c070305804914003210754200c252004c100d520396401041c00002c00c5000c548805a01400e025214dc05008041d070100346a140c1201d01400184000203d490150218a4808d081d070000420b00410140d07546c682039000b0404110380742c0503c828050f135480d80d002d05074400c0c00c081c3c0c0c28180e001c014a00500c174003c0300b00d82c080c50311014403070956202e404039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 586237329 1250 586236079 586236097
    0x3021c0501030807020109080102090a14040e010606180905070e01030510030203030c0f06010506190804050a0204062c0c0a0e01020f0f01020a0f0903020901050411072f0108040b1b 79
    0x40200c0c1d038603031603e501d140c2d100a000b81e02042601d040000c45003414000c403a8140005130841803e1890001d0040e0030040d00c0e1601e030352007911040120a0b0386024030900c002018103a0710070402445912071070b82d00c10959004210050705040c20081141e8000111480303548080c0f0b80001c03913968a0440012205503504000e500d0b0000140c000c4489a00007811003481d04084141c0356203980c1c6408000c414030a200c01195006260006401407034041c03102590b101d8051b50540310300c507886a0014040f10995040645440c02d03402d06100082d601d50003060f4507410074950310010303041040e00700805004089104081000d0801d03000032a910901c42c00d01c035190400c048a2000195a40070750107500900d0107500010700c003000c4003a0385841035803140102c91b00502700c9103050b402c0406100c003401c0d1b020452403d143c0d0400104000609481490301d0400c1a1040500310031007610411080921201c121030400c12100d0a01c030209515407221500f114010000d0300c11850038801b80041030040d8115 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 586238579 1250 586237329 586237331
    0x90b03060612180d021902010c1e060606030b060702150c0708030c070503010b0901030c03080a03090f14061e01090f09050a0308040b070915030c02030c0d0c02120c0306040303021c 79
    0x14001e50b51a901c1c2401d296207200c43c00e5079846400040c049070703a045035011800c4011100340040016500450f500401c0500581ea030742072044c44500e00114410b1805c0044407503650701da0301017041583c10700c01c000a02404031041c0e80341070419000900344a0400d40f090304005c10006031000d42d58001c000a0008080782020b40e9110142c02550325200c00c840c2c41810300030750910307140c4902864140d05a605a0350b0100f218564181551100f102980202d0554002d155445817018041541120100b551901c28201058081c1c00810f0343c0e800c02d9030103007440c070345002c80078552105441d440314900d040d1144804009991040318841c603001e411010005099401010000c4050581c00320302544603d02482d00000e10b80c94000c801c41d0340007424460300e421034013180707411000b5034421707003200441d40c0a5104583c200f810340521039090080c2d076030445c8081603035214500214144030101e1308040101c0740c0506441d108903130210b0b480d084001c2004080590014000104201744a4010411451404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 586239829 1250 586238579 586238581
    0x40f061805010807060509090a0e0c06041e050103060810150504021306030e03120105010e011202130906050d031728060503060a0b03071205011d0106150f090b03060612 74
    0xc611005040a010b40b120501548001048460141046450050029100140a42d541e0120070001d103c40d109440c418024070038003100d03680c0c5000140010380361451041a104a2a064018181c1d0702070b40041d06040c01c040040003c0e02000c01d02d000c0503581c80c180423030300c080340502c4081d10090b9600304541c03052000c81e02003820110407814501340c90082d24108820702c61541d5a5589001d020318684c0e10501c01c00052129500c584803006202d001810030410321010702074020166084190044101507005500300050742080c0640700040000351a0002c001e402510b0060021214660b800b02c014990000700b204500d45940003503a000b0b101c003072084030701c2202c5250b5025002c10722416120384900742c08100d40d840c09108150000340c0c02801461840e1401c5d0401c20500080d400c190b40d80d558403400707000045000c1c0390403208645003000010340c26080c40900c410840120380d01c01b082050443d131107000c194004001c482594813451082d0b480751303112030014085104401d1106440308882c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 586241079 1250 586239829 586239869
    0x52410050d0501060c0311150c07300311040302100807090f09020304020a06031b0e0d021315360e0a1a1501020309100e09070206240906040f06 63
    0x45c3c00d1101803007551080311101c0b603805819a54000ca19150550041400109491b103404000504015105450740d0b154000550f41d01811036081c00c5040c0040e0700c0c00d986c41d9000c0c0c0c2e4184640201c00710354000103400c1c581160003040071022156415414001a0f0002ca8286406900d010000b070284090b4802000e4403074440b04060340040e10200d02032039289202041c218064001c1c000750100c2c4070800f080c01500910126074032154030440baa00131004421781400b5890b42e804c903154419142801080c10100011501c1c0c4459056003c2d142c91801c0c01811500c5600e070418541050b00c03004248404114078000600040c02010a40d50151043c4140b0604019480200d42d8031004800e010080c2940d920ba038400d2241c4195605a005030003c002c7d4142514001500c01e4510300c0707a03d03003d5429003041c000314000b5141a02c204000da4003a004000d400821a508011081e07003007152541c0d83c10101000c180200409043c0704d00c41c94a415401c0d5107050f560b8080b40040c00007044e40340313142d0912 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 586242329 1250 586241079 586241087
    0x3070806040f11100f081b070b010f080a081204052407030c1806050304060b03010204030312051f0b0924070201020c0604030206090d0519060c03052410050d050106 72
    0x1c6401250180b0600c03d140c4000e14100d1100900319201da04c0c3e035004a558500c044454620090008618605c042c130480610f01102006d817218a10802c6030702c8055050845054008800754450030b1a940600d10a80c0000c40580940b1080762000114000a446034501103043c008020081480602001d0f41c003034117856040c4006020b1411a2010000424a0141200c40080e06000403040c03c1d122001045454807503401568040d01072403001500040040000342a039000303500036400690014140f141c82c50891007466045118103440d500c4c0d407103004c059045004003a00c10b01d01c205c10082003644e929190305141d43c86107401c2c240104071200e2210b9080c02240c100b0030069006201c0c100d0b40c2149801c19008450641c0e400420090070b0014402c20000e220910701d07801c8400307004600300058900016917400590b0ba11610011601416080c4020100c480040c40401c24001001989994503105249502500e5007580c00c1c080c0b50a4505050b500d502c900c0c9820130400d441c000000922941c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 586243579 1250 586242329 586242353
    0x1b0b030c07061409031c09080c010902100503010e0f09010902040c0801150507200a0803030109050f0609040210050a0c1b1d0903090d0201090e0718050406080613020307080604 77
    0x10940c020010703c85410030030807403030200716501c0944c0d50040003420301582103203110810103110840040380c0c0c0b0b55584d441c82c0070b0b0340142c5042c41d034aa4440814a085190480c80491121a04e1410606562500608043c551006490b045d1440b450031b0114002d131200b0341101c3c004075005041030150400901d40100304800034484c1e6203a401020802d0f0501130300c65001ca80ea91600140f0040040c122400c40709107104902d110320342e0048040e500024015021700181d4002d10916100181707620306051040c0440800401451040b6001c50811005946480091103440b5580ca0066100c110502058a15422501019046060810300c82040300582c0324410161184040e61925500303a603031101d1031403041902c1d48a065003080c04007500350704040503440306681c01454900c460b11780c4d98214004000d4140c0380d51000682803a00880c90a43c010b11802c01880140c6d42007210794a0f0041d5207071907030b80180000c0404c1c043c10441200b50766042103a40c0182140c0d03001c1d41e02c242803603c0c2ca0b03281507403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 586244829 1250 586243579 586243583
    0x706090f06090b06100f050d0b0d0c03061415061e0d020403051e070503060f0a06170c030c01080105010504090e0a0501020f180a05010801030201031d0f0f01050f01121b0b030c07 78
    0x115480d005e02c07518458490703504810119240c05007490340b150704407006800c0304c14030150004121000003021808d0000f8001c0218080c3d50000b5820702d005c0c443d44806c200040080100d01010030030b01803603456850031078010304421062900d001e90141003612031407149990380412103001260100c140840800e001060206402a000740b00e20204162034030395007140314080e451741054001410700c9001c0100036a203c0040300000450a03117655000f0b08811008009140c0f662125440c4555401c081000144e94102424840d046625184c0020000d211b54060491181c2d281d00c803070720b00040c041092250701c540c01030080d5100d1540c0200c2144039005038240010245900c0f100f103005081106c00841511010380d900c1c1e00c16030941d001500540300454107880d1100c11880d10802c400e60038840305007400a844090300301e130302459003c10f00303460303018003600b100351441401000070b40120003150044650114523004000b011100003031200105502503400c00c1000403c01c54003540250013800140c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 586246079 1250 586244829 586244839
    0x1505090612060610020109150e0d021f0e0f03030f060112090503030714090d0b010f0e0c1b07180b12030306030c04022208010609060e04080706090f06090b06 69
    0x95909000c12403051060307165265140c005201146039402e050b481e81503022528000803450310341c02d5841c11f56403044240d50a060355510b01c00a9028141440406500d82046c03001b40148050000355058104000e400f038000c41b50b682e40c40303c40c41c0b907080c0030424089075803805881c0c0b2480e20f450b4100d42e83c0c81c100c4803a0300203001e00707030b1290300342046102e2034442c550020003e50459544070400d5904a5240f182d120418400f409640300030364070708048000d59440b130100f1081c294980b040215024506030081460402482c0c07c0240001ca100141c3d144071a0b44002440700c40a81d065aa09004030340d000485c91713600c0c0d400d84800d0b014080e00f0201740e042c416198601c00700c0d081014980c5a01090311417a6040d0000a00f2141c5854250081d0200001085840f8800642100f000740010030b85c2e070144105135115941000300c2492440790300c0080508000c040503500c0c160352449500d00c14045d000706103e0f5140a12030600140007140300841c0d5000004009201040c145110442400c541180c42a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 586247329 1250 586246079 586246081
    0x2030906090a0309050d03140c010e0d030c140306210a0314040312120b0604121419080d060b03010305010911040605011b170a0c21090e1306150509 65
    0x1c079100094104500b50075548014200b4140820044242144c03c800d408000401503803480d030300000700c01000c0306100340d000020000203400103035040c0718105c245601030510380381c48940c00940000c0700c40307050744080c04225aa40d50380000201e0212401c450f0849915208203946c480440004600300d4503400303610303402400180010004a188103500009102c00c0c6818482664180140300c03400b41109411004580368094201040b141c0c0c005502181780c4001c4500e08601b03103c2e60040c11642c074030360740e406003c5203044092145005808131400030305c0000c0c006a20310512009611410151440144160b80ca594074203145020305200e10f002da80030240f2010042052402d8881c0034225101030b15414410081c0c190480000301c840715090751500d9228404801615104004085c61103c82d15141c244489505220388404c120301c00c508079078141e030f140d1401000d400c0034040e03045602e038466680d043c6d600d064802c18560505500148081e041c20701910000c5000e01d80e207019a4819030702c40d001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 586248579 1250 586247329 586247341
    0x60f041704030c060503100b130e01050405010e010b0315100e030d080105031009110a090912022d0f0703050f100b0d080a17011e0617070305060a050402040902030906 73
    0x36600c074034480108180f003581d01c200303c014040c2c000f8540c42000c400858070015603d203500e070360582c820288031403c280c4942003481a90000d1840d6800f40401391410000703076060140c0200740d09018090200030410100018485014202091007180f602410706003140c120040b0203002d01c48103900036032090040305082802e65200d100200e04031100280184820040000c40e40000d01c552141079591015641c1c401d840f0362110f0000340000c18111a00040826140c00c08420f0320440d00014011500820f0003030f40b50a13950701004121b614a1000c85c43d40420031403849141c0804e50180441501811000006001020034813544641940e8246c601503900c03c0000b03412181c0c468800c6a10500d00401d9102281c410f40142000a5460401e0121000c4c10840401301080980c483c40105241010756103052108440305001045181800d080e4050030b2140d1182d5208020034400c10180d40b1800500d8955580588000805001c0c0c0119a100c0d00d800544001e54801c507481310360391040c0404034035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 586249829 1250 586248579 586248623
    0x40e01170a030e13020d021b010c0c050a03051c0f0b040f06080303010306020c030903070f050102010b060a05090d0606050d06050105030105010b070c060e0f040204080f010507090f26060f04 83
    0xa07650650720307640005242800c008588a040d141458010350a00c0b403049200d40c070344000c0400c0d4401007004020b808800080c282511380c032950403002c000040d5001030000b48001070b072424443d4103050094440f000311044000c102170703000701d1180e41d905008811186051590000c03000c0041a1401e0200100e403022850981d1070368410000b15500410040005c1146c0e603000e00448400750341035030300d071144400000380340a00f00c2e00714008040700511700b04a15a024070483c41c0006007984c05905102d50008003410502640c10070601824560307901c8010044590300c150098040102440b09140981c03c002c40209400d0044a00a40c40d1500200d000c0d10070750b0a880c085135010100d003180c14181842140c2403480c003400c240e0414049140e441c65682c1c2c07400038002070074203c4000c0c840303200c81060150035190003910b80000d000c1051414005084420002c2c0c0903200d0104080d00b203481c2a01c500d003400d04d44812941d0303003805008181711340d41907492041400359000300d052462204403c01c88003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 586251079 1250 586249829 586249843
    0x1612140916061e23181009140a08070609060f09060503011701090203011d060108060603030715111207020d0e010905190306090f0203060c030c030f040201110109080409110906030a020906040308040e0117 89
    0x6c02140010f40b08015444c541c2c203900c0e80c2c0e180b0181000940740e55030201c86203800b82c160000d10100314190400d10885078001e0144002e1007042c03821180382440d045001d0401d100600074140c0f6410340c030404650720042504a040a194090020421900e030300c0c40007080e206e0740d6107803411309018140c00060b02130400590f01d40148030040143d45882d003150394414901d100014030561198403816940c4041c01d003400070340703910141d180090110b0329240000070b051007211003164060100750b10003914503036405000340701a9102503c0c51042400d1022545101c4802a44014225030800700c80808101084428a544a1080e0f08564890b2144400789495010031039007544055020f0000444103005042490707007180c01810900d0781c0c0d64200d031900e130942e1160340003903501650000d4200500350350f611450360348055035002c5509007c450380003d07080d40f00c054610f051898001c01c140c042da640d0141250b0086a1040d415070391682e03940c24106281c40c00340b0849003146140d108140c1c0d2908041407030303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 586252329 1250 586251079 586251109
    0x1521070906020f03120a0b15030103051506191a13120209010b04060c0b10051e010806010c080304110a050a1220091612140916061e2318 60
    0x10350103641c40041b40710040900d0003083d50702c0008482c0ea1901c460a0354011030181d401080070b01490f0030754459070341c0003000140056018143c1206101040944c1c503880c00f0a80d5043d1002e140c00314110403882c80b0300d010b81842c000c0418015100029281d640140c60900c142c4207542d03d41c1c0c20f030390f00c548500d401c0c060343c8039020205810001240004890408580d07014085040481c01c40351220045050100404a062106039110f14820400e6800c4441540d00140c01d05e428142042c4030303960f1590031701001d40014881d012540c00c007080c65807070304000c07000307080050315140740030f580c1d200b010b00b07000513032081a06c50b818603000d40c0c4101d02c0100810384c03901e5070227803403030f21507441c0c1030707043c2c1c41c0c10420015034400c11600e00003628450714a40105091040d5418100006090035698170b4100308101c080102d00c840e94020400c5015081041c0603040800c1d15044e2000118602c8252403034061000c2408161440d10b08031180c024800f030180c8107a0400001d03058880400005005006441c6265 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 586253579 1250 586252329 586252357
    0x1060501020a11010210050703090c0902030106270b03040b16020105061008060d020411090405091c080430020c0103090b0a090f0b07032403021521070906020f03 71
    0x142d10100c0c900e50420301c640503040c8101d40e038095203400ca18040710000d13511040000c1d1a45001c01c103101c221203a40b0080c0c8405c035811440c65260a030003500c016a420f20080f2240740400c88020180711254035480140074102d081c990b40e2030a80741c81d04144000322240004500885c880314011481403188510404010b411891805009682034034071a80080c419070703000ca20072018800580b10f5000e51641117600103140c0b0b03220a00c803010401510381c01006030006600200b40146842881c0c12103c559000030306001c8041d450754244400302c25410040070340c0701028030f144508005454032625082d108280d0a40d90409580e50044043e2500310710080d2a2100044c04680d214001c0c0d440500e02920031654040755406950350745074600740840700c40b00402c1d6102d08902c0c1d44100705442c00392007a5408030902c2c0c9142107500103510114410307001d203014500842d05000e102400c0944214150035040588240d18100e40001e0001d031450045130014080c82d041c00a4504000040c0da00c55484896 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 586254829 1250 586253579 586253593
    0xc0503030109110c0a06150e061e0102031204050c180f010605090f040f09030807050c1002070f1a0402100f020304230607110405011202010804020d03020c03070e01030c06020106050102 81
    0x2e040182c4801001c07188a40000c02c489060340004001501006214500101d041030041050403140030f2154401c040c6001043c0810520340d40d400401e80102c00400400c0c1d8842e00e8000040785103015404410003130000080a0200307000001030708401c202001c5406880d4009020040c15130b80f801940d80c10219462030300188042c1d80600060a6018000341102c40c40d0b45020380054260303002d80782a02092039464181c0c806140d4080c0b0100c0d8400c0d201c0c00c14a1420310042205c6039030b51181035202000c260701140410030402d9101c0c400d0007268014079420000844041c05c2141110f05440480c8035a40040540150f0350050080161190303ca070040c50400d460180020740408417443c030821112a104400d00560340c41c0b102030300c01140180180c400d1140004280802c451041c0c10803607a003214048030300b0060780c4c8000c140350301a42c19154122034081c1480c090385040d8801503e039034580200000804c0c0c04a0ba40081412640101c0d42001c000380c3e10700059089400c18040c1c5401a00010703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 586256079 1250 586254829 586254839
    0x30c1b05060a08061f050409050606030702190f0c1517060612090a0c0f08060702071503181202010209090610020a08031b030a06081b06040603240e160c05030301 71
    0x3d014035030000c00540041e644140040c1c0782508420f5801200001c10f10200d8140315a50480c0301d10ba5210030b041c3e81003403560a000e82c01964660340310805c0c00004c50210b02201c01c220707425038500b0030294020003030f4808a840b1042c14512940c41d490140001703140c5440c06259401000c031040c01024060310040c40e144c507061000d021140000e21044203403007015100000500a2941c61005109132072003201c0050900380490708229014148500b1035004110074040e101c250040020028154100000d20441d60410154128142c403400392a41c4808460300100d5901074004080350368046a254907250b5500080219120603000040c00580c000c0344401700140c100e600071b40e04004100c00120000d503600c80003030000d0b48111183e030601500c401c81004400300402c0314131940068032444508544c0c030500841c03c180264800e006c01c0644541c00040744500460034100d0704c5c44408581a105600c0322041000150241c0e180c0b094000aa00305e1041d4500c107400c0300e00580e9000b8099442c1d64030700 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 586257329 1250 586256079 586256087
    0x10606090e0906010e1605090303030c090a06050c100b01030b0a0f0609061b060b030307061a010f02150f06010327020a0b1c0903031d0607020f15041b080307030c1b05060a 75
    0x30300003d0000402c0b0002c5549da08202540c1b00700b000781c0d0078070341d9680103c00303200d00c80070f07254405800d02500b4804885100400b0558020000107020300203220307130041c40124050100b000322590405903840000c240d2803058800c41c02071f1105a19041c0210755241c4c0121916040c0513101c216140308a101c14000406a030048110303120000c017100c1c10f04006880b40000c0302c40b600215090040941e100791115604040c8201c503102c56400039007481b51404011604680d4000c1040c1c0d8034500074800240f040c2c0c040d922400c00c594821a81c0d10410900c3d800f010000c1d022204140e100c0c0c488c40e600003602c421403508585040c800c150200e404092203240d4040601001c503422402d00d40c980d0720300e446004841c0305200c4c0003408640100b0103402c1c00b80d0080c0c00d1000141a20140b50051401c3c900c00c0040000c40c42d4010f0b620444001e031000e084001e2a0940f1a01e420151050200041040906511540b03141c009800380d0803900c5c1c180c0d281c02079040c1d088810700c142038000c8014040121300e2809 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 586258579 1250 586257329 586257361
    0x30a05070230072603031807080a06050a0b1c0807152a020118110a08150a0c0306051e040603061107140a030203041e08010606090e0906010e 62
    0x4940c007980358070450790111014103440800ca1003450b030b000300c0040103900d0000710480000c11580012004d42070103040915280d220040240308500039800003c8400901004000010010503080c6c40c2c1c00059850498054201550805081424801400000c0c944142018078410901c00c85111032000c41d40d50441c25005400c2c00e5070310f035418404590100c1da5a0281c000701a480c0d0000681000300c840f003200781c161021409208681c980140184000b54040b410350700303103410100d2016210590701c0003030b04402c4503410038401401004104400e00c0e030103650a50003404d505105020908010000300d04a8240388181c070340c040b9140070310485800401200c00368940020340f0200d4815140d480d10b4040d03a0b03400040c80c0c0d02020014040040c801d2690b0750405074210a40900a1506a82c40c025034a010324000c40824202c2d05159100780090051000002d000c40d034020f00c92641e843c0d074040d01080030b510800c06500d4021000811189010441c03078140c62144070301c0c01c2151110041c001d01690 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 586259829 1250 586258579 586258609
    0xa0b340818030405030304060c0b0f060604140609180601082a031e04030522141c06110d0c0201020a09091e051503010e0a120c21020105070809030a050702 68
    0x401c408501340e03d05100600241095803540310005010f450300c01600781c0c0040c80b0184418a4005026042d9a104110750449155100d00c0842802d0300340002c0ca24400d0409950740324101d510803e03064118584075501c5440d003620b804006685007a07214000e4400b04270a240c2124603032401071100001c41d13001c0c58110f070400c0441c002005003074200038000c01041c0c8090300402c00100300a114518803403041440c500791031003602801442d05440d40300c40761040c44c5162084820750301c6204400c610179030002205820540c18080401510002039a50f8400c0061070189800e02d40765502060050003291003c004507500c03500002e1400500c04001c0503035110010b101641e100403101400c82da4020b07640180c0700000000240011001014215510381580d001c10b83c026045400104095000140801c0000d09161503c160030b49003941c515614806003405004a180e000744917035505501c00d9108014503140e0441585075820001d540e4012a600100040c4040100750010305001420910240c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 586261079 1250 586259829 586259833
    0x1b0309120f0209180706030905030f0a0512040609060b04060e070c021f110f01050105010c0f051005040305090307050405151509040501080a0c0905060901090e0a0b340818 75
    0x3940c00d60000354460b81c1039441c0e4951304a81c0300410110a02400504020500d0341000c00c280070300341d91117a4903801521700003000940003041580510703004004866001c0c044041c166114649413900c1c0b0010301a81c03205468451510f0014241428680300d00b805942101030701c600c695842c3d0004840742c05682d00700b05d80044100c5004490210340c0c10b06a041118540c4500580b041c0040a00340742c000c40800c3d092480e8104401001170382d8110000e42000d80d044a01044040030604003140b80660003c0030b501558901010002410b61010242011050403025175102550365000c0000384c641c01d4406400710700801e2002d03046454801c2c0c407c1c3c47c4003110010035040081010000341110401d078081400c030740207040004200145500c1e418003503c410075080103541040350128200d90814010500c80c1e80d0344080c8507000d0501001240e0000d41e00035020072140c03524405001d42c96600c180001c03011049480d544540c4054003002900720b030740e0755a0704c00281d07880e00c10380c412801f65410140d07418 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 586262329 1250 586261079 586261103
    0x30a120501121e021905190e0106050f21041b180e0705040c27061209020301140114120c090f1008100207110904020d060b1804060506011b030912 64
    0x142c540e02000404115030701721724480989040180b10340c0403100108a1300280800c41c0c2403001040740100030303041d80c0c02e902c1c20580f15070746244c051015216142c89521514922159913000306c400006103072055110b4203c2030b42c80040e002841c0d020381080d001310115001158480f400d0f07a0002d80c040004030500304211a1002d603100007050845008c1452040000c1a0f0301c0c6002c0140d00f011110900107000c403903408a400d243c60401045507100705141c01c00d0940b070b03481c41415503a00f508601c412800352041c0d12419603407889010031412083c0c103ea0300a4901508007150340308081f428400340b06d405400e054281c1d6a0703422072080da440c0109000041c40050802080d08041000610040341070003100607a030701094140101c542400b10803191156405604010058130350002d48400705a0007100403a800e4074034400119650400880a40d4696081c4100030a00c92603801c0280158000c0e00c450340742500000d07100c100f04d400f440002c0c000c128014001c100034103001860500c5640034601c600d1038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 586263579 1250 586262329 586262333
    0xd0e010b0310020a14040f03050c0306040b072105070e0102010e01150302091e041a01150f030c02011d010b180705120901020913020703020d05041a090f030a05030a120501121e 77
    0x194001f9001500a40c40f448000d100f008030400c4020f40404e01140100070314501a660914841c2005120320204124080b07240c1c0d01071190008014664004403040c0607a203411035004001c1e000312070302c49005608010080d502c0305418031a084800381481401c00e07400d410754081c00780407500a03001d00f42d180c080c01d02002d0701d5500d44080342d0003244a0264210b60051031742c00300409007410b0308484660009030300d550842c00d400190014000055082c003143c020f400401c1680107000501e02e2085154030390505120440e8198008803001e02c0441e11100100201000c16505035000c03141d15012850401c22140a2902529490f602030aa14000b61411024102041c00056071404401c042030300424003504150f0107100805400c2018503095090518200c91341d40350006c00c00c44000303001c41c0014400c044e5140d2a103601d19107140502203a489007080c0c9456a40c0b580f01c0000c100000304034150300506250f1600905040b14680622074501d90300725121031111038800d06c01040410485904480 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 586264829 1250 586263579 586263617
    0x20304050f1207030b1906053f0a0302010f1b050f16061a030c210f070b070506090309010c030f0c0b0903040f05040519050405031204080d0e010b0310020a 68
    0x518400c442941c5c190412441c2c01542003011a041100c0c0d90402c5d60070301241c0c4896004106d103181030582100f54140c0c200e203048824484089144580014610a40040c0b40000d03840003100d2090780204441c0300c1b0310340050300702c030502080205003a044600512085126101602d02520304503030491800da0b48400034040e20170390f03000803202141c5400200070342428004010786d21003415005040b850108c01c1c00204040c41c1020300341003010144024000600f02005001c074030050981c2122415611074490303480981000d1001c58051081a00142c44854044151841c1d10f9040c0c44114101610f40d5040e01d400303c0481c0b84504000300041a00301242c0c1500425020380d15a90146648500780354107500012016045540240d0a1100307102203448030303040c1c03140d40d07190342000050161694a00b95085125823080ca52041d03201d40b040c0801d0001381e00c000c004000d41c5003c1084000c000f41c3c2c045007030f99807000b445d0b68503801180241000001d950002c28044000d8070b0900002e0069003440701c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 586266079 1250 586264829 586264843
    0x1080a0308070203040e07080a29040e0a020402340c05060a171612140103081b030304030306082e0c0302040b07050f0d180b0702040906050406050402180106020304050f12 75
    0x180c0090111028840c1150051242c911400c00cac60313101d10b00c0c16a15080c007051404101260f20f008698800082801c02002e0225030201c55008105542c0c0781c0700710350990400c4441280c807a03440320104100d40c2d4814002d5581480c60b9511507001da40c4149030800300f1240390400c81801d0284100041c242c150b42200203001d51080c580111400f4000d440810018250101aa20310303142900d008404103071000030120b2141103d0740800c0303581d0350301140101044a0900300740c0070001c1d403001000340420590550400001d0326500b130111682c9007180036426800f01d41178014030083e03205000d0035000455240c0c04c6601c00355a60b05015151a5403000389c15501e074017001c4103031200c3e0801041b05c022013506101c1649102e0342403800358881c3c8004990103404582c01d10a140c28810700140100c110748a94102c9d46d40039400c0881000985801c0c00d09002405080324200e200e1317a80b81c3c46540c1c0040740c1c3c0e03541e40d05071407c96000314180303030a16050180208400b070746503902c812202461489080100011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 586267329 1250 586266079 586266091
    0x31107020a0303111203010f0b070206042c0703091505100305030a1110061401231314010804120f020a02090108010c090b0f0a03020304060b04090b0105031501080a0308070203040e 79
    0x8103c48001c0e0410142c20300c11405462403a034803040004001c160038075091041a146051400c032b5442c8410300c00120030b40b149610040c09082c07402c40c80c070301c420f241c0c40c1940e152a449030302800d801c0d51180c000301c044842c10180140144003200528082c0c0103990f0040f07034411154140321050030b0b00c03500c41c01c1c03440e0030540406001401d9001c006008200c14400300d2509151040113000e11401d0441c28010700d50321000c0700f810040018540846000b00d020301c1c0050101a00500355144501140e01885004601808111301400750b000340d0035504c50101680b2481e0003203400d02116001d540300302c41c0c0032041c10400045100d0020300340c0140e6500c204041c000c107900780000400c05c008000c06805400e890b8403002600710103201900c0e071404070304210f42c500c2c082031400581d00c0d80c1c0e42c17070090004c0214107601a0410f1808280c2e42c200711060141606982d01101102d120b0390030b0305402000032400f40654030071900400c41c04400a4011800d858210525005403410952a403540c213400600886030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 586268579 1250 586267329 586267337
    0x20a03110a060e0d02060307090906030c060906022d0c03010e07031101080c1207050c0f0d08060d02060403060c05070206030a1b2d0207090e01140109050610031107020a0303 76
    0x1400c0d0091618004800080c01181840d010010f140750005903000e2606801034040e400010014070242d1044c84640050201c41c14100005a200d0801910084940c09001d002ca41510004500d1743d00002d150100d44c00b6848042103199070f2140078803a940c0c40c131140c0103005e01c00c00a41169555082c080c1c0e2201e03410210050504510f1401c180c0603403401500168180b044180c1806410400c0d4403c035250020081c10300d084948541c07000f1100c510540710f00d0101800b444c900e02441140104001c080e003640d0703903244112a1920002c002c100f92005034001d50140c02048108005002c41d040304040c05001d08005040c49101e40101d98541d004035240c10703006507035200924190301441c600c044072003510718218914040c400c07030780c030070509510903288003220785041c060240038800c11818014003030b0b0f41c100b0302013144140c909070301030400000610310702c080c0350002085a000360f01c40c0c41d100e02c80080c106501040c651038260024800e11000a070550001c001c018096242c91422400075842030b03031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 586269829 1250 586268579 586268603
    0xa062411010903031506081308090d0b010306140604021603180902040f29031810020f1b01090c0b0d09020a0e0105090f071e02010f050108060106021908040e13020a03 73
    0x205c40d052180164014400780303e403202c00e002000144039480e814159000400a503a045064001000112000c500901b04020384c0004030400201d900008558911003211604d980c0b501420007040e80540c01c0d54045140d815915240840c3c46050701c4010540003900d152102a00c0c2c0700c0c0320b001d981c0039800c031220094243d00b003048501d501060340400c0920007006120000d1100442454a01c00078201031854004800352a80802e824000141205c02c0100210f699070104044c251064118480c00030408501004007064641d06019000105a00100040c0c0305800d10400c402d07144c100c030100b03255441d59001c07100d00503228515400003505c5100c540045030f43c5814100404804010402d001c0800c101c418080c2d02c0360015030300c4001207601d002c003d004080a20f012801000801e1904035000c1c145400095a104040303480b0341a1045075090fa2070070410040d003110100050382c80180461800c0000b0040c4281007504241c01c800e0106065076101213640014010070101d41050740c800010714 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 586271079 1250 586269829 586269851
    0x528021209010912080408180103181112070e181204080105040c230f06071b05030c010f050d0f06150216230d1e0302060109050a06241101090303 64
    0x10300d400c131840e205142c1a80c0510305540c41c5a100d020324408400c195840c117001e14202e038000d801c1040a1025400e502000c8030b02418001a0a07408494590107110042c1301e00820724808941c90040c1c840c80c01c0b04416a0300c45c214404e0f8000380034410300b412402492078881000b000031008100820741c01d00041a40c0c04c20b42820034180956a01c920581caa030139612a51001d259112050200022911030041100000104045202d080b0009100c0c281e0405a003401140d40032a003c1070790025002c40701c038440c0010054032581c51020b4900c000c10070501440c410340b00390342c21020880c480124045401030303a0f0002c5036081c0a104050101607009030b985004440c18040c02c2500810710310032103c08000344818105090000b0364065030090050301001414480310551081d5802155104100041003074280203450340800e024403441c10f030524000c100f599105020f031000342c910308001c410101499045051201c0d07a0740071280e061128054101e0100b0078284194503203a40251408a1507802038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 586272329 1250 586271079 586271093
    0x9081b070605030106021504050c0a0308070606060513030f0809040c0206070e0103020a0e060318071710021e0c0f1b040f1103060d0609081c0b010305280212090109 72
    0x1074201c1010840b06000401a007a1b000038043d02816a10050b19403540350350522600302070101020341d42119900c0000003c00c002080146030081c0221420061300351940c004940c680308071070302004100c40140040c8003180924a0242c0c40f280300340ea810340b900b549100403505940c0c0004980d070168000c10200b1550a800502011401009180031480d016480402404071070a003002035005d6800400016001c00303076905000396603480c00c412a100160b95881e480c81032404070f84040c070715018a0310061741200709802900c0b843c80030a02d0001441513403052034003903a0043c03100c174412446091007a403035081043c4400ca103400007240556400895a1f4140026901c541e40c65020350740c50220350107865564071080d60f800c02001c4032180b003049100d040c241e010b0000c01c42c002d0020320340003440e0007800e0301034000620301000200c014840c3c4000040103600b01c40c811500400c141c0d0740f00c2d07080100302ea207103000f042540c1d441c84401401c0c00c01c41c50701400003031800c50f490340090f90746440c3d1100740103803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 586273579 1250 586272329 586272343
    0xe150702090402060d0b15091212030a02130504020c0601060210050c03040303020c1c020c012309091306020a02030307110a0201021b030708061f0f23040603020d15050109020f0702090a09081b 84
    0x451001070110142c41400e940551100a00003010a0ba003c118ec41c0b0752200d104180d4014040104250340340c0103090b00741a02e40c1422b03c40d00d13000d482074075898841005a40030340f92050490403c0c450070340c1ea41e520702f074010350302036036800c1514000c00040d8040a000022540006000350303000b04522034441001615150720940812200c28010f030303c85044003c82000c440c602e6009807484511038a403c0f529030205a41004001d1850340007140c02c10f030b900e5002014520034159a91800101510411142d0315001da025010b80140c10210243c10303110040510b0f0b80000301c014048803907a5070342d51000d90030410246c9001c42c40803121203d0651030a4200544c2c030140c2682180007001600e420b0b4800001690400114074801303040344450142d50b56036024070029a000760020189000d207142c03034000714078008481802e0b00d160400100d50200d103442694070000c000106280303052865001c1140e0484003d104103805511b41920340300190311000070b803000c0c0c018000e0035155618400c0c00503041100c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 586274829 1250 586273579 586273609
    0x220b010509030a02120705030d050309060601110312041e05030408010e07080601060e0d1a0406060e090a060207020d121701151715030106060e150702090402060d0b1509 74
    0x9014407101000d40e5010901901403541140c0d00f8003030341e0f50a21420f0426a90740e0000b9814000d58020740e548540250040d80b061a4080980d403c40d600d080c015218007005051540059005100d020380340058003040581050007500068546800703440b80303203581030f04540100c829800108007013003120824042c480340449800c01421001c5d04040c8141d544040c144a04070400c00141c005443d15101d5800040781a500803001d4014000c415101000540080d0340849516103891b0000600740310240d412400343c0301181c0500000481a107500d40a9003042c40240d03800710303071001e641001800c8000b000c0c0303614840703850302406520124650740265005131300022107501070796041543e11b60710059902502e800086003e8043e1100c0050300901c04400248907015840c0c001c010616507002581d0b0b6140c2501220b0707210b40200010b00c030448601400e031000b904100090b000c42c0040ca040c8000d4034940303441d4035000500d0f03083c0358000781d811940e95501c04000d100000320007180741441117580300811 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 586276079 1250 586274829 586274837
    0x190302130516080c0d0c0807110a08041e0b2a0703020d0605041401110910020705060d0915240602150f06030a0b0903030a05070f020705010e0f220b01 66
    0x2252410101d5600c001e00d21007030003000f0001000a215100e00001e07200807101c010010800b4140203d8090850b600586262000c00c51031000e08100c00f0f4001103083c021940003083e5820a450424001e2803500a40201104a0240301000c80c0350007920010b001c0402c851401405240c260300c4e20308051000030f51851061750440340050002d40c84584000004c0b5a10141c001456030395410203078240300c80598100348950814009055080540026207841c0c2d10807a0b01c8810050540740c283d075205034030300c02c1a03003000060001a000120540c05150018004c2281000880c83c000002c0c0c00c03100d40600e0403610a42264040200d95100c903100d00141c41d00740001c01400f204503000066004000b0526806440e401c000102c845d00d081c07003442603090740215030b03245a0034640b14075600c03504112615000285030000049150384a0040019011b26603005081d95508041c01101c1c0b08510740b501642090315085000b402d038403048000401030307d00b00780a04c2042c1c030704203a007001d80d100720f101d041c100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 586277329 1250 586276079 586276081
    0x30c1206181b0607031205190e0a2004110c06190c0203090f030705220c0207051c081b011505042d0908030c03071731021903021305 58
    0x850241044048070300003c940081c0ca505040c982100c0000c1d5a88803056428101000d008507000134220101d070895021380f050003801080300440796108400d65020b80000501071581d07035444920b0000204420014001080d41460844200e445900007040e500c0a580704c078007005500d00ca0b10444502417200c1603c00e10080e1039a0741c0c000d640e03004024886100d0800361074158416174082041100501000d0200c004501e692202a0b541c00442c03030041c02250b041c40310b074401e014400b044120030350303100800d5541c1484a15030a0000c4c0d0b00c0c14a01192040f80070030950501c449015001c0030720700300381000443c0600d00340c0c0c91400340b51090341c1711500850038800003a01840c82054404180045000c0740404094007446000140c00301410107800080000305204100f44210021803040708181c40c0c8817640021800000e0390300d48100c4000108090728014916191407521042d9401d80e40b4800051b114041c58000602c102145080b001984196080820031030a112480284e0090500020401307 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 586278579 1250 586277329 586277353
    0x601080114060c0c040c03091505011508040507050405040b07230904020f0f0f04030c0f050603043f030b0105031e040302030409052d060307090b030c120618 69
    0x741c01c116590501c649008600701e149014200a19008910020828810440d503148050001c11440006a0351480710440844416070103002d041c2c12074600d0a1081c000001d04a411100035402600844403400350040004856440307025a6001e2800303805440c00900300b8150107001d0181e881d90704142c0502d00d044248640c0c0070401640d02c0104140c038003590f2907250350480b800c01d10800740c003622420700200e00141d001c012100644240c922400b8216a8292155249a103100140c407a00c0d80c003550400004000649845124940340e00707100901401e51242e0200c07001c05000e240e0680e4450b40c0342010407021681c5405040050030007800c0051071414008000c0000700b520313840155024000307401040c03c0500c01c2085070024540500c04003c68145044900003210b000751003a9200c125036000c034903510441026080c0203040040003401c1007890502460054601d05d10300396418081c808074444a5240c507081d111801c00160060102807400c445131088008642e034021015522000380c0002c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 586279829 1250 586278579 586278599
    0x10390818130b010807052119060e090a03051303021002010b0a1502030712140f0a030609050c1e0c013b0709200a0f02280209090109020d0b070806010801 67
    0x1401c440b0b14174020760f450500f0684001c1d140c90010440001f500081c04000420b00c3c01e00c091815480500310a018041d41ea81003070940070010340740d80341c2c103030004903210300007a0040004001c0507540003d1850060340d01d4000401e400420325005d00583d440d0304100310986031501c400009007000c40b845d905465650100250340b4068804000c5c0744117289080c04503194042e030564005880b000031220350352001950010f10503000300100802003070410501107224116802040e00c03d00c07180c007540342086901640c803900d080704242d00c5001464100040b5494290038003800a0711140102c4240c0382909010768030402d01700300301041710100501c07401441c0200000c90800110340b030420021134202b035440300a040c00405100c071407401c00c2002034030342741c10380e0400440b00441155400b611360034424000e24018020303d0907050414450005019001071421414080d0403444480000171992025400300b91807003904442580c100c07115104100c01c05510081c843d81c004420301c1c0c481d001c0d5261200c491 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 586281079 1250 586279829 586279831
    0x12120e03040506130509090706091d06100309020402040b040e060d0308070c060b0d0605160c170703051605030316020d0507060515090c0910390818130b0108 69
    0x184034001c0044c804502a100c40305500103480000e201e130b05981020b207161540c8402c10310a040204100c1800003414070f210f0075502e0380c1c3c84e514040300b00e01a540c1d5000c02c9030080c10019401c00b4555940960f02c0583c50328070180000e4030103000029034503400c000c0000b0081c0c900820382442079119251540c006940400495004441c508140b00100032603c1c03e070000c0d10034502a40c0d004009c5441d103005005207a04a240149031201d0090b130312000b000341c1124240041e0101422465074588000e60b900c4000000b4840b040c080d203005130a00190b050b40400d010a0b100e02582c580c0e01c08024001c04024038851421000f0290005043c0a20781c4030014009018411000d44082d0303440c0001842032480c1d40004c0004500100040120724000d10540000d03003125008502600c1c8205206a20314000d030b034030200d2417014800070052090b52a2404251a140040f021481e211038544240000d10700000f402d040c03060750f24050b00d910a58800d0042c584406515910200d003040e408112a0345c02080302 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 586282329 1250 586281079 586281089
    0x605121902030f0114040b06040509060105100302130803040608071b170706150801050105060c060a110f0a0c020310050f0f0408090a14122e0b0603010312120e0304 72
    0x10320303060011800040c0c101000300490400c594200024100d40c80c0c4280c9410717101c0c6108840b03040c05600c0306001d11040b65002c44101c030070750b070060005000758540030400301c0680401d1701d0003500c1c0c841424040c014400c046c0d8003602c40d80d03101117000d000349a08151196032125007440c00c030318030890740c0c20040300042c601040070b000840b2025882c1d9044904034102d034107440c0c00150074462201d06480c04c1050254505c0740c0025035107404004079507480e2800880302014040c100912640c5c8824203000000d004681441502c00410020300f0515900c54003d03140c403a0140c0c44070359030590207005160402d119401001d4506282108003c3c01550442c4619008503001c03865600c40d954524109265124003c407003503028041800000780d525a11022048244c0103403407071000e8104100b001d1f13686851814400076151804010b24030000549550581210884900491100c40540c080398880c0d0080c1c2094603502a20103d400100750084241c1d448014a640100600400456156102c1c02035001d070b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 586283579 1250 586282329 586282363
    0x51f03030302130b030c070209070305160315050d1a01060c031b1b09020417010506030a0b10030b04030f020f0d1d01030603020603090a210219080d051801060512 71
    0x5051420070a0f146a50301801c0c0d85040e40d075482c206420150440d400980040788608031940c0000d0754207220740500c0c0d014811748610803000410450095002e0070070400710300b01014040134001000da4400c00140681800b070382c8400200c201911510407101c6058101c00103205c0b00a2294000030792003c0e042049001c4050210042403051600125403c844640e00d1724001024030701058524a1340e00400071030b40000c40744800040c10321040e034241c42d003c950480d03041c0c10034400c99012501c4070009541c8000d020001211480d220399a0000c800340684091b070000f40184074007084030307404110403161032955200400d1040c001e440014055400b070b54480ea03c1c2d240f400c07031407440303640650000300145500500c0c49071603190000c00c83d6511860f403d415502d00c034007c01c1815038034003c2d442c0b855400e01c0740d80c058100d0524925202070703002c50800341150009420401040800c405104240c00b550004400c00b503440c1c66222041d09452039030300028414003c00000c440419800501e0600c04074060310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 586284829 1250 586283579 586283587
    0x5070f080a0329220b040f0c0207050a03080405270705120c090d030f030e030f09030c0d08070204020f07050a0606030b01051509100e03070608010303080a09031b2a030501051f03030302 81
    0x54004c09080042041504141461000030741c000490300407019044550b1b08598003659544204480c5245602c4060902c3d2810041409681010301d031a001e10316981c000c6501090b01660f01152450341213801000083c0040b0301c150190a020316034541214690400904100d1141300080701e450880320000c2c1408007154a5903d8a0300a030001800183c5240613a51560b034444c1c43c1d4611a0320540449102e4000c80c50107150601c1e0000200003580c0e00400c081d420070780580c0c244402980621840d481c4014240700980010b44104420740d4031501ca24000f0030514134601e04a2070040068011a11514114004a000440c010207803505540b0440b0805500008044181c940d203803001200c94250248400205980343c00100c0380b41200e100e0313516a070b02030b5901c1c0c08a404440540c48001c000955080f0156200700e19080c540740303158001d0f0032030400440650400550b00c0c082d888190f16102a00d0020030500c0022f22907603503c2040500001d1030740c590307925002d0041b00740b40401018954041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 586286079 1250 586284829 586284889
    0x405090c0d0501111b0d0207080a1209030c080309010e100e0d11210601090b0a12230c18010e0106050706141524030705070f080a0329 59
    0x140210300c134074601800350b6a407040340d0014603182803c1004002e1030b42c4112086603d00610000f2511704881c3e4070800780900c4445aa0303100318460002c1a41c40821030800804001300b50381c03c20f0030b002040c2c0c0e036000b95030304c8a5400015000d0300c2041b0fa110b10a1814209044043d9044180c400440008503441c882e031048901e85046801c0c0710360640c0d500f0a607100080c80c500a0f1520407074220140b4441101c41c142e036580c0f035030340c251008408100d800901605003001404100700b1009846445600d16110640a9501c841c9040010000b0003038103510440352000207042c120b207440319544c03054100040030760400d00404454001071003654100800042c1c2c44092140ca68400400b54401018803e514103111340300031031200c100520944200c480c4a4581000caa0202c00c111801980014407030031a62012400e540980042c4c00507103881415250440c0064070b402d0003095040250f0b20300045000c160500c20000b01c030442c803043c6140c0e40c000200d034025601c80000e0001d035031513800c0341c803c480c82103 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 586287329 1250 586286079 586286081
    0x308280213031502130803040b0403150e0a050601051305041101110f010e011a010503070801090f0e071503050c0a0203220503010e0c04111c020901090315020301140405090c0d0501 79
    0x7660015201e4040d030385107840302564a070000d0a11054584040401c1a11140f0017520380c8a00d1082c06500740c0d00700403c20003d46114980b0031586070004000800b105440200ca0800c860180200d4064000800612240c5000c009510f51850356080800040c585a92403070001c0128448250600406001d6200d400d0780411100e44240c82c3c1100a0107001b0741f44060501901d5001f00300001c85142810f202141e500c5801071b0b91207144070381d036410f225928000780038005207030311b101580a40d503c48903c0d13140840204121f03002020107080050101d40e080301d006085420240000380d0404081002c034540950003c213403500d03149980701c000040404100560541c060070b80c00981c00d0b50030007121045040e00880c01c01c0c4200c00560f400c0c0920900250950024800c0071401040d03041c1d68106c40306400c1455018000300b242c103042402c1380d40d4803074840f40c00c001d071950080340c40396070008014890041762200d01c5000c8003064030184a1410103010050b1100c4a00e4a500e0040d50f0901d01c4030288042 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 586288579 1250 586287329 586287367
    0x309350d02071806030c170c09070e09100801140912070302070303052206050a03050903041d090a06021207090503070e06040905011d03180d0c0e090708100903082802 73
    0x801291504541e41d03491a4081c241c82c0e00040342e00710b008c0c003455101ca504100b000302c1d01c07030301d807075900e00d01003201c0441000000072000d4150030480140030800315580300248988410038040341400076031841d240d40a140b03400c003415a00480d10300305000001c0002e80004221060701d81c182081d64803804d00040c00b542c08071019816442d2412108c01c00613040b5041740040500d208966414001d50f0303921301071141e59101d5840340c45503a1034510760401010441c01403440c0c10404030010348507032140c2500d40b9416070b00709041d030340038100a001c1030009040e0010703801c0004200079009031201074034180e510030b07068a0080024bc000c40e141ca0b010004c000e030a61024042094800320400001c4c1c0580f1403580d0b9402c10310f4110310a20290703200818520f04010701e10051341d444212400d69505011340c403501510090305040c1c1e6131043c00380100d07201c41c0030b12824003428500180083c244640e820f0003040c0c40d070050702e00c040c40500619060385020200e818016a261140b00150ba00d080051103160701c009 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 586289829 1250 586288579 586288583
    0x115120c09090c091a160b04110120120306030a02040501030b071b050c101806021005010b03060307230405040f0506010e220309350d0207180603 64
    0x480e21440c0d0605030740001001c019074104010400100300440404d940310f8006002c0c0f06841c102260b100200303185403034010000a010700a151008124507074034101c185405036011140115003400c1c0c0b00f1556800320388185129115054800c1c141c29016445e6150240e900e10b101c0003450000024415850400400f081c1580c0070748200200c1da5641003092040e1002d4031881c1c00603101c01603461507014412202a03085030480c002e00041c10703801040040c8041b07500441410301071100d991a00043c44004d50000900c0c81c2d8014012002c40342d494a012981f050300051b14004050003030010a8130002141c60660703000301c506e0848416400042102d442180104a40c00350800c02004100900107071903503c014881c608480241e40c03184014001280c04856240c002d542e0b2002d00844010b8420020348414080d0038052106c5803034034640c001070305c000c00310030a25502c0c40a000521390b500c8520094501c50500103401c0d52074044200030345507140c0c0e10a4000c2038a2900b11038290680356031002004607 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 586291079 1250 586289829 586289831
    0x301141c0606050f062115060409060608060a030f021908010c05071101020c0d03080604060509010801020304020a06030b01090504021e0304050f01060906030b0609070c050105070e040e0a050303011512 88
    0x486850000040c0c90300c0e00070f00d401103022800d44865801d110003070711b0280882c52036401881c0c1c012114940c406070018119000f020541411240c542c4a000042000e071130040c0c00850f0080c284007010f0310906004e000c15005040c00d00082012901030f41401c010070707a049132229519444048113109589141d001501c16510700000c0404003500b0900030544213100d040e038407940f024410010780e151400d00098542101c039100706440040e10508070182d100342c0c02040040c6203501e40c0e011400059098000805503035000040c8820344c41c02910302c500404540c501404000e001d0760009202d0744941c40340c64043c9401141c090510713011017a10040c001103a5295585914250408a1b40d440349000c85100a52910f00c0c0070a00c448140500401daa400204c4190349807100c905222a22800034a81e004102c2003410b4040040c4c428060a4001e01140e990506151101000c0004542840c0000081e580c80440c0d40350000c0d5020080d00d044440a480c10320301d20041c490161441424441407040d25 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 586292329 1250 586291079 586291129
    0x2010e0405070e01080c0c0d05031f060905040f09020609040c050d0c0905011d030a020d110a0e060307080703121b0b0a021b06041505072601141005030114 68
    0x16030343c080c4011040c003900340ea45103590b88807030940080500c28084050002e4210034000b1000398011402542c00c02109088219070b0a408000c01c000386035290031400c0010f4022b0020406460140196010a82040e8042021000c142c0c000b52036881156550350240b6110560300640e103018000b5540700382c20090050100c2e014844000b0728088190041501082408a2861103480c400c6c054040202020300145403201c400d0b020011f01c500014402c48064105445044090729841403090003804050005015070816108140c109940e03600140c5566000120400115411041800b0440041d0070054210782c91564100c41c602c503003100241603038050200f400070b481b9059004122800802405096100c24207258035125641910003400b04c1e40c4041624000840641c000354100c00c5600740840c4500d03114405011490320340f554115030750307000c10042025018042414024020466040303c000d551404050624041801903c04112245c480ba0031140c9903040701551a400f20580c2d9004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 586293579 1250 586292329 586292341
    0x30308150d081e070c1a0408030c06180c0901051519020d030506040c020d03050a1e0f0606090609031113500a020d0914070b0708070f02010e0405 64
    0x150707034000f100d00100401240b10912844050205a0340d2a940c80110a103103549001181c60108481e20000150030400b00000910428100014040c0d102200088d082c24038102c0c00b0385a03000c6040400c0100b54000300c0d8200c0762a51004501c5041d1902160301c4150f07500000110300c124082e45030f042d0a924000b842c4600030035000241e1903c05460395805101035680e41e0180f1040d1102c800003480580e101c0341e03207100014041e400c201d521140d17003480020181095911000000c8c2c802d0ac401c030b11141d0390340340000b800d0030b00c0c00742c4006440c0d10309022010710714155006201c0700d50b03444050300d107014109042c49566243c108151410385524001d0103905010441d02c880c002e9030301d400088183c50310803040c85100b0f40400c10034451040b0004004481c003a4480ba03501d141e40203080d0401c2603420000c4a168034040d115a16019000351580b9040d0014540c5540c584945600140c139034260505c0b02c440094854802c41c0c02960780801d00b42c4c504042e52005a94a00303440429503849070802040041c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 586294829 1250 586293579 586293593
    0x10082103131b0e0604180f02030f16090e0313050d05030f040e060f100f050a0903050d0908150405030a0f0309062a030902030a0204050702030d0908191107030308150d 73
    0x2003a141410005041503c0c1c80c000c000403240740c44264820880391244c540b007c030303120442103031485002805503080403100d110941d0030070464810f100c0340c40e51351002c148a03a801c94803c3c181c20851000c0110f1512100042300c00000c0301510400f0f02c65910f06164804000b014000d640c50103101810158550b600d41010174041e610440b059400382100340250021443c1418030b04080c5811034440c1294103895081c11900b552260008200b402803200c00040001c0e000c0101c1005410b0940c1d501702d03200e040900311703828010b00c00d01101100d03520300240008540c0102c1110603409840c10048004c5140f6203040c0c015103900b01d0098800c0b490650405411280010410f6400c200b95000000020210000f681113407038102000e90190310206100380182096806560014032500403a410503150030285000d541c00c01000712150701000c039004000d04d07804010390385901518213115442d8050ba1050030380e41c140340c1c0300181c10000c41001140d5600000004120940000b805041407203800e421b01c20 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 586296079 1250 586294829 586294883
    0x110904241a0402090a031104150311120706050d09060e0f010b1216030b0702150703060f12050a0b070912030221030f07080912030108061008210313 65
    0x148070400c00786442481894503100b02d8880704402080010301d9411503c0d42030300e40701c440c4812074000390740301c20103031030201c02034075040045200e40203021440921905101e80f14055880301031150340601424080c0d0350300181610113492101d00c000401c0c070600d00b00702c00138013011140038a2600440c420030101c3d80341900096030014041d61180c0030071002100702c035a500402100003140d003000c0d85007840041c601800658006d0503510403502c1110401811041c82c52083c1d400c500801c0d9a441d00f0800245408504001072603070322444014803c1d662140d5840341010302c4010a041c2994001803034007401900caa20182c9000d1525032f4601505140180d81d406002040220010407000c0c80d4004c0c1d0743c080b0881e481040a055100d195885100c800e452424010f001e50350709000b0100001214581140a0344c001d0540500501e80c5003000d000441346a0b005e508012603e800640150605403c85180c95071110300701010a6a00c0e9680c000c0680505d940000c01020307803c20f02d94071000641588a01c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 586297329 1250 586296079 586296101
    0xb0403050309070b0a020304061206210b010608061c021f020307140601051f0201090807080712030b0f21070305031b0304051c0614010609061106010311090424 70
    0x5030120713a202d1580d410700e40605a904001a07008000034440c4a1040340104001000712102141c5980c0360b00c0000d2075001900200c01d00e0300c41d24400581800300714241c150040c49a8244030b9030509201010820b002c0c409a8018030140001c3e4440c000c5440301e030b158a81034903612032100308044614100a449501010081d038568400303016218080101041c0c440c103c8200510301044101020040c50740e400c424400d00083d95a00c08858001c60050b100030310b00107216030b41080c4d50308814582420030b81c01e00160801014a0301c0b203404200e4807038001c218540c60086031280c00c00d0907a00b00d034110b181c0551241440a005126002040010010141c1100c1c1d0000c40c144030a10f030a6020302d56280124490f15500090100c8102030848070040d101c100240034000c0844c4400f0000800605244203900c1200040c00910041060b1903020241c5d201081580c405420742d949141c0310032841c1000c20803030502c40d481c12004a810004400b64844001e0005401c03160705480714a907050080030b4071180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 586298579 1250 586297329 586297333
    0x11040507020618070b07170f04080d090b0a080402220e030a0e150304060b04092301051b030402040f0222080606040903081810060f09110a0203040b0702010207030b0403050309 77
    0x2088882e80424040140c5d0f403040e10441c202181a114065040030031414200404401c11241070b000c0141001000940200401043d81001c0004001e003240025448464507040034050005401e5100b019550040e4040b6280001e9082034003148a440788114000d82d10285400a0414a484080050143c40e001921031000a000072005d110700d8400d41a0321440c410030400004d000601242c4c0580451080078000240d04205990f803209154111a981001c2d003400381d2040750383d54001d0103410350002c90b03030305041030901e48013078409402c0c08007400c000c0c451074542040d9840b050702581500d02c6c0d036000a4240c0d0340c0d440c0d00711401030055218007450000d4060034000840e03508040c06540c0020342d0594078807110780e8860b910324041c81c20f8086425010300030f402c1090b40c1a490b0f07002c3c1c0c0c4054500c82c9178558500e880d008410080728101418404450300903c0210710352900442a94121000039031807076551324043c40100d060111a8100414000d400c13000d00046c5584500510720500220003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 586299829 1250 586298579 586298611
    0x309060a030912022d1e1b03070f120203030904051f09050f13020315010906080c040c02030403080708090a060504091d120d0e010c02012c0c0904110405070206 70
    0x5400c07070325256003c5d030041220004660140000610340e0300b006212201c0426a012092221809145c101d45801c155000b0752011700385443c0a03900036020040504101c0061840b00d16003548140001c150b4482d48411303080101111056460502c00c540704400000c00400091070418a81000a2000c5100703401d4041e10380b8010564488a20886020306126884504259201c4101403101450003401f01e0301809804025696080a9003505021b0512090003050480c01c18640c98640300d40c091106200e5401d10140700c1071182c01000711804e4a400041103070781d0302d05d02c2c1880f41244c4180f12020380c100c0c1f002c10b00080e0b1942d002000d40142c9548a0091148004011060288104910160720035410421000e500781c0c403483d0040401d407100510200c1c0800c2003000b8203085800c10302004001d80d45496800c4012124842480014900c0103106004000020748a541e9026105d0707038103014007000780c04942400740c01e03200885543e8008009015500e01007000940b100d0060360701414500f4018 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 586301079 1250 586299829 586299863
    0x30606031e02090a09060902030f010518031e090a0f0305010519201605060f070f0507080a0c080403020301020a0c1403040803031b1612120506010c030309050309060a0309 75
    0x10620410903900100464121380340c1002c44401089900011030b900c1c2c0d40c40701c44800580b01401118206840000001541e2a09240c00c0d0b80b030100e20080760807103800801c50a18080075200746090f924000c503d06a0b01d907c440404a075406a0542040c0d4030803081c80000000c100b015003000c3d100300795030003600440340040036000c003e5034102411039000606040c0ca842040034160090001c0f501059a13842c080300064440d03600b004016284c0d0b00a030611101001b5805030131440041c1042424030302285402d003035071610030650244000703640070403810080800600005400340c40241d40c009000f10741d40e800095018010a500002c104d9584948640c000c8081e2804800d44003211914400755203166520245441a03a0004c8d40c1c5601e928428401300901c0e16590b01200f80c50b6101d80300410208a00c0c1e03101903e414450030002500ca82130804000003668011203d1945030f0b85030a004c1000203552421a00394000c44040d01d41050010404445070399050708580511801070010000380a018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 586302329 1250 586301079 586301123
    0xa05030307050105041a06010210090302190c0e1f120c030c06080f06060c070b0306060c0d080f06030102070f11150a05040618060807050c160308070209130309050111120403060603 79
    0x207c59480c050b802454944080458607001102c80c94400d2041c1c0341c0242442040381a000000c4605581d07103a00da1070180807403100c8600f05c6400920384606202d034640d0324104202c080c1d26034003070141e18065480040741080391075483c0d5000746600198010b000d5458490041c00b911080f921400150025004a1f43d030b41080c07821501c800c034a000c00307460042d0a00000030003940c4003401d950b8219008001151001105200111640300070740c0d030741501c1d414101320300045880081c1c80c440c840c2c0d204001d648002210903590520043d40005080400715080c2c0c0002c000c03410038400c194035210700242e605038030755009000780103a51030b603102d1896007a5500080440214580180000308234003c0104040e42c3c0960060302c40e240a90f0110f1307000b001c076203c1900c04c011030350b40b0451f540c100105076907046181030340c2c20680c40789109012a0700f044054500422130000351040c641800204030748546159030070702c000c2c5050184e10400b242e650b40d0304c3c9003043c018481d130b102c00c0c0c0e103052050b00015070410031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 586303579 1250 586302329 586302331
    0x4120f0c0507090209060903010c0207330f21230f010506030c0409020c150c1908070306050a030b04060e06162024010b070f110a05030307050105041a 66
    0x2c0402c1810070800341c00a50140354207980c00b03007080c04140e5040d5024011110140d000e9400740c1400781c83d00404000c0301d0003140c00d849041507401701065003181d21410500c02880b21703251050440c0c44950080d00c44086004481d092508184c1d0b04020b1041e050b04860031685075181013005e011a9000342d041e0490064404241d90084000104454640040656046284080030714a8907a8444004080b80d00140a400045d04404444106500803022995101d1000e06805160590181c1428408036911a0900c1403120403008900c85c01d100b6842013018000c080c0014170426141d04000286450803103040303460341d0504082c07168030403020804600583c010150710500300841c03102a100343e091440c05400c00100d45082c4030b40820200296012a48010205207da09a00405a10440058120b07112810082105100080c072094045842603005103062261083d440c0015201c1c9903030341d104941c14800440c0d6901401010340c011401107109010715128052100121010000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 586304829 1250 586303579 586303583
    0x3030206090c03060a0504050c090108010b0f060408030a030c050415020127020a030b0717010b130501020303010b0d020f04271b08010510030e0f15061c121704120f0c 73
    0xc5480481e017401840d03080140c0062160040c1d61035040d2020100b00520403da00200e11a0745a0841c0e10b481d041c0722a0700102a0340c2640c0703240c58103080800301075403880b50300c036020201641d07054108012417144054a01400904448188100c81d402009018101850101c4104d1015078522200b5214005070395220310b0703014001120300f6285490f0780189005c010040706c280800804800141d081c3c1001541c040c00c0080e01c00c41d1240b941310140c80503103003950402e50555104000500521015406a8000c0003840c1805a42d60056400c0c04103180141d90040811000da8400c2d1003c502c0458580c2e1f0a404000804214107a400c811039036200304405011004100000d0042c840c900345591805d10f8054141004500000090080303072400048480b5a400d85e003108005003540825042200d800c4541110501c00003800c0e034400c400d00620303103c002084260728451440d4414003814184040014040e2090a14501800c214001000044520000030603940f110003100d8017417142050215 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 586306079 1250 586304829 586304833
    0xf0a1407051207140a210206040309141c050304050924010e060c070311040c02030c030d0e1f050105040e0607020607050903010b1f110a080711180f0103030206090c03 73
    0x20411068400d40798443e81058030b1000003e01540f508550801910344207900c44e2104016090601286010070f442c5040c0d204115040407051002107a030085040e070540c4c1c01c207080c0d230798405032030400a800f021264012401400c807110781d0000348140070024108030359090714122456502c0200d0f4100030100300042015190600c00c20040c00e5108951410208034090016454280e0f40d5aa1910b00b0080340e004881d10000b9003221310b4a800c250240c01c5200d1703680d00080d410503416807041512405040758050010341c0d07907ca0740c2c82c108001c2010310402d00010b801d0410300d48080c043c910181409002c0c16000303a00341150500701d040300040310303440b510284d400b410f074903104c0d0740084a05602caa066958150b40712182c1c4042551340d5484101003c014240d0344110011448000e013003a1360b580010a420740201020b81c0c00708240340d00300e62403107900014100c859426000002c42800b4178802d606c903ca44a03504001444440c000c0190507640242c0854400d0354810b4030103036a407503260380002d400d5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 586307329 1250 586306079 586306093
    0x207180207021c05103e0f0408071a070203031e0408031602030d0c021003020a090905130605011509120203030922110f030c031003080f0a140705 64
    0x14a4199016000c030920041051401180720002c0c1d40d110040310006445a40240307000b00c240015038820303110508001c0a4480b42c4842201d008001000d01406211b04090003000f04541c43c40901d085440c03810b1b008040700e03125034480300303c1590b8910070300644005801081d110203c008034001550040c42d40100112b1800c00b41c407103240000200c0d50081c0c0b261400134000803905e26014400380030030910240d11061030300441c0c0101031130302016041040038040b40c140e500c805030302d4200c0d10f8184c04d4454240941c1d56903490304103e03620502030f48820121403070b0005006917403a001c25107101346402180309225590303c400641c2d003000f01c1c111100b0042030040c0b90408ca885404403908440c1c90006041c0c84c10700c4e20150102c0d8400c0c105684680c40344940d2059aa01002c051040c251490300002d20305e418143d030000115040d2101400b41c04004c440400043c10034406c80d152540039691080d0100e03228103d0000c050701c80d41242d034090b80460b1240c003141500702d101d40700352207900d41c00030f0040c01e075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 586308579 1250 586307329 586307369
    0xf031e01051e01051c1802180f0f0405070f0609032021150c13090204080a02130e0708011b0e0d08032a091c1a100e0108060a0b010207 59
    0x12940a807441780b0504035011a07111040000780b08420440c6010010054a055503104000894a06100407203098100405100071140020340d40c6601042642180010392200d0800b145400302d503511201d01000b0740340010a086502034458800c07248900715614003140150203070319480c5a41c800c1250850402d0039804180b4100500e039520381241c0ca000e031142c0d5851035110a0300c00c0700889030411210000600003402040c000f60705070081543c21402c5003020704003110186c0321000340e00c02034070074054076980200c0700c0510340c84658441184401c84007070503610101c8a002e8402404080b080000d02c04d00c0040090045103501d0400d54028115404924603968a04440c0c0010f4101d01200c0d0328414030030a950a5114007411403a0000b400c0b03a00e400c0c004041003102c02d42c1c0da81d12002e45d049441d01c0e00008074045468001c0d44102c1421a42c0703035480c0e102c1d1250025044d44400111843d030f800005d4030000100e2001e014a10a98040c40015a00e80c0107903500d8001744513881c10070b0400401500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 586309829 1250 586308579 586308587
    0x110604030c060b0d050a3305090c12070608180105070e03190f1202120d2403020d020d0302030904090804050406050904050604060c0903150b01021b030304030204020d020f031e01051e01 81
    0x30703030b40d080f00560380d01f66080103124050a60780300010f0781d0f80350741d240103100f2125000c00c68400c07a0001140d041e490707040100300454482106204800034406007401060441c560441810707203514104008001910b081d000c02004c1c48004036556009008006916608840144034540c2440d00410441c018902a681c0c1c4045005e40f02115401c50007010a207a000084180c02420f0080002e980400c0d130ba500c9180c130f01e0310440f05140ea049400388420b82040180c803451402d110f0142c0403135013002070728042c0c1000c0c0e0552080e00000d65016160a05000c100610b81000d04181c49060720200103142c3c490b024068250380684001d0034940c80807000034009491900f266913041201e00e081001b056581d51042c60fa042840d021403081521032050040d15681040988a02d40c0e0306040d4215406120011985030b12440c0400380c011074000401484144040d012a40503864070006030342c2da850803920201030056101805002c10401c04000555881c2650300040702c0144444281d60080301c41c0010340d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 586311079 1250 586309829 586309853
    0x5101b0c030506040305040f0e2403010b04020d0f0e06090c060705010b0907030501061b031b0203030f070c030317160c0f1506052403010e07110604030c060b0d050a 72
    0x840031500900d000c0700241c42031040c540202e00c2030312019180c40c1030092000d2454100d400100c0c000d00c60f01c0412858428203c0700c41841403144130188020b01040380803902410001c001141c11500010700c1d032a031301c1c3d601d034018422201071400c00c010120403000043c0e103880c400d440005c000e074023a442806241c80c10800901c68035214000010302900d040b404111070800807a071940100741c1c0c0d007004100341500404401c000e01d401d001c505079508220f0350060006c20648480d01b883d24149414502152810070454904080381d086030f5803180140d103065807c01d40c0700e000860028400e4183c0712007402d40e131016240100c029030448024401c4811040358a42903198007a200d03200840c80c444082332101808011107800103902040c06030600742401018258001d5111040c0007403114001a40281e105690564440c4503200c0301a4480c0c0400701c2d00d40300303000f118044900401d814001050380100c4500d0a5600c210720030300800c2800d40c104121440c0030700000d055170700504449400540811482 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 586312329 1250 586311079 586311083
    0x40b03070909031e0c0f2301060305010204031202151b07390f0e09010902150a03050a02070b0411210105040b0112150504020a050607030305070905101b 67
    0x15280540d4803140a0160307402c010090700482d06a94000c51100416900d8006800107410134200d00300d000e03500e400a45130165405824030721011000c8980d0a2400034003011008008028888a6201d007800e50003580103200856106800b0311441c0740b0a4004640c40e44104140d2104500f00d603940100c600380300c104007050266855042250200148901d104141d440f11030441501ea00b91225271001e0303400201c3c0c1030341c6003141154002045000b40d44100700007030b914048880324443d1903812905001d0403840d040294002c1c407121807050443d44103805001c080005139002e00140c2c550f000c2440482c400c1d5040175050b07440201c00200800e4240001e00351b24100035000706504406407103000846000d6080810140e5101d8040c00248040c2050b0700b0b000d010f42e441038240000f101c1e07440c000400005414401e1031922800020103550f01d83c40c40900901001d4a81c80c1e1303030a050b18006009040403103210f0082502c2300c5020886082201071058541d103162a041c90f040c0c60310801100030b521807201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 586313579 1250 586312329 586312333
    0x20102010230060102063904060c0506010f23180108010603030905031902100c05010615180e070c1103070e0103120c05070e0618070f0f0905090105040b03 68
    0x2c14480d11a1a105003120740c42014a1404010b448608031400050b0140001c2d04550000c400c2c00308643d00c858020010784a040a0003d031a51240071013032010f03907581c1e13141c0d5800101080000d01580c00007100350000e4421000e03135480c0d0382c132507500488030a40c2d070040c0760801d0136003d55145650018950703092604e20080804c181c1c030b0b000ba030601c0c08288098012443e981d458100420401d60010f0f5400090041200a06094138210048030400080703035401134415140c5024011105006d03180c00d456194020000703100c0291540035840845a656510000040811074032441e000008807c0c8410340b44582d0210680d40c454403402c5800740340000c0123a910301d0b820b440350001680c007089648010012500c00c80c40c5585076080c00441d020842d081c0200b0302c1001000c00b80001e01c04101d00c800c0c0e9030030740320980107610b8502c0410100d1410740c48128514552005010241e60082e0021014040d20794920101500f0b03c3d0341120660003500c16940c1000c84003006001515040c0c200030b21040300030381 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 586314829 1250 586313579 586313587
    0x40203071803050c01140702060d02160b0405030a08010527150d0c060f050301120204090f0515011e0e011404090506100911090f0d020a12080d050f1605070201020102 73
    0x5031100019407961046030b1990000d403101442d035803c41000d004000c00b1500072810211607070003080143c80381d0020446040e6000541141d500391210540446035044180000e00d03280616285960380c0c40962000c01140040c0000512440e09003040d02c035285116560828403010285141800702c001b4009141c003070400f0f0a008490740360240100013032400303070248584040c94404080e1203400c00380c0c00f08040140802c014440000316281e60b080017641920001107007442e90400414003484600c000b45280120300a12a0f940c2c070111816041e035100300301c548003c0b0000448102180024451041500408401046180540c0114805d241c001900100f0980c110703907550781c18030600f25490780b402e161103a410b20200d8058480c58445400d412891441c0424078800104034a000048041c4101040b0a6610464039624410340060412141510000d40746181c88502501310340c203c400c80750318040000d40b0042441150710301620a41d0510b001541380c4403022101e580c80004180e0556400308 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 586316079 1250 586314829 586314857
    0xb0403030c020f1c0305070b0604020901021504152904020a0e092e0816120b0a0e010c020c13050601080417070c06050d14040c12052a24040504020307 66
    0x44c00c0802e505210b80e0310241c1e202614030f010315658030040d0203540164814003000580382d800044418a05510b0210402c0580da40e03e070000d00e400d2000c03044139801e0b003800e0881e2a03042089000e5021081e26207041612206040c040c84103d0040038034400014850f190000c1d440e0500b41002500300110001c801018080018482280c0c22000d40e1007060040a1f170082098001c00d019400d074035204911004030941c949500e8100e0495a02c06c06040030301540007140c0441c600742d001500d0301040341d00921440801d20030185d21100c01035a594000c4a8181822540d001c07244247c9114a805071602a0709481c1c40c0c0303030100035041d08030181103402d00801514003c25200040710009140682d245955114180520750550320082c00b00c1a0b41c0da0078000b0f1200040d0000b00c05415103240c0040184408140d0401510f0700865000013100d413030071640d60403502c4090032641d050030501980c10102001991f880400403d0300403150380320f4150184030030320107454182c0043d500300d85249008800500c0301c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 586317329 1250 586316079 586316119
    0x504051c020109081c03020c0c100207090c05070803010b0a3612050705120102120c040e0612100c0c05010516083403091208040b010b0403030c020f 65
    0x1140000d90412840c0040e00310342c0e0080032603016003010006002d5414071140e180103500f1000444205250300841e83c10b001000400640d90700301002421400d14002d6000003a41b01c4255010b1118024140032503901e2860280048401e0f00d980227100c0740c0f95a18000307800700075030000c0042201300050382c006109032035565800c9400541000c05e01c1c0742015864000c4040444c0d00d507209250700c100c20442070001c20004202c51044810640301c0001c026030700d426142c02440390344004190301c91350409220f00c92444030b02510541c1c1e081120060313651555000c004840700e6240e080d0f001c5503c80310311068020b0309a00181d5812565003022120342000342c3e207170750075514122401480c0320020a031250f030841d8060001900f159a203880104030080c044080441800e0b01c03d0042030200300a1030a140180c0701c0d03071101210a8004041100480080c0d000429040d03041e90140ca29815860001c6690705100f001c450841394942c854002c6008264280005001102902507010b8100392540c0301344010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 586318579 1250 586317329 586317349
    0x90303090e041730191109030304080102030105150f1c06031e05060c0c0a0212070308121503031201050d060b060c010e0f0601030c121401110901300903050405 70
    0x6040d40e030526150022000c442105105180f00030113130054003e100c03035069030000381c0109014401d004107120344100c45410390751062055071a0944000500000c11440c19400b035416604101d91004054000121070001d0340200c22052616540410003084035110414a0f485040e10500d40882c0042d5240c0300c14082548400080c4440351590802c4420007809104a55020b048420918106031000301c42c1540c0d00c000c840300034003501a40169000e034940030044040116400301390359071740d0402802450542c9000759803210611049580300131389481c002c000d030f81e111540e0304482c03450740e861719081141d04031782202d05a071582d40d24041000240c85030401840100e980600100d1035084e0b410b0b00d00c4c90f080c1164580801c0d90442401400042c0064204804654200464079001e140504220380400d80c0038140725030707035840c00e803c3c0c401b151400302c050a68001d090b240d481c450784410502640000741c20781d100e15603540400510400c1e50045d400340b14014003e10b869801d194881000c1800820 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 586319829 1250 586318579 586318597
    0x201090c03080702040c0908030301061d1003061d0c0f0f09040507030506190503100e031b0c210601031502070605010f030507051e040203071b0c15090303090e0417 72
    0x8000140d00d8107604041c003e01060b00309a16006007d5807604c00030319100d02040c01810100041c0c82e00c03910409400860b100e440c1440205080c002d8445187c01400030400c6110341e0000c80c8004540d06000c5036664045842222141455894000301c20488500c40e40005000110050240001036a030703100c903c21b1750300c15249600c1c006000e0400c82c0402c03480d1030103016500401c4032042018002502c010412503030902503280041100700320159550304601030003000c01418040d400e0070700884600041c260303285c031205a603048814450305402c0500601c0c5500e034003a80364402001040056405598003040e410a1000141006e0080c1d991030140d40b820b03801007245000360341042c01446002d015900050108440c4050368030f16aa80c0c006600342640c40482c400c03a400300000e66000e0084500503401e40c11800b1484a8501c01d203051030140c44680109000b500d062010369480324003895500b41a43c0c1c01d9200ca05140780340140040e211a001007085039650114201c4440750003075040074080f045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 586321079 1250 586319829 586319843
    0xe0a0c15200106060306090b03030904050a090b040f12090510080702070819020f030d0f05071e06020c010b27090102040b07030504031101081509061210021e190f0201090c03 76
    0x84c40d00704028141d070b15940050800516284003070f6900d5500004881201b401501c002c600b44ea14102e86100602c0c6116000d03061421a004100800002c03e11540c2098442c1c0303805014110320450450324030704c20717014084d0080b00200031109064000c01100e81d001c01503204a805035500e81021500700f02190400130103c000c004060700840c50190b400100610083c1c0082c480c000c81080c00400c0312920402e0a000c0c80300c001140d10520070081c0300080b81558010500641c90020300c0d014000351701600304603659510304164003140d0b00e021300c001e05411202c08148000d14100b02e0f004200008003070080c03003040d9401c2100041072034040317000c0d05555020717444040e101e03480c50902105c0b0b4400b42810a04200c0c4c100c003000003590114a4810700c80f501583c078090030380e4880010032040c03c1c0e603149850240c86908944104402250003c05640d03941d4102140000c060200c030301501e0003840841c154001c0300034011544144600f10340f5003079003c14800407894401549403200d00342c0ca90307041901d0403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 586322329 1250 586321079 586321091
    0xf010c03060810020307170403030905010203040b060f0d05100c030f0606020c010908010c050301090c02010b042a0302030112020402030403090b0403060c17070f1b020a090603060e0a0c152001 84
    0xb00c20309214400ca2402d202805501e1482d054100a100d400303070074030303e4188401c2d28012605041c42607000003040c40d8041c00841d40d07810076007803503901458102c0c3d000c2c1c4203050504c07110902c2c3c10501d0482c00d0f100d6028004095001203ca031071406810241d08000401d9900c0c903100420022034010b5000074805074024140044200e8001070008840d500700e0703006a03040044d42010300394008100c2c3c1c111020030100150f40055403104038050310140011961141c20400100100c0a02140381025010400b02c809501411138405030306a0109204550345001502c80380d8025007070540045a10600c039181c40d07000c043e00e0786405503061b00580c05c250740c8640d41c0c2c10060303a0140c002c03401c041c001ca48440070f2a9946030402004042c940107806400c1001643d0040024200c424507094030300e294010510005944c80741254001042a8030090b2100707130410000c4000300c1400306543e10350719040480700700340703d0600c51080780442901c5081c100300840d100c0340b0440d900940c5460451042070400100d06 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 586323579 1250 586322329 586322339
    0x30c1608030105031203011d0a0e030c0c03190b06120c0901030609020405070c0b1b09121006050a0b0d0506130e010e060603060c0d1119020a0b010605090609010e030f010c0306 77
    0x6805d0310f20403580030503e810401402100481da41c0c1e010400c5200b005110140d8074030081202030312814500141030701c0301055038401d180b004a0f080038844401d600705c806204d03042500c41054110214003403d05080e040c04141e2a003084000c00307544c1c450610445031aa00e041c0c010514600090b4402d82e030700c139030b24001c4400f145041e0080c00d820410742d10f4080440314030340e110f0341600304000d4001c403030720284440860107070003148081d01d14145000b417140041c0c901e11000d241e106d10540440303142c00e600e054400304031840c00d40451010345480341085400d069402c41c880006080c003400c10b130341c4010554000790344503109020b08140b0f01006000400c0703542c0003101d40751408001401d50742c40313504031208100c842d1403128150365004004a83c040384440c8505010403580c4103120300c561b00c060108000140c140d400090b0000c0851113021007100c0c50307a945d0b4040340c03a40079100042c1d502c0301041281c07440359840703103070000041c002c01002e80d1700c4842c0441c2d14038211001d0340240000300e5111001006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 586324829 1250 586323579 586323583
    0x702060a0f0c080105040b010927050a111c0f0c030e0c01210b0406030507120c080f0a030c05030d0f060602071a04092003040812010b0a0e0105030c160803010503 71
    0x40450804010300051000d2407003c0c00000e4140a52401a07550f4543c3d031025030300c11000c1d200204040d00882700c907410030071203160203000144c4c40300c030541d41008085980c2d40c80c00d01c00d030700003d15450a11402c114a100204451006214100d55195180e000b054041c841621403041050082d490008002130040701441c1064045030549050003c0c0c1c4078241007030042d42c100c0c1e04a01000c004000f88420744100000c0040c1020307040613160344181c10000c144800c4c1245050045401100030710089507503091101d90718100c0310358080c050b802400ca1303076000a0098607845c5c141031151094070304048109a0500440d07030303482410400980c0303d4200300001c80e0103100050140029610b500040c4d804104449403d2086100c0c185d150f0f60703503800b060030181c2200c040404450507400c0442d034905090600311856001030b4000d13003461210000000740c06a100003101c21044090f103520a510710b0070001035a094000030070101d0b075000708110900364100303841142108a841120040c0d129414041814 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 586326079 1250 586324829 586324841
    0x604230d021011130b09240912060103080702060706110c0d080105040213031704080313050a06080f0a05070210020c10050609220816050d0f02032506140702060a 71
    0x2c02e45100301315040083c64459081e0701505c0c481e62000c3c1e03460003c600071441311916441d050000304111300800302c0c0301d036542000300203110040700d010300d500c904181c450fa1113600070b100080c18110304200000050602c14081d14105000d0b03000090350098441c001da003940c3c00040c4c95000c54200300c95400005400c020624090281a5800c6042c48000003d40000c0e1181c1e02000d0070203c1203d41c2007483c1035556080b40d01403c1a1020740e51114200c1c4880240c801aa0003018403c48000b40c000c180540725900071072240c80450008000e036200d40117900014107001c0c0c88403045010700303501c82c03d0301302c0c4500050900000d440000c00c6039034441030861027190405030025220721407003024060b2400c00301d194482e0704485401e5080c0700c00040c0c40d10889a200b00c4e800d90810f010101040014010082207208003880c171916a2103183c1a0040d007261244035006000c146036041c1084040039103440300f0451481841144006469240450300204e0001c08607254070040c1d02c01810043d5581c0300d400381c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 586327329 1250 586326079 586326101
    0xb03060901241b0206071b120b070c020111030a17090a05030f0c0a02090a0504030807030905030301061125081b030a06020307030216030302030105011706030604230d0210 75
    0x2a0b030b02c0e1416805409641c50070500c0c03403800c209503102c406815584903005a41120342c01865a6600c54603403030243e000480450200d010746080c1c00001521803c0d00000703524280e480017a185050707441081c2903d807144d250744141e0401034900340c400b800078030400040012039510388130101c0a40d2240441203a480c0000c064901c40c0e0800484c41e4000340c00002960914629020520707128070101000710f2510031010b0002c1d5003d00b4200900c001d901180d884680241c0c001d55420442d680d440100380d0079204c42c0c602c0100181c4c002c0004204903031107150001d6807602508180e03002034044000d8a070300c80a0b82203030b107203200301d07180c00800108004015403100b003000801d500f00c0c8550100002511401c1e84800a07200c0380e000000140c029109504a0b04400c90005480003881c0140c20014001c2d002401145d001c69110200304001c07840310700c08584201ca0040040403559511b644215240c1102d8200d80071407100310144180300380d01401640f4462400d036005052807804561090160340070701c03600c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 586328579 1250 586327329 586327349
    0x1606020a020303030703020a050d05070f0906050a0801030605070302070206031501082d060d0203010f06050405010f08100f0e0f011a120c0d03090b2208010e0d08090102130b03060901 80
    0x20304005031008030942c0e40c01070300382c24010380700d0204030820f854512850344142001b615020810128070b81240d00c041f80500135945400a0903154207054856224070b111000200e4100700042000075402d03008940e001c891450058140301041d400b0984980054450620203031644180c0513a07135074805040c6500c4074110110190302da01840004008880390450b0a141d40400000110103403500c208a800c410380c0500204088180286082c000b414103006442c4280e00b0480001521000d40c00007805443d007070070191208282d1003074002c00401c801e9a034000450344500400032203003c103000300b11602c0b400320000300300c40c00403074400040b16012500c2c03e0b10442e0300022401c51000001000924400300b40c800b854211301509068a0700c0406505c101b03041540001e608503d0074603a00c21700d11460008036150841e9071246449400d807200451424210b42c8010b09200340244540c0303100f500003200740b00041c6803400c0000c40e002c10600342d401004188400006101840c02e121086038014030504013 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 586329829 1250 586328579 586328593
    0x71d04140d12050901060b0c010f0609051009021606110c0105130b1f030c17071703070f06060801090b0402030d080f070f030212070807020f011a30160602 68
    0x100a002180c04a040c4080d0b142e44a00054500c4c000358882d1000e0300481e1645a01e404108142c2e030302a04581d00d03680c2c8924100040041c41401c00c0c09554041d0441c0400300302480d040c0311030000290481200200050a54240314011585074460581400040700700c0c0e913520402c1240c0a4207650300505181d004003c59440c01d404104042400c07900700001640c1d0b4840c0b62482640046c0444030b0f50000b804c16421010300045c6a11103a201c031218040c05005d540401e44c0e41c02007565140400060f0b10102e0f00b0801140000580250320f205200707210f0300c0000381c40398071156058211803032901d080341d01f130b4491801d2200390300c1d00f04007184076000640360070b40041c60030758412084a01e000d050760051152880029125074080e0301030798a40038002ca440e11051030440c0000307195400a403001009402083d09000500354180100310b1007000c450486040c1d440c4841c207015030043c80b8540c402440005299101e410f903054081034410407141030003403e420707490a070012805071031a4824829580042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 586330935 1106 586329829 586329853
    0x105120f061009030c0308031f0306050103030314040f02010f210504031701060503060d020f180103060e030c15060301200703120c05180102071d0414 66
    0x80b5035001680c101e602c151000c0300a0b002c0600710f908141c2c001e0001c2600a4015030304200301020441c2d001000101340d002540f2240c004a0b0b456031200d004100341a418021142422241d410404072810320741d591022900d88044001d040c0011031201c03400e0180140c00020344588a242821188903246494038001c11044504901040c036074000700e10a5580b10f001141601d20341d454117451130310740008100c0d4164080c241203a01a03400700000c8500e031500f100940c0e000441d4420458654107604c0d1102c140e4004244401032076200344803000d081c1a000a4002e040100c1c40401d0031142c507240c0109009d400038440d140141c2c0d10b8103080c0000500d00c0b200601107280681e45140080c0030b03000c9140243c0301c0324030365070002032000e0062406030010a80a00d0a10505004649074582d4810702c80c81d02e13101d0380740c0c01c01c1d00240c184108410b110140513110003070701c1d120024200014485d = true := by decide +kernel

theorem cover : BRFrame.Cov 586151079 586330935 := by
  have h0 := BRFrame.cov_init 586151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 586151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 586151079 ≤ n) (h2 : n < 586330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
