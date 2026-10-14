-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3607
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:08:59.059149+00:00
-- url     : https://prove2.me/submissions/98db233d-a213-4952-a7fc-faf7d933ccba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 648561151 ≤ n < 648741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 648562401 1250 648561151 648561161
    0x20c0f04092f0109091422050d02030a0f0810051311120405070e010b04030807020637020c0306130620180105030705180111010e0109050106050901050307150201 71
    0x101858031603800030b268000c040c0e40e04440c2c0600090f030320a907000f521680c400007104c01020340907081c24603490004110300308401e0321198040d600c2410f04460945c699075640381030080414000103070400718040403d160402842d01c00340341181007100a40c9400001d1807404400c9208040c410646030141040910607544021500c200c4280d40c1a90784e4003280403041458000c0e60216118803c2401c0080c1907000410418162169102518035213851034582d4506600590307410b0741d000100f0821801e40d0a1001d0214450322003410440c07624002d0005200b9140c411044940c0948d0032842c03015040740e8007c200309a01c40d2610600b26010100c80c00c00c40024207101c400001c00324100102c000c00740c40e28901a00070b4440550400400c0945000111000d01058a911300846d006008035050301d2008415080c015106262100d00c103a43c3c2d140f40303401d580034071140b20340d00e035550f029150500c2003e01403140507010035664114154540004241d03189070078410f00d030b00c80b61190003081606100b9004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 648563651 1250 648562401 648562433
    0xa0e0109050916030b0d05010b100201020c031801050d1814070501140c0304050d0308180312010b070f06150807141005030a0608030a0305192f09040509031207020c0f0409 75
    0x4075482e000c09890200d008100704809c01c7e01c1240100000401603105000312651031010700090750618603c103e854030b1000c420b04026040c0072061044444111107403045540c540c00d8580a00f513224414285255500c0d2410707040c0490f604845010f006613608099030185400302c001d50036540c0c80070510100c0c00d50140342c104c0e03a40000d01003070310030174107912810507030003800088a00c6c0307240c00401c0c80300c980da0311882c800c0c0618500f100f8010040b8000d1034000e021781d140980700c2c003d80c0c07036020340d109400c40341e881803034400005004c0d10034400340c0c50810042014200c160059009070802400050000050004070f508120000001444516803600034500801c0340e2012252a1501954050050001128070140c0000180c59918503580b0700e0088a000c0440c040d903c941207080281c500c500c61148503110081c50340c04100c50325080c1c41e6445114414a009400303035499001500c8540b043d013201600325402c40d407241810125558440641076080c520403103000460700c0d11480d040203070f1500d00403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 648564901 1250 648563651 648563659
    0x3022509050108010209031204140121140106090906141207090908070614100312030209060f040816032a08101b021504060b030f0d02030a0e0109050916030b 69
    0x10000440402c150040c00c2c540346c00301c041c0c17607811103165400309060080303203c2c3c0000500c1031103519103e94010140c800c003101c80b01c00c0840501c00c0029926003036039080c60710351101c0d00c12400100040c40e4000b5a02010781840d1000740034151920070b80608040384000060b20400c0c503400d03220380003201000054001c1c0141c240a2100f100075050031011078011f04030948806042622450b10300c00d81c600380c54402e98800d0162100d03141951900390080b24400800d00034103608008046040e661100544020010f443c2c9480e0350760306189d000d505050202c007844c0e603181c40d0031000f400000d9040e016940751a451001d410090007808108924002850f4005580c0307005401300200414070a4020350404a42d00b0f48122031450040c000300c0e91100c01d0104046841c1c8210301060008400703407c4502c1d5a0002005c4800a140d0100031313904008408401401507400042e01d4510740741c1003018192169800d0030300309400761030301e008101c0c00c11008240701148403e54040340d4004c0d01a50010715120b1001d4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 648566151 1250 648564901 648564911
    0x120318150c030a0b0a06050a0305060301150308040510030e030d020d0207150b0f09011202010806120303011d0c1e07050703060f0605040f0c0516030e03030a03140603010903022509 79
    0x1001c10002d07070003a1100540c150802d2a038881c2401e003e0000350441d41140e0303d10785840c8081e03d0440081a02038600d0303501d0754954103040301c03480d4a580004080d500072800382d03580c3d0b4a03090400c000400d244d0644001e046c20031014141100e008401c0d01d1032101c102d03d001d60f0b10708600c03503003100901c141c0c540244100b480fa81818102d1f1140d030300001c0f0801c810b41b900001b8402040800102800034130580303c80d1940642d03140010351040d80d20541000024141201d00500c0c440d4090131a0405d80001c0e049290f540c085103440300341c89911a0f00113085841d001e2616182100c5040c50202c200803010700d08000144410800c1020080500255003080c4100030300b2500030f107403a002d014184034007032041c3d04000790414296198800c1102d1000203441e00c600c0c2c8000c543c5076200200290340158140213195507207000030f0300d040c03000b0a40140103a600081c2a44003140d0035180c0000034000074080c6e81b415000000198002801c400d075034241c444922925040d01c50003508440da00d070401c0225a042c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 648567401 1250 648566151 648566161
    0x3080c0f0301090c181505070c1205060907060305090606010f110a1401060816090b0a08030c06180a030207140607080d150518060405040f0f1407050312031815 70
    0x96001003145100341e42c4540d0071404a4400217418011070062000385d50f02d2041c0c00304c005000b80c00410384a84103044143c04980d035207018500c042c034840400c0c2d43d0741c1c0007841006500d00040c40038902900e00d90404100e14180242c0d82640e4001c02007926060200289071509070f40e008001041c000351501088901151161030309044005403001011507545c02c01801190707007500440c02c2841541c200740c04440755451302302c3c0300020302146000f407a081200040d000c00c1c1c1c08000c0c002001100958001048a400e00a114412100d20740c1b1454a4640091803084002a80454404211114403030082516440c480010b5858401c03030000070315a040001d031051400d1015007003004200704001110f8a507961390400d110070300301c81400f4581c0000003d00003034182d1406510468005026045644050304155921a0701543d8110180c591b0a146403000e58038050802285000d014298040c02d500d6454000c0101c581c00060642c00f4943e41c042002140720808212114002c2901d0203a0780d0b00d4281 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 648568651 1250 648567401 648567419
    0x70c02120f0f0d140f0d0b03060a0209030d05040b09090702070503070f140a05060d051b0333010507140a0203060c041e051305100e101d0103020d03080c0f0301 70
    0x722003441d02da40c01448808055240105004c119401001c10786a14108032100b0220195002c5107007040c00d6681c0e400d020341580c40130000c0c0b0713100358120b02d00160340d009007608051030b00a5903050b1400b0408204014000c0c605d180095401c01541039400d0143d0b80c071602c1080e41444145d8105a07010310960b40300081c0203840700079603001ca65007409003e00307801c40d120a00494136540c2c0111f40c0c100c48208040b0405107050782c48503030312001d03050030450745501c0e1405500309a80255110060f0442c00c10b17160202c030620394101c000100440c07900070903041c20703680064007038090a4000f0340f60124988410310840d105000741000294000d00751401454048261301c42c2d900140110f0f50441154003860f03424040c10050704081d50001084e0944c6a051410001c010340002460305078003c100110005801c0105000390703000c0d04030786040c00c18560400242c5c4201b150400c50883d0140755800040015840d5251032000c15605807401d20110b5503645003501591003080401016100000000a0314041e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 648569901 1250 648568651 648568663
    0x14010c050a080603010c080103170903100605030607080709050d0510050a1401080703020901150c050d0306140a050d0f020117040302070f051017070306030204140a05010e010e070c02120f 82
    0x41ca4466180d162521400d050894000303601c1600858140310042c00412451644640400c2c0910b080f180703010341d400040f078244444003042c140b0154803560140014a01408450350091041c07030941c07907500e48201e00401e071b5409442243d015000101ca408103103c800e00c08195a040d40c3c040a00c018180081c40800810503510505c01755a0440e001180141000c40d0100c2141d800502d145041e90801c1c000c2d176904a90420303420240b101e102d041c20700069003484500c08605131602e0000705545080c0880c058488500d504a220f65074000c03041c0919030b03c441441c1c10054000c150017510940c80c0c07006807000342400107d100410320005c100004c1540c000f130760380d0503202c1c41d1080d40708069460b402d00c403420020113010b1010802060030301e481078100380c90710703a8800d070b4a240104403281d49030007050445140328600c031650307200e2504000b048501e9001d5140140031100c802e43d40e640c5804c0f503046a902c03014007004100712403c0c140c942035540c0c281c0340c200d034001854180d4a540d485e040002d41e947c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 648571151 1250 648569901 648569917
    0x200309011811130b22050105012c010e0a0e01150c05060604050c0910080f01080a02030318040b04020a030b1f0e0d06110c0703060605040603030507060914010c05 71
    0x140c24140142035804041c8034000040307a21a4031200040d000504000303002014919030840c0b00d50300e0781c4c81c56007680c0307000050186400540c00300101c0079601c54041c4c2550016000700b810b001e60440c22068412501824040c00c0400310864200c03640c406004070348140903c2000f0754041d41c1594040b907040841d06855040710140c104182c44444c00403402d40f0340c031543c0344020b0070f9904118001841401d264000d5a8441d0003001010725100c0d12000180c46800001c804c20300240c044400c116804907246411405000000014107000e69180e00003039a81c440c288506883c6000c40c00558407035103858010014035040108295207400c407856000300104001d030407540c4904403c10b0b10f9284c25070a0240400300070001d950300f40c5180c188000b8010318040c00b00b42242c049030b84000300300a00c103c10010304080d08240e806481c003180365040c000700b5504203400c010700c1186004001c2002135085000c031030045500281c041103207070745424a50750b400407602c0c040c0115400c01003a1300450b42c1c0280102018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 648572401 1250 648571151 648571153
    0xc0c0d080a0f14031f0b0c01090c05090c03040825060b0118030c091a0a0f0f0e0c0a0c230313090e100914010c02100516120f200309 58
    0x586221104031000b030f2640b4200004a4000c202113900c44280b091a070410100b1000042e108964800d20101d10394008243e49949940d9986524100200700e001440100401c507101c0d182801c2002ca4000e092101400c0201000d00008030000b40d61440b0689110300c0c000310005101580541c100032018110070700105001602840c020190750300f644c00d074041aa9041101885828102b2054000600b1a0961042e0304454910f07003a07005da940301c05241c003910035030b071010003d9890039070a407081c92665001802840143d008004000141e04145c480c4915140741c05016195142418000300000400e900220705942180e0040380500100902050036021b1540045965442d029011248000c003c808076803c0003a204000e005550000c0c21002d000c0c00759012a0b558540009003120003050001002d60843c100000c03109040d481020750109080d28900d120720340f400001001210082d0000038103039503449984120180c2944490341450344c80c540075194a000408103403058008540f12626 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 648573651 1250 648572401 648572417
    0x3060121020a031103191a040609060302030705031c08040804030204090303061701061a0d02160303050106140a02060601081018090212070b0304152c0d0f0906050c0c0d080a 76
    0x4404184800c1302d01c00d002c00340d0104224000c644201015004451a100a0130000005c0703ea860f542c0c0d09c80d04008051285000452518500c141418400030758000d5100f9044040c054419510316200845582c040380f60546483d035a500e0448650302032a08040d400c20b141180100c2016050303440b03141501c20050f45103440516a0045500341c41207409a030100310882080d51484a500780041d2020841000340507041555081071103404440142e4143c0000b62500010061940c00c40c0040c0071000250300e1040c9000001b40000c2d507114006440703103042050103c0000c080c620505440780203400d003d07078882d040b4040600c0b02c0d8060000b0350380c10f070b11070000d030f420042010300d0005482c400c550701045003500715035030782d129111041c03001d4020032081e47d20342d10b00301e03100e031007020b041550002030000c5801c1c68000c2061491038402e190010340280b14210441040c0c2d80c2e0003a881800311f43c06450015a0340c01500010b6040508050556802869040b0a032041112880c06449503080554071544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 648574901 1250 648573651 648573671
    0x50c0105010b0a020a060506132d14070e040902040f0e0f0303010602060708071e081e0603030313020a051008060102160b07030302090627040c0c0b0c03060121020a03 73
    0xc082d100d0283c034540035a124a030b9000000d965500000d50103a4020040d08005084031028270954140c4900c10940c07181c800c0f0b10b414580704841d0484410604da42d42085115003800d44c1042c2204007034034400521101046014241d621a04031070303071450303001c0c0c4184106942c190800300500074100c0a0049406501ca079140d07451000015070303040700c0840e03000b4071594a400f80140c600c00070181001e0100800e505000da142c02480012001e002c0c1107070703548412450404c1444142a800f6410006212034042c188003240c0c1e0008103603600018910000e265142c198030001340801d0f00307540403035000081ca02c044211181c1020801d849803100782c095492800070807610035407942c11401800c01c084802e0101d6404240709a0141c860703000d01424080c5080c184002c4460044159240c3d1004602415081142070400b030103002600d20417401c0c00c5030a0840c540e23405840c2c03003004100c0c218000010000030241e0707100308130002c0b100241503600340b19042d081072004040d6220490140100c1c0c184241c1003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 648576151 1250 648574901 648574919
    0x230108041e050a0c14010807030b0a1523030402122b03060b0c0c0a05010905090c13230906090906072708011b020304240309060507050c010501 63
    0x600c9035620222a0000318200303502584a0211003009880038030a0a40340c1c0f0014880b00c52440241138103503030a10b03e0b06600400100624001010030007058141900c18400e40c9450103804140c0c0c1156004608040800c4000c4400e900c28803503a41508010051800c0d110800600035401580280c0f20140c05417170202c401c40c0d4031038900700729604035000544411086a55841d404810380a0f80c580401c100b51380c5c11300780016400c06d0070b085c0301a070031140398a4418036250fa43e0000816003800c000c2c01e0741e86410000340c01010000c00714400840001101c119461012a6080103000003c441c1c003240d841d502c24485c0034040018401e805050104045441c502d04100b10610035880710004040907174803414222290031442e403168070604890042d490341246141410300c0a460000000542c00322440d0701c1040f541c5080c0c5001040d5001008180705544070341c1c03080030740c96041441c0000c10a4080f00c080b0010045c0350000303840c0074580014416081e500c040100740c8050742d04000c2c03015980300d05e250 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 648577401 1250 648576151 648576167
    0xc0801051f06080c13080f071a0a0e0a080114010612200a0908012d02030108121804052e15110703050a1202100507170c132301 56
    0x749003981840208205480f03100da0680c02072580820341d040c00c000300d0190f03a85a40580082001e40c00000038141c0e00d103800c0014000500c40c3c42d042d0010104c0000311601e0a206654804003000a05042106540c84000d41c0300024502200204802e44104d4080303a08044203000b1200000c50940403401d04c160079014400068030003401f0808078502070390300300740b09e503000002000900030704040010b110082031080030203e00328001f0220910b0b550050340000c80f6840101e105000d1310500050210120000740408003040f0911900c0d03a450358584102c402e807001005096106051904210710b030b8440001140343d000b080c8056888007401c010b0a5820108640122410703200e92a4201951034481c1c200d018020090409940c41d85840340c4406003001d80806007590500c0410701100e04199041105d0411000e420000304036030300706818024039140100120003c80000c89010540394420081141c1d20303500042882c06070540d5810650408030389468006437642c0c079000b020002d80d40680d0741 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 648578651 1250 648577401 648577441
    0x1101081005031b0d061b1b0c050d0c080f160503010e1209040902130b030c15040303030507030e030c0f010501090902150f16110901050d020102100e10090c080105 71
    0x506100312240f0f05858141d410450340c250700c81c10500202d40401e999204105041501005901140c1c201e0440903060381c0030361070a000c00141000301c04000c20b01030104a816100c00321900d50b503c1c040c505080400b010b40d50462a5240554041c41c0401e031000554410740740c00b110121401140c2d214105400c81f4107005441d04617030441c8100101d1005000d004181d4800c00800c00031300d088140e00403503140c0102c50b110141140ea258070404252030100000c10100000711081104405962881c24940c0103602c4000c0074142c0360350100341380c240a0b810007604d56074080c04130707529a00d0fa415156900d0100c09907a0956502c1c02c40040703482c0549006c0c402c0c2a0703402410b0041320a00100150341180e0220340c4d12510340e501400034513a010300c41d02c0074407600390041d0f1800105245150800c85105011b0303110700c1c03203071244948200040c0d07000b181c0d000016010041c001140b0b001c14944608040c1c1e2800003d121a14180100702081800c6000c0c8044c9d0342c880000700040d40c1c500e0020b283c0c113100740e40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 648579901 1250 648578651 648578653
    0x1090806060f030316060f0609020c0d030509031908070f1d010e0a0302061c05010807030f02060a0e060c1f020315060a02210c2109041107080403110108100503 70
    0x7140c6007440d40c0501000072000d421245440000c54100407090024001200c0040d280c4000803400c0000740903003409050304400c00c5107405010701d007040d6941c0c5112580002d168035000050380140c0107000b590060803401d100e04d850b00c08100c000510031242110642d02240011040403000c600c100c1c000582d40075495044114200c0000065070344162081000d54421a191404801a100c080260101080001041c00c074112082942d0007034a005030090f001e40d910069041010940114000c090141c0581d4816a1a007a4030800c94951070300e07040c03040c0c000d08001003081e440500040d581200811480701c0c05920564031505100760b11082c0c408035080310080c8041e26852030481c004000c403004038012248071100c40902e1326a40b100071012425404030100340e58a5001c002e0140c03d4a580601c40002401146203030806000c1c05080b0449010300d42d244c040d1580440c0610860345050340040c0300b151103659914040300c46258070344604e400101e1034800b14401c80c504c00c088805550b0014 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 648581151 1250 648579901 648579913
    0x27080109081210230a0f08010207140319030504230607020f010516030203070219060204031110140c030702031c0f090b030c1332060412110301140108010e0c010908 72
    0x203404d40c54112081c081c0c0907484032441c000001c0201c102ca180e100148100070001d42c442c0b440e400d200304005c0f620856000c86420030031080c03400d040d80103012041e94415041c0050540c41d141480d0503484402d01c485846000f030b07042031410b17002e00003034041d00c5803009508403809880000d6001d420f80d0300645017042002d0040705800700c3c1c4c900075006154003442c14811641d2100304184c00d420003000010056449070b500207130620500080b01c9030070441034003e44e6004807095007071074001d2169400c000100410381c808145070703207111000d200312903010b50000d044a0f20715011554010343c0011044101c2c0118482c1b40c01a00072034001d082a1048500c80041141075a4501718800403507803000c24541c149105444000c074052481c0311804945900d8203030030f112010640c4d9025402d200a414203544140d8041c0020020b603605403004c440300303651001c0c1c002092003820b4040780c00740800c0368501d40c401d8880c400100300980154003034000889000210741d2807240c503c00542d01c01c100c0c0e010f00d10701ca400034 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 648582401 1250 648581151 648581189
    0xc19062304080a17040b010302150a0c0204150801020a18051f030507091a031906050f0d0516180b091905060307050303190201061527080109081210 65
    0x48043e0080a6440c102032100c403211071544542e1402c05c03201268259401c074014800c0d4100261502d040c019125500c0d450420020006004d8881030030009116603222040716010b200202402d1000b072001e10001d40d100ca103403200150205403c03680404030a080740000040a14104c02c40907280c450307040703540c107051909903c101d0103840020090814001c940400042d41514542c040444001d4449243d86a0410203410382580040c12803080200781480c10521456880440d4040c0c3caa41c1240d100508100a00c1c00c40c0c1002d98185c0b150301c4100d12560005031041445404641a80c90f4000401c80168060700304030225406680d0000a4103001080000c00e10745a80081d80050005086a240030358400000f403a5a110f00022481095207210a91440d0b030240220030160401103141c0001c04d50f8400c004101655091813180e5402040c401c458040c94a84002d83c058400c400003800a2422130a004141d0b9006100c000301958081002a44000d150f00a80040c3d5586030103000c000040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 648583651 1250 648582401 648582413
    0x307110a0302010f052506020307020609072103030b03010609060e0a0507080a0e010f09050c0406060816080601120608030702150306030705040f0b031c0e03060115050f0c19062304 79
    0x3c4420800246c0340000c100102400d440004c82d80e0f1842131001596038070700040020b08010740a042559180d000003014403c00c1d00012000c0c012000c10440605000ca8a060072800307031150f400c0c0c007605546072003c04604a113080e08a0001d5a44000303143c081e40e25001c0d507110441da404c0b40c1500c00642544041154504684c00603484040050008100003c8801d06034044486811040f030745d079488615010001c0c105070250100034001810b00030814505450101881c0360008074a0381040703440800130300070f6030080c0c03e00d03ca01100700104100b0551502141030703480d031082c20140d1103a40e80354403600c41540000c0842e0b205071000340107030504030f1815050001500f007101c2070a11181d1504580c802e1a18104502400441694003900001c2d000c110b0280440e80c100b144107003e80c2040c0e006020103250091928140103081c42c146598440342940c41c21a03024004100a842c0070702c0c10003170000b06000c1000f003030540c001c000400ca10322aa14420f00e441a2009080c0d03e580c50043c00034001c124 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 648584901 1250 648583651 648583657
    0x816090209040f050a1d1b0d0201090b2212020f0405220b1008160e130609050d0e04061508060d05060405031207020d0c0b25020307110a0302010f05 65
    0x1c0040d101040b42e0038042c05035070544e00100c611006507039413460181c060380e130203c6030030555032036610103440781004407004015803c500e900c2d22409555070714800300469200348086e4009108041c40942c503182000c15034032610f89510780c101020450316401103091142c00c0c546c070101e180d00034600000c0d56a04070902000d044010311000c104a008019100d0800707100081040f03491082e211170308185001c000300802050f06d50001070003030784186440560b02000765040000d030b07803030040700c0c2c4a10340c2c580c040346500145140000740498242038405041120010355002e800301c3c41c2d00e170102c280b81c0d0b49042c0400ca03800381c4a0000c0202c90b40c0000c0520034012042540c10210250100300b1031400758903400d1501d00c055400f00c815500006900c0b218a08080205410444034400380c080301301c003000001c2c6180718198010b032180c2e401d840401c85400e02200d1404001c101c2121192000c03040c644040e450360040101a10390341d40100001c0802c2c42e083c83d8500a595050311451000a11444107d030250 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 648586151 1250 648584901 648584917
    0x21050610030f1b050a0909050103030c08032a180d2a030501020a022503020a1a090d03080114181b0403080c070f1d0c0c1e0d0908160902 60
    0x40d54400030541d91079004040ca83d01614284c4a141d5a40e81c882d00050903503400307a004000282c074020042c00041e41c01110f107101c1c150800c1c0003d03126142c42141c1003500781340c1040203140c400001c207518201d00310b0700c0162004e8900e40e035040944400840612121402c0d21034000c1000200325094080e070844c104070b4800b1140480c0402c451942c43c1d640361400c982c00030301c0060141e4070009035010384982c070740410340700e0118400050a141d40345030302107108100c05008800c03041c01100f1102024031401000d446070f424000300207200d8151030b80be02501211081c018102103600d000b40411322070030610520f15071685240740318012551040ca03481c20001d50010001803641c402c000c00404254000e001d0302c01c0f12180c10241903020b01d0000403042ca15a240d0107068410304503899194141c02c201240e40d80040b544189aa0f42d111110071181007908401b4001c2c0003001c465980e840303220f00000c61380c2c40c2c103106840e44490189c0b0f03220256661810414113500040c298082440928070701d8010300411 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 648587401 1250 648586151 648586181
    0x14070807092306281e090c0c080706230f09060105030d0c0f02030a050f060907090605011d21010f0e010216120207030c181116111503072105061003 65
    0x35500c1700701049090b503142412038600030402100780000c0f050b80c816000b686042d800c03e0070400e6242d5543c8040e03800703802c00290002c0c2d138880107001c910140c0c84100440101d4411020010b1805072810f08140d0b10942d8400c480e449401c2c008078003820000340c2e040d100303004c40d10b41012940310ba940d8644d0040c801c0300d040707030140900c0c150f020004008001e02e0310588407402c00391415243c80e901d001e2070103940da40030481031402e0030420045130341c0191544210410039000c01058680b0600825196441e12a070721254801c0703040798260f10041035104454502041106000039801130710741501382e000301005040b0090b5070210305c500290300700350741d08225206401500d90f4155a40c0b90041c1c2c4070002d6000070703080b581184140032846518403d002408406081a07824143c01d100c40410640400400400c20b8407401c02d00062690b481c101302c0da50001380201c0d2692032030b003034a004000c0080380d048684481000601034802c002c840c02804d10a01c00603040c04803100ca0b42c04128050b0480080708161 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 648588651 1250 648587401 648587479
    0xa0221060409020d14010c0e01080703051003120509030105060906100f030b030d0305010608060a030b06040e12030103111504120b0402040b030d0e1201020c0a14070807092306 77
    0x143c8400b064003000340d02505d101d00d0015007a40301c007400c2d1071202d4500000c014041454682c203070703002282d070350300a03c1a00e00058240d940c102e540424110940025103000d41c100f440040aa5000f00141503400c0c05030000e114540355013041c00f0082c0000c3c2c80301540440c4200403c9107240c891200c080c2c08030341518000c1882101130021904101c1d03840d00c640002a1240d00500c200c94021651580112080d034020340c10303601c1e41d246e03001125406001144119240c0400c2980458108689004000d2000d0a1652543e40e40f8040b400d803000400c5903401513079507032060303c1144440c0065804035045040c43c0c480080041c0e943e80b00f8124003c20807070780309507503200d000d1403510104070791207090b4211784408400d40c55402c200011400c000c1584c00700da81c010490400e040c480841d0707480c001540b2030400000110144902c40c141103441c1c00580c0359115165001030fa40c2000d8014101c021900e0303010201d0203284103089102d050046550076001395030600c01c1d040c4221a017042d0f840640c51310f42e42e644c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 648589901 1250 648588651 648588653
    0x6060d0207030507080c060105040e030a080f0c0c010e0f010b0d0b0a0c0504080312010e160c080903120a0807140307021e01020c011a040b011b0f1a04030302070302060a0221060409 79
    0x10381781c4c02c104050718003680150018080c070b0130725204201c04003020000450a1084e1031100400d40710000f0918040c01c801c10f40410b81d01c0ba091015100c004604a000b8009503184061080e500d100c088040c500560900304007a43c54149075805560b80c07500001209020350b81c4d00c1d400c5028103032501c0c440080000070040015400d41c18809014410709842091207554901482c0ca07500300c0b00074100c0007056061031441201d01e5000f0403844400d691100751a622400c0308000a4104400060382c901c01d50000203103090f58a9001d14242c1c401c0c04a902c8010041d022a0301d810f01d40c0c0012201400940d0103007c82a4141e81d00d000110f102c0301c070110000d45051145904a400c1d5526000030150380c20754a142c00200340b401d401102c0c90403034280381c02c1500304062240007101d0119694003030015000e01e8800f600344a2a12245442100317201c000c0f00c41030810b854000c0080d0720040059006024500103e90880c13401c0c000c89254a4038150407800108001c2c44d00301540300050526584155034642d014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 648591151 1250 648589901 648589913
    0x7141e09040f0203040201080612030414060d0204030507030b070201091101230412020111060c1606060906120b070e1509060c0d0e13020a17130209040803091506060d0207030507 78
    0xb1a000d0350260007685905240c8009400c2100c0604800e106500501e040c52030060000181c2c1c0840703c4e00c1c0c50941000f803090002c1549071091408030760a06000003404010f101c0c0000391441180e1280601e0784850742c40c460b0403400c030b41c82e25100400078801500e1604056103d080d40f50410b20380000c1c5191150120101d4007104d5016038440c5080d9100c207100d08040d503800c00b850341200e0100102400382450010010500c40c401d60b00441c203595801c184076414464280d1000d0085e0203103480804c0590784070200c401040c1c0b20320400703c40d0000440c00040449200f144070b100d080710060070900001d64222050000b0350001003416410900601140210741c0d4108520800340c1c0e1140c451510011007103082c445080009029085814010050481c00039808101c2603400411800141c01c0b94031035640d600c04100d12044043d501090040512050000c1c11008502610562040f40c003a800600981110381904440199101d0010f00803942c45865a8000701600c5201c1d01e0034a00d0510307265190 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 648592401 1250 648591151 648591161
    0xf060f06120f0f0f1f091403030403031e2d2a030c02060c0a0e0418030e010f0e1c05030f0c030a080f04080702041a062107141e0904 58
    0x849080e030140303902082c0e410060184e5040581d40d10054205040101312200750700c440003041c0036400d95984401c40c01d210488048100a01c021410740703070b8030700b014207008000d0320000d54500041d4a048a40c100480400e1243d2031451441c1a41d03c010031101d03100000425465581c0b0f0341c08541c41c0c082d2410280ca00c14194054043c10185420a02c0750058008045034003000784681598408001d015074500390a05640200e10340d441c04803075201144001c10060166680c285d41e03010700e4208a07508050f080041039001c0002a82ca229010306140001c41d0780d401000c245079000100d0040e40c000000c803042201000d18020b0003207a2510050803038200c41a032000b00c00407100c1e00301043e00e01c0c201381d00c80d42d29500881c07807603032154007800c1545420880c0d129202d0b000b4840c03652211050440c503090540c0c510032000007840c554031000d6604c00b032540e100601c04990060b0550000080f18140035148501280741a610040c0c01c20722101110810140300c1071070f110034050144104061580c4034010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 648593651 1250 648592401 648592423
    0x201140705030f0a022b0f14070f050c0c0306010e09010e0303010e132d020f0312090d03030b09160305130213090c0909050a0201110f060f0612 63
    0x9120202500044019402420000402a003003090000e062628605280c2200c02c82d08016520110114515205c0c1d4586600750f034240000071108080882551081c10b40c08038070300e4103000c039500481d02080342e407600b02c03130076000300d61003076202c4241d544100c002d040c2c1c90056800b20340240c0103010019240071426032207090044007a00c20801440c40a004840c1c86410400085003154102000030802c084d0003030060380b9071a58070010030184032a0402080302c0001c0c50903008d12841d00308440c6a03941c0b90a2000340d025070300442c09101300342400180c03040302c0c4086140346410300000908003c0e9a03403a4200035020907803108007100b4940d807100c1d0b5160092150031449180e485102c0c001030165078009062221a8801843c4e110140e21084889100007460140c00941100035103000c1c00171800a410070401580390036540d00401c48000b40a650442c001d03200d0601046072145165650010b19054aa140c0c00650210b2003000c190002250000701c000d0071180c0c03055111110781d180ca40d003203007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 648594901 1250 648593651 648593653
    0x50105010315060320220c020d0c0521070605010902030f06010e03070513151205250b0706060302040207060506150405091b0f040605091c241b02 64
    0x40003080401040b041d40300c811540140841d03850340c0c0b115402402000ca940380c3c1c0f40304001c080c0f041ca44d107003030f86840311100c0350034001808224490030303800402107050b01c0009807160040256456024403a22440d059105000f00310400d6404100500c964110856101300714003440701c400002c0c00c6001b62401f034140c4060068603032804c07080052000102614013410700c0f414600380b81c1c0c030381c8002c40d081050b108155498809225002ca01000600c1a48103622001101c04800705110070050300206246015500302d6081c0301010403c0c01c036009850404c8445000301c40c10422071940b034800030302030090180c5000168641c0d01d40100d810b9902a000c120388540e42c0f802000311500d0b000070021501c1408200c09820103050102041042c007002d40107041b088651414480781c14400e9088402e00c040158880b80c0f00c640d92240644180c01c0341c100d8a118141c1301d200461041c000788a00701019400c03c01051070384610b03840d0340c08282444d00802c8a00d43d1101d1180c0b05003445080c000d507154103154 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 648596151 1250 648594901 648594911
    0x50a1406100504090f0212031603021c030e030307110102070b0403210c02030a050309161502070806270c0604080d0201141611100501030c0e130308070e0d08070501 72
    0xa0054005680741e41c00c0244694503101c00140400d10441906a100341c1c169006103805814105171441c41c00345a10001041c84000c03401c10405a0100d88984041e802400c50840400044000c0e01a00c841c42c1110380c8592041c00001c0038948200c0d02d46030228210400180342185548540402c0b0b0421902503003c07441f061502c900700c450b210103562111400c041c04100b544c8040c60001e4032481685152000c000c1c000c0b002c1019840d09100d18861406c3c9144142e40c0c060b920144d425204180009120160207107480003e021400030426911900000104490420a010303603520040c80d0788440310312910a0114460507502c03107400a0000e4030329030f0000d2002a003606402800d50310300318900c882e8214004140001ea048404c00c0c514001d0890400e500b4043c0494800746c07900742c203100001d03035803070818000005004100d815081600c1101561010b283e0380c8100c00d14101490b10001400120210001030107240700e684010318040300188182042289a15080c4168100340003d9403940d560f1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 648597401 1250 648596151 648596161
    0x1090501080d020705031b0a080a0f0c14011b060f0c0509030f010228110d051e030f0c090409060e030a081014060d0902040513140106031e050a1406 65
    0x2c021000e40000944010007540c1e0810002c030344c4905400d010741501020030b44100c0354a95445c1d0443c0040d01c403602c06c4074199406405d01c02d0110912140580d00c0d8001c0351404a824005041c3c03405000c80180c42d00d4016040316101110411600e0b00b0940c0d070a50323108881040e19100d07014494040e15150745980d103541032102003605003124100b541c0d040d6072041203400e270f034001c03003114010518142104004000c542030b0b0703054074400c1201e003403000203000d98050500606c0d00840078104450070560703819040c00c0e11880c0f0000c20b1009507101490040b503040000c190300143e10041c00c12040c040c0003c140d101e1140d0343c00e019601d06420000f00ba8001159a0407295408004990b00a810161485100c0c0c504010040c0318000c2c9882d480c0140d000080c1080304e100d441e00003811690340500f041009184c1000200041c404c10b1001300d502082203010036903039000500550013540e8100e03801610020108160090782c2e440804100c0c1e080c041c218101c0c02140d0a44a1071154122120181605c2c1c600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 648598651 1250 648597401 648597403
    0x20604030305090c0109050d0c0f0f03110d031b0c0f0803190509010f0e0d0215030601030c0519081305010507181d280c02010b1815090403050706050109050108 70
    0x2030804000b5803100f044c66940e680d1010074001114002e440481601056090501c40408150000b42c0001c05002000813039503034000300041201c0c010f14084818030340f01001c00035a01640c7d080540002c12207911182143c0807403100741400d501c0b88809140165440d01000e42d0b00300145e01698080d00086848440788030202405090444079103003892801d0f1a82d00083c280361601c2c2140070800411031074403003564036060380944640d0b40040954400c030950311420004c51344100c5019000908055000140900a07001c0d10404034400c1d0484090b10180d10080707401c00c000500481c0900320004030f00d0041013080c0300b050b002d408540e884130440481d0368894480711a0941c0100c070030924007550140c1300c25407070070001d4004810302d5040b85444429905115148014200c4080c12858002ca01480703e030150301120039190190761450000340403500000804400700c48464692981d40c44000b0586000c4641507846031007424000e050030642d071180022204260421441d02d0381d02e41c014010740c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 648599901 1250 648598651 648598661
    0xa060c0b090106122402070f02040b0103110f3402090108061006052a0f070504051e0402060d1a0a050303030709141809010617030a2309100206040303 66
    0x40307960024842e482c90904000c050402e10040035051000300304461300c00f116041203c040e070b129900c0041d900e40545062503688005400340492040d071414140700e50075402800340c001040302015010342058258080301742e0540c4500801c0c05402c031800090049400401c030225030309410a4000304400440e403050000ca01c406802c85e58065105900300105119503440402c1a10810718181e138860070020b402c5441001c12a0341c46141040151188401e150005492940c510b200c4c01207662441e075480500048480c150352046420000c0f0250700714041c0c0440c0032a411900c080c10140c0780c83d40c900d4a0340b0840d1400b156003820103030220079090803440c1505601001d0700c403c5003e580365041142000c0d19403d40313032180c0300c3c2d003041c4216041700319907903558000d643c640030108104851a0600e0000d000304114020043c0c01044540c0b403440c2c40b00000b050f01d070b000c0c00c192a5020301000d5155241c0000c00e0303162400c85959004c201d645025140d61510500c4544540c0090185080914000d01525 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 648601151 1250 648599901 648599911
    0x30f0b01050d050607030218030a060e0d0e0102030f030718080c01120203150405040809150913090201020709180c1d060303210402030102071b03030909050606070602180a060c0b 78
    0x1103001c581c0421804140c21750088042d09006903142d40c0b4031002041c4088480c81d40c0d07418003c00d42c0003000d10003981c11100590903210f06032102d840b01d1841c141c5200140e075400500583c0241300c1c03a003012064000864105505042c0380d5514885010000075400c20354101309903e4001440118130355070414101e071901c002e02d5a05609610f030848800e12030f99950b511040c815601c44011405000707044003110500c00c006806912031104c41d44c10705d4616400780f05030302e000342650242ca812004440c82a251201d505030701514403c0d191292040150200360b100e103117003000c1035851000260030b29403158010b025034050f41d400410451032000d03550600a1060b8007942081000000303003408100040c00c032200246c07200e0b8580c2c40f680003081c024007504500400303c218103c06143c0c40344211144c4000c90740710b035503040003098541c016482515420780396030f50000018084c20001481ea50040c001c0f05040440d08450184c84030009000d00509038481d4011421403e501c03402c1c0300c28092015481 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 648602401 1250 648601151 648601159
    0xc011103070e211002130f050105040b250c060e120709091b080c090c071104020c031309020310140d020103020c03160b01361a03010204030f0b0105 65
    0x3628000384090100e0545803161849560500008090300501c00c864401d5140c00700d044854015001d07020300020752101110f6603c1454242d00040c40b80490301150040d101c040e914503042500c2c1480403000d54200e16a10040703040c0000c0008010341c2c10a503410036283c003071748181c8015490802d02600040c010200140180c40003032014410b1130b000143c03042101ca41d20f00010300d541e4079092800c0c2844180710084403150321608001491403000034494020b06003214003001c1338a81e000012428491613000510324045541041810301d803a90251901c040e811081e64680000010308540c001c000360031054031182d000c01401034030315103825694090f040710301100301d0100228001a41c1c0c1001c00078000d04058000038071000000c014410303a840c18542000200070344940e8a40302400b000240a40c1c000303030040f920700301d000380c6009000c06c000c01070440f0700444802050310914040d04c0c001016002c2c54280d000d00d00307c0d940742440188001d5001304c494041200140c40c00728001d0350306074041886 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 648603651 1250 648602401 648602407
    0x705031801110721080412030306170a02151c32060906010c080c0c04050703020a08040b060a0f0e06040b040e03040b0309070f1409090105130b09030c0a080c0111 71
    0x9201e500103a200143c4d6403d8254008600c1801c0507644030b409080c0c001001c0c807002140000d0202e94024017810098482d071401d00817a03448162282249034640010815603000703205a4016040820340d0903981c0e050308403003c0c501640d0300003044c1c00c81803241d02c20842c95580e000d009040c83d41d03001043d011110091001c216000c48501b2107004c2e500203004241308491078004260140e018800c2008407070392015405440300d0b07604400a0311561819581d81c05541060000707044103200b4400c40d1003601b010740b580c103096100da07112079246d108010041900010000c1022601d006004003200c003c1015841c01070700c2e490100300703000c1a99444400640540c0c201910300502d03001c04410b450076200c40c6507055440b42d8401d98001d203001d0865024888c5036410039400f080d0000b8000c1407115010003510703220015103511841c80d00b00c4d00c04803082c0d107a01d0003002c040f500103200700f2000b07a00440c4100840c2e003004540c0c212039007403d08000d800c0310b418800041400c1d00c4a4203018824402401808680c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 648604901 1250 648603651 648603677
    0x20d05150a05100225081906061a120601120f15091103010b13030b04080a1704110609040902040c18080c0307090906181b08010608190f080705031801 66
    0x945d89114138800c603a001c103004102909201d050082000a043c08021034184042c1901d508000b404a607000391400c41c1802008903492003101040d03c503550080c015589060483c07002d0154510300a400181000303807044661443d0305043c094803041384403070303c40050344d00341c0c07541251b500110a9002e26100fa0810488460380c2c164041a61304582e004080d040d80c810840343c40a000c00400d4100410351003045050106000f081310140900041580f241401e0920a00c9000158082154010b000064030000d08a45082640242c0b901010151000c110319100d640001e0036100b00b4180f61340000d40c440020783c4104a41c4034100020840d80d40030b015110240c0011075141c1510b0f000c7e00d003103a038a40c00031100308109a4040040c080c4100461040c401140c60301090000c00c6600c0c80d4502c1d803103140086110310307040c891101216601d000070f0803a03071450300d21200c1940c3c54034803c0d030f603819040c034441d004619441c0082c49101e2050300a5030ba03444e0603030002030040860100c814100400c1901c076503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 648606151 1250 648604901 648604903
    0x2010c0305160804150c0206070f050c0c10050706020c1018030804080313080d051005060c0c04050603070807060314160f0c11120c042004090b0301020d05150a051002 73
    0x26a0440315240c18421960340c1d040c6014500c0340030040068180c035001d1b0103001d2135404600140603004e03683d41c18841d052210012034090040b44a003840c55008510007a0b543d00d824581c0d402440c1d002d00f0014100842a00d03040101d810049e14461642c00c804840b0031800014411b0755020031310b0310310800b0049a0340d100204400c0d4001c200500d11400040811044050040210348090380121020b559102e2950b03000064182510351554520703071004046041e00d0310344140d0b4109500ba9000f0400c0742942000c01c800b500f806000e03541c25014050002c1480f0205205100141c00d9a4501254910211035100f0704010010124500054a0303458400010360200e10382c1168101854098000c0e540340c10618807c0000c00519907014120f602128821040454002d61508084500304402d100c40031803030120313080c2c90700c2204160000304011b0069442c503600c00c00078130502400045c00e000c1d4860b0310108460040d02c0d0105c1c441c02800c096482840c0031000035028080984044001e40502d003c06 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 648607401 1250 648606151 648606181
    0x10f030533090a02011e02031e09040612030908030f09100e030607110f0102030c071401020405060301060e03010507030605010f03230106030504031710090e0312010b0a02010c0305 79
    0x500c4111010007064000d58402103240c0801100010301404141091000b055070380c2c5014408038017003240d0304c90711440c0d100030506410407122a17401031441d01c00842e00d040f014064403141e000c202c030310030b002c0403885841d148100d0000d02074001c2e442c880c0410504014040508917031140c041390303008200c0302031025562000c1d5400110705640340008007481c0e100aa07280690784003016094031442081040042d400300c0042d600140030800d80b074040c00306816007820b0344000c80f07169203020000c00c50300c4001040000c480c0250140c03440010f05164a48000801c60780c001e030301c0b074400107101a4144170306140071300c80c4940050072410200f000c2c3c1c3c034050011b0600310588402c94241507035030b050b200d00340c80702943c08060031100303000802c003540c2c4544001d4001d0206603030540010b903001d01c24002c25850a49400c2c0a0ba42c50506a40514509108080030b0310b200b881d0052140000d122020030601b040308070780e0103048601e0080d500c4803901d40c0d009084541100f411810541042e09001c10130880c0c0b850 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 648608651 1250 648607401 648607423
    0x207030509120106270f2c0715180e010801050a06062c030703080403050312090f061911031303030e03040b030f13140102030a061205101a030304030308040209010f0305 74
    0x21600c84a012180d0340004090364510300102e20b05040000d4001c281f00000e05008520015809040100643ca441d80d1140c60340654924143c92120008031640103d54003103000c1310000540440d035031504400040f00600b84e0110059079154018004092020b0244001502061404e001c1d0f0503000100200f01541e000c05242c070540344181f402c0d1130f50300c050150001841d00079260541d00d50341ca1505c50b960f80d11051464608079400c80c0410360406000c100c41c4203881c902e03002002c440d15080081681b10050b004000c40a55841d0110a1070301070b608040c610a0403103100420590140342230203029105022070500c003d07001044140914600350085c1d903088130900c000d00c2829a900e42d4880b001074603085c0082c1c28031234910740344c52182d00150001d51160802d04070902c501c0b40d907401400c2c00414244401003d5070018a4402001c500342ea1280040c0d10f5000c1c041c240284212000c641150312a0300181d00144910040200b9800d010500d54010482d40d1105e6460500d1500e8203603c076810700d02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 648609901 1250 648608651 648608699
    0x60c0305190210021305150f070b1906150206070e0a0b071a01030818031c080907051914030a03050a11030d06090b0111010509030414130207030509120106 68
    0x5903401c0042c1c030812410500c6200c1e2001103668000c2c031250240340c1101e07442018401e000c004106e528180325082501e4203c0c14900c81282400c8299a0f440b00070360006010703003550781c1d00ca24400100319070742c0180c100070320154000051125503020000c1c1058401041d04007440b080c0996018280c40e622003040c11113003050300b101c0d11130015103414088450307131034010a213407581000003106000e0305ca8010050301907050400c1c220700751a0802c3c95180e810560302001001d140103941d8040034011080380d50f01440013000d85403040e8492001440c0502da81d0304c0c0704079202c541c4800b440340d40514414225041c90442c000e1001a070a80d800030407901c40e805401042248080340803150384070400c00d69030901050380d424009039490b10518001017240442c41c0d070005e00325603c2500d00640600c24207000d45030b24409546010309040d0b40c4420307422040340081d0060846010440307195464806401c01d144665192075640041c14100062a584451a004181d01d029410820f050344440b85010f546a20b10b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 648611151 1250 648609901 648609937
    0x30e060d021918060f080402060f0c07090f060909151e0216150c080f0601050714070e060114030f0703021b0d140903060a09020423070207060c0305 65
    0x861400082c0c015285008a002440300ca240c5510707410500d0150040002642440c540365102000c80b003102025880e00081625000442d01509240c0d0003040746001c00e020b030030f24142c2c2c5161250700e0420b60346e00c5034044917500d00410064503850f029080091a401e40c0501178640702c0c0d100c47c945456800804003665a0340c12200526884011824074951502d9104544498218001c9403000041c810101c1e0110720502503c190a0842e20804240a01566820000d0341c2c0381a040710035140050004c5042c098280038640000d81c3c02c03242003040c00309840240ca002d501e803c07007601c007006010340f0050504c011140c60500c01180c070419240d00030703010603460820761210082a0028403d95241922074070814400280000001520b80e030031004503610003d42030620100c0800d90b00504507410750607001304000c5071010016400451300240014000105094800e00301d10302411b03104d20460b814030b01c034420404460780502c51840100001d013032490b0f68101c0740d0350003003007441042c40300d442c90541c0c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 648612401 1250 648611151 648611167
    0x90207020409200a0b040b09040c030204090207030519020111030411040618090b160e01120b0d0510110a0503060d050f0706021605190b030c0903120322030e06 70
    0xd03400403424143c110551032144024a076045101c9080c181103180505000803000800301c840300b08a0b400c449030030722018200f010040400018000080e41c040c10180c00f44801300f88011144010540944207440365a80d40104a900c0700c040107021440205591408a104002e030039038170216644240d1129044128182a03400035009003066040080f00c50b0600047e0300340000305609c0006400d000e101c100c10195951003d4a03000120307540c4c1e90000440c114905e00555008a2240d400031101d42004243c001c0218003166903e4510041901c0700e6028000540307581020b0300c034100c0c2d0f1200d8042441d20749020343c4000761031480041c114500440b5040c0b01ca10510600f403041080140541d001d8444055407118020340d10340200c0d401c1080021056000121860b04410a001d08505803142d080c14502e08480d0069a4000038180032001c0c1c1c2c02c21006040742d40501a0401d08006200c03901e450342030010b07a00c1005154840f000880000306450100880c3d0442c5508401000c01c8800360385d65107503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 648613651 1250 648612401 648612409
    0x608060f2a0d0e061f06050a050c062802030402010c0807260409060f0e15010219120306051e040506010311121807030809010807090302031006240909020702 69
    0xa0800c1c6411070440800c98891080c1aa00407600a6911508441c0d41740c40740a4005040500c0c154200841c0055000030021940100080e0403d400c00f42000343c10806404141030400404a0708004e0000354440c041424000504031f2805440e1101d004500314a0151b0019001c012481030181c41c03880003185001c100320120300729241300305003422070940f29003043d254118150000d000300b07900076007000b20200b02a40d064400c201103850721041c0300d8a80e103400d6220005420403007401ea0450003400340150024240100c14449070344100c65110039a1010180101101e4517600080d1141702c0d00e091022580148100c42e44103c101103d00003010340b50540160020701e05641031900c03e04001c10100709000d8a0801c0511030440b1600e10708542c4805a865902ea4a0900000708051002e100c0031640754031510b0000d07440b10190406a06241c2c503600003d1504030104a8100f01039240d02080c0a82c40303443c1005101e012031401140c0243c1034180001d081100280549070b080c0c2d40c0441d8803029035131 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 648614901 1250 648613651 648613711
    0xf0f0203040b1315121b12020a1806080124120b0303300115080112032303100b16030804150219020607080105090105010c020406030c06020d030608060f 67
    0x405106580100c008064001e800d800c2c1d0040c19450562400814100d680078181b0030511882256540e14505c4441c1d806410003508030415400c20840d0f0f82844221135003008405901500c2d007a01c0307542d0b2549c940a240400698116107020300b82d46601c000380f103080c1d00a14184400c408103d030105440003088c0101c0d00c2c1d402951880d40100082e080c40906401c10b00d0b1080300110000d00c1c014606a0301c4482091010754021702d001c00152580f00100a041142255040310324420324200410ba5810f241210742c100801c0c5010341070200c008144003202104e203400100818a025100e400d01080c010900c082242049014041c000130b580002c08209111043c00020203c80d00110f480740c8421201c44010a150b01142c00584154004607251501886461741255801041054268244401162400a43d4104980058680c00040009080358070614003903c501c0d8000e00b15841200002010740b10250320507862a00f04200b40407002100c500303060b60012901d03c40c071a1041040b060024420303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 648616151 1250 648614901 648614909
    0x5040515030d09030201020609010204050108040206070c050603190c300213120c090b060d0e0109140606100c150e0a0803070302040f080f0a0b100906150f0f0203040b13 74
    0x20080081618101d9008103580041e64000e0b4200c234255501d81541900302d00c214051707907001c941c01c40002401440c20700c009140441c0310300d02041415a0b80c10100340d4641041c0c6800c3c1c0c0312200d845400c0c401c944d1910605484401c1484e00c0100041a0f841c20100c00d1031072420741402d80c41d141e00c8000100041c1e011102e55042406500c1c448a40d9442032036920301c0f1301e010803500c1030a0b064000826998502644185000007040c0d40d06d00752844e40104001c1c0444076002c07076995210031540d07000c1210594002c190039060b1020304118903242007005000c2005401c50350500031179502038800700740c50503032a00004440510026500c40746074a254a002c000b0072000348422000800c0040380c3c3e91640140c011a2110705000c0c90964030307500e2054035401808000c01c0746500050b09540819510f22849800c01500e03030a841c5419220a8098107650381c6803c805000c800040e012503046a002842e0a608403ca1401d444044034800d0000c1d1039100d644981b680c07440011600d03102d001e0104d0a010010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 648617401 1250 648616151 648616153
    0x90301060f0b0c011b14030417070c140411070f0c0f0306020c0c01050f0a031109060f03010512061e04240f0e070b0f18030f1606090e010504051503 65
    0x1450b5211204001a440f52203c1e041d0340d42009110451003900940c50040401251502d0f9500f081d140c4151400d40c00090007900c110170341288034225942e000c00104011805200e007114250b080c0f400e100380405143d802a40141c0c600808540c40510030f8080c2c4e41f055600141e58803814841d400c02e1490101c9030703000400b808002c0d030303400420440ea0ba0300405240350781400341c40b07041e041c4200545481c002c0000c018450b0404100d440e0403580f09502650128000c603a0740c50828020401284035074005107800007641c9000001803001c1c3c500708500c011f02440c03100040c46180707403103450050468002801440034803094008901005503c40d010702c1441e4031820f03500c030369441c0389442202404143c90000701051414900354500307503012070964195030241046500c0c102450800220fa507201038541e80d006c6040620700907540c0e1302800580c0031000ca40000300b82204c0c51034100a100d4106620110500100a00420030070810912160441c3c2d8102c40015042e6900b001c0c0c0780040021618050741 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 648618651 1250 648617401 648617429
    0x319110333041404050606010504030201080109050613020f130b092d0613050f01020d0203030601050a0e03010f06030b1006020c1320030a061703221509090c08040b070509030106 78
    0x32103404100491084d4001c0080781c965848050041d50103100b6070001a000401d4540188400c00c3d05400560300900702a00f440074401103216a00101e0300000b92400012600242c0406554480941c041c05483d40c80c11540c135280b45480050700c0074041000080403c1c0d800071000c4907130031181c6010f110f2010003409807507440b02c94030307055040380c0b07800d010301c80c1b061900c0707d00005554030020340c4440215071600214519280c4000642e00354002420305030400c60bc4e0004c49016440c2800b40200b1034140071004900c0a0651610442c80c417002041d00c090548011010017a2a42c00101184541025152008120351000c1c050025001d50149100c0c0c148903c0c1c00301b021030f9400c500a42c0300c4c8014000030014103894490400c40b072410b169400e44260710501c8505c0c101e46066810b40c107040d40806454504035620b28101d01c0f2211813142140200309108002c004800e41030094116503107007440c00300130318505a07a90302142040601030034108100032a04c1d40181c2c07025440040a400c44500f40b1417 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 648619901 1250 648618651 648618671
    0x1704080304150203070507090b0303090a030606050f19051504030b04121206120206090102010204030b0106110c0406030b072106030b0421020619020f031911033304 72
    0x29403903016100e5a81d4040419400200c42c51021007902c0043e03510902810321a03203400c02e510040c01211500a50500007042420500d40da01c0c03009100440c810300c00418114501404c00c08400412201240208000131580c1c0005170786100682c1078880031100716101c0c0f1031132a07804445000f2030700001c01076041c41c1d0502052110580c504503807a0f400f03a840080180804501a00b82d44052103129900c0d4001252b001c014030f88040544a050018030005041c035603280c540d60781c0c903402a807000d800f082084070410030310407080c0420a01c108069909100d0b1500e5503548241401000300b503a0b0400c146503c0203101d00c601e24403209001818420180b1406441e0b0911125540d01554201c0c3d5008100d0700d025600d141c490188070902003c1e8000c4d280955503142d41c00401c05484005103102d690800c20503641a0205000d0b41c000d02c80d10040070303400400602c0c5001142c40310000d0301d080350014820498050041d003c242c051340c40d044026080601220071742e101d0030340013030545075009041c441c4000b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 648621151 1250 648619901 648619903
    0x30c02070510081902130909020414070f0e061c090606030c0815090a12050304060e06041a100503030a0509031c03021207080402010e01080612070b1803011a010c170408 74
    0x502604001c0d91940a602a11070013804a00c2407010760b0581000d10901004142e61542c02000d1b154000303000426009241d0301c82c1240807104a484401103003000c5050035074541c0c496190b00d07a0350300940303200d45040312242c48240d4031503503a02c5212803283c0741c1d401402000501e4110100941e031100460f10a03e031140859601d50700003009003045810400000703080400c000444240094200640d45101c0b03403103807011119680010f00c265115911042801c03520402008200e1085000d1940458035a043e6080200c094201420301900f4030070380c03130052145540200403a1440401d46c02c040350f59500c18408242080202e050404080304a00d103114503e82e050380040608003503108991819564485040c2c0300800d05070b60103030020300320030040250707540035444683e0016401444440420046c0018034030742100740c0c120840a41002c11001c4101600c101000c0814100f1002442070701d101c521020704030403282e0701044c10017000b4051941402189054040c00c1800e060300ca542d1561104c44c91 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 648622401 1250 648621151 648621167
    0x103021017091c050403170306150a08041101080601080c09150d0c030c08090d0305100305030316120e06040f110d110a511d03060115030c02070510 65
    0x14160ba071044052585005120348111420b03030380d00003d0a16141c03036003580c844454000400c0150000c2b0b14025081c403043c000400380c103610b00740daa50844146800c0c034000c40040480410b460511461205200395680c00c40e50044d44142041007803600c07001482c000492070181c0c901503900d070b02800141c400e0b8404e00f0b60007144a0904c0e5480074000b011020908641a0400b25000095904401405120944207400860b040002c01c8156101d40d074807500c0e5107046500542d000322404070300c444440d8807190401968a03403020105020810750f41c0c020071b01307034480c0d03030044c8003d00c42031410801408004060f00c1c2c140004002901054814116207021080d1aa03090003071441901749080000314680c0096540000b42c11941414511b810b10a8010b11565192080811540d0700a01c84164480e4800ca0703140041d00d1580c2d801918881e8940e8031415600e200408034025041100140306003000c089410004150503c0d000500605044049041140ca0780141d039005908858100405521642c1e07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 648623651 1250 648622401 648622423
    0xc0109020f060307080c0d091401020d0b090c0f03060613080d030f1a040e1507090f050d12050d09050303010303031d0601050112020c0304050a03060e060a09030503010302101709 78
    0x1e4211003003511800c0180300d0004440d8080011500c10010720103140c2c043c05421607481c1c0010100e0b9106080e980e404001c0600c06402c4450707035000c42c0b40c2c903403010140262481d0500c192400714183c2003610350707110b1074410306039a0700744814000040340b00b071344030241180c0d2040400180c200c8601c0e01c902c107040d2100e440001d240e00180c00c0030070020824500b441002c54198601c0d8a1040400e06101070001030003100d80001011701500c2094055180300c035510600c62942e9617a501d0180f400e10950360303000380e2150415800b5261311400d040002d107828061022242e611b052107500c0b030591241d268098406501d00400c40e00011000100f0582c05d03802015a501c0580b20450401c000700e00c84079504c1800344501400240c0d600d1158a4402f0944e0040c004d0070a0107059031301c2c00b5151000b240e050b04050740f0460780a075981800344002c6000380310f50b80d000301c010803080c001c401c950340340100180411b000c081c0c072031b40b1502503102034280902078240b08462a80c010744040d2410492080e103903001c4181c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 648624901 1250 648623651 648623659
    0x10f030b01140a0819180f21020c010f02150109052208070308090d080a0e0f0601120203011b05070813030501090605010806070203040f090510050d05030702010e061204020d030201020d020c010902 86
    0x200c404e00d40200c0c1c001c002d80a80c82c50080301e080c480c0e5444e02d0314480c87e034a1007a18001c83d00081500c1601c24014035942c0e1610503001048a03880d1440010f000505504c401411504005a020700c140c81042c48a411200300c0300c0c0105558a405441200095030420300e42c411090601e1031004001d1820040c1c04914000c0d11020a20303030301e1540d401d03254190200c1040025015000040e5244403952095402503025821185c1162401c100a40761040c02e0700300e1188501d01c407240e0800c52900340513003458000c40c40d50185107400071150281c035034050040001d19240e8081401100c0d043d50b2080c85c001903030008004e10403045a03040c400c0c014a402c0c01501d9842c0220400590603500002c2180e0840d050007404008180c9030200a2009140151480310755044140000074181d403210b00c2041924010009103a6403000c52001404c1c1c1144031001740d01a80042c00000d241082d9114416403060301540e9564103410149005c0b070080c0b01d00e02981c1d14030740c808101d505071041d056100002e840d100380c07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 648626151 1250 648624901 648624931
    0x406030920130c020705030d050d0c030b01020a080c01090b040b15100c11150403082215050304051203011203030b04020c0a1b03020a090515040605010f030b01140a08 73
    0x1c442241c45540d0410a1900100040301e4212001625071140040528900c10364034130688550003c3e0504540b050200002003020400c03140002c03003445401e4039400d060608200310001e0070000703074503248203142c0900800300c0813507400250203003900081203090744445014454039007072420012102c3c0540d000454290340402d22100c6081280e6210311032401d81c0c030340310042c03500c1c3d80d9640d00a0040303164040c1c0142c0418088200d600c01c210252025620844180383c0b123140b602e091040d80d50410090081a400001003000410f2200d00d041e0300849480c075096541c0c0d5114100399103000c0450303030860001e0741c000000286040c040c0c1d2030402200d20a44e000d0200f0070401c4104000d070b0050b410030500c950001507945002444000140001604a8040a181c0356480d00001c0307072190181c0c0075444242c1c541e0100602210940100c003100710341100c04102440c1000f0001300800908075645043c2340d030300d100c00855680911101412054144141c5a4079440000001c0030a5001e032103040190b030540c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 648627401 1250 648626151 648626183
    0xa021306090815040b0a0207050c060d05180a0f0f03031503030e01020d080f0c0901110a0f0209060105131e230102010c090b03040201030b06070b0702010522030207092004060309 78
    0x1585160380610f1700700c1c0b40c0c1c200b662202c1a00c07200030740c0184011542c3e0300c070f07410720b4400035224000504443c62040d1000907403841c0200003281a820040202142900003560250024110305840307944141c001207810300c00b040320300d020740041c4480031038010484079442c030000802d42e1021a56114100c00e80c01d850b44030001140035200c544060383c102e0001841200040d004421150181a10901c14035245a81d0680500d03d1410540c0c08071066819580d000e0025040d81405501d0315000a000c1c030703003140b80040000ca942070192050040301064120f0700305408032210b0034143c080290450400307954070f0540f614000d4034074400890030359015500742408564954042c20b0a1030440e8400c08139245550360720b1340110b009118a1f1101c5500004c18444680410000b000132846011603400002d00b6040484281d08190303002060a0740707500c1940c02210000e5804070304c000c01c0700c0424001003030616522103084a440c64080c00340d150901d0208000078a9a456000000e41f80c0c0a1b04905002841c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 648628651 1250 648627401 648627433
    0x314041d062107050607030509131a06190c02010e0310150b0301050a030321050406140114030a0b0c0403022e180311150316080604090507030b0a0213060908 69
    0x3103240300e402d454000080801450a01100400000e407291801074609000c0c0d2000a400c00301126040c2210740d0f40c3d12941d40755880704003504840c010102d034074604003806502c000b5010b0101000e0541000403080c0c003041164002d447c00c1d4200b00008013660311851041c05101c1c01005500032001d45000b6482c0001110402c2208480c1a50760250460320f0507030450301d003955035200100c0024241600c000141d02c2050003403094a000314801d61020910642c000c1030a412918181c1040840c00042d000110a41e80c0000d09400e1803680325100c4000c90f6207007555600e850066a1010b9044000700c40003d2800480d8401c0c0300b020504010000711818040301d041b00c25204607a0182c101520850b01440070400030705482c59030f1100100813801400100b40080710b6500151200c250511002000d10445030708222100d03403151041d80d0401003043c098841503590116481b01801a84144010542140251301101e54403000c00001d120321560f00e0320014189201c6124201c0e440c014244c1150790340d01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 648629901 1250 648628651 648628699
    0xc1e0d140c1905060708130b03040f0203060f07051603020307020316060206010609060207030816050715030c030b090f1e011509080114010504110c190605010b0703020a0314041d06 79
    0x10f80074015504201041c0c0c2c807090f0030741c440c810751026040c0015000610580c07601c0110301c5980b045075200305008144c81418600720380501003070a403100b07100c10003a8069102050310450110b01d40120b448801e42c0c10140d056100e0000302039090700030403100d01c8080d0212001207007241c4140d8200c0e071241e03a8030001101c0e1004140227200c010303000180100f002c00d650801400e15002400c1003d13041d106d003a81c0342c0c1d01d0700d00994805210004192210280076030036100d1102207050905007070083c03200340000640c00450050400e13044401078070201d05400e0080c0000301d8500c0c02c1141705080307540c441c000200d008071031054110015803c800085000081070060281c8083c04c60590407080c0d091208100250044400e01a10230a0500102203200c0f4100440a504140a00c1c81031041e0f6650900506841050b049210b900c4400c00c40200000e50014803030740c1080d01858080c640c50940c9404080d070707204562200d03e140851006010413880c5000f112170080340111810f80d40d140c04002c85220f001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 648631151 1250 648629901 648629909
    0xf04021c030c12200106060225030b04050a080f1312081902030c2407050c030a030c120504050102181f0e041b11010b030c1e0d140c19 59
    0x180912280d00004404100c0c0c00c125080d03e041c1900c040004101111201c4c41c1600e02d0744250f0344500c002c12a040e01848600304001108210706562003e600350100d4144482c0f00007000000c40100250520505001c050500c9600c001c85607030350f411a0b055a04c540d0031510a10139444501e0b4400100c7d1004c07a0b400c8081e469010312001c0c00c000e68064204c03a0300840000003411740c04200080d02c16800140050109200c0c541d03440c0b40c900d500c5031003544440074018112424020108410340701c8201c00400d43e4850900c501d0089008030701c001d01103135007541907042c2850043c142010b110401c00103401500401240c0701405203180840c1c420801c0c0e01305080e604468644180820308142882210f00c03104840000e0030115091800ea0780c41d40704000583c441000107511310321901c80050080c0158002c010f0100c00034541c401030701000403042d00103c0b0480c038600c1c11070b0755904000e4440c001c110b044c0d42d8002e200d41c4500c4000c0e40b0144d444456801400344101c040c039003920880d940c145165001c0c7d03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 648632401 1250 648631151 648631157
    0xc1f0b010815040902031002071704061e0504240807080c18030316030c0c09050f0a0b03010b0a0b180a0e010303030c1b051c030b090c1c02030f04021c03 67
    0x164841d8001c2e220312064a5070056007040e02c401d21200541c41c02c0200c200410340b203040060f5940300f642007a0020030880c2011364240e4008010400500743d100c450ba04010461700042d00c000900400c060710706214a60040409268078882c02c0900e200b420b03000058030580f0384941155585200c01100d040404440740c0039842424848090030300b000c02c1c0580b41d07202c4040c3c2141d2078411000341004581003028021070000e880c840d400d02c10480300480711001003681346401d120310b003420801001c0c2a08010b280c1c0d41126a2411080303995035094011000ba08000b505541950b5110981d9100a0380650b507051030000c2040030660307040c204003040d18111400c0d111908130590030b5503000c80180004511620030804110f00c034942001034082001c055510800c0200448046030607a2042010360240d00404d040c5094070703162441e203950103aa6405628488056a0b605501e159243d80c04d040707401d01625030344003000f008090020221068019402103d0b0000c04100b03090f00a0280701c420740000b800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 648633651 1250 648632401 648632417
    0x20109240612080a1b151a090a050105040612020d08070f051506040f0608061609092f0901051e0f0c01020a0f03060506090d05030405060c1f0b01 64
    0x2000c1442465481000a526011a81da942d0302d0414107080b40c801429204104001221485a42c01101d5030060900d40807501907030300b0341c54407542d022046440b01c00c50280c0d10b844410001c040c8204d4602040c000080c249001800c0c1958507000620090003000d004604e0240042250a0b039010000c2e1030729401080914594180e545900c480d0b005030000300d0b461041817407810009881030101403204015034100c40d0062404200300000d854071440c0710b241c034a2804005000c11b04000c03514582c843c10560032142441d0404004480040880d03108850301c92505010b038404100201c0700c8500c1c1090b20300306008003054a500102e25100b40352890f40420010000601604084102c050032440c04040050501131940346060050380808040c20940c1d46c006440010160031040d4466220103514042040500304400304949204945069215210441200301001410812a005808003030211919210103410072541c034036242d0303c20350b28945005e0100045442c584618104110160350b42c3d04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 648634901 1250 648633651 648633683
    0x603011d031e04080a03110114100b1b03030a0e250e0c0906040608071b0b070c050304030204060806060a0b1e0a12050403210e0d03051e09030703080601020109 70
    0x30301c0a41e034810000c0d0340d080c00d2000141400040c054201794030300070703198410381c2c1d20001040d5003103600c039440c1407005007150000d001402d00d50168100c195416086000d03515610014061500304509840c0155840300101300203110704180c028180e421600070889645005940d89810807007203800111403c9101c2201c01c10141c06290b04440d00100c03906030151030004a5804074815602c0798104c3d0001c94104030030310003039541c0300d42c2503244042d019400d0150001301c2d0b52030301914040502108100031038a94100140b01c2c042c0102c90086600400801c1142d940d04030b441c0d1190b130b0403600c1c184030b503030003010004003186034104480002d1a00341000d260384045000300c502c0b90704628034081c1040380c404018821a07400c2e11820b4020b0b4026114038038400d4441401d00141c40e040041c0d284014180300c1c0d100c141a4002440c15140e141c0b609000c00c140d0340e001925070b00a0811410308003d803043e4010b002c1c110001000826005002c0d541e6000c0c1680c072800168240d8440060041c540342025001c94 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 648636151 1250 648634901 648634927
    0x311030705030c0927060103051b03030a021f020c01050421050c060601120f0c031b0215190b06220509040b190b1210060503121801030204030f0b0603011d03 69
    0x40008858103445c1070394048034088940f0b00b1000740c02c1100c03558003010710070084400e0201d00b10220a0201d00a41c42c102c90410029100c040549516a030300c48503030340c1c40303403660303041d80554620b212030030000c02543c509403c3c01c4031559804030b91680c80040514800140520a80c200c41181c005c4100402c0592948001100c86845240c0c01c90f100541d280003d0844040b00d00413460301082641d00400d541c075510f0103000c2e00700a41c80c1920159489a030107070010840d10916207034001041c81e820380c17403040102010005020800c0d00c8075480341000802c0030544003606110015842c1801000400b9600c80c8107101e0300e00c0302030380d0240c0b16504003000100c90784000c5189036007100d102c21010800c42d1950010908010010848109030f80091601d0000c1c00800d20035240141400c90081450002c2248040d20f14414115040d41d4400701c400500400d90080c1c04481c020341d1701034a0078090400a040c089008070060750a030780309509000310a04140b0411180082e4082d8a5000d10302d0b20100f19910 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 648637401 1250 648636151 648636181
    0x50a021306120b060d47030709050924100312030e06130b150a031b12060e10090b0726010801051801110906070213060311030705030c09 60
    0xc1c1d20350b100c000101a507103032080074240c5016803850200c4e0401420084586d034802e00b003204030b120040407010810f901d00301c03206040d41426050300700e001e90741d40d40080303800c202550b04804d105038100b00c1070049140e800902920781d4079015603000c0350102d001c114507a00c13000a4540c1070b030041465000b44085102d1600140c2e030380f80b66003400100c004d80d4548103820103008032494800502e0a402c800180400e42c1d605980c81340c540101058004001400a4003c2d035003800003520718810f50343c004420322601294400901100312040101095500d081c401800950030307520a40e01030f89003140c4c4106000e00944c0813840d48105604000c0c2d9666000300d41001d824003080d003010480c042e01c140340000501d5070034040e25071240003141c07601e4a80d10941e103007a20f001400039142c0c9814500546c1460090039140460310450b002981d460507800080c0b0341421911644001625040000041090b241d01c0c1c0c40150701c0542c255281a50744208040d1203545c9500c0c85500040c0c420000f80616250b4480 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 648638651 1250 648637401 648637427
    0x711070f06170c070f03020601092a0e0d0b0a05041e05070e091f05070915120207060f020d0902011b020a05040207050a0519020108011203020307201201020409050a021306 75
    0x5080c1000f41a481e61708202420303400a9000da00000018854119940580d08092141910041103030b00204058a080f6441151180c00c00c510384507045441e645880080c81c40d503030030281106160400f1002c4000400c2c0594049809001c42281101c4110001c0d403402021038104019101c028904545c40c030031000000c100140c28003403c1502980c039006440c00802d01c030070440c0c00145510300b1a0010b070144001c1d8000354403034249415042d04c4547d018090001e40d000043c00581c2300d10b1249822030180c820350030310000c0240007003040c044008144d4842c25910707000760b039680050f1030004100c0c04181c00042000e50801640c0c2c20034003041c20301d07400601d001c0c2d10907000c0303a1074091251903c034180303100b042c07800300d00c07401107800c0c10150741e8001003040c0502680c6900700c1d184a00c036030b0080d659108031003008000c102d803d103c04000601007802c0d900010800392051080d6140d030b54416001354098018004490302d01008601007115610039a100c000a0280702d04a003410000c081c1c0b20652002c01e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 648639901 1250 648638651 648638671
    0x601080112032c0406030f021c0c12050102130303020a0308070305060310090c081518030324030a051903080109270809040906020d0c030908041707030501050711070f0617 75
    0x3c031064151118402d00000b54060315080c05074502520410402c642c0000d610105001182040d0000c651651828000c0b03440c2c062421010b03007501d00d08540a4056800d00806840c01c41d0400003e054010a5070060701c1e100c1d941e4401580d41d6005e0a0303088490503100250140d0240e100c0401080e650303404040d20501403509016415a244452494892803034101c0540420b80c00600c69103aa0100d22442c10b040101c0103941142f410909014060000e44c1401c07000300c480620421054805009d003605960b0000e06950305001030602003451921360a00071030010300740c0400040e080c0f00b18032600e90342a0200107107441c06c0950a40030150042645d000751403200007008222120743e40e41c81502a003e201d00382c00350302c821000640508585100c03031410245818440d544000904440889080d41d9480061030b00c18280e00340002e00d0701e14070340c00c0103005600c1c3c2070902208642041d4038019010031802110640c6460303101c480c01284044c828500880d45000408803001110210346501c840c140c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 648641151 1250 648639901 648639977
    0x10206012411011107210212071a010303020c030c0d0b01030209180102030a0c1b020108160c1a0f060d080414220e01050a0b0a030b071412060108011203 67
    0xa001182141d00020101310944400681541007010320610514032211440e0078551180a80c00080e4a400d1141802d55601d1070004982c41004042d0403035100d80c0c0d04040301c0d500700d580c59240180d51022181c0000d40700f442050024900d5152101910905641c0300c00070982a0346942d0030b000c1e991102407c826244180c402e400420200c0900c040d42c41520104800b103841429030001400c004010148101042c0baa03104a0f80540d8028103a1508101c04020b081c0c1010300c20101200c0001d0b94540082400840c01002e001001700e0706a26070042c19480c502c4881a2582410400040a40b00c4024541901407004024146200c030307180140c6200500008490368400c1012050300030303580a880d1206554000c040c403200340034810715038880000c40080081141860020360603010602c0024042c1c1c0c803403000290041d110305c040d0707050300f5041055140c50700d0030900410b004103c11200580040c43c00703000000c24484d40050307021880e03050740360f01074a00d64012100000c011a40b00b0070040804030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 648642401 1250 648641151 648641177
    0x22d0607050f0a0c03210f110c0d030e030106080f100510050d06150918080c0102040b30040f020409050c030708011e020711010f03090609030504080c0102060124 71
    0x502c043c84260784921403030240b140c2146083c00c3e9443c100c00705e50700640c0025252034081d0307410240c1e10748110740e2403c00c0003040e280480342514003d030742c0c100d81313410107910320300c00040642000400c14141000c500a00c0095100c82c507050750b428051100b0340941c0e2041442001c61515640415042461a2031521a143e1600040f4080d55842c400440c1e0302e0303035202c2c0c0444007100414918409801c1c51801407100c007104810005c02d850100e100501149000280d54a013420254100c40043c58a80385031a2207294140e8001803010001007000103170452101d68041e6140c80003542d44c0705a81c000704410a459241d001d20004144603c0b080300c45111300448003089503020403d8100611550002186075502150b11440d920000c2c0f00e060209401803140c01e001070350030b00113107c54034001c0c80c14041000298908402403c6450700150002d458404100d0915034084001c000740ca04600c110307020340003c1e400480e81c601091298956035124114150300d43c07000c01a12140021440c5000c0c0400012 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 648643651 1250 648642401 648642403
    0x30f1306050f07030c11071e0e10050102070b0708031803070b0c03090c090105180606040b1303020a0b070b060609010c06051f2309061813022d0607050f 67
    0x950351402403900d20410000060344c540a07981214041d854040d0b45915010900340c0e4a81140c091043c10fa040104104210840c040801008040003650542c3c541004003100c407015000303029807401809902400305808071603404582420364000212840c507512140d02048405040100360740034003041100001003254000040c2c01a1043da04141d0b4034186400768604d4206040019401081c11000420259580f01850301c89503102c50400425a651280001e040e07100316003190340c8103680070880c9407080300d00e11606001d691081d01c800007110b40743c00c10328409018158006190580700e0340080d5290034442e01800031180181410862190559150016602d085844400302d542c0d0440c0050101402001600100b4150340041d030107450740c100000e4500003051085010315107000119021340c0b1030600049051090500720b441ea401c000c020201c1c40912843c0c284d100e2544108201503440da1070003114441c01342c41d8042c04100040c0c0e0180310300307600f1809c42a26a030141c0c4000c8018450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 648644901 1250 648643651 648643661
    0x310060c11210601051e1e09040501020a1404051c1e060203101505180307090f0c0809120a211d0d05030112020d0c08011508011a06030f1306 62
    0x2a00d00660031090384556182d038a8007030140e115501c14030f17265407501d5202400da00f00008006050f1031030b040303e01c0451408000e039160f04000300d0b040b4100300c00f003105001065010303140b0140d02c1d50b20040c1d01c1c40050641d6000f40a1402403d501403a0300466840461451101c2d824180c400d80c541c5464204650200d0300b441400302d42601e00d20b40000030807500c0c0d20071021641c00f07003100500186001e203c4040c01003c50181c001015003d0760300e0300581c03140d071350100b2043c00208203800c01440450409a20b0300c011704805c401017408900c6000c0814481180424681c5102d682145013604010484404940b0314084144503110040c8410f04070b0f01d00c00041c012002210341d60310780d45620740d03a0210306a02c2c00d03599000d40420030009100600c0300206148000250f13030b070101e444041c218101d040c143d24000180d44010041e61900b40310034010790581c03208100311030400000f00001600c0d044800c000c60719200c08182c0c03068003040043c00400120741002d1b00001588d4055000365100c0c0c2d5000c00f121 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 648646151 1250 648644901 648644929
    0x10b10050a090b12242d0f130b010c050a050a051207020a090209190f08071205120c0319030504020f180a240f090509030310060c11 58
    0x1520004150a50a0b08005500028141c1c020303914034100064900e0091030202900200034030320750b42044440c6155071000e40d000f0311001407080d041000c401001b4407504034145144500681c0c4400f0303012030351521400c418030b0707210081c141c0c625503800960098010031108406905004403020701c200402c00401030819452710410050a004149003400c0d482c10703201c4104c264025400b00114401600d40e004020101d4014004c0941c442800d01c00089440500720603240502c1e074850400541d1910b0b1415040c01c54141c0020b40701890b8440d072005040c80c0c100c00c170161440c2d0001103940a2059454008e0029940360403d40741444000e50340610040f41010000700000c3c0c80b98280401d5113007204510144803c121075503130040000920320080f00c20020881503d06035102590100440a40801c946038241c0d5103203c0d45036a2075240828407010b83c1d0090200180c0f5000c00103d80180020803280a401c101c03904044072841c00104484429040380c1c111130350800d140710001691582003169001d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 648647401 1250 648646151 648646157
    0xa02012a0206090708190606031a060a080a05031206010e0a08030a0e0406080606090408091206011508090a08030702070e13022407080c010902090117010b01080606040504050702010b10 81
    0x80030100003440c084000e010141c150300000000c1040703920000c0c44a00c40302c68400c54081a13a170742c3c01c0c220001c21180c3c0c009002290403c036451814580d10020317078424942100d02044440d01c880c42c1ea40d4580f1903c0c0001d10b0380e8810000e810713100c1070200e031560b48104145041032150003881c3c08252a060301d0f5000c541298030101d150583c55400907031500803060251820002d1030704d0080103030342c1d80c50042d000038000c2c55071201041c2880078940841c0c41012024180e506100c81a0020746e541c1d0800b4031401e0500c200c82001650b200f881005024040d111b81001020321082903110350160b42e00c058a24401c0d80304400c000142c00200c002c40398464141110101c00040c4540140180e0140001108244200b50304003689044090400d44a256410411103174899200d802007600400382d100703002e58001c01310300000868000c200c1c0e029842003550402030100700410030056071800826101c059206205002c03c4c4080d00306544043e91082c028400420f10740c0350400440c0030b400840c00c00d0800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 648648651 1250 648647401 648647471
    0x207140f041a180f09031215040b03030415180f061b0605071d030601031e0c030804030506180106030c0311040f0e0d200601051005071506051c170a0201 67
    0x1303610750a1512640a41c409001c1d529141c245154000d40700c10040c400340c0d8403c803040f9032039010f441e80e038400c142c802c2e0054101c950f42e944803103c0140d00c4443d845c0c8807001465148100d500c0e0b8407080281d80c101d030000214201b4031401d0000903240440c1c181550500039000c41500700c04900c0c3c502130180949510380b280c0501100c00d4400111001d20910114000d50000c1e004100080070300807400104140c42d0540c16100005140c005206007560340040c095002c0031801005200d03000c60301c1401001c00920a20030005104482c90907101c26100c007510003547d280c82000840c40441041500200080c800a048441d4510f0401292110041c40790750743d1180c40c039085144d80014401503220200c00c20046418411b901c555980c2205014242c0034803055080401160f0050064920880e44100d00955a603210071040c0c00501047c8030f02403052410100c0030084c054529426803c180d000100e0880ca41c203005520041c0307034000000300b4115941c030203c81802e50b01d0300580f003040c2505002c034400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 648649901 1250 648648651 648648661
    0x30a08031e061806010318061508010c09080a0b0a02040b071a06040605091302040905030301060c030e010f0f0c02060910030e07150516051002070809010207140f041a18 74
    0x8081c00001e00080c010002600c61604044103c490568440360074600811140d601c00090a8014600c410040890b030900c03c189a9005c0200382e44425140d000300200300a0b2048170080340c1e00840ca104003025604280d2081010a42c1d004081e548443c0400000d4945540e8103003606075944440001d035480d403101040d072030300499407041d55a000407084078180003050034000022003000d80a0040051350017000c0d099811901c0c0c6801981851780c00c80705a83e12503950701c202074a1048440e504400244040141c100651702907030500c0c0303a1624a903100c4107003c00c103010540e183d941d000420380c0e0002d01400180c010b507a950b04c0c121940c00d04d035940440c100c800c0d0f03101e8030314050300303134101014001c0d8105000000707070703440402c1c0d68003040c10b41c00c000620a4a41045414414100024100d10b4000070f082401e000c008001001003542c00c0c0e00703e41c4e13540c0c0d417403042c012103115608507141e209081010445031890503410411341a00149000500101654000f580b03221030081c03020850300782001001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 648651151 1250 648649901 648649951
    0x606032d0a021215060f060901121112091911060a0201060302031f1401030809090c04090603030806131103010501050c1204031b0e0903090d050f0609030d0b0613050609030a0803 78
    0x41d0301714000351402c00b41c0030b0300e01d03001880e180103420b0680d041100c080280b4150310179980040d8071090b46000019690702030608052101e5800f160210058410b0801d80941c3c41500c0740100300641c0c2103036480c000e100c01c050401040d58844104a811592030302070120260307805010b004090b064903000c0031800c4170005c50b02001e6480700c503544d00f904a664001000030454a00803502043d100700c0e215242603841d94200b018500450b00a84003442c5011008010903400c2501140540d10884100b40c05410017030300c204c141c40b40c413040211001300900040100d035000d000038180c401401415140545095004901150490350040d1a2400f260812210700720740511a50040d00421070b41040e1883d091211030b64a10032500310500884100b02445e05014003444401230310350301d0030141c56090808035152543c075088141e00c0801a4a090038000007441c001c412170f00c40107461100f0f00e020a03c0c3c18200010341c1c07c00010f1136010300a503045c0c140064403641c0114400d482005610205041c080905 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 648652401 1250 648651151 648651193
    0x5070201061403120a0c0605041511070309050906030a051b010906110604080f070609030e011b020924061332150f07060b030606032d0a0212 62
    0x20803007121032640d140e032404030b84c13840d4295911000c1e03030b0350740306102c8121402d8103d854081c0c10145400240030802143d40201c8844207800c0c18107001c80410050740c048980700c1c0c0703000140801e100040410107070400c159440e600c1000103042d101482800d85a060a041810400700706903080940086540d60f00310401c3c4002d007040303140a0741000c2c0d1894030556103880c0540b01030f0113118040f6030f02518078058801c507041c1d0343d4400010301078407045203030103071001046111503400304650520300c4048481184004c4240f0360000c10600b0107071140180e89041c440603c1d50900449007000b1818070780c0c2c8483c0001c0424080c3d0150585856107442c9507a80004145e80c1960902d2001c0a203c00c2c4080351100c284150f482c04642c070440b9280281c12001c0f180c4520340245600100200b180820b100300c03944440021602601030b02c134540d489204054450540072240d07180c0700d54500c564818242103c00c21445401103004031100c0002a4000500c0d01c00516040ba445078080208442d0402d414038034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 648653651 1250 648652401 648652409
    0x2113060c1407110909161a07060e0607090e07020d0c020a05090c0d060b120403030b0102070305010518120a02030304140c0916020c010804120513030f0b0906070503040203031801051c0507020106 85
    0x1d0070030b103211b0900d51203440c42c0328030807001c12624180032142002c03806030845405540c014010050042580c9215031145001c031204004108501400a0649101d9503820300c01d203c0c0380c2c050103600c5541d10090301d0f28a00c2e101d09a030407401c0e4580c085690746a029209000d500141540f54803007a0f40680710003900c0f01078100b00c04c80d4100303100c034bc00c50030b01c13802c05941c0041c1d05003008682c8880c600e0040303207800220350000d8079560906042c85200400c60400030f01c00c00b813400c1910b90343c1860194000051080c0001034005900410008002c00c0075607880d00b0100d99030700142e40990856200184c1c40980a40d29860303030349065001d04800d55010030903890f100e8000e0070901078615041c0c0710044e45214400b02c1d00144000010300b042c40100c0f0311140400b45510044110544216080c050035982080390715600c184141004541c10b24000e03000c0e84d00c2154000e008510f0021039003643c540048481c91040c0c103000c07003840026080c0025042d01a8003001000e0001481e19040d08001d0950b40f050380 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 648654901 1250 648653651 648653653
    0x142209140a150b21070e0f0d080703030506060408010c0e120f0616030608060a0213080303040f061a0607050c1011060c16050f032113060c1407110909 66
    0x1941c2c0c5001107030800300c040303582d00b4281544440c8035142040d03802da5070780210304600c100241005101504100311000011003510940c00684000701808243c48181c800504590310920586c40024880e4105070341c4032501038001410566115115070031350303114211032804524400c521103a181041907650b0499942e00b4010010300480b40081d5440b0700019003041d64501052000d428420702a800c040014003861f0100e0f2264030304500410001d40142460a4800030740782030000f50038030000203032401180c22104a1404440340c1c0d0342c000080100103c1c00410185881070301c0744d151340b0000a8021039000c2c4010b09a1560703114100b2505424202440d001d200003104a124000340005003541e100d50381c0710381e86550f02d1401e00440c01c9920f01ea100100188030384220050369000c04009440c0d0703908001849496003400c4051402ca10800700d800701081c68090300440003040381e85e0401146030311a4200600e0507540404141c1e01d0b540080300903152002664004aa10b0400c1080b542d07000824070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 648656151 1250 648654901 648654911
    0x60703020d050c0a170a1805160f051003021e0301170c040203010b09010e0301110403052401140405131b03050c0402090d0b0c0d2a020c01142209140a 66
    0x910003814000e54900d404030101c1181001606e000d5040c2c0c046480c2002ca801105514009480c005544d0030b140340440c444504805000200d075180140214151440141a03c501d1480d43e10120000d40141d10340b84400c40e1f0b9200d000c0c000c203180000460180100e500300c000741d0303824841c24520382102d000f0307960300840c410001044454000c03000d41f21242d40900e0000380c0c0403005800640540b0750500c220071548000280001000000582c90468604d80300d040c1c80a1103501c02e402207200030034481c09240c1c01101b205c1030054074203a40019400300d803030b41c50002100c1c40c948400314130b090307504060300c03094812010a0003031000803c007441100303c1c21642580b900420b00086000c1c191200d40007040c1e0350014011035940c102d0b5400303840100d80401000c0011601039440b01c00bc00503907141d011555203402186120880c03001c10f080c0085130040c1c5601050940b114140519503220b400c804c80801074503d610000c0f06402201c1c40000c2811441c045441100e040303442d24910340c003801e120391480c030300303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 648657401 1250 648656151 648656167
    0xb0108010e06040905030c010f0209011106010f1203051b031305091003022403040302030a081305250302130903030617070b03070e061603090803120a021803060703020d050c 76
    0xca020b50066042c0c4011451082e60f2034420b10350b00400ca400340c040d50030100c0464080c445980901580007090341c0f0b64151600b9041c00c2510350340e081c001c1c0782211400c40001e00c00741c034036564250306072031080c5030036807070845c5149020750000109807080e01540c10000d902c010003908801500c000d00402c40300c000b501e00f03043c1c4510354981c2d110721009000300b03841150404001551400e000c0060b0030804120350340c2c502451700a4496001e0374070354000c6230604021070040c0050702010003684c0d500c2401801ea01104a0282102e1820701140e032503440d48552010005850310f081ca100b40100b01140400c402c501c900e0301406031649900010100e4680c10302d00f4070140c80001b8140304542401c90f180350780b03032654034048822510f055607154104000058800305c4013a401521450a4041e80d108000c80d601d520202e5100d1081c064200b903040c555a002c02c0f01420154010502581405040580c2031042d90200741080f4040b91003070301007036002c0b80c2015821081e0040c15880600e00088034500446 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 648658651 1250 648657401 648657419
    0x12060b090a03120216030f050607030509060708040501150e0114061614010612080307020127020906030a02030604050609070f0303080f100306021303050c060a0212030a0f021c0b010801 81
    0x40c403018000b140c14844100350341303000f400720040c60140c005110700c2280d01c03030801e40806c03042c040040340c5511404001400044c420700c00d1034040c0318900d002d81401e4440800890311404040c0098465550307130440c1c0d426280750400e680c0000c14101010180e00d40c076100c1c03603420f00d2151072580c0b03008002c10051400c4850150319041502917110f0945070f610f07000c40d40c00034010700081e08131122814003030040800b405a800c0203903100d00401d40c000d010055841c58043c840e14280116000d4009045d00341314010b113007140c0c510782d00203c00340850300304002d0390300000d142000644058405820201c00d12110f40410310004005d812600c03000110b20385580d9005021020041802c600c011004012911019500d0500c1004503003298003551580b03841c0102e401154010310044880348960b015080d0903092440c1510b043c060141c018017071404c0c5d40c010305c0c0b61603803000b080031221a594041e143e0b010a09403000d044d08800140e40b802640708240c1402c0110b5112000150601003c0310040115580c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 648659901 1250 648658651 648658669
    0x90a0302150405190309171b040b010215070525030228021002010203070e090408030a180501020414010809150601110a0b09010b19030c06080606120712060b09 70
    0xc10305070441101c0c0d03964100305040040110a01110902d0800c0c01010706522002502c2034500d520761080b00c0200d84040c00d550b64407108040e454034602d40001146502d0a5030290717140c11018016520241200d003405189a90200c4055011070400f003103103820b04208448844214080301e00401103050280c8002e55142d444c080c445020401c04004500700001903006002c182740c0c090031040c403c070048400030f4040d4000725101000150003035501110341c0307050ba0416001e2900400128515140e01d014480600184c1007516241c032100d028500000d10b013403004000502250b4500550000e82d20001001c0700c0b03002d0a0b011035075001040c1d29041c0c90b0741c0345c64103401100c2420301840d041d120085150805040034406800c510041c0d0800c8016030040d04110f03210304c01201c401c0c0c2c0c0441c100303403122901e810500001d4620031980c8000e1041a00650500f034010100400d82400d0800d540140c80d000c103002c44e2140b0016204001220030ba00d850302a40010b000c1018484d81040c00d22030104d10504 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 648661151 1250 648659901 648659923
    0x1201030c0e0c120403110a0b0702160b0d0b01020327040c0302090906280b040e0c070308010e1b1c0c020f0d120905011d100204150c0219090b09090a0302 67
    0x1803000c0c04681017600070703440100b4415402080c0c42c007000d001c0c20500c5000c0b000301d03426005030084441d1520740001c5c0c50380da88103a80840780c3c0c03030b800d003660084004010400c25510358198481000a0803600e6105000461818001c80c05413121040b403905000588483c0030b1001c0605005020074041603458200c00b5070300490a945140c1102c4910958098981c150a442001c0c0409240d0102c1c2422410300140f00361895010007060b6a21440010302e014403500d0340250001c1c1e42d0f40b0040c000300e04146656a00512200000290000b6020462809502461900c1da03030520200007400039500314004c0c04c01450180c0040c0c0004005915120b03161581c2d401c41c40100002e502d080d403d070a00560041032200c0d0000001c00030075500522403074900c586030188150340d116004c8d00b03148030036040c021242a194025255000d4000c2c0740c0c026602c40310210700490388107007a0000803c03d0b20040c416900181824603001c2665807006d030600185600c0940591503a410403076030400800c1c0c0021380b4802c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 648662401 1250 648661151 648661177
    0x1c290612060d111c060b030a02030622120801030510060b0d0e101401180504030e01030b270a0e010203091504410607120b0d081201030c0e0c 62
    0x60000d00d015400c10303c0c10003a443d0701c0074a0b0b00a050a501406913041521417003184104900302d0890101035031104000402540350740a40001082041380480e21200e0312507400110718221420381d80e20541c080072000c08000034035400010414400101300100400244440030403226082c6181840d4074454440c00c0c0d10340a03202c00010080d104100300015201d003110008002006412842880c1d5520078070584000006010103800f481405206090080b90b25072105803250b5030ba4001034026003c0b159107954081f161601f0b4909107413104030007401c0603041001c0d5260314541101c001003110300e650007c080c1ea81c8180f04210070381ca00000c04120100841d09520070716034440c90601008030b42482144441e40c6600144610020b00301013045410410700b42042c401180c00300d0141c1e17160411500440020351640300d14801c1d601c203503c000030100d0050003400d005219521203241340d074006c041003002150400010014400100c000c070707020740350090f819401824501c00061442c00703602c14002034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 648663651 1250 648662401 648662419
    0x3172106132004090b040b06132108070b01090f090503090f040204050a0e0402030c0d030e010e031e07090f0c05030114040612030c02090708070210021c29061206 71
    0x100400d050340c8054048a00c000c542d50750341c541d43e0103000303005c5412141d802170b400d00d101d0110300c0c0b401c64162a44c01940d0300c42c0044a030328000070001c1d4000800414001d00780300340c0c1048003185909001f070a5441c06800711030650f514000d814811200f03002d896241c100d141c07807039417000100d02104035455110101c0d159001a0306210008009105a51043c5d0b40110362550016032421075012141c4103c1c0202c0c292140c007200c41d0144000d170a280301c1d0040c0043c1c0182460840c0b98011500e001c460a0040c0c115002400b50a02a00c4002c1c280b5800f51900e60003c441003040c0f10f40c42c0111205001c00340c00600008012080280c01c0e80818000d11b0110349115690a606813501d9001c1c900030146240c403605403072040d0401500d550800071050b801003c075a00002c0e4654040d0040d103016075020b83c000d088400c1800e840304002e4106c0000713000e0904285d403624003d85010301505d5003544441e8913010440b001015000340700d017402250f642c0034020034445610b00c804154a401d078071680544810301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 648664901 1250 648663651 648663671
    0x409020904060b04080a03090e040b06010f030906020a0e2e050a0210090b060108180c0d08040f06021501081506120c09040803090c01030e0c0d020a0317210613 70
    0x101400072030f00101880c58000c540001d180c100000c9646006e4042e44490a441d5291040d0440e40b02084a018044a07070650205846500c9420743c42482507040c540000c448800740c2e9503c4c160b0b40902c003443d0005074203000c41c1c0307114a407640380c02400081540740700101011100c0c00f00808400500000240b12005c00c41d40000f600034040700c1342c20146a402044091f940303203801018410305440103030010390940c000070001c24201e10700c000f00c200c20350010300285407500208600820200d00407240c9507800d0200003840009501080042c1080c3e170041d01014034021000c817001a016030128106521140c03a9603059002d104241750804400c0e103c40040c0310710881110328140052429a80003400f5004201c10701c000900554000c0c610241a1900c14185000450565111a0f90f42c1030a411000d0705910030300d452143e40082600c05448201c49076500d4071040d542e121000e07540d00c40088006281010a020321101f081d401d031110b0f034402c0d0181003ea01081c00903c0506001072120340d2150b001e0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 648666151 1250 648664901 648664909
    0x20c0d05340e040201260a0b10021b0f0d060e0c0d030906050f21070f020f030d200a080a06121a0a0204091e0507030b31020c0102130e0105030304090209 67
    0x700034a090200900480e036145106d03200710200854139001c80b649403ea840c1410f240009001440d10501e9004194100c800020403003418960f0211340c1d40a8528440c800b942e4540d218900b5503039002c2c020010381002c41d122450706280c510460140b04405004590b40042d801522002c00d0346d1035403411030345851896103039000b20302ca0b0010300408020342101d07603a06042da01414a100d081c082e9a01141b12061000503a075038491590401e0441c1c00c01d00c02940743c5100780c0d00c0611002403c22018800200d10b1056101944c0203076003c00c001280c4008000d40c028280c02500300034507407500340d00c0511007652100028800aa604c80030181510000729040301600d4040d1400341205000400110030701034400300921480ca2007421382c640c00e02000405142c024400d07450400809407115046d00000030109294869107203034640142c0500080703103403074185480640b2850310488001680c800c09a401c0d0300c0c10312600d034401450025040d006004070b0320003000ba2021036102703040168440d48004001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 648667401 1250 648666151 648666167
    0x13092301081b01031e020705010207080c060708090a08030402010c030e0a0b0702030f030c120703030608030417161a09040912082a040e0403020c0d05340e040201 71
    0x242004148090010031040808511148000e40c9000c1401d108401203005406544140c04c25002d0540203d140d6802d4440d642c00601e102c034882c500040c60f164003980e81600542002d2107000c819402202001022900418480c0c0c00c048014010056000319585100745444000c1009040101303286078581014001c0c007840f0581f03800144081301650f10b400d80001290084602a880303445103040f0807900040110441d103480c0310020241c00d680f800f0010122043e0b0164004808040c0c0c0c5610000782000284080c00240c415121000440e4102240e410715105461148400316100318008100c685c49c01e00100002d0400307000030300e40703800425000400400800c0c0000d824601d200151145140d070088000f40309281007040034000b01000c2c0b40c0c9138a41b203004050381600c83c0003004180100305085a406511912910481311a60070309008a002100e100800300c503194003c500c0d00700004181100d802e50b1003050781240d1110303030400d41da51803444124454503580b0702000e40800c043d64031074502 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 648668651 1250 648667401 648667451
    0x405090711030316031b02010f1103040c1a070606080102070201091e1e05040504050a020102071215021e0c0d090b1204150902031f14040206030403031d0d0905040507051309 76
    0x111b4102e404081c1c081d1000d51110070303117030b850882100d10b00c0b03c0b0b05040d01d0049400231401c010090601d0103010082c402c0e96019400c0d44424050040091210f010300b01c00b0380039117000582c480360144000744c074000183d002660542d42080811000d0010003000c8801c0b10f19289d02003a4400808400a4042c03481c1c7d000240c000b82460200011b024001405101980c400e900725118182d480c41e4200c541c440744c1e0801080980400300d40d503030708041c079006404103260704140d4040a40c1440c008200551202510b00c8407500a412020350080d0070102c01001400740c0100189808602c000c40c115160300144000c00c075030103c400c8014071100b59809114500c0d400340c21520342100b14000070381344940300400d00044904124216a0034142c504100e40620342c06082641151503981e0140c001d8034483c01d11210f0712200000c410407809042000c11954061a154085014180001d000541c0e200400042c00d00c0340801c04200303d0b400d40e182200450714054400114941f001c0034040c030b1a0a4091 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 648669901 1250 648668651 648668681
    0x606062327041a09010e04080f0703051303150c030c20071505180f0d03050a11070b040608100506040b030c1c140a0902102d05040509071103031603 65
    0x45008038501d4400c3c0454038912086910b10126039a0708131005100d41d044500a0000c9018480c1d03402030840c40c40034007412071203820030900307118800340f03c1003010100c0e80c07058984c15140100001104001d11070b0700c80c05406843c043c800d1510655015203001010a003055203110703408000c15040b10240043c001900101200c0990000e4416006003550401800141d01800890900e2030501d01440d1044050398060241040d2509030340717056070140c1040c041d13401440901400c40d20b440034140484806400362900c4a43c980741851001004200c1c000c0c881034401d00a00c400380040e81d9000280e40c101c4400c424101ea49039540d907410681070160500780d0352464a040d003d142c01604036007000d40d001c00101c203100c0050b520b0030020420340350f80c603002079003041c507582078144a1842821171144412407460310309180180070301401c80a400c51001c030000034101050034420351428020284d000381c02c81c64805da503c4040803075039441e8403020f05441c0c04010101a0040140c0c06a0041e592030042c00e2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 648671151 1250 648669901 648669911
    0x41d061c03050714010c021b09041e0b09011d0708031207090b03010303020703020f3f19020f090108030409022a060f0c04030f2904060606232704 64
    0x4c0d1000c0c081d10903405200c0260040302280210a0041c00c030380401300d00c00900e10502610b51703480f840c24000d002c41501d41000d0441403070a000c9207800754041d0250034940c2c0000b400c060064200c070111248022070180d035800004007040099800800d440d140c400700b1344c2074a120740300c244081e560920f0940c404151540b001c40000181500481d00740110b038001e4861014120800c800c01c04107000050305c03841c4543e100010ba210028078a130300c82001d0001069241c1c08580d56503165481c06000041c1705004501c254040001c6003011f0700301c0c0c101a10b007a251f03058294113000d0500c0d103d008130302410317030580d0340481c4900f8607810805540486508140b40d944014180701c13800c0d515054202e8000740362003d100c0108600002c400115000c41e80c1090064000820b6560350702041c1e6501707100c0c1c2080c1c6d281b5100310301c7c440c8031000300c06010704d1180900003031052074004003904a0312644440741001480154142074001490704071201c84449282d0391182810000001c250f101c85000d10701d810a10301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 648672401 1250 648671151 648671183
    0xb010311060714070e0c0c0618010e010f020d15030f080a0c0b2d010b0d020304060f060f060801080a12030b011808160906030503041820041d061c030507 67
    0x41a420161010b180d05c0d2101d603583e0350310207505880350740760050741a031121002900c118003292200003003140010000c00c642825000046c00c0d1400000c599001980c009000d0301c8400c071500c030f00e0310312040c0501140f100c079265848826513003a0010014001c00c2001030014442c0303105542649440d03511a08a01d4142040502c00b849440b42d0381c4881200c1c2140381c03800040980e00f050690403a03050701d076180d2030200b12404a8019420180084803240d0b00d54060072492400d5000300006041d0001e0703805581880c00400a03c80740041c0c0c041e10aa821085030000801c1203024605082030301d90402180031440c450048030848140604044800a8444040303080c3e00045904000c010304410041c100d55121100d0303d0840d80103100062035640304220400007a094404958803648901d1000a0f4410700030301c19580c403504c44075240d120349000182c1030000e8140503148558224050440c20301c42c3c5003102c04101ca070081a00e02e444400d8411405a0815114008072480103600c0b55810054500c0c0d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 648673651 1250 648672401 648672403
    0x13090602030f1f03111002030412051f060e04020d022701092304111c03030203010504111c0209060f0403050d020712050d0503070c050303040f06180b010311060714 72
    0x30a40d440c280f4800b110003052007009601032100300ba242c01c55035805d60784212004101c0311480003030103841503000c140000946143d2504001071058000c0c07001d00800d114030000b018003c0b0b00b40d0201083c6074176200b024461010405000c6522503410b850101c1002d41d10f0002607451103d103c010440e0b02c40c286038a45603c100200103c1c1215011007040c008145a0740d007002580108900c140200704580000030085000502405076103100505018080724103a0341c42040014500c0f030660210344c000004004504117480340314480c1c0c503203100981c182500303042c101c601c804690740003426154004c07500d00c40c50750300e8104070791086c1c00e00b10140d40d407260b5915100c0e8540001008040160148610000344062030f050009080c682c482c000d08200c4050060540b466000139000c0760400851040342c80c002101000154040c4d40202c0c210a1089010f140140542d80800090716034400b149107004001261210050f055940c88198046491420310115030540120700c0082c042c3c2c01c003c0d00c02d80e8000c00c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 648674901 1250 648673651 648673681
    0xe130f0e010b01020d08270a032307080d200d1b02031c0507180e1014030705040b1306060503011401020c150307140d02090102011b0804021309060203 66
    0x54600c0240074240c070103001a030b1507002000800c4042000c040000e8503040d040400704d51310407030100c0741e006590807140c11140b0b0069402000c40c04101c00e20176240d060510042c0780c020745000c40fa0703200e02e0700c90140d54988050048800c94244241c4502086d0042043c0003015540038501805443e11000030954200203405075070008868485509504d60080f44040111000029002e803102900006103000380c0051100410100c02c00c03a1002c12004184130b8481a1401480c0781e00b4480c0341800c1c0000000361803001030b400f40403c0300600c0340e00d00d603644000c9030050498004480008151a174070004c03c0700c40c4680b0342c89240007440c1c030740041042d41e04040614144c0b042e403c6c2059034145458016651401e01d40c00303440c8d011b50740001c00c2d01c041030030500035640002903141c0401c0441c42500360903042c1d002110040c0c0042c2d0003050f022190359091061900d60308a51160180c0000d002d0000b8043c60340103400640142c1c20102c02250b2080c0c03903023105180c070b50300c16000c6690345000000901c1d00d134 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 648676151 1250 648674901 648674921
    0x40302010608061509010f03020a0b0a02070b031501020615090127020a050c0d030608070312030207150501181112100e0403120e1b0909010b03071509060807020c010e130f 75
    0x1c170321040082030300700108184105680e4098101d40c42242004003803142500a1920441144a10607011a00f640d03000701450003828902d103c40c51400041c2c3c00a070800b4401841002c0072101e00c031000803d96a0341c2a0141184c9807846c000710034184681c2c04c0d400201c0403810360398040340002421410a0350200080076401a120265030b2180344580e0100d041e9181032203500201d07403200b203052010805400442c81e480045040041c034140140d81c5c2c0215880c0500c03a8100196619801000101001a03002c2c1418180200030054000310346142101c5004001c0d00b402c0c415055400110308545010380741d009456544214800380c0344c43e18000b4440c41c04003404020403030515401c00800d007400644020407881d824070340c0001c01a41030074090007200041c50030300159214800c481c640c1d1000d00030340d405080784080040d0700b515009805000c006c0035601001c10401110704121100340d021821400e009024070340101640c440c400080c4080811103c1310030000e20384000720070400e0721076200030140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 648677401 1250 648676151 648676159
    0x20d1113090501270c0c0b160e04090c17250602120a080402220c0201090b09031312150e010504020102070906060507080903010f0603050a0309050a05060a080403020106080615 77
    0xa41c1e2030700341c03181c1e40d442c0c010b8141d901c80e03140c0381c0070558550b80340d0413070085072205d13160102088810751110003c1d081c0c10345540030310388440b520320040c0c41d902012100c15a44241c400b4800e8517890781d9110b04c101c500b4440d4039400d0220304440c8900070303030502060001000940d05207003451400031014030b008446d80f10301000742c070401c0419003040e4110710a40c2c03190421740d1075a911590b119020300a284001c1141c840c0c0c100100c461641490300644907280110b44583d00029070942c4c00d2800c1020000003405580c0268400d000380f041c0042c03480100340540741400340d003004d0142a0310b0200502070000401c03c07150360030540508a11581580128820380c004d900700c40030a940c2c0c2050300103c50a0303001c1c01b00042c400300051000b2403509001841101c5c2e000e00002688280f100110085600f00c0d0401c8489810002c0120103050303001e610301001e000c00300e03812441185400000b501c18401e8541c000f0502c0240b20000742498001c2d07010390014190b04c0207507943d0b40b40200c02c1c3c007401580c042c020f170f2007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 648678651 1250 648677401 648677411
    0x50906100f0612020a02120c0a05060a020408030a0c1502280c0b06120a061505012d0806030c03060403020c010f0e060904020f070f0807060f02090112020d111309 71
    0x1d9081c000c8050044400319100c40040303030203042012010b50300620120041d841001080001c02c0110f00003003804018260141982c60840c0c5481810000081d00368440c1600602c01406510f201008460380c1c00480d040c034513800800391400f281d140c030f545a0060044ea2020a8640703802d940d42021020813100302410051002c03911070b00361594103c0800103000007150034001130481c1088241c88607444003c00072070b65407100c181e172a103040c0c035a070719460350408007140d0040005582016035045030001040640c16200347e007101078030300d103105101d00c4000c200c0e08030080307811524184042008860b0240503900d6a01d0203040c040d40c1d510910b0741c110300084a1a540245c054071a18840000180080485107032000060800c806504552011000703c441000b401002401a864240c00140703e480c80c0341d101c041030b0400c203046505000c25100c10300c0c0100200c12441e0380c4010b41c0140003091100c0161240c0241166400500c0f482a2400c0348070000039400c950327900036060078801c036510074a080c42 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 648679901 1250 648678651 648678659
    0x319060203010e010e070f030e150a0e01110c030a0e0f1801061e081305070e0f090d1d040f0609060605180a0e0a050702190f02010201050c0f09061c05090610 69
    0x240301c10040b10042c000a02d842c7c10b1100080c42074012040c4100284225608001d21842c040507008040d141c90455a41e24800760340208020f01801c00f070303d101841b0301c41c20510303410300071601d80c0b058046c94002c1041e80f144021485e59140c3d506041c51201511480d00c041090707015035098142030249001251400040b03000001c4900e4150090204075a84d4407001e45480074841d4170f03000505001c0300c16010310301f00400c428641c120018402c501c1480340c0304590920700c81d69402e100048507483c08100e219000c0141b0f50207080007120b1304440584001440a440507950001803a4541002d2a0700742003034400520250f200c0c01500d075644d00b424030b4998441d00f090410100350303072038407600d05c120080c80c000170516812540400c0c1d2005950041e05d2001e02107001400d684420100200c505c5800e18807864159642480703015400140084140c4c9804051501000280a201e540c00c4c4500e00005a655a518ac030b45202c85510351135907814011030402110040e250074007114030111b10301c00c10800003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 648681151 1250 648679901 648679919
    0x110a0b0418060f120809060c0a0c0e010b0a0806120c0619080a02030411010c08130303080103050d0305010e010902070503212406090103230405010e0c040908180319060203010e01 78
    0x608441319407114490188150351a0040b80d00010301e113039403007281405902030340c2e94188040b07042181306141c101110340c2000c0b802e006000041e008141001418881c18200981007481140c000300304a42c04058a0703e0035141d2450308001807281074101002150340c442924110403048030342403a46e201d071225a40c4803031640c4128001180c000c0e20704000e10b0f400038184d50151600e81540d90040c00010b1802000b05820a42d41d80743d0341c021400943e01400400900005003c83e0882c1c00c4149003d000fa0351600c801c90040440c180146904581e0014081c01008001c10888000300001e2544210441007007004015088003101c03814281054007084d17071801c004100e00700c4070020009000300c0c10030010000450040c12101415500c0c080070340f404a2802c41a407030500c0c41148610000725050f00204985410320b952105114055410640e03448001520300d000d803000c4110f0b00840c85580055500000d240964260441800040d4880640144901e0750000c1d41a2105014a41322130307641d81808c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 648682401 1250 648681151 648681179
    0xc0e040b01050f0a0e01110105040f060515030703030f020a1a25091202040e0105040f1523040317040c0e0f0c121816230d110a0b041806 60
    0x4120f100f1030410025074030358050390380b0f58100e10040c0751072110203440718407440c21980241c1702901c00643c6d1200c240c04010703ea010f26503100d802c56042c0544a4480d00c0482d03501c001900006007840300d0000c000d282d8510821211101075001f03a41c000351712103484011306941505030356800b00010701201d1500c0030204070602034101095076482da08003900c0c1c591501c540421890080341d05c00d84860785001c074060240942800396016100c400d09400007458208881c0703161070185002d2a040c07101c80c2030181008902e00041e03050090032840caa41e6a450b04441800080c8140741c840c0c00f402c0140300900c00d1402c01d0b541940c0080401035115142c03000e003a20541011100d200f00014100039081c8018003001d10381760031035440c0e1403000c03030754241c2d1032400d0510260620640001041c50703810000c07200d40e4030140300060441880d01074450750f0040801c003240c85c0090080d084280c0a4254945915219459801003104d48220b0b91615152031482c0403a80c00000140d034400d090020100b28807600c0465 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 648683651 1250 648682401 648682417
    0x603030e1c030f2102030408220501050d18021513060509090105010e030114011e0e01060e06180d06091b080c1c0204021206030f0a05030a140d0c0e040b0105 69
    0x525125450002c1c0125111404d41c03039001c00c010b0075441c1c107003029105400998043d51155132030a4581e0103045080c44000c1c00880e11074901808014104010f0b600321b0304541e94828440c2011584245910320f1140607072070041c0c0290040e40c0751942c00120100c9e0800b40c141400f48400e0588003541d074800c200c0e0140074407513a00345d00071364045c0100119030050408003410f0201034000f04022212800b172607a2100240e1007100c4004503a0700c0c45407240300c8140c2e00c4014103483d90300b202c401c3d41064001040b100d84210302900500002a1920b441e41c1440303040504030400402d402841d000f01c1c54540050318405c081154054403022040a040c0080c40742c51050740c0200300102a03c2194804104003081100d8088080c801c2c0407213840003580307440c001899140c20030380b030050720350501e1010325240c810408210022500b042980400180c0084111841c400d81d0b850403007188100700404036010b1003403601070741105107412042e400f91a001000301000c0801207408000d81c2c0c1c010401580d062040c3c1034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 648684901 1250 648683651 648683657
    0xb030f010c0f0e12060a0b010f0513050103091703070302090a21061d0106090207031b03050d050a0b030d0e090601021f18140102180409110f0609040603030e1c03 71
    0x180305003855103d40081c5803055030040038081c201c0d5805484c0d50510006444001c4030340d4540705010641c0d40c1140b00b480007105103282485c60016000c0340702d03aa05183d8080d142c101074951408005021022030002c00c4501d8041700c0707950fa410100d50140c000c2d130003080198060408004009090003070101440d0458080d6409403100e0300403641c0d5580140440ca0302d8880d07040758101c0302c40103e482446608054144041e0040e030320380e141d0902615010100341c0c03003444c0301271440d401400241e00205440c034420003100042469228080f902000c6c15038000c0490701442060205000c182c1d104030000b002d40d0091b102c3c502561145001281c80f44050407005403a0022098402c0a0902e0743c1d10481d11040b0051101003074901e05c0da18960642c3d80c481c41e040303160f900070845540601175840c203040c401d40110b50400001503640c2e60300160b04411000c1c0f902ca00d144140c101e0352522284110b440c2030f03e0040007013000c0740e03c86c40c0140104840d00341aa000304e0b243e43d1400c9184100c58160882145c05032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 648686151 1250 648684901 648684917
    0x121106280302160b0a060f2301091208070b01050a2106061508010311010e0d0b090c1215182104081209010f0e010801061808030d0b030f010c 62
    0x180281400e4503041408056007000a01810494242d10140c3c00348070354400c5809050201c440c0045e100281c00500b41051074500421200f041c1d00002658659008010b400d1032031480c1c0103a55259843d402081900084016401045000c2c0003c1c001c1c54403440140c916a40c946003801b003142041d000e500c0e00d09401c0161f200b42c44002caa000070307c65105040104030b1907241c00c800c0302ca180001042c600820b09440040c0204401486007480c10b60080c82c10b04004501c5000061020031224000b03070800d5026004185007440c24001e8400505001c0c0001500c5000c4403900f5541e003134001407000c102d80c201e002050005002004141241152500509030514440d480800201c0e901e803012b003030010100400113500b2010321660001c0b0407910702040d242c100c104005019008402549010040000b183c8031013a03070414007550540d812440e20000c54103070707001e80c445050341a0f041349803d44070203d00520a540c003504403800c920001e40c107076001e4803444501c40d801d88000e44207144c041a800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 648687401 1250 648686151 648686197
    0x3030a02070f08040e061002011b081906150f020601140609061903200a02120f07021201020408070f080705091e15150406080f040204060b0301121106 66
    0x180c0c02622140340242c2c1c1c0c40d00c01034400e940f41941070b03000d03a100901c40862001049a5440c02c48a8000c0381c16240c0000d000c008072401c5505000606128003005010000011541001440d110317443c100800180401407a82c40c0d07404400c002c040200901c0c001001420790350b0700d940c4045440d50403991140d1140c01240260800c201071500a024001d13001402400f200100c0100c01603061422581a2000140c40050412000540d084d00c7c04030700c0b02540070081c400e40c103640010021244030b1104041900e45998402c940403500c40e285020390702a0800c200403529900650090003180e60701c0c0f085039900c69031504540820482e82c030a80310150803181007000350f030a2001c5403945c0002008901160720b5101c1c64921108101501d611040c0c442d03103800c2c006141001c024a6844a208081550a052510300700505800c0300402c2c07120320b10707400070201e421911160041070103884940c10050b100d40e160502480400680402a161010210030601060030120304441d0180c5d20740001d00b12044c49 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 648688651 1250 648687401 648687421
    0xc0503040f0f050d0c0209070c02131a180108070909020102071208040f170106050906330a08070e0604060c0305090a0b1b010f0c091703120a0204051806030303 70
    0xc019007654154080000c640010b5400c0c8038131420846117481c0c20010541c180140070302010001c10784e078144106d01c40403c015036140d4101259114118a000c01c0d6012140c0d586281611941103540e0010800401d01d28014811a00300e416070f4034a501b103d6105940302581d00c240c1e100d1450182c0540c0201f2824484140d6110017140014000d004491030240d507088003100c090103551209081d81062201461145428010f8070300428044440c80d0541c03d0210010b004400b40b0750030007c8411024000c0c0c15015900803010044814609a0310340360b220000d03024000880403150000058207071400b030400c0b03180100944041da0707160341c0c4290311100b1664043e241a07200c400290b6200031841800204004a40300138840c0c00c1d440c0e6a03c906c00b401a145550070755003503200220303415091244a10b038040e8040415005c4030181d5642d452408d01e10384e00b140c00e5105030020300342c0160840081046c403c0a44d002842151070989000414000d84551051030341e07002d1301c0480d856002000440c1c81009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 648689901 1250 648688651 648688673
    0x90207030e092e24020115210c0b03070906020601060203040320040902150405130902240c150f0705030403021506030705041503020108131707080904050403090305070602010c050304 80
    0x1005a400032030603443e032401400c2501305491034180c0780e51084a00301115030a00890b65203020303429216406a080a01c20712099615445c035032420f106000d81002807141000c840401005030705400c0d581c030709015600500394106402004007621031040000351341440007003124101ca40084403050040e9015184255410601d0f820a9000e43c4903c0042e001d039440c0011400032403e0360000c1540c851a0005000e11080150152425245040d00010150f107915042851421002c8030101300c1c030408844503400c0d4043c0c0d1136540340501c01e40d0103140d0132140603445280982004004c0541903a00c40c2d400300c03528030040b60b0040040e0450303081521411000c10721707950003510090684814540b00d10100d812640304200d02c82c0c01403a040b400300155604410a00e81021403c108002003420980710110001c8600010844103000054004140315002d4240c80c0e040c500200240494102410000c01c00c0c50307180801d407414011402c2c0000c20301c0c014803410781a07202545a1074156920303500d5082e1003032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 648691151 1250 648689901 648689971
    0x4030b0619080d0201050901051b12090a0b040c06201b011b030302190f1d0105040302040f0902032a0f060f040b0a02070b0a09030807050106030c090207030e09 70
    0xaa1160740860080340c1400340c511424165400040c3c1407501900c0203096400103845502e01003031010484130707070081c16000c80d1414a180400c03007640381c8030800311904d070078140c00001d08582c00010501c420092203003207120807900342d6550003805260740342710400a105145800c031115480101c0c491604407040201903014003050402711802c880b60f10200e4007002a10200300c000942c0014014020306010410041c038620f580340198120421b81d101401410f4400701c0d40c0034058240580140da684110101d40207543d000d8010b0003c400c1803515600a0004241d040303119006202d000c00d01c0c3c000e04000c007031880c0202c2000e00210070651003441000040c646071660004010040203001804540051005000008040d40e441c014068001c3c285002c03904400d51104040041914140d8059100d00907203800c015800c1e994406072a0180c01412540e0000746042405c860008000049602a0002078000e85407404051000800c10120110440d25100803c0d0b500201000c90207650000350f00351 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 648692401 1250 648691151 648691189
    0x60b18010e031002070303060b3103150516080417070624050102060a090c06080a02090907021e0c1311070b09070306060902030f0109151d06030106060504030b06 71
    0x3920780038020a080c180c1008984455680000d404001c25502d4440c001c01801509042030401c0c811000ca9400c0000380115419081180318203040b00c6e0040ea0204030003558441510506446a0071007030700600011581104d0340b4591050b040c44450084400c0d502c46d40c2c0c0000360b02190b58001103080d0854014820a1703030079a43e19202428140181c098140050076840069940507251000092605c10700030034000c1c403103042144001c000b80148450500340c41c503909210080307a4505402000038014440915803001ca1402805002500071902100c80240c480205405c2c00242200b135641710003203500d103508081840d090300720010b0203a01c0f190f038419031072030024940396090b1110300c03080100351120300c000e0300401010030400c62944503200040030946e000390b040d03150503030340c6040400052085a0b01140c480e5482c2600c03040103140000a0115030046d9039070520302400385152840c084a04c0c40c041d44c41c0020108255000d40c0540b07080b254001e001241a581d424144044103003605501d44003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 648693651 1250 648692401 648692417
    0x506160602070b061f080f07050f070b06100c022407020603010b0307030c170f070212040902250b0414010b0909030703030b010f0f140d0905150109060b1801 69
    0xe800e500003065010f006502800e800c1c200441005010b030030744c80070000305074144d5440da06074030b80111059500c460f200c000301085664807001943c203445100c0308164103660009001c01080720312144680101d0701610325008402080100f038521510580c070103507020304c405c00c07001180ca8039205c07010008201160004d003070200d07540c08110250400c0c0c00c50801c20101008201c9050350600c0740401d09203a62516400703408111b44021140721004d015222016140343c00100d00c180200941101110110035403581d0740c0d507a15401009400014032040e520a860505020303c41404d812108115000708400d6104d440d40e41d01e001c20703801c100ca0710403415501c0c0d503010040386da940741c040307403045146c0b0000d55a43c00040c0380040c1143c200b441c15130706100144003c1e00f142c0303901130400180000d90742007000e0003070b1038601c4031002802842e02aa030828208403110003003090100c1e01462a00c00400410340f940d80712100c1006403801401505545542405025054035221425062100041c149505 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 648694901 1250 648693651 648693653
    0x2a160602042403180308090a020907171807061d0d03030f0e0a080327010507050c0708060c0f160b10051e03030307030b0307080f21030907050616 64
    0x8240d8000358414003503807074503294070640c03844142c0000414000314501003000b00028038041c410f403140180f0260401820f000001c103100300800c01050000d4004021000501d00408010040344032522011040075500700070910080c6040403036503200703d030301e0f0181c92900e0a040302120462201e510030400c09440601e40e0006488104210003010b00990b004100190541100c5040d00c004101c203000c0c0d5801441c0c2c4c1c80c003013840b160640707411084100940c41f1680c3e120b0a140303501c02001c215003107154605010b001c0c0c0c180e00301d001020302410581c01d5801d8184e80d02c1c00152a0101200c0d0f050001d2010800b03100501550401407490144031011100d502c603913138440da6004041202c0040c42e41510340750034491881c105210b00700c1912200c081d0f07100280200c01003074807400013410f904141501e0ba203140034982c0d800c3c00302001920280c021150300701a1021820354403120312000c01071458041d1812460b403402503007100e1051012800920250303180009100c0c0503441840c036080c21801c04c10b5550 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 648696151 1250 648694901 648694913
    0x706030b03101407090b130501080606070b09031810090b0d0207050610080705030102070c050f0411181309020d03120e071d060a030c180906020a05122a16 68
    0x4401900203460064504d0030010150540c40150000500302074140100c0c1601c40301841c2250070744100f0b1074000c41d0f5031a03078800f08006020740b04cac008100340719100412947e24400009032071205200c030030701809a01038034180501c10f2010134141001460b2000284600c2c03080e8001080100442180140342640c0c603169141041c00548404050303020b210020403032108208118400f91030228002c625041c4a65501c1003000a40d101e103601941e003110350302e14240e6a03170748107087c1201e0405450760b8410b03076250382403050710f00f070000360344200d80d041d0213040244540d20848100f00e5000e450000340b031001d520141c44000e80d0840e520741d002c1c0c0301c880c4a01d2400d07045c41004000c0c1071080300c00007070304080d0003030f503a507020300900b0940500c4035000c0c00c2000c034600320401e60440e0040c10720800d061000c02030440207020081c4001e0650344c00000d20406e10f560200050245c208056080802900c4049220f604200c0d54019100e1904101050b054020512001070140d07030b80b0410100c1d003158566941b0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 648697401 1250 648696151 648696161
    0x4060e100609051b03011409060d050d080a0608060c0421060e0f15100501050a032403121e0e280e0906040302030d0e1005090d02120c0706030b0310 65
    0xc542d0140d01d07207042c45860384615036510903490781d01500c981550b04007c09003280305540000c042c0316112510100d146526110742c64200720360414181c0d200c0901d9940064024113081d1743c50b5003807524042c00020345000110343c05001c0c1c0880300c0e50382c1c07405d842c24401a8007032214032030026103107207807218110018172148142c45c10b03c0c8030707040a00b290542d0a040e10b8106503540074100440c101000401c02803d410811050a807082400c2c035507114081c00c2c504030000c240010011303000c0205c984a11150308440008902120b10601c0004c000d500034510440707404003130080c110010b180113810105400d00594004d0210303180030746419040171000c2c20b01e480c4060307031a0681c020b401c0c01c400700380f0458039a8040541d001080c80014640d608166400950741e10541c940511129592000ea0342c569200340080002d2420f840401c1c04a82813401c09c072a2500e11007c40302c00035101d103602c141c0481030420296040c145114000d890740c0c614051081d00a080d0080034030351302d401522200004007030320b40b01d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 648698651 1250 648697401 648697409
    0x140112150504180c0501050f0d060828150203180106091b0206041101052b0605100e0117182a0d0803271e060a06030b04060e1006 57
    0x6003100c4145000d081c0801c0300c410400305002e2031580281c400106101c100200c0484001f0300e0100d94403152007030071840c0c500070719540c458124103003000000d6100000809018075040c241410704210b40e1401041500e04e14103d0080c5270005c00395840009004a5001d1340d0b122026075140a5143c8140d00f2042c21911590406d0701150340d1203444003a40071700300411285551b401e00080030315060940310b03540c181c610440b901e8100203002075080c064a0b00d00804002c1d280c00e103c80346401002d0341c1c440c00c02130302003405501d000c1c07505401e0b08611a882890302032090311040e103031400071481d00c40c071494106000403d55281d00c1201e46a076140e8500c100308602c608607100d4182e81c2400015620469074800360030090748600300c1c0483d01c8000c6100d10003240e800000855442e401020500d100103555403c08900c0420350044150220010401d000e00341d01410001d001d548003940d07140b020f10100c1e030031800f001c0d144140382d6000800244040e40480d02050501c0100c94400900700800400c0e6619a00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 648699901 1250 648698651 648698681
    0xe0d061b09140d0c120f0b040f061a0a060c0503070209010f09140601080c07060603021207090524060f27120129060f040803030912040f140112 63
    0x1c000c0003140c00758840d03010b1000b012198210100031548580c01ca2070850300800c041c080d0703100d11413000c02c000c6040c0040101e070b01240100c00d5103000d060200c0e9010280c1d5041d940726082c02c524160105001969800e003620007808001490304200d011660340e5001cac0012955440300b00309000160340e03000600c1c0d0003401c1808005e80428280720355038003a505900ea072018148811800d00809a8200d01c01c80d51141280c6800384c0c60340002e05000c000380031b23980e02c0039401070300800c1500200003012642205403a900f02050001da00e44442c0080044080652281e0400110140d00b9030342c80d10f54014400b00c2c240014441c04c00d5601001036020b0b81445000500703026a4042800c000d0400701c0341809200000306c0204460006d288800002040e50700d1441d84200142003802c51503681c9000ba25440c00880c40043e0700c403510b61510680c0d070f0340142ca042c0403a02c00c60076041c46800960003107406540d2910500748095240200410700140800080e03414801140b0300310610b00314a1088980305c0c0480c0c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 648701151 1250 648699901 648699917
    0x6090f02040519181a04050c0903010e070302100f02070b03070c0326040b0c04090207060506191505160206120601030c0518120f07030b16030203070e0d061b 69
    0x41000540044075200800f0303501500420064068070360100c40c9000b43ca42c10102c0c4c3c1c0d044092605010034542c00714181d20510745000d001d2034510070030203808110070940c0200036004c0201e0b07160f031783c600091000a600ca0284100c901065205002c01c0c5c0c81c4007590300451759808d44a10710601941c0048501e040000c0b0920840000c1c90703030103e480640c130104840303041c0c2c0981c15070503100b0031810001d01c06130502100d003010070082283c07041110010401c0110440d1108040c2c501000500001d8842c1c502c10303407020f40050341007a50611b03c0c6048030080360901410400204080e0f5003900803e41081150641003038010260700c807034005181c4440890018000d62178044005000c41d2030341c0a1080030480203025201c0e00d219214040000c02108460b60010304205d10b00301d0f4a00b02d6070920080310780c01500c900008110511880344e0041301c6034101d0000d50b11400c1011000c034041299040c0019400e007407060f89a0900e83c0c02c520105020b50b4020580725000070703490003840c0400b02d0000003c0c0c111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 648702401 1250 648701151 648701159
    0x180d050d03140f0411120a0b010821070b04110d080705070b0c070605160f0b1510080f06150318010e01230a0f1a12010b031903020106090f0204 63
    0x610500007090080603850b085030401c51030940107104020700090030000c0c6001c05400c80c1c2c0d240340000160a404e101100c03a58081407a15802c0c4002c2840742c202e40f0300c140c1c1c00c620f80158000c84204109614040e400e42480e41684038048101e0001c1d000390f90042081610f4800f41d1500483c50b444d041c003071220300740d940701d0f1450058038100207a841400e80180038891022585d6001c00c2040454400e03140c0a034032220008913003000f44d5010f40000382410748000c600c808001703060926620409985110080b00024441404000c041214400340002e040800203078580d09400c0c0c9154202d1000b901e07130300311604407004406a0740c0c42598a41300710901040303541d40322202409081514200311303009210007481d01c036010113804010141d1403000c200140010b61511500d6000003071a4403204070a00c4405607041da00c1c1c072059411072141e805261008405501d4180c1406100d180b600701074010500f4091582e56982a105040022400c5548884000548020500860300e003407800003070060b030b80c502d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 648703651 1250 648702401 648702407
    0x12140a090201170907090e0c10090e0a090b0a0908090d0506090d0c1221020f070309051c03030c0e06070c0e0603060c04050d03090914060a08071a180d050d 68
    0x1c15042952443c1e15882001024000401c0e12022101c4c00c1e240072805422416050f400c04507007110040c5c001c4035400c9054401c0e03074400078250480307503201c0c4910481c2d101e414418058845400d03000d00342103043c03c042244011180d009003081401010702c141814003000000b0808c50801e1029244c9074002d5080c4286014144055030103151f540c20a0079208007250f40c0c94006120b9400c40c0c900703000454158a02c034418429441e074232036014080c00c40d0b441e4030b500006105900000300c158006900400d003c5101e041130b01c071451000c20840c420980f0083c1c207540072405448074105605c20420503031003001503034441c203003d000c5031441000d401c05024184018044200b000400f0396101391720680600c000c0c0c1202d034040b902590310030350780a035005855080a950307003110b030350005100341e24201201b001c2c00404c05243d8060031003150043c110350b40d544101550b40d6414060030031076103200d892035900003450200030541c00301d20200c031041050f14200026000f030300e80881602c00740c00484091b00250741c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 648704901 1250 648703651 648703667
    0x610050f0307050f060703020c030307080d05131a070315090e0f030901050a0e031203040b0a0e01060b121008010603140c012f0f0d090303090b03070f12140a090201 72
    0x30080d00181103042c40d06002070744c01c1c2e04018400d8001c032400101c007024144240030a104c6d44001500301c0c0c0e5a0000381c07802c4490799004114880200f49000b020810040c88403000d1040103801071340800000034030f01800341c2d1241d800341140041c5a0756812035001602c501748418003c04e105140064000041e444050804080d482d0215558004204039002d44c1e8014040e140c540502c2e29003008100c0403000881e103804200c5030603200250307000c0204400c010411360341500c1511788610501c446039107014401d0a0320901e0199181c091001e00079592000414603070300f0303807000140c2801700400c1d40e185904c608541203904243c6040643c0f1412421400d420000462000e0b400e01c0c0c08030310300300039244084008a0301441e103a018513007003600400240c400c0101514000c0d5800640d84030003108100034005c004a80300403004100701d0000022100d0000c4142c1e8401c04203a12044440c400804c002c8810001072032800320001e80d5065580e040400070100d00f480b0700405600000c0c42c0f0b40038000508082 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 648706151 1250 648704901 648704929
    0xc180906060e031908070c05031207050c030706090b0a020c0d0f022b0605040516060f18030b0f0415090b0f0f06101202160f030801170d0e0a08061005 66
    0x207803100d00c00c030301a19034440c8000d180c1c5410540d41074a40c5200e00e0130184a807c3c0c1d511940e418419280c0f0702656003032000c010300e8070500c03d008036600350488009140d1078000703610031031020032007165003000074048445c0101004056881512a072404c002c00103443e484200406450103217036110380c5c07030860916206002c2e1109120700300405640c02c9580c500881c2108881c014501074481d404201005410406441ea8210380c0e1300c0e5408050b102c900050080401c600380000041324401014094200d2014200c1502c0e0007501d00340d07041c5e0340d00310a5101c025010b0011200300004250103c9042158411090450320455002c0d003281024a40e0200088025050401407000c40080c0089942d0346202031210380b125041c1442c0314440d0f140e10100a002d000d011000c486808290b06041200316081c40c0d07585803080d198050240d0700c4216000f940e09000701080d185900c00810182c1150044203e50280b81000709070b12081504c61030450b06065082d00c4105200e80743c3d003410300c0140b604d200020841 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 648707401 1250 648706151 648706153
    0x120a050f040807020118030209090c211c0c170409060f0602060708190c020a060c020106120311030409060b0c010b06160605090f0607080f0f04080304060c180906060e03 74
    0x5820540c44002c03952003070403402410b000388842454224250040c2e181d00454004203d43c140b807402c01c5c105a2582039174440c00c0e1041b4010b1803182442003c0b170309500c070000d2600c001000300404800080110588075003c400620660b072030b04800045102840c41208540e081c2840c0d06c0f2481c100005081c1d8250b80c00840b041c3c00c40080c140001e580c001400c0c0e40c40641454444610b4980c00070007000b249210000b04580390418140001c1c00740c000584c1100d29104d43e204021244410f8030482c202d541034000c5a203540300f034118120110348524513000305003141d0001d807454903a49241040803607205902c04107031540702040490084c3d0003071090446005042d01c0061a140c7c4056000002d04003104000303103a15540c0c00400c500bc201000120a580e4084d0304541090501403c0039000304801c50f030300d0245810000018561241701d0210b01e0040d5070001c145801c0d510b860b035408002d050340c08a00b104000c3c18000341c4000c21170194130003005103122000040c42500300384004200c8582400d103e806 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 648708651 1250 648707401 648707431
    0x18010c0509060327010f020a120902030c0909010f05180c0d12200a03020114010b070308161206030b0717010b0702150c060403180503010c171b120a05 66
    0x60388402c0200c9a11800d051107a40b42c000b401105000209242c0b141d030a001e43c600380b00340094802d42d500500000109454000100c0034030502d500503503541c813800030740640002046842c0d50900034940d81d040b115003000850408a040c0c2c0c00c40c1218400c83d1091422441d8192007114800c040c0410a6015015030302c4d08100c5219807240d05d034075070000d00404104102d101d010f001c2030f2007820402024200e0f04055690070030341428024040c085940300c4040020740d01d0f00004140070f0340c1085582c440c2e4507844424450f07549900f070350003651410203a50b090260501014121400f58814040550300c100300c1041c0500300030200501c40d42c03803120400d0000c1d0217000180891401402510a495812034000440c1c2c50f001d00400d180703024503151000b40744120f41c180020150441c80c01d0358200d000d0020b0074034240d55841050309851144d4420781c0482e13480c0350b10f00180340780c410300154044000740201c00801c00004c802c0c6010b41c410742446807800341003014443d0081701c90041e5604411004a4806 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 648709901 1250 648708651 648708667
    0x1221050601090b16120905091602120c071404061502060f1509060d020102030c030d06061209020d1b0f0909020406060c05031b100c230301141e0918010c05 68
    0xd0014040c1d04c050700565110081c05480c40c460640070014010241048440c1e0030008a1450036440b40720740c440260041c001400460181801682e5100d4071b00300062a099281c0201c10300701e10148502c05800076207940b130220300350103003400300c405400079580105118500b240600e00841c2001d45800000302e5150041060395940d030051a03082501251842131280e46840141e14620410b01c041140b4040402c0d14062000c40e940030104503082502d0385140b0002e0340800703408403414000d00940c40b030010030700710340440d000e0b64410868038800c0070801405504d030408841c019a40382d01502c4415102c50a500840c24603006841c020034480c00e000f02d84440581c0d856817240602440403514000e04c501d040f401d80700800c000307407121480c00070801c4085030042c4001c20907580c40340c4491003c007115110417444030300c542c1164103c0301007900c44060001054100421344413191450340c124011814602c281d95a400d14583c01560b4460f001d00488401d03201c81c5080d9a80c65008009000080c06694 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 648711151 1250 648709901 648709927
    0x30605150904020c032a0606010c030f1805040509030a180b030c070c0f060503011502061006030c03020403020603270102070209040f1a01030804061d030304031221050601090b 77
    0xa6000e00d4216005038036011014007440c59405000e008455198200380e030781b0305100703d1840005171400d801c0c090314496582c2000540e00c0351001034000b0b00051440305200f64803489401c0a0f4000403400c8031a50149a0352400541074030340507a04001a50000104035064540100350ba0a40701d0102c59822042d500e0b20304990510f0000500d10fa1240380000749400410140c1c0012501816001c0d0b2240c811686400d802001604240078075000e10f11410054058603000140c59446141c8221b1441d07042410860b0841c040c0aa4030140001c1c55000d0201000603510f0b10043c40c03058901038410400107000122401040c480e6186e43e15081c2d104205020241c0c5420402d140e201d900450010400c410354030704910403c4054010054a075003030000401002039480050045490303560311104801060781d98101501201c3e180c29a266104001c10400200051080b89104400e81010701c00701803400d490b80000103c040650004540d01d03c20030502d90f81041c500e0015000c1c0e00c40703e508022406a02e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 648712401 1250 648711151 648711157
    0xf03150306110d020f09011215180905010501080a02011b031b0c0819050606041404060e011113091521110d0f020a050303210a0b120d03060515 63
    0x75050503261506034020b005460b0440d80328015200d001c542d200980c1c0c28072012900302c2a03109000803520349211380340300341c00e02420380b90680312a0304c214100d10344404081c003d02155580c0c0034043c1c61b0910900070840070b204aa0080c450003020b4501c0a1862000400788210300131468048515261040d000c01e0344500145041076405070004040401414076080600282c0e10820340c034070035031101080b1311030040c0c8ca610010b03208408580160700d6101c100810303108001c003044000f641c980001008030b03c0681004000c02c909400008100025100203d0070794040502c0c501814101c1c00108014112071240a009800403840c814556081014115030807031040d070511380c4400300e02000d0092142c2030b2600450070074002d240407199455407606444000d42e01006910a20904400003803605005c0304071060f000d2841011190f1415101d5403030440c90018000450443e17490b0005080b41d1030b002281c821045544c4000c1c0826881c94400809840c0e00307800550107820320506c01c0111109101c25 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 648713651 1250 648712401 648712403
    0x21009020102011503120306080c0d110d021f0206090105010f030813091817091023040b181912061e05010f090203161b02030d080105010f031503 64
    0x49006841400101e000d805000742d80d40da000c0c02e944001040003d0600c0d00d5005869685061280f2940c4130321041e11400d8121505070032642c802c06402c00910000310394000300f00d0080440e6016505e40d000f1982c00984a03032070000740f2070f0f8810140d040a0301009811b41c441841c6009104941c10040030740308040e540e100060489002003002000c1e0100e00c050f400140c20244020042c4500c52000e0040c002d03e04030080d58441101400082c95615030b404484c0650b5000c0d00004900344082000c607052102c0e40c18000342c001c80e0282d0302c0c072200b001400400003805e00030031541d250040c2041202d425018144c00910400c44002c12030751a002026a2104030b580750521018104201c0c103040000d8603070f803d80303800e0f20807040c460f03490100003a51085041e2180440744a0300305403102081402c911098551400c030b1001c02c0da0520f012885100c0740400585280c2103c0985034056000c2072030103121401c510045035001c0014001035070b04c030144503401c03007403490705005215000303201c50425107803408 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 648714901 1250 648713651 648713683
    0x60714090607120503060a050109031101050318060c181002120a03020d0509071505030c041a07140601090e03130e060607120f0906050309100506040f020a09030203150702 75
    0x11558440c0e5038501c1500d1003a504412544214050740c8801401039000b240c1c1c55116102219002c192544150042c07010b80f58071050b48441250380c0801034445410051001d40c4010540d00e0030120800b06203c4940981804483c8517282d50100c3d10211111034103410086c06003101c40000748041354001030395598070108582c00e0742c1d0b07404820740c02c501074030801c2c290029441c203000501014080020381e83d41158030310340350600c0c040b4034200115007501c000d5541d183c07000d00c14002400030b00024000015100050341d5018078003007049e030b10400381603800300b610340c0550414401008a41540e0240314861140700300518034001844c00e6181041e201406042003100748480060580d803660011075040f550403144030072900358143c400403e00700011800c0800102d81c500c001801c5802743d07060301d001c0d0000c400030b007004002188120b0000c0100400b1144d000c2c2d241c020030300f0190f403542300800c0c108141c1c0d47e901e10300c00e0442c01030524040b00ba2a20203c54115001000306243d8041160401850406 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 648716151 1250 648714901 648714907
    0x2060f06010909090b0f0f06060f0c150a0509060a022a0f12071101020723130e0102090405010509060603240907031407020a080a0e01230c0f060714 65
    0x500120341d001000e401500e242444c0406090030701203210411440303089000a000d803550380d200e100b0301e540d50043e10200d03000a01400584424a801c502400070740745240219a00c0d900d80030f51901e604c41094640380c4981e6641ca06014001c00203104483e80310442100961520508074022441400103020343d003000e0f0100d02104150305028400e00c000058003000703c4095115080124003150300079802140c88858042100c034555002248040c2201c015003042d103041c014100316800da0310b642c2000e007a03200041d404031040e11410f610800c03045401040c0016203402040b01480120340040e04680e00c1100c1890420146544403412031f98440c0307268403504101201d00030b11592001500100517809440d940070050b85aa05d0f9110442d21508031009040a0b01c50400690715030980300b6010303048010400c04c0150142c003818030003c4c084018503140040c503140c0030440a182910a2410080c0c2c0f0000035840700980040101203c0c0d041003201034a01802e2504010f040c030401202003105540c408 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 648717401 1250 648716151 648716161
    0x10b041e0902040608100b0a0602060609180f070609060306120f260a050306010e060a020d050c160b04080124030b06130c0f090b070812040206040b07051501120302060f 74
    0x154101c400102101801c42d4010580000546c2c050314030440100e0091100d1080050078500c0052800c0c01410041d00600d4203071079002e080c08041d01d810011399030f10b1041d590850f80085040007003000508183e40d410178401d0038148010240e0313040fa0300c000020743c9944900780100d5480c0501c01c03021a800b54800314051007140c100000c58503020072103240d941d804241582c1d002c3e00500118031804090361140b082141301130401030709000e01604080142c0c0040c0c0c0c00401d4900a000902e159040319084a01e2110701c111074180d41803054000810f11403020504204030042402010301c03175120483e0703100300c01d25410098001d5529510000d040e110010b000705a280e02c1c0c07402117690b00440c584051101c4070000002508500c1000000d50001d441e05400090400c0094240c80305280c0c031604132441c003d01c90031a4910320801400990b4070100400c030004811101400070000c942c4298080c200c00c5000208950012405070f001c01c0e036403401c4403410000254045415944040500310a00560b221 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 648718651 1250 648717401 648717409
    0x2306091203220c03060b130203090c090601031b030e010e0102041d0c0f070f11061804090507050909060718050901091505221104060804150f1b02010b041e0902 70
    0x8280903120f40c143d12400b005001c00394002c424000002d41d001038020301900803400403848201c54000003508460091040d5181c68620f083e0024814980451001d0105407034500020790300807248040396a41c100f4494012003030040401004102c0d0085041c1807500e410b136501d00444c00d903003e002c990510b000858000b101e02c1640c00f01c121748220280c0361801031411058110380044159221603165008204501c1c1c20001c032030514007100710303040864141d030041c00060315101c4ca003203130640111203011030580c0b40e4031070440c400c4484d04000d00c03003418503035806014492803c07112003101c1e0742000e0500030b50f04c0300d5030f00c01c1c112180c0090010b0544010140d0001b0038903260400c0b64000309003154411101110244000e40305e098400070004d4a10204121055200b41d20505001c14010000038010505000c8200c43d0fa4681000c04100d0590a2a40e2411195450783d480d210700c2012004400e007c2d4244600c80d035103602610b081018080319603400c40d43c00341400003201c21644440a040454603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 648719901 1250 648718651 648718711
    0x70203091e06041e090f240b0d02090a03060e0a0b07050301050a1a0d0908030a0c0c170a020a08030a090b07030504170f041a090f1c02010c030c2306091203 68
    0x170401c1400c02c800e4060100d02c1d03020307144020348000b001c500000b80d071704402c0b20326042608440200c0003840ca00070400a034040a50000542d07294000c408840001c0451030364000c10010b03185800c0505001c0f4003d00d44410483c0c0c025000108224090005000f00e071190113100d020f40d14400d121040e0080752481030b640a00c2105501200746003040240010410320308007840c02003000403414800c052981c03108407501c030b00140c400f03841c51202c104004800c824510092080d2801d91058500401325a1585190f652068444140083c4e0703440d078000c10300801d03440403a0040420314090046003060740340d418542e17000403410181c400c800200c41c0c1e44c20402d501146c0c01440000d81140c01c08042d01103950313258000702d0602d40900002c4a00c01718900d80b1b005104a0301c440103200030b051000c141c00445041129500403001c0c88122080301e03000c00d500c045000c21710b8003c82c14941d4600f503408102c0341003030070240542e00e1a13481f4000340b01a03c0701400903240d01601800380607196010400c0d4024070a5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 648721151 1250 648719901 648719909
    0x9060a27060905070501020a08071728090b0306091506190e0a0605071511120114030f011a090a020f0c0703061518051905070203091e06041e 62
    0x8829412000308001c4150041180e0500800c181d6019981d00c0780107a03141c84200c0401005c1680400c2484d001031000b0050040e030f00441d800403420089100c006042201040d5402150800406048030130180e220403684094851080c0003411410240b0102d80440400307000941810b400307508000300c0ba02c82c03900740d6041150444401885c025450030181c669020912072a01030203e281012880c02d0140d801ca41580e5070203000142035031041d90580c002001c41c0406149003210400c12610840d40c1644014040c1140c1c0c9400e100d40000c00f42003524108070802c3d0f420035030741840042e008001c40d850810805c17000907203031031000d81e5031581920002c0c458824410340710707500440c03192010140003c0840980c0c0c0700350410072803980c100300389d858901c00c14440c07400d48460640c80c420310702220340c010540021044bc1d820703249200038401c13941031700c6049a1080069001240e402207a01c1c010403030031100340f52074a0a242c00c02019000c00d2a910850148020f19460b03010241514104500d881c0024 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 648722401 1250 648721151 648721211
    0x30b030102191409100f0908010f3201121403032a120c1c05091605040501080303070503090a050703120f0e0307051908030f120f09060a 60
    0x18602510030000c0d0202d2070305114000802e00d07808038500300000e008403410164014004081000d00d00002c503000111041840b08110480a00003003680c6c003405920541601304001044850450300741d00c00e074216945603010b018410482ca0f003002c685c40c6091070f0558201001ca80b480b0805c0b410304084224180a80003120b02c00041000b0855010f500c00074600c60103020f00048280742d030040c50b145805004c0b4040c4058a150020402000c2e0343c40081c16001014031010805101c040c3e1070700d080302e20403600544181c11a4114400d21503100f810000544003c450820581d4100b10f041e90b500d000046c00841445800008105143c004001c0422203503400350860f40c030240c4900d040340804009000c89030120f04841484061140140b075031841000380075000f0410b03a4585010402824004401e6016220072900003145005080c8020501c414030001c1d16030351928601864000d07030b4402130041d1340b15400340c4280101e001d804039545400044112020500125103845a810700001942d00d10728 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 648723651 1250 648722401 648722407
    0xc0906030a090203011b0f2d0f0f030911210f010605090c0309190204060b0c0303040219030302060a0e030f040e0f071817011d16050a06050910030b030102 68
    0x116211500119030461081d00240b140886043c180206140070072154004030780660003060819202d80d810340710342a0103c200c84100380c235501c1d410303040440d0003880c1400500c1c0c00b258034180681002e421440b18200b440d08004640e0035807511035000d804079040d18840d446a090400749140050365440c102c60300d50b0266458405e208103114001c00c0e0758418203000b6501ca4000071480c601e01c00c03c0d2482780c2d0f904c801400c603440c2d40e0701e81a840c11542003004c80c0d0065880202140c040c08220282c66441e8580700103559908043c0104402004071100d1414030658409041c00000d40c01b16030250000104000802c14908410409042d40104010000440c00c0420001150240900040c0c016a5844140c24031516540c00484020789000d42190301c003010a80304100e007140b00c41408035119040b00000801161120340000846841c1802e014035900841203203411166400c500c500401d000c584980c3c88610300180a4010300074420703558400d112003d0890307145402a0400540202c0040c02199 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 648724901 1250 648723651 648723661
    0x20a02030c01150b030a0b12011b0e06071e14010c0924020319030623032509090615091a030604151d060a05040b0906100501080c090603 60
    0x903480e000880803841960800c2c0c640c107884802c038040303035007610f003981040c900c2c0d0f6a80d40d40c0350f0b01610174120400d411415404070025290300c00e1103800301e81d000c00001610ba00441d41001040750b40800e01c25032040c04204403580000b050031614040800300c3e0240f9400c10b2a4904007684000b50605003010b0079420049090502036020032071200744c0d69001001c0303d03202c00c5c0d4100208103100303004420703000d07030710406c450307030305190b03426001c100c0c50010340340115640382c40301c09541d45414590045400c0c40010f00540e0303402e1a06000c0164a081d60200415035a4218450702c2210007e51040c085801c1e036581c4840b040c04540d400030240d00703a072409418916641c406c0408001c000b40911005400104203241c030892901207001c600454121544491002c4100c0b0610010004c03601030700c80764180300c0d02207011001c040c0081440351020550014107464903041003045020300403c0a1080e82250003007146820145026806481083c0b07400c44240e51040d45a031600e100b00c1418070760040e40802006 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 648726151 1250 648724901 648724903
    0x50f0f090f0106030503300103110a080a060204080d050a020601030f15051302030d03020c0303060603132a05040921120603080408010e0c090a0e0106120b0708090c030d1b0501020a02 80
    0xd84807801202c124801203c8001f01d20700d01c60700d141c061802c12004801000803981f421514500c0d00b10040420319044d80d6503090300d16094215070201c589980201e0200040c00040c043c1c200c3c040e25505041c2e00d000c100010003911100140001022048100720f410107111010b00b881c8105190703200c003000f0034101075000e14013171501640120710a1081118020502c3e210b8000c2e20560804c0200035400c5444000030008140c10090000c4100003080c4c1e00740d004140308914041000c00c1c007058103007407010440103521824045800c1035000c0c1e410000144000740003001515030b08010318040d0700c01411701071003c0303070314180b00403480148908080c000310610003164010000c0321043d00c0200040800c80c46020349840f405410150b22505c501c001404400301a00710a44c0e2100c21800050324036291082018a10190301040c0d03213044090301008140d40d08003402c160814054402007150b480d89030002a0343d208031614010401c4800304441d1881c844020140701096407000080d9118141e5071002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 648727401 1250 648726151 648726157
    0x311040312031512230c040e010219050714011e09020103150810050109050f0408160204050a1d06090c1e092505090102120a0512010f050112050f0f090f0106030503 72
    0xc0d25444402d1100102c1d0061449086034000300d11703000303090b0300a107040c1004000c06402030300b08425502005880c10744415120303200c1c003100304d50301c80944a9003d420462100401103012130940d030b140a6000540403c0c0c0110070320070703a40445c0080380381c00551004070060a03002c04440a0070304403600200c0e811b08007203500708130f8060a0f10108241e070ba0b24100c01c0143c0b907040ea001d445c010b02c0c1e0300205010601410040510091161800e00810495404502160b20807208210074540c0c842c82a440c0c407400c444244172802224006187e18207011000d00d40750b9010002161245585c13181d2903090010b042c02d031415400c0f004101d08070354500400a201e0058040750186030318000c041e0000d03e41d50203034056949450040c4d000b80047d15005441d10915844610f00409000c010701c88207040784584918107018003c030f400d403002458034043c0050540d2240d21160740441c1d080004100aa40996105d242c0c071108444441c45181c440d0030b00d0904111820400e80c1c0a0350a00d800402809400070003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 648728651 1250 648727401 648727403
    0x2130b180114010804350d02030106030c0302130512070305030d0203040c0f2111090a0c020105010b1e1305060a0201060e0c09030a060e0709020414030105070311040312031512 77
    0x78804030035070160044131002e80c21500106441046018002c2d90b01e0718807549056219130207140310610350700d000c029451b9000281c50500413600040140503103a0315000d000700c2c4003180e0074290300701886c040c002d1640b11603600610307000b00a00c2c5404c4452060030811a0001c60300503055954070003001c02c0d2030f0003035401101d060350b107001c40d810001142815503030307101c00702c0d400c011100f150054000081c0c18840901c05041d210075444124035585540e5900405025070100c034000601c070a80040040c0c02d440c41640002c40002c0b00b401142407100043d0003a2101c0c800d6030307045c0b0742e0303174032503859204070520aa40040c1c0e0000001306407520513903015885039040c1d0707031107166a44441d0344a900740d4030144a1150495010341010019000180d9540c128180d0047c8680a85a43c5a1511046402c98016070701012603c841440c01100c2c60130301b0f220701c40e0821460314040c443d81134030321a2142981310b01d100c01064440768403482c070b00f410f21a030f01c00a02890041c038010a11940d03a2050541c0c120319041c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 648729901 1250 648728651 648728669
    0x2c06060f0705071e08060406020c101a0a09020901090512010e07030c080105010e060609100903021f09080303011a0a0c0812150108040b070c080415112802130b1801 72
    0x310074051180c131203900e04403400900140900c0c0d503180d541c3d4010b03402c1030100705814407400e07150803076880c0c06000e58114900282d101c01c600c00b01c80b0003041031022107036201d00c000920410003030006076400a007a41c20750700309aa102c0c000c1c034082038a01d4010500009111054094040d0200c100032160210004032081c1e40c00a11099884075140c0c0203020040c1c0e6559070010b005c0200c150181802c400000f200701d414207002c41960760301c0d00070800554104108904403003240611000c000d8001c007040c4003503c8024001e40c1198107240512181c0d071010328910f1074250000c6000010b60f80b082003100c0d201ea074000d48007525000a503241100e00030b000c1d035130355003412140c865003c02541724900c1548100d42081c420740d540c0c0c86204d03042e0750f48100c002e02660449000c10000c601800c41e5205040d81d004c0d43d41c5c030f0010f62420107510318200320900d4801c80c3d03400030b60041c402001921000758404190102c03810214140542011001401c140340700d03542040d510f1104803040103074454000c1c12100c070300ca = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 648731151 1250 648729901 648729929
    0xb101b150213140609010c1b06020d020d1110020f0d020703031e02030403170a0f020f12100b0a1803050f07140406031a041b09152c06060f070507 64
    0x100b101c4090381c005a0f480e0000d605101d141d98562007400300048040c000c00805081c45210851004a16880d41240000d41c0c40503e4801c015981000a101034034114a00005440b1040f213001c2d0b16440300844010084fd000b19407890700d203103540700f01c500001130f1550441d07840b4001e281c083c02402c4074120003108611008120b48920707510f802105e1103140c4c1070380c07000e005000080c075150302008003420400107142d5030602090240795910040508030007581001c6d0312466602c0144d6030703d0000800007116000da6007401c001a0b079890050300c08100c014100341c211000128000e00b6101100d44c0003800a10503803040101010700460807905480003001c078501e0603805501840240c89045c800281035070f890f42d40c2e140001d6900f088498109114002d413203510440c0f5160440e811285422025109035035228204010280500717202c002c040100c07190002140c1d50448400b8004a5000d82c95120080d0002904d540c1c4c0d100300300c91005c902402043c0d1100054103106a8400860151192120110f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 648732401 1250 648731151 648731159
    0x604050c040503061305010b0312031b070305030a090201020c10051e04061b050102040306050f090c0f06040501110c040c020309120c0319080909190c030b101b150213 73
    0x128101d40c2550009001000e03281c803540e014210300c80300c59106488955031010b101d1856602801440410112224000d807a03003480e6443c0503911110911340e10620b03404001e01c0300069040001d4a038041c920000c0001c1a603840c0c00142c0c00c04a1801c400d99002c0180c030f0500041c81e40090161a5190111590203030305424148003080500c105d020321070100360910640c00b0040114028060410310440015003010780e00e541e40c405554069072520780608245080100d0050304204490350f520f811035800861051070400700c0d4542c41580103080c1046040c0301c2003a1200b0040029113825238018008001090101d28000e4407600001c5c1709521070030518079041c25003900025588540c0074002c02800450000082182480341c00741c00841c0d02c0352081c411604070b6034030300d00740ca4401d8139028690314086243d0840c0804454801e4030200c28986071008050303d90700ea07441615001207050810f654841c185c0c03942c240765480c00000c01011100180d0000030310314940d4010340741200d41b0520802995480e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 648733651 1250 648732401 648732421
    0x40f02070312111b1011040303170601120b03240a1d1b0307080d05030708130f120c02091503060c030f06100908190201110102070b060d0c0f0e060405 66
    0x1c0c0e60b02c1d07000415020303c0758445030b038100c131a0700904201e03c03000c48019030b5003d00b80c1c80540b10b200e410407601950104080041c5074000d40b580d083c1c3d1038205000c039200d00e482000a42100440d04c80040d405030380d040c101c0c4051710304100001072481d805c0103003646103580041455070800301b00c0c0c400c4103003820a003440000d080d416a001440b0031006018080885020050021a000c059085541480f902d20b00060a0905101c10b0300104220b6840c2aa28030b442e94028104d880042e041c00c20a0403400d8619011031102c2508019071980103100042c0315070401e50442d4810201440a03502264a0041c420714134103a140c030038180c0c80300b50145c8500341e0310021411080e002c100c6804512030703040e00011b00e840c07414038134104481909050016249403070f006a0b900c0e0008007034900b036010301c1c001a040c3c103640e04120500b440d0421800203510706076151f66072100000000d02814050504900140d080102c10580309019008544585003010303aa1a10140054003c2d100e09004a1a24000c1620500d0b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 648734901 1250 648733651 648733661
    0xb030a05010311100c020622060c05060705041409040203100213090b06073302040806070e031b04090c03053a0903240e031806091008040f02040f02070312 68
    0x44e4644540c4c80740c060a400340850f6030312040b00c00c6080c2001100b1590400b10b00c2406a010b0003955272030415014083ca4140d10700340000d02200240301081c441000003440411310010340c00c6003621055001c0d155480420700d07005815420244070350000c54400101c913600f010490444491540c1030002605113400c1c4072031842603101c05440400c0c141c02032881419500410155615580b484160711205c81e80e40710101d07001500107403881e070402d100b0301c01c07020783c4018604016081100904205d8030741405e1580410a1200e46038051500c0c0c1010b2020b00c0000030014008540220984020529091202400c440d4002e0801c1001d0100055a184d4644110440150700c40030303100c0b003010340c0c15a01c901c2c028500c121880c120181c02c4452040450305030780211910b43c1120001075884203942c1140c91031406076001c0c0700b80141d90901018000c0c0da91412001c14540003800c0140303040d219400c0040d00300c0301e203401c0a0340040c2001c490b480034184540c010500c0328043e9650000d00b09409410380182e030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 648736151 1250 648734901 648734929
    0xd150510091a07020d0807060b090106051c180b1009110a0509030a020a08010c02190510180f050307060501050301140105090907050a0305071509080619060b030a05010311 75
    0x4008000512070400303103a890510100c2c09100b140d05100c290f500007080360032107031001c4451180215652040144900034270029000c00c9403441e4466042480042c11400b40c2e4042c80c0280c5040fa9164450840c240d201c4c44000e1014502440c94030440d0401c054549420b035135100010500c4000000e000c5042d00c64010348420006d51382c0e181c0140350f1811103843e04554580fa60602900c0054170040e950668904010007800002003041a81020040e00b803c06c0304103684410350803a00000000f4801141d006c1c204a07580c1030001e0040c1030002d01400020700224001e080c070360f40d076503a06d043c2710300003018040c007521a24041c8075580c1c9038011b15098400b4558084072450f0030070010300180c940040501d9201d05421f00300d406c13041d50b07003000541d012420b5200f030b29250001c00c002e1085440c01c3c000c2c898009054288030781014a0003542c180d403400c00511101003103003400b5507040303c1038080e0400c40041480e03100542e1a0f04004840300001c04080c8001ca1707040d6215441000d49040c006500000c036 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 648737401 1250 648736151 648736157
    0x1b07080615010f1d0f121506030102120115022514010f020d030b010509040204060309050105060609090408070c09020a030b01120b0604030b1506040303021f0b2808030d150510 77
    0x514120001001e60704040c1c10000d030700010042d4101c246403584450081401b9480e002007110380c44096200141650181c03800d40a640104130b41072148003c4d0540b2070440d40d003200d008020b090340030812410040780310303020300c00c2c1921502c95140c1450340c00b8031582680c100d04074100780000100010b540070081000c604001d80c01002003814101c0c02940300320900c00040c14400e1800b450800060b080b03901640141020075600d82101092010034445c0a40c400e03410303180d40b1715080c1d180300020030350100103000805505000401008002000403800c00401400704250b45820404e82d01030050710260f1440c60000d0426005030712802014014842d000c2c101030500b600e01405c4d515100010400101454410000c0a650902c03503280c6a0040c401503000b90f02030908070000b40c1031001148964000c8082450400503880b00035502d00a94020320814030300c080410000442c46c4450300b510a9001c0504e43c000030812810500e8036030000205921800308246405c0d468004101d103140049280f8400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 648738651 1250 648737401 648737417
    0xf06140708010b0d0b0604090e1005270a0507090605010216030809040c0314070c03090b130603021809090f072108090a09021303060c1d04021b07080615010f 69
    0x90401d83d03000030090760071072039408182c41e81c0034804140103900c245d001c40d050981e80c003400d140300e49040c0a80c0706c0d241b80507001030066003046080800c1d5603260038413000e048420b00d15010b6802104208880615074880d042c0c40c14280c3d55002c1da402007074144507250150107603602140c00001c0580008040d25030010400b810880a40e0900005103420003014090654801030401c0c03003103d05112611404c1c2507596140550300034070b40180022401c0d40011030320365080c4518040c11290040100a07035a603480c0068580e602c0032101350140c080eaa4034507806c8a003d105220345080d010a1042d21000d00f00d0494200720795850340d40ca50a0b4101d8200110b21a04041c0400000c5203900100001200146803801040d1200c1003c0700301c2c0c0c4110140b5841070542c1a04108220f0607000d49a020452420b10340a20b828203511454940d20144200b8881c0f580001d10803040190345200b4007c0d00069401c440180b601e444400760b8a00041d501141f1010780c40d1340341d4910750b10034074010503440707030903035921131 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 648739901 1250 648738651 648738659
    0x1909080d14040209150a090614011e050306040203040c0905040528020906091b030a05041b030803070c140f0f0c0f130507020c040e0d0801080111072d0f0614070801 72
    0x1181010f05c15641c803c10b0400300141180603400b4071006048003240d81007000e03201030005002c03138080021421000078500c100000494008090301d034040820345000d80d5990350341c0b92002050901d0340068804ea0b1400017400280800042c00002c400c0c41c201e1900d840031380b56405a58052000b0300020340c400c00400001c2d030310781030141541d41c0140040710450703407100010805c1005a04100c4005403030315550400c200510001c54082d007000d440b0340e03042010183c19030301e03054a240300040c00c0c10b01b40480d4043c804200050440c0e002e80c0103111605541425a00012540d22030b400d044860f8090711882804001e18074107000300240c0460010004d58a10a407131000c20003824004040c0b50941c01403403504041c40d200c50184003500290900a04480715991317001811011042c0c000c060f680e0f14143d884854251448104d0381d1240d0040181c81828020658850414514641040303a120543d102c200412000482d25180c683c07040605026003071011090564210007210301000182810f40100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 648741007 1106 648739901 648739921
    0x150c0813110f1c1a0f0f1302040501081501090b01020309100324051212040501030b041122060525050a14071505070503121909080d14040209 62
    0x8050030f0000711413003a240004e1803c0358046c0c0600124110400324001030760129402030082c4203035a11002c0e000d444d81d0001c82100d02124243c4008180c20080d40105000380724107074011410b107800300003004024400c0ca1030b04002d05645201ca84060310100440342c010301656950900e81c10b14020510401e410746482c2918640c0114402c0300e180c002e80070444040f180c0910300403845220010004000301900c0d81c03056800c5100142034104a02c20107a983c4441c246400b940b425541d880710f05555a01c00d14404102c0b28a104298001800101d074030210641d0081d021035801840310394403155910300f141c40712170299100d29030130000140d01900503188000107182c0a0709040141e41e4140da41c0c01071000c040043d10002c0c0001c4e281c0c1d04840d0305203440b44081c2800b400388001034103201140794001c02c0d08544850a021501c40101d0b03e629416000b01e502901e00740e025074036020b0803 = true := by decide +kernel

theorem cover : BRFrame.Cov 648561151 648741007 := by
  have h0 := BRFrame.cov_init 648561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 648561151 ≤ n) (h2 : n < 648741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
