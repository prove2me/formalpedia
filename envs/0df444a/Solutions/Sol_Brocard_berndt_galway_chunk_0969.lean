-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0969
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:34:00.474992+00:00
-- url     : https://prove2.me/submissions/37b500b6-a1c9-4a91-bc20-e7d2c4ca6320

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 174100719 ≤ n < 174280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 174101969 1250 174100719 174100747
    0xe010608070c0f02041d010504060b1507110d080415030e12160b100b030103050c010f030b06090910080102040305100b040b0913031704050606041104120303020d02130b 74
    0x60021000c119041c2d802d000030416080c00f83c1015a07044900180c038407904031108800100792141c03034406503c2c01d4100002c0c0002c1c1d400005180c5000c03240c550502840001c41405070180c014080d124082c00e08000701241000507074504030600072501242865501c5008032074101c1710800d4500026140c025298440c402003202c0c46542c4407003049641000e000c460308925410b00c10308082c0c80c234840040800d0001a90300449c4002e007104038040c03544d035a1a410110742d54005400850700040707040b11420000c910922814180100041456140121940070445007040182040301c2c203001005001030f0440b0301744024401584608094000360690043c41e0089500f0600950300950802660804564034a50b11652207092000c0012140030681002c03a88144c5084504105074555020f0005004c00010000c0c0f10701c0040b01d042c8040e0500c1c08644000f030080344560422040c180303010000003406500604a2403650400060070182072030620240758201c0d41c00710600341c3c000100420300b1654 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 174103219 1250 174101969 174101971
    0x13020a05010809150402040219090311030a030e06180a1d010b0a1b080904020403080405120a030f0e0f1c0b09010510030201030209040f0905070602190206121f0e010608 74
    0x300b4204080300d03180c030480e102c0d1a00450300d984183c036010b01c00050f04651380d40c0d0642d1034010007001c10a0002907498000382c040408c902044c0c03460f84403e11958440d160000d041c0307552a42c9507413840e045003160400d01100b9042007681894580b9200411030490700e410401c40001c142d1a100380354010814640c42480d508185c1040d039031004200900300d401038101c007140101200e00a4540c0146401d41400821409091403580d071183c00068008248030038070300600103a8104880d0700c0210400c48513000d40d00c2c00703405001004228046803100166008580d1040240030107040b03804070488001c00a054642c0b9504086080d00c541414078003848404440141d210314104000c0009003000c41440c04103200030321009040503000900102c40c5c0e2200d800c0541840a215800e10215a1500c2c041e922403816002d804010311461007020b0b01e0907640c4204184d5240c01500f81443c0003400c550015440b880204028500c000e00108602518501c0e40706a00421201212018a505065009081480c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 174104469 1250 174103219 174103229
    0x7050d050307120509030316020a020d02062a01021c092f03060a1d060c0403061e02032e050a0b03040606050603070507050706080106170601030b0a03030306090b01050c0607030b041413020a 83
    0xc021400d403030060b203640cc3d00141e80d64040315510384076800c203000c1002800d0784000c00b0a04e90507400000002c2c82c07054001d00210b03000c00b50710031503084003e6145c20840340220000f4000c0b44503c01d40606001407140c0c280c4038540500c0d140140e10300303803c000c24a814000da40405c0d9440d6110103594550916201d0702001c1c003c240701030091401d20504204150040d400048c1c005a51880c0400c00e5114424104130310713402685066481e450440c2d0520540b07015a8101c02c80141ca5000c804c10000c1c1400005068400c000c0203440c04509181c000d840325000104203e5000e55114030100d9140c0e0341e040618070039500707a030720140d84071190f103072141c1003c42c40d03031019062000c030000510a00b9081102c1c0c181044a110b02c00c503041c0d542c0001240903109221119400c4200b0080c040185941904140c041c7c401c4420140b103080181c40045409100303403002c6a0b015007129020407000d03842500942080440140080340c84080110341080903407080e02c00d80307c2e490755801d400d01141045030407040101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 174105719 1250 174104469 174104473
    0xd032f03150d0312051009110306030f0106060917010212040b01140108130305070c0b1b060903090109050909010b0a0e2e053006071407050d05030712050903031602 72
    0x200c03030741d8060310300d20550030140041912800001c00c4010709003d644000d014002048c000ca14802a003001c3c2c07644280c1e06940280104032a2803c8628140078600441e2060380e141802185000c0b2202848408400c4070380d240d54081040c0b0443c80d00e0100f0f25402a40900b642595030751600101c4080c144010340e085040c0524007040001100060039410316154050800f6990703a40d00b850318075030b0890700380c10011030104085420500031a604807075500356615202211040e0312505181e41d500c2c01003008084c00030342404018856410701d90702183d0402804000864034a03980400a5142c05c4150042a126418a020031480d030400303c10b125000710402c550140304a88030b03140d400400c041030241d9402070b007000740b04081140400d00da114440d0300d0a805007a0034a00c1c000744540f071b07510994140700000c10341a0031401f0032a041045918a80c0d00100804c41700780702c20390a0305c0c2a08024601c03018020a6041e9002d084840e000d820721511039079000d1962407400c82c0c2d2040202e84600c0c0008115 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 174106969 1250 174105719 174105739
    0x115060e0a060e0f06070222050a06141003021c0f0b01030c05070201090308031810090204060503030a050d0b011407060c3504020d0507171507020d032f0315 69
    0x50704d648104a0003c1d0003510444d81e141c1890020072a50748001003e5004c000d4003020712000e8080c1c90303021030301071505a031050117030ba5980c000c00a400d600c031801d980d074800b04403582e0040060099004000203039140011524071304a145600d4211107218806022294440092500a42e8140316041441c0320a08042e0b00304140794000a081c04078500005048010000220741026174610480352025003074811a052942c0020000002e0464400c0490059003001008200c9140200603180b103040540d503058100f281c003d008602610300300012506000d2910419030250841d07500608100d400b40001051010324281c00406000d58040945d10042d0103207804513840f201c032100c548051403a5603c884094440d4000285450a402e0b00106684260a4001201101c01d2600c1d500800800e09a481c40c03031035800f000201c058202c4609006070090800e060545000c0e503c140e0483d0322510740d80070340b0003072040c0f040c4000003507080a0a6404010042201004044091003a601410380d508401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 174108219 1250 174106969 174106997
    0x302031507080718090c0e0f0105210a140a2013030f0510060f060207050102060f04030813173c030703090203030703030b030c010e0901170115060e0a06 67
    0xb4014040d0905003049400d0141c1141518108801c01c042c0040309000c02488401080c05400451082031244c01001c2034401e03041e4035800f800a480710500034104204010f20341203520a88048014101b4880a560b80c1603111107480e1079001d517121710440100080e00e401c017078110314000201e0b150000c8076904200034000c030036220100000c080780e0b4051021001c0b4060341c5020b500341041844074041552a0410000f0555541e014000072100170742c0a03034004039100c000484c3c03100c60488800002c1003c0c04046000648500d00a550000a004280018003819a01c001c03503400413040b010100200410045400c807506000c9000c8002511044524001200362880e103840b0b8060807040800303008400194a14040d07001a03040a034000c6c00d80f6900e413290306d4050020031220304042c0c00f0348280385100407594000d046000311914001c00500ea01d07072070803844c104941c00400c4404025520f86d2000c0c1506400808035502600d11911819580000a001c0c0050414294003050030004460300c3c0c2c800d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 174109469 1250 174108219 174108227
    0x60f0a0605092704030e0108090a0804050f0301140406020c0712050a140a050708150106050c06010b0c0c09090c010212040f05060304020f0907020c0111070503120306010306050901030c0302031507 86
    0x2103400d070b041d20703040300710141e40301c11200c2d000014015142480003102008109a07000b1081340a0706400d880da43c50315200c0f00d4000c0d5030342e14a0a4020170581c4204230031312140c03406048410f0740c114028008070301c800803c4080c28100005a030f0454003182c020070307103810502092140c8805009400c0030300d080710049454255840e0044000503040c1e074943d18403861030341d04c180302107038660b90404116026181e80e203041c0b47d952020700d01041850b441400000c5080c620036006c40708201c065400a2000f64201802000c031035001e03103510107607840303501d0303550b1510b4455080140c4201800c0300a04081e0003080c00282c18079002c3d450201c90314404002c2400b00c5d0f5921003000381542c0e410390b82035460b0354440c408104203003c0300428541c40303240300c0e080008496000130701e1420305030281c2c1c1b24540810704e290740325510074103801000d9050700309440d861010000200a194040310514000c2542e903590008200c04038002c0c0c0081c1c85d0f80102e401c0c14421340c04c0030002c0422070720b5880011b10b494580700800070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 174110719 1250 174109469 174109477
    0x10b01021e01061e03170a12050c090a09050915090304060f02070b030103050105070207061803020112090c08030720010905010c0204061e060e0312091207030c0e060f0a0605 76
    0x14020711512101e084006500354403400181a1010022840783c084003456000010948021110201d00c400c1b10800c2100d100c042d58400d076159200c1c000108808080c030030280400614030a0200810b00940540d80d48414400004041251002526080002d845401c044032003510580b0110394805100c550b0000004690444e440c5240c8034003c8800380000300e0802515900001e0180d40100c00481030010640c8594018072964003110100303070b682c10050f1b9002c514511070400d1505144800c2015502411502c140700c3e080d52800034410b1125500e0704c01c5d103000d5030090ba071290300101328042081425100c42c00103071040c05a410300c4080742400200001401d029150400040826060840d1125002103002d452040d40040b00803801030307801e4000e420603219580c001441d50801013218200070a01117200ca10f07140d0120b142c2003800061061940f00001902403e11403280c00001042988542c10064200d0381041c502d10705165041101e0000e208a1031407081d101d00c0010040550814121 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 174111969 1250 174110719 174110743
    0x603061003080a0e060a030f0c08040b1b0705031201060807110c13230601230f090114130f0b090102060601080702010e120406020607051806090a09020a030f0e010b0102 74
    0x82c3c0e841c400c0701030071114000b00c0003c064014101107008142903030150850004035040078010080c0380390060b02181c09400580b0081c1030301390001c0c082441003012400c3c01c80064100228107151156558034a031851303102c1640d240043c00400c006108142c2c0c841c408a401440a00e00008410100b41515450700c2441c40c2091061240701e0014140c072441e0f80100c0e07158141040e412003103ca0340804960b0700d4604a48060005501c0754400c005a06046080d407421114013500301d060000145144134140d001c6a54a41800300c175401c007040aa80510041c04603440f80c84030010581d180c0300c00000030350070a4105540c9400280014030075642d0015089521500c2443c0c0820583c481000c1680108034140060143d40507240c2c03112400d10b0360ba0300a0080b22030913401c03248580d59008040350340b805409580d000801c0704546000b40c40ca004005820f429100420512500d075603880f502c0103e034485135441010a898042c80362022030140304c2c5400c4224950000d01c107003040303c00000e44400ca51914 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 174113219 1250 174111969 174111983
    0x120e15090601080a0830040f0203012003040212030702121b0607030509280e040506070207030b13060f02030a050610030c140f090a0303020619200a020f0709020903060603061003 78
    0x240514043d1b0f10401000c0f9041c6050082241444d007005030600101d81020f03800381d03003840411084601120804009030400002c124103640ba03660810a0381c1c0da50030004c0703d0502c010721440303000d41d9800405102103203101c030084c1a00d140e2030f5007894921a001d00302910a000c148840808a5041011904401811140f984500d0141c884542007016000481c11250004482c00300700039800c42c1a01c0e00850155080718840d5030b411a040340e46040c5030000400d18030740400841c0d00209008818440c003403090780c01081c0400000b400108036001200c0180b42640c0344c3e414800325050aa0722280c0c40705a5240c01d0092681440c0042c0085284089400480340c00045035000700f0034090035258030f5076004298103c11039a80c01c0c002d6895606988000001c03001c0f01310580000c0451050754221020f030031034100100c3c1100012122030304040c07495019409448031859107070034180f03c3c0e1b10240c80c5045005031101e0a220a06140c4500181081c1c000e6218070140200003d0b8896410112540054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 174114469 1250 174113219 174113257
    0x60913030f120c09060225150e0925080405030a050a050405060a0c021504050d02041112040506090106080c030613050a060f020d1812120e15090601080a08 68
    0x1c903a2605203940c04002e0a103010480c1d940c55a01c200001d040303560079800ca413540c2c0c0d190b10650001d068001e4400c02102141401001a43c03061401c0c18050301d094100411024243c0010840324070080320240b00c1e100321240c1e024801c020210200310401290310304940f25250036500c05a480c03080d07000180c03d105010030040c0075030713118108a81c06814041c1400e51a149081c070050046442e10504900c1180318820501c158400102550211355008146c3d030440110341d000c0c04020124013503028040402000107241410031041c2842c0124461f500030403440c6444840a401c40781c0326005030081d5001000b03807035402d60300081c5d40c54001c20072103505155140c07585030051900c040203500401c2e440c1030200300700c0f18040300c0e03000d000c0005e0002c0080c0601c43c215804280080aa010024550109103c00750130403803007a07100002010701541d001440000d1303030030030602e491107000003241029000ca080150074442403000300e00411b00358000b0003c280042d40c1d000114010a02c032444007401e491 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 174115719 1250 174114469 174114497
    0x1302010801062001021b010b010f05040b09010e03010207030c03030e24180f10060905010315150b12060a0504050403140703050f042d05011713050d110606091303 71
    0x604104003c0c0300a9000710766032240c0001c0048100341c040d050410325482c245030070341154005c00b9000d85011003070b5503040c0741c5401c00c0310510f1250031407204241000300801c1d107101540c4091000b010305071300944a0145d0700d15140b80040640e0303482d4000240302c3c1c000410028130b160f643c509442014072150724022155070348038042c86444140b941024064031501d2451343c848400818400303208840e284050001607219030b1400b054131000e00c0014804082d803038800b000c65840e0f0384640352182c07200603c82d012559510071615039420107280d400400c0341c2d20051041d07910b4500c0c2c0c41e500401f01074a0620441c5001e80f0b002d0241e212408208104203400248402010703c10400c41e440302040c07400f07240d121070f11074210620002d68400d4414401c52441c20124205e0070140304a01200c005945011004400100d0050451405808030040c07840c082061000107a06001500242070a0382ea5040d818070b41d441110b25000340606400d00541400041c07002c40015a6070141c140c98141c00e0401c2d0b14240340d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 174116969 1250 174115719 174115757
    0x3717061f030303050408070615030b01061d060a171005040f0501030218091005100501030c0e06031504021e03060306010e040809100c0506010305010f15050a031b0b03100509130201080106 82
    0x200c00800491070f09c8002d40900e50b03028510000d40e03000707240402d82aa22500281e50b40148d02c0014030340f0101e4102c1502c0360b031501c14000c14150f880b07454091100d590540000e24603410544801841d010200f00601042c180f51040000c1011007031420b000c03039491038010503102038003038082c54010b0300440c0c00200307107800400a11550b600a5001081140741c0142c990ba042d8445010b2140000d04011034070a84501c0f404800407081c00007401c56156840b0092881800045e205034a0307001078090041c003090482c000b0141614118030f220440d03492415504041c2040016080780d1342080604042c807000c900301c00c094a400b000c0c1600c006401c800c1403074068900b8040403200826a2141d20008020080190000312b4214040b000901810707002110405210b11240503894005000600c100045002e61041c0c146041c60800c0c810252902c4071075810080d801160260401c10003418200050700349050219806440942a404d11010545c0028509907040c8215803c00507030041a040020003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 174118219 1250 174116969 174116977
    0x20f011a190b0a02060103060b0301050906060f010306030b10090e060108070e1b0d0903081e0a0911030607171303120905010209040f06030c050901053717061f030303050408 76
    0x140d09501d98480301c2843d002540c84100340400c030f030014105840304a95050501800740604c0c881c80140409a540005010a422040c0445e80c10075482e120300101184201c00143d00940c080b01030035a645082203480c4090b51415408071a007584020010803a9000200c0c50343c050313922050100207540c40740c02e080c4421442444911410bc2c1e00046c1f0200d18144541c08060450311135180c504290343c0d40c154000382c01d20160440996071550f6000280c001229600400c405d9208008801035900a030300420f00d010030846105001c02d00c00084518100752844585900c20b102410200c0b60425659005010b200080104980c96440e60018000c0100a40540d0413071040504204072542d2820310b4034018000900c015103002161840108450810b0304007141a41c41c0500901c0004000c0034140c880041308902140040c0c2e0560200181d02101d003107044020301403000b004046003036110640d418500060b1006a066110132031900c8090611010704048a8043c100054666924189141c0ca81301e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 174119469 1250 174118219 174118229
    0x190605040f0506040e07050102070509040507210c0b1804090f05030f1305040e03190207080706051b0120070302030f191e051611041b020f011a19 64
    0x1040c00d00310341d50140036501192240100301c80522981e8070100a01e512900300c0d015441c0141c011241c1400320342090307440541c1062003441110241d5981c1c505011a80c03103810414425285108904c4e010f1003510200c9801902607500d065150080e070070240801090199552400345860704000d80c18800c1c40300e08500c110760007000340c0350b8502204690011550004035200b091429401c004200390034030348034000b0082190002035150850011f1449105e4200c185583c0440c81960710111b03c03100c01740116001403440b9112035482d040c07c8049800364070708508a07040280e240400c0da60500340e44442d8282003030302d04242242d481909007022403d511501c503d4410900300051b1044042100c64122210080141c1d100300204014a09001c1c0c1400444842d4000410038840d65841d662070001407034400b0301c6203500d800d012184802060541d003458060078807030240e0080c40000242c0502c8074081d1035420800800c0350030280e0745000503844803003c156000707141000102403040180c1100d04041c0c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 174120719 1250 174119469 174119471
    0x5180403170910060801060e041b08070b090103050901050f07081e0108030d0b06040e011e050d050f010b0111030409050601140c0d0e0904080a0c17070c03050706080f19060504 77
    0x710303210b40b041d80c1c0d034400c040788515401d142207000500701006210303240c140c410110b038002c8107031110f0b1110700b032403000f4071404480e4014130007000642d248104040001840c4180046840e500080005002c8900040c4061182d9042c0380070402e08134002800240e2000c0241002d200fa600c407140011396800e5000d041c44c112401c035000115a401000005d072a4039000c14406004e070008840c2402518040d6104400c0005a40001405181c04600801e603460426401c481c0007290380e00001121030a00d0002904c040c0c00004c07d6540c080350070b0042640703000080c00c0016900c40102c0b03496650784500c3c070a0b0104503503660041001d9a01c6907a510b4660303418180ea141d11080e84c14101e5880300c3c0034282c000082520781424401d0390074406141da10950f00000044c0c181815280700356952405207604032844070562142140c030a8449024007201c900820113660320b02d04500e0444c0c9407080c250480350921000c90104010304550394078082e03006245c0028445594095800389c0c01404154205d56845 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 174121969 1250 174120719 174120721
    0x1e0f0120010c11120c060417091c020a06050405150d0b0904081207081003030e030a0b01080a051504080a1404030213020a030510060518060c06010b04060f090518040317 74
    0x30703583c0004000c0784090118166441c180e4649603404240c032548910700712035080100020013080d0042c503c1410a001080245d140220400002c0c0200003001d40745031220000080ca0015400e0844840024207942c0c10858a06070a000002c0c071401444200c000c00458005118400588260444152480c1c05000d03128141043d00c0c00d2140c0d50056641c0d00b0610711240001111288110b4403a40142e9032a002d65100d50b045031003c0700c1002c195421550144115042000083c04035821117009040d0f100240040403041e1400c1410b11900300308d1415148038803014407012031b418200f100c8003550b040c18010152185600c2556807401b5a900284d030190b41c4034005071001e4425002007480d2a81035800304519614a14802c5106881d40a02c100255051194107102e01161661030041c0800400340b07401d200750522801e113001000d030041d03039003100d01003001c1000b82e4011200c9000540c95041513400241040c020234581c0d60101c035a6558003100c0c00c00b09050500504039070b10b05600040300e401d82 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 174123219 1250 174121969 174121991
    0xe0303070e0306130b04121815140909010b1317011517120307050c030d0608011103010305280614150a03080d0b0105090a03050a021e0f012001 63
    0x80c460441c0000d50090003083c00281c103180b8000032540031540e1010700c01c455516691110341c03105071004a0303d014400688280200f800c1000c41250080c440007655040c44961624018002c200f0741c6030907400036900f446426000e139141d101c50340c1036135110314107203850364000491100031040d5580140c5a0507604030766042003e006401422401d100701d04111803e50b80c480381c0d4010028580344000554000e070800340b128004042c001c54111110b85005801d1459203404242960b10a00e05a000241d13640d01c10042c0f00401e020381c041d08503032410715034250b40c551f8860ba45c5502004400524001070078008040481884980f0034090b9080301003001840d0b0000c00e103101000c8255444560740c3c2c60254038030030910b0000c42e204181c0f94000c0c0700b242000840c4a01501419203403d019061000c1408480201e480e00444a8001d40c060802130007103e03010b005121305803071084000e40c1c600303141320b0003e54242c4172080242408842071802c0501031041100e0b18604d2090300c40070190b107508003102004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 174124469 1250 174123219 174123227
    0x80c132f040e0f090a0303050421030213080111040e131502031503030a0e01031a0409031707020a0b010e040611160611070c0303210501060807020c010305010503120d0e030307 77
    0x2a2040407152000341d0f2100720300e801d5400d00444149000d58810482540001c3c400c0c0c02168000c1d01c6030040712003003e622039882100e10003107552080025804190050091003240c00e40c0020100038000700f044e90305010304240c0350700ca14001d03503013807400c02e101050501e803040350200038190700851000307916800080c2e058043c2d802a24041040c02d030413190340c64645008000c80c1c00c0c804d650345030146000d2283d4010750151101d10203400103000990382c541e00d280c0341c90250b03a41542c4242e440c0c0071011500101e4440006c00642084110b62100308070b100003039100004203042d9003013401c4420311507441d4035100e0060414200d106914400c08606010180b03031004081034110301c5944140b00d4044212001071450180c514040e04490b0005020000700340100340f850043d070f00321026202a408150205004e07190203078840030000b442102041001907060020b02c801c4902440e081c4242d51401e00040c1da1880f94070070048919000040c42c8030036491039403190303181103c04000d403a100d00c1d00d520058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 174125719 1250 174124469 174124477
    0x3040905042004150909080904110a110a0b1803070501090503130501031107020d05030d0501080703120810150507051501050109171002070f1a070306080c132f 70
    0x1c1c40925685049503918090198001d5003584e10f0140070160702d820503c3d40501a040707000c0d12044001c220b01480ca44942c0a40b00c66145140c0c05c041d030318000140c009196080700c00c50008070f070b00034442d02000500701031041900641140004410f1703038550400179095214000006000c1d42c6880400e00c200900440a000100c0d0301d00c200482403691500107606031810a03100c121001d81c10094000180f42008550a00c0e40c014021a420128601c0215003120000c0e04008215484180100100510b48404846400040c80e082c0c00324102854411580c9440e406a64000706141e140381c2051413044041e101c0b4030342c0007000c44202a0b42140000d036000020300a290008a14030800300b64116030825001502a591005003c0c1c200c0320071001d0025084060111040c030b07083c14a2101044120b00404686001c070500041c2c5420700030b101404a0f00396034846940740e00f05901d10b007040d9a40d800350464242070b141c070100b004849060949170b5407820850300314010340051038840541c524103001d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 174126969 1250 174125719 174125753
    0x50d050a0c0204202701021f050a090f051f0b03060a05040206090409060e06010909021807090306020703020d08060406050312090a080d090303091d0106050d0912021612050316050304090504 83
    0x70f13100170200c200049842d44441002d5089010811011030b034401d031680d105640c42000c3e2040000c0310300840d40d80d001684500305042c0c85644c400c10703030341c005100100000c203000c0c1d141800030003134000c41d400842d03150103001303281b00c81c1c49554200050541d100c010494071414801042081503900d01c2c0740c00d030020941c00070614058803a0400100d41075900b4030400c540da90300208a05c007052154510000000001420441001095880000003801500140902622a4018281c00b185001000b020450f00500705d070300c698242002000540c4010504e0042e15100b4004c40d683c89225101042c407138050350388940b41d588120701400c0859603101c4001400d580c420303134425096139500c0f40c0c1e0f100d4503405a01c1d0040e818620744010400340c0c2c0914001d0108001841010840000070380384d100c1486040b11124026130032580700f60504041542100d000703810744600c00858400d203602c40582d84d0260702d0010030411040c0710343e01c05100c0d0820940d001400700010134481894580b400390482c900c00008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 174128219 1250 174126969 174127027
    0x1140904061a04090e03031003150f0207060203010504050609061e060c07031101080a020f0d020c01090c03120e06070b01050904050f1605180f07180918050d050a0c020420 75
    0x485e101032030b000320440340101544040c64440c0350854445410880300014403c4c2220b59036070111141c4012800688001c5029800058596141c00e0502c400d4500042c00b891103440700c9002c2220a9943c0c1507041c0c0310101080b4003100c103070000d80128215229040e0140420710952800204012800080016000c0e00b0307a03e02109480f0f4403450b2003a0701901e114007000c04410700445c44101c4080c0d001d490711221820011070003402d181c071408401e90440d0000d80381c260112491400882e007184501c0030342a02660304515143c03094962036030445060045038440d4101001180510000304420200e0805040a56038181100c01c004003200e141c611400e80510f040c010503a1714041e018104a10800a5a08400c80ba035900d800c04c4070040f8000103403070501d0880a4000c20310b8640c922400808106001c08004610b406050651500506e00c03040c404101c0200200d070300c65a4000701c01600254140d0f00402c0e03168482c10b10076010380caa01c036501130380c600c007240000d184c82144807101882008e40034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 174129469 1250 174128219 174128231
    0x190b01020a0f060b060d09120f09030203030405040b06040e070903060b1e0906040e0f0c120f0d0804050a0f1506061b14010209030613050c030a0201140904061a0409 72
    0x16038940c1c0c00000054009580c45000001040c000c1e0031031004510010a0300d480c05540054500445445100c25aa000720b120510790b88190000f80da50841980b605000b0001403950740002c1d900e00c5180075160149444002c052210b40707030401a50702400c80024034100e41c0c40c0c070b4800180000300500c020743d4194286a00c40c503040c1031010a40340700700340782d001400940c403c4805010049a01822050b0803030364828244410b140281b1550744410340200c00b40030344825000400413824a03032280c091207900b040a00108545d030006d598401010f036810300305002c0e0358a00f03049040c07100d00d171000f030185030a42c0e01410400802d00190703100400c062208001c05511580d045130101c40750800192145413601c42040802c0606c00d240929031503d10000d403070804072101203814200305541c5064103030b12503100403082100a025250010100b60000c1440107015000240002940c0d01c03940e00d0b41c54009003a0100b61140d810400140040c20711040155691400d0740b211540148210001245032403 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 174130719 1250 174129469 174129491
    0x3170c07050105040e010302100c060c0e030c030d0219140d0c150501081e0102040f08031306050a0f050912120c15010503030f0a090f241107151719 65
    0x43c295801d82d07400951805140e820341d8240f1400c00030300c030f00c1d400070310100054040c0000d50502495070b02444640e280e04d80b084060301071510b08502c5500081c881d0700041903242040d0b90020300a804111005a4219040503908243e4215100500841603d0151400b8403c0380c40c1c0180028103003038030400e10f0301c00c141c41c0e401c00c40c411a0000e00aa00d600d8001860101c034070a40030b50010b45080b01c22000525096481c5c0c0c00512220ba190300c010307540d40001c108601d400a0145e4a00010402410070710314080000314000e0120341040034560901c03c01141503a02c6458148d01180010140c40c01c03940e00c1065071114451a4005480c0e40030710740b094602404201c060003c405040b110064010350034000d115800c240c954002410250422820040014014510007a641e0003007109130007d000091740ca42c0f0b0885505640ca08040600480d0b0010001004c1c00040d080c00701d9034540c0880c011300e907520400315940303100d4881c0c1e1001c40b05448103011900e20380046418150480e4141001103405203 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 174131969 1250 174130719 174130727
    0x506090105010f14220f090b0306160503100801020a02070f121707060b0d0602090f150304030f090b0f0408070e0f13050319051e03060607060b040603170c070501 71
    0x112101c080040c22400c11424101c094202404804174070a81074456240004044080c0c10700c00c0e40a24840c40400c4001c01c00700d080c40c03040c50b180e590141c028000b81e103072820003880c000d008220030f54100000000050380c0040b81c0800307140a0450500203650b1640c0142000750b85012031700034080f1441c0d0a5600140d0b110381440d00d030200c180d011401d6002680ba607404900c0d141c000c000242d40075600d400d01c094007655148290103103103208140042c0c5401c6103006211001624881030b074051182e4040100161681d04142c0394010751500e4401101c2d030f40d03850125001310f1298400d03800c024020410260000021014106940c1144125002c080e0384a4080d2122a015111402c119030000c000c2440c4c0000194000f225501a800303d0b483e00c4610700c80103040d105100c2d0703110000340000c1035440042002d92152512180c10081040c10341c00d0110015801d40302c1c074a402030045503964080c1d28a61100d4002c04003c43c1c001029041100625a50321101e50203282012050700810402040039801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 174133219 1250 174131969 174131987
    0x10090204081f0207060e1f0506130504020d0212030d0e0102180d11030d1101180519050f0d03020c0601170d050903150a1b02010e0616050f0d050609010501 68
    0x200140600480048540740300045a003102e0b01c01c80d002c001a1000c81c109000d00b84003512902d000b0091000d0310040391185859001a03200043e0410090020783e039142e5003e80061540c6881c0020503484910004d00d951a00490003504503012003005403103054080094030320f400c802c0c0024880301c42c050300882d00302d00c2810300500c424443d00c0c01250260800b0280c0ea5299849190720080d0740c42c80f9400072386400ca1201003480010510300080141410038021001034201000a40580070f00942e1000d8940d100400710f0040b564040c1c2c0f160341401410440c44c121085a142074070703100303000a0b40c0180a9809071313602140314850a00001082544401d440464a84140280c82807819403603089440394031501240303506101d003000d19408030507421004d5014102c00c41e00001e0b8212480c40c6008101c0d0340184031819a40341940d402881d45006c18416841989480d5041e107009410f2000e55441c001d206440784103c40c04580c41d45201e1081e408103000e100d0840c2e00080c00c5ea642c1e0011070307107900303 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 174134469 1250 174133219 174133229
    0x60503010501170609070503191a01110d020607030b13020415020c0d050c040933060b12010b031003050f030a080c040305030a0807031805011e14010b090402070b01080610090204 78
    0x8141720004858520540107140c0011410004600124446a84900f07691010030309003202c801c00f014291080d278000ea520000a4200000385c03c034a412003801035194000100801d0516841d2030f041c484607621091000030b42d510000045445646802c046040742d04641e405101503c150402140d00340340800407a208544e008000700780e152905000c0c04054101004110390440d203034041c482d0903050034110400d2505812242c1903642c22000094002d0f43d1445c5e01482540000300a84680900074000181c10f4070101240a23540f911811400d00c0c0c100e01940c0040c0141c0298801502e080700040014202c031255541c904001c3d40700e2080364192031281d40300041256004220000115010300c007000d41c072690078100043c00c1c82026100c441d880f00080340c21a01659100d07070000d00c00803d1000c40c4000548648100100344410b129400d4455060040d09550b1901080303c00040d610364044a81c05940003c43d0609560f4856071107903181c000f564016422042a0004180703842c0902c00d8070101c80c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 174135719 1250 174134469 174134479
    0x9060e0c0907030207020102070f060c051b010e0d0c030b070504090b01031e05060f060d020703140c0718020d140703050906071e021606050c0d090f140d0204060605030105011706 78
    0x103160b400d02a4000e601c0305c030041781540615440040d4481000086c00000d04c5c2c580c84100c1204501d00d429400c0510003658203210745145c008642081e41e00074035015190390705682c5c141840b0700c141089030b80382c0c0c6a0340c8020403044290040200a9600c00c0c042e108545942d041400f04200120040d4180c0d55400100c2136620050349405100d005243c0000d9044200075082001c106482c5c808280e95510211120300825000a061010075a0010a427000301c503055031010700b8011000380b002c1c0c4620349481030041c138401d0400040c544c0801e42d03040710341355010a40e040029480910346100c900d13004071501d10101c1e103400001380c0203010202f81d03144528036690b40c0341c240030541c9681001f50307003100b560301e802c522511350f0400206070b0080a41e8003030146a01c0f625114840b140596282200c81401d420801201c98420810850030b814414240e074204100810140e04000106040201c0c2c0b0002950050400b03000140642c1c00c1070045060f01c10a907221725048e8404032040c0b0b007080c0192807990f004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 174136969 1250 174135719 174135721
    0x11212110a0204180b070206061003151205070b030106020d0f02010504110603090a02031009110109060503150402091c111203071112030706140106031a010305090304050402070609060e0c09 83
    0x514080e80804d02402c0703480480703440c1c140962030b48010902c00300c800d0009a84954180000e0b407408005c1c0310700700c4280d8030b02482900f0200500420084092291080c40f404150410702001001d03c900d034043c020036441c003500c139070b9148d40095403020b1400e07020001c82d5902405864607413040c01001c0c421900300040e2050342031108140304003640010310200884c01654000c100603a0706111407030261103254400300381c4014505001c000c1071a011101414825400410020342ea000704c281c13548108482c894031044003124021901a10515035a1588240e5980d24440051070454010350014050404962144841710038007950400381d20a8010b40d6005001000001e00c115107034800c030002c040e1035400300e0481d03600b4403850350700410740484100d038807801030110b500d240118850040003545010f01903200600e00800340380d1a8020440c1c101620782c000200940c1c0c082003200d00601c1e01510031556000c0508200340100807c10b401c851950620030720b03950b141400608841807480052805002e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 174138219 1250 174136969 174136973
    0x905071b08040909030305012303060708280e070b0c0a0b0a02040e0103050d1d0901060305090c100e030c040207030906050703030908040b0406180e0105010509120105011212110a 78
    0x4038a14004003201e96070350400001c6804900d41c0a810340036442a200859079504100c1d0251040c21500711451000c168a200d002e13580d50002039040c0c100c2c1c0c0c00c1c1000303159a26031091a03800c2103000c2c0905800319041040902031542250f1002e800c0c801c44074150b5200719180d03808161644540f001c0001d03503920004070000444c0c0341340b21080e00038402150040c946a5251200b03c01c00c1c01c00d9109032419000b03110211940e070340000b40501c00741280d0300c0003031644c0f00400c0002c1040d00180264810141e44800081c10400c0c00c0008048100000345445c0c400a034845006002204000c4c00502a01403410745803054101070095034000f0790b05032100800181801022601a00171030003d5080545500007407020464000040c000f40041000c81a60355040500c06031402040c1c04a1018886e1080000c0000d20703c0c42d0811812741e407003440d01c01d40d51032103c030000e1890a1214110170300e65292030000260180d0300701382d00403c036202d20b0089600700b00c45002179844d200308a10134005a0040c0203c000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 174139469 1250 174138219 174138257
    0x11030a03020a090e010b0705070e10030b040201210b040c14030708060a090c050307030c0c150f15140307120c09090f0501021911121204021c110a090507 67
    0x2410340030303d01d45030542c03d42d10320f40c101010100b0b0f030201c01100c100049420a114060001c84040c0051848800750f0342031507200030305409600d10014100319150f00c0402c0031a80318001402e020001c0302c0413a60300383c40544140c0024507860107124440da140070107070a040c42c00381c0307803130b12443d900c0c0d0314118107661b1102015291004000c0c0030075440f200401001c601501c07944201d004c51140c655804d0f0300c901c1d00305005000c817541300300d0071028407070750f003085d0400505080000c001c003140314030717010400c5505103821201401006070026030b9160040c50101c0c043c02180c0c440a15a001203049803011651000d01000c48102400050102220320206001d550165001791400d5449403855802005040d1900b900326000341181056407148030780d207402c00d50383c00342007038003140c0c4007170007800300c600036048010390910030340d24420061001d200002e419562030400b01c121000c040468100103038800e2070100380741c202e0460701a11920b00740381c0100d05049640b040078841c0c0415200c403500700c040c40300b25003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 174140719 1250 174139469 174139477
    0x70e0303120912070303050403021002040311100e0a080105091009030818070b040b03070201050105150a080606040305030f0301090e01050103020d03110a0503130306200702010804050102091008090c0111030a0302 93
    0x189903105a442030040540c3e40002003a845000b0f54000a07076042c1894001d090003a80881c14042500600c02800405c0c0c07035403024020400112510110301e00c034081e0503500702610652240d4000e0301e200c0000b425803419001144a20708050580e0802002803072035204490b11140b0143c000f44211000030504100340001c40d0a00903950b0407201034940c0c0e0440760070650b203e1b4018000144010082c4503070183c09000e15805031404540c0c80140418214020025014500300c0d40100320880000c24000d40724401110007440e084816607989510314030f80b41c0c080354000c0c803603003030414900412240645018800c0a0680381e0003000c0d00c05c0e59a040d01c0480743d00d0749820348210035004d000d026000040041000b4030101c140009a0300c4454510b04124080f1201030082c0d4803210710003020255011680c0007211f400d5542402c0500356504c41d03040145c0203006a918582d045000c9281ca118030540000c01c0d90f21584c000c80496200c82011001120281000448605d0a910510038924100d009070054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 174141969 1250 174140719 174140731
    0xe0d051501271a150708070305040509070f021b0604050d050303010302091f050103050a020d1a13060f09050705040b0301080a140d090e0606130f0914010b070204091401090b010905070e030312 84
    0x7130342460141d498503a1745500440048000c2600041c08201a0809940c4103910030760605044c80800000040030b92100d161840100501e0205034200000340d071100243c40144c00007a0940381416000d250040daa5482800283d1141a0020025000302c14010203401522101007043c0b110f20314000055001d40000b0304841c02d203d800740034a48a101d0203100b030000007542c4110980d01e0114441c18001c1d800010401c0c60540b0703003049000d0008184200100c4200c03508030030001400d13564883e0440342c0780103d800c494284000040006003503000000d1880c0818041c055048481c9401c8100c80c3d91008600b039502c001c1141c401b0100441d00544e1541d07a03001d80040c101c9450504c200d40e500200340c2c5107070490441078a0036903040c080081c0c5481070f019801c100d22110a01541000240044dd0260b008000d02c603549911802c000c11464008800c9080504d00c002d005100b40c0b4941842d040301c0134004e4280b03251500300000d104620a55044000100141c051881c0c0690b5071940694201b0091007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 174143219 1250 174141969 174142009
    0x10f050a06020a020d0321060504060914010e090a05060702030d06050402042411030d1a1207170304030c061101240605210103030203032202010e0d051501271a 70
    0x901c8508440e94550380700d5070702080d0787c0016620308003030030401143e4140d0070000d40795140950024101c0c2d009982541034803021460001207594480480e80b51000302c42000f40340e4040c50f002e000d070480d0004090324501e1460705050150380e484100b444104c2c011440743e030002c41d081e40c4d18268022810084810810082d24050902c2d032915111540785910135401c6100c1075540f1602e81c84c09042038041024048001c4500c00e42204c44e046600341e554000323018000c01f0b0704562000c858280000c02c221002940e12100d007074109035466402603e081d0304105c84031055424100180a4801c5c030390405414611011928a074050038000d04950729000030074000d00c4000c0300c0c0100b545d41e4035004111030086d4440d41c01950b4a1a110382d145201c81c0e10391b01d0078801c03110950325201c0141c4c0c00c1400c04080c050103554145200c805414010700e0045017000310044c3c9100300001007510024007540c0020050200b000c1007400e40300160700710494161803c010301c8a500c0091003482854a407032004080900c80b05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 174144469 1250 174143219 174143237
    0x302030612010c0e0415050619180303030b130606050316140301080303060a0902042709020406060807021e0a020d020109180203180a120f02120f03010f050a06020a020d03 75
    0x808600319150304a25401044c20400307040d03002d1500780034402a4040302c0e4000240c2c0c0e464400071981c0e5000c0c503840c80045039102d400e200c210900c159500003103440400003603000b0703d5503414058010070000003c98000c801d10481e86586c03881c0c0740207140450b00180c0d1154610741d1040319890003034144220340340070020100701c3e202041c103158001e18043d0610a002d1940e03070401c1c90811241c5601984015082c0740180400c00c2020340040001c0340090031000c8514102507405d002000030000782c00000c0d8490300c2d142010552550005203140720b0102038080f1a042000035048002404a245903040306900c50007000005007030518007050030b2031040c186504074030388510346c4001c0354100c100048501c42c0e01008101c2c126030401d452071000401ca90140114500b151581c0105480803c01c0e002485000121111514801c0003201c0342001210505600c2d25240e00c25008107520a01c1400504036284c440460b40303103801840c0404881c065001132188000703950a00c1542d01c6e00d04026414850154 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 174145719 1250 174144469 174144499
    0x30506030f07090501240807081510020f060c1201030f02011e0309150203090613050313080109050106060e060403151b0302070b0109181e1a0f010e04080a03020306 72
    0x1080b0240032500000300b03856042c0581c84028241c8000c6e8040c1c601c884a19a42015070000380341c1d60040268a0051100d03550212542140b0300b00050140c0c0010800300000021039000c00c0e45a210b21922080c0c4103c1d445828010a007030142030458501000c10000420000750010804410b46206050000b01b08005c2d684c114624903d07522440b011a45801002040184aa6640807544444102141035040c410700c00f6503541402401000040c0d50101c0460500030108140c400200390003c4079003105031102d204a01814001d40210780c1503080c020b0201341036001d5004c0c0340707403060094074160400d451034031004507215818510b41c0255942d20303078004802c1c00301030500000041c0b80d2005652603401d480d0072134108805034090700d076180c80e040c0003403041904103542e101c07115000400907002d500c0d100484440010716507402030001d40c403180680c95000c40081948d228561440100c04141c1c0d0310390400360320352001c40d0f004100c40001c12a1a040c2c80c0241d0103150041703400703480c0380700142d200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 174146969 1250 174145719 174145723
    0x50a0501020408070e1f0504090c1703220311060f04080a0804030b07020c101404210b0112030c03050d3308030f040510180308030406060605070c0303030506030f 71
    0x76000001079400004051010101701004e89800204540ca03d241c01400d1402c409203108090207905d100350380740c0d00480144004040f04c20081c3c2020002400c0b107699524850755258409500c0411141c000b50b1b41400707e456125889085981244103807407552440d00030854103074030072806006065024803000c2072030402005001c0b465031082d0300c0309030354a04505100280c6840100014115480210004040d44a038190030050703503207a05007441035450303400d0301e1102801250041f4100c84540211414503141010002d826036001e078030300325483d9882c0c0c6220094a14002c0740500807400d08032401002034450300040810810002c07001a181c0415010740d100c40c0c000c1d0640b02101484004c040151110004586004000300c50080d480c1c1031000042441c3d40c000d40c400c540c4250a4102c0a130b03032041c022001d0740701a18007040c10300c00342600d9140400d881d401c1610256032083c94203d010482034040c80880c2d218070303041404442d50f03d00c4d5a074201c3c0a010000e0034280c05000d0303c807006ca824030702 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 174148219 1250 174146969 174146977
    0x2090c04030f15180c0501050903010906050907150804110118080633030a08031024031103040b060409080c031c0c050412080a020703021c1a0919050a050102 69
    0x1c01c881d0b007507003502d80b01c22450607105070841c04443c01007143c9125000917407440300c50301111002e003070098070b0380d405000207401001c1580c000740c6601d0a000c200000c07010089030780744c144e500d142c9621410228120040b00c0807501203d0003002d620304210807403000d41c0110b80b41004615109c1c443c803607654646c10000d040a05c162454540140080d5400e0340b04801307244148469590340c84a80f00f100380a2000a9a408a04c0d1700501a041e000002c02e801607685000752024056584d001101c610301c0d0310074652104840041c000000b8582581030041400c0c0c072045a000b982c0040009540da180c0c40c040000401d407040c0304a40001c81000140141c41c428006230110030030903141c02d109004030104440503100f08070441c07000c0003001c000501c40201d4180034040f83c0390700004020384440d12940700707915154080d000030398004040d0039120a00044051045019032290100054401d0fa030710242042442c240d4007030b02e040e0011114400d5102c01c0079a01e2080c070303000340c044400c1c541e602d031141c2c0d08a0f40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 174149469 1250 174148219 174148223
    0x1a1318051509070905091503120403140d050706020c100f06050f0301020c03162a0303030b01030b0105042c0901050402120c090f071e08100602070b0702090c04030f 72
    0x5110820004058454462050001e00581d5101c0a034541920001c0c8480701030301400d0f22a092420214908940403860390307205440103000c2703483c0b62003c2040f2003c00d8205202c00c55071040c5038160f5106000c004140c075102628a0740722a4144030321652910080e4000310401c0c0501c0c0318061f001c1c880880f081c080d120030180c0e18040002c40c0c608040c10700ca0102614072001d8026801000f05034a410b200008803561481400f08006402d152442c286260508844000c880c681080d590203070340b541c01074880c6c02268030179101002102005401902907d03086403500e40410401c3c00100610f02100202d4011000c400740d8090501261049030380d80024140d40c40042e40e03545208220841c240004000400c0013800b00814500b12450001034407618010911862038241d000030071080340c060740455405610100190401c1c0b2101c2400500b00c031030481341132a41034075406000030040d0010940030165142c0c5048a49032404680a0204051000e040f6070300c1d41c0c03003c00002012551101400b48664 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 174150719 1250 174149469 174149471
    0x1103010501090503070e0105040e0709141509070903030f050f070c03030206060307030807300f02060c0c071e08030a080403090b09030a0311120d050f0a061a1318 71
    0x94140400107220110581041e4081e5002c00c01c244004280a45c0340c80c1120b07411107001c01c0c1c1c030b810161064280001540905102410314207211000220590810710074a090039040701c3c0c2403170000c10000018030695000c008191004002d1012038802c140b100c44540140c1012450611004500484c40e031240c9016216503000b08001c1c010540d040c010160001c00490090034118103540340c100480c45603a07401050001c0400280601800c210703041c0d0142298000c0075501c402c07452030007400000e102010343c0010b004100000314200c40b03110a60700d041c400a4000d201490424140c040c103180ca1156501001e425040000f6440c4802c1008200e110065a5420341504080c58082c00c00d1800d0341004280740d1003071000c0d1807180c90004001d08507607007600c2c0c25242c94802800c03407801c000e105280d2011300c10000400740d84010302900802e006425030070801017141d5440034580e04580e4035000f5044040984401e4808010209014019140f04001d205992a0b51803107980c20101410420740002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 174151969 1250 174150719 174150721
    0x10e011b03021c0905060a0f02010605130506030607030614090603010908190f051e07021302040909021f0813030e19082b0c0f1205030103140f0616121103 68
    0x8240c2000e0b035441c005001d400e0400c951360901000500c58001d0380c00d40c104111290300d940e000346100b5004500200409040d140d07040e00c034070f5003d90113840121019401391280c03a001c2034202d8880c0c402c4000b103607a001d06081075410381c0b4003044265070000e0050750380b42d901c600c4014040341c035420042401c5011040704a1404403010710183c8000f2040b00c6640500005100101040c01002c40c0a8005071028027401d0341d4482d00c0c0b0005100e1403450305100304152000c9004102502c0f20f51101002d54004c440000240c0703a150390404101c13824000c8900001c403c03c01007010708452604005032140300342028111950300d41c021035036001d030b12500e8889100f8610320802c40d00a0a00a42509101c001141c68051101703100241d540490351141310200005c041c0081d06002c904980d10762450791004900400069041004000d80c10030702003514420207441c440c50151000103510a0120a12005441180d80d08441c0c8a048a03882c40c0410038801c0c14002e4082c00c03a100e101c1c00d00b40103030303001ca0680c403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 174153219 1250 174151969 174151993
    0x16080409090b070905031f140c090103060b090a03020913080304060c080603030909010303080c0903070e271506061902010501140406030b0f04210c0629010e011b0302 73
    0x80c0280152441c02882103000c02841240c4003c13a4000111019401100c01c1f6560500020b00806e50402450309024030b10050000c032481103002000c1d080c400341d8052106c43e85400e2600c445100b640680b6a02900d00c0008000508005920f00e03030110031242402400da046813141e0086a10460302101c035107540e0401c030f03040701ea00f0503695500207200703500550509002002045503040b040c0400340a1000400001d0f00480101080b0341d100e07a006010381d603202da41c412003c80310f01c5040d2244076030020b2100d02180c00d100c1040c04030103c5042c000007071103a1181d020100909800c041c080765000b41040105482141340091540ba6402296000142c150301d850410500c5c140d15028041c0f180e4142241000031070aa045402e030450000c9201c0e0ba0903445e035140c51000c52014407480820820f0407400029a9900520400501d13405203100b4014211401c0e0310070185240740030070607520002400007000951040510781203403a010304058900f005c000ca17094459402c00c0e0021030042e80700c0742074084 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 174154469 1250 174153219 174153233
    0x1060909060f1203030515031204030b01080607120209060d020309030a03050c030601270e090718022b0f02040803090301110406020622120809011a090703021608040909 74
    0x7000b0010380300d034030028a04140314212034020303070003024040507150008214250007000e005000c401e4010304403940c440c0c0f9500040750540042c0f00a80d150001c07600001504007010613030b40c3c424100bd40d0303101c108410103903079a4007d421404100c1c4c1c22600a202800342140b0620042d8065103041000b10b440c0e4250303000c0102034030b500030040b100c0308005109008590340c029002403076660200d4800007010b500200c80080c040e150342d20189105c0d03a2070050021002002c11048156428022443c00400c400c5c032a4100781e200e0410440c0440c3c03a030311403ca6003010545110701c1c20301280c00c8042484e40600c5c50203016a0441d402070000e90f04001380240b1189001d00c20000410108440203042070b2400001a468110042c06420a60708000001c070400c014070340c084051681c010135a0140f076040c00401840c0307030011140b6580c20b41c0781c01c0070400d0203103030700052100e2000000c0090980396100c8100b200a034100782c440080803103296180000042040000e400a0100e01500050302c0c0b40c1030030810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 174155719 1250 174154469 174154481
    0x406030b0319081b010f0f0e0d0e0a09050601050c010c050903070e130b190c0305010e0117070b0a03150b071e03050403170705010905060105010306140109180b030601060909 76
    0x1000707030002121640010200030a4a502139604034520344006804004d031401350001c0f00c820310100e13140050041207024994415078510817554111210060201da041d10780768030070406a82c0c040140c582c03c1000d9256900020340c46203044c9010390805640c0100942500e42010410011030004580da40e142c0c00c2c03c10440d00141486d015248a50401452030310703019052000103425001d4010008240345e01c04448040020300c080400c1000c1d41c0700c8000240102028018400c01c3c90a0000010b01030070740303000314200180380d200504078149c94078008a03480d42c0b004a1420901da222200a854405803d2070140200040000c00360781c0c0f000740c5030800f0780e40c0c56100070007000c452034005280425844001d035026a03900c0f0b0391038101c1c5105108030004138010000014429802c0082090411001284841c100d840a0300e0500100340c5410501030200200f0244138009414030744100000e01c4230519000d01035030b80c1040001d24000700e0000ca406d05200760480c1001c94403081e010840ca10040c8252 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 174156969 1250 174155719 174155743
    0x3121312031d0a0c120501020702060301030b060a150203090108090c060f0903010b0315040f02060d0f0f05090106060c0206070c09021b0c0414180f011a041802010203070201080910020406030b03 85
    0x50009840e03196200d088802250140d94048015041e0900c1085025411148527640040c051502c940c3d41c0d18114402c48022201070303001e10014a40069401c00000c9422100301c0550040c1d82030070440e42c01119400340080c8203c00324031406891820940301c840007000041c205000060381c0d411008103041c02c3d0340900c2c29843c002c2d80041e5404482140750454150051b51041036190b54601500002e1b0305401100c42c1d808440d458030040111220380d0358007107035100c0c94960741800b4960752401c186080300c000f40300d148042104003070307200c0051800a0061880034840d000f44112180c481e12820200d03000b9407445020004140c1c40000c3c1a40c0402c095130021008850620203100408414507902d200a00310750700e1b20200701184904014203020f0036441c076006030001c1006071031441001d0a101c4484514600403071802d0f08a8562200320305001d0001034042e00218904003040d0f00454560340000c0122040b4014043c1c0e110004146000030001000e842c0d41c0420840111420941050420308035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 174158219 1250 174156969 174156973
    0x1060b0307050406050d0e3304051f11210c0414010f05070212010606120b0901051c0b161103090d0204020a0201020405030a08130503060903121312031d 67
    0x2000300d41e42e4001c0c11a015102c051510903142e03001420150003420801410301018090014103003a46103d0110a42030001c0301842d10005140000c05c45424400555000d04183c00407880c244c003941c9410494101e02c2008200060307202c40c1c642040304103170050700d10000c107400400e000c44501500440c020b60030503080d440d80e5160034034012003600348103030394034049040c84202c0d00b10503003041c015000c0d605c850360050445410080d06950450080009000c0c0301c001c41e00740010801c000355548a00641000c1c054207100c1181d007400100b000c90b0400070000d299003c0f10302c1140700007400c142c0003103000e10604403400c0da094109417400b410040c04081c4500c0703540d00c280b00400d1607a413110140b0242c2e9406a400584c2da024400089019200d01e41246400d8030842ea43c0e03d0400082400030561502ca04d40340300c888544800402d52100011381d4580e01d44d0380b042c4a44900c032400000c0c041e030480e5034004da990f1101c005a8450311105103061024001c03a0b65222400c1140110540e003640c60030b08100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 174159469 1250 174158219 174158221
    0xb09060708061903020906060f0705010e0d0201021c05060406080f0c1c0b060d060204210521041e03170d0e0715120e01110c0c091015090315020c01060b03 68
    0x41684031410141c80040d102d1031b00003020446d03603106c4000725041c025642c000c0c1e540d55031840c14881e018103500906c00c0018400c01e01400b2100e44181709a0b081b141021010012403242c1e034215401800c0d011300400c0e84182c4d00c060000c0c155501304240b01030f401d00031029103105054202000200210220300c0d0b055416403a9002c0005880388001d298030203000c940500310010395050510007401950040c03420b421030380400c50919100c1c1d0850f02200c600c907108589609100034034000e02c116410050540c021130138030003400a074100c2c3e11700d0500c1440141e03818403001d5880e02c904410408403c589482c103080040c40d00c443c0c140074000c0e1045001c0e908000c0c500285080c00000101c001d000c030140030000c1c020011461603040e44c02c41145000f001009100ca0501d1103188101540010b651000c207110303010080109041c42144607200d0222030403018081860200380d49200758020301504c0402811500100010b500c40c5408010715048910058032000545d40032821515142c2040b910144144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 174160719 1250 174159469 174159499
    0x150501062607110706031e0e060f19150e0609091207020102010f060e070807020d020c13020702100917030403020f011803050304080d030b010c0c0e070c0b0906070806 73
    0x220a0180000d50719101a16580d520070040300e0340d014000329003049000d16003000a4a41e0315410024040c05100074030310303082d010040000e003200c2ca0709011900c0c503007042c000a00c080c4031004115600405025102aa00d04a0000172045405a42c44405281a0b540b800c2c0103907a0b4259a4660201d1b040c9e868110310b0074104562640c5420b000e8075240082d50000b2010210b910030340018420380d41c125018441140c66551b0122510000c68807000000c41010019924a1001400f40101c40080d0054003160007031405200b4a1213502d030044168940811164006854104500030350100aa9490250900f1304414000e550300f900b11450060b407080c00700b400566190741079001086003d09205289082c604612104840c00d940042d007140000720380000c26610104428003840002e6404021515031880199000618020301504103541e4450510100d1603040415400c038009017044502544c290340c0d0001c6d010b00448030000300e60814802d0205440c0c00468060300074400b00c800e440c08a4941c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 174161969 1250 174160719 174160757
    0x8070509030a06020307090b0304050a120504060906050318031216050f09040510030c030b0402040b04050106120f0204090f0e070602010b010c0b2203050915160b09010b03070315050106 81
    0x7001001d0303e050f50002c049121240111000f400034a00c403141d20780c07245802d0038007540f0303103400c111b080d55551100590068520b104030b08030760907601d1540341c111020b400c140c02100d40d83c01c010818a11010f100041c40300420040000d043c1c150058003001841c5c0c50b180503ca232942460864000500070140300c1e1440e0301c1c1e000d80a6503d411025100080c00b50b803080589802500305500242c800125204d000c403e000c1c9000500b40328900139281444130a00200600085507800d01c40c8200080014070050400d00325a0420b400081c4016409400c0c03545400203030b07085441d07405c9050220f0f540c41043c003000003804e000d48001000d50703000070400c103809400060300080c55040d0007040340881400041100758000c0261078031000c1d80c2034404006101717241c040c040750f1091058a115540d01040c800900990b401103920b200b100084015450f0350ba07980d081603807400074003c03808554841038020101d03101009088000c41c01040c1c101321445184481c4811220b040e001401008590080421402c1c45 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 174163219 1250 174161969 174161983
    0xf020102120301140d30080c03040308010b28020706120c0917010f0227030d0210020d0603020319151104060c111306080111030603070314100203090d0807050903 71
    0x20541e40803214040d9494801b40c26108801c0842005801d0082c1043d00c1030a0004e0b807002c10700e252505411030300c68500c140c8550000301c60060028201e00010310003403140f40d0141c5542c12502c03582c1c201a888012008400c5c2c10001058030040e48070135420017819034070440308641d146100c40100400100550020044481401080c1c0b41d031800b054a080390700400d600440f90100117950854845e01030720306907801141c00c002c01c0c51032844050b2200c0e66034a00402d5150219429400030400303803400d01384485c080d41101703a0717401005941e22400030140c0c07014010396142c5066a1190b00b4038240524000c0c01c80450b0070700890b8001d14005480c001083c4000c203c809a83c00c41c2451103034502103203446c440c59400009441d410200f212030a080d03a0105800110584070310000074886c0c240140b0410029020171108141c0c940d020345400c20104030110907107110090408103507114800c5030700c2c1101c141c0e4070030741c0c26013199403025402e14003003a40043c02641054861500074940514140000c0e51030301 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 174164469 1250 174163219 174163259
    0x32b08091b03030f0a050a0e03010513030305060d02090a0b040e06070e091801020d060302030106050102210a02030903160303140301080a0b071206030302030d0501120b0103080f090a030f020102120301 88
    0x48207074841160707a800c10540f02c0001c020b000e000c1c0e460301d0f4200001d041350044030348400491031024000c1c06a15041c00340a105007100500c031044246507803411009010b018100d02e0f0000b408992500150310307041191485076604950201e0f0b9866043c080c84102e816541e0307840401d4001e00c2c140b111141e806003e00090110469000c41c1d44d84034000c0c00c822262041e00c00c610b070344d8800a049950f20341540c000c081100c0c0214003c0000550f18001640c4541080880301c41c107100c01c600d40723080701c0a070368044e0400540d184100c0741411a04000709252a1204040f141c2c1045003100410405a01104a8116044860b0142d00355490403802c541c2d9038502d03000c0244040900d00c0002c0c21244104052000c088440f0707010701c103156413403c003e9100e90084603095002800c1c200045620403407018000ba4003039120110820380d030310355110b0240c03d41107000c2006141c42e04014100c903c1ea00c403500000130714000c805103119041c00c2d1001901d40117541280c09080102800104400344d110221400022 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 174165719 1250 174164469 174164503
    0x51603171e07210509150106020d0e040f06120f110117070c2d0308060d030c0f05030d1a090a0c0806040b010e0406150f05040503060a1109032b0809 65
    0xf042d4542101106051090080015442c00c4200011400000358180034501010310403115640c8484c81282c5400b2903030f0003c404182d51703c01002030f9061035404080c0c0315500c140c001840075156290900403004598050f10751450010200c41404080d000d0100c1541c4c09013800d1001501621a49404030750050001c4180700c106488a018410f00c0c1a400c050b04110200480350269180c800c611010f0620509030001801e110001e6001c0c2800c00340d4401d0710340c054a80364030454841d034031181051200e41080b2000d010038401640306019134000e0184041c3d51505038002c40b0540018880980d500416400000d401d028504200b907801800303007600520240c81c041171a106140040c0d4940d813041e081c5030340080c58070000191038008040c150640500c9641c2e80c00c104040041e00311401d0040c2d000e00c59052300820b001c10302207030b5140d1103002c01854088441b8188020381001034200740900c2d130f00b042d0311420b480b030f610041c0f907540c4101540b0308200d0804901500745208079681e103e042c400025028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 174166969 1250 174165719 174165737
    0xc041d011409090109060c0f030c0216030b0c160302010c030e03070309050f04090b0c090a15090b1b161412030405040b01170907030b0a14070c03051603171e07 70
    0x10b04000e40007030000c40e402c004180017562204600810203000309448c040001d141601c0a014288081190440070144040350002d0a00355100d420698401130505100c0200401c20304512244c160b5171607900c40d019400000e08103402e200f0140a40c0c00403103c01c0303010f070409c010001c00241c04c1400e1005644081c1c0b11483e100c81500b000c280140400e440c09031038584401c08024440214a0003070403000015070303a580c10b95942d410074482403001d804a280c0400c5107050244604420007014000460a00e0700c82030f101417000c4101070410000380d444841d441c214010500400c0a00c00000385040401d91b45000b02d5440c040c0300da62280198080c1900c980d444101c100c1140c2e1184c1102040c80940303c00b40c1200f818501e48031507131072607140320489013645850001128246203100310801e004c41d03071401200665075003004039a894050207044043c0502800b01c82c9102c0314000c900c0080d5440f030746540a203449030b034808980d0094000c1c05031165034010700122072090b100603c3d158005405040003501 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 174168219 1250 174166969 174166981
    0x305160f02011815060b040b0a0c021f0c0c0803090102030a08060301061d0f0a02090105070b04020d29100605121008030d02040603150f05061e030c041d011409 70
    0x501499a1404000418200d0803c240040c0380c0681503101c42d02e44080046941e1910244400c0c000d52242c103492580034021750f81c0b000c3c0512288507240f031005044800100544401301c5800d54525085d900040e85a01c00700d080210311010480641403260085040c402c420340001c0d501d2180d8841d0700e0801c140c401c049a820b4030709400c020041e0444014002c001c034890417070040d540303a0459120607a52041d4010441c040ad0606c22500a100c041e07591618001c0b054450f4125108003420890b0040031851081001c03490859034103d40040c1d07681303060617038120b081942c0f140381130241410168403401d91041110b603400c50201c80c0791907891013504011390f4548825110b420107550100499010002d03401007201c84c69401802501c0d140d07101002503181400c02040300084a0003041d5031195492014072462900c5d001030035143c2e010002000110f85417844401003500705488804508501050610000c007180400d440e08044003805004150b14299461080300c03440303d039180c06443c100000c918 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 174169469 1250 174168219 174168221
    0x30d02070c182702090c0306011106160e030f0a0b13150204060906030b0a170a1a06120a05060c0307050c0303100f171b040b0a080a0507060305160f0201 67
    0x1004240c1400b110320200800d982810241860011800c82442d0320302001e260955012008000035401800c6407140356241500c00b00c107075002401d424107002c648540314820040410441d40b150a584030301300c15460800380050300401650010a100b07030041c025160140c1000070748910000c3d0403440350b8043c1c1d02d80d081241d2000e440010064040c0908401100381c014503600144210f40141d5921814240d58001c220222820704100940c4401000e008000783c3c1c1140803d08103510300c180c10b44500121075030361f0481710035441034107850b81101c078810410750346824140600342502d504040e1250101ca5911541c40d481e00802d950580907010010038000d500c41c03410b486108080ea01100e40d20304009402d80030140e0184070b142803409400c1400300e00b452002000c0700b10003001d03000070800c2d00c000b51440240d00f100c0c0501c46400582d2000e20324299980c2500b0007008020800107440040c10702c0c2030041c10004140c0049003810304010134400c4010000c00250203c00e03d51130400c40101010b40301b01c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 174170719 1250 174169469 174169493
    0x10b090906040b120a0b09070e060d020108040c051e03100908030a091104050f0901291e0a1205011812260c0c1507050306010c06090501090f1e05030d0207 68
    0x3c1000c0c0b117050403200403c41744c4059603004580843c2110301a03550340307080b005498001c550302a0010700354a5044015401381c2c1c1880d0704280300c0c6a00ca000591100301283d8614002e014900c05411080003035101801c05010070354006941c04000d1090456546940d4940d12003e80342060a43d0766281d4007051002508010001e0030300180180000d0821744480310080c0c50542c4d00314665460840d403107030384415854404804044000d4442c40710010641001800f102c44a0301641e0044074401c0070100d46e9800803020007030100b211080904520070704001e800c580301909400f4203c0505215a004694030740c1003102000018500032840f0020441ca803013600103403804c42c10400100c1c80510070a5100c14016040101022049070030010700700c0d1203103000c84802d5030208045441003020500340e511900041c420180075890100d8800d004c0e590b25402c440c40c1c1502654500340f910f94060030003ca003000005c400c401041c0501010080b600d0301c944a100b14410790035038a500056000812420035800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 174171969 1250 174170719 174170749
    0xa021005070b0f0610030c030609090b0103050d1106060402090301020c06010609080f061603020a09030c0e0a063c050306100305060714040909080408190209010b090906040b 76
    0x158482521104040c0c52604051000c4a0b0325140341c0001d1083c14034448101c0c420080200000313000540d000d0141e00825400c20b498080544038280401c40241502400b030105125000d92a115855401c059013001480d007008420444121000360072030a0002d00c0d640c10031800c03640141c0c0c4060314000680284109031940d100d40c021000001500d54101d04400101c5480c4000c0e144140c507950485a115a400c641005000e074001c90090040e512036070141101d1241d82c102490642c1d01ca448507040b030501e65110748040056141001100e502501580b00204400420481d44d6160603009021a20a40c03082489244050382c410b03c0402c80509903400400015040d1400c0c1d0902c08600300c0c40440314042a01c01d41b03e042c0200d01540c0c400c0125140c1c00d01d107002c2d400e0906050201182c0900340307654007903500e00828040411131160030300c1441c054048030100401c41c0342c41c070b10600c1401c40c0141e114051148040c01400a16141c9040c20b03640310004590000b29005640c0c0050400442c4c4996 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 174173219 1250 174171969 174171979
    0x20f07060e010519090206040905040f02060408011e0e0a0312110f070218101a0415020d030b091902030408040e070c0b011a070201111509030d0501091401170a02 71
    0xd16210701c0c819031005000d94100e080034600301e001c1e0000b83d4291404900b00a4100700108800c0010080b15846260064030509403080c2d00c048903000036003142c0294000101603591151480c900078003a201c80700070103800c54000d0200800024101341c5510007aa000342c14000c01401c16098460b42d42c1c802503444140c81a0a5141c420079038a0003825004000d00300d00170040442640d0111150b1650b2500c550148401801158204a00c040203072011031910881220305000200d034040e011100101e894109174000e000e2401f0140c0028103a400d20840c0d01d004880b22024041c80c4c1e0385284c0404207081500350056178903255480c01841500c0b540d80b122940c00504014082c00ea0350203440c284c4103034020520415540d1b00c40c00d10801c081c0b49059080d071030001c10015000194040e000c5405803641e45401d0b03a088c0e600402d254800c101c82150031a80340d4000189125800440d8400c0c2c40c05070550090800030152514004059030006000350000c004510200240c000380400c40b01915179800f0b02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 174174469 1250 174173219 174173231
    0x6091f17012103050d0605191e150c0f050a06051f1a0703020309060d0c11150105040b0d1709120102030903030604020c03071e02090603010911060901032a020c1e04020f0706 76
    0x72350441100644c00b0310b14074403007042613092111000c48110800d0340c91101c00c007061070020200640d220b0980100c1190705003148402c000c040f074400e1040d0051207001d600042500c4c0f801c030800c00401402190364140d6031044480030700030120021103440d95944000740706540c0f1080746c14240d245020300007020350700250001d8040101107054214806089054884c0032036100b03030381c190a85801d03a4014104401f040200104030601c0c050300100070141e03006d032001b000c1c50a16109c80ca031101d076582260040c048000380c10386042c180022081b410740030b080c00840c290305003003410f07580702e100c003400092081c1d401003280e10305003d00380212198660b00c403002803003000c9440390714038451510301d40c140e1060300c008001039214201800780c1d5aa85900c1a141000c500310181000800c1d000312020030304250b921140300307402100c00701e444946d56045231206848a04c031140024503081004075194001c25412440c10f04082d5003400c1104c03400c40855026844103a00307a0300030414005c4200142c003e500b003c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 174175719 1250 174174469 174174499
    0xf01020309010c080603030a080718090c080f060d02180c190201050a0605310b030d170106030e0607030f02190e0301110f070206091f17012103050d0605 67
    0x584500920f0000742c07150141e0399103004c2015140c0c01000041d4000c50010b00001da60030f885050035107610f0148140d1560303020b440310144400c4801e626540740c04141c20409205800c0d2144003401d40c03100084640b20700062180c0c1c0403030060341840c20f0070802c42d40c1480114408880300d20a81e452013030580d002001c1c264400c42c0080c0640300a94100e21060b00d012404030311424440203c0880c20f0780c0014058481c0307002400c8104070940118406e101030f0b524600d001036035800b40301d45e103200303003650340d612003e0001d007400a900c14206902c407000313040c039040d00099912004107049900038070900b00050f01095a0500030081d10600d045401141c903640f14030349070150404d01c083e000110a41c000c016a07103400c119aa110f20529014101c5058107010380d00c014901000248460f00c00035040c1c0c0381c2c0d10030201c0030401403591400002d010860801c0c07006404005032901900405c00c884081c0075103a41105030102a03d00058042c0030410005070390f0b9420303030050704004d00a020280c40d070071611480d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 174176969 1250 174175719 174175721
    0x304150b0a03021302070f0f12021203180c0301111804020406080103030503071e0503011e080601150c08030106030506100807082d0a0e010605010804080a05070309032906041e0e0f0102030901 84
    0x800348c103c2c0c800303466005c900441b510005140e200803080c50452031442d00c0311212404500207043c1304103e01d208000e4800940e88003030103018441e0300c0741c09009880d05040c000741040c0c44102e2240324040c0e48140010401c090384900b541c2d04481c0c15091040d920380318090100d1300c3c00398000014000850701104e10503410703805002103048410074402084050070680700301001101740c0c440c9840300d62007940180080d503050781140c4100c142c2801c1140c8104500c1c0c2d1000c00c150000d07402403000c00e94960420203642048024401904041e25081900b86050309000d0403000010b81304050b88200301c90619810481c42d50f62011005501c0121403107450107200050240c241b00314102420f5081040000301540181c65881c090703a0700440190606070207110854180d046058150104174480b94004040342c2d40c4540b0801d94000c0321200c400d01c000c00e14040350001805003046024500d0b014610b21a601040144100340812070700220700d4801c1c0258417031420001c0c403e000120351000007484012141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 174178219 1250 174176969 174176993
    0x1e06050f0106030506030d02070b0a110f030403020103060e0915040f061404050106080a0309090e01020f0f040602061b030a050711010f0222050a27020c01020304150b0a03021302070f 80
    0x2d0380c1d07803d01151350303800c0034144c0790b034108070010001d07030300262050200c1c0a44c80050401d100e4280f9141d940031142c041c4051410b03608502c0303960141c00001e401d20079543c0c0350040780040c03e2104502615800e00f154071541d20235507000303a20615a2490045420400d58030079128003280c00c07140c00d12003155094102c044010040c2c500b101c1a600e400e0b4001103002011401c04030b03d84d0140c43c0c180441c0e19010742c1310302405100440d640707555400c00041e01e020346060040c2c1400024444110b0f02d80f424948003134500000a00000300c90070b85800420a580400c00c2200d038020400a4040303110340781c80f1b200342c814a4030030143c61080d5003014610120201c0c0d41e409040d406202d0000c06421425200c5403035902b1483d0301810f41c0242d1916018806c4804000e00501c02c0c240b40d085440040c030105090a080340c002c00b6505071642d400105120500c641c2e48110b00c40c0021000b410000440940d002629004040c48000e00035400b64102c842d0401d499816112843d40242c980c4034500725518010b03011040b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 174179469 1250 174178219 174178229
    0x40303020d09170316110a0b0a110105060a060e0f030607030f15060f0f09120b070e01030b0a0504110f07060b01020f0309010f030902030316150b0102191e06050f01 72
    0x14a410006024050300e5600c001c3c0c00003000145142010950070f00001080d070001c03e540745107200e600043e443d2281c429100081c441160f142e42c8620070f070070b0020010f000103504c81525030305240070300005c0e542d0860700200b194003a00b00110401c1000c40418a045207200c1101e9050103a03004000d5800d03059000540240e24190041000c2209204c0b03c903441070b1030f07001c1e120015114005400926015440d080302c014814100340444035901d400749d0710090719030b800c01c0300c4807042081440119a00314068010351807007403c0900ca404115804542c0706c581707a102d49441142c540350283d00d01c1f4100d80031145480e400b40c0030203a40303d9581c103251010b804010740c007a005210b07001e0313811000702001c0203403452032005a482d100c80ca00c101e00118064030404c0010f0783c0c103020401000b400114000d481c80900d510420180441c5400045510111043d01c18880e0641d00110104a81d0b28402e4450061066000d050049913070303084d48a0070007091050320010103240c5010103000c0d9078840e2840e9541216 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 174180719 1250 174179469 174179477
    0x3100c1e020a050a17070804090b0108010801050609060613090204080c09100b0d0207030302040e090c19060c0b07030b030718050604021c0b01110307210503041703100b040303020d 79
    0x348a00702c0c0e462500790b202804035080703501342000080068584d840d0700303a083c0c848a03046c601c058481403050392180e4420003a0a60780d40d0703d094a5600f0807130227801001550000c2005140040c080390144000a0025218640020b94010701c0e11071031402c4000b0f40076899045444544030f1504a80d00e00c2c007999100c5c821090440005d480d10a0f528900b0309581a0080507800c1081e000a04006500440f400310b0506030240700100d9030341a01c40505100b096190000c00e28a40c60105000d2140c00f8803000c510103c0901c1801e122050300301d403000441a5101c00907102558031004128024940c1f0b00c0484e82c140030307003503000410180c80c406150000502007001c00c480e444070800c00c800c03840355500541e070030403c841e011218144260b11901907241c044c18802a11010b00c0340d0a800c2d80c0c00030008a644000d442c181c441088045400f51400c1c0256050240c61424a0340740d695002c00c10313102c2d00c2d204207030000006030391044031111400140180b0381c0d00d42c2c40d641c1301c0c900a5241c00000508200003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 174181969 1250 174180719 174180767
    0x30c070e060414060303160f0b0411120c060927010807170d0f080a1401150801090b0a030f0c08010f0203060f04060b0313081905070302100c0801060e03100c 69
    0x83e88419a01c0c2c0901001801149004403d0b12400d1080c070340c1a000703031400360003401382001203a401c3c0d840038030030b9104000d991a04a260b1041001c154042e0411580940c468403640c942601e03800122844480d08803203800c0d0b48002004c0c0000c505c40e00e942d10b140041032001c000202103000091800940d0050141910a494056000703a902d41c0403068038000070f114182113000d8035004402103500114611000310b02026500c000190707805080c1e00c000d409103503d0481c407030b02030f600904442c050700045100340702c00c0303030300000040711049039000280404200c03003850700c10003860008240c02007803554000d001c0c0c1941e01b0001402904100d80540c082c0b0b0f41c40d4800d2030580780a204600588100b0340840d4256264204170340086101b016084130b64260402c21400c690380121807011020391541d40f0b00741d03250b00c140390003800e09441d1400300001c3c03070924041c580c246800c280954150b400300d00e440b2100c05040740c0007074900540c4640d00c403071851501c031264140a50080c401884100c07803000340500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 174183219 1250 174181969 174181991
    0xe06060310110906030403030b03060910200906090315041b0b09010206041401060503030d0e01110c0d030f0f0f0b010f090305070b070206040b03130b0a06081e030c070e0604 76
    0xb9180b5865046100d0b0038100244a00c03803802c0006150400e000e482c00055041000f004a842e0001c143d41c03442c0d071907002c1d0315100d1502401b401491064822500c07904030b01140307400b503a5260f000d070f01e005c1403207424042060b0565440800ca91005142807002107840d40c241400c1010303090b003030120707168080c03000780101056006070603007100c0d1140c0040e80141110750760707501d4179081940d8000e0400c03003a542b03907440080c0d150341c200081c2401808031000000d9261518000c0d90840742d54a0524607046d00501094034909004550080c102c40305040103e5110b66030b16882000389081985600300d9440e012044403600d0695100011301c01c0c080c0c13544103000e8a401e00503604a03403180320081a0394001c1c8811f125410701ea0002e0500c480c40944640d0425442c2c1c1007400d00c3c2e400c2102e078801c016016403098801c5c044824981c0b030300320400c0001000b8140c01c1c82e03003003900c502e0a440c400040025007100c3c000f804c0002c000300c0711981e43c0c0c1400e4070300454903a250311404480079209184518100102521 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 174184469 1250 174183219 174183221
    0x9021809061e040b180a0b03070302010c031b06110c060a110a0c02030708120d0c1d09100305030a0306180605010e0108071206090c02010c020d0509040b04090203010e06060310 77
    0x10040900501280b4095524601c40e42000b500c0115150480e0310340c0a1022181c942c46030641d00f41c00d000c1760711100c52078142d0700031041381e010b040c1d024800c2d80054020400750740c20010541c04560540392080b411802d862141c40b41c040300d0080104a42e00d481c0040c030b46007003220007519885458200b55140754460070084000d0712a14031800c00030303000812403c2459401404043c4015102505603902165145451410b2280d507082c41e040c222400540e02c0880700251241c03500d04d044606050b04403075501000d0302400c44094140501948107003003c03805468400d4141c900071a80700080b80c2ea1394460f074070b000f00501a41d1150303002101044881d01c0e4000c10500031842901d1060f5076241d001d09519004403500e200283c502020321840d001c800444c1d14090003804090b0180880c00700f91a10a800300900b16030b000c0b2941811074002d6404030148527841400c5803d16082100c0100ba040c1c800000035000303085071780000b9031542ca44040030f070440308040b0383e2030710400302181030340c1103850703c4a2114 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 174185719 1250 174184469 174184471
    0x81207020909013e03100314150a021b010903390b0601110124080d08010e0a02090607052401030c050d0609050d080f1f1203050705060109021809 64
    0x2121101d00901105400351645020850412000d4002c00143c066040c200c04c2c0c6a2081c2e800b00e07000412180c0c1442804808045191b40003035000051425540d880170400c8008000760804101c01c4d000100f52030003214064a4504c048178400082241c100344e0714000e8005208801841c282e42c1c40505284011000444c6502c0440b540180e8040801020307034035203034000d400401290607c09480b81d8014404000d220304951444a07501062401400010490103c85c03d6032000030f59912a03144512170070740c40366005e811100d11444050044d00c442203820041e0144031407075900032501040120520000080202140c20304410020f00d0300e60070922550242000d0101a001882c11901042542082e00110b04480e0040d50002034182e4180c0c1d40b20f044c12035140306400040d01800503c503104c0140c1c264181c0186183c10300301172054a5141e590140b00a603c601215105000640c0c410f050040782255030342503100c401d80c0c1d090360711420060000c0d0031101818846640000f60310425040140b501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 174186969 1250 174185719 174185741
    0x2060a0c0302042409032102190201050910120c050d05070c170f04180906050609070914030f0706110c040204050609131b02010b09060f0a03120908120702090901 71
    0x800b9072134032080101e00c5000c40d00c103500e100f081104440000030481c40484600c8100007a581a0898960307400300900d0500060310b000516104030785801c0041c1c0c0c2040840310a0a0203407210b0003003501886040c3c4464040e4241c107940c50341040642c840d0309078000020155840440000c00c110b44840c1d20481d45000701444c000c1c034161141e0200141003c0001c05820300303050408183e89040c0d00e071844084c002c070121503200502a1a0f07060300742000a54002c0590042c01501c2ca02c41c0c0b40360190000b04020004e07c24a14501c40c640c6503000c0580303091000d00ca200c6150000c96000c50340c0c54100400c0700d08040c6c4600b01d2800766030458141c902d0103008407403c551004240c542804101c40c00c1050202a0030710b00340b41c256840382080e6201d00c074414441c0c4ca6110a400001d40340003440107008144800414141c07003041a0042007032301d650744a500000380e03908081207949046039030f5015510010346030001c2d0014812000c9044d840004080107081c1240300341c034041c5441d1182c010075801c0c0c030300541c11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 174188219 1250 174186969 174186989
    0x302040612051510030213020403030806190605070501021603021509030a0509010e040219021f06030506010902211906150c1104090605010f05120607020312060d1202060a0c030204 79
    0x50000c0d01c804501003540c011013003903500c0c0c0e000c035520350001c1c2e4040c4540c45204030664010408000341500009800e0307102105840110140f60910381000d0350850340c2c003c19003805000705254080c0729096050b504030b80f1501c103914a00c811241800380d03a490320800140690552400040c1e24000044181c8007140407a0700c5003800c01602000540700403078852615500107034240701e03041c030400614108284814094024050b4200d00400c040c11000745010300492007402e0000400000c0c3c1c0c00078002e41100c80c9084010b8490340080041d2098a03000e060311000c0c041002c2c280000b00c2e60f000307001d08170103641c6541000b105030341d807a01b00034509020b203c070000300b070203401c0400210306269020780301480d000b040012036075555501d070380c01c86500b82c00c51190b810b42d12009010904255103454038080c00c10300100294546110001e649205940c900e00d64007100a0108000c0d07250a090032440f95846403070290050402d039030095640301c044038412070072400c0100034942c00d8001d00c2107409407004010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 174189469 1250 174188219 174188233
    0x50d08180d020409110901050105090a090507090f0f0e1303020a022101110d0e0a120c0501020d020a0e01081f290406090e0c0306062502100504030204061205 69
    0x1002104a11035002240c00046a01d031110041e0b949100d11101d540c410705210141e0180349040c0502901e058219605021040008030000d0f5502c241203001c5a8046030040b40c2a52440d004490254069008141c04603401801146590105030500f050700c40d6103030040000c6c1da850600f00c68040301581e025026170440e41c1c802c009401e10f915074004400c0d00714803c108800602d45560308485984c54211690303c408a0311040b092107500a4003034641c22400240b14540194840e000104c0300c00e04558103015402c9003040404c08290182e544220424004540f650404040500004429130103240010117900020b10045440600800d15035038500b281000c2a041064920640c82e80060403110542e03c11280a62092003500510151403550703100c4a0b003600d0300c0303413842d5801c40241514040d0141842000340e252503c00a6500000f0f2540c4a0b1040d25101000c0116001d60102c0203900001c48520510342c0d6a0004000c0040b02c0c420b5400308265940e9803548070041819900040c003641040f8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 174190719 1250 174189469 174189487
    0xd080a11030115030b06040602010c09050316180b0d0b0403030e071809050304030606030804050117060904031202130b1804020304020d03051b030a0206011511100c09260106050d08 79
    0x18183c00320302009420000b41c42003810001400c0358116501c5900141e4545110b520002d030310500800041a06500070040c031032841003000707080d08190042000303809146989509030042c07a0020800500007401c6803031510f0b0941810300c000e88007160140c01207820250240d0740f00e48009512800c407503c08151002e0040300c0c2c5200c038045c2011080983d81880244004030201300c0d076205036002940b264080c41e998a1070000003500150780c04212094120100082140c1c80c0c56450500b58800d074580740100110038200d90801c024003c8240c0300000500c9a08045034034800500102481011042c411624001000400090348411070b402504080e09500c00ca001902030805881d03000091010300034a6049001c2892440d04280e0328100140c4c850001001140c0e58280e015103286c0c0c031840d0080d0110130207000c40c1d5407003c01542e043c00440d9030b140c0c170802e480c0c420f1214802500d001c22009100c88584804541000c80c101500c8c1404e500e030000000ea5441c007070b8110107209510641c01410100340d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 174191969 1250 174190719 174190739
    0x60d1101050f07020a0b0c192012010c11160513020304060902063405031207050d110c0d020607080a050601350c0a050f0d1104080d080a110301 63
    0x302c0c54520b0059050003110016951102d22102901c3c0742d02d802a04c0b9490a150b0303916000d07c40601303100000c403001107040032a894840e64210800802d80002800d000713900803071034050180d42505603039442c1125035942a603000d10400c880c100c0400031101112003c2c0e0b15407a0341748061040c0d0f80c0c0301b0346007205200e1990198003d580c2c082d000301000105441c45801140d615407014543c4015205443d0010300c809402c194605921a4040c20500c1007101ca0387c0c1c1c0c55520301c10705658220300c8024800003507a0900c00d40848000301d01e130f41000d1210030b851b01d9a5091907001807259499500403844d619000b1440010724030701c1107005943c0c01107a43c4a61a10400801010348030904118030100c20001d0001400004041070403144082d200c10344041941564615000d40500104071003041409010b030341c080156400d06148405566031007441d05640e034000e04000700c04404400b80403500080c200c40100e151030381845244c446019603501d400d000c0c0c044a0004200a00307403c0280010301c0311141c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 174193219 1250 174191969 174191977
    0x702070b0d0b030102040b07051e0303010b040e0a060801180308090312070f020a080a0c11010e0f130e060408030106021608030a35060f030c09040f0201020312040501050f060d110105 80
    0x103000145002d40710f040c4213140d54440074045e1126032040b840d4100484074088090462b045440145045505005d05503c961065101d28000c0d11000c10100703226040550180c802030240400030003103042c082921401d10f03550340c10f041d4049070301d180000d0505c80010044650b001d594040050255440b00e1090390001c1c000c040c06000c602c078102c00d070f40c00100b00d034004102100b0700707460381e80711518580f030002651800c036000305040000250150b4080e0321404003803070800748112050340c00d803101d8041540060010001104543c4503c000b0300c418020301c0002903040e50311907420b4481c0b03075604032200d05c40b01d4071520442080303910400400c80f01611500f400c0c079051824042c080c55a1034040c4100040c0d54203010490705640b9038209029851402402103c1c1102c8254098003c0314040c00c002851020010005000e51217610141421a07209008444462a402d200c0310504e0170942001d50003000c040340c220054222032030110300a031801c00c0802140030380c000550440054524011691500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 174194469 1250 174193219 174193241
    0xe0d110a1214030c0306280303111014040c05150d090311031812011125020306070507021527041107050105101403060117031c0e060702070b0d 63
    0x2c004640070b980b008040000c50042180321400758036030070a00100140c0421100c1c41014010041d40d40b004641040524101100d4150401c00780458201501e241050382040c140c0304500d181c00115030180001d140c00501460003070421507041a16841840428044200d03c0c09800c0c400380004881c0a0071034029403403003442131411200e20300003860f07480e141d07400c2510070304070900042d07a502550381801c0100405a41030301000380072141c5a800c59081c2c901c81c200211150000707900504001c1032034904c92010042d405400c84140b403410000003052600190812071044900000022410211a05854000031041400b11440c900e50300c00f0550070000e0b11a49410588513040981003401850240003924048c0001040398508460080b4044d03005400180706185001d80c9d5000716280003545905681d4494110300280d0503030b0803444d2440c058000c00d840f0455401d080c01d0450005600b14082138004041225140c0c0c55940041e40c5034112402803288025080c071005071914855044548510 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 174195719 1250 174194469 174194477
    0x91527130e160806191e1508120c070e150405060a050909100f0204140105031e040c06020c040c05090f1f0503060901090b03060402090403030f0603060e0d110a12 71
    0x182900408542c94001c2e801032206810400801043c2034900d800100048240c100401958400e105400c84058010420b03055403a6500c0602c290b400d4201030100c0034280703010860b942031750311068a400315030080a002e01107009410000410300c24640805015005082c00c8100c22070980003840000c1400424140e0b20103083c13007000916444d04490640a2014078019246840d4840705510945000c28000d0ba641441040104450f0020034461a0180824a41140d41e52154101a00751003250001e0703c5442007048240001c1050100c03a01c012101c158007500d0111140d0007c01c0122101d480c40f40c00440c80402071401c40b032500e00c415021000005102c5601703c0784030082012401d03140701080b0049840081800b0140c0f0f841080b09004245442c13060000c4246180425204e01c03003e00001d005001d81c40c0814201400307900080c070800c02c80e01d401c0045030f660b42890800380c4031000311001507020303070256503102c0c81c03140464440540740a401884986c4082d5100c4001e0b0902d411103000704 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 174196969 1250 174195719 174195733
    0x50403030302160c060302180306040c050909100c02010b040605010813021201020403080c01024506040b120103031d0603040f050c0607030309030e0a240203091527130e 74
    0x1800305411384080c020726580103071103140c7c8901d00c46100d101c02c3c904500c01d41c446030400002814009a050580380d0940300301c01540c8a112281e4507014000400c01465410301d4035000c8100d50561110f0824201142c1c02e03c945565500191916141541d20041c1241c040000a0250801000c401c49044007070000614240e541d40b41c007115600500030701c1100c2d03500050390002c04426601d4081e5401b4401d01320b103882400d00304040388180c8201c1044140c10780707464500d1103a0b58420040e9801070042c5d0110550f1000103a140c10903052090000b14085942800e5070f50010f0140400340288405c0541514590344541e104da00c0c43d00d031250821100740c81006052201622000d01405241e80310f0744010a06440310b1801030004c8036400500c50180601207400c0041801001010381d0304031180310208140381e4694012030441c80703424202d581040380f000e003800c5d030b440c0c1c00c030014081d8000b540001810665000d01d0b403000c0501c44451a64016207180c030a045000310b42c0c0c400440c00c03070054211121 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 174198219 1250 174196969 174196973
    0x605030411120706080a0b0406060503070320030117010606081308072607050f150103121106091b0402040305070e1503060c0a0305060a1a0c01061701060f09090305040303030216 78
    0x3e0a403054000300300040041081c081101000d01441340b440804480900032242400c1c001070280c04010220f01c10103845850300446443c0c41003180440c50385190b4125540d6031200c0c0d07090720310180c1011500043d0301e810000601c45100d80f1410340190b08035090b04c0482005915142c0a98100710826229981e0b44c0c1071011685042e04058440c02c0e09100401d6113a06544c10001d0900c1c0b0007903505400c0750070208126900d40c0c1e4121407a410f5076441040990040107502d000c54096800c42c0d4001c105216100c03d10545060001c0d207801031307440d0308240c5440ea5035100180010380c002c0e44030043c0564080142070041e2080e5505103a4440c0d031002c4007102c000040c100183c9000029105c0320b031000b8000a0120809605008455000406a8800b03d42e546045040a010442110081200c640100d04020050401e4006100a000488044080d15035600a00f402403005100d43e40d03203206200400030b0030345401d02a00c4061601030b102d0038105455620705601039800110360354440680000c1c0500 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 174199469 1250 174198219 174198223
    0x15090c02100f061d0609060d0302010e0a03080114030309060703030513080d0501091415010f020322060f0c0521160302100b0a030507050f0d0b0112020307060306060503041112 77
    0x302480c4120001c69458542030303854604144e8030f14200030103c80394082003401e8961820054003d8400c0e40d40200014442c141240140540070480d801401510405014198841740c1e6505841c0d8901074440d40c081c0001c200740c4d882c400d902c08141c01207014402280403034040d601c100d0380309031440744401c0030b012151b40343c880540c031070f10700080001e50790001805400b1081c03142440760003210304400c000b414840d0401760f624082d40c100e03e042000d400c840e182d0369403003402a5411003c405078071008441604450702c10000c00c2c1c2c05190001900c482d900d80120b41b141202082490b00a0003602c0080c001c8c0150700b240c000714000001a18004002e00c07008400003200c10b05000307009901070050200c18040181c00d880c09205210312461004405101040700070980c0700c01c5a0342100d1411000c10720f0f1000c42d080380364804025104450710400080c00120a0f858891114400c5058405190701d0b21070582c201c4000d170103802c000076402e000040005080400002001c10010a014035115105038071078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 174200719 1250 174199469 174199481
    0x906190305100507080405031606061703030117031c09020121050604050601031b03050a0f1e230f0711070f0801060b07030507021e0604060c030e030115090c0210 71
    0x1c03000d521040c2c4a1160038100e12409420452500c0c02c3c009a08181d19126524020340d4503600080c6000380b0381e401044041d900c004020030040105c414550791003100151a90800d115411054008056211002d0808021514220301c103440150031800001c10180c010100d05c00203e05200d603148100c004030b01280c0070711200b40705d224008152440c2c00300a00040d07400241c9041d05250070a610321400c21700c0890041e800107120b150010743ca40d9122404c1c00509101800c01c0245480c01c0c00118150300f13022076101d180a41e40e001404601c1c90010a54905441c42c0c10080b03800e00c04802040b00c90a6140f200d41d000205481c05600060744094020309000003a0300003e12225076040410984000f07001c0c0d140101000c1a6541c1045400c2c1c401402603c15810000e200d103c00011200f03000780c1000244d481500083c14003502c3d01d883e06409008051070040c2a03010990441a04099280c140a61000c15107480100c940c524542810a806050846060f50560140c100e59101c040d80034401e907 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 174201969 1250 174200719 174200723
    0x170f0102030a02040311010c03121a10020304050319080a110a02031c090914072118021f0e090c040e1314030a05030601051303060c09050307060e0f09061903 69
    0x42c1d03130f2032031803a080368180500705200c0d040c40000a0140c01098000407010b900041c01070010030704081e80079001000c03a40003420f040d4840300c000050a02142d0000141054038020390403200b400352850f00c840040485528000c1c05008100800001c0d44c1c82069503281041011045682c42c040543c00070317041041d08040400d901726a11001178846500c0301a003401407024079410011141c464680d86a0600c0082c910b000b846154050b00070302d290383c0c4803c0c407500d00750508200056080c01e01220703180c0b42144c00036031003083c1000951140300295003614100f43d03919100c442e1a40d20480a0240d0780030010040902000c0a010014410341ca00300c0d40d0744074180041c4100c1c2460050f2611008104040041000603030041c441802c40a1f0400f044030f070005824205103454941e040d100001c40718003608010070b402d05108211076590b030440d500b5001d40d60f01303d080d2a0440d8441d8030403100e1207101c488440d8020000500c0008600700074021075044803000d02142802d5100b80d01180d0802000d03402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 174203219 1250 174201969 174201971
    0x10090b010c150912110c0904020a0e040305030a0b060405090a0b120307030206091b0a030807020402040f080c15031005120309040912020d090e010e28060f051504170f0102030a 77
    0x508030402800451055600f081d82c05d01a8640641c503281683e29507000c03004501480f4144c000c9000e65940c000c0180040480c800a052a40351502c0c00a002d5007003902c0d0700701c00c07609125100c1d146207031050549064803c0034140c19200d84d130758040d070b6010b010b030200100d801c010b1038000fa0005000900042c034019021380c0041200e407e00c03e03000d9181c41c441d03260486806e40c07a000a2001a43c034602c0c9442102c3d0880304443d03d038940303800040c0080c07059500c4030b68029290400041ca401010400300c80d2900d0494800b60180350103995103e2034841169883d0030100c00b00c00610451500c070f406003401050340c80031242090003d00c0410b0407a00440b1050701c0c1d1600044e00315003072683c100300a0070350b0038080c64001400c502d400d1070000c9041042c0610003007644214009110b011515004107a00022451109078032008541c21000404890080b8050b80c621028041840e052415141c04000b0502c00341d14a400d207444812603101c074416403980f07902d0240c0e46507004200001d001031402841d00d200 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 174204469 1250 174203219 174203231
    0x6090a0c2f06060402090d02091513090b0f0c0d0e070e010b04170114040209041e110315060d08090d060203101409090a06050601020111030a050405010b010810090b010c15 75
    0x725407440c24000400351407203140100b140348015103402001001507a416200c5c0314240d03d0380e4030442e400d8400c80403003036000b40304c3c0310000d000c50388a60000040c0b28003c4d030040c2c055846620003c1e601078000c450076092000304000360f80da00800d41d03001da0410741742d00b000d445c4c101d030b19025903849001c1c0a910206640502140c07e11065107140c03403110310001c0e060000c02500c041122000c0860500500113441901d6890004003840000e10003500140c0c00ba2500315026038251900211081c0403002c183e01922444001440103882e10366014003030708004040200110b00c1c0d41d59280180d004040c041d420900000150300001c03101d00140d801400c03540403800e040c6040507082030b82c440300580d44900ca80c0841c028460040c1c008aa1131000da0b400002c0440c2e1591101d0050b800f6000481d40b0180301040001045035124055100c01d001e2881100240640704080e030046070300c0102951b19862200b2400710822048940c2d501c150021a0181002c6c84441c10b83d850740d00c2031403407032345042c51000d0310341c5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 174205719 1250 174204469 174204557
    0x140102060c070f120306080a0506070e01021b06070c080f06041101030207020105090d0204021b010b030f0105040201090612140103050a05060903040b0715110a0c060608030306090a0c 80
    0x2205480e4800c29241000d07040020b00d4030740746242d20200801400103154420240030044c440d0300700c00c0c0503104041c1221560509403404681d125812030b43c00002400d0000c2c4142550710124189000d05002c4070a2903501040c0d108004403030340b2007503040b52001e000a00c0098501000c0c000c1210300a0581c02800d400d242c981000d44802c000a5641410944100702d00e0005070f812605542c204001a02c2005030103402d8804034009105102c00007104503422000b0903a14035054208900c4030b5403d030261514443c8010000e4241e03401950000d0101d60601824000c2c0d034801c03548062904441900030038000e0341101c5480c1c40b54420b0301309440c2c5030000007441d030902808015103a00800654001c40c60245020344075007050007800c60003491002c4510074190700040d00d8000607c0b9400e4251038503513840c200003001c1d001291000c021190745090200c00070f0014000b1060340d00c500409442208141e50710074008004008440c004801d100e90a086e000c0d0400503003020400804441a1041d1340c0009a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 174206969 1250 174205719 174205723
    0x1302031308280c030909020a1b03090f0b070c17070b0307050904090809040c020601060906050904020910090305061315020a180308040603060506070c0902250c180e061b040f140102 79
    0x51b80000c40d04034010030441c5407599000214642441a80c0401300d1485500d14044071001d489030b01c11840301500720b2003c00c19000c0340f0002c0c02c0c15407290103001d5520b59160400d006500b8080c042c00c420fa00078500c200051102ca0b002107920901d0303450402c0c503100f02c0303c000a086508200c010740d840100420420000d083c61b2042d502480c80030f0000b0701543d85041d40040172043c09001345000c02030007123440181500c4640607191440d5009284c61000590560300601c64000c52109840034400e0501081c4983c2ea02e030205d01d80d19420a840c00086a420300c00c010195102c1c1c1c2c00701e030401c20710744001041c104200300d0003c0910f1140359095038a61500c4001000e6940a410580c4925010040d80d40014601c40030041200c0060401589030751440007134180d81860307075980c0180815509515410000f8684400e02034400e00007088208910340c641d040103c0f1400741d5145003962100b400328182098802d10050007a0401010174503154460b0782d106110b4002c0d40c46104011107103030300240f541da01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 174208219 1250 174206969 174206987
    0x40f06080117061b13170d03060b180613050306040b0a0f0e030913020927130206090d020f040f0929010603020a020715020a021302031308280c03 64
    0x41d500040c900da080c081560104003115206118021a000400101701c00c4101ca0ba54000c09a50844030000044001010788a003500c040b00e03000039180407070201d0004103610a45a05050074040c0161039600c0000f8800241c0c09a120310880d00000c0d0300c00034099808006a41c400c0e8490b0041d091581011038408007035620300303c01c1903095410241010142c1900009071b80f00d05030704075a403000c1c0f15810810200203208400c00701c0d400008400c0d00b944009102040180a5800c80042000366580d00038603801c044420380001b0342c4444200600c20071858004c6001c0101e0b40010000006801854000f80403a4118070621a046071a000200c0070300c18902841c0440d0501c40032070765403049d040241c200b6184d805014160a165012581000701d41c0300308000000b038602c0c0e0841c0004042c10b100301954500814004921640384401662880172003030096034040c00504402130b01141c0d807995243d9003138020341012064a45d010300001c0e0240b41880d000503107200c1644034480b820800342802080748031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 174209469 1250 174208219 174208259
    0x902010e041a04090206120126010b0a0902130e011e080c060307110109020a120b06010e01051602011701030b0105180702060103020d140f0c030c0109050604090b06040f060801 77
    0x115120441002c1e03401071090720300d081d204990009002a0503c009400c40c040c4102c1c1400c003808482c00419100c000401e2200100500125241242e465808031401c0c2c445020b00941c20469809082000855940203442d00304480244c0c000e081da02d4070250303100090300740d0002c03824000411107005282d944080c4003005c0c1007002c01904c2498084000700d12240b00151441c8208542e5520a009101d400c2d0f02c040e52003a8024020711050740c0c0c1b450500704941d50188181d4080000ca80411030641c05100b000f0940c440c1a101c103400c0c080825008848a07c400030141c1c1800303a140c100342a20909101540d020394840d00e40a1402c0d41010148841c0345141c01c0b40c4640c0624610a1000d25a0001803031070440354100c4480941c20914a000d90002071100200308251003040c1c030003c00c016000c501001044416411591140c5000c001111038040c0b40c440c40e80c00940c00c0200f4425240075030454402d0000c050143e43ca800c0c0e6541e003162056203107502010002e8980001408850070703801400707500751 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 174210719 1250 174209469 174209471
    0xf0c1c0f090506120c0c0a05010f0f09050a0602030703020405040207080a0206070206010f12080904051602240c0924030105010201140c37020a0b0a05160e0102150103060902010e04 79
    0x25081c00b02244042c4142c644001014501600080114080c1c80440e4000100329051b60840c070541d14080380605070001c403019030503080c501100500c030002e1240d50302d01c45e000001850040740c541c592100952000c2e00b078a003016020040442c0d039480744c0c002170696501c00c49601d582c0b81400d5100a0400f01d020304000110340200340108800825160400291140400484168003051810040910031b81d60200d410038140f100700052081c1c20030084100360030707030f4080d2800012940064031030b545583c51070040a02d18003001c50109501d080c0502070a41c00a0401d614519680700c241e4070040d02c5900403c03c242d000030040c40390796820b001d1a1402d80f01c240b4007040c242000c5060383c0b024099502d101ca14520452420500c0008101c005000d07100449008107100c1c106e0500203440761130402e0151268175400c0702240345500c55210301445485d204485a002d40c0f413011085580b0343c88c0c400300504521921040480d0760030128007250080d0300c141800100301c14148005807190a9008240b4822 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 174211969 1250 174210719 174210737
    0x90308090d0807080c160f060f0b040b10050c0115080f0f0703020d1101031d0304060e0607020303071e020405010609080d02010e060718030803040606081614060f0c1c0f 74
    0x580d0025603203908105050182c46d10742420b109200c05156011401420004402224406004050344242582c000300c49041c41000e002c28180425150070072841c507000303d80e003841c1029030342c82040505804050000041808241e14100c91580461a004001710f6000380c2d19280e03201104100001c0c00c001c0c514090a0402d2840c0c0014000074541c0c0f40140074041c1200890342d603030f031080e4007030040c070172494400031302c11301c0341c481c1856413504107016034404144404920920742c5010001d07a151241c0c02001036140900320b81d01c0c1010980303d04616001e4120914110006944900a45000e130005030380d85100b203490010240d207080c020307441d920256403500d0268404c02d02c001c106503030310803480e007084809510110140c0d242e0040f00d5102801c2c0c410040b0a00040004e5504213004840d544012240107803503040490007082094445c4d400c1e400070300300d08260035040c43e001504d1040318031030042c2d081030055640340c0c1c10010740e07030703071128046000e4040024040d400c440b001074005000c1c507007000d03d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 174213219 1250 174211969 174211981
    0x804090f0b0a060801030c0330020304081204030c03110a090203090313060e010206180a0606030503040509010608010f030b04080f0c06090d09140603060d02030d02030d1a060304030807090504090308090d08 90
    0x446074031400081e1407143c2e070070a80f0030200090100c000030360802782c2d805500400d810030006e459070001c0c0517031002405401d18038592480302c041924140d03a04040d1100312180f4560b100162502400b003555008007800d0070000d03004100c0d101561103070000001442e40c4d6050400384115103580c0b50132000a101c2602c0c200b050b00d0368006011680004004883d082461034250003a10741252200014140c0d03007070090200802c100800500100c810030b80708118140d88580040d107682d1401d00030004142581c61080010a0700d00340b0142d00a405089120714010401215441c6544001c0e40e160a5601103414001d50711403c08c14014140d2541c41c010460504000101ca526081150058032800340800030070b140ea520290a00d8900d98000c048501c80000d0b514069140e03003040342100c0e07045184c00180088008019411144420024103492940d40d80b0350f0181c0d0001405012201040b8103200d000c5140d4550f44264103001d40651150310080c0750580942c1d2500c40402c04d0101000710000134012 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 174214469 1250 174213219 174213233
    0x615121b0a0e280e1204150807021b0f06030406090b0a020306061602060c010c08150609010c26040b370c0602070b010b0406120c0e0d0804090f0b0a06080103 69
    0x5000d000075503101c020f024880b035150080c0c2a5441c4480b580d0244c00b032081c103219014070042c002c0314412180f49082e002d4900c001d844014046601201580241c960021500034040e035460401c1001484070051542000c0880d4441d003045604850440c0e80b0001c084c207002503145400e40c0241907600651442c80c00c60082071840c042c285c0b200c0ba03d544880c003008119030b80c50301981c4619610760000c1101242c0004006c040c00da06603125003242d0b00446404010b03003400400c40f4004981a1036415202540c1c0e9139103201d260032107030f5988040780364001030184095564000c1c03005194107001e0300c0d00c0d8190750092032000c9625552082c1825860402c1e00401e12450001281641440c01e0418841c2544c0c00c1c514040c0c03045040041a900024002040103d9814058829200c540e541d059141490041c90f40896030140308043c0172403411382c80c81060b4940f407103040560510a005c401e04240e0380303401c84000d80c3d01400703440440681303810311440e9908114144030005d01d03a500d814195942365844100c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 174215719 1250 174214469 174214501
    0x50901060f0506090d02040504111813080d1e0203070e010518012624090f0610020703021f08130f060c0522060306080304080615121b0a0e 61
    0x19000380c1010944c0740c0250789a01e00c454406802800511091806152900d0604c6131107221034410301070b4404800386020b0698605105100300300d4440044c0c91961103920954209000d01d40610f6220000e002e0818800880d04403410401c0001507200e0600140c064440038032907204c10b041000610820071007000364404146900000e0a041e07501d00c0000e200e800004d46940c0d003480541d55901e051004c0d03092040007070100100e0340d03001500c01005c28410042010815595080700303407d03910108405240007038800a4110a600440340c003103980b940403900080c40351a81c801e00c40d642c40c1d80c0c1907006410034000c2c0d91100e40d001c3c8404111152f955500b45034030314210040c5c94150341b0b42078001c3c514042c1c01201d1884203541d082c91a007c8200310302220000d49400341400080c20075800043c000b600000742c03403c3d5a444005000b05680b92000c8600000c001030b046039208655002c03903800d4003c00e00400e1942c40581e0070300892841c602061204141460b0302801061251804001c90083d80c08030322 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 174216969 1250 174215719 174215729
    0x50d0f0f050304050d0f0302010605040c0507033f0b0a0302130203040c0b03010314010c05091503061503010e04031e0e040b0d0c06020a0219060206070807020f0a06020409050901060f 80
    0x2501030842507082461540c019900526000481041a041400860300c64115014400c0c1d0003484281d84410610080d5400340d203004002c170b90103201c0c040010340500c1c06950030841c030004800010078080c0c0300d074818405501e11004426444030250001d5642c9000e01c1d00314101c256102401c0e11710b540d0120f42a00c01a80100801e2a40400401c1c10050603604550090498110458507940c4a0130b084400340e844040165166181c0116045241e00030001d803510b04200820406c1d03405e84d00180901642d000902440d4807030105810604c442c0060409140a4083d005824042c2e240c41e2030702500c084408440c0c1400c115040f21800713095a4840d41000d1151002c0d6008220503071031101152180e50420700052000d00400004503a40fa03001070551441070080300c0c0000d4210f4040100403d2070840d01031400142c00a000142c5428040c09001c3d4012001d84101ca405800900c1090306091510204486054000504000c1d40520740100b640242c1484000c021652520090401e00990791080b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 174218219 1250 174216969 174216983
    0xa06170607021507050403021f0215090709020711030304064109040902030d0f09090e120f040e190e0102091011010b040501030b09010e0304120f0f0f030f020601050d0f 74
    0x68504d03105000340c9005543c05804045500c810380b211146002e101e80c6440d005214160701c482d018490311624070b000e46400030180041c5420140104007070350010200365a4003c90003081180740e101040200001c01381580c61101c4801e054078030008072038040b084900c140701c220b0b4120a108400449202540714002207550b50340c41c034000820040d1150f550040e505010304070080183c1c5030030440e81408025940d0340d1a042c0c0e40c40b41d000d941182d41034031034040e00f540484540c42652180c50300410440c0700480d40d40d4200356540d141d00c503030070030112440c0a2488142c00109240161806849118805040294100703c4d00501091040c81c152198030204400c0d00542d1380030075029400300c0390060000c1d009001c990703103e0030544034059041e90500165840c2c0100d8001c040404010785c4c090343c0101001c110701600c5030322001404000382205955903601811410000b56103003821103041d62081d2188440941e0004001c1c0c20560160721241c041c50030010041c000841082030704034075990100c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 174219469 1250 174218219 174218221
    0x4050405070e041e0509070303080c09120307050d0e01080702060f071e0216140a1701060f06020c040f0c050d02070c1a0d0c05040303080402100c0b0a061706070215 72
    0x41107990880000105403c10b143c03060040d80303111607a0490218a416983c00d101584031488150b56074401848041d0029075854041800c81180e80000c5c074a125000b0050f5080556414295055038003050f421103950703100e1920312603465089814032a0b065400d082c00c401502d010707000a03443d0f0400031302005100d030948000070702d89801104501c2580b2845000f1024000c040c58019554495411488040703400b8040b000a6140031800b0b5502c901c0720180113100154a803a51628007040b50708500c0c030040d503c0701c0011550752907100304100141034a84c01043e0307000603176041c0710440d9840b18195805904003580780500da07800c40c00326900c1d1002e00e00016a98112070901d070084800070340040c00d50380c003a200f06010000c90356000d00b6000c1806d1400700900400c1810603140f80c4070381d02c00100442d00b080b0010340985800c0341480000c966a00b02600c02d0402507484007020603080386c0b044c00170395a0380300034050f41091916038003400405000030659410218400703035a88054184160400803444 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 174220719 1250 174219469 174219481
    0x1030f0201121802090604020304080a0c050325031b050d0f020f06090708100b09070c02040f11030a0c03020c0606121c051803011a010509010c02060408060604050708070504050405 79
    0xe5420100305002501000303c0b01104401800c5104807810a078800c031400f0700071520f1460288202c0e4029944003405500c1c00000c0c28080c1c5502c09154000d840901003442001c001c48141603620405141c100360208032030240c0c1c94041c0c0401328252904c054403004a45850010300e001605d48500da065040550006102190803450025580008000c1c3c1c00703110288040c00c040041c2c00c405540c1000242c503c0c81d140c800514003164000c005c602c4c0d1042050000c01d100c01d018a15034145d82d070010344049500070305889a039040d40c8008040300144a0000100190000780c0c5c45070301d1034003040e884c0072b40c0b03031000c0400301540c2e460000d8001403150b50700072170607500d05404001c004001441d1031b00d1a42460440e0f00c0107032054214800509000003a413581410324a4188a50708501c0e40b03485100300520a21001111690001340d035850502200361009405070751880d002d0401481150001d12241c6801c00610003a107002502800a020040c0b05003c0c9440c4c200c2c041d10306480045e44c000405581d81 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 174221969 1250 174220719 174220727
    0x606120c09370509060c03040f0b0703110c0601060f031406040b03010605030f01020703080115050a080405010b0d1511030f0109051012290c04030809030304050303160308010b040e01030f0201 84
    0x36034501070242e50385600007105140d540c10181c41140c0740000d40d48281e440d050001134504c01120300a000700c0c0c2d10b04241001400340200f0382e400200c0c0d440c0005074101c04151380411030b0701400d49100568001c00040111a51000710719400030303800d14007404100c1141d080780c1c48000c8081c05e264071454030740c040300b15036480943c00007000305002411251040e62146842c0e00035440080103400040d541800490078005490650011100556800d4a803005810080b2080c0a014004664a54031043d8200007951901052421f8602492140401c82203083d019401c860055616001c41780003801044400303440b00c09154111642000f010407640d8807450103609154154012603250010000707504280042c00c40460740c2c0c848840490340234030804040000362210112404030008200700024800101514040d1015071005002c690074030703840f000006d081d82c000b044103503043e258803903034442413552084600d401040012100c503c6c00e0b081c8910702d94010014000170340f1001820041404592003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 174223219 1250 174221969 174222031
    0x2505030a240311060310030308040507030204050c0406080f0c07021207030f150e01141302010306050d03051903050105030d11030d05041113020c03030f040c030507080606120c09 78
    0x2400d1107103007000d07a008030000c0051003030b001c281e070650f9490052400c0e0341040300880f4020000c0e85a5440c03942d145580480d8500b0000f00102c0307a50207003c0001005859034040d030750180700d80602c034648807402c04074020202c07440103042e40c103040080300901c054031b082201111040c54050310030030f540d0444501841d1400d90980e01c01011103940424860071b1103020845080d284151070342c00d0054040502e40142a0380b0040700c1e0b84400010003011407140040a403140180601c1070401040850380d44002440310300c0c0780307a000d4012a1000514492403648405001d4500c10799080800540d41000b01003030b0355080d0401d10006100403581c20b05502c1c031081080e42e00100040c981480345180038500203d0100c1e00c80c0d44e6501400350300750241349030102d50080c2c88403018203500941c21581c800c0c1103031250f060003a10a0b1501c00d1300000102c0803581c00c1c80070102503c205001450641450418800500341e1103c100340340703800488107100581c0d203203c003413038001d5259030310451082c1202e640d091b000d41c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 174224469 1250 174223219 174223241
    0xf050c0d0905040605030a110603180715030b030607050a0507060b0409050114060604120b13020d06061d0c070311030d0905011a010c080f0a0203131d2505030a 70
    0x46940150031400d0341c44841003094440c00e4900703104c01903440050607a030724841840102400c1c5c081e034174801d03e4200310015652200100552580810116a466003065070710340180b03203144480704403030f96201d401d80138600c411541038000303019518000300f0080a41c05402117801c100100000c40c0424415207802c20b2500180c010010401640c80d8580507000701000d070042142640b4034000201c40e440d10500342c0342240c034103040c40500e0b040c1c20341c1c90070a00306c0c00824228280e24011610000350b2501d00c03681541c640700b01800100d95013403850b100c1000b0a91003801c3d101a010004000c807602e219010707a00795a13030604200324101c81c814142c40c1103008100f00301074039034a810f40304000e00205410032006807401100c441072101a200045601c20303400c0708042c1540d103080201040b405110b400a000c1c4240e5441524103005000c01d0002c00d43c01c0540c4650b4404100030541144601200d160340d03080b001ca41200c0000414443c0c020200000d41e081010900c100400042e00d898441e4001e03840e008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 174225719 1250 174224469 174224473
    0xb070c0b0906040606090c050703030e160e040c050d080d0504020109080f28080702010f020118080405010e2b0507030b0109060e0109020c10050703140a1b090f060f050c 74
    0x2141c080e800780e80c0c0d210b080354143c44e842c1c18030b4000140030b4250305c602040c07000190b40701442c0c800030351015000b60186e01c601038400d100e42c0b5001c483c03102c5004140d20143c484004003002906103820710002c04900c40e00701621a14030349801400042e256011690142048040403c980d40c0f0b600042e180700c4103943c03110794180030705e002180c803500d000b040307865440c010701c0c7c00707500d014242c4256401d050380e00c1d0000400001d020807003d005903004030002c1d0803044c1c2c14800410f048060158049258034800c0c01101c040c440418144040d40c2c00c8001e10341d11070b03004e40e1411103540c4130b4180c040c05152007000d009618070300c840041c014048140601310285420407229400d07540d540808038010281445582126800400003041030b00541c02102c1d85502c00c003008100e040c400c10400b0005002c00341c108014150f4800302e80e145009400100e52003050303280310009140c01c10b04070021107840b9560030340040141040c8140704c6c04402303296034401d030b031950b01c1c00320489103016101743c4080c82891201040f82c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 174226969 1250 174225719 174225721
    0x4060b0d06050702010e0d09050906090c0d0614180f06090c09061209060c030f0106120f1b030605061e070f020a080c150403080919090c0203130b0304020d0b070c0b 72
    0x56130f01500410300c0640303500102d61241c03000d21001c440307210721402415403080944000c20f29030300d0005810f540290f0984d03080740c902925044080e0848030664040d140341080d03a581380d105403911040c41714142c41c0f00c2d030300f1200c01e290242c1c040341d2270b0000402451140c01c059010800c16150070040d0b070880300d40030b450701d51744502c407542100040008a9030f80c6554814140098003a6088006490081203040c0382c102499083c55403c1d60042d01101141412a64411703982c007a1104600a0b2014128111b403a102c000e4030b00c070002400e580742c0f90401400b0307801c2000a000d40341e1600fa61003c21040800c04251241d440d86020707180482d4500010f94044020702001c2410540071070f130107a070044210b0301d115002c00010094006405144030240c4a2041803000007a0790824022407a01107041c2428280c009071100c004070b08580b00b030700b000340060f480803c0c14503c1c1744441106002401004580609516083c3d001030808500c41c000100f40c10101e4004c035071541c0c001d203658110309500906220b03003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 174228219 1250 174226969 174226981
    0xc0d050f1005010306050601111c0314040b070f022409010f0203040b010905060415051c02030709240b040b130504050403080f1005010207170a14010608121204060b0d0605 75
    0xb0709000e00042d21028600404102c880d805034581d0852004071354058183c040c905c4031a03d42c0455091204800d160b1a0008a00b22030a5511081d1203148a414400b20a05000c0001080d5498100b1900255405424041d1169a4009407111400c0700c4183d00741c416030fa91009540588150018a00c2550010090000b0090300406441c180d48240c0f1f42046a581d5400802043d118060301c0c1c10440e0202c3c107428003150400303d440110103a80480d6020340c080700f81e40420714203400c6511602c0c085907601841c0e00c04030101403011407000c00d07032810940018182500b5406a1240344a07040290300001440d10040207905c078008002c01c07000308100010b25250402074640a07080320215540032400c800164041d40415828003070b28410ba004040d11410a07003085483c09d4450b003007181912801c0d07903000019000c40c02c5043c45990000010800c50b2800c0031044ca8005c076141c100c12548d00522180041441416045034400c0e004003003c92041030100c08101001c0800c003010f0b015505107400c01c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 174229469 1250 174228219 174228221
    0x902070c0f0f06020610141c02090a0203150a030b07050c07030501020a0305070e0402070b0a050603010e0f010905060702030c0303060d0305160f03090f080601090507020309190617090c0d050f10 85
    0x440f1010b80903510343e80d54141e481c40807150b050140c84c01d80910032880c0d1010381011840078144801000140c07901005940008514103400c540e0345503500c2d000800c0040880030134001074002403054510810107821035a40c0c1c500c0102c000c129030704215000c80c1000141d18204011402542c004000f10740c0d030b140e80d62004020704000c84500011074101c501001c010b0900b0710840d40140d80107102d4000d40d40b5001901c101800c4040d02440c1d040d900c40911410a031014072012901c400704400008440016282c2282030000080140c0259081405024001140401241c1d40b02c0e004540129024035545015a6240281c0009004400c58000c2920030001460211401a806500d951074060390746c4c0782050200c3d0003806828901d8021500400c04c0d070f01036400c0140c101c1c1c560300540707040403040c002184007000104001e0001010400d400c02425400413091200442002c600d0a807911b4411600d50f59403000c0001a07000c0d1591080d000c1c1440000d01c0b451013146105c1e01942c1d604403003010f802c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 174230719 1250 174229469 174229499
    0x1419030509061e0a0503010f060509014d0c03060f0403080702160603020d110421020604080f070e0a0203012106110a05130503060402010c020d0c0b0a030207030f0801050a0902070c0f 80
    0x880c030074594440110b800ad010700c0940c1c404110507500e2140500d042e0607442e40d441c4c43c0d07240007046041e00304802454404912040c01001281c04802c007440101c07203000c9481c00002c0701d4001c0c0281c0007038081c4141c2d102d41d4841c070340d4451381508103c3c1d49521524000ca20b0003500c80500c40741404000c602144103039240d0000c00000e4070a94003400b0341c0c904d0a42c0014544181d12030b012640c0502002d0140c4456a49080400140004e0500741001d07a92000075041ca01e5800601085030403016003400b404070104103050308200420030440c155030420143c3c140702440c1c802200303107131403030040c8400800050380c2080581d060000301690b1200c8801e140949960000b8001c0020700d94245004600b034140007034801d100e00c3e016940c40c120000a038081c0104803040c4181940e138258116004954207080c41c000307142003602a640103a68101500f0014141c0c2280c0b8156010480102c00410440e41d91458000035103448a41c010303503645091400d1351080d8160b80c0682c046a122200c0003d20802e84039040c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 174231969 1250 174230719 174230729
    0x5040e040b0103050f06160e0607060218100305040c03061d010e010e0c010203070c060c1b03080a17070e06092404080d080702070b07020a121419030509061e0a050301 73
    0x122001c00e1000406521180112031013030805108040d180f087c81c1c03040500380044500645250700c0c110803500e45c003060340d10801002300e00c7c000c81d40c94a1703024209800b00f08016011890100034600f01590350f4810000c0a00c0702504080e25040d1940c44942540c0758901c0b258500e000030821010511841c07400b0b802d99185070605800b82c0b00c007416055002204461030300e0380c0301038000180340c2400415240a0007845e07003038414140404880f50386072200c002800143d800f490000c0e45550f03110300000d04908210145510300c0032000140040c05421140000032175404544440c2c45000b0003000c550003072081203804100d54609000c42e03603600c504100a2041c1c9140c175090325040c1101140c11b43d1909425244140140d000590800003000500c024142c3c281c4010989101907968411014117201c503000d00b580c02d04032401d1024543d500411484254002c04a80d80040700d015481c00307492070003001c071614064000050203d1003002c02c64403062216209140f290384030000120001c066400034011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 174233219 1250 174231969 174231973
    0xf070f05060d060e0420040b010503011203050c0604050f07060318060b0f04021c0b0406051e1915030b010206060303120a0b0303030403171014220203070507150605010c1205040e040b010305 83
    0x41c1b02003801d0600842441200684460749940d20f4a0714220300054844019030401409001c3d8480074032007401118055130090b4014450407000501c80c074201042980114140352a0803000c18a5140c030620014041d41c1240e000641207d011011541c170741d1000086076441340c070020708901c00a41404038619800c1c2c0003001003010322056000c2c00101c035494058a64030980004c0c04940c0102250101e505a2038060202c8809542e902c00300922425141c011006160307000c141e8503409a410f106181d0019424402403440b414000c0220761030f4480e014411222000401c0003a150300c450f40c10101081314090100c80d524501800c000b040005040d48044400c0c0d81200800ca4000840e480e441c1a00e51b00380c079451995849104102d80b18421005d21711281038550524060301c0e0940c4040c43c0301c0c8106480d45039403100d940c506000301c080c021780755501c200e02e41003041c000c80e68480784007440c13103600c81d48484503600b44c10820b503294021075110286d0a0700180400040141c81845035040300e2040b01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 174234469 1250 174233219 174233273
    0x516030b1f080d1d09060312030c0f130302280b0c15010e22081801020f0d0905030d08241f0315060e0d020f04060e04080c0f070f05060d060e04 63
    0x4100551714255103240d40755100083e128010000d260045802c007985004c0240307460103400042d81c00c0d4128060521002e030040354104154142400d0404400d070b907207951628280709030004400d91203000c0c06403000c8100c0108510750020f0302003140f1204880d40078281c04040d1380d035903a00c5282c2642100c030040054001c65030011100c000c0226120050784c8181114240680410100144000300c00d0017030451080340c207080366011040c800070039440041d546030303041c490924007498a80905160003408000d01d100401c207850a000036000c510b00b90000408142486020009104154625020304c026400c8607400d034107244c0580c00101c00784a0b1035803c0700d8980c0e03140001d540c6209800c103000c6c0c00058014600c40186020300d50140c3c8208028400124282c0700c4008265510048800f2a4040400586800e01d200e0401142c4404640080200501c0b42881911041402d403071203403034040c403008503803a40d8031322954101c14050720405540c9880c610746030800b00700320700c034028200c80324494240b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 174235719 1250 174234469 174234527
    0x5010b12070b0a03050703060e040b06030d020c090c0903070e010e090d050301050d14190501020309010b0901060c030305071418191a0309120c07030516030b1f080d 72
    0x210309041120400c40c0540c3c1020608041540913041c020f00c41c60405075280c001261100032070411074010781c0104400005842c210f401d1601c1e2098941510b01503602131003101140707544200009510002d550105038603141880042440c0100b1500000d40304040b000000c941d100a52090920814480381100c0744d8068001c010b0f92548028001c6a80118803050401c0108108801ba69801003000b800c440720b200c40d1100d01080320704158001c850303503500082448840c4409006611b8955421108103000d545810340140020a0149004050503200d40000745050300801c01c0454010568002c50790b42c4075401e00c10038032444112a031354450385081d80c001045c100650040710540742103c9081c41032a100307002c000c2c041e410007010307200c0074810703002c044000c0d5580401410702400307036600402c2c0f2903007146003042c20408080b42301640d442c0448400c0001c914540e15184d00840602080344854846808c03401d038101217604491414402caa6000c101c25a01010b80304980e030150090520715501c00b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 174236969 1250 174235719 174235723
    0x30106020616090e012702031609050a060e1e09161101060506090d060605030a0f0b01081504080a0309050d020d030b030105060607141f1401051c1b0e0405010b12 71
    0x580549005084090700501c64501b402d01c0030b401c007a815020444001c40c005078075000340d07802203900c19200003565404035806600840e1103005444104d544603001340c00d0040040c041000310680c1845009000c0f4042007050044402181000000d030420029182c90000c0e01407540002d00003000107080c07012040103450061055406a8500a00e902c2c50941c40c1410808150104081514503668810002500c0d41d000c03c18480628490480541c0f51041402e04440100051740040101e03000302c000110241c01c0c11114992150740206038640f03078440c0c9101100200000350004040d44141440b80d83c4d030715000641703011290941da606002030108001032600340c45040d038034282c01200900c00c0500061203528134000650003030003125018040c01c001020348001c285410364460307a4880c110703024201c10000d05805014165909141144101545041c480543c0300240c034246048045055201d04000f00800401112070201003509160038020300810700440e945206280b0218450700c007002c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 174238219 1250 174236969 174236987
    0x321060301090b0f0606120a24120204020d02090d0f02030601090e0616050f04090e06011d19020c100509160605033601151e05010507020d020402030106020616 70
    0x40220380401503110420301211130754028050b103a01070350a1180c095807051144009119243c1064082128101c04500d103100c0f0b0703c0c56108d030840306a030344c1c8240a201004042d1003d1903174140d0300181d5900c40c68501030000e019071401e540e4400d40881703414092201140032500701500071000e561503a661001200c080321507244403425640c00907000610005110000701e448201c0f81e04127075250a110305044805a80503402111910707585411904200508100d0a03024109809010240001b003641840111030000c21030109821107a80040841100b90143c845802140c02140c1d10044c22280e010041c00003211003092900c1621300c3c00d80021107010007041141c0441d05c0d002c1c80c603150415400b041c07401142303102351510311212540c0c2d03d014102c0da01846c080007103000001c801d5113105000403d80c0c4d450703101095a24102c10552074225009480100310f440909215684803a60301c04070341c3c100c040b2a400ba510500c00300000810700d402003100d0744100f21002072500410f021110603551000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 174239469 1250 174238219 174238223
    0x18040b060301050603101d0d180b0a0c12030e030a0c111c1401060302030a0f0b0a0507120c02010609060b2a060105090705090d060b011115150d05032106030109 70
    0x403000d4241660072449507c03540343c001480c49040780b455402c03003c1a15011407600c94000103040b0740d8030791354041e000d4a108409815040141883e040307151074000c0802005110140c14950580e100d01c51403802544040c44a9400c1d10036a6141c040d00070300900586c0d8075400c240c89a648100c640a0645400c504800000c0c4014851102e91070441d12044006c8600c840c030140700399601c070341c0880035030303401c201c881122031151200403503040d00e52030415140080504240e1195041409020b000c0360046801ca0303015404910001d070380088030340100d02401c1a40d0000841c207180070004a030111300e081c000c0c51003600e25130140300d8803019120b080d105040c8502c000d0f0030b250481f02c014005441c0548603160410b0191a005040030516800500d000d8184441103480590390003920642d56001000004403140440180c101c1004101040024000003070040b900ca14903200e0300041a0b0710120010341c00b40c0c001d4201c0340c958001e078814180100510780f02444802203080002c0940c641401524005a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 174240719 1250 174239469 174239473
    0x50916060c0c030b090a0b04080d0c1815050f0c07030201090f0b030a051005100903021c03020a060507020109080d061e0b0910021c0206011401050304030f0e0f18040b060301050603 79
    0x2e03185840d940e0f034031310015013101424014a032001000c15500504240035a014100442c1d85008842241080325112007607007043c440c0c001d400d5020300050100700e608950081401102d558182c100c00c8600348a0003003032298450f0045803001201c4000607001080d02d01c00e807111803c1c6605c551412104510b14031070904c0103001040000e8504045410642d08040c2070350341c4048481d00d41c0300003078148544c2c1c807a43c80012010701d01042580303840004a4508103403261101c2c605201900c00944070008036001505468581000c216860700c04d51214400503008402e2684800101105c90040e00c01442860310a40b452044001d0150303038500c00004540300303100e40614003803101050006511703180b4440402e5008081d5020005021813101081003002580501051340c1003a01085011040c028214100300043c010400041d420242c003051184450514400001c69280081e2680c0362115100d40c00014041e00c20081002c040c40e868019403181e10300c0441aa02c1106043c02c0315012601e499240e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 174241969 1250 174240719 174240743
    0x7270b0c240a0b010905100309020a15050f0711030d09170105010b160c0b030a0902010206010b0c03030f1306060603020a0813020609100309050a08120c16110310050916060c 76
    0x103000b071a401450000300c10304104000550b40c10001d800c00d000745a9200c04a80c803074000004510340104802c0103001c0c1c01944000015050b18001c01c2c43c0165081154035150015000c01482070303a075240c81c003c10009007141d081c1c4031202002001c00c400d501c91910420615142015052018000d0714180d8080719203e6003003190411900e0b2042d050b02030256540800c0c1440851403641840c011840f90141d95004600d0034414800203280c00c405900459038402d042c0032600c42a4400b00807039801c80b030100940c48041d2149260f890300c0c03d0b41075500a002c10301d005c0740092685d41580182c2808000c0343c45046140d5106020b2075900f000b03154000758042400c00c00601c1a1610140c68001c5000a140019407030690347d640314030b000c100101c11381c0c000c04003240b11101c420315058019480154000d160342407600341c1340d60031841d6000000c003d04801c1c0c000d1004000c1c4d00c1c20441811403d901e8542405030b801c0299402e41c1ba003c014001e480c1c0c142c2e1105011481d1805508500c4265500801030850 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 174243219 1250 174241969 174241981
    0x2010512070320040510020303100504050405101e051e070302030c0f0417061308120402010507050d03140a09150c0504120c061706030607270b0c24 65
    0x9100c0c802040d1506040e81c0300e0140c0042c020260444507600c41c5010441c1d42c070341c01d01080018110321a120801154010000c00020003010900e0310101c81c015030340880e1a03190b0745400c40c10500c4540b4481a850b281030316221620820a5482c070705240302050030480ca44920356081e252801c84400c40004105c1d22000c80ca640c9d10075401594040c140001751070130010703c40801c03240f40d4000da000c0300c031104040914018101c0e050002c00d07004200801c60340b11520f0251f55420041c01b0f10b04d09d60280d042c2210000c0d0239640038100b250089a440802c0da8500034044101070000c2820008501080c0700780c1002540c08001840350014580e005500000c480ba1050f0b50080a448101c00703800170804240800609008011304040b04144036010396180c20303080c103030002d0234078803002070a42482d4028414882d05844c0810281d40124082c43d12000006810084c01501c0d4441145c688245d98500c4002a082111b179000e001c40504030000d40301c1803030701e80441101840a042807036200c08118008900 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 174244469 1250 174243219 174243247
    0x150608061e060715050c090315040314040b0310080c010c06180204020304150f021213110a0b0909090c010e1224010303030b01090305030412021305010605190c020105 73
    0x204200c02030000751070384410040440c00c203411040d0112400c0b508000c1c90100408a40105075000203540c1c19541003111f10070012750380d074118020b0044000700500128041c9803041d035400132080c080c40c03800355503160758126800c819401120464030080e000900425544408565050a150144c0d6004500310b040e031200001410318451504d40c1042b550110001030f2a54005544180d000340e41402411004000150a8030304c00c0904101d403910400c00b1500c0c4000c0c2030f84c031039003040e40d5110390024040030345030008442840c9400d0550000348040c00054a00c03096004200408060300d8000054440703c0006540350b1445030080d0106002e000d17500c030300e41000400c00c2045000941115114810801480c000c03010100c000f400e140d51420040c0181500f50080800400081c68003a4202c0c3c51901c8958482c003039400b03181000c0c03010070744a0055544026a4510840311650100541d5a45400241c425403004440039210034003804060300441c0521080030071140c044c3c44091400c00e0b0905055 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 174245719 1250 174244469 174244489
    0x19030e0915130f0c200c090705090103090507030501020405040c05070503041403150f160503040c17070905150f0d03090e060a150906022107020f010302120c03010915060806 76
    0x1101696440010078803003111801042107013039103030f118200c01c14000e0500814042c1148078640c0f5035800b0349400c05454403040700c003640c03020b201d142c001c1c0c650703400c0e0300120043c004800c1f025280b4030914002200f03004043d80140100e40044604020000550f8020380b094003500b6406849a00306001c100503419445102c0032001d003009080d00e200e480c0c10400ca40607070200f41c80002d41c1301d000400b04082c0780004054401c104106017002400c40c17805035500d01000580b4017440007080360309110f6044003030040101c1d0303000d0f0481c4e070000d020514111000d05180701c4900c43e028030541d190904124242044040205503a0705a80c407045440d0404d005200070042c00303004150400a4210001802c000101c1c1080c0084105c2d1744070750340349103001e10003450302041842d0443d503a10080f120031480c4801300100c50195505980c2c1410700c805600040e402401590700c1540014a040e04100c01b42010b0802941a22242d40c01000f03102d42000c5241d6801c4100e010b000040382c01640030078810301e0071810304 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 174246969 1250 174245719 174245749
    0x70b07061d060412052505030408010914010501050d020a090c0c060207030f03140709060e060705060711010c0206040f0308041506060e0301050a0b060915090319030e0915 75
    0x118030580d04000d0956100c1c400305040c4001c0c0c200074207020812502c8000e400c0001d41a02c0c0050400013900d0f8040d1404031420030841c803512110113404200701c1c0c03d1040d18000c20b02c0000030080d8240c14140751110002090043c1125468031001040c0d41c83c00750700d50a0710700d03000f50500303e0081c02e2401504c0149070403000310080c800708040050024513140001e29141d44a6a40c4818032818210050300781d9180d41c10a1460240171010400440d601294044c01c07a80d280c41d20000c10f40140000c43e0480c0728000c4050030902540d010056226041070348030b00220314000c000c0103540c04c0041c080342c9032070090300d0040c819101040304502091140d800b00741c0241c0210f00d0441ca10b03001c030313403280101ca1903507004c0d001286034020800010728080c4141503106003a00b900740040c500010020341c080c4130f100d240c1031240f840741c1d02c03134182034000c0c60948001c2013020b402c0341c2400a416900c1540200140800ca000411100101169007485600300e40107a125060585c01443e583d0104240c140242c1d10f1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 174248219 1250 174246969 174246971
    0xa0809030c01020d0e06250c06091b0510050a05040e0403020c0a290405061905040312020c040e0c030727052403071505030a0b09041b05010f02070b0706 67
    0x1d9008000000e100034401e20485280000f022810710410f02d0600600900c54205401c14140b00a2001c2e8115200000800945421000c00e9050301c3c000c801000300da4406007115110700c1800b8a5045d100c003420003a1030342140d0b400010410210708444c60b120380c2c0c0720600000d5091004000b20743ca10085240c000f0f1007401903c401500310004540a044960f02004224030001660380c01000d00c0c0e204a41e004c010f2607051840c00d810207020804511468000850038000400c15002d507610070800d84001d03584c0300050850f4941000030080d070750000c2c4071010b84241d1826000180600000540c03000106014020f4042a4507100354501c200500c8441500140600409494800c0b800d100d15407040e8242e60600c05103da103542c1c0c1e29999030035040c803076019900410044c80344000c0d030980f02c4c00d036500500d0650b0f5070b0340d03030180b08102402360700c205150841000030900c0f04115220300410040b0744042d40d215907155448004540390801c020031480035030000403040c00350281c410010b224142c003501c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 174249469 1250 174248219 174248227
    0x9030a030b0f1e04060f05010912020f100203030a05130f0f02040f020c01090510050103150b130603080705060a0b0f010815090103030507030e0609330f0a230a080903 73
    0xb01055540a001401c0e40030018030b0f0029040c14901407042d90b024100220002e000c5a0402d400039005c0801401200c2040c041c00c00d201c2c0456841d00110341c012000030b42070b181001d592681c0a03580390403e8950b5480d17641000700180b614070544800d80030954009498a91031040c944601807410050385042e41c010703403100c41e642420410fa00050080003100c40000501c1642c9003082d50a0103041c10503c20030074100001000420344c2034070b00c80c0c41c0801c07529001500d144800001901e18403020b06040d41c09003860000424400c01c3d07409000316a004006403943c540c1c0c0d028404c41280e03014003119502138400340311034070154418020306034400b4884d07080c0d60901214100041e80c40009a01c221700241002403140101503000c4107030b208034001594981d043c1210309000400a60901d200551440c0a00701c51f03944406101c3c61201c40004a001d005566005510032240c6651100a6841c0800d00305035a2046c00a01e52406a45c15854035240d9070900741c1150040700d040d00301800c4243c03070b480284 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 174250719 1250 174249469 174249499
    0xf01020109080c0a02090a020304111903060c090e060a03030206070e06310e010f06030902011206170f0c15210109060f0501020309130b011206090c080108030309030a030b 75
    0x400400d400f10520000b080207503264410488000c1c0d000b440411414014020300c40011880450480018001c803100340c0020015414204d008a89600c003810580c00d041d4582c90711608102500207035a150b81d0b00f48003e5aa1034248071045425110040059020328000703248188110b840500600d0010f0003589003008002505960250b414030a5001d2802c001c09524410304200d80380740100790301244d0100b550714003000d001d19905e091013020181911004202d0840e07105210361252450f8031001001407d46580380d501405030140c6d0129031521450100b030300e0f000c1d400113242c00800300051022031440c00c020603e040d0354112102c0c8286030411000400c148201c08114075000e000c1c00c000014106280020001405203264080c0b8155042042425425100c0c090750001e54440c0706004201c0c51507001c0100c4021150b4140000407914003940410712a1031134022032640b4410380e461005698032031794200d4581c8020b03110040c0c40c2c0d004002d503074a418080d41000401200091021589621035 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 174251969 1250 174250719 174250733
    0x6030921271502060f010b0f0f030f04020a0501050403020f04020d090b19050a0504020108040f0c050616050c0102030307080a090609120807020706050408150a0e0f0706022a0f01020109 81
    0x52001c554980d010310240300c140b540a1046009070158402840d4038140100805a00c0ba07040c0520000d600002900c506110301c2003086840302c1c05880403c030b81e2464030503206c02d01c0d0b06090320124420305441c440064158401d02c169130580e0f40040c004c5143e14030800c01c1000075805507103115000c546403c3c907500464051191113128507500d00c107828290003d12050340850300d000300980300c0130703152009202c050b0b6130046200341d000e54048842e0000440f2030130982e0048140c0c4c0d10060348104006603003a071000c60b085481d000944107a0858074824000030041e40c9a00048465100040d40c0303500042204a464200c8910301e8010740000135062a5034440c80c1000714506010004194900103110601d5810018000103208515044c0d043c42d0a0100c000d4403003540402c010008c03400d8a010a1000805510030000903030350300120b0b030403035421810864440c0781c18494a0091300400c81c0c89055100c42500f840764a0f200c24068106d0202810704102c1e51000c8034511604642d6200f50706c000080c19 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 174253219 1250 174251969 174252017
    0xe0705070606080102070f0305030601020f0f0f0615010e150d0c0905090603010603080d090212070f0312030203090a0326090c030c0d0210030905030d06060801090606030921 76
    0x5658040d6a03000e6820301d01c064035819403000c0c0075607104002d0000854600010b1582c0c1d240d240c07034160b96030b45500004038504144086451202d0049031107007541c10800081e0b09008007000420b40f45650350b40b00f4075681030040c428925000c20f0440440415501d8818840306400c1c080341403441c24107100d40041011075420220603c0855015802404545809102c4540c016800c900a00c2014250782d01c403011030291581040007d5110300b607510840d62102c0400e5083d507183c000321001180d03980142c1c89128018401503801c445503c0a8804c418843d0085a21034a0030200420021721161740032103400e039495586449060355000d048640e00315400740780d03014002c800000c00065152004041c20646c590a2162007072656010b1440162034004440c0c090004508000900e05150700b8903505504c50081541c03030003440c020001c10074903080b0025078182c400001c010050980c0b10a003d0741140e02000c1c003d041c595100c1e284031008001c100c0394040d864110b1030282d80c48040d880c10741c02c03001a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 174254469 1250 174253219 174253231
    0x11a0d14010f0504090f0303050907030b0a05070305010e0705031303110d0906030f27020105040b07060c090b070b04150204051201060e1b030103030c050a0803040b07200c01050705070e 81
    0xc0e10010808520780308081806450300321010019a149950784000c1c40d20032000040500d5240d400282100c00c05000c07036002150885044662072604044240080104640d00d01c00b0a180c180003103001c030f03140c100c040c0c4200015150b4915544644060b030480b00c8140500310100b11400f1000c810700f01060000c0780c0030006603100e0035149030400318060300703803a8140403843c1018500b0904202444c0c40c80010305d031000d810464100300c403815000482d810f1041c3d4006426840e030010b40382e030800c0303071540c440c41e0a40c0d11036039020b01407900c5161008142c45612005408071000002141c04220200c800d41262800f51000614166807280414142e98a04080003456507640300c080000c00324003480c017540700c00c85842072070000c6501d2400c141e07140410b000203020400400003620400400f000200c0001341c001c102c9a84a00c0d0500c0e040c038681030222484000500c0d031000a5110380344da00a0b0030100e614000c09848601c8000004580540104800780c51f9441041d41c0000c5040b02d0a1302d490150f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 174255719 1250 174254469 174254501
    0x90a1701050916170111030106080f06030613030f0c0b100e060d030c0305030403050d021b1c08060f1503090f070f1d0403030f060605041a03010e011a0d 67
    0x45410488908441000700b544403240c100e8a09440d0703116404481c54240c1d895140308405504482001c0f50040440c900c440c50f002000200100b519600319913041d01c500c01c00e4520302001ea4400c000d05864601c142c8081a10b5941c10b0395810000c4d0144219149843d907601d4103410b1100662542d80b0b070054144c52500d21044c40107000d10480c5400050070b58020020784111f07091459547d4010201c010b429005401c025011012408040c845c004a0b503510340d05582c195140c01c402c0d108520344c040788002c525181d108844104d10ba003150b0701944141101c1544074800503a456100717014040365284011948018111803071100d60040101850103031020350000c20410150f04003075881d00341250405104440000000c1020302024028031144480708401c0c10300c161502d03e000d601030300002481882290800340f001c260b450344507000c0e104440030325048040042e203110103044148001c0c002c003c030403045240184240c41c007105010300091100318072103103008081328507401210920780e4145155 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 174256969 1250 174255719 174255749
    0x1a180307171b03120c19030e040506010206190b0105160b040c0608040b0103170708070b071d06030c0901050919050102060a230603070f0308070204050c0a02030f070602090a 76
    0xca03004000341c070400807024003500580d403002d80000380e991241a4135103003818000a5483d98114003844030b501c003100982c401110b04000b500c0c01516034103d4a04c05409545001c0020341d243d031000603028004c041c40904402c01d1119030030036601600c242203d2a052140c1080054200040c01407445078190080700ec00d841d50403e403400c2d681c0c00c1e03000c0d80654100700d455000d00020500c1125040c0c11030354046544072a04001c11080710f02802040c401419414010030040f0a0051001c1524499a110360324007440103400c044410780c0c90b00900c15181c11080c24000604c8400300e0f4401045603c1c0305040940c00c1000c04400151301496441d030900e084040154100981e5030100b00d0540c215000070000c0c440e0100c9962080200c85120076a070304098808030108403591000d020303501c050b101503800390941c2e513280d051031105075004410484c011441d03c00080d040c032021100361b9004640d6a8061031800d44107540002c80b6030025031060307403c59402c0181d00290781d41d00d03520310010011100c1c41050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 174258219 1250 174256969 174257009
    0x2030721020c0d0c0c0503120f0a0212030702061801050112080c070f080d12050705180a1e08060c0f0301050d030e03010504060b21250e131203061a180307 68
    0x110391000d5102500030b0340840c40030550b0317041423800e40e030034610820030168480f015110102e2400040da07450b01a1400c00000b03000f50594049005441452151981c01c003402482d88080e00f281c20034420321100030005e20400000a160340b005011515080d803c403081b50362101040090000b556100610b01d5004090302550f242e041000761072000140741c003c03c954138001c00043c146110740e400141204504410f1406103a13500d0303104401419250341c141d144454080e444880141341c50140c900688515000241d0030702000e401c59800e1014804024210b0340ba000900001c1c1c080d151046041c00340e02886500319881c244250781c4036501650012480042c01000c3c03020b400410408124940071a041c18880c0c41c00000340c420b002e000040c46020345600c0c41803664440426600214000b0003041c1c01d00041010101603c140c3d280911414840403c0e454419000c4034005c2c8900c40380000074520407100c442c0f41c040648141c01801c01c4800c3e50030007010010742070400e2a0820b2103015440041d0400c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 174259469 1250 174258219 174258233
    0x2040b0412141605151225021504020607020301090609050303180a02060409051b0c03040f090e0d110f060a05010f051212070201050712170a02040b09060c010603020d111302030721020c0d0c 83
    0x1f0f8202480c005450700000c4400c0f4020f0303011006102a0240324006080c50841d00e00f51711210807250064810000d1240e1890724648030350054070032080031041d4500c2007074000c0010522140060380100b140d40390030f00d41032240000e05001082c0025541c101140c9181004442e4020080d1034030803009191b43e00c0c1403403443e40c20000305400c43d00e0360701c1c82d2004004e03200b240051602c040c0c1d032860038000b4a03690781d250344a00d00703a00d0ba0061016409080d081c000020041d402a5040e00d0360103d0002900b6120400e000c0b401c1e15186081402d64004080211099501e03802801e5103401854428500751041c1c844000c1c640c86d203d640c500241c958802c0c4d69903072101c400402e4102070780364400c0d46010328120056025010302c940c01841220001680749a1170307425031004004580c0648008034240c01420413400100200210502400307820304031181d0301500e13100301d0f4400c40d12500d8019198000008070100d94042c100d5110000364200700100342200e003084081e16103405a55001c1c400c07001ca244c910 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 174260719 1250 174259469 174259531
    0x5070603020a0f0c110d0f02040b030c030601091109060a0e010e0102120906030a0204090e0d0215061c1506090c020f01020f0f0c0102040b04121416051512 68
    0x9081510600140500503403002c94400900c4043c40c05141034907080c241901800c81c140e15107036200c2c80541000c03082007040f070a4071a20f5402120308000000c07801041c55110300000e140036602d904900c1c0180000c03045a482481680140e0b400c09007000c1c40c450225529502c00d100c914045102086010101c1d82e000360f0300a240f8101384003414400b01d40020718451402020000c0340710b24002f000064004200f64140c40c01800e5a0302c00b40244820120242c0e1940703550400d1000500400706543e000111441640c2d029140c0500354034141c0004201d5800c003400344102c211400f103a10610004208030354003803100a00340c415070010b45003c47c2800a0715156000501d0040350b4010310400c4540c44480094500804078580f61a80d0342280312000350080c422034003c00d6105101107030101da00c5024212450b091441451b001541071000003015590315040410003444003e078800c01e008500b08061858088559081010f041409840074101250380c00c0351080340c1150388400040c0c81c489000c1a40c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 174261969 1250 174260719 174260729
    0x414070b0a0e041a3111070302071202062a0601060207050109120b0c1c02030127150b0a02010212010b12010b040609060c020d021309050d1409090901091e0507 70
    0xa1803501c0c44c40b000c00c1d01c2e910005003a600c1c407042c1000f401c1c421901c0609407072040e010000c00700030764111255600b030302d50810780c010b80051182d00340100350100b440108440003a002000542413080c0158011034401103040280303468442d8102c0d45001c82c00c200f03c0b46000c1c26054025100d030b5410f260005081500700e52281e02c0d2404400304000c0030a104007001c9800c0030500c1901c0d90340d48038007007a072031485900b08603044886100100001e401030252204080b20940b41d01418a0303960040702400030b99441010450310030f40662000c0052030801030080c0b80c41f4003640009801e20307119420445e41603000f68042d40240e2000150700d045081c29500c00381c09020364003102c904082c140311006225175854002d85090100c41c0f101e8206554600c848004104c0e8000d007a000484c9840c203409021703011030b070800c40f1144201200800340b980202034100e80c2c00c940c2d202075070070703c85544104903401c2400b400120b00d65680c0c031546800f08039150008100040d008000440d14040c61601e14504500c50f440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 174263219 1250 174261969 174262001
    0x60c060411060a050d0b01090806040302100f1a092a07110604120803060a090c05071104050112061508010608150106030b0a050105070c09050a0f0609050f0414070b0a0e04 75
    0x103021a0540c0140540781c0c095022030380080c1040c6c0380001640c11070b805400654041c0b0690040204043d030001c0c1e865911210642c06202411030b8410b22810740304181a10400780035400c42d090b9070f500340148403a44c40788280d40c81e002e28441c0507000f82042d40640c0c0012108100000384001400040300769444110003c1d11014609454400981c0d240052403030010881c071400070116540d90340d2004000c002d07200c14042045540700b1120064043e80c065101115090300c0f10311400080e140911601c0e040b02c0800400752180c4500341e43e07100050036415000d000c0c666400c1000300d40c00200348100000341c2444802000000e0100001d110300d800161301010825080400300354450700e940185408449007820441d8950f50b080c680580c0204c4d0300d420142400340b40c1000c0041800042c0c001641880b07038880200110f688410500d0281c41c01101c3c0c0403c20b581d29070209000501c40588010f81140d0003048d91030854454259605691191280b0341c0040e44114040f41240303010700c03030f0200c80248003070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 174264469 1250 174263219 174263227
    0xc0d18080d08070c021c0510050f0c090a0305070905191803031a04090803070f03150b070206220f050d0f061802180901111303020d02060702060c06041106 68
    0x14003599500281008581003004101c040f40660307018480c15a50300d90300500c0305081181403600021005900749050b90316108204807000540100c0c42141e0003a2000c1300100c0040c0c1d40e00c04e0400282d8040d809068001d90300241c00000300c5c800b40011006000b1902000c5000d00f48115442c2d410245010090070061600145003d0002d00011580c0380079410300b800309075441d149100389400700151141e10340050400f4020b90400401c40000e510130500c9032101000030100b030201720122600d80481070000348054406210b01c0c018000508080c0e4030040840b0702d0a040203280c000c00c0c4044151070100d0500748102880352024041581d00600020b48080c00c0c00d80c55910707101d07000c0c480d0010180000e42d40b41c4000310400400090341100303d4005d45a02000c0c0700342d4951545080044a03c400c04c1e518100c40c4065036040001214409925407040842460540c8c003044428109036804aa000c00204002c90060b241c40000d090a048103030080e082d6442c0034101002c1000290f40c0d42031140310200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 174265719 1250 174264469 174264479
    0x607050c0705090a0b03010c08040b1602072105030c0a1106090102150916031104060f0302100315050a090207030906050405130902031005092b0f0e0d080c0d18 70
    0x80351402c50b2402c07a00681203444000d0402c0c0200341c09903405401d5420034000141b141e8012003030b540500d1056242241c1035555038089035400340b05001000058011a0040009500f00c5c4052110000d0b0405d1040b040302c4a40d503010b14550115400405c180c01c0a0640d0003030000c0700b241e1405403403058580d1881c0c4501c0b400001c0d00d450f10f0352000c001c00b50211001c940c0c01c10040048450002c6100c0b01e0985494485c100a0b449000c0f8221451190b400c1c0b0b28041050407410507106d0460350b0141040303808042040c810b03000b03070058241e440300803144010300044c1d030b40d80c20348071600a164080005030303150840e040c000c2419584e07421030814001c040008022945480d203100300f141e0010b030000607800b5100d10000c1d040c00003040860003140e040105220b1030341004035100350a80c0552040340050366001e040e00c2020708507001004045903445001d51030b440e0240300307051443c60000b400d1a0303000000e90b6a00a881d0065072401d0b8450788140a0254501d4010240c01100d40000980c03400040c586 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 174266969 1250 174265719 174265723
    0x20f030604020c0705030f01060315020a0e061b0706080108100c021b0d080f0301050a06020a030f030e01142811070f020d08071a06060309060105010f170405010e0607050c 75
    0x1420207400303240e0000300c0c18141c1c3e0042c0078070f2000d40002420380d42003001540883c0d001e005140420b44400c510769050880040040c070032241b11071216101c1403400c61100042085541211400c412403030a0309018843d64070b0144900405401c0340c0d103a106c0380d9410890280d2400c140c01c0010381c0006d103448040300201c1d40005045002e00c826645210340c400e0008003090400d40884001404140040703a1860800e0110f4007860503135000380c58010386a41e40d020101c1c0d6448030b405002c0c0110705000c055008041c4030380c0141c50409144030000c18080480c41c9020320341201101c4019003c2b00c1c12812101c0c035040354840310300fa00e510b00c1d403c0c404200001005e10392845090300080903039131100b0250045448003a40c001000d5001880d1988a43c001d017004ea00b40341048282e000180d400b100021306520340030701924040c682400007002560308040064410542c22190341003031150748402d0019002d0070360704240c41140b0441c0082501c029601e010761070b1400c040c0c4100180402440f400c3c20140c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 174268219 1250 174266969 174266971
    0xc0815130b010315060b120103020111070e041509140a0203010e070e0c07030e030d0224071d0307050d060603050d0503070c0809150a0201150f050d020409020f030105040c0305070801020f03 83
    0x3846080420003800844c030010520784c2c3c0000245a80441c06008600310503075001c1c1281d000fa21140d1402c40b0007040103032205110b00400d85000e0742003000c100840d10a0310104114501d41c8030000d1552040d403a1590300c42c102d90b41f5460396034001c00c5100118102130207444a450309460003031005a040401c20704500c03000804a002000c00440c02c101414800c0d420700303c890702301609844002030301b040001d4503003c0180038002d0300d8441003042c100404090389030900c25034007a9942c0704650101d4951641c0181c80c00d490b55030600c90b1a0000c1015511800d040d00b0b00c1d4412280000c0381c501d1490000d041003d818410030500605100308081c40350071814042540390b00144003583d4500c2840045e1400600b4607130a0391300340c008034200450301d4056204c0040c40c1d411030a0740b03040590701c0c28100f8880b891401621b400020b4480307443c0043c107054000000e00e9100920b042814888107021a013141c1e0101c605641c030b86052002042404000c0c03040341c02404080c07009503c0c014030003145552900c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 174269469 1250 174268219 174268223
    0x3060203042d03080a090c180525050a0306080124050301020306090c0d0e0d03050718030213020f07022709060403081b07020a0308091905090c0708070c0815130b0103 73
    0x110f0300010040304850748040c8840d80e1010700142415116508180529942d0305523000c0ca62030000070a40d00c0b8064451030704c03000001b403001758020034405011103203608114050010b064071a880828080070a006a4020070120110a219000b50b1a00f00d00740d0b800f55030205009910400a0140503181c100d640c95000212280880e03450307000b00d00c400c0040244101c20341c803078040c40c000b2030561a0706400c01405140503540c0c42c140080c101010440f43c109620009500280004052030390307410307079006803a00c0340e8407400807801c1180360b80206a00c0d91001020320780240001078094400803500306001d801000042c0107001601d0140e5000d84401c00140c48048400300003021440c0103404034048401c0c060380544002c044a59928000741317139403c212080c41c41043c0c016091684c131100d903454181164402408007203a0b44600c0024070880c5e05c045029503182c03804014400104400e0f04844000344038100c001c10555403400302c05410343c0300142040480040400400012407180075556065035 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 174270719 1250 174269469 174269477
    0x15090a020105030c070501050f06040e010b0d0b09030c011104050306010f030309052e030c1b03080a050c0424030f060308031501050c010c08060321030109090204140103060203042d03 80
    0x20712550001084c6008240e001851582450104a00d4130445400140113101c00e480a00c42d072a80455950300340d440240403075400030f905080301c4010840c031024880d00282040256443c019142007000c0c29101803903403001101000080030011400d0402869004020000d0f0b5810080d0842d039000303114502d0781c40303501c3c4034400d1250705a07290011310600c0760f000e4610107100d8680015221000d00904031414a95001c100010505030050004002d601c01c0a5803540d5142910395506d21144002c10001e0044da41c4941c00f40408255019000e00380b0314078100c0c0d03141481c81d001204500405465030044044100c81c04c202d0104001840c080940345c20034030716100d51610000030001210680180c0918029139801c1810360307040c146d08203481a00a1806500b5130b400f441070b95002d060b940b0a00c81304505a640300b00010452034049501c801030a500c0100041103ca0380001031001140c02070300b042e9045540002031004128581500302000e18542c1440203035415900c1004081d2280418003034184 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 174271969 1250 174270719 174270721
    0x61d090f0607180e07030f0507031b11010b0d20010203040b04060f0201110313150c05071202070f061716020303150109030b0114011409150703121d15090a02010503 72
    0xb43c2d403841c001000d400803000160b82c0f890840c500802510050307500811240c5000d0106000034803074010b481c44e0446094007441206c2043c5001ca640b004a207842c205255a224485286a0b890003080e00c105030040c0c640760b441115011040f41d030480c4500060f810740d80200001c2102544e030030151402c032031490a01420500312500b040e400b500300d180750103598800000402c440f04480d01d80540301107000d40c3c0c0040704070f0401c5401104441d141540040402c10034445600041d00c0c50716040410141841920019981d4031460210420190009008500c0071511302840b0b041083c890369110402c0001058000c0c01c41c107000e0b480340b00203440700803011003031098416140d00644143e0f00865004104001540e911804000c171380306400f051034005866030382d044a440c0070303100689030303860001450b40500d003211a090040a40c440300c000c07414007001c400b841c003001125104000102008484900203000e40500751400c000e10030607440c0c2c400c2c0c9410b062140c0e00780001054100349a0a00b0a07541d0703 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 174273219 1250 174271969 174271997
    0x10f0f080601080a0209030f011e05010f030803060a03060e060615030403170619080a0302070e09030d0902150703030525020c0603040503070f0302070f090b06030601030506010e04061d090f0607 85
    0x81d1186c1e001070398052080c20600c112202d8154010b03102c000d00c05100b44d2540200c110030f0f0082d500300303105500e03801514800034004a600070f0300031a00003500400195401d85d40c4c1d40d501007551040e80c9200303160303004a0304120250411414415140d031048011034a14509030b0f82c0070786401c8042c1d5a15100004140000d600c685603002c00110f410482100d0034a000e542d4030990ba44c2b24074004040b40140a107000010343d080301e144c0942d0090003200040e600b4540d130140100c0003009466000e03039200307840080038a8900f030010010074205029583c00300f135514104001520f40e22901c2e64030040c4581580c60964950382c04606041d603030804841c403030303680d4443e400c25070710b9805521805041611f9562004007091f40014114040f502c0851040e0761007136039806114200c65100e203016800110420000340c01e90300c264040c65000d601414001148964440403804852507074010711615000301388170200c44034101071090381c0f10200d0001400c4207020744082ca0386941c4060141018001c0120803182 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 174274469 1250 174273219 174273221
    0x40204060503120c01060605030709060302030406230609061005070308090c041517010204030f12091e0914060d0201120219050702100c200402040e1302010f0f080601080a 75
    0x4000c0c034000b0120b514854180d428050741d0ba0101e041d020440d0f04c1c18600049040c01042524031820741ca44460300d0182c030b421001d034041d51000300200c0d0025a00c40003d07a1060021501802d01e1644408079400342c42d00700c05101065030050509071090010104640420764844103c5140c42d515103007007000368807454541880e215140003000c1e405801c4c8161010740c0011480c011080b12803074246401040307241c0d8001c600b02d00c1203000141c5203000e0b040040300407850001c544846c3c46c8803803410b01401690390742030b401685200c9040168044100314104806c14041c0915600340c04c0340c402405030350405070000b41c441d503121507009050040341014201051025415100181c80e03800c41484601d100b050003e049a004041c00c078801e0080000b0b20450314031034150002c4540e0302c0b5102c2131f40d180c40036006a05168842c0b100c20350140e001c11001c02c040e6040500740d4010820303542545907000d198030014202c0a801c6084d00c00304903003504030f400d24590118100790000000e00340b9264640392642004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 174275719 1250 174274469 174274481
    0x20402070605090a200d060b120d0f020d03020c0a1101020a050f0d08011e0b030604090609080403020f031f02160f050609010501060f020601031209030b0103081e160b040204 76
    0x2070311441c80c0008104192202145425440e071090520710254200000c00c00c0c0910100c60455401040c0d080240b000140d03130b58030070343c0151002014007100441d002c120924044840f0109c1000500300c2050902c55a01005454114034043c14154282032915002aa4a4403514005400d640c0d00b8098203416900078000205442c2e048400da030451603415410b00c2e0364001541a0800088160340005611011107100150048600f44403030360340f41c40c2c04400c58254202030b111652055840380e240c0006078661082c06c80d824881d000030b40d1a20314500401c110352856008090290b080380215000c82503119401001003d021100147c6602e40c2d00100a82c0388036894008084e001c0f00500b040612400180c000d1090040d00000c0c40303940e0301c0d180d00b21004400304884a000da0f103c0001400000c401c000c0e500f158002510b440790300c140c2d490f11000c8101c0c0080c0d006a400000000c1c0c80f440b203000a000e47c4507840c080c02c081e0361800d40b90407507082400805410151994540e000494215519600030b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 174276969 1250 174275719 174275723
    0x1f03020f030108010501060905010f020307060504050f03040305010e010b0a030c060f0e06030103052d0a0308090109050d050304030e010e060f0304020a18020d0b1f05030a0f02070c0302010e0904080306060702040207 94
    0x9903100c0d07031540e400728001c01c0e003800303140003062184c4400201076100c2d02d5403d100cbc1c1c0043c2c1c0a11f0400f0307c0342c0d4401c005040003403c200c40600520b050708803c2842000904025030103a0b0012640303250003545a07086400d100710141c060f030300071101030003c01d500d40c83d038034112001072401c205550100f500441d40083c17103401255200100100000c01c1c00000070b0708400042114084030f10f46054000328041208495134001801d80104600c0e030042030080402542c070007011f03000420344006079a11a42403840c12079551010a00210a200605a000c01520b4400c40d0030f08000041090141c00100b49016545105800d507900100007130440d101d9907003d0004040500f0002c0510003002c5160001c2e41001940d40c00152500c0702c041058a420251400010f8401c03092410940e51083c0480d01540000c0402c0005600e0320310380700243c4100d200a001c20790040b4580300d00181507100050078103681da854544264100000c2c04003044c01c020072241c00640449840760b4441d02c620100303001e40292000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 174278219 1250 174276969 174276997
    0x20a020a090509060f0105030717030f0a030504031b050601050d03021f0204170307021c03090f06080a05070f020601090e10090b0f071103030a05040f0b1801050907051f0302 76
    0x24030001c5940006004088040580302241c1e03c41d1125090503c0901c105030b81640030440070071032002c9248200c41922000c2003a02d24002c803d90316040c1e0b6038010080400081c2d510402c10092507801202d030b141c03010010318540068109521402c6d0707120010300405118035550055201010300070056042441c0000c40b009003082c3e000e0042800a4105228101921401c0c0c1d148031640d000100c1104c2031070b81d004106c903550141008290b5200011000210144410a40c001c680360a40d400464024290396403140d0081c6050a00c0d14142c40015002d0000e100c44141c1d815099500811041d05441d000c00b4005040101154414a880c0290200703500c01c51600c8248414011158603462003500e9005103881d240d00c50300e0044501c00c1945503610510b41052011a0845546030003090700140145825042042d50703440d440841d00003954800a4812401454400744801303001c4c00da484002c90b005080c001d407808010403800110307079516210502c40131500041c43c60181d4140c440090380c03409 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 174279469 1250 174278219 174278239
    0xf0c1202070e090d02100506060c070803180906030d1116060818060108030301090b0a0320032b05030c0d0c02071a0a0903060b01030902130c030b060304030915020a02 73
    0x502a45032082030103000c01c20024a000186035903400070324100313507900701c2d4000c0030390756101d00291008020181c48136074030034001c000000d800007040149401619610300031710b030382e005000d000c241c560426001442c020b804550800c511954007060b903560b1403465080190044891484580c20044001c43d07041d6203059641d40480d51961103541148540420b071506002d180414080d555030300c3c0300b441000c0596000700010b0000c208d442d00040301841002d0044202e00741c41e55034110703024800010305019440050702455403072408001024802102d4044118841001c29041d400809256281c0e81445800000300711a01d030800d0482d0080407507040100101c0210000c029201c400d640b080700c035044441c559141d400036400084aa9180807600c1d0825aa1b02e560340f0803000c3d085881259062558803e092005a140e032190300807101c400040c00180c1410086000c0d084400c582c119500505040c010400020380007100501a0781c14140701d05014505004228900000d0420094020600e40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 174280575 1106 174279469 174279503
    0xe1b030a0b07110a06050a0b011205010b030109021305090103080301030c0b040503030702100e040c03020d0c020c0f0105130f030503030a0c1805091009090506011d070f0f0c 76
    0x20068a40030b00e0151551030449100303e50203291f464988501075165a4003040020701c8424039001045194140100c602542c081405550212540000c1c4040000c0758504020b00034240101240308560310313441c00d80810b400c03c3c44116200b484d0303200c000c01c12500f404151400c0c0c41010b8025030801c81c242c0c080004a1500042d4041406140781c00003c854955000e081c00c0c440858401503611f8402503070130b10440300d400c0041c1c01150000b0303014108550b119803e9840b10442480e084e80c46120462403a0b001740b000d9803000ca640c000155001040100c0440a1480350941007010000c0c8400d005050f04d803594003031001c20030100710800030b0029240c0303030b14019001441ea0700258039003511110f070035084644250059078207034805801040211004c1c4d02d0400ca19182c0c0c4009003450501c0000900707003c0c2d1001552080c0240104040e0f4281d20031507401c1000c1e80c201414050a104035 = true := by decide +kernel

theorem cover : BRFrame.Cov 174100719 174280575 := by
  have h0 := BRFrame.cov_init 174100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 174100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 174100719 ≤ n) (h2 : n < 174280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
