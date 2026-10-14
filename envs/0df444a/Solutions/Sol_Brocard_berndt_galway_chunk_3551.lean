-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3551
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:59:38.248991+00:00
-- url     : https://prove2.me/submissions/c989c282-2050-411c-a93b-39528f6f0749

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 638489208 ≤ n < 638669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 638490458 1250 638489208 638489221
    0x901030e0604031d01030f020c06010302010905060a090603051009140f070504030f06050c07050f0105040209060a15031a030d021b0303070b1902090904050c0108070315050f06070606030f060b0405 86
    0x1d40134058144100c2c8800040c05403850303229500500581032141021904c2d17201c01241580d4400007408101c1c0841c06d11304000c2164034003030341a03d841c44030310340d681d10600381800000c5001e008060a04810200c1c81500450000b0160240d45443c0401c410800d41c03500c0c11b040c948814000c041c00790300600c0300070001070020803400a90000b080d508000041059261a05042035910841c039018000e40122a484501c0c031a064000c0c9010701e000302c40d0000e041e1031300c1d0208108141039101300300d031403210703404413080c0c0030300030340003030b402844014220403426002001084c02c002d5500605c00c0142c011280306008840b0107440c00300e40d090260011428080c5580d1000d0340c0104c054041400c519001d1302c4010912016011034084a00182a015681c102817801c0e5070348110200340c080c089034980c800169020301c607100d68442064039600710461300c1d01e441706020820100707210844c2c0210003041403d000c52014003400300110320070000c3e01d030790750751900b441030466030031602551046050000307003d00d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 638491708 1250 638490458 638490467
    0x50105010f080a0f02060d0504050303180c0d02010e0a03060e0c01140708091311040b03010e180616020f2b0807080703020c010b090103060c03140103020603181f020901030e060403 79
    0x4120344c406885070030740702ca5000140c2d0500441c0c03080c40003e8148404c100030020080003a502400d540d028110f841c01d0006032403525800141c00c82034101e98141c82c2e002c055845015010a81000907105c544003d48a4440409680d42400c80210300ea00c81c82048105581c820120030340e1310513000c9401e092001c15a40e9000398071848503414416804042003c00304244c87d0311162984916074212641c89a50343c20740c44075130b00b0034030a03031102c02c094200103524451309400e04603d1040500141c4242d0391004080030003600c0910159003144140508500401c80c02c120b10980d8490b001402564181d844044c0b5007001200405c1c03004200a0400780280340341c000d11110380222660401603201c1b2240ea401500400900c05c0711980802084000401d100180d030002d00e800c1d92655042c0151500500b440d180c0180c01c2c80004c2d0410000c00000e5110400044280320154212080d6190007494440074809a40511100004143d000458828035a0188600300000c0c0050001c0c00e141e1a0a8030041c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 638492958 1250 638491708 638491723
    0x12115020c070f030c14041806020a1403091509210d09060c030b01080c040b09060c0f07080c030d0f1e020c030102070b0a140f130201140a0c050105010f08 68
    0x882203401181e20034241a06110220142c8900040407410654905001004007140d100b04d21082e550f46151482508040c01031101d00c41e440c0d2504e464881055035210000c0d4045103d2100300901c0386140585070308003d0003540501814402080300f011030808010030210701500c0070046d0ba004801003600048030f5200300000c0c80d01c103c8550348800740d485056001e00207100d002490640b0700001f1402c01c41d0940d00c48103d00350300b83c0c0c2e81042d5586245841213180b085001700c0b0128142170007503403c949000401059403031400310581c2c00c0d00e4954402c551810301d180d04245c0c1150403200c0e103000b003800c080000350040210f501d00703241010300510002d400c3d441e10382c0b40c0c0d50146465215a0b201a40200520701c031041014008656030001c0b410444c0c26801c0a54400c61190700700290890008107202c0420b010314540c00c1240a10b4450b4000e01d0108200103500701d041c0445142c0c41090541c0c918068041c2441c69203030003603411114a407480c00c440058000c0744040407840001c2c084000c0018000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 638494208 1250 638492958 638492993
    0x30e04090c0e150306040f030905060c060f0108070807050405100b1c0c05091c061b0c020a0906060e22020313020f0301060303050f1c02040b0406080c0918071e080121 73
    0x9900c080000c0c14116400d504607001950400c000141030409004001004ed1040c000041401d0481e40c0340ca0115448540e60302c1200210707803001030280702ca032401e0340c080b40c1c02c00101642c40c282d4543d144c005107903a40040c0700141c0400f50382582000c6c070301241d0103000d200754a60302e44585404150400501031440d036016004d02c411044071080d08000c8207502c0700441c44120080003030038103055100180520a410422030250444180001d5510050b0040e8015078409450f004500c0300c01e4400d00800106400c84449040d480724030221403c00d552008501400984141040c00d1442c0d0051005031211349000354020703807405400b003002c00d43c044141c8828210414000743e481050301c03442c03032902201011241007a840010f0001b44142c1c01c100500498406848890070766552103481049401a48610341e004003a078000d500b000d0401c2144a80d00901a0505400e40c05035131000150f1040c003020200082400c400041c05501e00c06e00904140c1103c00040143c01c0f6055640c0c00c00242d15042c0e00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 638495458 1250 638494208 638494223
    0x302070e060901030303020a11150108151b070c12030c020108130b01171e03130609061211041d010807121a130206030702012301060c0f030e04090c0e15030604 70
    0x1c3c013184510039026404c0f561940801c4508090b4614405218ac1100307124038059403249050f4940d011848174400c40c8174000380e250070b4000d0b15034a9000c4007a640500320444032082514404103643d000440c80301c003014081c0da01d03044109184c1c4005054554040c0c03c0307940c50034a0225100003c5c18409090b030558202800c02000c400c0000300080c5820540c1500e039402c1e41d19140c400d9a09100000034184c10103e9174000c40245503121001e1b0b0710414075000d841c0c0012041040004e26204a0f00502c4942c80c4640100d4a0f051759015140f20380c0139040c9141034070340c5011380100481b240030030200000e85140001e00b183c103105552040041c140d89200110401c05a20000d41c00d0230001c4404c83c0f1154024024039070324504144e00900038400e071100c2d095a0407103441c40011185000b03140074140d54041c0c0f1005465070503074442c3e6107407040d003c0e0210200500146048080c1e02e91340501070344507214407100c035001d904103449112030344002050000c3e0b24091241000b020368002039404c0c0c2182e0401c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 638496708 1250 638495458 638495467
    0xf0f0c04032105191e08010e070809031b031c060609060809010b030604050a051507050a1d041a040b090721140c27031f0912020106030302070e06090103030302 70
    0x41c20350f210f000c1c400341d21a455100034000a400c6400144107946030b001c8499103200c0d00150081034840400038026030855541c40c40000745d001d80562031080d0002d100c14100d03400c00018043c40140f102118010030601d41011600e4440c1c415220000d0841c145000000d01c503030360529100134400700c010320500c1d040180d4200400d030150000e510a0040e2503016098908602d03285c205542d5132722040201321040d22402d4080450300b040010100d0103955070f580d4003850300c1e42200c01100c1218101070103648000302145040c94030703500d52085101c1d4080420720074480744d49410801007224400c055081c014400c410800c1003042c0d21404401c1c0c40c5407034106059495850b420403038010261000c1c5818034007400d00a0050400b000d8000d01505200200400c0c5260361207450740c011030490001c01905580b1400e80740030410383c01240000d41405609000400154a07110303002900b001424400c0986d545980074818158188508000b9103d40c0c100f0220314100040407542d412414071010302090b50104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 638497958 1250 638496708 638496773
    0x1003050c04090305040e0f072303070c03020c03060412020111040506092e0e0a0501050702090604180c03080403030f0518010c170304061a15030414030702090f0f0c0403 74
    0x15580071b4070000181000038a850034080d4820582624584046025040105c813641e0851045d503140094099807030b41075489504040e551120510030440650003916440c036102d40301003000610441c000e41e01020221a00d000190071075540d8228560b009004000600054560342c084490280303041e90504103500d0301400c0310300020308050307942e1070a042189120300030035030041035014116400c845031500701d0703901c400540707452007002c800035002101c03200040c841d032801741e11440c4240110050092210065510280756400c290422035003044042001e10070301d9400921604c251a0504017140307480c59410665203442285441b140c10401e002003840100b100d54401000620101c04403540c403801c0500d0820090211a2100400f010304030501088918003144500d410100e18500545503454a8440881130451001d0701e1409103c10400f900c016203445010038484c1200010320501401c1080308210400005841510034550a000a00119598250711104107072858000c0c4200c42099 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 638499208 1250 638497958 638497967
    0x90103090503040e040302120a0c060f0204050406031410050f01030803150d11040b01030513170f031006021c050415020f1015290d0e0a0303090203061003050c040903 73
    0x62482c0000b04000031018144071400780110b110380c0a03030f0140509103103500c2c02800789150540000e0100ca60120109009074044001004c80340405807809440d000030030265456076108650008003220f5107216890305100b41d130518005580c06002500f0a52420b240701d5406000203804a80004081160001005540c03041182c0192440341062001d007000401c2c00b100d034507814022400c002c91007a0340e6103c1e11980b4442c25500303007000c01c0306140d83c8070401c0d1a82c8060b03410349400401c006848201c18003d02842c440d444405c0d00c4041581420002403c00309510000c103005050f0034143d200540e0040266801d4900b20781880ba038a0900c2740040b454000360903052485400745c000795460403111500f124540300340c00c080041c10b641d036071002e40200c503201003401c0c48080f407040300c410320143c00040203154405042d000440c020070144516400d013a6490340480110755184181411400c041c01500c1d400303001e0303403600c21680e403071622110b8484840201c0d07184034560300c400950416014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 638500458 1250 638499208 638499221
    0x5030607020a1b090501060c050f0708030a120e120915030408092b03120e030c070b09150d090b1e070315090f05010603150b04030204020d110a080103120e010e06090103 74
    0x4072824405c65a64803006009488080026600b5020b40401c4050030b10340011804122482c5074020742c40c01c8200481101c10400e51400c0100f26926503001002a207810000c03042c80001d10748030b40d80d03621564800c2140e8076903180c070b94072202d006c14020400407070707c000e00345e07941200107440d0881010000ba48026540f50740007015650350300c2e800b2130041031640c84a05182d0003500481c08201c00ca400c480704039601c0c0070310700a6107000da12a0702c2c140024916240606110b20000d03140418070a45d84082940a030404074145200c0c6542d141100c00380036548171002c1d04a101c02d240c150f40501548122028540b0051082007450f4a80c21180140c0110b04000002003641043c00c0050b0241e5401e86005131100b842a11300290502044042004000c1900d104540038003824514181c695401d12019400000b01035058641d0b4240715501c1d1003032a00200a0481076607075100703043d030451420808890002010f1003c103c00300d68140c4c032030f0760000c4444204100859105480b81d843c0310040380903045 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 638501708 1250 638500458 638500469
    0x506031912051602132f0f0d0204081c121103130c0504091a0c03060d0b07120c0e0411130b1605031b0d021209040f0e07081605030607020a1b 62
    0x400e207125500d40b0826a00503a2030003205001d0991416010455801801b41d2076580c4101820411801c07035800405c500402c1d50400034200541815505c41c002c505240c500c15a540350b4000d0509500d4480c3e0303005106201c0d1200d006402c010320b00800c61807200c6030000030f002214507990883d40c034050000405003e00241801030003808501021310b444211402c840302c0fa030b2020207540740032504401039401500e2140c0301c094102c0b031a0481d95169070790110300c09404602440014022124840f00e9400740103551041e540b5a8014400500b0901089071148a802d40c44040c081c03050914044c4000307102c40464084c00015a00c0e6004010000180d1303468100041540c400040c1d02c00005007100055141c4400c00070a6a0740d0b100000416030302c405030b1700300380d07940003108000001d0607203001c1c0d015200e00b9a032703200c00044410a00d407605282c9181d0390020764480e070190306c15807100c04c031614407030004d8030080c1c0c051301c0d0b241800321002e07544a00d105c1001342441480c54008162030030000000000780b1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 638502958 1250 638501708 638501719
    0x1d0c0f07020a0b04090212010f05011715060318100c051902100e060105240301050103091505040b01090b120303040809180f01170d020c19180506031912051602 70
    0x240d0300d414003002035000e0391f64018580741d254000031b20300c0901e0f0140b20484074107840c0c2c4910308078521501800341000400d000039a040100c8601c000741c45181c09544501d888404400c001d030b4005140914007103070036020030300c2e031400c00d240c00111950000581d01900c800180204041c1403000c4240e081541e54015220703a6484d00c181a03166040001c4e0450403924250b4011034012503081d001a00c60b612510342c071403403040c1000108629403199110f004610b0240c600f030010000101090401c1d14030555003590340100080c018480025a440740c96016030013104c0c2101c0140c0000d0a17075807640070080010b030911074040364412a54446422588150f04985064140c52074000340684101d08207001d140f040c05000c10901d00d240e003000601d40715040841c5c006004411300f04c41005a80c0880e5898051f448101c4400090340c7c8152207694100d68008081c042241d24004044c90301e42900d2070004411350483e800c000c0003003403510807401e181954601d00710340c2d43e8518070402c0c44d00c9507414400a4005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 638504208 1250 638502958 638502967
    0x907140a0314040c0f0608101a0f1303050105060f0916090305120a08070509030c041a0607030201091b0e0c030714190818031804140708011d0c0f07020a0b 68
    0x1031130344040e609440d00e81e052a00c1c07081c0c54410444601504030380c100401440c120052050700d031680042035905820703c164625050a0319840c861b80e41010000364240070700b2481c1801080001c1c080e0302da0265042d501c42001c4031004001503003c400c0a0310051f5411400708001105030321950a40c00615085030807101d068811b1b0501c5004e640c40b034200c4000096001d804680500c0c4580b0440b651024003c0080c0207641e0310400700001030042c0c016140340c000034912030103220f0b00c4200150010034080c5e000060040c4c40350516520f820755007202e0210b44581c126003403004820000030150004c16174924692259140c51068603029881441800d00d418041001100d00c0304110120b1806919592040c4083d00c42060154810040c0000001550414805460101c0019541c180310500c001c101048400d2120380c903c0030448155180c400048040d401070001c51100a541004400c90840304d505503d045d41944119000b64036a00082250006000e02555105800780015180341821240d40c0e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 638505458 1250 638504208 638504213
    0x50d0221220e090d0201050c07021306180b090c0a020307120c06090c1502010b03030306010f0306120305070209090a02030c0d3e0d02030c15070c0e06010e0907140a031404 75
    0x2410b804481ca0305040c40350300c0b81815868810700032a8024144d0000c8903052102030b50802114041c240000d0512a80d03402000030389031031641004408121440e000100c0515a070300f4490b00c0100109000340b1100b08101c4891200da000007122403154001c805280c0c0d141c10904c00b02c420741403968019045a0030b0040060038440100c01001c00c81b83c0c81c468803281c03101e200a0690981b01180240e950541041c40040c0741540100b04026030714001c0d00e4000b68440e10341c1c007101300c0c900d1207104c250300007600480c0010441c02e0405005800c05030b80401010500340d40e9000a5450501d808118025058a110b54040045076218211501120411004450004200303086501240065003c04c4d00e14505241d0a505090700300c0d15149802a0146c251401500b06004101a1b486081c9e072a400c82080468042240700400c0700c054080300c07644000604041c0d000610054091444c01d1040700c840050061240e0009108080c0d008401e60080d243c1d01120819402401021150002d50340484208001c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 638506708 1250 638505458 638505479
    0x3050d0c1701080a020117091e0303010305010510030c1a120403020607090b0f040b030c07170904060f060c140309120604020909010204061202160f0f050d022122 71
    0xc8503690950100780d507aa07100c0c403141d0b03640c040800290204844051100d0590031560300d40394821075650885001c1a0030700084080c40e52048403083c183e8001000600c1000002c2c002c440d000310600300b0005082d8115201d0044499040c800e404041a01c032140074001c51004055400303060808141b070703c0c24506410080c0d11842c08403900000101c1021022034402d03031b94400c1d02d01d501c40e00c40c080703070406003084034002583e030020b080d402c01a00144507031400544100d68103501a811510b00ca52900020b2050006171031032030f0445642929044403d002c045d61045ca900820354010a914234140d040900041c2980304030903c054004010f04a4000d078400300288041c0100d1081d039892040e0756412140364200c1c0105c3c094080020418070100299100700d40140c01048003802000c90900520ba60348030034003400d004200d4034131101e1a090818408240420362960801380040c0c4400003d00134900c0084da00920a002d0085000c80c071410f02c03040f0500c0350941981a0100400f0007a02c5000380702 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 638507958 1250 638506708 638506727
    0x1201c1e0f02030c0702090c07170a090609050609211c3c030608060709062613060f060b1201170a060507110d120b010203070c050d03050d0c 62
    0x100c6560030080e4044500c4100d20032240f18210380460103003008083c1e42000300c040000f0f04609050042440701c000480c01d0700e001c440300180401c90311603403182c2c9044050a00e00c0e840c2c5c40002800b0707a2407410011307911142c04a0325902002c840c10701c0351603e9907803150041d01401e608007500303106200103000300174150701c0005c44400c001e466804e40031401c400341d000a040180c440f40d41c2020f40ac0b49006000140f65841c0c0948003040c2000f044d506d4803525410318043c1c1c100c8041000403045241004080e4106a800380c240a00d0581303c59584003e00c543d01c50380d5005007004910b905840c07100d10502c000c90380403c0020396118070034403850b079586a2000064000c036124130150015100001603490705150440c01e400180c0c03002e0107500721541c03294002080010001360502c9514180daa8540c0e41c148418403c401841c0c64001c5004041c40e4000d045600c80550315056600400035800451180e250b00303001c079041107541c0441500d00d403400311030354007804050304407490501480c074551030740000c05031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 638509208 1250 638507958 638508011
    0xa0f021b0d020705041e1d0a11011710060807050405030304090204051504080705040f06090e0607080106020c010c020d0203120a03090506062b02040b2d010201201c 72
    0xb42c2611307841c0d0b400c100c2154202030003a00d540e440f0103403501c2e4450790341e08641c004c004240340c0140005103032a04d86041010f03d5004a45080d2104c46001c040e41e0030490b141c1c882200d403041a80140b800ca1050a1510594040c00050121600001d4010346c814002c4502510000c1d007581e4032140c0d50156207010350014045c546c4158080c4d12a10f120031961816641213508140003003040924140600c402801c050030b100144035100d91001c03512000d5030098001d03858001c8010325241c54071700802450004103800250440d08a011180f599a0344490f42e030000310340403150802c01c1102480000e280181450405402c11380104403a2a41c3d034155100303c0d000c0e0302850555140c1e55501c81001207124100c0b180e031619055940b865404001e030340000018051001d000091048004000600385a4000320440782c03503099501c101610150640078a401d6806c20700003400000b95500b03000c0041302099001c0e9100170804500c0492034100704200144110349400100601c400c0e038030002022240003030340d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 638510458 1250 638509208 638509213
    0xa02070c063618050108070b07050d0e04020409141602010b031506040609052d130f0218160306092a03021c0902100815040c09050306270601050105030a0f021b0d02 72
    0x603050003100c0490303000c80e5008ac0581502802214280d07088050080d481c0e40055091102049040b801d201e00107400090710000d0aa51502e15583c41c1d80c048a00005421641020803071030943e20000743c0181111002c900040702556802d000ca002010507034021501c40b400c140501520800056400c04421240009a410801c2105101800c140140d444058600702203040c80c0201f80300d00343c0200c043e8801130035802825801c0d00800100f0701c05660151040841428603c075080c1c040c860040103200e4501e051000c24030007661559010203c00c41411503000140340740f0450342c4a0750450301d0b9103c031080c0440b015001217480000a0000a000300d020340031004c9a940040d005138011881403a90103401c2103c01c48200600018100e85000d00091150414002c204e5580900050303208581071000f001c4940749040200d01c035820a00074880c85600035000521803646e0090071030303611007080c02000c12500c0030701140704001d102d490149801c2089040d000d948840020442031000661a0308 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 638511708 1250 638510458 638510473
    0x714010f20030c03010509040602070b0408041d0606030609041e0c1d090a020f0a330c0305121003081306030605030304080c091e0a02070c063618050108 67
    0x40c1c4018900c07040d41e401600c88400d100400c40e0313282c6024000c0c0e100e44076040141c14600955180f101c200411349003240c082c4d00200e801d22001c2e1245c0e000007400c85a09046222038105000840c01070320024100c280200714520005050080038039049030145803800440341c04103610300340116088080d004080f203041030030103018070921b2045000ca000d411208003810151b0704030703420810b45111004c1c40d01d8000941c80e06c0017405024050342e28400c008044843d00b4031407a618241d04010f00821203480502c0071b410045408282d02000351030b1010070141b011800354540b0b2036210040900e6500003862240b0002c1c03000c03d0721200c010390004907452a00e00303005580e01c0c0c804040c1c81c0d006031f00818110764007090100929140c400d54543d041281d0480b200b41e56820381030340c1c0c0d1911400322010424190000360810400003000c1e80c4074001d00086c5403003071000341c4c01040002100b004007030941c000c209140c4841d01203091208480010021080107204c85002c0c0382e50000500800d1140500f940107040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 638512958 1250 638511708 638511761
    0x3020d14010303020c0d052517010e030403110414130b1005030a060207060b09040305070b0c03041a07021f0f0614060708160c06210e03030a020714010f 67
    0x4049410790b0383c1a0098041c0080da982130100c00802d4500544552041c14204015800d507032801c114407500142c0e03001070983c02c04001c0402506c828004441a84c540358894000f1030010068600f9242d004080510701002c090028016006070340f00100141070401c10700021442004100b4015403040c0805085603890140b40e0b0000000e03882000e4141d00080c84080005d2082d07401840038a2040c0c40c001605103c0740081080e00100300c60840102e10002241400e1000b9005419804602c505007149945040d54a1007001104010026646100b610100740d0701802030100300000c401c03400382c1c220001001c80c00000504420100315103087c0c985180403031404004525180c48000140030585040110341c2d4036407940e4040c1d01c950381d039000c6070302240c400208c0800f040300003469281d8589601b14840301c01044520340011036403451900d08204d6800c0700d1030110030349030b000141c1360006880d00c000e030421a07802c00016203500781c00d51074003008003005100da034030242203a590118084802c85000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 638514208 1250 638512958 638512991
    0x6090c0e040b120d1413140a081b01050a0c0f060f0b041b0e12060a090b06060306010f0e01050f0705150f0403080420030a03110f1209040b0609030d03020d 68
    0x3618411241d00881300d040750050140707030303201501240944e2003842c10852602c1d1882c900e04a07000030780c44103071001c0041c83c98601045101c018090080103000480c0a0f1004201a00d404a80c007c0c14800c001c0b1b81c0807103481c0034840c3c141800d60004214001d06d00c4a00e482d8000b00600e20b500411030b45400e01c0000d060030710f80705a2205080c1d03483e900480401114080d641550084038480e8410b503902401841c668080c451303180699084000410300014900e044c440c000d5000303080c54080c18061040005607a80600f4540b540c5155017040c07952a800f10b0012202c5105985802440080000e0300d2000c11500085015a07403500001030b1180d9107540702e4024400c44180e40107000102c415010801090241000751103a9901442030b26010034000082030070b00c42c49000541c08a0900d413108140d20b14180860b180441c80c0d04003600c025140e410300c08210b409860000c034003480d501c40c1a03080d141c84500440e80f00d404018200c520090401c1401006580304000d40eaa0780c0341001c43c03002295811 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 638515458 1250 638514208 638514229
    0x120c030506031e10050a18050a020307152003130f150201060302060d0e010617061510021018061d011104050d0f02300601080307050d050d06090c0e040b 67
    0x203201c060b284800b844d0000c04058000641b031250032941e5070341e0400035006000c403642d0341035200d000a801031400300c1c0105800d01c41c15502c4a0046808290b0003a40d040e4489850300441009407000f16100c000d2080c494614000c01c202e602000c0201c43c8003181044049203030300102c030318042440e00035400d280c0040b03080c1c2e0283e20000b034002c60140860941c4070301e240c00c0142e42c0745205c400003404035980d169a0700f042d0140f0070314440340e41010f01481a403114042c8050205401a605e5a00c422003e80d4000c1d525602031021040c40c07a0703240d1580e810701c0740d070401c081d0990341c0000080c0509a8941600350b514106030103100f80561800590b800568005416281143c0009019100032f03c0380f61a1043c1030700c589e01040740e1014203070700101e003d0182e600418442004101440411a0f440020246800d5060308041416401403003450006000002d81c0c001114003450429214081214048090074440d040502c4080c100b00c0724403107203503220542100c3c03048125400c0c080f8501c040d090007040c401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 638516708 1250 638515458 638515513
    0x917091201060e010501051b01050a0e0607020607120905120c010606020709150b0307020a0614060a050d08070618060501061e11061501090b131e1d0403120c03050603 73
    0x30140e004000317542c0110040e021984d0007a00f0041c000d40c00d0354143d801c4500456500c100143e881400710040789040108c00c1c0e20001c80d00003409681850301000c1e00d500748061200303070b4044e2950110010172030140074180700301481034006900d0f2a07100050034040d1990f4002ca0300144516040000d05403218010400203c1040c58401c50b03c0d0b007003501074000d0350303c001c044d4004e5204044108000404c3c51080558109034066800c025062910410409007644d41c0300300d20400800c012800030a407036900310b408080d4041400145c0c07280380000c0f40081800407a02610503413a14000040c03a94103c501c21021546d5041060200381c1741a40c00c0e0380c45110010700c4220b81e40440005940202c920143c45140c0605043c4800b40030303543c0300d030260658003602400e402510440401c2113841c0c140101c155002000074422407035581130010030550a84285288804400c503230000c43c05050040c0c9100c00010040c0500b1f1001a018110140250400380c4246000344203500342c0075814500d0418610f407011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 638517958 1250 638516708 638516729
    0xa02030d02071202012316020f0123030618090a020114121f050d1406060103050c0d1a06221e06030902040b0603130c27020c01091709120106 62
    0x103072203400440c2c24840301000e01c591b0312102d0400d090031074502000b8004607035207011001054401407040c011800264400385040c0405042074410394090201110328904080c0085a00c07544c8400004e503c00003001e209580e103000240a10004e03100100340081c810f8000c0e21000352200ca80401c03c420b40c81040b40780081d01050201240d10154048014003401110b210680115900c81e00007e0704102400400c031030510308001c0369528564207002e4203600c500242001c01817842d02924646c100e2061200f000801a5124400b902801c24400800304900014000c80e4490b080304811498080c0580402010b1072030201c00050140c4046d4203000b0b052070987c01fa5156549000d03020790282000c0502240c5c046d0320f501d142e00541c4c440720080d610503103140c9100807001230076040041c60000b007608802140c0301e95810b00004540000707044c60054807040741c0184d40d0240301c4c61180c0181441c03e402080d003a200d250b1002540030344030261056140851341407180075905c0c102c00382243c113244501d20040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 638519208 1250 638517958 638517989
    0x60804020f011209170d060b03090703020603040f0f060507170402100f0203190801170106051c11120c010e03010501050306070e01020708010507020d270302190302040504050a02030d0207 82
    0x6511400101e444000c010101260b414800e40d00c24a0314000c0c0b0101c5c21507840085014a482d00d6130340240401850f4241c00c4a1950400195030380c1c6922060101174007481c0c0010108041200d0100007980440c3c01c00101c41d03880c1c00501e850700140ca0140c44030700018906d40780e14000a8081c400c400c0c011740e40200800003e8134801d2060b030758942c070f03102c0350400c0d80014484000c141e0780010100000090399520102950f060026410510003420200300c166854400180306e1a221020f508100d10710204500f03802206615010710000080c00c403440d041f5a14224050040c10001111403200109803251310070381c6e0b03040301494229013092003125450750112010440301b0340507141c881c0d0b02c5281071040c0c03082c164598542c1030948000307a0f81900168001c601d130101c0c00f039016030389081340c2113601006180d0f1015072743d0220341d04c0b0031400080c0c0300d405400c8207103108003041c0860300002d55000d0000c1c0031600c1c0c2418107603100c0b16068416801303405001003144402d0701c0400c260050300e0500b0030071104d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 638520458 1250 638519208 638519239
    0x3150a050a0b04090f020411070803040b06060405030f060108010b120a020402030a090f0c0e06060a0e13150305070e1b04120c0314060603070f05030304031103010b0613090606080402 80
    0x40d1030041d01c200e5101c2c2e580c15150100c0c0d103650040701e0f4140c0c05000a000071408a00c1400200d402c10080065546028000309000907118011283c00a402c0200e070b980030b88502d000540782e0701c40d9512031681031040e040d25400803a00410018100c4014500803c0071418102c1805140090018841160342040304000010700e000c0e4080c40e0002c4400900203818207056130707000811304220006441b080d00340d40003041440c80c4100c1c050b5010000b942e00d142411841c8002501c084c3c10304000794861080c401c020074180c4196800240f101c0e181448001680e0307600e041c50741c1c41c1c2e0418016401d220b901d03100001e4070b007000d050f607005070000824522480c084c904406241c00000345030040f42d4490350f240000000c80c085a840e01100706425002c0e00150410b2401c05103030240755441300c1c0400c0303a116002c000c16a008425242129004000f028030700b000403000a0042c483c811806501040108a0000f806480c050300000e486040b030041108946540082e01c0c02c42c4120f5000354085540b0010b644c1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 638521708 1250 638520458 638520461
    0x2061602030a0c1e0807050709022104030e0303040605040501110102090d17040e0a14130506070c03020f060a0207020a08010207151d1506011b0b010b0318030316030b03150a 76
    0x1050041a00300815014a2000c50300c0208602066170203002c045115403c0c0642802100000d01c4904000c40c6450f4100e2442c695490030120010a820074490004e0103242c02110103451a00000302034039031b5181c8035500035005030003034064203001a611002a044840c01442112140d040c0101500107400003956078a664459010025a042d45c2c1072200091000064a215000b003c801c4004540b91094202103100d160008119112a031a51401840400c6020901a0300300003186410241d20405040503032030510600d0380b0a00e6880f84500f00070041c0c00d5507024010340c43c0708440700500c0c030350750300034150903070007101006880410002a61400389000d9031003070499042011224030022040000d250914030381c142d81c41407100300030040104940e03004011404130032802802d00808200e98440c4407501605005403841807400002140c2c404000d600f0104e50302d510403049980d41d05c2d24142d00b00040100c80d00440209041201c05080d600d0080f418203140c0b0b022907801841503840490580 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 638522958 1250 638521708 638521727
    0x60f1b0306151303060218090c1323030a123c090315050403270b0d14041527020411090310090b01091808130e090d02061602030a 57
    0x31015210743c100000040c0131400902101c21610441d4420341c40c010050065440c4002c1500c50705050400a6035121074045028005440c401e1144c1d52010078400c210010901c1400c90407170341849048148410040074046d00c080820302e40d942c0d500110b040030a08a82c407950f070b15032080407040c00301034401d0f0b244002d03c90103132501140c176000c44c2c1e9a03030300e0b202e04100404045034849072507240c8013008103240c0c1140460000c80a0f902c0100102800d882c1c1c544821241405001c0e803821703000035500504000d03a001200542008506480242040c0c50040804140360f108104454100300420700003504a6014201eaa14900519485c02d9259401c01008040200d00c5002001c0140308405044d2010801c0304030000c141040007500f43c41504000000c0c20059005540260604045c80c0301d50101c414084c2c240c60b486101d2944450144000c904190b460760011a4441039039410441c850500194081d600b01039a000c2d80d005886264110456070702060000026034800c0100c000498031555061 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 638524208 1250 638522958 638522977
    0x312020a0c030b10051903020405060604050406060804030e040203040b15211b060f0901050f0d0c0302032703040513061505090307060806010903080318060f1b030615 73
    0x25018600140d076901d4210405400c2520038000300d50400c50303440c00e0009000060801101c418040c1d185105901c0c80007040c0c0d0100901841d02c80d07022a072141c0350801550040c0074010401e028607a12590000c01c2c4503003c84040e070009429140c2d007452070a2600c2243d00a94014901e600e05580b100380410307001040e038020741d400031a00c80340c0551200410b10004040380041c406443c01c4240701d0304000510b00c1c02d02c03200340308600400c90740c0244454001101d03101e800a0a100b925034038441c4188066002e07240408404600b03002d00701c2c248030b80c15801140b240f4040020503042d04012600d070031404d441d8028024644d8000c1105012515056005920780b00003c0000b1801580b01c150f00c14046044c0c85422011550105480b9001c0c81d007072001b503001d000f1a00d04004185408170000301380c8004c074803001d001030718000042440200c40c0c030b00d80c85c00038510000700c1b0a107080c082407403005a4022164140c0900e18a0081c0d4840c02800d070031a800b84070000e0101c0703d407022102380300d03a00d5807016030403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 638525458 1250 638524208 638524213
    0xc1309170c0307050727020c0c010806031906090204112a16080c01080705130612020403021008150d0206030621100e0d0306080d0f020106052d030d0207031202 70
    0x110014a080110b40003825040301400c100070440c0e00c4a0750b45000e0307007641b66905170050000071042040081e4408410209107064000c98550380c0c04641010036040c8001141800c2e03604800a0040c07a80007000f005100b0358041054280c0e0501c0c0d030b00d040c020083c40980d2040711f5800e2800c2400c0350314010095900000a4408921b00034158000c0081f1540c4a004180c0104043c0c00c519078110304c0c6160700002504041e89003a07004165064501500d0054005014040401080040096041e20091035000d010380034030012950001e41052411502460325640342200348016090000040d410164060320186c207507100c8504125800345110400c51603e110354000301c15a078001c204c4080040c44020740010036050f50701000f41481d0280c810203060508000c010040d6607400204c110707200c002d51a0124441021800490150200d540050b500007141c0102c2c8001101442e000070900705420f050030341007030740c682c189034684039071004000240e0031107541000841c150504c0840c1e0b4941c280305 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 638526708 1250 638525458 638525467
    0x1b0510050a0b040624090e01060c03050403061d120c1b040b0312070308060301050403052a070b09040f06050f0904030e09040f11030a020306150d050a050c1309170c03 73
    0x1c80e00301c41059200359418800c0b0032404448400380030031160082e105242c200746c114280510302c0d65942061062500f0826810300280500d0b00c1442620040c5a2100d0240503c2030f80c0d55817191a0703100c2000d440903c0c040c1e60044141000d103501114103014255010700b4910303013250b00908036400540c201329042034a5800c0c50740c0c56a41404400006010341c4200303600c400346030500a00c07049000b44024001da25080034400402e0b048010346104c8170200d91414528248085026070355038031f0003500000751050b00008910b107c0401d02030a03d03c003007542c0820408001c0d46000c0169030480c814960400f030311110590710780c14404481a41301d400f0b414601503c040881c041a13041104503426941c0500307080080041040c982201d0170316400c120001c0840c0c05c03840c0c0020391184e8010704070000c1258002c4c010400790311a25403003082d894200050320000141d504050351200007400f0654460408401c501704224118803e119040d5000240098030714030001c0006491b0f4840c7c0c240c070980340300c20310 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 638527958 1250 638526708 638526731
    0xc02010609052e0608041101030f0e0706140405060712020f1203040c05100f0302090d1401050f07050c0a08072a1a1c11070c0f061b0510050a 62
    0x32180245408902c3c1c00c401100946000320110b5280c2c40c80d12000050841000318036844403020390040c7c1c00400344d050114542005070001e000880300d003148981880e4428000403400f1603401b040f05c01c03d845680c0b80040307150a4401034170641c0281503200f0400e00034500406c0c0076030950b03640c8000c0703401202ea4900410012510348100704904040584e0000b0401040180301400c080080000352044500c611110101921400d4010010710415070702244143c041d0b55a80d802c03503031141e004114201c001d034503607001c0e40c0600b03030890b00813050030750250202c6d5030a4810b07001c94040440c0940a400b115443e60b80b601c8c0326a01c600e2043d00c00428246520b8030900f201c2071a104074520341598050141d03e0144580d1520380c21950748100b81b80103009803201e03e421030f140c0c06514001280009406c500c4c100300040d090048120180c02c02c0412000480d5100d03540280030141e0741c10761909200c040107500d41100c1e420440b40d004000780c0100203100d0420b001904140e03008920180003007008040300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 638529208 1250 638527958 638527961
    0x1e190905030c1006060504051320120a05010806040203060a2d0b0a050915041107080a0203040801050610141e1303030311030f010e13080409091a010f05040c02010609 73
    0x31070040c2e8590080b20003090300304020300c60140140317a1403c21030f080c10b00d0b220000302c045841800034a89140c403801881075216800020390fa20b140c28200c9142c54401c810707481c1d10000340464420410614210021070002c4001036401c0c4651f078010003e103074603641c0e1814200030b49202c48081418003040d01c06481180c0c4010401c0c81c120300c440d2000511001040100201000d450380500c8c0114141c03407d005130000045800e40d000c180c207440224100c0c04010011040303104400300039001010100380080c0403580440140100c0b1482c1d0003d100031303100c2004103c0d83c0d01840700b0400c0441e02188120350440942e802510501c40d126105031851420b07003950701d82a40c041d50742800d2041080409000309505442050b4000102c0fa10141c114600600c0030003031800103020300342010310101c00085c03c90040c0056406240c0d40500440d0f00c8940d560103030800350003914400c803000e4043c1c034098107064940c00c018a0480340005034400c0218034103010f11004160501102c011552175100c00300c0e41c0e0320507 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 638530458 1250 638529208 638529217
    0xe0303161211091e01050d020903120d0204080714030604020d260408010c02030705031213060609020d0501051e090c0705010614040b030703151d060708010e1e19090503 74
    0x1400740035942c2d03c262040108410400c402e50403081c010b007001c0c840c980d84c86025151500720110b001a510b1810500181c6480340b1450240c0000000295824041c5820340103841101c170038908a94500d40c0381c55440c0d0003c0540b552264259010000003005403500b50755040700b040c0a0034115034040c141005a075050b42c801120303003039411400601000040710074481c0289030034603031001d1410314032a0f0307440319100d00c0740305400d0303c40340d12580208190607010f140c0d1103109548540c08001703841c0d41c0e06441c0c0c003942000310160b00d020320380000001d46051120f01180e150001e104900c5813440c107001080381d80017000d4481605500c0611441e00059001d1142c2e2014007019181102244d400b14200401e9510780d000b1240240c204d4581040014601412091403086440000c51001440c0704560003011202e51110201d201e2201445146900040d800e4146ea4841c1600321403546c0e4425040c03510500b401800424031403100015a00d50601c81d1081200e03410f034000401c0030002921003d00d076800 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 638531708 1250 638530458 638530481
    0x60d050412020606030c01140703020304050d0620210403021009050c03071212080c21060102060105120307140a0c061d01090e06040e0c06131403010e03031612 70
    0x1070380640000d080d404100c0d8651250301240140241c02c0840d000820a01041c819400070440105808003094003d00c05d0307402408001d0a01103c1d1840350400d00040c0c040141d051420015800b902801c2203e04011944030399a01c200c06039114450668000d80c48000810950460180c0360482c034080040d40600c4900d14019001030121040ca5420035090105590001c1d1800d1407085030000080c2c4100b10390511a415400d00307801c140c0e40c40311410700f140f20f104561007003806a0451840745080204100340200c0b000c0e0308039041a80c8500500111031405d0081517a00d500601c080400203c903810300b0545403010b1802e54000303c140e95940700c0c15500356007044011484440344512141c040d24544410180c09180910103185003d0303010004070006400e0034000c50b100e260031240440c04224040a0359005400301da80d9412400c9a500e01c007400d030042010048603003556604600c2d05014404422501c0c030b010314619200e90300301d1141e804c2e50b103400070300388098440351070350102541c03291000c03401 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 638532958 1250 638531708 638531723
    0x1012060b0403110901050108060108070c02060304120806011d0d0c09020d0509100c05070236090f01020c0d051b030c01090b070f141b0601141807020615060d0504 71
    0x182036191205811040380c410f24007031450f500041000d6030740310707088641003c0d00382007041145d203d500c0101c481e000d1400029400100000c02c2c0400c000420050784a243e2460303580c0f80390b07070301c0d00001150041002c850705d010104000d46950a070345070400c140809070388560b024440c441e03070310b26826050f82c0022141c010740d15920700c20404541000c2c0804d108044012004101d20320540c0b034050054001d100b0040d02030720f81b404030101d802030080d44090000c0d40072007180c0c00380c90000740100c54280040380d80f04d4990184030f2003890103c2050017524540e1603000003403c6202240b0030201c1313035234001c00071100d48d402c0701e1203a00c80c814000744020020b11035094002b003881205400e25101410010785441c04010221b1420282d00f0351040c0d8000c8140745c0125160703920180c140c26140d000030100d0f070700140380c040c4200000d1041c40c0009078260f000307001c0d141500a880301d200c07409290842118a4070150700000000b8042c690326a60a9000010051000741490f00c0c03c0310303a41c01c640084070f00b1120b01 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 638534208 1250 638532958 638532967
    0x140705090a0911030d05040b03070504120c060f0c0f200a09020301140604050603060f0105131409070903122a0f02011101050c070b0441010506010e1012060b 69
    0x2042c0c0c05507124060f0b081c1d008002030711000c02c00070200d00c038078860030044d20030100c00f05000a11420840b0010038030075540c101c01011500b070015007000c692161001080e200e41d60200114000c400d80001d4070303000b24401450030740c2502e13000d01e0300c0300082c0b8858041440880500490b03981441c0d084c041c2200200c0161298180a803031031203030717910030800707880380006020030003290b502d040850380c0c01682550001c0548401d480103884034042c079911f510b54014102008140320042100c2d0000c5110203c8036148a5100c6003070a40d0b068040d800050540209461000742c541e0203908840481d071800d84155a0741c104032580d038080104200f00860355911124040300942da4850880f003115640356008000c18140840b00c2d40d0a13205940c0b0050600851100090a00c880e0f505440c1502450303861b440c541d210804000008100e0318101c000110581307000303d0003580070501c13030548503c50603107800c400044040f0405c2010602c20f04904104000340703e620840d680c03503001e402d00400ba6000c0c00c5488 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 638535458 1250 638534208 638534213
    0x3140f010c1e050d0624170606160c0b0703051909050a1401030209030a03090515070b280c05090a0e360105010b1c0b010804140705090a09 61
    0x39904584050740410401c4000103a80c0c035815003180003404901e0030010394807013880380e10b800600200e80c010070f881101000d460000c13280c00e00c00080e614001795a9000403c44222008000160582e103482c3c0080041c03110601d5000003d1491486a02400010583c659162500d100340c0e41304041c1100082e40200d9040b03001c06030510b2800c082c07011410203649072800d0030301003404001144668a8444921354905641d42d02a604841c907215002d030a81e20074021500700030300410f000e07103d6140541244035400840391075120a440340143c1c0090318100715241c41c0e0f9a0304070b803007d0000584040042e0407607046041c0075885620880e400640701d2503200e041031020000004141e9203d001071407000b10812081600c00d203d002c07114008031115203d5090501c2e00d6030000c000c28075008074550b203020008111401c460020b8541945d003100d14070b800102c15210a000d58255030015030120b00b544011038002540040e00c80070501c80101142c002940d903c2c0042c075418425685035820642d15240300d0306 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 638536708 1250 638535458 638535461
    0x5250216270c110102040b07020a06091d0604140f01051002011103010b0a050c0303071805060f0d0b01120c0e040c0503010506030408070206070c0303050d0e060c0a0305040c03140f01 80
    0x10140500300444880300d0540301920003031a03191041c1250341c0c40c2c400512060040309503080c0c001000008546541d15541d04841075801080281d03c6420a40300000d601c603c81c013485002d450441c5e2280103d0034482c862502c0010b00a08040d81c499110800205c1c98401c0c0c41005209400090080d1865454030050006118203241d0039021a4102400c0030120503005003264112100080d590765696810281240d480c01504000441c40c000041844980395006068500503405001d000c3c5c2c000741d40d0406c01c881c51103074252145100600303220656070070649a00c400501003041c1441d018180b100c8018108851045460b11b000ca008240440ca041c2070911961302821041e0800300e286504006c001441c40c04011303c0145202c00000e0190115104c80c030654046a40c00740c15410003607100d2030041d000b07070488501d0040329031604103040c1100400003101800341e60720750f466130f281031541c0404a001e80f900a205842c1441000c600100043c40900784000c0c84031001e010341071700e043c0e810701c150 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 638537958 1250 638536708 638536753
    0x204140601031103070903110a030b010e0a051e01060f03090b011d06030d08040b090f030a030207120806010801120512181e01092c0103060209040605010201060315052502 75
    0x5103c010300388208803249070440c1025040d130750000700d078041001c0c0410000710880469040200400d0724100001000b2000e490018024200d44400707100d1995844001d0300b240207070424841c103030f8a910f0010001a0300440311240c030303c4d4003841c1c007045101e1652034100300f0324400c0c0d2000d07400e002d0109104030305483c041111600058114081c1002070100300c00107003c5280600054400c0c11380e1400310303114510411a0501030200c160660340c545020300c10207002504403030026940c510a5000740f441d9148a0340e14244502016115400c13103900744500000b02c241d04090448042c490341e0310b0300711542d200c40060300440c08050401040507810409020981c01c0707464410b905129851252112682c201a40300c0c01d07201c500a80d04160040080c0c04202001100c28000310300c105400040f007404956001070200c12001d503010b12402ea6108012422551540f002030a001c045903200c01d01d000c40c98010540001e44100d1000c0b2118240351440c130346205000c220005a80300d031145c543c2051104002c607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 638539208 1250 638537958 638537981
    0x2e110a020d0e035b050403091502101103010611030a0e010302030a0204210203010e030c1207050a0c060c060f0b06030403110111071a0c030903070b0c07020414060103 73
    0x6031804040d5000b081c1d45401380d407402101030701000b02c18110700280040c880ea010307154a44001c80c402001610b03140c0c540000e900c1034000034034800a24500f8085008041c000d903032565880000c20716140306480c241c0340210121045020f050a0507141088034040c44080c03504a000c0c0d2030f520f5141c20f07000780852000502640380390b0414054000102d4000060a201c0c40c02801c1c056900d0341c0c0c5d0344d00b5000074815900b12203650b0305c103129007003914001032815029051003070b402007201da074020008035664050402c1c44071244d40420b05682d007200d070301e03005804158416000c54103148450340d00c0d50203200007900070000007903031042c014041c460203018501594090100411100a5910100724140b000400181c00e000b18100f061090f401c0960080100b55940d10880e0784502951601440c4074214103041c104500140002c102070401103802c480c001d2240303070001d610700502d81ea40ca81c0311102c01040c2e0703805003c0c14011000940c5443c010311503415001c0081c000c4c94030f0120700240c100c54406046 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 638540458 1250 638539208 638539217
    0xa0f06020312060d170906090603090102030702010b090114190803040803030406060b0702210a0203030d0b1f0503040f05011e2403150917070606030c06112e110a020d 73
    0x460301041001c5c0720780d680003801c144050758030460400440c00320f204001c52250050000410804a02e4066020f140142a6540280700064800b42000781c03000c0300380241101c034030034060000c85524022015107549403034106100a00c0c0d98440280d8215089548680c0680d00b0000c00c10040066500c1854041c00f200359155051101c0b41c0c01240e50140300c1c03401418100c1c140f010301680f1190400c1700d2022a07500504a950302c51424034840040e01d1b042d11803c3c01941030241040a03036408400402c0c9100e0359550f21070850781c494079141400184454140d40e50f550743c60301c02c1000328001040403040040c2c208041a0002820210400c9501c0718000b05400e408540e01880014071003d1036002044a140c400728042820741080c0c12032400d80c4400e41c905030070001d030800030030a07a030f008038007100d020b034070315050f05541e554040d907410b038648100c4929500101d003d00100500c003103c031a03009a210300705807080f0714030411a004581b08007000f50954036011a0080c08135078100005040c59005241 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 638541708 1250 638540458 638540479
    0x20d1409011b021e040f0b24070b040308010f08030c0a02190e04140f0a050c0d0f020319060b01210911091501030c0305150f0a0f0602031206 62
    0x18a11203030089121040c10000040c41c540000800c840c40501020340050107944009200180301401442000441c0d005a061000c800300a281034414500b60304030280c100c885110346640140404c0420040d140c2155030284010408102150380803441244240c40e0036880303505042c103041d031200c401c0d84541d00c01d90041080044c0c00e4000710340c20758035550680c0c50b031030302441e00420f0706d001c5038454101348503495000c01000f0a000a89000007d0040710009541045803a0b00c00c1a4032580d00d0000603066074041036520b0884c0c180444c0c1000100d00656142c1c00c0400150700083c14045010a10140315040e029841d0904c28070384211081d500c8242080c0000a100e20100b01c480d0a081c100c0040c0350380c0e200710766418401461041c0c400040000e004a0892800e0180031040b40c6010100c00c1c002880c010580010362b000e4412603000f14660100341d0b148450120070401c40d102602c072400d0300150100c1d00020300360140d01450001e4441900507607180c20700354280c0010403130002c061a01c101c00560 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 638542958 1250 638541708 638541737
    0x8070b1005180603150a0e0f071403060106170c0405060d0e0607020c0a030615050406150305091911010e130903030e0d080130030309061a0f0d11060415020d 69
    0x20b000c0a4072020420812403d686051010b0001c10101d10f01f410180106084855a1103000c2040303015594035154a00702c5503c80e00030f06a40d1355090007000301058209403c00480181031066650041441c03034801d00c0d01d611440410102e40112000001c11500c0380342a0012080601645034031036240e200400502c012500065144a11480064105561000c203500c03d1904051810040d040c040c0c0180111a51441401c0941e02201c0c07520f00064900008150005004035065614004c05050005082502e898000040d031002283d10f041c880f40c9014040c1b503032034903142012411011100021103000b24100039050302c1c00010000326941000c070304d6594803904012203d06640080761b042c0b051012190007a100311008070800d13041000d81207030311010180d054000980b010303c038240c144010000c0301000071006018030311003980310300d095404d82e646040408610140c6070250100582c40010440410301542c01600512900e5802c8201d14072070326010844030803050401e00d4414120382080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 638544208 1250 638542958 638542963
    0x40c031d060403052704050c03090708030307020c10030b19080c04020705121b151006050a0c1115120a0e1209041d01020a031410050603010e0408070b1005180603 71
    0xd83c0807100b41035040386485e045042d0700e003424001004c050300820003030801c5482012075420403182c144680c440c070a8003290041c2d010044c1c901a4000b45c00414402c1200410010a0010440341c0c00415a90741c100001c583d95502461100c50380d482c07443c0c03a805c1d0030b14a000e810020104059070149004109900001d42c001070000722250308100101d0b180d01c06040f00c1c40a000c1c41d00ca1b040d81c02d11a90b052810001034080a660040b42881c0c40800d09130355a2505442c0c038080c1a0468020501c01d10481c004140d22443e64191050b00515050804d1204190804203400c901c20686100c00d02c030f01080012000d5102c5c4401740c4100d0300007010f500500125084040c400e241c0228040c64aa2200511104c20001c0d1190703200403c80007503448140c150401001401c0358400030300750701e000e00040303103030300c405500820709617138020740280d2840c1c2c204a5240a80740d00940101c070207140801442d0081500507003041e0041c0350035824221403030314000410204600705110282c59231a0700c003e005080d60b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 638545458 1250 638544208 638544217
    0xf0417070201090e041b0603050603060112050a0b10090c0306150203040f170a0f121d01050f0c0f0703030c05060a1503030305060f100e0315011d040f02040c031d06040305 75
    0x512100c0c0c13256580c51500c1340b06c1c120402c2d10b000010242400200e849909500a1803080381c068040350b11582e070f00c00344c400c11200ca10402600c40d4101141c0240801d01d40380020b40e1158030142d965510300c3e0344101c4101240e00d134400036030019641e071009018a91040589840d012024070096092605001c5184d04111451003490807040301c00c451310003211014440c0f07030542ca402ca00a01030b81c03c0c4504000b2500c030941040c1000061030658049010f0750b8110783e0f01108081030759110f0804100b400300d0400c0d640322407400c540303520a00d44540c160150401c61b1801961180e52107014202c2c843c580f00c1d1a060001e000480024200035100d128008036900c0801141d415281c04526030304c821010940c032200209245800c40c01a1194201d803a400c111403c400d0b800c00d900700d0703c081444100600844000303001e140c505001c004400507840f8100b030441600603008a90350b07180d0020590008040360440e090610211703849040700302004521000d56203841c0803e4004e4030027480c09a400801c644103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 638546708 1250 638545458 638545469
    0xe250c06090803071101050a1b0302130305030408010903140c0a12031503110f0616060b1f0e1c020d0312020d050906010302150a0914010302120f041707020109 70
    0x24000050014418590401c40340d590b00501c105550741010b54008140c2c40c100e107180c0b030f1950b09120100f0382408580c80b6450b000300408082c03c0030410007440c2103001c0c2d40f1215880b08130410741140803012403014002800149048000011440031030f01c1c002c2c181c428080b2404030004418424248001c10100340c0d5401c0c1ca40c00f903008c0e2100010b44600f40e004151019a07440d1201d051040030080103001ca40c603211084003128080380c0002c1c40c00402045104071407805200724030451000c00024041c0d08041c94002e401011030024218008184021246080c49080003441c10500181c160a147d04030b45410040c4c400b00b06c20740b98103500800c04005122200400b04008003844000f151069816101c01000014050005003000200c1907601c160a000036489802d08038034080e040d000b81000c4814070b150a03150070710000d01c0d02540c25550120907103543d0605da001c1003211404c140f1165204c3c0b041051007400111810103041c07a10003050340404040250204100040c0540c0c4c104264900b22203 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 638547958 1250 638546708 638546717
    0x19080702032a0f0f19030e091e040506070f0809031903060f06030204050f0a080d0c17030711060f0c1c14040506070e1903060b04090c0f0e25 62
    0x14034040308200d0450720107144030b880e0054050800d03000c88041100041c1198000031901118080d0b0000710801c40041c2000300820441491103045040c030704d152540c04034140d0950300810404e007070441c03080b0f41c0c112011140c0b9080700c800c20010540041280b0b0440d0502c1c50100a90b02c2c0214140e580c82c4500040741c4031109404140400d5244640c00c108098207803d8004642c0b2a41d030324010b0040c0d00640501032240c0b802030701103e010706050212404540001005040d06140c0113808c0d120b0700e003101c00555403203010104005942d06020700840c00b41001da138500c0010b49500651505008028090b8009a088001031003210380c0c14030b044d42d03a81c103204480b06941301542151003005060b03003a145a85500a038080109024020039801e22a10998031015680c8880c10200034036002c200381c803481000724025050003c507140d9480f21000b00d001510010300d0007901c2c1c640d010300086960110142410104003072081c0854101c0050300052100013280040030b11031462104003075200000b00410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 638549208 1250 638547958 638547997
    0x1b07110d0501200a1d0a03150906150303030b040903050301090e03090d03020607020f1f02031e0126010b092d1003020f030a0302060402060c03041a1908070203 70
    0x800390701030030041c40903002d1441c40002500044015800ca201103601140d885d0041402d0700c0076010380b40c0c8400b00700811001c03c1c90b00707540c1c03541c1d2a000a615800141643c88004800040c0c01d403150308141d00200e10f503190f410b03156180c02015184036416050150b030500340c1440010750801c1c2035138152010f01714045442c01d04080f5861450143e852450b80c40010346940400340760f0003041c040e010f4229035090b94901d14007501032990300e02602c0c01401c542d6803004e8849410b048142d0166401075040c40c2c250983c6c82201000d64418031007a00301d290040f003044803150410b55035641c0d1080340100303900203200703115001000502c2500d0050543e02c5601d00c1c18030b800c3da0001043d20780512113010308420407050600c1780b1a41d0514001d4003049000b80180c1e40e2040c920300e0b0000d41a040349501d41d005041c5541c0b00c0d130234003955400c1108038080d40c0c8818400480e26803034404000b00320030043c1250741c0e1610385010540200a42c102c0f11542444000f00521101903030200403610440084200d50b40344 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 638550458 1250 638549208 638549213
    0x1a010815030f120c0c060c100b0f030a0339110103110703170f0c031603023a0e070911040e0c030406110f07030c02060d141b07110d 58
    0x4040c0040d601d000b20b0f00032003041448100da038034043c005515800003110031040e00d66080c404540704292071034072076034406560075030707444d0391900003c14007100035121440b41d19a000100e071414540c03400440214148070070903110740720a00581801d0008010790000d000740c1100a05014915080c0081c080184845011400381d009822080c81510740300c04160f924455800c1c000c00200c85140c0a5100d80d0801c000f10384125080500640100e074001e0440e40745444034020f2420b041d47d540d0030a01419000d101c0d10609603221401e1100003c4c100c00d8005a20000c8440728030383d480712041b1501087e281008184050758005442c00548140150003c0d9880c0f40080182440c00359611240d14000201d04201d011030700c610245005a218800074070204200355440074940c042c2554000c0c82450074041c0d400400e12401c94280c43d280080c02c01c41ca00010350480d001603810500340c1600d14258881401a81c0c01009100c50707032003440715030807400c0c016250380e12441d0325420001644514850798141d0b09 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 638551708 1250 638550458 638550463
    0x106090504020c03090616170f03010e06010e0901090b0103150f0b1e0d090203060a05090c060d060b0a081e010303081b09030a0506060a06030e120307110610091a01081503 75
    0xe6858000c00854403a00903d043c20200320020008823503d00b851051550308103146400e882015040f0714000b0f046070300303100c84001000802050303a4100400c11059080b1600ca90315502c1c00b80c59220008202c1ca0744d03030b80000d000c0c0d035010b042c059810103612404002040c949000e400540d03000e081865a1005d64440c0d0300104c0784990843c001e04040084c0e10b42d420880d0b40d2000c84081e20990a07a41030b0796420208004039402104ea40703da80e000149000f03114580b081c0109101d400410000030901d849104164894009003d542c6c0802c0f003050a202e01d01e039a40c501c03181c0183d06080404420344c119903000f80241805000c220003c1a041d0403807071407440d11016200740b060082c0440b507210000e81803559a400c820740d0501d00a240c028808598188207024607030b00480400c0082821032010000e0f0340d40c80e40020007c0b4204490f0101d02c030301c00c0c2c1d014040c66005621454240d4416414003c405040352403544a090300742450032110201a40c1005105e03a00007032403400c00803101e4880d0007190 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 638552958 1250 638551708 638551717
    0x714130c200c0109170c2106010e0702061f0905131218080703030212090d0c060503061302121b04050a17010b01051630170601080106090504020c03 65
    0x14400740884403180c0c02140c0014004078200007680e031182d25a0307407015485010307120080010040d4012410004507801e1410300412815039044c0890305101202210704c0c00c180302a000403150aa42c17500b0300669907410031296801c90008000c3d0403542400d0030402c03015490701c0c442c4050303e9446000060110072944140d21000e0f0308003001e801a40034100d00100907a02802003000c0c0d00c50ba410b00400c01160002ea0541542c0d819001000c40208520302c50805801c0a4012079202480100b080005045071322054010300c0d40303403100c030b0312030502104000c5400c9088010f282e110307105100b0303420503400700401d1340d4000315505c206010b500540c4c6007008161142d03400c030b640c00040b20480000d03030300d006080c90408020003100800424204900445881c0300b0207000c640311480301c0c4014800301e40c641c0e165540000f080d5240c40c00441d090308100c1c48200032545484086a2405908442c9141145010b50b1040091030100801d6040c81c5016200608500917039010f16808101d01e00380410804c00c44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 638554208 1250 638552958 638552987
    0x5090a020a050d0b01051308010b0109090e030d0f090602041503050f04120e0a08060c091e0f010810051c02010e1503010b18060712120902180402030118080901020714130c 75
    0xf45281f0b525a9084c90203006002c584a00060581000242200f8140314009103e60285d01035071502103109104000b4000c500c2d80000360603038800c0703901d0000c0c0c40380c07000f00002c000d01d0b0b007000100181503002500300c5200512010136036452030200800222011011198800b4a041002c1c1001030f020109407440d5198100358a20301c00c00f81800382c20301c00b800c05401028422900491008200401000400b00d6402c40b150003040c1c000078401a276000c2c4020369070094080e11411030356035681e000111940841400010070a20243c0c02c4801e41d644050701401d120410b40300d5414a2006000b03030362083c4014800d040f081c0c0400703d401c2402c00703103540000302d02d1130340149070589510090074416000b001a503421004249200d506104030092401507040d1b00740c0007041d02c01d00c9203201e82d0306080c00c0ca0040c81281d00d55a907141a001103074a2045503081d160080d420b103621510018000b914102440e04002043d2010300380d200026940c40410301c0c240981c20402203001c0b41444403c0c5c40303020000808 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 638555458 1250 638554208 638554237
    0xb0708180d030e1e03040b03041a0c030f010e13080a0207030b010e06190803040b0711061810020312130201030e0307080d060b0405060a0f0212070c05090a020a050d0b0105 75
    0x200e41d654150841c060078500c4a0544041046561101001d10305049040d08103400511042000050b50801743d80c0c0310b1f029284215020303d00314072443c85901e080314101c0c031040c0c0100601043c034103407a00c41405403c03001b00f00c088a0412109a1901000e240d0004098640c00583d08a0b083c1c400c0c000607000b554440001d50a5584980311043d080c0000c450f002d014114510f00c3d12403080d203002c0351400300c4600d03801452500781001080b404e5548080004c0e140c903900e0090a42c0c4c107444050041c01070b41c1c0e105c17000710f090008001c03c1140301c000c141007200455206100600b00030000d400038036001483e945d1950300d001524030050300901160a10310201e03010100b454070500c8510300081489410003e403c002507600e96008500502690080582000c018420440494007500c02c030345080c01c06004039468800000c40030305055001d2202103070b039410070900401490520500140d00700f60121740540c01d0403250200100b00e4000d02400c90509511450754545c143d000c4c0c8201d800d40c2c1d008055 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 638556708 1250 638555458 638555473
    0x1d090a0213090b04050a180b040303021c0903090501110c04050405010b04050702030a11060411092e1a041d0c0424020c010e241b0115120b070818 64
    0x12400061030140080d50145003000001000c01b0b04500c5092401c41000b064a601d6070704d1b5496400026800410840506508001142e181c466500e00303085194003003480466003d02928000700613904951265045c0b101131203940324881d40c0841c401003003503410340700000c06680b181411030141082030303503442e00a4984000e00145960203c000c0c140340e00b042d1650f5500c070170720401d403a0740d4880854000e800164036400e800058034011990036008820034910882c5003500107802d146561401d0154400ca2031254810490140303080034100741e0850600c42c2500b0646030240d4100c00c241071030240c03c1c3c2c1d80400380000388440140001d0360050611f41a0507071490103100070369015410600c1ca07500c054850846044682c2d803240c4540c2c05000b501404810369907444603041c3c1c608520860f40040e040c82d0038019410700300b8506d00780f141c060b00c5200c0045801d00b24044a40c1902040d90040c2c10b044100d0301541003c104164a10750b004170280c07a00303402c199941100946420030003481030903280903018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 638557958 1250 638556708 638556719
    0x20904060308120f1603020309030d330810020c031c02072021071206020a18030c050118030219030b0c090a1202030a020307081506011d090a0213 64
    0x2c01901e005000680c44800c59203940540e91080d140c1292902c940940d9080e075226258400e40155400641300d03003c4904050105032100c080c0c4030b400c00c028401201202c2c0c007092440b050210b64003281641d6403145941420015400e403284042c0c84482001c81d0001400b41019400304203c51100b807064081c401c5001d0240b000074065849001c00b03a4100d0503800e44c071818040c0f204e0310707003001000040510031042c1d1180301d03002d8076643c850310b08211406144c400203400030041c2142391100e486100300507915190755001a200402c40c403000b440c4034481c1710b0140300007002800c40d081500c0090811913440c1d0405c0f50040320307003c896000290007842d00c40100b000c104460342001e05803445111001e2260b500c80610060901810314a1540708030b42400030024104074407140d0f0f0140b400601a40d60442032074000c680b41940307a030312014980d0b00c900c185404000c050342d01aa00400d092802006c4d0144040440c4200491f07a0035451084d03e1100c003044010016504442140c4d482035051000550740f034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 638559208 1250 638557958 638557973
    0xb091f29181504060605161b0b16020306070f170a0609020a170106050a090513140c030709080a02150a200f070e0c030420060301030609150510180209040603 69
    0x2c002c1d038020780c00c03c2c9020540c0e0740036100759400301d54611046410100d9503161300e0080010311820518403100380c8404100f1014450003440052800d020031030780c88020b80b040c18034016000345072104100e04040e01b20f400c10390142030800032000c6240007014a480704510000281199409000d4580c030011f070255410707800285a01401c0f40341400409180c0e030b94001034030a4030030348844500003020044180b0181c6082c21540d541111158000a444504a81c00e19841c01068070341e1348092001001f0000d00c00e9010728050081c0440c603001e0a120740c401e90109401c034441c0685016082000318110001d00d01c6035030070101d035041c08600406401c0418005c00d8682180382c0307816409016002c400300b07048071203214031030007140401c041a2642d07a65441d40012194071071500072450f07118094084240d80c0d084090f50186000d001d00054402c40307450100e880303410710381d00301c4106810b1004104100203140e41040c111000303d80c0e9240d0509000304001c0c000d100e0000e500f50722a01e40319000c014000303c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 638560458 1250 638559208 638559241
    0x1911160303080a0b060906070302031e120108030a0c0809030f0a150c08090d0305220b191811061308010c03050c070c03080f04030b091f2918 62
    0x1903102c4160075141c02c8061010740f100c2041d00390300010100400700d210709111000b450454041d1050780e0900c0b50b001d05d416400c50841350140d181c1c03c0007248860403407000003c03250041000900541c642150118090044102c0160113040e440020852a20540b0305102c4104140a1312040d100c1d0741c042e41c940741d240300c01112000001181b0780707220b43d10128003131514079004001010050143d004c0d2214101c010b00070040c455810301c809a01c15415400030400ca41c06130500c5800000406c1c9000c1106a2290051250350f00b80c0c981071055a602c40c20196209901182d080403d4811440c011008103026120700503040400c1c000e0700e200091540419440100c00446035030302845244c4410a14030124001d1190140040d4068007003000065101c0e4001c000c145072200005050a41d03d0f1581c07100324804841c03035034158001d1044555107d01400314480407602500d0100218840810105009406d68108042d84140100000b4142d81d8a6074141d580d854140b80040851074a0740031850200e19 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 638561708 1250 638560458 638560463
    0x50609010c031103010b031f080d030b04180209070323060a0b030103170c07090e2103150108060607140a0b010f14011b1e02010801051519111603 64
    0xa0488908020781c4640981c10503942550308050940e400c0c056900749a038005051050320403206200d030040c042d840121040100341d1400500b4408400c40006410f40701000e01e000c3c801d40c90031299602c070030406011082c5198058807408050303942c0c0c0000390002d0910001030318800c4812a00c0701040c43d482002c4a1007007a0560781c0180301507940074464010b003c04e01005100503894540800d603c2d02103c094142c0808407411a224180d03280301c0c15044402646203103909400141c900032450200b0a1501c0c2403c4002d05440d00c3e40ca0f250700340c16901d0303e4a0a240e81005100804158079589503003d841119030810140c10904001094055407002a90b0040314400300712000000c405000040c024125059550071006552070000110b82c4440020508054034208400485c0404d051400000c0d801143c04008074406e0f1007400090582d03103050340814490140381d0790004d80100c00c0c0302614080c2c00c00308540000450f0400301611074910140c2690090321400f140315400d42c0f40d14a00c60300f260b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 638562958 1250 638561708 638561711
    0x2a0f07170118030e09130c06030203011707180c02010228020f0c09070f1b0302010204180b0a050d080d020316120b1e130e06060109080d020601030f020402120405060901 74
    0x1c151100e520780c10315982c80d0280205107010aa0305450a0000d80f040c2e00401c40010f2a0a1010580c2e42c1d008807c10350b0000f00000342c1c0400107004c0d602160341c2d42d168612641000f45000340c40c201b008001e071480c80a4404034180c6403502c04102038000d4060360740c0721140c4990002c45200d036801028400c9281940c850041c4100d401015207440b011450140340b01000c0c00c007440c284d44440081e134002d4440d83d09070040024400f11314103c1e0f689110f1306201640b0039400541d4480c5020003180200c121a24401035030751500315003425690f140b09507041124406c0e180f51100003014280f00c2c1e02406081d4040708107900001c10000403c0c144480140100e0701604d0b103248058000c440641156506800103810001540c00406210401d401c0c2280258004008030110720008486500f6191030307406610b030a50000e4140011580c202d503550000e086060700409820b8041c48009545050600c00900304144800c182410340d1075940456440101601030281c1605080c944555500030860342d90b01e555 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 638564208 1250 638562958 638562971
    0x71704031824081e01031106041d010e06030c01052502061801171603110d020c070e0c0a0f1b17070c0504020418020c011803050a080c2a0f071701 64
    0x24000420030500404c519540700c0c6450b0300b582d0b210f13040b0b003140540c0c4507400803083c48005920708941c0c6d454080442107042041e000c1d490425030b44080398025040d5442074200c800748088599000e400c2da661928855003018400e10300d4500310341001c0c00440702940007240060310180101c0400d0a4007102282031761005081d1a80190350715400385c0954001c3d180e000050014441c0f24400d800030021a85441d01c000c1c13912100106000417a4400e009501668010003820811074440d800026446445c12410614000c00c10700c00900341036002c6000414400d0310301d4855405480032107050100b940c8094044080040002c07607200540152a04950b02d811111011800c3d051a0007998100d40b0001d42d1046030420080d1003d000c0d421480400f0000d640c5c0d251082d40b18482c010418152900030740744c003982d0741c07601c0708000c140a50007022510b104c2c404014004001c12816070740b89807110b010220200b0812030300da4250424415064003640c5101d004004504400341c01003903031000c50727184020000d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 638565458 1250 638564208 638564221
    0xb0106021204090515060c0a23030306010c052104091503121407020604030803071407050d110f0f070906090b090103021908010c0503060907170403182408 68
    0x1100400d1044100300703107051000b0007803040f0701c1d082a500140b0012864a144101c0004100260080024072080b07500505503a4144418103480c0003107400c0b00030242943d80346000d43d5603036034071016144904100c14840161706003c0d0a21040300c048804444680d007100f1242142c0c0000d17040307809004912450000d0340d405070001c0984290441740e02441302001000803500650303a9600c01c552202c0800c00c10409600140d071102c0c001c001031031007042101e0f101c2c181040000d200300400039400c11326090400250303020500015200c030700016a8a0200d09101c05080f1040c10840444901c032810720034181c5102e6403040c0031441c8003c0d80c0d01d12104204083e503500d45001910f004220340c0d030300031801310018005400c00f103440c00744041c6082c08861025580d41511421100c4c11348010300040c1c808400d010383d0349041c040c9582c100c003c502e4442070a003030114640100000140005047c04078824170401c10000c12455007005060f10050a000c0c8103e2002e000140100c290304000060615070000d0074 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 638566708 1250 638565458 638565463
    0x9210c14161205070603020903030409060b0a08060603040f0b04022704112d0111030c0a02010e0d030219030905030706170109150b0901020a08210a020414010c02040e060c070b010602 80
    0x100e90400000c2004c18601602074000b98090550290140001c00011802d1019405014000d01e201c600e91959481e0403d0010101034001e400d440c0701e05030030010b100c045a035004110310782c4d40d040b0203099202e407907a01c00a107001d22031606441e140c045400582c01240d040c0c20f8050320560060b555a501d540080041001a01c40c041e0512481241c80f64000b14042492026518219040c101000c6130a10140c2c4607245412070008442213070f110440940445d640950240a4103000380d0361020701c05440e170360103500c800d44110f0350019400c210503030106052043c4181c500404001c0e0aa404817a2244070080441c07603200d5102c0c0c1410808400040e40807494450324024071f03000c40300da800c800d05200001c41e45c0d0f8400115141184140000c20011451240c001d1090300e003564046004800000b41450440500a1103400403510500080051207985140384a108400346029103038003240e8800280103103800034802c2c90920942c42000042544000140101801000030940320781c1d071800d0403603 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 638567958 1250 638566708 638566739
    0x2c09060907061e030e073302010b01120203040c030b0108010e010b103005010603050108010b09090c06070c0e090c011b151e050411120109210c1416 65
    0x41400700303e080843d8040c80384d8828005101510107542401d992401d50003010410860200d40400300001c40c0f0b15200342100d01101d2001d594002030100140b24800130b0b0451400d0054540106d800200140410500c0000704001e90380c40501c080d090f58444440c02c0c02045400c0000c2035961034121030300381514251150340f901900540c0e0366460600020070004984110780b000716440101c0801ca0305d1302000500031640a0700c0f06550000d29985050701a40c00d507004503041d14001c0ba042402d110f403080c1c0102d0071034800303817054078220f60303503101d615100c4000002a80016520240d10060102d000380200d00d014592109a81d048155071003c03200022034005a5002000e05806142c001405403490300211010004840a55001444402d1074400da41c0c2c100c0301128036035045a0311508516000652203034900302500208848c024554840d18105040c0002d12110038008844050092050103520f0a203648800101e10440c10481490f9403244400ca402c07141403440030000c41e2221005a210 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 638569208 1250 638567958 638567987
    0xc08031e03011406070203120406032c061b12010f03210503071b020306070c0b0a0b0f1302040515030411041806090c1706041403132c0906090706 64
    0x12500100d10fa401c01c4540d500040c0220b07058083e0380318880f40c0c0005a0f028000410302074801007440e1071a22690340910408054460702640c07032404202040c240001c1e05c0b6803088038000420034400b001d01c0c400059005d00d98000603c03011500003c68100303410601e8108807032180c00c0900d00c1200251344008400400502c0c08001902480051011072058440203402c02c4040c0e402c11001c0e20271b40200c3c0c206041261564007060a0700158420440c9440c003442e0300c941005020404c61404800240c45001c00056030303880f030801025180035000256049400521009005841d444a04091031342c41d6001200c064a10b40448641c0f100c40b0b090500440c4080449884612000f00c1d46039220001005000420f03644003194041c00300703114261006580c00c460a40000b0b110a1415152042c11011030301c0c002d51503500203200356111121618004001c0d0750045541c5a0b1410f0b03454900482e040c0700c540385040000014040c030100441c003103840303400380c020340e070aa43e0f1040d2196020742c0c080256070fa40 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 638570458 1250 638569208 638569229
    0x6061e12060203060105040f15080a0e07054e03030c0304080304230124060f050c10060f08060a0b0609040c0c0203100203091c120c03090c08031e0301 66
    0x4031400a0740340d0b4001c680c410300c14101641020f4540c1c0110030843c001d6041a1004043d098007044c40d2600700d0311281d0f1004800744180079040e41840c1700340d00c40c0c0140c464540100098480020803d2451480d1000f029501a16858040c0e0034040d0394094061081c01096807602a1240c0e82d4581020003124451040035050364a1740e1138903074a00300c0583c4000c20039111078807a044180c0041d4030398030b03400c1801c2c1c0c5c400c00041604042d2225030700b010748024019048499101500300101354107d0201e41d02c18120341405501c85440d160028104000514800f0403c0c3c500745021400d403d00c03602940c03d441041d0f0032904c00380c0d201c550000807509000883c580c44181072024800501e041d4000280e041c00900c0c0000030b00c040780e40840d1805c404040380030302c02c1e900402001142c0004100c0f600f00c43d816840690b0810001400c05403050304215500c24181e91192244030711103002e5084400100d078041c0c0110b03e680c1e50750520648a03004140b0042d51208a517401180c6e0001003001c1d46d05171050a04e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 638571708 1250 638570458 638570489
    0xa0b090a080915090306100614130501030207050a0609050a140606010c1101210509010c0f080a020703090b03070c061104050a090902041508011406090403080a0c0e0d06061e 76
    0x2001920705101031110f60b2003500300041e0560341c81c00d002c06400b1305000c41b5400025410208003420862441d120307880c801f0010320041c00000040081c03001121020f0900694400c69030601e03909010b0100000342016003085540f0381001800074072101d40034001c0c203056221011072400c85854000c15a40103001601500700345002c40e00035685031907000414100342b0700045184a140351002c41280d44c080341c10740d0b0b0700d0070441c00000038021881d5402031403404e101080d59128004d4680800030b003040080941c0401c80000305402055220050300d156106141c070f80c9401d0b0001850b842d02140e04480c0756003044e03900e48038034004c04190317419a540145030104103410714407210010100617405983c01610399418941c442810340c10900074081180011a10b8000080505440300300a03100c18000e07440e000402000c6a401301c03002342c000150310800b054030700c100230003250031107a0700b9400b076400480001440c003001001e500c41c004481b2601c05400c00c00070b0280880311041a68800c0c2609003500382ca = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 638572958 1250 638571708 638571727
    0x601030515160e28060801150f0801060c1106031f050109050307032603070507330504060902210c0604241209110405060f031218030f0a0b090a08 64
    0x907681e1514181c4d243d0f510150400c001040e410384560b42c0254041000f81c0c005101007522413420f80032603111428909904034480000404c82c000c14401c89041140032440603003080988034050400020042010340c507401e00c613010701242021449aa14454800310b000219035015542c0340c0201c1c1c900902901c0c4440c51a190440c6101d05811441a0201404050881c1c40031140155016480982c0d999032a11003074640800c15a08030740e026103500718529010031540c0a15040d0a441c802d4001001c2034644851810401600501d10000d5000038005566000303809120030010001190350210341400d2045402e09c5460320071401901411003400941c00d8154000d1104008400744c0392401c28414510b00c4400340440e82000400c4070b048100c104007208601c0c26026003a0090011a2655a040c040700000713541d50700003107071800c0d0350b02011540c5010a120500606c40d00c1b0005015244100c042500c010380302e032004c0c2c85c220f40140c0860701043c828030300041d81c45d000d5584059624074111684 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 638574208 1250 638572958 638572969
    0x117060105100c030201140c13080c0d060f02090315100b0408060604020307021f060e0a0b0a1404090c0308190c12032c0601290301090b0a05030601030515160e 70
    0x124010f0f030030340d074840554040c0c0e03408070002c1d1031203044861640342e09e4051122441211180c140d0022140b50b1060500c8540707540c07004455240558040400909946442d520340086d0207200c0d141e660601401d1800b4484440400d01a485040000d40003402070f900c812000b40c150149004105856004400041c03403030400317600454000b201c80c0110f5440c2d20180004004500c400c400906440341c0b200c80801880f140c02401d90b0308161500d8040c4141c06120012404442940c429010094090003c003100c079119a48841181900054078100c1c0703030780328244002e02e0781c02035403001c000c0307840b03c005210224820103c83e070080758050710380910040a108114098100e4420205a4140e054150f000503080340f48030400e1452000003030544d541c5828241800c100c0d2140200044240c041c004002030700c807000031139055401e94a0000780c0c09401c0c41c0482d0500c00c16401880e054414140084140400012240c070942c0004400e0845503440c00c2e89030308003103031405018000c501440c00102003440e01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 638575458 1250 638574208 638574227
    0x408060a0905071502010207120807080a0c111902090106090f0905060301020f1c0501080f070306051b071a0105010c0f020f030a020a0603090b010504090503043803011706010510 78
    0x603200310360f807039a00c50184411010ba11168800540e500041c1300c0e041282e020201c000e40c40c00c80c100a4158541451b01034076180f0011f000400051781c41e030a4070103c074010b1003036281c4200c40e00c00700c4d03a044c015401130b0601b14205080c140d2160315510700000d03407980f24181350015200e8070820500e46526101ca40e030050f180142030700354155004d00c04c01c180f01c001d040c0900203055034190403510704021103600d802150810b803c603011035000050a8201003000080d4282103940c041c0c0d0003d4960781d000b100105145032985c0d164200e18000070a503003400024901c3c0d01a00c0322041c420607090b66603030015034180b4102d913401468405056658809460980000c4130f141501405840404100d0b40c00078510301800d4004c2c5000c6076444202d0400c2c000080e915501610702610100305400413512510398a001d00e114a510741108014007881e40c0c1806181c40340120405000c0c00c031800440e020303a007102d4109008041a590141002e4560700000141160403124054107920342d9200101044800850 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 638576708 1250 638575458 638575463
    0x307080c010603020d0f060c0804020f06090301110408060f07080103120e01030f0501242c0105070f0b160f090504020d0b06070c0e06030604170a030603150c090b0408060a09 76
    0x42e502c10000240c0c580c00c04c007641052094945030001c00b420714040045807060342c52182041504000c1000607124007441c0040b4941c2180c180c0c0c7c4030284000000c1c003405040c1002c0447e00390200300081c0000000071070602401c2c04030781805031903440e40400c4806400c00d1001901e6100f884070b443c80703254040c0f61003681c0c81006240206010103095901415940f003a80102520f04528440500c0c2c8510703c560105902424582842c1202c6040301565019004920079a08800e040304aa4626030017141100c0403d5400f0400101e00646030078030703800d103030f204664048406c1d52400040d036000340708441f40c2e9107120b035a80704d0b410b03960b05100a100094000400d041c0085643e01c13195650741e500c41001e8200c05100301d175a040820f0400c030307070801003010251055019078020828000050420054202e21047c040303401615824040d00407005800345920160140d00d00c90b411125208207a04540d001e00840e0304c0c0c0407045070f6511500b9603680b04910404c82c45070040c03408240d03c1d020613048070b15a10b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 638577958 1250 638576708 638576711
    0x4060c080919030303230105040203060d14030307090b040303170c09132316030c0c020901080607022b030504080d06180f060e06011b05010c0906090e07020307080c01 73
    0x1001c01184000300000c64485511100b0082002010790500030b0b049002c510b410a01c0000c044640d111404202c180a405d01c84ca401000049117500c407441c100c00c1c800d81100c0300000b40c814080e0203c0e10384e8015980030001512000c40030810890003000c40c1d0840f0340c10f94411075910b1000031000e080220103400d588113001e0802c004511035540004019022130454000191000704000d1030365210404402000041c091900b0402c1c03e401014811559615904010560a8200008981c0d000d980c4000035440520040042134282001509600c42c030095001c0712140d1103190795411202c001c1004e0b80d0540400480c4a200080c402d400c01900240b2502150b800c00c0c10b480f10150a460a540061220400d407080000448246004034030f01400700b1780040008908004e00034043c0d520003441c29040c0145031011406290b804040c074075209400c0402044110300c90200200540ba80c0e104034400134003500000310710828240344460142c4401d03001186804d03038940d140322030350b00030480552565 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 638579208 1250 638577958 638577967
    0x30106050306091b0d0f140102070c1814060307120c091a030607110c06030718030c140307301b0501120e0a06110409090b0f1b04060c08 60
    0x181c60802c4020300445049020b000c00d0401c41031201c6080c0408103005100d00c041050510200383c9030901d07482d60581003102004200c4004c4070942c068424100d00401166840d03c000a4020744240c0300d280035a00290144010740d06441d18215002c41507400c9035158020340d004002c05d00d20759015940c01445010844070f02966205020308480c9814080820b1050202100603e890305201455200c44203007445c007103443c0e40744550360340c40000b00280e6000b40320000125020b1409002e04542c50f030400506607805030b4481c50f15044141c1d1621541802401d800b0403402c40d480c000c100b4105071419003204130360b8a901d00b200f08a80a0946100c4451a0b02002004000c5140c0300c03a8405807088050004008030325000004100111342d07002c4842051404161240000c0041a00301e41c3c03035000320b00819000003240342c4608520a660118080030f00d407440b148100328002c195240b048d03401100461442d9109d0a501e0035000c41154020541001003206000090041100b04001405031300c125050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 638580458 1250 638579208 638579219
    0x10b0a1404091407030302190f1509080a090f06051809040f1424011410140c060a140402310e030d0e0313061b0b040b0412030501050f0609030106 64
    0x2e0081c20403c0f95401c0e009000c0920074035404009295800840403051016072a9039107800c0d40c2c400c0100740c014a09409040c1e802400541500120549034118800e10b80d80c00d446640540415010b10403480712482601d0000b910902030025a60402013031003400c800c1110000810215220080040b20f103030719154120008110910f41d00810444a18010800600e603902c402600e5441c03d1090002810301c14018840e00c0909144110450400d48a06e80304860b440c8040c2c0b01010140b040b500040404908400c3d0480f00183c00c6025684da1407040000b00342c0c114100a41800c00c440103034004482800300301c40d1280100000312150700a85070000381e54501d418600560340b404980151a80c030205076201500068070965503101c81d1440150720f0403440720781102c1100c0c0300e48212411710800c40b40319484003c240081c0980d040e40400750150f54985842d0008003540162410755640281c00c00b0465064003a00c180b90584000800006141c2084d1007000348541c0519001038040d52200c000180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 638581708 1250 638580458 638580473
    0x50a080405210309070b071e0312050c1201080a0b190b0a060302120609011401050702060d06150215010e060904020d062a030b241606060512010b0a140409 68
    0x46030070b0a050340036924206020791034989103854110110030001088240700080241c030100e00c0321004a056007800c0e1007903040c180c2c1c0e0070107a9806a207080741071004000704200e680c0010a07020400c0c2c80c280800781d803102426070755130300a401c0c001c000b8072072135012a001c44561141091201440d440103d44c1416083c00300d22018400c1d880b2102003030f0082500c04c0c4010035144199800300c02038444648070340c5086408206101c01c074020724140800007449209646039041100d0606044103c14000982d0307550400d400b9201d8401c001005008094030030341a0041001c4a5040707a0940c082010aa20340c44200100907401800885c1d001940038106000200603001d80c40341c001d003144102803090400e0902001440b140400703001090301e0070595403596903501c03907903020140025510441007150810a0b4025109601b41c0d040f104004400c585d0030010b00790071550595909032500c407098668042c03070500fa98800584035a11080501051080501402e0641c445a00040c008a032100550310f4009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 638582958 1250 638581708 638581753
    0xf081e070f0f030b01120b06090702010b18100b04080607030b0a03051903080604060e150a031704180621020105130306150e1e04021801060f140a050a080405 69
    0x24a0069102c07010802e108849410364010b02d4248128254101c1740d40c1c4517004140000c01140c41041407601050079240300354802040d00c00013a140201141c0e43e80c1860341d00c20011141d03541c02e1940c0340c00c089884401c4000340e07000c41d55100020070050710b80082c15801342098003036a03600070300400000404140304006414038011180400300f801940c07403c00509401300100301030700660800c4030400142200200441e8404440a800400981414006004203409510180407075171050200c0c03030140703400b0000300120786045851516408284050100b1303200c803449070030100c82100c11940c14a0300b80b14500d0b4501841494060325000e071005a1032001091604169a026616644d981004220306401d001510f504005070b84241b0b0000e0f680001d20752032401d480b40640c0c928001c1821515140300c41607503002c2c078620301a902d40c1c4a88000300090380340c3d00c41000166000c5070700c000314641c080885105130382607503e842c031301245032009a41415000e8421104c507c110440b0001950750040c869 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 638584208 1250 638582958 638582969
    0x3011b05071106210601031b05071b0305071d220b0603070b0c011e05040210120b0303040306050a050f16050a0207080102030106030b01270923150a0f081e070f 70
    0x107103018144217000404450540c91030500e00c001c0b2199035103041c1e030000b043d02c02d19680a0043c40801c0342080340041c040309070b544010031900c203118004c52410655101c000200c010b0343e00511503681c42228003008028000c1d2090403003c10011554041488420f001d644454094120b855650b079861800e1080d41c040b0000d144540d543e540000c8003130301c0c941c109213928150040d042c42142040d400096140e100165150b0900210501d1140d6815690308131004485004081c0c035180e82e42c2cbd0820341c01070101200c10102d9241b6103030010f03030044109142140a83c030683c0c40c030307104640314040a45081e800400d00b181903210f25040040c0794142400258086c107a666000b1483c5000500050050b1201d01e05481107410288440500c80d044200300c0b00c1151040000410b440c0b0019110050a548801e610b110194804041001d047c0000c0500ca4030351200f0384134102c2540d40d800140840c1c5c0110302509909801c08554902c2c0583c0024081c14017880000542e8006651134070001100301d00d55101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 638585458 1250 638584208 638584267
    0x41a07050f0f071a0307081806070f080a0e12340203010e07140f060d050727030b040f0606080a0501050412320912010b03011b05071106 60
    0x440c80700d540c0a118a50050070400c0304d6521820f0400c4580940d404002c11220800c106040000c217600f036440c800c05045201c10082da0814100850005c0c20704500c8404403001c2185a4085041c0340d8a5104804410140101412103a44009480c048592040c204406003060110120f2031110500401071800c2400038104904000148141420344050030205d00650700b01c5d5404010304100b000d961840410203c6a0707680282e030300300016000e4001c07100380d0341c00f040c6031070304100070280c00501c09109010a01102d10703884c5800780d010314591030f0a010040001c125100131400160384080904c06180c41200d001c6541e40d12400218523103a00080c041d103460303444d01c05101c10301c0040009801c410400d40303083c50030001e01030304040d42404020206c1d0036244403001003a0f4890a00c0301660340c40e00004100c00c6501869050903400380c112000d805210394a014143c2e40c0d074950210b01c21034121401d85980d0b09224103034403545504c007078902500c0c0d08840d0811400641e84002c410013502007213000c01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 638586708 1250 638585458 638585473
    0x603130305040f0b0301210b011e21020112050712020c0c041b1b020f01050703140d0e15040b0609041104090f05011a1f020109020d110112020f041a07050f 68
    0x100c0d024803074407500920728545107c2c0c7c400100703220700c43e00381c15280317141a15100e200c50484241e402e00010b51001700390304040580b00382522903c9031200c1c00305000b6030b0703595542010150f1180496006032001c002044010034030f50b100040f541c001c0d0038603c0c082c5041e2880d14441c44049826541115007004a07807075040c140f850a01d8100300c0c81c01101c00032842d90b01441c18641e02186510010306078040c18484040f8401c0200751150010040e500000300c840d60b1540ca07044000e4025001503000030410b03014810000c5a5019070b4161144a29008235207102c850300c03000309000c20404042d0040c3d800c48a100c0030304903251240e0007a03102e414410b1407901c280c0441800e02c9801c5651590301c80e40c0403058420a00d074103586441d213a400c051070320f9807114000030402d0300c160300420450740c00a4000440e240307500e0501020071a0111000f0081e00e8041c2e4a4940d500208202d01c10704010308a01502800240140448a0881c001c1c0075050044070f80381590a4807070625014103003500580d00d40c00ba10 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 638587958 1250 638586708 638586719
    0xf1d010e03061018230901150e01080f120d0b030a05060408070b010e1306050a060f0806040c0b042403060512070501030c0f09050f181f0f050603130305040f0b0301 72
    0xc00c00d4026030281d4000c00c2003082024100b03981c50341e2070481017400c010b071402040441d00d0070360003040750b40000210f00f1452542c40c1e0306004095001d1207802e10b1030182560180c4480d4001c10020003858603486c60038900361a442e1004010110a8a0641c2503c51480070302d000501c20080540074a0280d2210b540f1204a481e100104080503045026140101018030150030040e516801640f680104003040da80c0e929054a0000c00c4243d0122400705494400001e0490001c591540154020381303441f420b580d100c15100c03d80c0e2066200d136801c2040c0a40503c184c030302030115000c1c034061491401180155560001035074501d0052035000481e0004042041250381621a0b0b14802c0c0240c1455000b4240e06207019101070018071075240500c41030403010203d952000b61404955181e000640494203010514061071070ba90f0412944002da0314101003400314a040307200e011900c0090600f4075580d034004010003401100e14080382440700c10301001c608103400100d920301514004040c280c030f941c90701 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 638589208 1250 638587958 638587979
    0x30a0209040807031e0e150a02030703030902121009060605030c2d040203041208060406050f0402070602091009030b060307150e01020c100f020601120b060108040809040612120f1d010e030610 84
    0x3503141030854002300050100103801205a950b4150182400203205066001240780c980016030075100901800306a84d0302c40c1c50690022521034018581080f44035100c4090558990707140c7c491035070103001c50804022600f00d2840703441001980c00b1207030124008040c00701e400e980050301c0845203d805103c07140c4800d03601800c81d5030300c480103d0301805464500300108500249840308680290b4000034010103224454049409c0d4907006080c8506046242c2401071a40f501c60000b1070f0b0310006240891080d10b0f0006035a41901c10002d50040103e0101d00140e030b82c080130000c5141507014910000e41d6036034840c81920f418602c0d586a0b0604a416010000d0900034140c110055840c16103004102291f01800102c0d4071890a09050001d52620f040245090080d8000140e000d810407401103101c131781485095200e80e108002030f060b20014604162401c900c4592580d00203450b0a505c000100c401d081d50307041d405018104184580d0b0110013281c00c00404440c08036884001e802e0420065095 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 638590458 1250 638589208 638589229
    0x712060e040b1f0909020105090607030c02130912050a1107081b040207051002070804031704090e011b0f05090411030115020a03020316061e09050c030a0209040807031e0e 75
    0xa04043c004240b09481c8044103103942030051034116640e40c2d0f910000c590143c404c0701d500300c00003400141c69488a01c0c0003800c40f8a400c104a004052309096030300c4005407409002d02440d40628051812101d4030011100e0780c00406c040b6080104540342c5000c2140c0500880c0080c01e02c603005080f031030f018659203168100c014412a40654410446a804034001141c00c1348590032190f070141e52140c0a0408a540740195003010703040c221000c021444054000009100b181e600f4181803001c9010345810500700c4c0c203c0d0340011154010201200102441062040c07039000d010308046041441d1a4081340494640c2100754280c8007000006100f20003240042c04965222440100b0700203032190f038001e40703d01031050034070400d101c0727044503c0c01c00030180c11540300d0004480103440f00881d02644100901840401500c0303a0003415802c07611030802254644141d41c000d01481000d444680d00c220301c07a40800000c1c1c0c100400d80740749180f12045007c0c7e80d2000c1d04282c1e2002c84000c3c5140070851824030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 638591708 1250 638590458 638590471
    0x12061903050606100203040807060504031b05011d1f02062406070b0a0f020a180f0503030703110f0303101503050103030806121e030406030f05100b030712060e040b 72
    0x106180400c0000d400048240e0301841c152100b011000a44900303a00d180116000071403d0302030400081000c41e40000a00100c0e4058017040302d55110700b21414138180303201e015031030020b40c01104542805480c03a0b44110248030103000403104824100d42c040154040301981e800581012080c0040200d40e900d1601116003032219900800e6003041c000341c1c00e8428400020100c0348841c0010b00c450440e9031220250340880390701995210b041c0c0303800a0a83d401404200d00d6104000c1e8003080400c8403544010507540042d00451908029890030783e07900c0c18940c25043c00b0312684a2a9550349001c0c000f40d40075410000c07002da100d0381030244480540c0500f0b0619010145041c004002295010a5094000c1c100303030b9028603681c0031200924241a00403200c1a03100c00896195440f1902c000028000c60701e0350b1f0b404000e081c100403012001da034010340300100b28500312501840100c0080004540004690500103808041c420740001643d41a510001c0c0314a00c140820003400032a5121580c0042c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 638592958 1250 638591708 638591749
    0x424090c0c0620030723161e05060a02120702060106050d1a1c0c0801020f07060e030c1510051c12120e060601260705030603030c0303090f070812071502040b1206 71
    0x1070300c407600d4503805904c100010304a41c4240d2381160f41100007203420480540c00a05072200c0d8076080201602070360041ca40f61103c1d100c0c40c0c0000d00040e101003142c50507940c641ea20300b803414a4082d02e88024145800001c0d60301b106800c0081c2140d50f9419500d1103080070101821030104d0241080c0324043c4c1c07260320038405a4010003245200440700d10444484950240c2d000851161900c407443c0b82d4001c20301c44100d18410140b09011407400da074502885820742440c40241952541d05000c42d61252210201c095852003202c0070014440c11041c4c4c0d00c01e405403500786079541600401e0f6041d0fa40c040105031003500600148081b03542e0104101c0300e1044c0c010181046ca80e04544070b526140300080503c002c010f804008203045507002d0080f46c040044500886e602d90400c0040a51100440310400f0030903c45c0c0350000942002c08200e44284a00040c0d8150406245464840498600e4076a129440307608110100ba8000000090040c0c440d200d03c2050032407428000b400000841e190943c121070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 638594208 1250 638592958 638592967
    0x80106080d0e1e060d14090a0b160e061b070b040e0f040501150e01080d091809020102030904181b0f050f0f0424090c0c0620030723 58
    0x50382c20035160724502c0e10607141030706014220400b0b40306052004540b558801300004e0100d84105071a0007419900104c0051644281c03181c102c0d0310f41d40c48224800400c0361403010300042403214900c6a42c00c5030b12240c00c0c02c502c0d44c0307220800100c41e03074420000d1101d03a0a030664000755060041000201800140080615050801c044910107100c0101101d0301760813100001410084c0a41048140c401c02c2e07000d01030a2511040e507094050381c00d004103219441840341c1e08400034480d0f4041ca01b1605411844042112080b017500081d11034502d00707a05502c020000485991503600c104075410102d200b40d240002072920340300e026040c22890358010104a110309028195050300c050f81210703000c1f14040080350310358001c030380d050b0240680e4a80c8185800301c1c1a024103860000001041400c2c02492540c0f030301c0d04140e40440e0072604006c0005044035225074009a20360340028200c505c0801d01c810f16900e000014042a0301c01c40f04e60000a02501d02c42040a410031019246d041c00c0c0000e15040c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 638595458 1250 638594208 638594233
    0x5030d0b09011d0702010b3114010e071b080d0b0a0b090103020d1b050306100c030c081c0f021c0504020915120111070b1f06180803040f08010608 64
    0x38890283c030100c401d01d85440440d030f09500135031080042600190903000414200c0038150031000e00316a01500e00c40d1248032071000700c034103803183d403030900d80c40300d141007003030f403c18042060f050310050821041c011096000a40502c02e41400c001e041c1c820390700d0603510410f02d000401501e100c01d02003402a0035150082c4481705d02c48055030140142841e005891710070031188a4050301c0c070341d02d072001d1080d10b111010004640c03140095204240980d2070f42c160103849102250401d5000c00042d0000c0e1466800800080d1550700400b0b02d400851240841c1c03c100d2a070843c1110f0403140c80000c8107038001401d10005040b4131000f401c501d46524104901c1c03038660081051500c8c020301c5408942c5c181800003089603078400c02d42107413150360002040080d1100030b510030341d40d110750410b031745403140240000e03055600e001e081d0515400c800366140c082d5141000944038065100c081c404e2414841c072003c549041e042018200404541100d6141645003401050850340d86400505464000e448802e01e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 638596708 1250 638595458 638595479
    0x714180103030822050303070f080114011b20090601020111190201020f07060b010824090a061509050a06050306100e0609100c121e05090301090f05030d0b0901 70
    0x1101c0d010304140034a6981c0c03814035060718080501c0404504042c004013014010008003443c403030150341c5c5400036400a80304003958602c10034402c6203860400189404000e51140090026810503843c200700c0c02c145a5540003490040014521055101d089480c0903030324204c1c0c0c6030b6410941c02c0c0001c01c0822480c00800c0c1c0b0900c61002241ca00d00b01048124249500c00d50403501c5e078030144100e50b62207111a207081d03005001701490140c0012910408524080185403401c0d000084007109440801101c40601c0320100000780310b0018103a07143c00000345051403081c0c0c0780f548803007603854202142c03c1c4420400e68400d590807450400030240200500e0791241547d800040d16a401c000050000d0000011494812143c05682102071032041090b490303000b040d0300104604c928158002c030f0b400b00c98100c1e0804401e18040148050052900e2038460090009004032000940041141806925144100c003804001101e4a81c0002400000a505031043c000301c07007400c035004180381d450b00c01d0b00309 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 638597958 1250 638596708 638596711
    0x4091410241809050106390312060b03090309031608151807090504020f0301140604020d02040e07020c030607110c04021c06180c02120d0b011709071418 67
    0x1010310078032001c60300046046914000040c44020018404c1e076848900041c1054910059800b040381c84503c012100701c4070031030a200400c007803d10100081c40c0c0f501c1c100c9642d45540d80384013516603120004650820580700651043c070500d0300850383c2e2080c1c48207042c030b03061038a02c030080f0030484220140140140407520002c030200c015240034080e10b41100b460010140107001000a204880c00080c013588a070300041d01c241d008a41c1c0c03100c108407040074903080e215901031040c01c1a200b000011218038003540034103030716060241c1c014141505c0d894494101e480c280c82d00405a40300600b4070100780341c200807070742d40f14000d49409040001c8480a265607a11003007401403003a0b03008034080c07050a920f111134015043d810b2300240041039880003248184010b9000e20440d85080201d8210881d0001540b21030b544d4181000071300cbc0c00c440107502c000901c00c4000d010b0401040b1059406021515001039009004035005800301900c1c0045c0107d42540c4102c5003402450b484008000307107150400b130789 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 638599208 1250 638597958 638598029
    0x30303020309100e010b01171915120804050f100801030f03110d0f021b091503070b210105010c080712021e030403051e0714010504091410 61
    0x9078072900c8511070306042000300c010283e0014a13199100407084415048001080c10a1300c0d0a83c00e842000c0b8052541003088503902007903015801c80301c1c050056640301d400c000d121018102803064031081c644905c985c81440555000b54080f9080c03009140a45210400c00760489a60449180e80d0174054002d0301c0501c0060324548058281d001894000c1314440850750b1400152075408164040151000c0c0c1181410801071140300c0c420305444d0076030403070300d1108171004049000701da4a4a091250240c005401a03405000301d810001e680301c601401350100d041c0e8a02075511311840c45081c0d512486050784020304201c2c8801c43d62010458880440d83d2968200b0251841c181c503220080c0e11f44100170002c51a0b420300e41154464110000c0090800e40e4810001d1304e0310b00c0d4070102200041c1e803452110303520641182e03c040201081c8100805002c003c181003460625640f550501c0c1201c0703c0e24020545c0074006c808200503402d8584a8001030482c7c6407003002c90385401c1740d02030007148411101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 638600458 1250 638599208 638599211
    0xf370b0a0908090402030c2703150406020f0309071802040b0304020603180d02030d060f0501091e0f1203080601181404180804080d0c05120912100b0a06090f030303 72
    0x158024481400e04443d4090030181040d9520304020000c80010352101d20442103080070b1361701c031989480010540051400b0000c00805101c42700d03102421803107101900072035031142d08214040400070280082d5104402001c00303041c080e4502a20f81c0c4032205e48020130718038240b041109003c80c40c2098144c0c1d410030b4055580c19240e50380c00014901540750031100e08020b22440f00507501d0103600100500c807001800b00203001140d59452070100d050710038002d09001c91214001804506030820700e199029540c9503c88461a581d28411201c070a2150805008440041941e8042c55048560b030b80c2c0106013881c01a91010002081c0201103130580120710a80c10042550300c2c403507886820070b1041d07c540f503000341c0e0882003c5c42c051440d03900520803011907005500b0014100c40c0503101c0b42e0803031a048800350000300c4650413580346651021828a03481003101e040300d195554108101c21222841d0310b40003600480d801d0070050b100c001079109200b00400c03c41c003071043c81c3e110744980741140e505040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 638601708 1250 638600458 638600471
    0x30f07031701090203010f0b04140607051c0f031109010804030f020c13051803030708040605100e07020a030306050a0302061e0702060304050607090501081e04050f370b0a 75
    0x4040301e100800c09a03010100414030008940c00000740d00442c120f4181036502c0036581c0c0d03034140308030842c042ca200e00080c10051241984103810900000c0c501a48503009a900346c802e41701491140940c004030400024600c0f24142040c0341d018813480e5802c1c0d514420050510700c42600081c1942070080009041003d25107148618034020022820b8061004084071070100e48444418000d0500710343c1860b45160455030b060302c1c90004011a402031443d9950050159a1911040054100034001c0e4003a000ca036440094504455a1a0b40c00340c200765014002c1c0b24985e060003001d03550650006403242c0001c1d501080140c0e00d02c1d0803140c0c51089108042c800c0603c078003841c1403c0c011400302035041a4000304120400001040d01841601c164940800864464004440c42c0f0002c4568101002d003203100c04049400007441507621601c03407000c603a0343d03403080e0a076142069103900d044180d0825103507015814075441d40140a8850045034000e00441c1a5200c0940c0f03901d0151510700c4441c0d440c2c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 638602958 1250 638601708 638601713
    0x112a0607021c0201020709020a0806030106050603061c050a020a03051509071d0408091c031101050106090b1b0f1b030a020a061202090402040b0405010305060d0b01180f06090c120e030f07 82
    0x446070005090f07500c1c1c01c642720184060041c2c0680b2049541c1032081d440c04a0200301440c0101c15640500b00c0070384040d940960310003203181d0079101240e047d911440358403c0f076401a5030f4101e880003e144100f02030500060760581040c2011406065400340340c109840034050106102c120a100c00c0035000320340c20790b40b40c43c14101d002d44030300191181c01c052104c51920035a0000036a02407203e200e5551303003525845496600d42210f40030301072070700040e01d54034080103a23601680240c41d2500c0466508040664044100da1801030a140310700c0b00394101c02c0c542c091000320500d11481001060300505091482d6a001445500b114081c00050140a032001d920180301903041d2a03104501910840d0348689829607050306401501c00e160009050100080080c1041c2c808000c400c0d60000e030f0051141d00b441541480d8402116a10600d25910360b070b550303071300303030790b60141d00020800c00c600090001489403000300030070605410704081f035041c0341c001c04400300b001086800e41500110216103d280c1031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 638604208 1250 638602958 638602963
    0x4050607120b0a1413020415050c031c06080f0307050309190305062802070507051003090618060e0d08150f0d061a030d08060f01112a0607021c020102 66
    0x14003a8a40041a807400443d04e413840025490660000303c4441c3c120301445d10028060344214064a210181e400c41000825401000039010388040c1d1003c0c0d81c100307548018034001135590001e03064200f5484880070000c4110901501d034101c1d000748080c0d480d10503d80c842e16500e00c2901c1686000d11200071078004000c1020700780101442e8440152030703060400c5081d885412801c0c0c000105040616202c8110304403080c404c48003800c0c0d0000241c56602d281a04204449441e000260241501c0380d803510000351031403007200c96000b144655840c1a07119400d0050440d088101c104046510080001450640061075241c2c0800798544840d1781c1401a03000c41c0c452000364081940066000801c442044500d400100d01ca81e148401c1c0081c0e086a9420903595058850318440820406400302d0b065050180200e0040d04041c10305c000010810b40b0030030714040c81103510f8181c41c00c48846020003d41e0146100040b601c1c12600c09081c54810f400050701d4480401084c101000d400c0c3e032000469009 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 638605458 1250 638604208 638604221
    0x703081f0e090105070207060c021c0302010b03070f0812030408120a020702090a0b030d050a05180d08160b01140a0e07140a2001060b09060a05040e100311090405060712 74
    0x6900d20752520307041211226010341130668800d40035000303110002c11820310400800f4505500209403112124040410f02e080c103c05010640840d521150310b5101500d0800261006020450750654002c0c5400e1109051030114482880b04035020010700c0003081c242c0080c1d90509480b00c8800280e030f00c44001d0714000b44119400207400400c0c8104110a0307080380c0d0300040448a00f60b0a80c1e4000c15001030441d481d01c580d10140000c58070034047d094202d0031080c0b42d030070214400782c558004030312280c50b50b01140d0025000310030040c250042c00030810007010302d807030b00520410742048650901d900020b2040419401103660b4641d83d0400210075903c9540d11032480000d032444559a620301c620b0003010320000c122100d40c40100c20846280c801e405204c0c07102101d158020b8241844880c0c01001107a0340303c5402c1504104081c0400301d061034500c2d042c58050a40108030806062451501c00d140b81c00520880707118011a104202c086900811740c540e22500b0340ca40440c82140e2a10805c004041c0d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 638606708 1250 638605458 638605469
    0x606071209090c0e0f030c010f0c020a180509190c030b06060d1b0905031b041e111e0c06070f20010504050111071e020423010311010201020703081f 65
    0xd101d84071100304c0d044403000310031600685251190b5141201419a2510801c00d40d50000307003448910014584141c1301c1a03441031005202421040d43d540c003a91101d40303000c0d00c1c003102075034032010321135040c0c020088500342d1606091301d104243c2d21038681c00c440c0a420301c0050441665040011f0b45603448604461404065039403c108a030700207004403c1003065201d161001c5204220003141d0dd24000440301900c1225000b88402651344000342700182580000158060f4a404046004003600e40125201d800803a041c2c1a11840101480462100740c41e80340d042c2034400f00b000705418040420f1003680a013850811015100d0035180413142c0001c40261040b03144146400c814404006410807406940144000e01c0a40034500c80e1150600c904038006000f011010b841c60601c401c00e541c2c0e14041c600060000a03203000941c000406036803081140b96000c50418014010804200740d40003c8481c2803000718108001ca0342c1c00340030045c020784001d080e031156030780301080c542204188102904 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 638607958 1250 638606708 638606711
    0x1205070804080615031b0f040e0312130201031407020634110c01090b03010612140f1e190b0a080109152d02072a1706060607120909 58
    0x7506502d50041540c0c1341c0750080c42405030b20004150b003182072600341d5401000a086c8410851200c08020040040e8540c00045000c00e00402c5070030411070440d14462036048210924050302440018225030003078a0741d44090b00d6031400c1c0302d00039a0005a50360311104100b15480c021507848000900711488000f851100c0768440d900342d21082c4d0115a01c54155008004c8511503001140150742600b200d001c1c025140c042030004204842c800d011040610000b140b0014030001144250f820f5818200c0c0d945510ba03074800140142c006400c01d002d1800d40c440610700c07140341042e1420385401001018552502a140c4001101c6691890043c07001031105030000c000266851a082d1030041003d810141c0941c60690303a048801390a40c10000d401c805a4400480c10901c40642e030001d410141058070507000b40194191001902d80c02c600390391000d0365182580f6441d0400080d102d4400c06a009696003240041c000c2c9912058140e92a0550003401c0295040403210200d030070039540c0d8060722130203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 638609208 1250 638607958 638607961
    0x504050724020609010b0609060d0207170a2d03110f0408060f1308040605070303091b08010c030605030c09070c0b010b0d0f050402030604080d141603060f0312050708040806 76
    0x100789440c2200244041c0b41c09980c800e50711414407608a41c003013594260415410007401000b40b411000038038441000c00e600509004881e01d50f5458560005a40110340d5030003d084601d1540010101e640a0b01d0a0101d40c0c5481c1c16110b0078001c0014403c5127000d150b2200300d000e0044017620180c076410191802580c1d225652181d103159101d200340c0d0142c2803c40103402086511002d140c1680580b0741144c00d007403400b4640002118a548000c0c0b0540030140c0e02c00d040e00c0000c2c00d440c261100c04500e0000c040411f410440c1e414219a621030030103040c0341c60030300104801d807000302c1e4144001e0401c5130391640c6941c450340c0a13220ba810700400146502c40000020464200320005840682c80d910070400c200303181c40a40d00100c401c1605c020794994000030010b400260305030028003101d0034001001c02c405002c0c040207403914100b500d03000c0f20f210a60080c24443c90b49881003000800600301040c000500c3e54441703400004920308000c003003000006501c01408400d0040358018080a42181d500303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 638610458 1250 638609208 638609249
    0xb06040207081204030306060f09030b06010509030a060f05100807030f0201030b06030907060905271503072d060f05221401031d07140a030f20010203031905040507 72
    0x83c104032002c4000c00d15025001c0f03861071007401e42101d0802d040d20f440084c5402c644840e40042c038000c0049041140402c80701d03549031810f00181081e18402d11020449000780c41c0707800c05031440108500d402081c0c02d00100712f185400240d9000f01c81c1c001816501113822400120701814014608907008040002840141d6030001010811039640e55034404c074179510b8504000300103c61042540310400c03408130151502040f00d2005800c5030711104211559490040485d0405031664030a190065a807a001c0e012011352100c4642caa41483c882244040d0600300d0182c2000020030381c60042101c0440e01c02d415040c0c282101b214801001e002a61250703448038140402219008100d0029052001e214004000400c04c0e140390103082002e40442030030720b0703d600a208244003c90754010500080000801c2030b201c12105228002c4003c449221720300c800c050802c00101d007900341158020820840c0c0f00c1c400001c0300d078414908070b0000c201c5071101d01b40310b4540308042c0c002100310844000c0c0c2c02c80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 638611708 1250 638610458 638610487
    0xb0108100c03020a1e0c06061d060f030a03050f0f030411010f02150c0c1c0203040305070b0c1f09050607020c040b030712140f0d0306180b0a030b0604020708 69
    0x900c0355100405200907880d030a400c07820380c0a0000300c58003082d0110381404141c8002d80341020344952034078000007005429283c1c00c00b6221203074006060b842000ba10a031a50f005048040d61107042994200030001241c00443e5841c40c0303140c00602000300200e100d20114000034111203110443d05015500d80c1401c0c2000c600da80e44404c900b07404a03042040ea1444203001050031220700c516814644101c0d0354800030610141d100b51103140340d9000e80303500e1154004061110750411001ea9004546590861510500c0c1c2040c83e00040482e500c1440003030313844d860010b4401106155900c03076100c4040d880301307844003614288a000f45140610010011020350018000301804411035090209081c014189034030303aa8103001d01c0740500741520741040030400130f141c0c4a0a0030300070b0040b1054030b490540c6050804141c1c03060302001a403500030030410034151803501195412441b40c1045100030542c009101190144030042c1410303010800291a42e03a9941581c840750f030450318140c2d40f08114403500c1d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 638612958 1250 638611708 638611723
    0x12070b09090a05040b01050108060f0405130212070b03070f03060305030d05041509110f010207211a090c0d0501060506040303051902010e1504050a140102070b060f060f160b0108 78
    0x74000d9500c5400200419090b0080c18042c41d00121005030b580d0a000045541c3d8200800f203030340003451807880080c0e54130340c1d100d0741788100859004194204d0319481009541078090070090b68981c8040810301c140c00a48080301d13045030b001e08001c400c0300509002907026013156400501a80800720b000d280c1890990081d070f101c1e9129000a1320b29850049548046510591010304402d0102207428141d0510200e40040c0310b80500488400540d6801c01c1115202015112241940c4500302c0104002c0c03c1c400304d40103005032880d0704800e490404003c41c3d0341d000c083c0a0912500d002c540113424060207500003005010003504065070340d038881c1806003039680445a80078101400c40c102820580c07044c4200e00e12100040c0207000850070b58564081c0304900034200343d640740100c1520a00145504010881501c3e90400142e2600f50504044685e900000c240750301880c0035072003004581d81c4e40d030200c503a5107406061840d03e408004958060760190103d00501c15480400042031220b00010b04c007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 638614208 1250 638612958 638612977
    0x40204140103110406091a090a060f020c010503060d1112030301140a080123190501120b060a030203071206020903060112051902010c11011101110c0c03120307050912070b 75
    0x240b0180c030b0f10500014441c8541e110300d0000402c064001d010481c5500c25407001442000f25050600c04401d000948540c0c0d2031b40b299001ca0f20050b038190000390148144c440702042400c2607820341c900744020a404081034040280410b01e01144031040b0b03510400c6181d6402d401604072501c9603110410400000030f40040548200d406510015101d0014003034054880b42803050a8000030340c02101e01900f803400f800a83c00041852a00e41c0e90400da0700c1524002c01e4440110318904459061105c0d13010700141c030041c05074550b64400c0c40541c50009500b41280d842c094003201e02105410500c0090186400c0380da8140a00400041d05005e401220794865009200740e0b5850721a5070880740e081c918405c0d00034080780450040030040b40d2250040211640103041070080e0702d407001d464034211000c840d02e200d00c1020114241c1801c035400c008101c1100c0065008140101141031000c416010080264042004c00155680e180d203440c00d880760101c000c0011030f07201e541c4450311046103401c081c154 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 638615458 1250 638614208 638614211
    0x18090506040311070f1a0306221a0f1f0207090509060108010c08011a0702011205040f1b030f06021b0706030f0b0109050f15090d060510080307080a0815040204140103 73
    0x41020304102171030508952046503d611012044404460300b84c00042800b58810300001d074200798482000c0b908000b42a40c000001008901108903804001e00603509a01802941c054a06180c03030b00c0c0da10340f101d0100c8100542c0d44010301407049283c0901ca4114139545401c1009100e00d4100018010b810307114000028400c20410300c00840304020709205805181d0317460b483e503e4a0030300303544c010320300035006150280c00155645031940644000341c90843c4d035100303200c1410044c080482040c5100e0321003480b0a40c660751441d00e4042d2800c070304200c00782c050380d80003c0341000c0f0448100b500030b03c0610a0140c600302a0344900190041004225004255090042c003070b031030398460b83e034500c1035070801011003904000100506c0484c0040c21011480f041041101c1c2c01e03107640316010045814400c9002103801d140140400401035410b03070050800e036000b4804000051105416500817038118603207080c56a5510881040d21143c000c103030b5030810310014001c42c4148000c03101640c550f9082e2030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 638616708 1250 638615458 638615473
    0x60d02070803010512012304050a0b0c0a0e030616080603070510020a0302010506180c0a12022a0a170304030212070c0e1b0a1d0402041401020d03090c18090506040311 73
    0x504500b65207001d5134140c903d0310701019415404c4001400c7e0f58001380a5821603032004c04507915200304010603200c0195084000c034010581c1c591100844150302410b901605070341c207040b1652064044a24181d0003400041c500040307075614100199001004001e0480c0c0c15081c0c4190043e495542001045d001542444006512424030405100342800f120301c200d20280d0342c0c14509905500b20040300c0c02001006491500d580d42d00c0c0c0041c2c41344a0340c4091903c9004d1030580c1c1d00b01c541c0004844013845030022030911000c112400d42a8a842109030942c60743c03652980760072030502240c10301010b0400b1012449100784074003084810b06417900d003448110291688040101034803107500c08601141c00c100320304816944511882c2024403810f894010b04002c900002406036081900700510410030005601e2040da4100003402e101450b034201003011008a03160b03c10030002c070307000b00003407411000c2c81d007003c01c0c2440d40b001211f41c0d00101901c6040c2020714000301081a01e42c00d800702c6204103030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 638617958 1250 638616708 638616739
    0xb150703080124030c11010504050f010c1803030c08070b0f01030606170c040c03092406050114070215040512010501030209010b131202150a020102120a020406051206060d020708030105 81
    0x10608402090300550b08240510024210083c103c602105406c00c8280c846003440e1410074001c103405140320310301904100040005030340c00c58074480c2c3c40c0030130440141c1e00c03860425042d8810005498151501444201284c1003400c4540700e07000e0014032440450f01000104852014018180c1c0c1c81454180400361382c810021480ca4140024000307107403c2141805c07028a000d80c0308124055290a0128680c0e0311601c0f601c003444c88000f0504010800760307418003a6003515104610240c5401d0178001e84000a24407000c1c0d00340288a00280520162054860400b94070750035500100401040103a000040c00758081c0070780300c20311003240101120304c0081001d07a41b050a40d0b912034417140b40c481d06940742240740c7c0034a01d500c0d075060b42c0244207107102c0c540381e5910070010f1502c151a0380015aa650043c000c80459150040040c2c219030f105000078070030280d00404035800300302d100c01c480340c01e070711600d0004d6801c0c42880c02c000800e40c17000403103000f0460b4401c050342c12141c045440105c02030084 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 638619208 1250 638617958 638617979
    0x602010509120423041b020a0605070906050301030f06110a11160b0f03041e0803071107030f1407091803170f221e11041407120b1507030801 62
    0x280100c006074914044c480c040d201480b1591009120014000b00381016004400480c0c0d80f6070440d0000160012044003003400f00a0003440e412104526201d5840383c6001c2000340607004c1804020a9010f0b120101024020160421340c40380761601c0890b5941d0791501009031083e002e280040b12103002d45105005903d4107121900708a43c9028002840d10f500c010a044075130740002c0c000c848424030f942c800c1070394950360449007443d9442184256900d00302294080c05600c405540702c1881da01c900342c140006203115220a0125500c03da1680b65800d198035554144807803a000744940383d03e04242e1401d101103a004c06005c071070003034643d0955940102d03071071a24140115044034102d18a003000c61300703415a600c00850348911034030022480421035543c084001c600d403401c0c03000311268080c051050044180760809003038011101000899800268540904402086a001d020325a10042a807031615044000d410100a0002d031900003410070200081e000402d007500000c00040021403c3c1d08078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 638620458 1250 638619208 638619217
    0xc100201090c0e06091506180a090c11211207020c1f030b0301051b071a0103080711030109020d021507510b131503050105061804020f0415060201050912 67
    0x84d20561500319058030246007844070208443c3c10402754800083c0745241072043c60301c044506e80e50104c03c4801883c6241c03034094810300320985031009050405159a10304100e490041c9071041070031843da650b01c0181d00704110380f40d011b03402502255800c005841001ca03003424a03185510100403101904043c1030881c1e108a50044082d0036002240b403001014001030b03c1424880c006d400e82e9000fa80052a20103a02030707004440c0340c0b0011668004000ca1030805898419003900208403042d0b594001443c2140f068202901a402442403400c9039005c00d82214107050f0424030b10706508091540015024a449850b5001104141d610100305040da48181d01514600e004c64400810040b290000500403000035070303448100c2125110060815016070b9044d015042005960349185041550035100c0040010f4403483c030381c0b030b1452a6420440342058116405076180290442c804006c58000c11146011964080c80140000b034503660542217180f10b01c0401e401d450350100d101140c4200f5008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 638621708 1250 638620458 638620501
    0x708070315060c140106051504030201020d0c0b1f080a0311010b0306010e0103080a0207150305160e0d060519181e03170403021606050a110703050c100201090c0e0609 73
    0x980c1c03420760125042c4d015a0041c050500000603203c0d82e01c05c00150640280e985580f09031001181c10000d560b010300140b5051041818403440341c84080d5501850244018404c020642080b416200081130f6000e6400280c0818011140c0b0000340d0300f000703400200d0141c4281c6840d07080045051036400d0128130103048891400b501421642075655802036504550380040441c426044005090003105141011280c0d0300c0e1400140d508044090401144644850b4001c0c0310340f081d02d200d040c2c3c41e101108511203400400c0042d081e1907804400a200508404000800703060800c62012500441014640588141d8a0125802d48440c1c0c0b030040d13501070140a40441c070828445051903460340882d90f4130520030320507508409500001c801841c19190058000100049500502d035500b145905409085001c0244481c91071580d649550741850b41800d0300540c5101c0307044658600075000798401030341c00444012915140d00c400f000a0742c0c03c664441c0309490f540c2c00700361800c1100400d80040781c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 638622958 1250 638621708 638621717
    0x1009060f050d0b090a0b01060f020115050a0b0901020705040e1f15093b010b01020f1216080f0702130504050a03111212100e070801050418020306070807031506 70
    0x800300d450340108810014119845401018421700c00101030580844c040c0407180c8401c0308418034807030000d084a00c54006010000503440c07013844660350f8041d0040c01c0310560a405940c0b00f1600d00101d050441e00c1d0310103a0454104103041c2c211090110341c056000d06003030f5005c0d40d0141e0b00c00251056804626000703c280a90110074821030310030703802c02e4866051340b5414419094007500300c010100c41c2d8000761599000c00c200c59890449081c040c04044510910042c0581c0c0c1d8215001034030b6003510124000110b50001e41d02d0185e050341092080f441c1d4004010300d403280b40608040001e6071210008a125048a824401520f8400c3c8a01da01880c1c00000811b202803182e40c0640d181d0385031200001683c41200c00785101201080d005150b201550346141045007050440107102c601035800004007441d08a0810001b0717a440301c18141114401c982c081840c1030300f4007aa0900d508014006500b40c0140030400500c140c0200040707000d80c200d56020418030081012142c04494640a5040040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 638624208 1250 638622958 638622979
    0x60518120a02152514060103241404150e030a0503010b030604090203070b0301082a0f03102c010504030f03050a02090405091b030f07031419050d121e0c030908031009060f05 76
    0x141469010042c80ca60950000984800702b02003003000c0c0c1c4000c441c1201d06c1c003482407103040030242902a03480c015503441c00544c181b0104000c00b4085000c14050300e2203100c40800002c00940d615042400380c960094191004680c480c030400c0e000758400d000d007084a101c1c640046003000c00b00700f4040e010340021100c1d640040e015004210a00c0b0218804a03410b00c5401404031a20780d60380f01d07000080004a010303d00b80c40446008a01c8031901161004099151808100101c0c0e04014001307200700441c0740000b015620070840708002d00514510036006460081000b01d02200001d040030a16030b9a1140d52950661004050b562103035403110f501e240c1c00600c4200000b034094141c00d031b02d55080d0320039164150f00f16841600c0c4003004150550b00c43e40203c0c014041c035508422420341c6640d4080c000e121000401c14580c50080035084950540d80e07a5000594805103e03a001c1c040e8079038448019903032418050640c410030002400f07080400303443c0c00d13000111100449276880c11108040c00700c5120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 638625458 1250 638624208 638624243
    0x6090b0f0c01061802130911030f100b0a08010501020c0301090804091109060a02150a051608060d0b0f01090c08040f020405041b060518120a02152514060103 69
    0x240d000241152010740d03d80340045500041255151910312003010016103c40c0b082c4003418081609600c2482c405151110100f42c460311801101e601000c043c51b00340450701c0b89503481c90f0551041d844a600d0309c2000c61a045015884000c590403034209030308540ca0680f28100305400c80d100c1c0d03d0010403d18040000f004a110a03030440e00404040d80391803400c2008440101d10690f00205100d4016006200702001c151006c25185400c204104401c102034544040950141c8000d05280014490840001041a9141001d00b00d00e41e9002c0d82c11402d41c1821700d900c0c40355280c2802030329162030030202c003e4441c5100c0c0c003946200742d4018286040180345602408000c202c00782090b0fa060a6041012521280311510280141095680c0d9503442400c0540e0030012075200780da540c86440388404010380c030900054460f1205804503030305080100f0a103500c0c041e42c410884505110300e20110800c1e0404c0751507000314801e5002740d61803101c402c40312000ea9180c170400d0200400180680728032145 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 638626708 1250 638625458 638625487
    0x901270506030f030403151d07050906060d0207060b12010c080c090102070503030a0c02040605060c030d1109120a020a0b0c07060f0302070206070b090d1d060c0c090108060103030906090b 82
    0x200400080d083d100c00e0307a90000c000c1d003541d000b40c1050760300405038491801c1c0039800d48900d400015a484050740601d140001c001d4442e1a548200351040410101043c0d0139500d400440c4c80403205075008560b80c200a1030030401510032112007074490b06e54080182000101801031075190941d60b1741e0410640d94058403525140c10000c0140c2c1148030b408004600b54030100b00903c400c2102e501c03104410241391042000340e864540101d40204010300ca40c00120308004107039400d0500c4a070000c126018404000e60090084200300d07648041d01c180c0600301c1c0303100441da04081500030386003001c00070744540b4003101d40d100c1c2e08409842944080390401c01603200d01c001c0000c00101d80f46c050319040440d000104c05030891841074580e40b41100c240f20040380200211041f1400b11304000341078039401d2903c1075000103e06030103805501d00161401c100c4406200703003401e21304001c25a18130f958460f5502545c4000c2404214045000400c0c003040c0c1500540c6221308650034117640300c1c034007031100c4d403000d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 638627958 1250 638626708 638626711
    0x1407060302131e0803070317090c0d02210106170127020105031015080106030b0306040b0c090a0801060308190206010e0711390a0f030b0702070e040302070509012705 73
    0x110603d0503410100d10110240010028207000382d82e400364241500e0b020102046014080d01c140b0307030002039580b00702c0d00c5501a40c004940c0443e40c51090410f1483d806250565410b40c02070700f035280c81008641c0501e082c02504480c440000200f20f05041080d143d41c2c40f404854800d2150015070f10070b000198407a200459210901c1500c0c0c030780140e6510358124050f21015030510102da00796005019940d0b06101c1d501c80004121700a21143c1010b4039540c50b043c2000d415450040e07400200070f17509072900260f56009060410003003010075543d0504107410303001465001c070070401c07016190300190301c005101d9040e60701224070820f0a456440302680c40044d04440c0181c58099024454101c032100070644210841810040c07400701400700310386040c4000300c43c0ca54859040300300f0501c503c1131810a101c0070b0707075070160a030345058503095002e0340b0f0018640d00102504511804003c109640400c1c410115a426280701f0101d0b601c5000e440842000150144103030b00e03030707038603080c0c0150165000340f03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 638629208 1250 638627958 638627999
    0x10b030f0c0c0304080a1a070807050c07030227100608070f0c06140415060e06060c03070c090b180628050a080a1e02030d030507030204050d140706030213 68
    0x346810b46449065003990002e510090301d6400010461041c0400c09000c1c500300842028011040e10b03184d030015158032405040e902c02c01902041d00c05a0200c00c102040145070001d040b80040c2901039605541e07015002410501e840c0071102094400400640348030035102c00d51691a00c59881d02421107441f10451280010072254807000070100b80c291081c40d1904001012051603481c041c103040080c80c629000f140c2c10280381601c200304030390302d0080003504204121044d80c2e0710322200a5161a500400d400a0300c0b40204850000d1001c51381e5120200010b01641c48419000503031803a22890b00c0211075140d00500d01c0504404e009050380e00361740317010080c0c0a004014544940224082d80881d40110b030055000b16903000a002000c20064405030300c240c04100c0c501c05560119440c0e80400b40200700381501c23030340810042c601a405a9000d81409011030101d0000d60400c502a0b40b02458902441c0c000c9100105069219008840c0c000c10303c43d1252080b01e1521f50300c0c6030700c2a815000fa = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 638630458 1250 638629208 638629231
    0x60c0f03050f0f0a0c020f09070f35090c0f150903011e020c01060905070903080d06050319030807020a0201050910030b030f0c19080d0f050d1409100203010b030f 71
    0x12001e10301e07943c0c0c1c00303041c4070b2503503941c2c8440d01c29641c4140304a8400121099118a01c1c200c00c00881075031200d80380d45d6081c0146002c030700010740192840d0701e100800c421000c0440c0d40c00282940014458031561203401c1c00750840c1c088400b0403090080c141311407440c80781c12140354020015640d81083c000d103000200a80001481030046400c1d10100c1e0b4152a440526900060400c114801c2409800e0260045001c10411820004c1c07000d001c99405110040c8694000b2800503d10311160b40140010200a0b0656540320110030303103a80951802841140800d08800126003240d10000f01402000d6042c4c4415203803406074400c200070750300c10251060416440e589400c8558070300b404407182c400d100d407008160a41d282c004004281e00d030040c074a0440082000d0030800d9000c00205101309110343c2c07d142480d9200e0003400c50b800d00c114520310f0940c0382407280f8174000028080080d881903040d08195105115280c2c41c407802d0748002e104e01c040e024000d20200f1403800150315910f8028805400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 638631708 1250 638630458 638630467
    0x60a02031204060c030e06130605060310050106092c06240f1b0328090b0c1c0c08040306050c070b0c03010320010206042622060c0f03050f 61
    0x101c1c651200454040741c0c11515410780032007840e003600480e10b00d450f20300080c0c4031030b2600040f070701c40c00300e17050b0b0380a4001a1100080b44060701d0911104c3c0c00c841c0101d00c03d014945e11181d0140813403080e4800c0b000f011348403111a03c0204140244082c10f612007101c0b01c01181c0f01c003410070406d40280c1c0052613030a61001080d034458070700721004104160420910f10780340c86156a001850740f20321801044990010441364403c8820003181d0103480304812421039001404100403a5840ea40e9001141d01120000c3c0210100c5000981035241402034841c0714131190322084100c800340d002290052034220248000e000184098001d00d80c06030402003c0740c03c00200d40ca849100140540da4816000000001481404842d0b00304949040c1c803207040301141c08005000170f6842c400213001502c49618020384112110000c1100108e036541e1120854840151924122009030f03854480f0011038040040082c0a0340201a6180016003000000030309000c1c03034030191199400f500b40001004000c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 638632958 1250 638631708 638631727
    0x100b010215180717010b0102010b0303030f0a02070b01080616090f0504020c01140c0c060901021213060b040f020903060f062101150609080d170c0a03020903031818090705060a0203 79
    0x2583d070080502c18607003d5141c052000d41d40c211010035140604590524a544000e500d0000c00c8981042200c5a140c4059560f030750004002c1c040c48600402c4080414000038808100091440c002d400303c207558100b02221204c00d84140d8000d114518500e01070b0b220411062400d139014160130390b80342001052401042da00004801c8e81194120a040404200c940380902c04002140d442502800210310300643c001d0110003604004000303e8940180040450030007403075800c8018590317809001032298030101d94403230001e5040741410b2406445080300103449078903400c1c0c809000302c1002d84408080b00c8040c2a9640c43d12058031441020364959003200b84500c54003811000501190b982c2400c1c5504140040e810615111500010403aa0b007101c41054564a44566004001303005036581d00d40552800303401031b0152001480d45400085100c00b480c00e0380031002e10581400f00c59418400134407a144041e000c0c401c0d0340d00900e580c00b541e0140710a003481c40c01400c1c031740c4040c011641080c0030302 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 638634208 1250 638632958 638632963
    0x62208090d0305072a030809131a030c01020c0906040b150c012a0207060f0905090a020901020f122b0f0b1002150402041104030b0a050405100b01021518 67
    0x700450000303200103140024030212165407080142c5445124100791080102d020403c00d440c00042c01c841400154034005640e10850a010740400b40d00c00e000c140400742090b03549a0190000174042c0c0650a07824190b503101203021804060700400d03102403611000c00f800010584032581c240c0003880148000c02c01c50b20000070f8076042d4003080022542426180440d080303207000d1003080c0f2001c181440011140703600452400d081d44c20320700d8261010386a4020440711460b055015680200c102000d101511070390b90001c008151081e003c9400002041000c9070b03a40008211000c80440b083c443c00b100203505c080850125038205110103100038012048000715040521140780303c0340d032140c014140d4284011009110031041c000760001c510302440c4002c0060f00100001c0c800c550b00c0181c003406030f00d5034081e90013842c0c00800d10b4005203031048111004190603102915030744641d80e5a168600041d0140d0682020103901600c00214000d50410518201508105020b07007001c5151010000c00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 638635458 1250 638634208 638634229
    0xe040609020604030b0910060e040201022109060f09040615090e09010b21060c03060a0b09040f0903090906050406122301230a14010e040f060c0302031806220809 71
    0xc4c05041fa1180346145241182d10030707071086c2010400c0c20108400350ba00460712014001602520b03034151500c049407140d2602c11581500e52004d4045924146e0900d1480600048d01d01500c041142c2c9442da440c41b400c650340c03800d68030300180c4690000e1114440c5510000c0d000101710002280201b90711000895800010036006051417141e02d558050344410048260801d8010322111301d581080c10110b0310707440741400b400f1080300c0c0000d0030440548880d4042c01c0d2a201c038000801c864041460000d008545c10702ca550549400c1c468046903504c0c0604c250b5040b1100c1920705400c851030b81e90385109000d1802e0a82116104100b4401302c001c90a000e184800c0800c9540c804180c3d0040980038104007010340784413165481e00c00c1920500f808500202c0c107660f07480c0b006104581c0c8a00d0700c074080c0c00c130290300240101d050482c4803a0362038050b0007441c003850782c074002c07403440780da520090382d5441c6400c0743d000e0615914005003040b011403002c413403136145015207001d40c0360805100214500c3c108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 638636708 1250 638635458 638635471
    0x92701060b0d1407050f1b0a0b010608070809030d0c03140108010510170303060f150a0201020d2315010905090f04051516210c0c05010e01060e040609020604030b 71
    0x140b414444541e078496072030002030a40009074207040443d001001341c000d0b800092400400025500900b41d40030034403800c02101e4204540c4105014500b10360000400e03c1410003240c5041c000c56102c5c0d01904869208441e0703034000318100b1041c0c144a201410400e0001c005140d50f400c41216080740d10100c0310701906051001207118108641d20003201070a95110081c4802c0d4980c00d1654064080216500503074201d400d44500080100081c10080d0111004441d030702002400c9a0900e4041d0050240400c00d040300704080e40c010052080e220100c48200240c85500d84c1c0050152a0254844c01403900c0614140784a182c0382e20200d0201103094851f0f45c410a100800c110400804200010022904000012240c103007095500040b0108025141c00e00c4038042905c14040990105c88510440e41c000c00d00c0035680c1c00901078803518640c4000d45041d400c040c0c070054407a03814014902125800d5114100f035a5807a1940d1004101c00c0f40c040b82e1007001044000f0105030f140098902508 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 638637958 1250 638636708 638636729
    0x1d04230a0c081c0e0910180c0206130203030a030c0201060b0414030607030e15062706030c062d040806090312010f03030503040213141f09020909270106 67
    0x10306001100d45410070004a030f440c110035540702034030304651041200c40c402400740c8200071240c49040c140a513514954010303074034240d45c0f852001800303022508020942e085540a840d01da4a40e182c4480304403ea499020f5010b034410004440203511a6002290480c501c1c03000003101c54540d041e4028580c880d038054181e0411840d410041490103002075a04040385003800c0024071506031201780c039440180000300c8404850300006102d52035601c8401c81c0c481030035401456400c030300019543d8001c010f5034001c0c001c1c814107240710704c0c504100c021a04046035140c0c6c0a61180d0f0500000081d15180789510a4080d03c1400700248000703041200c42d00a08500001d1511091890045034450b0310580c0500400c10308040c0c00c00c04079402404503508141c055400c0d140095039004440050585e000c01442c0e550b05900801c81000c0100042103407110301d80b510103165036035a0103450180c1c000e034400c240d032005103200812204680ca0440308940400041c00860b41c03e022184c00d421034515920122094 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 638639208 1250 638637958 638637983
    0xb03030d090314041523030406050403020c0d03081503071d0115020102070809041d070906060f0e0906270a0204030c0801090c030318090e0c0103061d04230a 69
    0x50f000508102e51030a29480707641082d00e0032942121560803840d0500c180041e0198504c41d01c18080804a440e0800d40b5081d552800c04d0318010000304011107043e401401140c031f54090742c2c9000144040309642591382c0030300e140c591001d4040c001c6491002e090340340c4211480080e4400306c5600700003001300043e102a6596140c0060b0b201c50301340c0039010800f1644100821000034181405956045500b902d002940c5420800224020514801c045241d40300d68180060401102c2d04003400795549680c80300040d60503884161041d00300e003071110fa480910b40c00082e8150905c0190342c06a2003c03c20030503103001040c007080000c4102940d0012485400160600522803040d90380001070166200800108015446030100424203010003001c00c40ca102841010051a000000c0503007047c0804000c6e0405045040750b4503100003110301d0101c1d0400c2d5000442011a07003042c02c030414500d5004e01142c0d1155a25450f44140303480c85e40c0d0031b04110b0241c0c1c10040c400c02c0304201b03e5100d41c4808146 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 638640458 1250 638639208 638639213
    0x31e09030309060708010e16030605041a030c0d150c0e10021b150a080901060801020c0c040f02040b0f0a09090501150314010b1b030408010507090f050108060d030f030b03030d09 78
    0x43c039000626080500149900420030081c503c009540c2c0030b00c0d550a51000100c004000f20043c1800d07074402a4031038100641d445950074682000f10400800300c0444800d845080c00b440501429000040e04a60401900507854200d981040750403011030318000300010300c5800003d006002959001d401070307000c40007004076003035814041c1480c02002c80d881c290284c040c0300c44d00958070800b90707901d082040003030105032110000d4004201511030b00c0c3c000d545030f107010081d1035a9207106100062040b030906004200d00c0e00180300302c60544000c40740f80b510b461861104881380d94091104082007040400001074043c078113100b0b0501805054107030100b60503807074000030305480c102070351800c03210f40100c01000b00d202c2e10401c490783c3d9040901078400303a40602180d0b90460185a202d084a542401c0403c02850790205804e001e44450000340c0c86600d450300011100504100c0c1c240703800c002c620a6409c0030030700074000c0c1d880341c04803460045110301507000840d0954101c0403902e8805a140c0302203004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 638641708 1250 638640458 638640463
    0x602010501060201090b180c13020901030f060501080c0313020904080d05090c1e180a0615090b040b0309010f0905101a060703030c020f012a0c0314031e09030309 71
    0x10b20003031000340503179a45912a403240341005049000544052010146003e009000c03d031a600300090482e04520300038900c0c0000f0b0345c030446c0c20134000303441c04054032102005841008241d03107044e07681200c56a01d46001400903030015103400006504c0a91380c0700180c0d200b07035400744582d12944006869550200c0084150340000d040a8a2504409207104140c2c40b0440c03821410001011140d20700c1403602c01184421404070404543d05402d04100041c10215420440840c1d030640034070b0000b0b120060080300d481c20a4060840726030401c1008000541045001d103030007030100300c00012070a43c95400c010444034040e008841c070341c1021100d10103030b00c514030031000d15007010685810710029035400503c0034440d12a0007020b241d42d40d0101103180d4403c04c540d02c7e407099504000c100141c0222000f410044102444007008038115402d120200c3c40703080c142028a80c551680c00c0300c940e00f00e4080700c0640004216108800c1100410300c1041c45400401f4050038002c0080e55990401104003070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 638642958 1250 638641708 638641711
    0x1207080702100c021e1504080705010f050f0414040b1f030f0903020a0209040515041103070b041503091403040306090b06030a031223090303090f19032703050706020105 74
    0x2410700010002ca80090303142c10b83e05c9400305203121400a4802c0740d0100043d0007940d2407290641c0c0b80c030003040108130610300141c403000781caa090b21a502d542c0a0b80e001101e04d8419410030b59520340090008000c0e0b603882d001501e0b0004002000801d0400d21400482c2d03515071000c07c038503907400152041c089203940520502c0d40719000c40f28140848a51a1406950741000100c021f0142440c0c40001d014040140b1104000810580400c01035082070701742410b040101a00c810b100340560030340040c030303000614122411a080d0b998400111428114260b0061401d2032098a004500c0c1ca050808480140028005148690030001d0b541125050036010004010030950007948034901020103ea04001c4508c0c10710044400410644105c65821441c0c68030400340c5210617040b071048c00260304012014500c40c0810b1f02c2200c2da92502041c0c80c640c3c8012880402c6041071810010b140806e2290b4501074451620030205034071342484100100b00e04a01d94020f0f14590400306007844001e60a000e003a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 638644208 1250 638642958 638642989
    0x180607330615050d0b040e03070519030801120303060801020307020115120203121e1b060610050316050405030307050d1106060a050d05011b020f15010f0311031207080702 75
    0x40201e5401d01c2e48441d03070700c80724020380428441d010451051520140d0844058050040d100340030703e0659101c1240d40c0d800410084441d40100007000901002d030b4103caa0b01300d50103507070310f803203a0340381900c50710000400141c00d03001c16484000204100a09000860041c0f550742c0c000107040314076040d038848140c080d8000241c0940c070f075080c02015907000140907803c62004001140d9030316540101104924105a029601d0003001c116110b00038040444d0f100324140b46000d4810550b01e10040202071030060307a0400c00304030280041a01002c00c4e50020042103160f0030558502130b01e400009286800c51101252141d0105140d0780105901100f100e9020142c0c80c0146824101100083c00c4001c2500847d40584c400c00c1c52807062190940000018001c10700238071507074524002c4001c2d1141c3c2d410003412010f1242810705034440038410156812500010518418076080d59a004000f03645040126414494101c1201d644c42e060001085d0242c803480d2410380e90005407040c883c0c0100201c0c02c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 638645458 1250 638644208 638644211
    0x17091e070b04090c1209081b0115090b18090309030f1c1b2009150d0b180d0201050403090501030606051608040f08010b0406050409020618060733 64
    0x4002400010741950103a44a058011601e014008030441d00040c0d021382507100ca504100a80050004507001441c502d003000c50701440c40c03004083e00601345c91442c415641005000c00c010481c00c0000d41c05140001d200a041c0004540d08107404254148207a940b5015500300181e442d0940c9400c0108425000310303100030344804114944e0122140c0194200c0206024a900e502203600040740f00e0800900d50000c85000401408020030449050031200300b4054111280400c8031182c5c0c1c2c034030046108400030404103141815175603c2d030301c0c004060810f2002640340c082c14904e02c4411b1203803403800d0000340d000282d00e184c01c1c1001425050075500081c10315150120034000383e5800012168061207280090580d207032030f49031030b0b2110706c00e41e800a00c0d0a600821b01182c0490190441ca4140e0021107003802610385460410045850840c802075020008101440f603244185001404295008089506040580d00c402072001c220703105103c420000005400300190f01511107528036180740d00d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 638646708 1250 638645458 638645473
    0xa150c2c0604090c2f0a110a03080d15080606280504020316120c0c0308071806031505040b06041a0408010f0605100804080a0311090303070f0b28050717091e 69
    0x140c0e00ca08280c0e1004e0b140030017440c4441d48903141e01810350009d691000840741ea620f11912900c00501250503560116848000001503131403001400302e01600004020088103002c0030b000342c4c14a00e002c41c140c3e0050b800140009079683d654809584500c59900080048500110004000000340c5048500740c519042002c0c0700d903948a40c0c0180c10036414100044552070740d440c01e807101d006240340307003010200c4036801081907a0f158200480002c144d141d0340e5401a101c100700b1003a6140030b403100f50064000e00040050002e4000d02e480380981c10985e003403500b40c4402da010b0958140c030000500c0561100390802c0700f4285580c8094402030507141000c010304040c1d503156058416004078104040c0c503401e0800201181d802100c3c00500020110b0f0395070300c22850f00d20880c010002041d80d103c8168000562090702006003020f48074164080c494407600383c14814001005c0180180c01044a0302805064003422080c415018458400043c1000c0c00c144582c5c0341d0340c0c810100220320703a4200c4070303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 638647958 1250 638646708 638646797
    0x42102060408090103090c0f090f0209060927010e0f09010b0117060109120c06021e10110405062a0f061303020a050a150c2c0604090c 59
    0x1811a005a4801e902c1560740c004000120054411250003504801d5000c9001134440018400c002c02c840c00e000c1d0078084561040660004c90140241c41c0e070300010104506c01052034566900505005a8024141031982d141e001d01c00440c8240c01580c001000d01c824840250a0100b509500a941000900010441d803000071b0500d50281002c5a608a03000301140d82c0740e0007021381c807000d041c0d0720002800300e624034240300441c15000c1c4200409802502c1c170101c6c1201d844001000c6c5001d80700b0080c140040c4040e800d030001c06540e80c11241380302050101141680c0c0700801050304609020480c124289041e211108102c60b00d03500c2101584185084c16408801103040c652112410300031410300d07500f0742800e03030408524000041c11070107600608030801007a00352250001c140050204002c00000500b03840312410360b03000c21150004406008040741041c0a11409818043d0415080c40d64a0812105540e41140c0d2000400d00c43e18907040140050140000c2940d840c0092802418158 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 638649208 1250 638647958 638647963
    0x6192c01031a04060209060f070c120804060c05010204050423010e0709050d051c08010e0c0406141e0a030c031503020f060c01090c12120201050f0c0d060b030a05042102 74
    0x2041070400b40c486000000c0910003140d0507188200d40161290f82e83d00b620990800403903106c04821540c8104400010a0301583c03241d05031300c0990310005013490030341010415590ba074040e49044071603640800020130103845030b0003044080d650a02d0741000b49000840d444054000503000b10350618503000812080c180d1000c0081c0480e541910134011600d0203080c454246a07003005a0b109000122006451080e0300040141c125540c4031b000c1c60a54a40c4016203d140c4500d115250000d0654444100006001c1009240c50b244405005051150150702ea0145401c0343d0003000106c1e5680c620b1f005859018001c0c455a07403d0103046140c0780341150b001680c0401c2e40c00d5200d000d12004612980d000409601c9404050b03084010794031910760319505000c062504030001c8912801c4092080c10f15401401094003c0095507004002640c1d64214042d403604550f40c0440310f0713600c078040041c003200c840000b0740c0503102c054008902c1c0d25180c18001d030741451303400261170441200240c02144aa02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 638650458 1250 638649208 638649233
    0xc010806060a030207050102030c03090d0906200a1209140a21021c050718021303060b0105070b0f0106020105090a050a0201080604140a09020f0a081506192c0103 71
    0x440340341e5152801880d040b0024000c0380c9005005610020600031009139a0001e1441050b01d00c4c01c840d0500800c20007200c07404c00c50312490000c60100168803513440c00080400019a401604480e80c01d00140c031800d40915000e4150b00100e90b0710385c0d00f40680c2445144100380d4040648082e500f01c0d180145800d82803c41114a600c231045081402045517903a0303401380d101038406504041480851308000e5183c00c4940301e10300140c0c010f420804226910b90007660342240c01081040701040c5540c071040c001d000400c030101d0400c8020003400e400284040c0609020380c58101d4510f00703c0d81000c0010b402c42c0c002800350f1405a00040005000a00002c5c02d080159030a18010800e070310b482c0017003000740140e090840f003e03117038100030060076221a0780100020341c002c88100c1e4194012000340403045189000721149504052950b008008080e044240c001c2d8020b843e2201e0b6100b4041d001c030450016070407551400700120720b0b0007481e41370040c207440c40c2c412002c03007030166500d9542d91070708042c274 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 638651708 1250 638650458 638650471
    0x100603090c030b1b0307030b0906010e400212070203070507170c060f0d0609060f09021b0303040b0709061d01080405100c020a03081608130609050115060f020c0108 72
    0x1441c03c001400003580100d49244288441c4096449040c4107002501a001c586800d5021b4410000000c07076030341c401c900c4202c0c01e60000e803001003047d4000400f904040031208010540c07865446900400c2450540c00344200e000b0701e9030040c0c0300d880071090801040c401a04d07140855100340485030206001007104001c441c80302c00c00c01040103080f1306017410b1030b60320800c59a000c46e0200c5d8100d034011601c801001c2c51101c2101c20056191200c0c1c0c5c4104441c20b034040c4400701c1411a00a1015100c43e60003881108800900e0720440c044a543c503c0c61544219800c440024500081c0034546800031180d2002c0c1c141c5082601d80f00d181a0144240042079413446410003405d480842e045c01028444000805d0000000380004d2a2051019507100d0f01c51208074000381d00a40019101c0468144048204070560782e400c2c110f071140c0d07501c00009804940c0c155841c540e540d418000180d02440307101d01c1c2c0c0d4000d8003e0349805182c040040c1a1f810400e049000359040520342203010b81c3e00c4100150b2000303 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 638652958 1250 638651708 638651723
    0xd0504050a090902011704050c1009030605090a030e1210110913050c0304170702120102030916080d0807050c060721181401020d1a0f03070b0a080618040605100603090c03 75
    0x2501e90405d6449c14202c03809094001584072040b41e06c0325403006149040d64000d01e03060080c0d40b945408c1030344e5280800b80260000c2c40c126a00d442c41c0ca8200031130b841c885904000c0394080007800d5052001c66480850103506d80500040021032400d00800d090001040a002041640303020b441c07222042c030000344010144484000341200c01d0030110140c031750694000e086c040f032001c003d40c8170324002d510580e8000075500c910104130100d0204043c40100f03882e00740c400340c02080041c206c00d881402000c0c021900b40941805018207000c82009032030310580040da10b1103140502103582c5080c00a20050480345a4106952801048600f0340103e00d100e5018400344804140c06401c01c0c02030144000a4800c0d50800c0040c80d01800e141d8400101c0b80d80880c2c042001a07000d20030144d4a483d9881076901008060141d01105c0c1c0c098503090303500c0352018203484003000c00c4407041141c2c450129030854580b90340b00140035603000200c40c548064181b0741000c02841c9240d03200e00110000c1440001c0204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 638654208 1250 638652958 638652961
    0x5011215020f120a05010e010f030201210b190306050c030c120c0c0114040b1e010612200a080a06050310050903040f15020d030c05070807140d0504050a0909020117 72
    0x1070100c42c01c45014002c000b0b611010b034201200e840000e410f0a124440445040c0c200108101501455400032a94140c491702040c48108044405440e1921884914580d032980302d10710545903038542900525100340e21807035960451801d4400c0b104003a2220804000500421045003054002c58550300e40c88461240d01e0b0750f0313910131700f107061186864030301a95081c4050b0700c4a882c602d2545034003441c072400f00c02085503100c4503110300303001140202680d101960801080124002c00d4241c0c120050700a000c1b41494440c03002c07150300200b60b00507100429000482190302c81e406402141c0107041e42800380107a915100000c0d50301c4040102004000b82e8510108040001c00c1084600420b001030b44100700e941c0d5604040c0502c02c1c00b007031100141c00341ea9644a8000e02c0392040e4010442c0c180c861030f08184058071284c08940204808450402c01d00e070f491161000704001c1800c6010361655041d5540d0301700020320801c0c09256201510860826a0100060303070041c0728205030001300340344500395 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 638655458 1250 638654208 638654227
    0x1030509010f020c071715040212121305042f0d060e0a02030717220f0c0b0904060504020c1203040f080d020307110c0a05060c100501180501121502 65
    0x6002c40b4540c407081d01e10000300d24001c40400300d0840304464010140a000e4141c000ca044d0f2103070700d94031170030803544184c100280040c41c0a40710781c010400c1d032508032510028040c0310f9500f40e030711500980c0c2c14405c0c400d408109529003406000c008810000034160710050180ea102c00c001062040001c052401140c40982e00b41d05606c980020f126810415401c0cbc02d200100c84025802940d21100050100700d542c803020f85070028030b501a15a1a9a40c0300c65203100304449520a541042162a40310f4811b62101086100b070b550b6000c0d20700b1f5050140d8410040c000c001c121007107940b11500560041c40320050440c008103002c524060034940b1141e82e6070b40d501d000c4104500140c0c00605019001c140c6841c2810f40e0742c083c600c50070341501c58000100b0707001c0080d41c1d44c110b140c0d02c441e480440c6210a12003410964054032410982c5811114480c41c55100001a100d098014000008500b001001da0300700380d0050314010222210020a810f62940301c590080d04920014100280c002038000700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 638656708 1250 638655458 638655461
    0xe07020a0b151201090f0209070c08040308071718030c0307030c0e1302060a0203090f09130609030203190c0512040b030c1c0504030309060507030605030307021e120a150c0e0103050901 81
    0x8403c0c1940001c020401091401510400802c0c8041c2d019102c4540020450350242038070444540d000070000b4101803642c0d031080704650040d00b044450a02c10401d4500c0c160200018010800c07861040d40e06103042c000c181880c011201214604c40e910101e41000400d900310f44141c00e468070f402c000400759542089684801d050164000d410410020751039900e00d80c04009880f085008480a41c01402500100b1082c1c86042c1c81082d9201080c6800a002032201da000c042c2052180c0162810688042125078400840104450119040caa0710104018081c00361903601000c5007642c3e0309050910040126a00000304104001800081e0112100190741094400000f000340700707024a15080c500103000d0a0b40300c0d4200c642c0c500340b8020440b03941c080e022b01415100c01500075401e0000355001c100c0640c0105018100031140409032840350b031140c0700004140020348000744408041782c81c0410901c1c407450100b00c06140303048114803126500c40001c108440c0c0074a4045003d80311100032a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 638657958 1250 638656708 638656729
    0xb010806091015231008011a090f130f02030114150a08011701020d060b190c020f220504030206102405180901080d091a030f1b03040c0e07020a0b15 65
    0x545c04484030ba1050903243d40054400c1c1a20107100324401000c14038030041d9901e002d0381d907405034803c0d8407410004080c03c080c0c842c040403850344034000c90001c0d2450044000c907842a04a0f021500c00400100028182800d00c02c044603079090600340307030000e035100060500d101800b403480318804c0c101d0141e03892003094042c0e441a41c085103080000e107568243c0140f81e40d1010b188107803080010189020254061404a4842d0740c0291800c002c00e442e1390200009010010501390006032481d1003000907180901c00e0b248554880d40052505081c55203021268038840c5d80070807010516001884109074000c12300d420b064955043c6a40c603110b010b81f56a100c900d0382c0a0940e000020341000289480c0000384c4e03130703017410f011b91202d1403016100c0022149a40c0d20000079108860200007040443d202e01503200d6003c0c014140c008010b40c200214417010743e1041d1010b94910705265414886080c1000c80b0f10780116060004000c0541c40e686c0b0000d1380000103101d808059080c02000e461a01c503004243c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 638659208 1250 638657958 638658029
    0x9060f0c0a060228030e070e0721091a014a0a05010b1810030e0a0b0a0f060602190201140a050304051c1b0c030b010806091015 56
    0x25900c410108002981c1c0c0f05030104e5550004034580c9060000c1406803141a4003d15a4000ba1020703500f4908103043d0004c01400700c41c208407291031041c5402c0030710200500c100c5040c1e100820b19140382d081003058401e190110042c110482c400400200170b03019400c5e92030900044030166818014000030f103004030510b048140c03071010516a0861143d42c080c01a21a00c1590b030104881d90721071103105480e000d0000344000360500591800c84500d4203401c1081c2000091030302003801d040c1084800d06003520380c00e00700c41d224100c40c10300c00f40c0e400d41d0140100488941310200801445e040c0c009580c1c508030f040380c400d83d070385c1c0200034415644a610780307a800048110307501d0b5480c47c04420062842d4000c0390151100e001d06107000107601052480103000c3c20031a0740325802010700c01c0c0c25401070788071417508445101c0c64107070010010708846070540c000c003140409040d00d032400204050070015058a04cc004501d0300c900c400000605407142c0d0151a20f210740c900c0e00000c1c40511001201001c03038030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 638660458 1250 638659208 638659211
    0x3190903020a0e090f0303130206030a0608031b07141e030115080a140703050705060c0102120c090306090105011a1b1605011806020304150c06090c08011109060f0c0a06 74
    0xc203070103401200e03e40c060b807200c5080300c141c1c07240d0f0142d254580c0420760f611314181002c0900f000240c50900e020307540100d400364001404586d06c070100da280d580b10522515034030401e000c03000150582800100001c04102c0c8c0420350801e88240040c5c1c21681c410301d00d040d08000031000c140152000d522482d400c02d175051070b0207100394540e560b40e56078150f01c1030b088a4581450300e0300d000c10038000c1060000ca0f54020b0040640034105410400340d608601d461000710740d400e1201103000540d40c5601400f03900c40c0031030155503818800515080c41401081c0c5103090b0305044c010002080312040c500c184408954070140c0f5040e800d8a5901c050f07080018225040c444c8885e01c1040740c0c03040781e000044840036220300c56510104110361508a0a61085a0250700240300c1080070780300c80c0d444205078804a140403a0255455a600021030b1705008060b1200d009850042c0310024003441aa1118561281c81c10b00300401640014241d1244d400c14500141002c244807034180810000f00c41c1c0c96501c800f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 638661708 1250 638660458 638660479
    0x6020f1c030e0f2107020a0e1f151d09070f0c020301050109230c070303020703030b270a060f12020301060b0d0207020f0d0b0402040c021606030209040509030c0319090302 75
    0x3065440342604184c103034000b04808440c0c407500c3d1060440b00800d9014100e11002d61601e210200d200000502c0c80c40c040d00c110300310414080695010340c0c040e107044070783c503652082154002030030003400010103020700409100d02e96266940301c1505500086500d080101101d0240c000c40c0d0100103d60001c1d01903003010700116100415030042103100d0441c18040c0d4044051301040c581090040d60489941c43e02084040302181c841d80003090384a000b810040f1b41a5004000b1841c0d10724140902152004001c580d41c0b00030301500d0035160007049189050203610b0600c40b00e140002041d1090001c50501141d02c00b00b1520290031010050003143c5900ba1210090310079400650310421040784100c3e2070b225030110a1410050302c5d003415030804402c107090b94469007400002e02254034602e00354407800c0c406030300040104070540c01820a6540250321450700505000566001a121301202e410501c00708800c207800109503410007200c801c00081e000483c0109442103502d9030406904000c3ea000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 638662958 1250 638661708 638661733
    0x3120906020a23151e0708070c02030106030f03051201091a041d0d090f050a0320010306080316051507270b0d020a120525030e03030403020105090706020f1c030e 71
    0x84d005d2085c401d0404141600306030401c0242403c000310b50120214040e500032a010912540e165500302e1703c007600010344680c40c2d0320740356000b9004480840004000084240340301a15036502401415207040134004445200103c01c400f680d8a8150b5009a0381c404503004a0406c40001421520300d0a0907603240485080009141182e03600861801007414500054541442c40040d822030360040071040318651270020450f1b00c1d41401040358101a10341c6000b264a100c00d100400056000d003a080f1151425803500e91700700600d4852280160f076144080010303c9801211803039404d03101e00d0004480007a03803840d4105515180c2c02040c2c01e100040784495a0b9041070b401864075405580301c101200003080314400644e903085400980d22401d0307034a50f0304000c200d607507035004601d01800d010070f140465207400c502e1074000716829401030b07450303400340207480c0b400f401020090a024409010111204548143d90309280049110343c90200c0c0c0608000c94425448130043c5000c07582a68101c006a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 638664208 1250 638662958 638662993
    0xa060504060206160203270a06090f0509130b06030a0f0b18010e0a02040507020304050d0c060e01021b0904150f05070e180609040813080703120906020a23 68
    0x703000d12005445410702140061201410621300240300d50f00071840c0105c202c5916089001d02c2c035554040c05c8500c900203210341e0701c1603205ea01511082d544c2403811450403101460488075036000c03901a15021050005103294104294900354000c0c0c031103142c640303480c80400d1070705c5030016014103070b0f004200c484400c20880400e124007858800e8106d198104000400034221207201e426000b26601c807050020040c1481e0704910741c8842240160723401c00b655800841c40d04c0407040d0080b20b1070784050720b050040540080d106a40040d0030b00c000c003800c81100d48108509180f00c00e00364400c50760000010104200b211046280c01c50a060501c8040c40003c417240107001c081e1288008100080249441401c0c0354540321041c103880b0840400a403a8181442504600903005a807402810040070340c0b140850300490707008007048401802d8003480c500b040c5102c043c0001040c0c0420910003401c02c01c0c160300281c00070b085900088200038100d06400d461020303061aa110210070301803407804445c0c0a034403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 638665458 1250 638664208 638664217
    0x2062a28080304080c160b0a12060605030f04061b0c0203070b030f3402060403020c09090a170906040b0715060e28151a0723010216080a180510050a0504050a0605 71
    0xf0341d02d441c607100500000e01c2702030b40d516008006c00503105000003000d081502400542181c080e9400184a0050600001c0344000c94540c083c04144148005804c504040040c10004c00320112031034103504040031000b0301c004020b8060134061400010032007454140700040c2d14180006440c9070490311512a0181d12180100d4080e80036010f0582d00d07a0311414102d109030302c5981d2003400b8240303909c00d5607142001c100c041c1c24503206d02d100901400d0030b9511102c0040001c3d01200c0d003e15166805882d01c905c0c40131030910a282d02c00e050410400140c07032800d841a8021038141040d406584285202c0e007174030641086a010814185450142da0003019028081030700c841040c4806400c8007800007007010320030340320018103281c110044507010b90b40500094000031030900c0054036001c2e20200c00d095044409a06442001740051101085600724040d44803040041d1a58252a0320340400100c502400c40c0051092100002e244452184200e040f5009460024003824900740c40c1e6100070120f402 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 638666708 1250 638665458 638665477
    0x906011125140a030816110a080601150504060210020705010f1b02010c02010e03121306061d01090b0a14040e10050105030c0d0b0402062a28080304080c160b 69
    0x22041d20381010b041a403c1107003a00d070048901d610740080d696000202c0e0f04034100554420300c1ca04090181943c840c00c0400081130f0241c0108400e504100d1914000c0702c0051040c0207210080004205054000c01c44007002031564000586603c0c1c0c6041642c0902101c503080d00a20b031a000400401c2e13000701841c2c0e2441000381c1d000700b04a030240c00d8260f080300c5150150034610303801408810100c58440948590050342c0a580041d0703071102c0c0d0b94141c02e4544c1e039000318110440b036150b030b601e5503401e501e805401003080110501950001e80c01107100b0601d1402041c1000c8500f0501c2c01c80b5441d1078002c0800c2a00318422290100d804001401c0107003004c0c02194800d020703c0300440380503e0100416041e05803c14403100c5103072a0b5a0800c091036000b100e030340340340115600c00c452040e1480750441d040c0d0402000985403080c008020f0198074141c610410109501800510021421a038262980103500070b40240d90b176145046420701c3c000c83c0c0f42000c05d803072403850300203c0c625851324040c0c0410761 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 638667958 1250 638666708 638666729
    0x2091215010906032102010605030303040807200105070b09010e030406030603050c010c0b070e0d23120f040b090f0904151b08060f010c171201140906011125 69
    0x980b298451015034006201c003030800e4054202032041303500e0103408012000e07118000000c000381e035140803908580048038140c9100f000820841c1c248049400e10030911307080e954400983c030f0316000018205018600f005041e80c0031541c0090b207990025808403035040c0c10135084a441e6562000c0040180c0350901007201c6034040c0c0381d0041c1a07075015003031203448240d00400540e200c0e502c0560403034121004c800002d80c0041c8a582e12004945039245030604100c1015000c4051140e0113070152418500000404a2280400480c0c1d94030032000c00b501c090f039030034a01c010b5450314084001036110000340f00d0584d0108542d000d01c030401009075000315134449184005c3c8110302804284914401c64118080045401000001c1c03030703480c0c150904000880d05040a9600c0c408940300c1d2540c008144c64030381840900052407614081440068600601515608840700001000864030010b00a00181e041c40f50303440c000200e080d000e10034190741541d15050305801a154020301403030b000591044c0c05808 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 638669064 1106 638667958 638667961
    0x10c12111222210c030914120105010602031b01090c150309052a0306060d120c211b020a1406070503041d13050a06050a02091215 57
    0xd8024102040500c02100a503c1c14600703026910040c4600031940c040025070040424041e50020710b10000c28130344000100e0a42c00d80e41c21500195424000045820b40d400005030031410300d040306000c42650506c6581d82224030f036240281a400c640c010034000361140d410358070f042c0b10945c6400642c0603004d85909007066428003603c41508144000d2428000011544032100c08089003e41214213202c40020010a01140018603014402022560a501540e40c1d0020180c001c0f2038124018042102061410702c105032242c08540d04038260502d04050780481b201b210f9020b0030440443d41040c0c580c0d00300700301c0d00d10101d82c41181000315000058046c03020344010408202c01e068a0341401240510802006201c0040c0c0703120302d4905404203100245400c00da6412003c00510342c1c0300c0041b0030003c0d01c02c034070320300340c01c03605920501c2c548090001e001c0c81c029808078a0080e86 = true := by decide +kernel

theorem cover : BRFrame.Cov 638489208 638669064 := by
  have h0 := BRFrame.cov_init 638489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 638489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 638489208 ≤ n) (h2 : n < 638669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
