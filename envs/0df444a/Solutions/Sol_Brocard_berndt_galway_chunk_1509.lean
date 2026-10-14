-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1509
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:18:58.593333+00:00
-- url     : https://prove2.me/submissions/b7be09af-2185-4fe3-ad9f-4f44edffa8aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 271223021 ≤ n < 271402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 271224271 1250 271223021 271223027
    0x7051903110109081b0706080c0c0a06060b040510050406020a02040e0f01050c190c0b01030b0915240613050f130905011413121b08070f05010506040b03030301090b0d0c06 75
    0x128000c410f500c0f840b0400ca060170010390b560342c0d981c0b04810125a00b0070000e91080c0b80c10000c0e003034008080302594195805555000200d4a081c2c001441040c0701007030038000742c101080644240d07666800d10924103402c1880c041c0d40e9802d161002442661078122a464100f0b043c810405d200100314001c1c081d42c100229000f103e034020741d40401c4603036203189019170480c2c410401c1307900e140e0b0002088000381e400c40d01c4080140c1e400620981c070500c5598003600524141c0840c40b071040c1d03120009400e42c0307210300a00310103500360501d0440c80f45006100d421307040040750181008480040790a45810810760340400d6148500440a05c06035151030351940a00106410840600401700d10801c600da80e02201020b132040c500704003134020f044031004a00c4441c0205020001c0e140000300000402c4030540d42c0c49995440a58102c0e04506068401e40810500f4061a074000320200c40c01c0c40480108004a5607a010500c2285030990302e80031a03003000d0b1144920f1010203a000305c00c0c10702c12501e0741005 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 271225521 1250 271224271 271224277
    0x61821080a121104062705030708060105010212030c0a030b040e120910020609120a09170a0c0f1a0306040f05040503071a100509070e031b040b04020705190311010908 73
    0x3481c00581400203075241c6007403c4044805407401d54940c94058648080f281c0075112480700b606000f080e4900f40030895940401c184401008884010200396062000090422401402003aa2900180184a4440440b505030340d503d141603e070002c0d0911103400024060f1485211400e2075000b50082490380b01c0ca554014888114142c079403628510340d03500101d980d040d089660428641003942241120302500c8000c018aa0342031600030140c685400c201080007031450751421700b0740e02c8003641808021040d120031000b0110141e00350a610b24084004041c0441251807001c1d0300d000100241c080d94865010b616043c60b810000c00280c9014646180d40394402c0784240e8034030440c000c102185d03201141c200b52190351509901c204c85490041030143c0a4030103080d1409000350000d034402070751400c0009208010000d012690030302c0401c0244000c6501500200d070140b8010040c1c0740116000044c1c403501603c00b075900107100320701e81c142111480d03002da00888442d42412034132010700c0200340c00303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 271226771 1250 271225521 271225547
    0x11b0203090102070b16081305060d02030421050901050a02011404050c0306091b060906091203180904080304140307050d090311011803060b0d0b100f061821080a 71
    0x1312101d040c3c07100311a8145000d108010441d108058240c03000083d001d1014049030142010304841c1d8503103880020314942c11803644140c0300d55011003000107000407400d444841d21218030030580381c2e022040d00140709115180905042c4071000581d440194800d5001c41c06041c00c0c6484552907042a140043d2200c0541c00300500c07a10850003c82d07074022010a0703000070005c4080c261000c141104081c454140c100300c410030f034010000d10200000e61140d0640c0d20007250510040e542e6032102d06c801d400c0c450610602d490050400400300800501e40324200c0744c0154010f05a00c01da08061100540355202c0c0002c001c0284c0140307151013240c075411540d80f4091340d00c101c400d80d01c180405801140ca100d00504030407d40303007503c1c40c2040484e01d1640641d101040c041c00c4040b076510251604c400000d002c0d1000d10500320000000c0107800f2121011401821071460441e150b01c0c0c1c0c100402e8581c40e1980503080d18411010350b89130b5103a80480a443e0510ba000c50f04036103c0c03002480c060105400c04c15 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 271228021 1250 271226771 271226773
    0x302040905031b06090c010f0c0510051b09150702040908070f0b0c0f1c061211030d080601080a0e070f090203060406090605010c030509180f19050f06010c05011b0203090102 76
    0x80c076641c2d100403d21314442e0b000b0303400074041004070400459029040a9507e82441540e2400ca00070640500c4103101000703020303202003854102201c491000601c0032600c12000d00060250704549e0356841d0f40340103210001c0715802d885504500000c0e00501802c080203201030030000d030340e10402409000e15400d09005140721700c1181c2d18148044041d210f00124015004d008020b07a40c010300c40e5429420640201650025000d5101c01064a0010310300c1010344007140c05011500062408011401202c40c442c90f10741c0300e038200140068001140036202800158031030315007a454141c10440c03017008210000340380203215680c0200400a5205443d003a0107a030424001107030101c000d00412045500603960220326030b0154804544981000d2151640494502110a82c49564102e40340c00365050060b01d400904148045045469143c0c17003290b442400c1c07400704940a504034030040da1152007801d010103110034625043e40144095112407111044807121407240d182d002000d07246040081e0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 271229271 1250 271228021 271228057
    0x603050408311e0605071109070302040e09010605090417090603180c01110616050405060d0605101103181315061106040b070507021903080a09120b0f10030204090503 73
    0x80d0300e06100b2010f094080030b040071031010040d20703100c2d01c020200c0c4c60003031002c001030300d0201002130351040f41900c00c000001d4000c40d00340490740360042e1045c1c04c01c10410080010a00e0324000c20f80c640b000600152030700740d501c032071040500c21307800840b50010390040c642ca40e245014250560803040551011103607101d440d440a495500aa1101c12094840d000801c46a62807195100c4410b03104c0c207030f6034108802440000380c03544030480a403800e14512140820b52908110901801d64013101d10641084460744c42e001a4000100032110889030342103a45500581140104001080c00e048081d031042c03601c80c03d24010410100c07032400f0344004c2d9031024034100040b40c54a548a0081d88c0c00f03040c0034072440200703220718000d00060800c541b01500003052000040031650040035658000e464520000541014480d4481c140e40701501d212061100c03102c9041d10303015211480200340061000300d10b0040307940005100243c2c4000c50340100306108400c0d00b4a016901d0f40c008503010140b0b00650 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 271230521 1250 271229271 271229279
    0xc11070f1703070209061318060504330203060f0909061603140f040c0305071e09060803071b080703150509070501020d0e0105120a0c0f03060f060305040831 69
    0x8000c0f520341d950010700d1000f00d629444100114070000380c40e89491240d5400b0329110500515a9a2041d680181c000190314030306401e0100d45503004500300500c3ea064203100f0310020080550924030f03c03205180058803503552902044a0310747c4562000e034040304000402c00103180001f0520320405065000074190380340008203809039a0190a8504034400110000d050320104001a13a03120b801550f0910a01e6926101c140c03c0c1241a00180c5002210307042490320002d4052540000704408401001a540b5064030359440b4000c100000344455164409210807040d001881d8000e45224001c0e034184d1503603423404081180d0490f107520840b60410000404401d40401c10700219281a005803810719170411003100c0d10055000801d040c4001413003c0d04055505104c0544500409000054020380d40740700075000390702d06081041003500b001d0302401707e0344030340c0406d01c11228242400310f0300d91a01e20b405d4100e8003d004242000c03240160b280003a00903100c10f5544903030f180c14040380005442d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 271231771 1250 271230521 271230523
    0x2040b040209060403111513060201061208030c0c0a05010f0b01140315090c0f030a0b12010912050903120a03050708010806040206030105061c140a0f0b090105040c11070f17 76
    0x7858030b032603403240c0700b44010800b00d21441960300345007200414843e85000d000800c04100d401010306001040d0803800d045c004290244141c4029045500114a032a0603d542ea20a9848018014000f21320003282107808035004001d03c1400c00e511000a11042d80c2d480c0043c00141401c010003800203140c0803000c2c54441416003201d0080c01603140b0f2100e400d00900500c05506d1028003e00c0007400c0404c0301001c4228001c000e540500b100002c041b4058104108201d5100d441e6003d0040d1a490a41c0010014880700000d0715403c116050458a8092060000342010103c400800002c203001400011081d4581c1c042407007801c05445014007030340c131042400c4c0e46c1d000071500250007581c2000180010719166014080e83d4048407043c803048080650414240e500a0f04103c2061418134140641a803c5003c1e032a071003138a1420421035642107000240104c0010300c81c00c1e02a07651101030900d41d034840c1402003654040d01c801c6030040c2c1c0c1c0e1444400c143e02c020380710382c1e02542c0b10210132482c4110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 271233021 1250 271231771 271231777
    0x60806030309010f090315050105040c0302162003010203150301240e1308070506090d03020c06040f03030e0316050106050108040302210c011d0714010f030905100905010902040b0402 80
    0x180c010340c1400007100064400481140760203090105081300003000600c000c201d800c10303049108003c5841e514142c2480300740c3e004904007800f0716006004c0c1486107441e40030030908203600441c3c4842c0ea01009107103203c0100c041c455013901540000200004203040c03412424112070168020090441d040c01460403804407882e403c001d814548108103d8041c80e580300324ac0010007401d00d04d12000e00c50740c812540c0c2e8030020302168240c10800412201d10b9081c000c0c8500900b04c0d08084d0718207040000c940b0785410700200020219000c214140742454469401116480f10160807690384144543d035011a031181c1407c112038030b40c03e040c400701c3c0035489032503003a0046034180c00800c0361030444a5080c010321a041894405060b0500500d1003400c401d020303817032030b4681125142036030000b1200040e09000168001d14040c42d420030075007000b0f9078486d5443d0a40046881d0000baa0042480c5c15410450101038107642d09007002c804106100040d40100001482118100868066403061000f680 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 271234271 1250 271233021 271233031
    0x3070b0c061603022107090905060607150f050403180614090d020f1903030908070f1502031204030521010b0a03020c0102041d1008010501030b0a0207060b0a090e01060608 75
    0x3400000108011640002c54160b464240307050240c1080403e2000d42c0c00107048140395044000e13080140040e0541200d4104081c04400300d05208515000c07001c501c040c40b030010000d03c1710141c203a24503d40b4981c0e90000c1114003c1c0c070401c0c803150070720381401019000c1d18903030403011032484400003c03001e002c1c10780304e8010031540c89128240031825003001606c0c036116000b680c11401c44124402d942c0d962803081e5100c0b01c00c01e8584003041e800d5080003000405140c000000340d500810042c0400c684002c18a412668200705107000011596801c9041d030041c200e101800c13a40c110107001c10142c11401038424002002515014286529001008000d0038400c1c494580c208105c80444244070750001d00b0040b05803070000d0318007961a40c0c0b010030130010040700c91542084d5802d1001031410250000c009140450081c0036650454841300450b803005407d1504643c1d000882c84100402600500480c13100202031641107503441900d20040c00c0501d024a2255181c240c0c0070498901070a0118054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 271235521 1250 271234271 271234273
    0x80c09010c02040902061308100f09021e010504080d030c030506010f0f0809030c06091e0a03080106030b0a0e161b080d0c03020f040602030c10140f04030905040908040503070b0c 78
    0x103041074007840000c010002051b0f803c035208000c4100c414154518503401071400000906400581034403010407600180507107440503041c00314440c050390341d00740181e0502000e2001c80342c401c3c05403030040e100c0c0d10641d401040b003401183c1c00d0360b2005070507500c2141000300c075440510289c0d580d44011100c118640ba41c40000c80c5500003c100c440b40308000b082e610a007864102e81c54a0040c01019161460482e14856a41c0c401103038117510380d822001d0300d2012214000281071603410342d50003820b401014040e80b420169159000c0d031581c1d640c21000c00007003040400083c0c6070704181a100154210300c01d04d41c00031902e400640180782c00556441c00c00d19800c90b0311a130500000402d140041c10a4061010405409002c03910380b092410006100414154004640d14802a20414208982c200a41405500c4c10344480004400b9001e100d034829107405800c006962140340550f1001640c2c0c0101741c01501e843c5070a402c100c2c07007100601c15603008404880800783e03680c004807120320890403d5265 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 271236771 1250 271235521 271235537
    0x714070b04030c170c0601030516180c0201060308030f1b1305040207020d12090f0803031006050c070308133012270e060a060203090d032607080c0901 66
    0x12901c0b403120000c0c030622403d1440301805120300d13020321a400030301c10401e0743e4219030f004100b0090f0070404a2030324607103079480e0003180b071403e0300e17000b04040c0d0782c42c000c05e0780c40e290785460852610070340c40a800f4540c030001c1c0d00c1c0c9074205819440803441c8204e4203c504101c8952038420f041c40890183c03454002d0070700d4101c082c1030030501071002079005168126008100c8001c0c03e000100c01c2c0384014011880d540e00c424140c1c0c98201c141c060440f031980200c0003034000b04140944100402c0708141a04c0081c10040e95400402c00c3d49480d01c3d4103648082c001400201e040321079000d034888020200c03142c1d07132042100320542c0c40c40405000600f8072000030000007000f08000040c3c0d2040c60074841005030600c070401c1c07000700c1d00c2c000d00e00c1d05049403c00c02c684022028001c0143c2045c1080e0444019550203000a087c140007a540e032048010b0144030340a0000702d01c0800d4800c07680005011441c2007038080400c2c01209100203200c0c180d074603402042d07500d800a004041d036403040d908001b81c141c1d2102c80d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 271238021 1250 271236771 271236773
    0x20606010c0b0a020904060e09011e020c0705090c0d0e010605130204080a110d06060e060103060909020f130b0607050c1005032a0405100e0f030703050312090307020d0503030714070b04 81
    0x70096005c00440780c0c03c203848620015000074100e42081c418204c0400104a942114007070400e8510b02c0c1010b483d80920612044102d503200148420030740e40d007a036441156071503180ca0f01209000381c10160340880c0c01e02280d14040c40064104804465096850201c00c1c1c1d0f0141c0d1200590155014006440d40f082d5255030100c1d501030411a4440c0c07005d001455591b415440740410f54207181c00c001d06800400c41800b81650b8940f00740d80080502500030010401a603000486121010500078802c8030800300c0503444140d680d2240301d03200001442150b803880c00b407416545914100181e03500c00c105074800104603d0145045921440040104941e00e07280c2c150180b000b1211000050104034040c8400318140d11608002d4001405589415101c04010020061681c4209207180e01a4020703200070000120004165200d864220301418035554413039100600d0b601034508040d5010503001e02c85001c2c03000210095000f03c0d8240e0b03c040c0120850001702c545803141c25401001c04a00c031000134 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 271239271 1250 271238021 271238041
    0x60f0e040906020412060207030e060909041101020f07080a0203060c03061005070c090c0512010501051602040203060d050d1e02070605041205120408010c090510090509090f010f0c020606010c0b 85
    0x710502d11420300142002d03228816405d502d51041c00403940305038006114803e041e044007111203030b0b00b411034000d49020103901c0841c00350840035100400002c0300049040c1162f009018950001c0181070803140403a5940c550349070390303c20611051340a401000c01040c801844a0222889004050310041e65410300c1d0104494a521a1400381c441c4004154040340d44e2030300f0b00605002407000d80c1d0b8a0f8642c806641d0203000b000c810b034401030500404010720b44074003400c0c1448a41c1c1c10b40442d401030700d07135841d40e02050100c061840e0050841c0564803902c1019070300050b44038064107480309103c500740d0200e171040c0d0f9200000e008500215100b0310081180000a00050401c3c0e80b050f015210000901d00220388141c00c9504002d41c946d44601c1c91042c80d13076100c40144000c3c42c2c00c03030707809080b0001f40d4000380005015000f0b03180200b540d50009030741240b0410201c410844d03208002c00404511018200c000c11001c440417005010701c401143c000e622810381424559004000201c55480c0e90040c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 271240521 1250 271239271 271239281
    0xa0e0c0111010212250e0102060109021606050a020705060f0402010203030105041d0a26040e0c0c120307030b01080f0f2e080a020a060c0b010e130501090c050109060f0e04 75
    0x200740990740030807451081041980d12240900700041c066a411500f80c190a01c410103840c40e83d00420140300c0322201c1503a400503100381102c0c4110001699080381000f6061b01d400145805001d8a00300001c3c0203a41e21194002c1103541c0c01403040d01c1039921000c0301c1d24090301d0305640c0a80142d00a1005209518060b400640511a544010f03c211107002c003101341481205842650b0108003000c01000054480a941d8007420741c6112240c039081c14800d010901d40d0011f0300e4500341c414042441e03400d00008104041d400401c00c0f00c51380e200d10703001d0b500501600e180503545000600c80300101710286440302c000f9008040060303018211b5135503186084080c140da4494501c1c060000c0d4041a03086803004641005001d41c800582180a401d006204081c0c0d0a5400201080381000154003c21660103038907065400d8080580d060392501102052941041e1a0103071442d480c1c507090070204880c80c0c88500855000f030722402d032040d0b41d541040c1d070300008a0714603034081010354020003c5840c055110b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 271241771 1250 271240521 271240547
    0x1203040e0a020d0c090302011d01020a0f08070516031a01030201080601031a0d030203040e01060c1a04050a08030108030a021005060112050c0708070804090e0d050a1209020301050705120a0e0c01 85
    0x700606240790310300c1d45402d440b003011010010402c958024030070365a04c203c90802c54101d548210350881c168400003135a81c3d2940d8405000901014400c10402451a08860074250090100c4c3c0d5083c054001420140307080303110072150030f4440075604807030500f000751842c1240e030140c4035412980e0301e941c01540604000e0803075440d0801c01c0100503203da500c0c0800c070360b60940280d00850b101e03801c10486403440307001031700290301344015100702400043c0a1450011214941c440750011501c8614285203000d14002000b000d482d8048004215184e0020141400e05456802c550181b030b1207818080440d141500c4050000c0c80b418117004070015240c00103900301500001c018540200d03522a1a06900700401c2240d000c0c46c0054104640d5895001c0ca45034150050040d00315030a400c4400340030703031140c40b0102040c8280551408280d200c10f0f480303040c015401078000d0140d4038201800500b16030100240d00704200705078001c0b0f0300c00d01051248401d00241c60006161120309000199041d100f2889 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 271243021 1250 271241771 271241791
    0x1407030210030902010e0f060702010c21030902040b0906130902010516051e071d0a18080915070c090905030d09030e011724030109080708090901051203040e 69
    0x40020058039190405802038031259000030780369540c1d00c001004071413584240ca01c04c0c0c49500c00490300356207640455128981c2400c20b24561003ca207020312080300c010000741c3e40100044d0300d40d0a001d80680103288654400c85040000305070380010410421001e540840d001204480361040881d0307180e100c800c11a0050404605001c401542e181006200c001c084a054001d1001d5001011341c810404884103030050260074102c0c20089080713400303410510380d540a1485a0f0210b204411a80d10800e440f1740781940d407100c060740b1030510100c507510008c1981e00809415500303803040e41550381940d9a07694409003d5240501e02001d001c05014001e00c1600d40d40010440c150b440d500ea480707800c040038481d031607041c582c01081c9e002403d0100d44181e075001440c400000c100342c00042c450b00c24206c1505200c640b11500910020a00401c00c1540051041c00c0000388102480b010201800c070360701c0c0803107008200360303201d40a00820421801b88507207a54000d2105003d03120740841d81643c0b10044107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 271244271 1250 271243021 271243033
    0x30709051002010902030a0f060b0102030304080306091806090d09050a23220621050a0f080415020c0909070f09020304060902060d0c0212030105030a082217071d0414 73
    0x40c00207400c0c0340078007c0c2100c03060006540541001507a000d000344131310090020750704624061303d45400d42c1c0b0008102d14800c60505000034080001c08040300840310b07903101203078400c2c60298980d9941c1d03410310090101145500b04000392a20b4818040d5080e0381c0e0f0070f01c01d5000404034095a110f03030a07048065076072124070710020554210070b00b0024206a0019130011400c10303c0d2010904410000c054034000c6c403800090f203040441d50005030701c9640d580c0b0551250491256050844c21400307160030651811080c000c0c4000139550008155202244c05c0384d0348074240d214028101c3c1c1ea01064031541d01480e035104000c001032a41503000d1640140181070112344076601e680015515884040302c0145150380d100200b80c4258108904440210582401031565060800003907441101c040c008000308400580414a021100c940900280000030801c46482d2610b810040b20100d81c120441c0b18421070000085082e0034807a5542c00d6424a000c0086a4a5940b00e101c50040d00c03032038030782c2148114 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 271245521 1250 271244271 271244273
    0xd0903060f110c100606020d050304020628030204030c050f0d03140c2a0d050c040917030403020607110a1106160f06050a0e01200a181404110307090510020109 70
    0xb0500414040d62003c014080704420030b0070000880c3c069030003105c1198003108520040b2508481202c0e001901100c0c41500ca101c41c00f203255041c0150303900f0039445280e2100b4000f5158064000e0015a441100d0843d0115115002d008810b9079051100c0d0384480341d5400c140c0407a002d180e0000082d0240078240380307000411014645400c420002d40402d850042503200054005828141c0510004031100e104030f0640392134543d5200009070701184280c1d40d8020000401030140540b18210340000c6101e40c8030714050070041d4070b4030703001c0350700070301103104070b060400340240c0400e442c2150703a4010182e030001440d0000b0f00c100c40e0041210749094010407003030140841c104007402410385204000c040740ba40350448129080e584c0041c207406c03007607040802442140c0442c0f01e85c19900c100c0b400340302d40c41c3c0003107041c00c8908020422103c142600104400310b00c40d044152114003000d8282e0302840a402c42400710340452004490010005011090501141c0380800d03044031a03203164800401c0c41d00359 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 271246771 1250 271245521 271245551
    0x3020a0912200103051303051303060516080705071a040804080307060e01240b2101080309010315120221120403170c0304270504030203070b090d0903060f 68
    0x112040664031000b0042801c07420340c807200001d644550003868244402e0605168040704008240c0d0018188040401c01b002c0007a880b00e0038000540d0003400901103414003072890f030b0f51050f0094210002501a10002e40700600510132503940c0c80e407008040b80a01032181e0010021100a402103880c2d08041100241c1e9420030809050124001c210000c0ca0009600d107460171035107040541010b030006240140c10000c40710803680111008100115540e00e80300109441604000d2645101e48100400210b10508000007810b58101c0c280c90800035512071450030041e500f014821118245220715102c401030400391404103a00c03d1500a4441c014124032035603050448801c40d4800d10f40003c0ba040051290700084203081500f14044a0302d045440664140c8070310880c05003800301c4000a00d40e44002c1c80c044901603080b030340c02d50100040d040918000f17440380d120403c141ca040802d4000300d502180c002c12a0188544240ca805e1040c91a560319400905501041031703034069680c483c1c407110501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 271248021 1250 271246771 271246799
    0x90f0609051e060601091e1205100b01080103110120030423040c0e06070302030408070e19140112020310050c070c0f05030304140d0f142103040303020a09 68
    0x2115030064031154034821070003461142c1d80388240b0391541c440000c1c0440c6903003005040060341d04404031840a050504802c1b04100c0980e4044066030f202d0148000c10b02901280e45541d60b201c4c80c40520081030b80c2d00044a0f6614280000741a008034109410700942c02103d00640c09801e01d0401d041c54045040e034581103403c190f00034407440d1a001c0e40c5090b00d585003110342140c2201281d0402c00e4004000006000880b42c4030343c1d80c02050000791560505000b0400c0e1402040130008580b0034645840c01461440b105540850030307201041c149451420300c82c003403110503180c10480100503030f203807180b8070960700e044004c181d03018021034025020b0303000c580c043c513449080c584482d25940c50705da151001c0b60b001294401080981f1241c0c05000a980c0801200c0440d00a04036200c1c4031914000000e10400c01c00d01d0081403c0b506010384401c00c10520006800c1084800c20703140a42c1c00414880140041c640011142310340810004001a000b54094071580d862440c00e148960384800042080720 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 271249271 1250 271248021 271248023
    0x209090706030b01020a0c05010c051203070314060d020312030a1103010311010206060a15050a03020c1009021005130911070b0a0b040f0605010c0b04030e031f0e0304030c09090f0609 80
    0x500040024800d29425001d403100b10802072000b03001e006c02e0b945507100300301303c80c2c0281c0d410480040c580a00f40070b800c000d501c00c883c00710984142ea9080665010380102203c544505429100000080440c41e1081c07403050190303005400b03407141d409245603003035035540018842084680d503a0714840042c00d591002d1800f951103400a412031a8400c80068a4071500808191290090324000d0208045409503442e03801e10605080d9140c3c2c0326840b05802900621040c50480d2145d5102d40380340c003049400a48a4500a0b1029414103179401d8007103c0b14400c0141260b51515011410004c104080d400144440e800480b01c2e030070180d090f130740d5a1090505441d42943c440d115000c0e0b003040d2819103d00680610841c07801c0044a01c0c00d00080c01c022004a0080d103218050000502854060340317440200759402416520b00003107545414018060598031028441d1070303e174000100074400022142540d41180b4072100c0d0514000e5480d001d080c0c00d1100303d07900c15038a8041400100306005103000c003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 271250521 1250 271249271 271249273
    0x4060506061c060e0a0203090a110d350c031c1b0513092a090816060206090d090b0c010b0303030a0209090f0411010318021008010609060507031416020909 68
    0x2501c0d0403840c4c1c90190002c4d2180000c144100284000c0002c001402000d0550000d00b4500b403a01030310000f00407204016002d0505404011122a01011510400940f1104806140c11361102011511690003144a4028654000c0000068803102a00c230a0226480103201140c405244d840500700c201d4442c2c0d0703120208a0214a18002155152004c8060998500d0801000d20a5238580030846008200c01a01d2104101804c0e94244581c03011805070603043c040b50001d43d11140240802480da215020040c029140456019100850950411100b40d030700c59207003a0400c202a100365111050b0480d040d0b690b80c0000116880500145105119104006840745624010f100d1416001480d101d000300c0b503201040001280500700004000d402e00c0d0005088041c1081c1d284401e002c08000782d0b008210205102c43c041e4000c0807607059480c6a51008003c680e07440e030651307040c010960000c0c08600c00c03504c104008072105000c2d0401c0c60140a030f034540c4003050b80105003102c8080e2511461 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 271251771 1250 271250521 271250531
    0x906120a0503070809090c07020906060304031b0b2409460c051905091c080306040605030a0b07051c0216032601090c02031c141e04060506061c 63
    0x20a00e030112002e070380035601c400012328141040e8006010900014202e0303101c0c80011011800789171003070044034011240169400031446450520303c003114011600d0110b4030101d60341c4070000083d1a1014580e04401030404002501c2d01c0c01d9104801c44120001e43c2e030005001413103c0e080c0348030422000d91030883e25040607106c98014005080e01c010b01000070070300c881041500c600840c1418400206100c0c1d1510585550207800000d4000c01250380d0401ca0303080740382e0000280514100114041e0750304850401425940da010302d6180e020041014100030381c40000112018010350040404101c80e80003c15211403c00300b001c126003210101c01030792009501c1c0c0b5410150011082d6071994000c10320740d131200da040d00d160041d100c414010400b141c1d40f80c090f0680304074003c100b954551202c0003180d0300402d001ea0000c0004100c011740034004204020045400034040c0401210f201300e402001c02c149903126151000688000790801740c20060030000400c0c44108810703e00d190528440340868 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 271253021 1250 271251771 271251787
    0xa0c051501030b0a0516140904090b0121030c03080a09140f010507031505060f0c19150603020d081305060412200f101202131706060906120a05030708 66
    0x8290f0900070040854a807800040c061441e080390340344c01c6001c02501d0840340c407a283c00307058007d40c000d103c1401d4005003070070b40a004000071515118140d52841d40d0707940c034003480c104c4a49403262084001602148000408602280c032614249a2140041c4004547c9401e140d44041000a0407106158039412100850148500a02403d40c02c805540380900c041004904000390b1080b07288504c034408c1e10b000940e000040c080d0f00a1b602076192060964038051000301010b903803001a04011101040100b4483c0c25a64480c0704260550740c01804254004040e40c0c0c808110b94044d48a01d03000ca5030200d0001102d645400042001d009031807400f4003821140d140001c8081070615103101c1d9503000c1d218040c029290751040020b04502224107110807640c20301c0c15198001034120305044c0c24000100524095013408001c01110350494007540c840303070108a40384d03c0d22016628540d0203048000401c010f80340400c040956496104141e4024841d540d0f11fa900d180d1200804461011020960390 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 271254271 1250 271253021 271253033
    0x2307080408012f0a0c0c0605070c0f06120218030a060b1e062a060115090e06010e091e040b010e010b130b030a180f06060b04030b0c0a0c05150103 64
    0x60307a04a0200f6181c80030400c4005101d41603801078507101200c41011908215052061031110034250700800380d0362007140ca03944001c1481e03006100c1a9425410302c0400502010341400c0d540c112407107540c903a2840b951001550300654800c18142c2c001e070b0b008522246155030240912000039109041c0081c1b1440084148555142243c81d15030340c41825211120a03925044116142000d07040f0110071601d01501c0100010040e0000f0603a261289030700200e251010000582c400c425681c4075100400e94900041d078000b03601702d41442c0002d91100b000d81c1503082060303445401000c540341c807240030343c0f80a15803618148121029280000002c00400000094416a50260040e1801c0e9071420315891840f9104002074804c2d59510790f00080081c461a82c950b0042c401b201c208013009620788000d0400c0c10101d01d480c070003a6440c6141150006182d00341400310b0f02203a901c40700030036060341c95941e501695008081c03d00c051140c00756200c40019824085001c071014540007803100d035410340c1000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 271255521 1250 271254271 271254281
    0x7050906161a01090e010b06120405010603050a110414060d1b0909030305060f040504052a09010b0703020c090105010c0201030207020a0504050c030a0506010201090f2003010204090e010e0a0210230708040801 91
    0x174071a0345450503d0041d03880300c104854800c402d881d24a2a42c0e16246801801407620f40d0018103075004031a04542004603a003c10b505100040b1014860808444100602088180d414070b030300c1994100813a00040c40b42640710502480c0000e200043c6940b00111700c144c2d4040718080f000a03036030307004100c1c00d0f1034100d202c00441103040c0c60401482c542a87ca1a075a200e1041c1c944400304a0b0b1004494010105640709100b914003400364400340d6550761031054141c111901c110050302503607402240d541003044045040f2107050750f5a580c080345540055000394420316080e07811014416000c1000d8686001d41d5016040e0301c0315081e0307680b41041c0000700310b0360090012411a41400340c10008610451401d1401640045480d05081f03503020300c5850041c400c0301503580550000ca40042c41103a030352b0110081011030350080c403280d1f5030051043d40f5010300100003075021000307442d0210050310462209013149480002c1c501c070403030100200380480e00a61400c4500110000341401100000e02031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 271256771 1250 271255521 271255541
    0xd030c12091706010b040323010609022503050a050a12060807051003060303090515070209070503010f050f280308040f05130b18061c060b09070807050906161a0109 72
    0x83c00d040d504002d02e07000103104a2001900d4014100c844841c2149040f544c04482c1c4060b100070040544d68101e940007130b4020b1a0070405001e00000f13901c8ea15035a84050810490f8195101460300040c40401c0d274168124040460030440140b95514075902640b00d00c4010b0f12802008000282c9484104484203602c81008410941802c400f040080d800051080903074004a0b40101441503071040040329000b5800042d50044250003840001504440258140c4004bc14144600da40782c1080c8650b030b0300100b968a4004d54000310000c807070494030131130001004002885694059598641d640141c020350401c008940d441e0b002081280751007000310703c5000d400c501c144000f50300030001418400300c20300004110181100061101d07500c2620f460030005851503800780b042c0751806c0c501c004119110400d0301482e41080813074400340c0076503003c42c46200d09984007880c00c00441c00348a01500f00d007040900e080800c041d0349000511420240401c240c184508644079890200c0e02c1094400a0b65 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 271258021 1250 271256771 271256773
    0x31201061403070309020d0503070f020a0602030405062709040507060f08070f1101110c10050f04020a170309060d0203072c3a03080717060d030c120917 67
    0x410402114a00030b0300d92004040c01c00058641c001c0c00442c1214910030002880c90000140f42410410803c603008030140c004d07105ca0705c40300d8560f042a0303604c1c431403401480d900c550b0600081c0b082650003405141042c0704005550701890b0240301084c04408151401c4403da009100140103035a03114a50548800003072134601c080d0708001d6030140c401007860004204011511400f14943c007000d42004c108003000d000c030240c1d25001e03210b0454555511380b00c100e610740e05100100315031004002106000303580040004844510340a02c0248200190401018500003480034000a40d200f0000c3c00c0d55849000d000f50303aa143c880380c0100140071428003001d4004200070800c02030a040c1c02440c1040405440625901c070001070006030000494512003e540c071450014255030070309003010b40502d882601d6150542c1c0f9824003d54075048060003983e5101c2050340000d502c0d280c58400a81a070b4000d0402c0c2507c0c4c3c001c0c0d180e042c1d810782c680003050049003034444204420000e000300303485540b440070 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 271259271 1250 271258021 271258037
    0x50102040503070303082e0b07210908060c03060105270607030c02010e0a06120b01030209040905070315051501050d0209040501060f090602010204081209060408030706060311061206060d0e0105010803120106 91
    0x2460800404403c1c041c3c85880c2c04041540030401ca071618981c0c07842001058000458021352b103000b01f890300c540c0503500d45800345001044110158005a90252405844203401c090071100c0c000b0710042c5004282c403803072030b400d40c0212260704c0d42401001c1144c040d556008080304513000141c0340a00050006008101c000402c1204030741c801c1c003c2100b21220b403c0410902c6807900102c001e40100c0069030390103460000c00b58104100040c4945c21248030f46804406502809800d500b294001c40b203918201c0c85074600c03548103612443c000c200180c40e17001c00504014128011a0840f84240c0120000c1460310448440f0720f41c00015070701c010310451000f507180a003090348540c0c0b10f0340c85502e0b894211502082011031540d034130040d5400f45c03003c1c0080701e403148542c1c1011800740c2104d01c000d43da2020003648120050a0000c100c0e00072020011044a803502c80c4401d005407540320f110000c4a442d510360640544150030300aa038020f041610085889008814551522010680c0302101b441072803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 271260521 1250 271259271 271259341
    0x19020d020a02010f0e03150108120406090302060706020409020c01060905180703110d210f0302040b27060c010204080d03060f030323031f090605010e040905010204050307030308 78
    0x40d41800703166080c81c00f554040546441507072500d07000320641e076050082d42c032103400e05403d0002c1141224455021100c0c0300081c240d0298591090f40075180006205100600140c14030400a2814911420005140c6956004850704076000170f101040c02d40d4492908101206030b030301420340c000620420056050400c055007558070300d40c40c480108003140380c1d0a10700c0700b59101810710030442d8021003260468140c5648807256030100c0c011820101d800d688907034210511900c291800e0b0341c02c1c08212494250404245800b8080d01c0c2412684902c14860b034200d1616030030050304441a0100015031074030300300b03000141040340d89920700e0100740c41d01a040003582c038410f10b40401c42e6010700f051000e184d10303400c0c1c01202090007115001c80050020502c22003003c03410b070810305040c107100342c059843e44401c0d04009651072071080e00d002a955000503e00d52915a0001d214544104001443e207541c0b900401e042c655240c2c000c3d004204400708112103030f003015400904c00d1032441c2d0013800b00703158 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 271261771 1250 271260521 271260523
    0x1709040f0b10020d051602030304030b1305010e03120114040b041a0103050c09030c0108040f0206040609030b0916091a13091e150c1b080c0d021b010e01090b030103030519020d02 78
    0x3e02007060f40240c108403d846c1552020701c11140616080a607030007603807402e808074201081c1c0c90341007201c030766181960300c00c08a07002000703035201c0c0c41d410800f0304080c2c0d2910480307646940400b103416a0217039030f40880c0806941c0e240302e5103140085c00f41044140091000c00503046807001000b841588004201c2d501090b500030480e01c0d03586009003800c2190b40c5450810714008815128004c3d0001400140031803e1604074805000320782c4a00c0f200c8045035180801140c491404400d690b00064502c6010300c00240ca54000e0003160b120318807004d50a041c08000205130369a00c40d981c40020b0b0390382c4a018240000d003101d218201c0c1d021324100140140f40c0d598400c11360100c0113103d491030b50312280a144288038030070a060082e420a010101c101290400805652203402c6220640c860512801100f40c0042003160f6443c901c00d401c1501d5483c03c01c015100c4021151140d41080f411345d070041140e0303031190007441c041c5000e9585d10f61140c0a404900d410150205100030640d401103c0342d2811540c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 271263021 1250 271261771 271261777
    0xa080304060f12141b070b01090b010203090618040c050a170402010e060d0b03061602060408070303060806010801020a0306120203030d0f1d0f07211709040f0b10020d05 74
    0x20403890218007101220720100c0e161248240c3c9100d49500349020300e40c408405010075030050403503800c1921401c0400c903074004c0354031440c4c40080540700000010811300e02c040c2d010340c00804043c0140ca10b0f240c03410002034290351060b04410601011507410340e0490606104d8a0940b12a9062091900344441d4010340603a55180e0201d820f1034400c0005401c6900c10b010402183d2800303440aa2940700c00115003000d0705c1594400c501034420440054064926010300340b88280c0c09030081c1025440742d4640785065405141d043e801d2686a010001d56118100700f140e000700340072400143c513660b0048005095400a81c040b0b00707510300075019900540d4022046810002c0004000111120b819400f43c019128446281da43e0b8641440086203818010400c004400051400e444040707450340000d800d2540d00300c4880c0e1100c200070045500040410902000345042d03008004d040110040020f8241e4200750350007100642c484c0b85040303980c245945114041c00150015050981c40b00c04001d0040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 271264271 1250 271263021 271263029
    0x521010e030309210904020c0a0b25030e030f0a08040512040e0105040906060305010e10050f090a032a1101031d060a02131503020306120a0209040228030b070207050a080304 76
    0xa04403240c860a00c104d0340d0100d445110000d081551103100c4145c51680722004c1350320a0b515014441d001848060f001100e000d07000e458540d00e2424401e1070b0b03000310010210000b440b030180c40200668406040322a02919000145556514951a051070309500b056810204c07808510030900083c0031202441150505413a001c0c0d03000148403140e4200500501403940c4007800359460710301d044815500102d008041280d1400080c0000d4503071603040c006410b411100c0600a4018042c03040000707100304d002c140b210f90844a2a000c101906181e16583c42000d0400c940c0004040b2000d4a2541c0500400010f882000c0031102448840c0d484c10b519000018090603180760300040307402203244194429401b07401c2c4203603026110443c0740c030064002d600681c4d500b48240520000850400310015015031407550140a1020a0b115a800d004051700c41c5404252104802c034650001c0c480400200401140540111005400c100c8400b80c00c240e210340080303010b00024001405000e400008450481e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 271265521 1250 271264271 271264303
    0x17040308150d020904050d030e0a020a061404170706080703050f01030210020f03030c0304060e19061104030602160209101a03040809030304080a060522021203040521010e030309 78
    0x10340001d40005802c21078815000b94404021000d01c02486000100e4101c40e10b0b4035101001035a800d0f040e515170f103140340c0d0f00c0294000c00a00050001911543c003000000c0307161029541815111001031070321044005400304558840d180401456074400c0300c143d0450540e090411071401d000500741510001400702a00400300a0100b40030306208000d10302d0400100d10503240c40c0c1c00d0a9181b00c0c0b843d4020b40d400e8031054281340341107032440b030b0100e205190301503102d055200d600556a6104041d244076100e00000300010700c000030200d0118001003041203200c580100ca849558410040d20303040c0500b980c03050300c49884c1c051042c586203603640b090302c00d140110b0545983e95850b007030001d03200c3c080c0401d03003601020070f001031070040018800d11010b114a00511903030356500c1e01412550b42400c050000c0240800c03901307000d800d0004800d0030744000c0c80706070b91400c0e0703d58000c14172102084500011000880681e02c3c1100350a1080c10070315420f141c051469030600416481e60b80700c05440300104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 271266771 1250 271265521 271265551
    0x601030b03100c0207050f031c030b0d0b0106031514010e060d0e011b090b0a0806010507050106090c11011103040215032a04140d05031606090209011517040308 70
    0x110303940030058002c0128400c00b0a00c10400c0020000352174070032a00c209800364a41126001143c5008a00310460514250060f06000c0c01d1040c106c026050840f03801e038100300a2418030010809002802d4007a144030340f0003041c0c201c2100d081c40d0903c001c1358040345d400f103e100011622a80c1c048010130048408543c0282c50b0079901c481a002420701e5140140250f10b8494000f4036482c00d074405c00400103142e11034250341070743c400c1038010b9885140c1140002a1680303000815941c01007000d40001da00034400000c510b0f40710b403800300490311108031000201d04210342c03008040c00c00740a5000c001c541c80d10388509509095010607101c5403940c01d0845802000b10000d0350651002e100702c01010b01041c2200a07501d07109081003950b41c482c0c041c0000c0d040342c1c440e0b41905420440e00540c00580d11800840c1f628441440c2050381c0c100417030301125001e0303c0f80d950401603540c403d000f40c003a18180c01e6560000007401e00107071114104007001c0c0300c070b510701c60100400b02c2e4000c441c1d140e00031034070080540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 271268021 1250 271266771 271266791
    0x1d06040902130806070f020f0105090a08070614100f050d0b07051c0903120f0506010e06030907240810030b0402040c110604140c0f131113030803040201080a060806060103 75
    0x70425541d900002034031310994080100183d4419144032400c1156004e4449241e452034006090701d100310340c1540d566100c180128006916000107002860203000c001428410445214100e00300941c1c514948030000d400038002c40c1c8582c034010004103030031518500d00e00100d0741c0e90807000e00300800c0c075401d0180104440721103020040783e01c800c43ea09900d0800031010b161030302902410041610328100f601c0c01c10b100b58001e1982c0306140c09668161258005001c9690030000d10b58402454110305002d40003000426450b111052150006103070076003101c101c001d00c0c4c0103002c0d80000b840f944424030b09003000c00218010f600341030b8000c2c1d0143d9010800054003002a105501c42e0030484400f4070484c42048180301c185019801d22030074800940e000307500008104000303840b4020f0026030006249440340980c00d03659001e1031004107114070160074441007910352540110b10358030603102010b0000400085680c000310050b40314140440800026082200650391920010006418103955440c101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 271269271 1250 271268021 271268047
    0x21030e070b0307110a08040e061c0209040309091e051605070f020a0b030705030901060503010e0d0c0f08070309170a15150e01141806010f080c07050a121d06040902 72
    0x1061314400c1c881250103401c0c00d4640048070344e020388111040035600c4000b26015152441042131049071207a00180e03540c000780c0800980c0074020304101c00303028000d140003441c500c4e90300515034030706c000f4403004240000183c0c2850a44100501981e040024070325400411904081500c6000e50060344282c3c001d10980301080642a0315000084544404020031950650040c0214072841c01c003002800340641d00c4050509070740c0305402101450b0403607458105814411290b00000c14041d402d09442d0803d5615522607583c003030391050300099100a4140159403800c4204180000c01c44000c00c2d010a05441e0700f075503039008015103a03449441d00030300007114417880100f80c064043c1e4100c11160356900c00842030700b0407500803003500980e111040032110104695150b0300c542c7c3c0684440e100c20110441c101c03109003000304100164002440780001041041000e510043c1c42408000342007500030a001c0d085030798a10341d40c2509001c503140c034200c54960105480031208220405a102c1031000c0c070107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 271270521 1250 271269271 271269287
    0x506061608130e130203010c0c03080a0f090606030f020907020c030601090c020c0a060e030c0603040c1202120a1a090f071e1701020a030501050d08120a0e0a21030e070b0307 76
    0x40fa003a114408140654480003140e1040241d00c02c9000300491064400c0940316802903442c040e01083c810780024803c590340390800802442c03aa00001400d104550300c1e602114015042903840305502035440b0214141048c40e6a00701200380014074541b942c1000107581d840050042d0390700d250300d8091240500f4000c0041c034062080040049509075120302c0010002e441494000d44244940100740005080480850740a00e410407058020681402aa06061010200d0490700612201c5a45651290a0001c4900c55104202c040d00c0d00d02c103080c0f070000140b00946142d0058200740e4910078848400152402118000b049903040d4003000d072102c0c400c00e055a40701c018209403261900c884c255040d80185020f6503142c9042040c0e90702d07502403040300898514000d0230710808000340b200000c09651196440040d40c10003240751041e5900310390400704145400c41d084070780355600c44040421f5042c43c1307003148080c1c5000c000440c51200d01654072240d9206620500700d001020030a41885a404 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 271271771 1250 271270521 271270529
    0x120f06150d12020c0109060e0102060411030304030b010e060f121005040c0b0a02150c09030d051e0f0315030d1b0f05070e100f0612022209060603050606160813 70
    0x40d50001081002c0030752201c4d0320f81d0109001400140c808100c0901883e0300e0894014181d000f03120743c1d91580c2e50503407107010038042c0c5685071000b808004001904010054085c0c42d10f100b0328103481c00c0007401d0001c00600055030070301c0303282c0307498000414010010b41000202051800030400ba25176050030705404a0300e0308001c039110000251006001e03000100410031820310010142d2569911a04001c64040e0390707a0380f03034150411002c50150170711603000b401040c4601072091501ca0784540304120181d21482c4854010319001c01040308006190078483c440d400168040d00110490803001407014070103040b114010150840104240400d0004014407140d0001c21581d10315110702016030811401c4520b55a03d41d24928085103200d20559000222185a1210380c114008030300100041d400c000b0b5602072980036a00f0048a101d40405040300610a8140024080c0c0c1070842c01003e4640c02404a802804100308400b401210010401e6260750000c010a480310071850030541d0092841d44 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 271273021 1250 271271771 271271783
    0x90f0409120302070c0504060e0c030718030f060f05010605091215040605040b070c0f060c120c11010b0108100302091b2808160e03010b0604090209120f06150d 70
    0x18511071641c25500030211980901c050384000c6903614204410784166011382071842c80d5500104e100346482c0c01c0911740049071410b02d041100d00141700f80c0f2003000e40d5441601c1c1807a4041426041c80081e20410814560907401032050b50304040d00038010b40300304d9201500511a80003803100c80c801c180881d000d000c0c4001000440c505103801c040000d0141558140c0c1c9030141d881c046018140a1029a449994032040303030f0301c1000c0c0a407242801800c03828408020b000144180c4601d9000c50b1003503580b20034480d01c5034803800902201140c02c44e5042e00b0b07291305120f802003e12001a0801c841001165811207041c241540e0300c0b104020b841d0107940c2000b45190010450140354016503540c1244001400200d42d8440f030206002c45100b182138812404440c0e244422441c1d140c410213052003062000750000c140d0001d41d0010a038103602c254040c1c8140c0d0740c08034001c1124074000c42d801824802c0c200003404005d06618015480700c0000c0d00740e003011a60301414800a444615441d542250448 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 271274271 1250 271273021 271273043
    0x33813050f010e060a0e07030504020a180507030501080102040f03020f0303270310140402010e0a050d05250602030a080406110307081b210a0603050607120e03040b090f0409 76
    0x2488070000070a006049a00408100141e0340b41005400801103aaa4941d440f80302c2c0c8030000e00341d008003006002640c00000b04a00401c540c441030800780c2c4403001140b8001401e1a020b50024115541a000740319682d00411003000076203d0380b40c03d20140c07901182c0c000a01c5a1040003c0d2075445a0703204007002d041703030b1040c01c1821100b200814485807001d509039002d03c158040c070313601102d41405036160313a070040e0004500076500ca564880c10080000d0084e02c0c00a44610005d100404000c0c0c2c11150f40e07001c1481d010b0728014900d03040c442031000da001410860706202e0082d403280a614001000c20610900040a1104c6500402c01e0720902800e40c1340e40c4c1c1000080204080f108588180d80080050300740c8210742c04002c02c030307a0480c1402d540c540f94807480d80c2e240c1041d0303140904581003864480f0404008110b041c4038240c0104d403691603900b9034150024040c801e861461844c81810b400c10b0008000e4000c00c1c0302120b01c03c400444200c00d20740a04000039005001120024100740255 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 271275521 1250 271274271 271274281
    0x1d010603080703260c0307110f070503070b0c070b1c020d05090c01090f12080c10090b010b0715020702130501090c03180c0515250303381305 62
    0x1000400c2603c1c000c3c4c0e281440305803000c0c610810180030900c01658525542c000454604515015581100c0c07540342c103104e5542440314052800d04c129031080c00580043c0700420043c9010003940000702400f0006908100305c944106031a0201807203101c2d082c4c50002041074500c08520308040012074003000031501c039005580e910008110403684002148035a80d00e0750b40c1d640c011400d040442d038800e0b95200e106401c2690090f801d40c03a0540803a105c01c0148400401c014081c0140e80e6201c504e0000052a081c0c0750520042da4541030340115000e21041110f4404251621459082140c6034000580d40304400e10200d10320440c48400305402501d0900089031071302c10b98100d88400140341ea828400490002e00700b840c04c002045006024420b810b0041129040c48030ba000006070410100604180040d04d40c000c614000d00100406141c202030f202041503003610521000401c48032042034051000b0420801041d041404064803d607201d603500c040b5540c01c04000c6202c40c01c40002e020324104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 271276771 1250 271275521 271275533
    0x509061014030a14013807140c0a05060f0a0f09090e0d030506040209031504110603010f061403010e040314130f17191b050909030a120e0c01031d010603 67
    0x50304450441031a20038000081100315000707140b054203809200880f07080da00c0c45810903040300300750306d10001d84024407035440812400701004554126010107003001190000810050110a03008103204e5242405920080030820b001d8511580360b43c00c1840703030100804010345200c00168801241d032420610301908041001c2501000c01d13aa07618180138030788900e4200802d90060b9040310350183e204040d0164007d58000071240c01c00c2c010358007400c16003180d4010901d0750744260041b09404800380820000d00d54000b071086e40d00043c0c00d42441c19941403218080346020050009020400c0450000722400f000c0c000301c1c0d43c0d80f000b03910f4030016207070345980440521040707102e03040c0c49405040c190316038001c000c608600c501070700d0b002042c003030402c5580f0035800d03250306002100341c04151240485c10742c6480d148540204501e01c015500d400c0000c400400740c2e040004060607a5013002912504441e000039003645040b0300742000300f0290400f44d10720602c465914102e00c03003907091000000034000c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 271278021 1250 271276771 271276781
    0x40908070c06021f0506211507050708030703051902031303020c060c06071b0602071a06030a032003131215021204020f01030b031e160509061014030a 66
    0x44600440c1c1005540c4100a83c1c0307503418038800c076404490481e804080d20555500003076200301c00810003000c181002c00807511030380840311101078903403045a21003000c20b41480d40030f60020f200c1c600b03245002e28603603d1002c0b501019200d1024162501d020030358154100c00c9448007003610101c215100c0c0303030410f8109005400008282c0160007a0034060200b070400c80c007114001c0720010014a2591501c1030100c1e2a80a0490489032140c4a000e0550008002e07000030118180180b40e0a0300b485940300840d12840806404244030b0781c04402d203170001a41141a49035084585c17180041030525846210b0309512a14695251020146c0710100340c00c2c400000c0c00003858066960321084280036500c15089114000c80709800583c503000150061502d410301210b080b4043c0340126801d040000464507110225002035a001d100e07607102c80f0581c108108054441c5d10107000e80c00d05070320b070001107405d801010b040c850080403680360314020f1600602c01440413107e0481050390724074040102000400d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 271279271 1250 271278021 271278023
    0x304030b090a2f1f2a03050a0906110a0b060105040e0910110c1b0a08030d05010501021b01050405060d0e12120f01080d0305270304051c17130504090807 67
    0x8288034003841030303411300c900c1c0700a100c40d140c035002056034400081600e4a14441d0b54a1103a40c000305000c0d00040c1001c41c805001d18841c0d11802d4480c00c8502000c0e04061080d002107042100e5100c2c000d000070b030001104801e4503040080340000f916030b400100c54502c80e60300003c62360321038442800841100060082c0d80d045080c5c4040208400956820406104034039003a001c99000e02508000b61500f10300c10482d5285c0109049101644d54081303d0654104008002043d40d0b6200100000d5070180702c4454001c0340320201c20000d04100001070824020340c058140210004034203490000070760b51203c078940c2a81e40803241a155050b4603011240d200c4040004110a000c0100384a1482c01c01c406041e101c490014082c40000d444003107009001c002c180d02e60b00109490800c190f00c010880321101c80e42003801542e42c440c140310510500944041902401910451f103000200342c56450710300d1f17030040310b5815590310801a158100020910f411469002d803030254074a08004007680102070315 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 271280521 1250 271279271 271279343
    0x120605040908030603010f0b0607110d020a03030309020f090c1e0906040e1806040213090f1b0303030608030a020a0f0303061806180b031e0a0b07020706080a0e0304030b090a 76
    0x7007c41e16030302d0b1080d0343e04039210741d0b045501400b1500008411142c9105240c0c0c000c0c000001c41308054000528846165000781d000c41d6503140410203500384508107850510060f6415080340c20402e4aa513017901c50b4910001e010201c07001410500b410b111700321441b400000303200f1903e498031a1703428002c0c803a00781e5045941c6589800a8168100c0118403d40700f14ac004101010040d11000c44c1c101400880c042102d2810a049014000890200a00a0551062850b20700d064114503001d0304948007038014680f1a4028030030200b00d5580024107000c0b80b9806810155640e030740d4501500a8441030b04082030502410001c441d490141d98402002c44d00002d0320040d83c00b21541680080381c0c101c030000750f00754000d030302081c455000d07581c00100200581012070307002900589401028041c29101c20005030401001008425800500e00d90000f080c00710400544401d5071026559100c1c5d440010440320b030020000d1804c40090110b1845580c00c070218041030000c0c11011048110448035200c25 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 271281771 1250 271280521 271280531
    0xf0a0905031c080f041401091412030f06101206060c060b06070308061e120a05070611030409110d020c0a05070f030308060f0301111303050601060c0503030712060504090803060301 79
    0x1540310866002c804030407054a80c982c0a49481d0f12540351840f0082c0142c2e14490301690490441500744507081109000b000320f48030b80064040043d09001341c0d092000180c075018010b003c900d492014685820071001c444041150b44c4032141542c000300c10380b665101c40c9150500004400d50050070700400e80c3c0c0314901c10045a50038a0800036039000340350300900040d0141c0c00207070003810302080c080d00c40c4c540003032075a02440450700040c00f031107460b101c0721045401010a0800b040010000b04000c1c11044c1010020903a41c080c000741e881c01280b1406101548480e4404034200016007212007800d181042036560347c00b42034400f6540c501c0040d088a02c1d03c1a0800040e80c544a400c00c032080d40da05a403982c8050300c0e2102042584130300103a0a940c59580d4000a016026143c80185420344507001c0b00d0150a1a5041c520f080c18030503030015044c442800244400200302004603a84042035041c01204403114082c403100400d0940c01454000e450200c15000f40504003019501c102822002842 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 271283021 1250 271281771 271281793
    0x20c28030801051f030911100201020409050a0e030a030f060e18120c21161a0903090906010f030e1603051006050109230d12030c0e01120903050f0a090503 68
    0x800709510410070812013604074552075803e8407135080f214000740a11103400300c90f040c4c1400102c41d1000303480c0120141c5e5000404120b08003117405015403102880b0b00400c48820484159074592051038025800c15070313174499251410380c996002801808440001c16440d24240c40051401d00d000c02011201d4801c50008004005601c411200c0881011010b4007031040103a00d0050604508992607800d03010501800c0307080b8549940710300c152130161583c0c00c0b41c1103103182d076200f0162024000340a80d800801503d8240c0d29602851b940002003032804ea000d070328945008500038055540c41070464003c120354240022081c0c0c0900066a0040b401d490040c1810f42a0b50102e4880d84143c60109440180c10444503d503a040720005022501403035010300d0311080026006101c000c03044840d000d0f000c4610380301c2c5034144109002c0c0307840c604003030300c6070524900081c00c02070300355203007403201629083c1c82020140310390240d80ca0040e0303071240d0540f00c1c440000050280c01d4203006540c081e206003502d06c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 271284271 1250 271283021 271283029
    0x80d11010b09100605070201030207060c20060103050d0c0614190b120c04020304140a0312140f010509180a08090102010e12030c09040e0f07050109060e09010504020c2803080105 78
    0x203024078450f00f074181c2ca45140140c10b883c0394000950907410705a00344506c10128800380034440d840d00065a0707a124596044148603da440b141503008115440300b0014000108000385858521245091004c0a48c10a2801102520101c9150070660030424284100c020340b103a114007807405850301c20322400d042c0000340004402c030316021270305560010035800d10390b0410754001c41d001809400c00003848504138000601e48000c185044001400c46108064810094030481c84207103075a0071100c1041c1807100c005c1414403c18000c0d01e205190340000303d101030018284441540a0301c0090b5284044c444c101901d051304003410580c059400c0282c01140c0d00008202440b110314098106800c41e04c0b0030000050503004000c1007a08240c0d40e1018a888601c10800c241c550407502c001043c0c0542031400050112485502000510240040c4204c4aa03a0792000e141540c005030f40040c3c0320304240c00c00901d0040d5000c003103002083d00c520501c9030441240d03603004049010b80c68240e42640e03110244 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 271285521 1250 271284271 271284289
    0x1002010b01091d06090406200a090906060522050d0303090b060a08120306030703150203041208090309010c020d0b1305010605010f1706120f0102090901140622080d11010b 75
    0x703440001000000501318501380d00c04940081c01404001090304200618001c810f0f030720203c103a20018080f44080105902c941a1400341024800602103989000740142a5000704200d8203182e282c25101070110441030300c030080007480000c01c0c0622181fa0750034064014582800700751401c0017141e00080b034500b050f044c81811200710740d0080c4001c0343c10032000d41581d000603104030fa05000b400000000305005c1041d110725141d030300c4401a603034105440c0010100c10003461003000d010542d41000200200030041d656016000c1c2042000001c143c0b0000d85513000240d0005e0105600006015070010b1440d07058150a209000070040c050b161030044d1800003081c2150f10000f00490003141d2000d600300d075981d800c40c40180100c10301c1d401091050f810030000c0500c0c01ca80d80e60100300b200e81490214a49030040460562102480e02000301040b050701c2418103d0042454031400701401c80b03010b01c1130347c0040544105403101044041ca00803d80c1c0b4101501160643c03c01c10415290b2400c5180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 271286771 1250 271285521 271285559
    0xa0207060b0a060c030c051014160e0105090103091401020c15100f03120c06053903010b09011e020a032d0305090111030a060608130c05060d06051002010b0109 70
    0x55020140c0700740c5e0201c40c40700000030300321a03500410b030038402c095005005d8141d40c0310000304019100c0c40c0c19081080c41520032407a01c0304100311545e0040c881c5c0d800104607401030b4020300c1d000c619006281801c800040342580c02c9400c039840040c91790991480402c00c4880c2038411081c0f00710310340701c2000790852800c00d80110560710080c12010400214601b0341d800511556080c84e259540d00c4c1e441c1c100446008440305905c0c0840d10346140035400308000c1540070300001c011010b2140c14000140760990105004820703070601d0028191845038018480392042c3c0b0040c02083c510504110340080d220001c5800440c003040d1556824071074280300584000c1c41c0c0b51816041c1c102c2084504044020b0071018168414955848480040c0560030030011849075184036404120a49410401098510000c0890412036040000080010fa0700948074044850403a2138030384495141c15014010f003201c0d030000380c0c000a50b0323103008100c1f9019000315000d18000d07212821400c2c0d0f07941400324542e0108003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 271288021 1250 271286771 271286777
    0x60f1005040209040b03030d0e0c06040810020304030e150a120501060f082d06031207050601090504110a06030e0c03030a1704110405010b121303080f18060a0207060b0a06 75
    0x20600ca142801da010f4003268a004101080845039503020034216406501e4400341c1a03101c034040041c4a40400c50b140d034010701a14001d2070a40743c90700260712070410302600c1c4c107400e40000100d400d151095008d007895084c01085640001200b4803020307038907486080600007168100040b00d2a8001d140b088078121800c076200c011034030540003030850b1820710040582c848012002c8040b52a8070b03568001c00c0d452080e18408203003a0400c042014540390720310464281000c81000103000180021a140d411682500404907081e00c680c9009510907940b81c2c0b032a50400c40c1290006440d03640b5401c5403030201c0f60721040e6040c51092000789912403182d400b101010440f900007404007042413080903503109009040c100310a8500350f0014050310f900380d00c502c04400000c03e02101c01c0e4815011142c001d52581050b01c50b10403142d0300684103641c000c0020000c405000000307244d612a240d810180311203407209a03140d620304800381000a4000d0b031000d81d0b8851410130100f441e8103241c90204184da0183e2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 271289271 1250 271288021 271288051
    0xc1c2a0906120b03012d0c0c061d16050109120f02060a0203070b0a02250305030c0c1606020604020306010b040e0c07140d08150301092a0b03070815030c0a050603060d0c080d02060f 79
    0x4c2c271100f0240903032a9400c951038110703800b030302100803080c44014411101e80d48c80c80140d900d84800100070f00c0c1e0a8100704005c0c00c0c030543c483c0001e440d40840c454001c3c1c0c191000da440d0240300e1001d07030a5002c0c441000c1c0a103100740e030400941038601c3c1c1c000c01c0384a12800d03c0c00d80c450b00301900e60b43e406c1031000009001c20030070001f04660a015001520f03449158100301c1e4554801022028000e4529510071005030744841c050004510b0148038241c05070802d624110b06242c80e08102600300e0802400c08003d5100001d090030501103103071076021441d6010b400322076520f00c0e040b03c018124502122600301c04006491071541500d01070203100d0b00180c2041c0c844095045034001d4010384640c860000c4028110040700003101050303800a1486091282c8900c0c4403403520752002e0324450a01c84c099482900a920041100ea031808440030a0303840030760302c0f5501e0740d4400d00800c0485030101005407803101d4003800045c40c210f0008800c0c511960a03402e55800b5210740f503411700050700c1520524402c40b400c07 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 271290521 1250 271289271 271289273
    0x3030504092a080a11040305060f0705130308070f02120a050d020d3c032012150406050a08010228080c030c1c2a0906120b03012d0c0c 59
    0x140341000d800c03a0b0b10f01c40015507905c03074014a0036141c0c003d910031107440c1c00c10350810024190603454980e004481d030611350301d801d1a40005944119040c00300810040d0003107100c109200c41b404000065036800750400300d0001d0390f00904c540c2c41584242c202c03518070071404e40222145c40840d0b18240b0060a44030407080f081d802c0300005880c0390b0320300c3c058076005894403005d2000d02e44111280fa801c20316240000d401c041f01040384602c9507010b100711a041320800050100c169500d60607648404410720540312200d00500140103041c60780e100960008442c5000300b103007501035004004480740e40c078004185604208060894a0030b890000010414940003e1796a00e4440300071135000b0b44040030a842d060117200b05001d551500c100601c1003680d0340204181c0500708022800c03044c1c1e255007c180d400743c940713503004128a0484c0a00c02c02c00c0418207c40c0f103141c0c0180c10003030f800f2000070028801c4100d1208214104009443d51140c02c2c1065410b0b0310300705030140310b01c003200d00e10b541d149000c1c1c1650b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 271291771 1250 271290521 271290527
    0x102130e090118030801030506010f0e221b0f0e011a180607060c080a0e0c010e0102070305030f0703080a050408030103080a12050708090f06060319150603030504092a 73
    0x1d254034025501e80d0400a9010b02510019650521a4036081d41550440c1003161611905030400f00d02000c000030140950801d001695500204a144025014079050204903d000551000a08403010703070704940010020400c81d0350503038180000c0301d84070a170760f80c0800e1200f550078413462090580d22800316180c4d806150003084201d00c025234010058550703001040950340036102c2550255502c13621400c013950702c0380310141c100b128038000303001d503d408441e40e540351040d51100c0343c14001204120780850f4002e100080055410034196a100c904110072010141d11030f000403400920080c0000c0e01c1900c0d1403190341d002e030340c1103e40d40c0e045a0842d0784420f040c2d40404003100074410700c03803c408050300b000c0c02814480c3c103480d03844403202d00340154132914150001c03840340b0701c641240c3d0800c05e841c0c500043c0c0a0303080e85841d50148043e5024240501a0300c1c41c45c0c2078030640390510b0400300900d03400c00010802c84800032401c03c00000c992658280b01c6010400010403800d0141c940d52030350384 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 271293021 1250 271291771 271291799
    0x90a1a0f130209030a170403110f01120b010e0901030b07020111070b060906041b1d0406380406020d0f05040308090409080c010f0f0b030a050d0503190207060902030f010213 76
    0x140941103c40441164580ba185000151b181900b80c2d0b200141c107004102c2800e200305007803502954280552680c0c240040d00c3c0030080030000100135a40d000740d01c400d1388281281005900041c041070007958507410038024854048070760102643c2005024450010484116214582c1101c013a00450f20b400d820003600480240140c1d91117500c1d00380c00b0034401c115240c50301081b10756464111448444041d007804d6094000c11880c400c03440d11000b0080058650940714850025110319000e0944903410140c04c030201c241d801120150100313010a1450b0009a1008160741e40d4a90000d41c61140c00215042d101c1c500001700381202c107201d01c0c1d2150500e40c0152040c0c5114400c410305181000c000c80342180c0c1276550024045480c1d8281c401c1c160104e200341158280154007800d103500d1aa106c4554a0003829041d0081210000000d00c1c4042e80003020300010680d04020b5544400c01e040c50b030b0240c010748001303a219010f050080b1105144c14400c031020400e2814100109505d4201c411400103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 271294271 1250 271293021 271293037
    0x60c0b070819061502070f080d050304150504050618060c0d0c030915090c080a020d0b0a0605030d0c02180609070c02060c030d021309050112080315090a1a0f1302 71
    0x228411400b44407640c0c030340220b801800c411070200c03400c0c40460400915003080c1d5442840c244020060900c0481000311f85080c9115040c00c000d0741c1d984440ca000c00540c2a06100140c038589004244020090041210760080c00403c00b489030b43c51a02500c981c64440035640198400001c00c1103d5050280350058038841180742000154440f007500e9100700d07007610319004004103590b100300c0010425840300350b50280180714010141412142d020440c8601e601d000030700004c66500025a5401c1150030450280c4000360a40d0290b42c50f07014080c0c81940c445070124403581c100c0d6000542142c60700512407140300002e000030300c1916005801e03106c10908800507a0800010001c280c40200b0070402004c0700d8001500045e52104800340d2403407408880d8204451840c28400100320308540d03442400c02d403d410084042e03070380d104c1c41c0d502040c103800403d49581142040c0100861030b541584801660451000c1c0d43c00a00c8030b460400c04c0200c4000c030b6043d031000051070b82c2400440140d021705225 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 271295521 1250 271294271 271294291
    0xd050906041710060b03010f08010605090a0b0d050708062409040b070c0803011701060614040306110d0c0807020106090b03120706060b04180f0504020913020a050409030810060c0b0708 81
    0x105510b0403c1419207065801c05610f1110000040001800b0080310800074800a0000c0003510f0411000410044010340001c1c1d140b0b4540e41010201d40d01c3c800032580803540802120032a5540b048101d4035403000300c42201e50402692002c0c042028200d994034442000244400019039660ba58080200400341401003003200320420307440003403902c20003980a000c00741408120490840c0c1903509403072040d0400070410a101400d507503100d1179242a901078a13805132004c00d425988100001e0329004031040c01e200d42d0f080c00b90415134190002c035514059215540240807450300c85600781c003555102d00810750194071240540b403243e4040805444218454040482c1c4a40e03900b240d080950801d800295480c003901000c41030402d0310b88610140b411000e00184964a00750300003a85a21004100480c0c84500e1002c0310110754682403018090100207008010350032190400401d02d000071a20351104c0b240d1810b0105281d4003c070240c3d9480b03507020020600641e81d000044403c444054803403150 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 271296771 1250 271295521 271295533
    0x311040b180702120d0e250b0a03021903230601050706050a150303120537090516170309061b0a020607030507030e190b07050c09040804080d0509060417 67
    0x2940c2841c0005003030717481c400742d004200c0080344001c0c1c505000340d4010444400c1038400018407220442007000d000c5540d5681c038251600c034802400ea000e8840d82982c4142e01d15503144181866405070700c42c461510010889804515140c02d0009560b8010317900750303000c01c80a004180004005401946d4044000c3c240818080d44440c2c0c051144101c0d5081240420460300050700340c0d8040b4464944e00240604c581d40900306011400c02d0014092800340d8503030342c80c5098400700001c503900001e0000d54450111254800201820031807417200c0e000f28180626012140760301180d002060300d51074040100b0092800554142003440781282c258800d0143c044d40307540e90b025035100000b034000940039855203542d440451500910346100b4071480e5201e82c01c0c01042980e43e0b41c16081030001e844141349100c0c0d8503101424054540410303012040d03802100001003104220302200944100d40e07501048a40b107a00050301a600c90154a0406400040038401041510110081c04c68075140314400c1d04c403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 271298021 1250 271296771 271296793
    0x436030e0f060d0e0606030f010b011e0201150f05010e030a0809040e10020408030702090f070e1201020c070909110114190c050f0a0210020f06011a0418060311040b180702 75
    0x205681c0340d04c0c8884440c0e04214104030072810140200c0c0680d051140c002c1000b0120040082c00800038a0b007200260075606804061541c000d510a10714054041960051a85d8070152042c0d401c1c4240640e41c001804030005a015080000f0a4001698400d0007941414020010302000300309420308104d0b0742c8a038a070f0301000584039100400243c04201c0241d40d842182d4011f11083d500080c01554685012400300700450780d1080700ca08a0f110200c509801842480da07031940a070180b00d0900c2d02e5409850300c00941c43c14182d00c810344031440799960040c0700003540019204680c81c0861101d0f00c01d420810031110440301d04251610a01d581071201d018003035500c0b01484c00010080c42403081c0d10410300b51040d8a41180f22a480b14000d200400582082c0c3c55110380f1010180710b03010102120b000403280122255040d900074114905503400712410100d03000c0c024000d02e10050341d08d401041001075090519015070302d410308015221342d0103a01000343c241c1100400610400450007a400c03108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 271299271 1250 271298021 271298047
    0xc031810140435010204050411041401080402130c18090204260a06061706060a08030a26040c0306050606031014040b060c0304060210090302060f04050a020436030e0f06 74
    0x3030703c1c1020007400180c59500388800d100869503003104031400d03000c050104104141081c2c4070170069107003c4c0303000c0885803500d00c08541400d05a001c0020350034142020389c2ca41c540d0004200321050100202501115600c0b20050128401c6000d01591114840300c140da100d03400300503c14000b0540001c03108110304603145c00045411031380002221803c0d000c01000c012400700841038000f0002c48281010300c0c600016241ea034410b47d482c113028040a40d0440d5a100403641540240c1d10f411603206000c0d242078900039440c044e441c04116559032a240112300f0608111058a1180c10700c6446141d1150070003404098601d0000031051740191a1b00b104107a58035424041c00150051000440d00d440c1400740180c24144a8811114064a410100e45c0072a60011341c8035040760b42d5030030703025041c0c55608005080c0000e00c1c4c0007a40160421203424840700900d103244818004d8001d4007040d421203036511380c4d46c1c00744080c00640001c003482d04070f42851400855021405000500291030b01c410359001da = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 271300521 1250 271299271 271299359
    0x1501031d30030c0c1c0504060e030f150402032b03020c010213030c0f080a021503041e03080115020d080f1314010608070b03130809060c0318101404 65
    0x1510303458004100c840260f202000310b2113001c5c83d20050109400202140200140111304c190000c200c100c09016115072000e211180b503186040c81034131000c20502103840100c65054808a0081c420515080140b96040340302e0700128095001c3e041081c5806c01084002e90444000703821655801c00c00301d41402e11200003d4029881909841c2c801403916005442621a40d0300c01c2c0d21607000004903900694031007641c00d10725640d0326540d0b46c580d02c407400d1021000007601c1c541484007151152003000e15403c81071060484602d2400ea486480c0c3c0c0240803611070300c490140f40085805000800d12a1525402a65020007c490080c42c0c1d074a49407141c04801d8050743e99040d44c1d075504e003000c3c00b15074400d00121f406400e107452000c0c13540c2030050300e0142040203010044d040e0700d03000c00c0400307503996200c0440b0640c40740c1e0421a911058140c0d2030b0a9040c4030200300300c0c0324841c3c148851054038010260a0250790049800703030f00303162504c04090240c0e1200340c9600c01e02c0e03514982113000301514000c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 271301771 1250 271300521 271300531
    0x1021020a150f020607031406130b0d2a08060604051803070308010f0b07020310020703020304030206042c10031704030b0709080115030807030e0d0204051501031d3003 73
    0x602002e0703954070303030303000c1c4c00d040002d4031420805080031040b00d5102c5010b12019003104c410b582c0000d0702020300046600401c6e0b80c401d0140e001012902890610034850030204500000c2a05901184074039000308040742120301c5400d100f0b4000344005011803402c0d500c03445c0d10040e001504001501c1d0007044a007141d00c42017007140850941c0005000854814a18101511a80c020a8642200e5400181d0754855030b05103e03132003a400052040806100340305840003568051302440e00c440d16036420704502d45407580024074002cbd65010a060701032000d886035000d0840301101c5180307241140c561001c0c0d03480851281c032604404020010000e603540c886248180352542da42c504483c1403140490030f6581c24090420755051403001840400c6000e07088038038203681405c003109414002004240024150341010354001c2c50001004503000540901c040b8a0030243e80811440c00030b010040c3c1e41b000502051816170f80422a1400e119824800c641d01e13025018108a0300842c1d4042940c00d66032044813 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 271303021 1250 271301771 271301777
    0x2100503090a2a0f0b03040f080d060f030201030e0d05041202041d1509030f1c0912031e0e060f0618010305010b090106050a0e01200f03030601081021020a15 69
    0x2091455003e00110800042d040e243c1600300c800d403514070510320501000e04042c2c0141d120381c0d100d10410002d282120301075038000c0c1c2c007071203101da4540c40c3c0b030500070310382c84164042030400000e27070401000450500c0480c10b160b100c50f410305080c004007000c11540004121b80055440e40b500300d000072815800c01e50781c0300c000d004100041c9178900c655400301001d0010805a030042c4807842c0c4041e041030a0710751040d100c800746403000509a5005028211007007000e420741d0030108658011913416000000d80b510400020002d20900c890184120342d200707140f05100e60081c030081000408403410864118a0080c07814001814000d110b841c1d4100030380c800c841c81da65840301c000503418800742580c018590b5082c4182018400760018000c2ca082d041c8040c104000087e40c002000f1811201141113807403d4200c6060512494403030fa5294402d44850f40800c090030001600ca2140100310740075100f00a4030403040281103004000b441020f071004a0b44002202004200c1850900c2c854a21080311750f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 271304271 1250 271303021 271303073
    0xc021203100302040e03070f020616020907030c0306211101030915050406060e060d0b04170708030901060b160303270f060e240405250602071202100503090a 69
    0x40f04020032190b040c01c1c200c00c40d820074801c0c1e10104000240c10260b094056610304d580e00307209203031042030350303c0800001d40c441c44520a01c0442030b80b41d0321000c013070216920100503158882c1c4802e007000d01c0c204048210450f00c000d031034000900140c0c05907110141810080b45c880c4103a5100c00c400c90a00c2c0320152001e58903020041480380314000c0c2e8000300090107820b580d50400340c001c500e04c0c00d01d04901501000c80301000c20b04000c4544001100b050b6807100164943d05586070210f02644296010100c560a091000c04c808088004890343c5001c00031020b241c0c50700d60ba078154040c0500491403502034000102c1e044c15000403075552610f02d40b00d40b201c901c0c07041d0640340c02802c0316003040030217000381e10004801c07120440c5201d0b0240e42000401c0c070450b10b0359441c5001031070080121003503100d200c0f00d249208103040d035642c24041a07940d543c00f681c900c04d450b400305810649070408043d41c040349050392040c220380900300075038201031030b0b1043d19400c80079521001c502c0d140f041c441103c480d005c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 271305521 1250 271304271 271304273
    0x706200c190812090a05030d0b0901050307050a03300903060f060b03010b07060b030d020c0a060206070e01030203040614010b131a0316020a0501060e0117030307120c0212031003 78
    0xd0150108005000300d900040c0309040d02e0780315441c050311280c50f42c450452000b19140b010104079240a107544082106e6136074103107540d400d01800407080079900481e25800040b815103004101c100507a84090415152940365031901d44503c03464889003204009001d074142d000c40c41000c00084840303201d880d2618505e18501c0c107182280d5003502c0300b110480c035020701407049400c032504032411100350416040c1c403905a41404002400c1c2e02c0d0075141d043c440c4c0002c00d00c400c0d4011640c6040048101c948841036540ca80007a0b0b01c1d4402242d11600080080782e0b0102603600903409550458000c3c00f0008420381c804c1c3d0712901d11203003a0840622031030041001c55880a0b214415005015400000141c98941d003a5064541c08040c00c6a0284145042c009004c0b6100b00500d600040d0410024060659500c400800400d009c4c00b54201d46014031031500d0100304008100c0e4021a020382d6030310801c640403101000101b07684281f500445c0224445001310f1058034020714080c0c001002d10b07264540c55 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 271306771 1250 271305521 271305523
    0x10207031103090109031401021c0902090c0f07030c030903050105040c09050a0603020901030807060b0a030605090d0c0b06090c1c020310080123100f0b0702090f090d03020706200c 79
    0x10901c000080e9600401c10f010190340d00810309011250310240701201e80350480c2d281406409103202c612200803180c91100c1c110760942d0021082c0324001d5944a4464480c2d2402d1200740c800c0718184080c04d10700700050f40c0080c0c17240c41c2d21482c850107450070907a02d940342e549007420344105440a441584500409101c0c907860751242c580c00c00d40b8100d040064a1950b8003040ca00e803c14800984800f80218540041c4074094001405000000b81820388031074491514500400058507106510700c682c02084e220640506000e1000f40d8100303850320482d0740e40408001150742c0007081e00480030300c28800c00c03111013126284545034000b0504096141c0ca0024015000da041a500600e1a80c0c140040c5d0307280c0841914621038112650b120100890b611002101240b6240ba482500b81103004c0300005041c855520241080c1442262030200ca80c0b41d020803009001c2095840d0006900a4940200003d000380e000b0403809119000110301c00300c038007142030705020170500040300400c000a00c00b403031514 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 271308021 1250 271306771 271306787
    0x1a07060b12060718080d030b040605060c0d021b060904230901320c0a020109051c031b080c13050301090b070801230402090f0d111804020d060b0111030c01020703 71
    0x5280301c4404c1564036200d1100da8880c110f40c800c5c402d1541d01c819680058413035401c618003401c000b5000540d9520300403401c2e80e0740c04410903920700500954420380540c8104801d030f500c507048014443c608000d0742408110003401500d0081c4020141c249000035004055511644100741c00c400004254103100400302c2038644039003094100c1070141c1074000003d10403440f0b580e0017100f204030683d1213403d000c0e03060340102850340c4003400c00c1c8141841e1079000300c040320f1800440c1000765014425181e83c000300c1c506002041c00500c0110304540f001882e100c1081e8084c112039140003110600d01d03541e5501007821074000032000c0d10340c1e90f02001080f1a0300c1e0040c2c0c0190040c0000d46450740014881107008422442c030390040c0e80304540000e129090350f69045408403520b24000d1090310915098a801c61a03070140001c404e001d0490b526004040700202d4900c54812a000350141b01d03228842c2d03640c2001480a2a5141e043c800074405401945104002412229483d0000140d44800508001e08409 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 271309271 1250 271308021 271308047
    0x706090804090c050306030a1b0e0406060f090209030606060901120e010902040b031902091e0f07030c030e0304050607050304030f050c1e010509010f03021c0906050705041a07060b120607 82
    0x13078100284085610700082290000782c101103c050107030a201c0c0000c0700c80c05141d0007000204080300921092010030b034005c60481c0c8244d182c040c01540d8408400d400c0c1e01644041c294540c0140c0d00041683c2405001804944c90515003100130b038001c011880c0444202c0510100b09a546480304d80c11810640b01e000c400741011030041c031030510f81c0c205c404004414064001e000300b442d40f0105800c500c0040790600601400001100b0310b18121020003030364901111000c00080c103040f48031900c03601a2040c64103001e880006140307031904110a0105c950310045c0c0440e264801000000003051f030023098450a03903c03a070094591490780c0c40c00c20186a402020b00139580c251075075458040da80110855451410a00f400725a200081c0313820743c001c1c01b80042c3d05041c20508114850364420540c008071503544581010091625494401c42c0d10b4040c9010b014440d058035000d44043d11034070009002164800e46011a6580d060b50109080e80ea0600302000c0035405501030061503504841d001c4018 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 271310521 1250 271309271 271309277
    0x5031506070215090616030c150501061403060f03011e0e010c0e0f0118060e090f0112080c25050906040c02030307111509300d0b01050706090804090c 66
    0x220119800060041c19060011074076500001000015071720384009036240040c4005003848954910f05001d0565018243c040b40c014952842c0606020300a00c01c4a0689800c4c3d9503080150615031002d010030760018013002d0f03003e002002c6c08541c0d65400d000b6003010000e01000070440140c0205084192a400940301c4d14030390500d040c1550580c0d0100c0c015820b0001151380384010007501006848200025082042d1420600e0020401c2034100746e1a01d600182a40d41030711030354600b0034145808a0a0048a020240c011200000704040f10041e00d2100c51840030b85101c4608584c45001046002c9a140b0707481a40403820041c03031908100983c1c1c031071002c1e81c0a0020200c600c00003134403440010301c420180030b584420742280150030044c8041c000c1907031032801d0301410001c0350560b03102c0b0b404c1002d5402044030001400484003540c02e185040c1d601130310041c1460440d0b030700a006082c0c048401810003806200c0760300481c030035000741c883e0980142d5041c0c2c1e41b07038140341b181d005980c1605441014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 271311771 1250 271310521 271310527
    0x905010b0a0f06120b0f10030e150f010302090402150a0206011d0423010b0303180307171203040812070309031b02010504090203040c080d090e0f07020d030b0402040503030a05031506 80
    0x5003a001528410012804440005e105903c240000c0034114100340d1244c020b1080c400f040c8541e60541d1100480c241900100c640c0c03001c1c541d032062845401140d900d0031600c0034500400040c2000340801d508248000c01c6c80c0303420041c00380129078a410400d03517a00168080001001103884e401d502c8032030741e03009010450310303403400d034440c078040580401440c01e100139400600d84801e00203512411032040d00a040e6a5501c81c20316141c00a2440107030154400c0c042c4142c0020a1202c043c1f11501c84480d0704090a9001100080c0d81e100d03030002001903580ca00f081100c00c0140c01141c03003030351140003e600c0000300c1d1009418018681c0c40d4406484141003405410440580e030000e0689045076025080540d403075131903245c4449202041d50240402c3d1248500ca00c8031550000740c08019921b0481103000907503241c980000c8642000c0e43d0325000742c1c0116000c0074589120780c003d008080b801030400752174682d50700046480c542c0082070100008001006103c3da011140b41c20940c141c00440b081c0381 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 271313021 1250 271311771 271311779
    0x3230d0e090a09120e060f0c150a050106080f04081b1c09060c0f0203100203250504120b060103060f091d0a0512070501060911030403081b2502040905010b0a0f 70
    0x3906145042d1030409000f8100030b450901e85d02d07070080300c1f10001c0d40d0084a03240d4810461039540c070b010000f032102400f2001800145060741e284078103812520741d6901c01090740c4600840c80c0c0300c40c3c401b51069590003020004640084880805060700300b040034010012100c80380018070760480944040401c000030030508001243d4002c0c02c1c4108030380c109194405180d401d20002e440e001c03201080c01901800403081002c040441808040c64010900c0954100d201401c0101d42620075070003400c06109010f0104004034000c5c00459a01a506040c0080d1854a07130080390140700f05640f0200c070365616084011400c50100002600700380c440402881448000d681d40c80d00c074005103000c5042010085071314418032500750050401001d050804001442a5450b07205160703008031000e80100345500003091504c411040c0e4280404610040c01c3d042120b0522002e007884450342081103034030f04080700c1c000580d845100c4c10314050310a03000062012001d105000b07030000382c1d41c407209001e030f0703d80c200300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 271314271 1250 271313021 271313033
    0x21201060305070b1b1005101403060a0902040905011407030b090402060405101e05130b160b1005090903070203010c09030507090f09080c060118020702030703230d0e090a09 76
    0x582641d40040c544d0b900c03031005000038130007118141144070151183c414500b0000c229075000c5405482c044040e07211054070359002c101c826505481080d0183c0c440400078004003c2c0e6800300c0d0400d44000e00104200403581c4603182076420210071085078152403414441c0032901071040f402c00302020350703a008007440c00b50001001c9000c5ca110b42c40c01004c1c03000003294118030903882d811445000e03000c0c1690480c0040802030554010100500b00c44003a007102280c4014130106442c403c0c207a40030b10350381c0040a039580444040c005403800c1415021802c02045d070b95140d40b4060301c20148a00116260b65040c0101801d507034010415078148000d52509201061010903520156070842202203035040d41010f04100508250038058100d24011031000d60008004c40d4587c105c17100b8101c61590000d10804503000c0b8401d50750300a506601a00e020000124000003108220340c00c2601e400380305003806903c1d030605008136940000201c0c5240d0480c254680f803001a0340010183d50200170821456440e1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 271315521 1250 271314271 271314283
    0x15060a03050606040f021608030610110a060c02070503030417060115020a0620030412030b0103060f03170f03041505090d1b14100b0406080c0901180e0a0f021201060305 74
    0x40f500403601d402480c2036451154044407071002c46440e402ca891401401c103110190016103525200315160b4040c0000e5034400d6104400d4841010080d0940e0a22580e030580203180309103910301540640c0d0f000082a50701800608002c05001b00c491800d1006031003c00c0c10484140c00200002011903040e124041c0e0020743c0c418003e41c42180003c40c0030040400e24a5403200c240e03011041500041004100004540245c2e10001603450600040004a0054054500c1400303181e4030680680d8080010401400016400b440b2200a10307141a803881c0d040780f0580d00850701520f01d6030a0100c120b425800a00c80c06a1180c408000303010002c0e21038000401050301c58041d140792020040d81c2109008030b000406032681e400008983c00449000d00074070140c0806074205114a107060b07400600e0010200e820100040010f100c07070040c0c1c0c01c00081d0381d16201501c2c841c0c00e4540d6280c0603d60711050410940a6440c0a0f560780004000c0321710400c05400d115500700b00d49641440700c2040000c00000320 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 271316771 1250 271315521 271315531
    0x611040330140712050c060603011a0d08040521070b0a051c140702060612070305070e1b0a051e0702090424060909030f05030106020c0d030908060915060a030506 71
    0x2c4042014600c022104850184034000f030004c141041003140322940140051542d4000b0708241c442c0c0b617881d103041508031203076101c080d020000078445101052500c00100854244500307490b508207a16140402c2c07549102c001144403c200b440701211400d402004090020400721040340d10701100118010041d00802014074211102e5070010140c0c14240d800050001e0b00c41c3c074180c900e506d0802c000940c0d841c4241c540c40d00400800003442e186460209403c419290042d005003003007450f158040e40285070050100080e20302252085070b5504801c0e000302050286035640d19241c0764040440c1e500c071200d40301308011114081041c007005890302c40026511039008028008402c25401c0c3c96022210702a40354440c1920b400e5000c100045542e10024809002e540c40d0801c600c15500256013a01c801e02802c00036902401c000b121929043c4000c0c06040d11900e800003009075140031880c135003481076402c0b000d1604410941c1c03031882101810b042c0d0100301101c02805961658980076141c00010304 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 271318021 1250 271316771 271316777
    0x2160c050405090f0d0302090a0e070e15160206090a050604290315130f0612060b04090804211202030a0f03020a050d150f0605030a050c031506070c030611040330 71
    0xb07880c0500e5500c8100100c0100011210302b00c42d0329241c80020618000442a0f82c4620b00d40c41e003800c3d0f0000a81c1c140c0f50b00132007140c0c030300c1101040360b0200100c41e04890354070346d400145544081000d4542d64080d1000300b81080711080d09c5041138005900c01c5401d0b0460b1321000b40705004104072500078281c0c64101150a4451001c01901c084659018140b848030705c92040e8102880028500d480d8800040f5140c090101084131000c0e8000300f1058840c61030340170300843c106110038032410030751403144001d1004440081010221682e11807400740c41b000840e80242c1c0000c6504420303070750450510140c40a44d49011484c0604122019100d40a4850340300d640c2941c0350030f401103030420704032048003801105148503565a500d041c0289584d00840d170103c9440c0c28800814003594049055a0064281802c0c1d40d4540c8a1602480711a41051105603500000b44000201003001c0384140808041d00c0072007259a00d04505040d0040d5145910741000120300f1440b050414210500803090344545113 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 271319271 1250 271318021 271318027
    0x1050403080109020a1815030b030a022d03060c0904050603070521070902130812040f09090312050906010f060c0b0609061206130c081c050a020102160c050405090f0d0302 75
    0x801c1101c810058490b00d8688103820301b8080f810080c44c1600d150389100c1030b90b05101e032200b2103051540703c0c100e003040250000c484a074605a040c0d03000c000c1c0d845000c02140307904c1d010203e000004e86810401e50340c51042520004184100d410316000305a0b10010603801409094a8407000c55032128010700040c0c40c01d0010042240d10050a00182c0010413442e1808e540380c07010281060303081c900910841030140300c3c6004500c1100281ca003034504a44184040d03a11451400d0f44000103456280811001c00440000c251200170003403007628061031b2800b0051413198141855451645015000b110a2002c0700c0040000105903110a039030049007602c44052640750b031808100b4462025461400074028141004050105004060301c2640540c00101030543c1e01e002c42610b035020780308100c80e040014003988502c18045d10080c03055807228400140383c03c40b1582c1000d4001091942207554442e0140c040000e8500b900841c1c0d004225000901600e04248440a07500d103035503e11441459004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 271320521 1250 271319271 271319287
    0x30b0f130206031e0c0d050106020a03050f0d0f0906090201080603010e0309210601080f010c05072019080f010f0506031b01120509030702010f090b07061104081c02070501020105040308010902 84
    0x30030781c0c4d142940c88024a4201d041104003100b0030f400c0040c8000c1c803980b40600000d4814400609a456190903859182c0380180858200304030b580312110202d210342d1619442650301d10a40704441105010303250020f2200080d10004100c2c030006407841d48668144109101c040d00013108a4080480441d40b031440c0c541290b0060110005803a4204120700500000250301e140100d43c000b000d0002100030480038000032000d8520b4000c01d20b01504020204049031415040e500a030502810000c0048910000e80f080d00310482d03a06400c01043e50b0020f80d030700e400e110424052848a103107045c009120794588040400e0765a82e9901c07506803030030039030320040300789901a1040ca8a1041512002d103c05d01d000706090360b881d40480d50407400100c0400001a43d288100c09180c195210501c03441d03d0243c042d11203401428000d100c04d804d18030100000590900200410300320400c40c00025004101c040001034201142544100c0c19079051100b04400a40d100e8907041c103417004c07448010303280d2003d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 271321771 1250 271320521 271320541
    0x5030601050d020d090515160f080106050d0b0301110717030402030c0d030e090703060312210e1c020106030c0b04180e030912060105042009040207150c09030b0f13020603 75
    0x10317140054040e001da4551444039a40c032032103a40c4210700d10407442002110090702252589884a05500040c02345c50040c0140c5110700014007071041d000c0c1000c00d81901d80800642141d92140c80034005c1d03032000405030308000524045009404c01030340d1080c00d510745600402d0715400002641d52140901d50b15104c03c042c001c01d10582c0e01c40001d44204032619090704040e00601039404165066440d03540800d400a11803048110709800740009901c681d255600410080d208241007050b49008800281600549980d1030013540011340c0e0000c0303083d501d503050540c6e5560031134003c00c5043d4010441030101584441e4400c804040c03c150014168009107802e42c1503005008240e640103074100c41100400d840007866030f040c0c4000301c0b8104217500417159011032803102c0d09034400401d00240500c00691074658040e01103a40161484054403543d40540c2d021224250747c55008502205410300a1003046a0211b62048910392212081d007008503071011000002c0c10001d200c4c281c004001124200 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 271323021 1250 271321771 271321781
    0x6030f0209070903061e06050405042102031605071403070806060112022107120b01140a11030d050103061401030506040f050106090e0f0105060109030803010b130f17060705030601050d020d 83
    0x17401c603908001903c400d00407500259001e0b00701020311802c20a0128203898148039181c040da0b40490300d01d04199003030b00002906008c6030b0020b010b60000707001c1c0109000300c40300ca0820b828491400f4040c920b041800003100c1d0385100312406e000360300c281414082c405002401a4000c03000b420410705944154090102a10604c00c1c00790000c03080281d640d5100402220031030140b043c82d1103a84664012107840400c880d41c0d283c5590009901203085420340605e0b400919103014545002541d8091030f008652556200182e20312031150350300e0040017031061074484c1c50840c160030390200216502d0b50b212a6511000a000907240050001d0103c007000425072084004111052060201d810740401064032170301410b4207951079509200025080750302c11000c01003900d0703001c80524110f900307103012042c90f90000340b0620000304094001107202e805148001008201411004486040500566050410240c00103040c05028801d00c0581da03044400d55840c080e0510f03006071900c04861322000901 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 271324271 1250 271323021 271323023
    0x1e0f14060d140a0b041109090912070b09071508070806040e0f160e160f03060302040510081506030309040905030f13050306070504060503060607212106030f0209070903 74
    0x10301c0c201c20502c0c00d02d25640c00724422808031104000c426135810500c01520110001c603d400041007000103050302e000e24504d038110810204403064410003441610280d4008041034520007240300410070503220400c030106c081c0400390200e0201180c00100030700701c070001811840601c449100000d205da1220b6000d0080c3c1000d8401700d4154442c2d0300049502c446054442e201c000007240b101048040e01c07500050300881e41c031103110303401d009420011200e05103886c05100825803507000020259071075001d000d000c1e40d190034420501500d041c0702c491604c0b021002001a0103a41010406250f4004c403e60345029003c0d540407502c8051446c110713095220b1415000328281e00032800c1c00d0100f008080e03403029030701c059003180d00986944109440500940c411071000034030403c0000c0075802c111000e40b2095104480d800140210070844211403490581d9201c0060003280a00040c0304040d650300c4116400c00000f0880c060440d00c0f03500c4c4008003100b029000710103910104501500c5030407014011 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 271325521 1250 271324271 271324297
    0x1503031207110708073c09050609090607081605130b030601090503160909020a080303150901051008160e06070f03090b160209060105041505041e0f1406 67
    0x60300d0424000b40c02001c503200e1080d0140f20340300d40822a4440043c10409407030701048aa20a0540c400000c01444800540343c02001481c00d650f1a6805214000c8009008100c1000c525403034007900b8012500340040242035503a00070700c1400f082541204a080d00300025004d1140d5135264188203403100d11907183c0320100c2078401280040d4042d4040051400340740240d035201c54040e5108101543c92412810400460705514030070000d50401d45d00c000301c450710242c00c00c00d0717960352262080e041d50000c48103050700032144040c1400c2c510301408858094076040b02d14005c9082c1d000700080031000b0050506c800e1104644141008a004410284594070000c0840c0e584840c213240a00e103614400d10110702051288501045001e251000d40b1958800200720b0b0015031069002c001400300e015101c0c0d41405030400000c940c50a074495005003109054503410f580c3c61904001000028184c0d46540ca901c191240900210440c000c494080b02c000f20800002c1c198081c002813880c3c8107008103410303c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 271326771 1250 271325521 271325557
    0x10522030e1903032109080f070c0b07060f0608030309190606090501180f020f16021302040b04030b01140108060d050c0a120605060a0f0504111b03030919020603150303 74
    0x2059417200240f603c441036041c20b20b020002400c404810340d002d8800060000f4014080070381c0d400311081c09404824000d03007401c4001aa0385130340401580c40740f0750903140c06403221104031340c686080c06183e004008810085140d032400821590f1611002402c12980b840310b10400c0007804030035000308000e05400c00080145503540c01c04442c5d201c1c141c14003141401d00749014403014090b0b9109991101900c580d00c1454420301041d000000144900c0803a401400b2480c980c0c0c100103184060006080c1500700d00e0380c0c660950030480192641680160303419400002c92a901d640d0042225802500581e1420340260303191414a00b4082d6202e460703074116004180000301181c000440040d01ca020784020407070b5840319814400000140e00868600c0c901f00301c0d0800136818036a211404030100c100c4c1250511a040c05840c80d40a4501e074800350303e610100178080851004d10000074000100390181e07803040c15541c0030801d940001892407080e07010025483d03209403000d20484071640c2c00498000303c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 271328021 1250 271326771 271326773
    0x18020408010e06011706070813030512090c040f0b310911040c0c051c090b030103080a0e010f09090507030e0d020105150109080703060c0c020d03080603010522030e1903 74
    0x55120f41c24811004540c54110355903500c84404100c1d1400341c0360710b641e981295a22440000c4050003018822020072004000070440b141580c01c429000e4028103000d07140c1030f8810070070081335910001b5052400ca02c0e00720b50b0000c07691fa00218000354202031b22200d40d04112010300d511000380c100080300c801070415800d507080200c00203038200701480071581048483c560520032141410000001407450740034200d0403104008035415418001d10a2070322400050b01c500f110050340d042a8000c494940c4049040908690000c0b058510302d0401c2c038000c1c143c2c0702072010061120303c0c0d5220300700b0019641c43c041002c1500ca41c0080e0b080c00103d0b4201e801ca8205008024003c150840710300b14004480d2801c8041c0703600c10301d12a000c907900d4400602407103045486100042202210203400e110031564500016110443e020f040d080c020744800d0181e00c0c00c43e041c142911402000100007145610000007001c05030764a421225070140b5088040841c0380012460f08403056092600c4000f074100000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 271329271 1250 271328021 271328023
    0x51309020d03020d1709030702040f0615090305011a03101a0a06170108010e0d122c07060302070807030c030201060b0c01200a0e0111030708070b0601021b060418020408010e 76
    0x196040c1110742e10400ba1840304217441e4010207003502c0e050031540003000400c02600e0107800400c01039030b80d030f20006251640d0700c0c180c8a80b00c40144180c40455103496080062000070300c1140b042c2090030310651204003075840081e8a4000d000d20035030041e99100b1364940b040c91030b0f144002084074081c1289829586030000a0a8500340752031240401d0030740000440c5000d0180646280e04240c10018280349003850320035111121640704861203d0f6071000c20046080c84210102c414005141c2c00c0e17141504403018190600b001500301c2014540100841c3c00064802c001f00d48010340c240c03804c0a601040c03461704a02400e07065002e41c60111021070309102140040d44005082060000700075005c0000b10110460380c06044035900101d09052403c0d00c1e554040c03034a082120320700c102580d14042a643e00d0380401d41158009a500840400c100070103075804001c00440c00303580c2494864101216000240c56201c0c0e07004042c0803021924002d0310480040c2c06035005011001c00910080214000c11 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 271330521 1250 271329271 271329283
    0x30807060f110c010c0e01020607050d1803050a1704020901050d03030b1906090617010504090c0306051302040b010519050a140408030304110d0f0221011d0c031204051309020d0302 79
    0x24000b15440e142c1c00005d10703401003c8080c450f00c41a00a440c284d81c40714420b90301030b00030002d00018282c0710780195a03440e10961301d1112043c03098803003035160003848200600b1013031208103a08444191100b44170150360381d0031030a070465108541700d114600c0c10b07140440113031445544050304240c0342c040380390390400307000c8000059404540e10100e000e1b9070b5600440b00e81951108950701200140014000f82c2816040080c00b54040c900d082c00c41507403603070707035034210b50044841c0245020806c041c0400c5103801d00944145200034a0444e060000f9030511603d00e0302c0040314142070100000b5040e912a0180c009246288400005542c51b02c3c0d41c1c54405450ba4403c07230b0119032204012301e944c1310320318081c050209030326000013000c440d4015540c280004400030b441102005c508190b05c0440402c002d018120585210541d260002d200c021885803511031a0225907200e500011150700c0c2903503400054508455040391000c24038401e498058005000d0141c02a4016220070301117014180c0010780 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 271331771 1250 271330521 271330537
    0x3060906010305210301300b010f0b030103030806090907120c090f1107200409060e060105010509010e270c0c0c1008070509130213030614010302010207030807060f11 73
    0x1038891140c4195880c0c4044d03100e403206985448020310042c002c42d44040181184110150340c2054080f80400c007078000c0b00450503003203505540e03400050003035101555100000703052035403d00342154110364010b0f100c5100240124040d081081c00a43c810b2400c200c00700040c4526104881250786a0030046650341d07090141250340380c2420000500400a407080000d0300640c0055141440019030b40e179100d1155038203c000c0c11040d0105000c18981d1030784500788100b4800c500015030158411401801c1c103d0503030102d41480310500004070b569801800745030702c20800301d0760040c0100c40c002d109464511607040142d00b0f001ca42080020140c0c4481c010450950300342c048544914454041040b288010820000041d064502081e003d6002d14058003000800400b0700c42c12041c2060880f003241c00018150040901c4940c0c104184082845a481c1c095042004400c1c0c039811500043d564400d188070003440c140340000c0039003c0c0210f581c0400580652600240110440c0000f04000d075081191 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 271333021 1250 271331771 271331773
    0x41703010608184206030a0b090c130605030118150f090b04050d2a20030d0806130506030705060a140a0309110301092604080307060f05010e0f01030803040201030b03060906010305 79
    0x8440c400711404e8050072882900010010020101e4682d500d04c0d80c44000341c2000041d2080180c00d440941d100628212200c003502800150145080101800d54800c1d107140e46c41d18265200700d00108100c012000c00c9007400c2d035070101d422924440114010900388030094503820140081c4000c00501140e00108002555540301203200c450300303142c880c2e070300703802108102c103414078021000204050045042c0305c24070a1903030141420140800d08101c0c052010300c3c0012109002c1107254604075000043c4c4507212001006103250440c086659080103005240c4207081c00703d1520842c42c402d100c0704a0015285401039110341440401501a20001808440030544800302c04050f003414826451207540000c04244c001c1d8000c00031342c504199035008403405580800011035003c1c003c20060200c03e00c079400000b01c4c0c03c50403440c4422510107802c001c1252009400784204c070000140074605603500100265680e44651005030002c0440e0038003140c05004034020484503103c04250181202c0c0a10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 271334271 1250 271333021 271333123
    0x80301090605191d040c0b13090606032c1e01020903100c0516020105090406081f110406050f09090c0909070207051e0409140604170301060818 63
    0x8211281c80050070301402908601d03002c03d841c2841040c1030700031780080c06a015400382d591190f40c440010b50100e10840c0e0a00d00c01ca10030002d4043c0e6100e004000c0c541072a003044000c103501c0650185020401101c100820044500001da980038003440c00712000c0c111541111460392043d0314042d400c08000c49100703000f00c0841c3c004181440c021410552820b42d00d0038500710307448403401715414000300141d04002e005d210500d00c0f52160702c612400341695a00900b44e00180c10340465841480c10f40400c0c0b071a00b80b00c003002c51003e004064800b03641c62400c2c941d8880001150406482c0a902d4441c2d43c0088501d0038008800c000b007000b84200c08081c0d955621a94907840c090303980301c034a0b02c516900300101010f5443c1c006e00803280c0224520000b800032541a540b03442e81080580d9510405400d0740011050100700b2104095042c0c1d01c402c4c90340403d003150701d84507020344503282c001c02d14814a0711035079800e00410800c0c8980150040130b543e0300c116514182d1011880e41d00e1040300016400f81b02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 271335521 1250 271334271 271334299
    0x9030903060c090f050904030c05010507090905010f1208030a1b08010806130b150d02030706031b080f0f04290703060b1201030204021c230a050601141303080301090605 74
    0x180c004081940c0e81300500c1c1c11141d1800c400e020350820000d006400700f00c64400e81e072000410a00915000394130b16540e03041c0380317410143c1c1781c0221141a4130100140700740302e204000380002400110101500b1406d01c40d241c2d900c4c1141070001c1c024122215141401049820503801d0300500705906948828003100c1e9140d550081c0d803480491000c5010301000d5103440090740109a0028510302c2c03ca01034401e04600c100e982c0801c1c5048015003014010075110618000303640d0544032221540c1940c0d2a103c6210304160701011428280a40000500140f650001d07040c069a182e0700210990084900c20f02e241e0b10300014007080380d060f00c5860010741009070002e1801120b00a80d00e01c4c550b100c0010003681d02e180d00b0030000394001c50b108455500c5084400b1140c1400d8850615441c00080038082c0d084510511484001c01c003c0010185c01e290909020a030b0b644284c0d0081c9608500344219a1000c000742219881245075000601485000001103a440362907008441110401e40710141c4603042 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 271336771 1250 271335521 271335527
    0x12040b072703142122080607020f03070b011a04031a090609012a0c05070f08120406170601090f170106051c0803060f0405070302072001050f0c010e0109030903060c 72
    0x1007011424013801c2c5080403039181c0510390050007002c034000400c41c1034824044010f03039000782c0c0c0e5014030721030340000007082841a014011070b0071404824026610705100344c1e480d040740200c10b004d014207032440064503c00b00040e0f8421240555003000d094440f40706100360206500608448903d290701845001c241082c6c03050040e400c11641a0480c0800c013514040900071001c2d00f10306a00410031564008804500e0502000c000380c0312609055503020b0500c00c0503442c01c072040b00400042c1c107041108200c003e42c000206000c5200ca0318200410352640c0e00100c1d130341c1d9a2904007121400c605900010781021240c4140c80a0342080002d110080d41e400c01c02c400c1028101c0030f40980c58035904642d000130385040c0159400380d030050030b00c0c5168102d140801c003142c1040b140c075000301350f00094038010312070b06120100754892042215210183d011000a1060040801030f0400c44004950407048020070b4200c840d2034000d05000304010f03c0740d403c0c01016110248010f5030010b2410300b95461030346c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 271338021 1250 271336771 271336783
    0x20a05010e1302032a0309060606040b0f0c0a060510060908010c0f05030a0f020301060c0605060a03030203341b0e010602070513090b0f0105030c03010212040b07270314 74
    0x40010508401c640e0350910203000f80d44000c4c070700e9000e000400c0202a060802d00c0c041c80e00002e5160f4031a13101e1400e1b01006181540140c00305109245c144000c00c010024901194000c100201e1990307201e035680d040403440c0000b42e840040c40c4c00c1c280020080da8154540c1e850088603004c0d9554903040e55201c1515080b02e914005580014101148140c82103000380000c641090740c078640010b10f9510072852508070f800a8000c0c20010b00007603100d01c140051401559085602120681d038450301d0740e80c020323580c0d11500e85503840c03500306000302c0409280c84a0501c1d11008036140707062a41e0030245014629600042103050740141c07842c43c00309203285031262a60507649690000c0030350307506041c00c11401088a024030f840c115107501c6c0060010b00f03980300a501508040c003250380030354102804c01d4107045100185500070303071052102d40005c071229041287c005820240300603864491241c200c030822507a0320721042030040c0b56132081c0350f08070101d51403049a000350b0032900720312015411207407244 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 271339271 1250 271338021 271338047
    0x10b090f0603131101050d020d0209010806010e0d02101202030f07020118030807230c01060302040b030109030c020d020604050a060206040302010b3c0406060201020c01050903120117011d0109020a0501 88
    0x2094500c0f06070005010102c444010a005041090500500d402d448040c2d03030240000075030311500030510002d0383d41c20841c81034001000b42060841101c007240410680f8a0089002c1c0c421500641c0d07029115000e0010701036407005da00300540d9a45010110a010014161003a40056203802030106220000e200e65000b11a40342e41c03010410745548904640134180d9490000340454800e444104180c14600203021801107440082010b9180d030041000700c0c1d600c0102540240d04000320030001a611094507845194101c40e125062461800410300c54015600b05503005015000007051085d0001500c07481303507111394001d2080081740400c0c00000d0310381200d2103144072480e540c50b00504540b40b00100c2c40100e00030b000c0c9041e090b10300000701070700c1c400d60005c07026035800156001ca001c820f00a03194080c400d94010351412800e1610924907410501c00c3c580c485c840c100c40014900000e4025150341010420300c070200c42403204909000381a9190f0403440780d06000c0000a1139405000c07054481 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 271340521 1250 271339271 271339291
    0x203071a070b04020118080c0f010809070614040302060307090e0603010b060405010f020c03010516033605100914010c0305010602031b070e040303050403080a15120501090605010b090f0603 83
    0x40d480e40d5841a0342032003d00708a050040380d400740008101a02d143c50010601607006240c4114081d0901032103a1503407001f14104010901048041c1000042e403030300b202c0d518608080d52548408441e000390195400c001c0d840140041807040141c0c0c450201c4081e030780e03401041ca803503403110001c00d4200e480100000ea0826000d02081006600901d0000051002401655044041040042d00b1904d04071602e50901c0030281d00700084035414801c0040003c503094407800303410f10070340a01500915040724000c6030148a0404000c1100c24070003041880005c81091040300303224500b04210000c0b03489542d455600e070510001c101c900c6400360604a5080b034000e585003480028148441e13035081030b0ac800c0309101d61880062024140020203201d680240d40026450601c0c1c41c00034051040030300b02001c80c6080404500344070901c2c0038a01c003103804e41c545002100701d251500d1070142c040c80101415507481c06000050300c01002004000d2648102c42d00141d904803e820080706002c261603001c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 271341771 1250 271340521 271340527
    0x130602071410050d0f0c0e090103051203040203030c0f100b040c0e01030b04110d0b01260f0417070515060103090809040c0c0b07050a02161503050c0d0e0601030203071a 74
    0x207503007000710785401e482c00689000740c5003401d80001d210603070307100504240d040c55880a4004083e03038015011a03c1c54000c0314075130000c1d49540c60b8070741d0300d4410f9040c0045019001011600b150b03000c20460305c1c030710070101c261000c41c10f69034003031030301d4941000c0c600021600740900300d2480e180c240300d010a80c0f280c5480f0040d05e06900d0004400030480d000c81d0b160420350f1403001c81d4648040001030510031802c04400f2802d4030240000410322250305030020a0403e46950082001640c20509640495040c000c864180e540342030011181c400c40040c44818900000d2100c00d1020200300950010b0404050100c10740f1070300c0046045940540c40502491000d124845043c500368001403803207013040c82c001052340c480b03480340c0c036606070152600008588000351000015405010803800c0c8240b042c0900503180c90140329010120180e40200304055460001500520700340095940e103104900701001541500040113980b668207001c182d10030710810400003503104414101c002076801c170145c9281 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 271343021 1250 271341771 271341809
    0x1e0e1c031e051e28020921030a032309030c0f0706090303030905030c03210a02030408071e17130f0f06050c03070209040b010302100309230a02090106030213060207 72
    0x512000601070f14200c0d00c030662115126208040400c0300c480341031200580e0342c411082000007e0301484a80312218485500340e0309229808010742d2800d03500e5040209006031b4032603007000404c1c440304d14a81e244214400384007a001001020700065242c4204880741c00600788810750780c95165104000010790000c80034800039100380c001c0b418003841079046904012403036a2150840d0040c0c4603500c45110f444c88110840181900b4943d001183d14030704601e10f04003a129031400780b25079034002c0c040c0a41407510010366480304010b21300103074020401980e401100010040994092204004503020380300c001f169003024807201d50b04a6103141341c54498149005400c2d107203038100103801d4090703000078070000c07000d0384811580758450f6100f41e04604d400e41c1144100120f200a4110302000c0518020308940003407003d00300740707404a22003103030b962440614016051800d1420b6030003d4028040000008049400d60003400d40448040f109613a11500c40300101d0b520449842080302c102c01d0070810903 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 271344271 1250 271343021 271343071
    0x1704030807110d051e01020f19020d0801080627010e06151206010611150c040924050910031406040605011715071b0507090606031e0e1c031e05 63
    0x1841e50240c000c0054140ba400403140d0400b82c1200b60136081c0b03940411027000310250f050141203520b81003800c240100c2d5043c407410313690f1080d0040000210a8505078001030074400514060700c1d132021080288040d01d65070070b1254644200380c800700d4080420b0541206903280440040020011036401413480340c0c60714600701d44201c050101c04026018401002640e51842c022721480303414400012a40c4619010864003184c084a88004036500d00e0303400603140c1c001000d2050101e400031103050311240c40b0290422100c80107039000810f9403103021020a1641e0300411110f01c500d001328020011a80e0756031a0021100c0080c14100058002d00d00c0c0c50710118005089980150f21460076403400c495007c845440300d240307900b050b9801c1c0d00500007006082c1c5079028030300190000345030500580c624010905980803041d0505484180c880c59100358403801041a01b030401d030404920b44211007000c0d07001e0000d00c401008034440700720185100122919034083c8a018003514942c2542e4505010400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 271345521 1250 271344271 271344313
    0x804020402130e040c03030f030b101101020f1201031e05190615170d030b0d0332040e0114010828060b0909090a110d1704030807110d05 60
    0x52215102c80c0c480818000c1010b005144580e20601d04d1036021819802c018005402e0140d114040504106e40d5010b241c80c6d001e6005851388207030800d0000c180782100703482e00ae030241c040c4200864402084910f40340040031800c0c0d040b24050491310b0404a00f80b0040341d1000a50342d0082c1c49036004080c83c40c0b1203150458007109041c001c0c200001c0c6030410b80c1c0034018503121a03020400c194848220b002981c1014490307040710707507560305042140b00c40d18030108008800b44070380681446200c951402114001c0910103600303404140ca000303d60701c0c500940c0100313030b0454000c6840c0c8040100000c02d02c4480300905135034002058680b819690346d4460074803001041c80024519880403a04003094005060289038083d2901c2e4188548459400041c001405401800382241c1d42c070029001000c80c1000940f44040070068440e504100490306000c0c4130080c9410030304078000c40010b030000521000e600540f0303825100b100b0303d0018110316400c000d940e6170720100c09040c5410810048510800c04201e07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 271346771 1250 271345521 271345537
    0x1305060c0601172e3605100204060302040f0b07080405060304080d0905010b01030c09030b012607090506010e0d12081f091d03030f070f050403050a0c05090a020405010804020402 78
    0x12581800010010803130f402d000050800011600c41c88100562401030003110b6403002d0a250410090ba0745a107031040d40080c0c6000070008074070b40801c1c1d405128051007035041070400d00710103541c0c2e65641c180040003540144030b5002c440c0c00e00c03080440e8403121401100c2c0201e81256800c3d05040c00c004c2044110390000d031044810802c104030745100c1800d103019411009005034000200400346200250030b0f18000c41d154000c1040809050000a058904c1079055911005d4808000c0201040840d29021303000300c900010700c14494005141103107034100d50f208000c20b030303240c01910310f00d20103002007001045002098400400380382d40071248640025a030000c10038484400a144200a8481241c4282c00424100b615500e8004c20140c1031040020115200c00040d0b20b50700d414400c0ca541e54101a10240811802110f1031000e6480389043d203000d15000019150070311900c2c5401e152945061003074a0050030820000303131104900e4425101112030684900e0795998459080100952024034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 271348021 1250 271346771 271346773
    0x615030f0f071802091309051c12020309010e03070507060f05090f01080a0b152502010914190e0f010803090112050a020403050d020f0c030a1208070210050c1305060c060117 76
    0x81072505071b44626a040b55000c5200740081d00760054103050b41080300b03100a0b5607028402980c4540703c2540300c5c0488102d14a0408010703100d496040c901c82c0504200382c420b602700e200c0490070f4010301002141071005c6442584500c200085076030810341d024050507010680c070441030340c040106540074188480d8070241c1040009542182c0340d00003180640c00c50601c00d16210003064601c011036009408520489400407045420881139000801e8040240650121400e81c25521900ba0712021281e2402d4280443c62a110315103e8540100c0e44804807510307020b000b03894000050103d00401160310315881070f034a802028002d0009100640006010700e10351540c00c200000100302c0500081d0130f00c0c05158080c00c02685002406842d0a07003048440b4400d810402c0503500082c15003928001c0f81a10f402c0540075580c0b182401c0e428540d204003030b0360300e0500785001c011503010010020683c140e50200f00380c80c010346440920229001e8500c160120380c2c0900010700c00b2000f81101d4965000c1d504e4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 271349271 1250 271348021 271348027
    0x122a07120204050411120a021306030b04021c0b040807020306070e0307090e101503020a06090b09090601120f050108070f1a030415091a090d090b13080615030f0f071802 74
    0x400300d44064826a6801c185401c1051f4031400c41c500750764440c0031070071403e205001250a5403912026400c000d4002441070943c1883c0300740c2c104540107140161f641003040500c043c0303002d00b003a6119a2241404a01c40d0146600080446005450040240b50090010034581f4240501000100f648500a081c24441c0303107034400c202c1c0d03a40c0c010340c51103616105544030036903d544140000d5134014cc104a0520495580600400d418a0152420003004461031f40c02c2c1d0b2121070040e43e0182801c1880d089560500d110303081c54405603000241200e004030121100c180d80c42c40703034400c00e034414020703202001c59074070a8803040c0300800046c0d40c00070f001d84c0300c0160039004030b80e80804960b0b003130301e003114000825034001e00d02c0d111040d40c055000c0045c8001d003440300b1a211000f0700441160241850101c4045444640c60b00c3d141034260203015072074101c50303032801c29881d41c0642c1c12090600a1091140b8aa640c1c061400410b07120b0011002c00014000c2505102240b80803240d00803038034202e00d50034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 271350521 1250 271349271 271349303
    0x230c09030118050d0201060503060c070807020a050d061413020d1106160b160306050f100516030c0b06010203090a0614070c0b0702030705030105130f05122a071202040504 75
    0xc52210b0540e20721440080c196070880b41340184c2540e9441e8040e900c00e400c604100b0245052000445d0b0308658080b606581c0d466251002070102816904000e82000c0c80380500000c000042d442854060854514144580e684035070f14014501c01d06402504448414150750000e050342e082041c1941e0001d203031500300940e0700a444c04c400315490040c0c03120f003020414810826130303100e9019a0504149828003034a400c01002ca01c0d6000c020702e08500400184034203000c0140b00702e054500d01d041250206114030658203004001c484806400d40d01c00d1400f41c0410313000d41c000001c50b00c0e03440c8040c00c6401c0c1d5a207400e509981400300d1084401d0030481c1008004001100701101ca005402140c00894440c5043e0040c1480d0845a0704064001c1e03250000303010480c000c0c1260029180c0c2d005201142c1c02c012490828100b14001c0900b2100300c0001c82c4040c100c3d0a00d072480c03a0582c00c2e8000c0048455040307000c141d501d524a1042038001c65444003580091305091700426401070050324400881c00342 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 271351771 1250 271350521 271350551
    0x6012909030a0203060f04060b06090105070803060a1a0a02010f140711011104030b041b0b0910020118050303060111060f040210020a0b010605190302030f0112050a060504080409230c090301 83
    0x1c0711b11601000c2020100700401c0080c2c03080b01e0b50404155015070420a00d0710002c3e00c14420614054042007000c0005411640c0d0b8403460805402802c1e0401e90740080740c0051a45504082049009942040b42200010440d40714601044c541200e480007030b500d503000140c0e100d81080701503807030554803103849400c10380b0341070000e1000b54850201441c071803505050506070489000c01d059180b54075140108010400c6005480082008070b40304030400825640c02da005142d86001101c548141c3c40d034060502c0f2010014612505003038030b0302c0107294076401c032550300c481d0201c0354161020200c101050250400d48002c503880b8880d401100c1701c024250300e5441d11341da0300f47d02040c00140001050000d80000e1310040c0464516420158110b051000701c24001039414003451080e880d5040e41070301480010031048090b030350011001c205600b40b604202880389d10500404401d0350030701d00d01c02c142d14881d6190810b0603e400e0151441c03a00e85021a035460317400720070700507810340d00d034000a209502 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 271353021 1250 271351771 271351783
    0x10030216081c0608030c060403030b0d0605090607111911180a05090d030e060c0c120f0315010806010f030b030708100e100605130519020a03020c06012909030a0203 72
    0x190b01095294000d0b00260b02c1d41691200d8005901c550014000b010039544005010303030704a54181004a00d81c4000e03000f20ba4101c4080a0281545040400744040c211000c00c0ca1406000b0507912501c80094040b4482c0c1c0c0c55840861074440300c40c15145010118458200b01040d100d4001d240e403e512041c2c8005007401942501d1740707240d8541c0d44091110418041001a821150300c0c2010b221070211045c544e6141d0100411821807480e0006044103509810710451080e0040c5031000e648412040900c0d0f080750b001210f407401c815034425040000780d806050171034401c00c0140d4604c3c0343c010043c607044014140e2055841c1d058401c000e40411448400d0040c03106030550004005645140c40c2c24071443c3c0541a81c0d00c0841d589415814095a200c0d081c5260311503660400204198a48a05c4000c0ca1990110003007100391000c504041c14030f81c5500103010480045049032026600c0b0030035000c0040045401d03001b521040e03014428066143d0000d011880001006d94281d140c02d0340100342070103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 271354271 1250 271353021 271353037
    0x1a13230621070908101805010501080a12050418020a1812020418020a03030507080403020315180d020d0c06060e0c071a093705010c0905040b1003021608 67
    0x584001071180c10300314126106a0002c1a89031800100d8034040d5080e8450281140d214441502c0364055601c44119030580f184241d07216008101c50344c2e54002d125141c140503841150041c1807001d89030311251241060f103041d1041000640f1812900b0308212000303601a0810304140400d10b050300c00c924100601d030304001c01c4a1107403040c10b058030f403040100300c030740341c441800c109051148000050b0301e9291000c0250f0307906007089903846007142400b030914042c40d0700003581403103500c008600c05092160460300480b011030f80385074906031022100d9282c0c0c580c07030704c5100141d11100548100e180301b168070b69000340c041e840c0002d400d52201c004c942a404110b940f550780c9500020520304200440c1d085224840140880fa0b00d10709040011a031036544100012000b418070100181e0242178001414048440000d071100000300a40b900f14064540317080c0300350102d600f01800058509150040341d0800a00800e0009a00c5030060180c0c000d4204c2e00c0a80c400151010f0f20400049000004007401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 271355521 1250 271354271 271354297
    0x21c0207051507050304030326090d1103071106030c281107060806090a060b03070c0201110a050624060d06051302070332131a132306 59
    0x2807420a010b000e5100b80940b48001c0503030701000350401240022065a0969078140b6105d00b00c0404039070124a401605114501070f40e0500061007015500002c04038074014403529501c880c00120640e05880740152035018000c030340702d117148402c01e00e030100046a0009a0281060a103000841e1170b40e0100328150000d107d034115161100c0d1000c1e008a4071201040900d00181100c900708034005200d20b5016000341e000e1300d1000007040c503641050700404040c1c1111501c0507207900d0302e104001c10071481030300141d02140d014500310042c100d0224150030450b800600400c050b807140a4103a03203c15003800c62102070104005c0c1c000c501d5031054020419400c2900c0c01049803401c1104020007164458250000c45204205c900002504900803490408041486100000b8501206005400b002100140c00d1900159440302c0d4030b006400281680c6068442481c1c0c107001d1015030090b442000c2c482e0060141900c0300b080582c0100c081b00b00110340c80640008042413060100300c2e6900701300314146003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 271356771 1250 271355521 271355533
    0xe0a1413020c07140a12080f0a0302070812040b1807050607021f020a0b0f07120209030a020405010f031e020f10140d0e0c03060103120f0905060f03010302100509060306040c021c02 79
    0x36914210010001510307045881c018100c005980711f841d42d114001c145810540040343c000d004034003a506981181d900003a003143d03100c81020800740388000458041351203004d80c0c400310b195003006080c072660380480b80d00107040090919003007010070b4000d581c1c102c0e40000c00c02940c060f804082708084d04200c0c0c940c3c004220044072340c40c10341140900103001c040a1000b080401c1a00e42d4003440c664542c440c0d4201c016a10944607000c0303800e00641e0b2501940040c20000001042c0c7d00403815042220300900600403109174034007521085201403100a036201000809040c41032610000c3c01e983c88405040001c401241e41e4000d080d16007120710300002041d82e811881e94100b500740b00c40030380f8090483c05054203605607602d004c5045040c10f5214108140a007001c400240a500c4a03005420001d040075100c0c44411030705a00d13a4024082280a2450070002c2c00b5640e02a0f4241d0309140c4000b010541565662001c2c00001c1102c151002c01b107100d001d11544080212011420741c1c3c3c1915405800c3c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 271358021 1250 271356771 271356809
    0x31106071401020c1c052515141803030c070215040e041a0f07120203100b0c1b0316030609030c08161202070f03080a02010b03030a0f0e0a1413020c07 66
    0x10b0744030346044405d01132000400000388540c0c2100140c114254041c07040d9060221541860ba42c000c003a00340500d2010300e02500d03c60340481556200344511440181005034640030a203080c2c881c003068034091604203091154000501c3c20701c50764090310910440c2075040582c0d841002c40d810720705071070948140a019420250420780c0724403c1d54000c0c6045070655081c20310300d100410f10300c1221040c949036503001c00400c0541d0700c21469400200080c0c051192200c1289032003544519100c0c03110415080b0f40003405003d804e0108070106002440082c206140380307191140f0011300340161003101000f0f010141c540008400c14050601c070040e264225402180d14504207240d82e410a5069040d0f5200d944204075170f010144603131080d00e92140030181caa40c0d549009901414803980c0c1c080d4035000103c1c2849820398041180e01846441d82d44040704044090240000c01c02d050141c0c007140c07084031f074170304210f41040c9001080d4000f00d01c500514120051000d030782000c1c01500304008003070807991189 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 271359271 1250 271358021 271358053
    0x120e04060504050601080f0406020c1506040c02010e190f120c050c01021207110a030803070819020304021c0c0e01080a0b09010b0306160903020a0306021909031106071401020c 77
    0x500505010b031401c200b42d003071440c00a0800741c001001c1c0f490000c81ca50010f0301700106030b01914900c441010448498040081c620b44d115681194030078043c91400107020b84c5984140142c98143d83c040740900031020112b0103030119070464500543e068200c0041000001d00710740800b444202e22580e0b089580a00c6140540c01d101101c0007107070440d400f100c80f5256003800c040486101c160f2001959621403220008948510440c3c0d00150400703402001f080002e40d0002007242c402d0345140821800e03c00c0b02440700c0704a0000761340c0650041d62030b0ba40360000720346c100400d24145000300031206805640300034200b0341402c26000302030303543c1040c413105c000c1100c0d001100b5080703203481d4020b1184070070800c0400c0d174641d801000009005a1030101c0101740d4016070009003c0c507005401c606200c0d40b00d040c14406548900c01c200f49643d401310b0344040f42c5109030030075000e0701e03409640300010340e201c1c0040000941000b50256050f0070302d9045000914401d2005008143c0204060002100a03035049 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 271360521 1250 271359271 271359281
    0x6054b01021e12160203150f0906010f05300705010f03090b06040c1b0c03030806060304230106050a030b0115050c060f250305060a1508160c120e04 65
    0x81c04001100303030102d44842e20301080020b40b0410f00110b0980ba550303000d035200b050030110070010b5018007034204400248416480c40605c80c2c14000340c00526074070703001c003c159180001d02c14490301c61003111040c0001d1a003c5800940f804501100031080210005803d01c846480c200da0905a03015034800c02165070448a80c0b8043d10351402c040141c256180c44620070054010030640c8991303078502c1c020b504c40e03010b03801b02070094902501e40030704084103140800b80c88000d4001900071130b60250001c3c0c1c01d450000110782c42030303900900c4c22500450750600e03100b04032129013010b8810354030755501160350b03280c0c0401d100003940a140f40b04403651400303d40070054000303524034404214003000302003c01500050415001311070400031500c00d0f039541561260303c5111051100d1000c80e441c042e071007181d50503049a4000d0808658082c1030701e0f50360106910782c03d480e441e0b00c0003064640d0b000404282e041401303400e002d052800c2a400e01000381c0d4840c1c0e81e2411a10071400840c61107941e14100f81824410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 271361771 1250 271360521 271360543
    0x20d1d1f020a0c06020a05120109021c020403110405040606050d0818010327020312070609020901060503070f030908040b0408100c0507080301090903090b1305030c0406054b0102 78
    0x1189401d02c55000103101244042e0080c0c80d80f600011401c00c210700c500b0454a1004183d40c4151041d42c6900c3c03200080c3d03001c056061038841c49041da41994109602c01c950840380e014841140082085041c840540360042c02543c0183c2e9682000415031034100f1001c11462003031039840e91301c0044802c4400025a20760340c40d070400d46005580c4261407405204446403054141c11042107c1c0280700080c609039000c41c01d0001600045450000c002a07504034016052013282c407884a03030307256002256180802c8031110002108445100341080c0250b21010010f8040c00990b071070662240107001307143d030040e4442015a4814043c00640036254032a0507480c0007549401ca1600c04503031580c0c18180070600030410a40d594410807020140a200c0f40001030140c86030441e200d00c10440d0403c21719004d07110780c9009008007040c00401d4a4640300b003906448000b420900000000d081c1d409900c00441c4050501518003500280c2114030044403d103642c100d45d480034151150303040028144040720b44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 271363021 1250 271361771 271361833
    0xa02160909050c1201060b07060b0301140c04170703081b07141f031803080901060501050313080703050c010203010e010510050c0c040e0a021f090503070810020d1d 72
    0xd20200090700116442806881c21144956182604d951507401800c0a5020940d00c0301e001540808000031600b148022990403002000710008140c0c26145c1404225a00740405104000900070050382200203078054000310103d603015a1640c0e204455580700401502c405034030380b0600089422b04000320b0025116410300e80402400c0400402d10035811400382c285030004483c200307011140300741c0c000328508820b9521401e0804580c180680300c2d000036904841103501340b05000c00e055005800302c0b8069200c079041c54001500700c2d110740f42a034220752811000c00c40308100d140316891090020754041c00b01c00701c0491031540b4010811015056160420040c007030248880c1a81c0c04000c500d10f41c4803082501e0100b0015514002c10342000d030038040007503110900c0f0844448907a032004032503500000c039896251030552a181007558484281c425000f1591118400140001098015140c1014030500104616071101112a803030240740e0740030403240c3e02008920b0100300424201ca17061040b274117 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 271364271 1250 271363021 271363031
    0xf0504060b120c012a0f11060a020703060c02160306050106030b100e221a03160b0403030e011704080705060a020c15040f060c0c03020c01030b0d0b0a0608030a021609 73
    0x10301c0302d50b1940410b105460510400704410529684540d0003c1d84142c10568607983c000d0382450b001c1c2040c03000840941e8000c00880701105a4180842100c00880c03043d00103000c07d51a50382c0f4031005e000f0325207054085000f41198603c400e0001c4035100701443c0301c0c0c90082072540c106603008044034007201405201c1c0e0704030644001c0ca030317422a0a204510380c060302e20780611109060000d070300b50b40b10a010208036181800302c50302e00d13141e40c03e140c0b4060300031816106500100c0310900360143d598003071041e2038401000b04100282c0948040c01e90780e10181020340c24400c018405481141084806666040f00000d003a000c20400b40441540800e0300300b01103081c100b071410515980d0014110342240d4209004c040380a211003038107035880e803d501c02820302c00000040c20040c05c64a03e03030004c401510402e1342c06015503000740540c6007001c03005801500454015200c2c60084c0d10040c01b0010f4443c0ea410012a80241c10710040031190a035130010200c520b030352000850500481e0344100c00c07440ca00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 271365521 1250 271364271 271364299
    0x3120f040f060905010605030619060e0108060720010c030204441203072a17092e0908010b09070c081603020616050309070302130f0f0504060b 63
    0x1440480248940080c0000b95803c00c0b480d01600608040d0000380d8544100000c02c41c8040d00001c0e260178109055009001d0b4507500c680110180d0340a0090084c2c42c0c0103500040c6040d44100c030040d54501d110781001006802c1c00103803508584070387e4010300000703030001400d100403540301e40b41c0025014800d50417800541540c0310381e5981c24283d80c180d003075a05c5003008045016410401c44a085801514243d41e03410710031000b6000850782120850701040d02802007800c25403d1941d40d143c2030b048004030448084038a0704e458154021044643d0148800501c0d900000000c1d46a007041503031a007403808e100e90480000f40c641c2d001540304007010783c10000f100c0740741d40342c03426010381103817040c207040001c0c1200f0b24010660340620010f4050110300c82a00d11b0a040d030014040340201d000320344100481c07c00c04811102480100d40c20b4045601c003840802c01410401941200c1e0b0060950000b0080c0040c4084010b0b503c08a003c0c0501c0c540310000e12040c00914840d10f0140c100440d0b42c49038555030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 271366771 1250 271365521 271365533
    0x8070303020d0501122d0611070c051504030f0309090c0206010e01120305120a1410181b080a0e0304090b1009030203060a020f0d0f0509011505010905040207140d0203120f04 76
    0x820000e40344019000e46c0d0a807105041e2851045003035500490502440110507520141ca410105060350031424080c80007680c1e00f884103c0042d05229000502e140c1815502c40d1000205002022403c20a103140001081c6d005445014042100c944c0601015450481c61070964801a001000500c0071951102d001075080b4046494050003000340d814079a07a0604420010030100b000316100d200e01100700311b10803101c1e5a0700401c0d02c841808401d00307002c03103009240894034940d4150300d440425031130314241c0d507010b03642c1c030b1340d0002c02100b010404661100c01c05056412551010910603100c0361459410f00d4005007000433414a0300d4540210740c80c607000a550b80001030003140074a81e0029032801c00f580c04a0840d5a02440c1c00018888014144405802404100ca4a4920307520380360141c0b0a81c2c51020f4440101ea030141d41e40c1114a0412041000a600c0004111980c0106060002c2010401d00141c1d10078586600610749940891152581c5164000e141c0420040c00c02e01300710020f0f03d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 271368021 1250 271366771 271366793
    0x30f03082a0d0509010b04020f0403060c05040b070f05011d0703111f0804050a1b0303081003080405010e0109030501060f050109090e030d020a0e03011e0b040501030f02060c070308070303020d050112 87
    0xd048100410f450f156034081c1e600600b1400c0001d034000380005400c400840d000001081128030520003002040c44100f400c0326140124005d00c4452802000752101040c0016569852a80900c0000607528105560049401e0044040784075079000f0b44400c0062244028941c9560503007914002004485440580810500c0c105894144800724021030140706040101050490348203d40040b0b2900b00a2014803440c01d0744002c4001424000001c0c41c14440360704031000700c03940000c08034281030078540199030040c4007240f0181003018000002000c1002401407000070003000c801c4000b11818800018038054458102074a42410701d1481c800790712000003202c194110384000180c81d03030b4940600701c0c0e1104d1504d2009070307d0340c01d00006507480c001040c0720b030500c610034141c2002000e0b0b41c4018002512003d20010f800c510345c044034000942080c100500f1541201c00c1920340c196200c1e0b507400100e81080c0c0c81a07002940c003003803945132400c1a00c1968058583e1034603a4409081694600e11707909 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 271369271 1250 271368021 271368037
    0x13020d2a0f02061005040e0f030c10050115020a0206030c0f030a0b101107051c05060906090d0c0b04020d060615080907060c12120e1f050c0405060d0c09030f03082a 72
    0x190784614017a548041031043c2340c94006001d0a5994500100440c240c6d29081c4800141e42c062401c0000030b10441e0103070395081e00c420aa005080945200d8080207442c0e0002030040000711020071007100c545002100452052004880020751005520103115000c05002001c1702442140c0141401840740021800100d9400b1640c412a22080c0a5444812603ea00004281d445104184140040302051241c1b140c110039045842041160004441e40010502d015003481e0107140400e002d410301601c0040114081c003808200290b440000240e440313942425400054062024030042140c2400f8420043c030051070708176640d046544401d00c041d0902c2c4d24650500440b452800342071101340d008006460b100c1415103490200d20030045040342c000000d02100070f440c180c001000c0c840c021041e5015a00042c0059040c414404040c0008003114103040061014004000000030078118584440c18400da450003220304100a103c22680c10000307401908210700c1c01c5030030500c4030502c242c0b0118 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 271370521 1250 271369271 271369279
    0x40818030c04021603020c040c050a1404081203040c1a040902090f04050114040f060b0405060d06090606050903010507031407051602130c02190213020d2a0f02061005 73
    0x461500040d203407802210704290443d001141a40d88079100c0754028800f180260240c40800743c20608000803287d100a01d030011a0701403042012080c401c41650707000e1003060006130703d4252600e40306890b001100414141c045000800c100030008212450f100401c01c000310410f02c00c0c1c0380d2047c00807500481c080c02e6566075010a5050042d501c0c84181c0b00810b030007078410171039540c4034010130300142600c1c100640038504242c400a0403003030b18800c0c2c500f00c8240c1c1220718140f40c00c2030200002c0d03921002c540e01c20141c480402052000f028880c210080c940c40c0c5445a13240011024142034810051003541031603c1c00c0c62542c905910b04010561050162410507a01e05404032215005106004040d422029107150a940c0350300c10b90200400d44903580071252043d040711813822865252080c0250024101c1580903909801c94024001c1e201200b40b01181192800e802c00055810052a02c0319014080c0c4550890302d03009280d040e141036291000d08241d01c0c0c100c1d8100170402c0b030b0b07104042c06 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 271371771 1250 271370521 271370557
    0x101a09060301060f051c06080c03150c130306050a02030a06060f020703030e0411070b04020117131203110d0b1201021602130b060703080a0513050d08151503040b0c030408 75
    0x88144114216000303913490107424100c1a80f00ca096400901f10350003030401ca8400e8502d00e224914001448002480020348102420b507a1100200b0864008000c200c0e0007030001d0b8401320000d075050280c50310030400490300503180e15150070b9960568100d40d0000341403104d0148146640c0c0d034081200c00030b481d050b0500510340c05c4848085001424000f240e5441e8200100303c450030060000c40c901c3c090b44c001d03a11050136040006403e0700c000c005503502c1d21907401308500340d00000c0e00c1d1941360411801d24100094400001070a15030b903a880803120251003503840949201c5881c0c04000e0301c0724074a80e0802142051186136050980c50b0b40624003920948141c010500400f055400c11039503610040c01c0c440c1ca0311842c0c980580708042c10f80e100d22415041c14002540641001c5440e155280c0001c01440b140b021500203503410800580590385040400c0075410141d141e1815050120050101c660f0f035078501410291034544000e030910403a18001c0090001085414040d40c688015500720015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 271373021 1250 271371771 271371797
    0x30519020705031e0903030c060103061d031605070f08030c0d0813030302130306060e01090c1e0c0f0b0702030d0e01020304020105040e070c060519051b0a0e01050d05101a0906030106 80
    0xc40d401401d0000d80d00d81f00001c1c084c1a14030002c60910304a030702c60103050203900d111600c401800d45040c81c0b10039895200b80300c82c0e2100f84103d010206a507001d0415140401d40792280c0348054150350b000642964000a5401c00c04181000b4000507503009180c01140c0703042503049030078600d0907408040d00b0542c000c588081709201042d03004004503072200341004207590300d0800d04004030302441181030030380c64014100e4601d4055948101c85c08801d8070201203e07005014207540c41c0d07500c01d0703092301c00300700280d11000010703000c80030b55004400c190000c54445002c1d92904068404a05c00480540d006000b48030050340c014080d94144d5601c4581d03c2c0003550340f003104442d12171507107001810941c2054240042e01c0050b8529014890100c00b090000c0e9a07008035240390001c41e82c81f1031920382c0081101c042100e10a074101c2407008014900b5914120188140c002a070704203407007034081d58001c100c04000c143c00071200d20366400718400809082114043c0059410300051043d0004d100e20100015 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 271374271 1250 271373021 271373077
    0x3090506071a01090c11030715110d0e01020c0c041109010503071704061401050102010b091f0b0c010203160801030b0103030509060f0d06080d0504241107030303051902070503 77
    0x605403002c0c1014050302903030f480c0345010141c91200d002c0d40115085002c0040d9006000c401c403450684c104100c1c0381c0703d84080e005000100b44ca4499600d18883c1030152020300c2c0680d000d60b420001103c000561200503181caa00c0c180390024422a10a038506045044544142d4068514403902401c0141e00e80d65030340c80a94407110140000308114106104001c2040490307804030305010a000c040a10b1030380c1300c0b40164201c52002000030b902408410003d03150a043c034807920700140d1050750440790a40d44024109041c0c004500080c160794010040004800464040e040c0c0742c1c00500e0001621751441c0c4030303c40c5050040c040501000350000d00101c00d51a00011120a550358012203996040b50740a4000101858084e007503140c0100c4441e10056413003a0140c6095840003541244034200a03041c4080e003410b11900103040c00f00d54445032120103000c0c08401c0041d4040d44001c903003450040150241f0440d0490311220341e620501038203000c91800015990080c0e024810500c1707945507003240d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 271375521 1250 271374271 271374293
    0x60f0b07050a140a15060e04060f062102040e0309280302060403031d01020d0f080405010b0901151e0f1b0204020a050904060801090b0402060703090b16110103090309050607 76
    0x14100c014069000003055000140c0c1d200498002d0031009003180c1c1c803044c000146e810a2107203007803114810000c2400f2030f045504c40d0217148a03421340040c50701d541f909001040701c2800b180c1182e102d50b840da0300003036003810701a10090540c140040c5181041c5031000036600301003014000090b4002c048621070302480044000080d6400911103034890f81d40e0b00d002480c4080d150304445404152051141503540000745090030341a00752200e01d4442c200c01022030325004001c02c01d5031030703649500b54040c0e551a084400780c0a0450001c0c902e80d4019042030290002c5070b40903148003189041c01500c01c446034003990300000003829290801c100c4500f401c44610070001c03070030042d41c071030310008003c8041900b0000402050905940922040d075540c1120b03422104181c002600c6c25a1202c000f03801407821134020702c240ba100b42881680341707864a051074035a402a8850586176440303440e03d001881080e0803c00c001040c2440c003031140320f51994006002201d0381c407905000e41c5001c1514010001681c0380 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 271376771 1250 271375521 271375523
    0xa2c011107050303220203030f0705010c0306060203091306090e0a0c060f050f0c210903070506072a03080715051302031f020705060a060f05060309030a080705070b0906040312060f0b07050a 83
    0x440f41c5036840d513272a0f1080c41d070011758121500d41c80c211000501c140640202404ca030718540145090859480603c60b94100800f8004203040d900c42011400210320b10a821200f41080f00070252041c0901d0241c030b003401c45800c20307014400d00c040144803243c0d001c011260512400703003605450740c0c000180c080c90700c088003614030402c04005500d80355100d042d07405880c1c0381c001141107034030140d51582844010b00c6180006000128030005524030306d504d00f08002001e6810700d008015041e03036a107640f00c039500188405c0700c00e00d682804030340c426007060040d0307070704000d81c11400d4003e41c1403540002d41e01c56540e52000c0c11000c1013541c600a01c04554141c0b0052500501516110716203419824002c0030707180500e0035500302103403005c500760501e001a01d114407000ca00452502d40007a4068801080040001007041420082400041e07040e5142c039014180b254000d00581c1010700d0050550391140303464100c00c524000b8100182004100c0e02022980c4039003119035641160300301a4101007041d90 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 271378021 1250 271376771 271376773
    0x60819020f0a0815040204180809091518071d061e04050a0801050f0106050a0512091903030c09080c0f040b040209060c07031b030201080106080a2c011107050303220203 74
    0x100340d00c0114201318144aa4070031a810002c014107080d91001c14885510301500c0d0520601010a070360038101c141a03000800c01c004050f00e00507082c001015500300d4a5270182e0300d07058200382705045070081c0e404c02c40d8045002c201c0d1110120800031651502401c402e1150f16161440704002c6001600b04071005000b018007100c40294940500a0190100340d8440e80c1c1030089100000710701c3e100d401039520b0384096544491030038285041c0000e90711409080360075507001d40c214a10048295220040945210b52004105501c0c20711000e030826260f03a00c0007540c0d4100e0450600c01c0c0d074076103803a171001ca074044a000580b89070880c049002801203002c0c00303810680000700059004000190501102c3c404c8410495070f041072454452451290700c4000d021540c550010300c0f00030300407000140c0c002a150340019008541c0c4400c40000b0140720a1100d40603a00048000c0c001400e0140640070200300740c3d218030307161480d07032020380d030344001040e0138004000c004130260451450007100e60003a400030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 271379271 1250 271378021 271378033
    0xd15080f0304031e230705130b0f010809060a020c1c0c120c020319030203090315100506180d0c09050f180d0f050d0b1e0301060819020f0a08 62
    0x5080e40e903072043c0010f880d40c401d69000350b01504551451000260790150f5189140000c0d101c2584a40416a0440b141402420350210703103915007162189000681d8140850359018007400d0103006030300701800f141040040c0c0100a8400c2d400150250050560100144d40303d40002907681041d5585146011078030707041e184030405961001a003580b00d0f01644030710700f000d07201100507141c1e40c3d103184001307405070001c03500345907510160f20700c105a0038040e005407407800340354000281c1002a1403080c1b4010483d200203000e0261464070303000014010035524107180810405c01e40c01c110300c252603a203210303910b070300300110030880054101700052580407030600440c10800e09035207041a00b210480380d224640c070031107404904005601e10754400310b621a0400321b490500112902d902844035841c5850710b0301590320040d100e401702c400044210980c01c0240303a10315010142903400f103600851540c2e220400004082a92103c009400c41e81103c010824886000c0890a840e03950b0b400191030740258 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 271380521 1250 271379271 271379293
    0x140f061807020c0619080f010f03030819090b0a0b01030c2307020603040b190902010e011206050d080408060c070506070c0507030803150109080706050a0309060905010509031207080106050d1508 85
    0x5000d01020300305c0c41e484004203a41c0349044800364100c2440344a02001e07042404202007030040440907001005c40c0c240c10740b070b00ba429600c282034801101007103410240f40410800070341003c2c0f0980041c0002440e0501c90480d12201c0184450456050702d41241500e40d03030b0314003008801003114400e030382c05098a51030b807a140c10300903d241c000b100c480d440540b07030003460300b8001103902c511103070b035030703050310f481c42c00d4200c0400450f44501c0d600c004440301c540d174400c0440c0594850100c000882d01c64140c0c0c654681c1403a40080c01c01c580500900300c0044280041e0000640124030a1f03845002c41c0f524071201c00403402e00b41d01c2c00c0560750001e444484c000083c0030b5403828401900080d00e20030703260301c0300c55a920a0f03040d9a80709540318084c00034505212941e20303d032017600a441e409020700004981d4540545030303c0e08461040d5448400c9900028845000070311080c2e030541e110341c00d030a10441c650314141d0040c0c014484d0014864000f599aa5880b00d01c02c2801982c5001d071800d20f040324001111 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 271381771 1250 271380521 271380547
    0x907080403110610170f0708161712030c070c0303090302091311010e0f040212040c0b0406020709020a020f1c1d10050913050703140f061807020c06 65
    0x103580540009805401d60240400e0001d05280540389401c10b10341114604054106012100d840402c3e5078001c400b0b607000e244400f001020003034181040900b48410b03054040387d103030940d280d114400340381500032808103083c400310300a9100ca0000900507038956800084c0451489610b20050008026142c08001d141e40003c030041600e02c20385102685449100101e10842141c81d0001c100ca05498810f007059403086604a00d04c2c0800340c00184c00e0521100040d00340d1b0020920b041d42002c0323000c1003000740f1500a064400916000c2c0d0350b50720382410918004d44070310b241c0c01032644603030300001e4411419100b001016000c2040c1002c5d00e0311034840c0c400c411180c82c000c03009500055405503491f04806041702240e1240040108504d18802440c0b1084e5101d8100b0300c1c1c180d5000580072129441c2c210300b4014140f05010560740000c02c0054900880c0c3d4101000c4e09d02410142c4000401035580c0318020307000429000300d8031409481ea0369031022481e0410341080c3d11b030000004919000305440d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 271383021 1250 271381771 271381787
    0x303280905010809060601140403060218010806010908070308090105071509050115120f02041409070501090b070210140c12030603011a0102210f04141207050114030c090907 76
    0x18030340e1840c80d41a581e600458200c40103407644000c2e03800c00404201e8940c0241c0010007090503a60703d02c0c1c03c6c103941740c13201001c80c2c110604411051261040300c405540e030090119a002009003040038000b030605400690381c1d5141d000080040b0800241000300d6030142003515199030388603600c10b004809108901c0041c0a00d170404a036150f00348481028841c5c400d03140c40080e1841542c00b1a0380c02019100c0c0c100d959560103040c2d8000f41d079903040011800e49030400b24400e04840b0000c250440c5018001440c201442d4090b40382c10a040c8080c40040c2e51b02600300358803e081c4e1030192101581d084540d0128402e1505c19000c600c40d0030703003900b000c00044010b50b202e104110020800c1500c031480071151000c5d12042030740141c018200c2001c01c4000b801100b4a0042254581d90030501c1d0f81940383c4c09035005801030414280380c1f421540c1640b40c407140728071400b480071018007003040c0740c00000303480010440c42882441c08080f00003840c44824806480154400803c80b20040c2002c05010707200d44 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 271384271 1250 271383021 271383097
    0x203070606180f050618180601061e170106050703030e010e0d0810030f0b070941010203040b0703030f02030f061306180c0c1406100509010b0403020f0303 68
    0xb40c144101c040c4851554440e692284a020380074441c4407450a541031a81c1c1b00c000d00030003080c19003892030810070200300411b030701900d8035854504074482520001417440c1c80024400c8100481c10800a500350000c0380e0440c11079500c0d0034015181d46042c6020f601401a01074100e0640d80f84c040c40103082e840c000b6080301c101403251140c01040d1980581010382c840c80340400342040c00500032600014035034130039841c1d120010f441c00c10a031544844140d902101d40c0602c400e50005103103001058030044042015400382042c00b0145e41c0c1455500203500ca008a2041007481480803440105040c002e402c01c049081070301104641d2440e0441c5001e030401010303106940240301c1d4810003264000540304400c20ba8001a464051320340c0704a0000d0080c20b14114590200003254030444001030401d6041e40c0d40400c01300140180d460460200c50384031002c1d500003403040f0b0800c2c0040090ac1401030460342070700c1d01541c0b64000d1800034000700b4654840c00070402e0440600c2c40030030301c1c0c503c001034104a0079 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 271385521 1250 271384271 271384319
    0x40c05100207050d020108220501020d0b030d09031104110c01020d11030915151017072109080f03180105011d0609100b1204020a1a0403080a0203070606 67
    0x544000c0030101d940c0d04950141c00e8020800c0140c4c000917600070903d8a0f4814003004140704115064107900c038038140740c0902110503a402040c0008110070030301509690540c160000c00710f5010309400144868081d11002c1c000708903c59444805480350380149840701400100c01e940c5041d982c0d84c4900170750001c0b5190071814645041c80ea0440f20a0f07046900451019009080c0000040312a060030903014213503c65000b0a400f03105039640751030003034100602c0d1a03150b030f0048025261581e0045500204074001f00000300c010400c4a06840d00c04900c0341500301d2000460240078a08100d082c801c8082c24101540c001c800c12840311000222901c1034004d100090107141d80c2da0400d295180d92162199614916900004580b800d2101c44103520420300703c4040790141ea1400c01840c1759000d080404000c01000b002c10003941807145084008160100000380340c0c041c90104030786640158007005002100005801100c41c0c400c009640503d038002030108405981d81d042d426040010038a80419 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 271386771 1250 271385521 271385539
    0x1060e06090a1e1e1e0b090115030902030309030f03040335091504060e030115080d0c1a010e0f090d02030a0c0503040e041202070b092115040c05 64
    0x14840a4081d0041d840318240c828000d0443c0d203000c0001a03d0603076a01104da0310405038025410780b041c05461114010b070080700908008000950060780c06213074020f0700074400c50b00100140b01002c199003160307864034030700080ea02c01c4900c0000c3c11403150444941c0d1502c41c01944562482e0080010802c980c800c1d10b0000206648200c29803851034844c1c0c2c111602d051803007400d810006124000c0c43d00102c020006504a000351160404517040b6400c51000110700800d281c0c8a81400d00c1248001d15031042c0e0010100d1425a0041e81c0f81c01c01d0764600108411949203000700018a03144112080200c030f44281c6c00d42e11111400c00075042100c90101210101c2e000c201c0030280401c0f40320504007540d0145191100481d01555100b480c0d00080398248010080054607440d41004140910b104604800e801c1d2240030000745401080d411003440b0003030402a80c0c140d03998950380c00c04150085007d0307140440d0310504035410201d0070264610050082002c00040013035028100f001ea50301119001c103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 271388021 1250 271386771 271386781
    0x19080108100b010e0d14010f020c0c1e01051309060b091e03250b0304110108010f060c15090b040309090e0d0801092004080304060e0d0203060a090305090301060e0609 73
    0x20b0300e0070b0441c0e02e03020401202240030740e401c0c03050b070001c551030050342d18501e141c00f201d6006084404088807001060303070100340c1001d8072100b0b004c0c0100383e1108036900b48200030800b4014034400541c42c8024140840000c43c030782d03040d4119801c0c20080602000c00c0010640d47c02c0b44c0f02540c1c1c462403100388100005424960a07040b400c070030740c40380d650140051480399085051443d90701025000c00c0c0d1318030b81003600041c0300b0182c0001188600d1040d540d200c0c00760960400034100000603045110340d100d25407018480c0a502c481e0040d4042d410154400302800c040c0700030341c01441c071011b029005281b800100424981c00c0310345082212001041044690b104e203580c0ca80350358100101200195400c00102b00d14540750b00011100240202859100c000d4010300c2919a802544451015080030800304106500703c0c1c09075a00d442c05a40001800d056070b400283c841d02c0c002c0c0f4500105648200410030305104200b6610340f010050000c2160a4071400164503040e07088440c1407003000f000000032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 271389271 1250 271388021 271388053
    0x100e0f0603070509010f05130f05090705160303020f12040f0c05091b0705161805070c03050706150306050c04141801030f080d050f010e090705030304140619080108 72
    0x7902c641060b99401c0c0c00e119400004503912482028070780308010044c0300101030501500400001055050f40303281406142005011707605d80c0080190040c00400c0c4080007400f401d81985070034060b0305240042c1ea8400c08001c00740f242c022103110b04041c503111410031080007940081d00740301078055030140703c06640e510100310f0001c8040b241088401c000c3c80407040035505100103048090320540503680d01e00010041c80d030fa062111f038040c105200c00703440c2e41007044810744109034214540780743c01480c000040d14050014071840400800140e036805444d0915003078507281d40d0295a100d0001d0041e820002203200817504a406005001005c84c1409010303481c2c21484071019400118984607668a10303100e4822025008405613480203040014030725a524074842e46108035800c07800c000081d4103044e103c1c00c0300f8000420003409903001750f900340f21700d580000a807000c4800d0818544103502e512004200c240c0103200c51100f521040c10610200c0d01c1d0000002c5059542c9030080f100d207015004458 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 271390521 1250 271389271 271389277
    0x40e100302040e0c031f020c0f03070b010e060a150320040f0f12062d021b0a0b0c0903030403140d0f05040e010e0a0e060405011509110301170c100e0f06 67
    0x43e03941031b0300c0142c41000300c2c068141000d1015001c80401814a10b0b83c1d030312175040800d101101001a00005051402c20442c03141260141020400c0181945000340205554000138051141100001c6807403910591090701311514101c20f807001701215501e5011071500f1034010740901040c602c2015404600c280c8224038400488807049981c12503000d998a0b103800400029410101566141714200e20030b4146081c0300b5140482060b0041c0e9804811010401c5c8a6041e03060400b141c01c00c02c1c4204c049145030742d107143c108012a4a180d40c800d5039000181c40d61007580c2c0000d0030200400c40c6003c5003403010601030890001903c0b15a805008000c040382c0c40d1165000e85c0c4080c101020052000c1e041d03920946030310081e101700c0014104004110b1524043c000c8404507400d03911a50701c00c6461680c0c841e000000c1c8030702032040c010f00d818101124172900050040c1c0c1c1c0c04608000250008940410086400b04400380440d804841801c100a051408032050a030103003075440090601401c000c411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 271391771 1250 271390521 271390543
    0x1060f020c0a03080d060305060c13090c08060f0f150c060a0603081605010f0608030d110a051204020a03080705060f060a0f03060b0409050706030609152603040e100302040e 76
    0x500c0000c182560358001c8a504002d00600301c991b81c80b200400090f104220160150302c000d03000540350514a240040c03001c400d5040003010504041040e9207850b00641e511380c205004407900e492407440d800c0410034a20600c2400c603848040101c180006107000c1c1d004000021200e82600d80380d6845107100e00035070f960340c40018020107040140c0402c1628101c0700d191150300c24070001c207102d220b0034130150aa5010750020001908005212000c5a403280306401120070941405400c129220001070302d2802a0048007030a00d000318002411940e40a040c180a198081d0055850b0b02007410055070304c000444040e8025490440440c0403494066903090884403038580d880703205030550391280098a03407904a2038015844444c41400100280148000340507966000222070707103840e007000251440250300c982c2e07011b04100b0038400ca4201c9008251050b86030b081a542d0910b141140d80e2540c404e0340d1044bc8102080014042600c1d2030003090421a0300031103052210340d28150784a9220b54110203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 271393021 1250 271391771 271391779
    0xf060510020a020d1e03030209030d0206010f0b0903120a0503090601170d0f0309020a0602010c091a03060909030c010e0a120816110a060f060e09030301081f0b120601060f020c 77
    0x3003400c0062800100200d02c1a120b1242480c060115841c1e05d03034034101410040700480d40120301c3e00c065017400c201c20b156941c544e01c024155545440c4a08940d4216805031620f46040000c14210544081054a000c8140e81101c140d40341244840188207400c00d0f10400c41d0380c0070701800082c0b140d80340e60b4001c46440c010000f410130542214426111702801c00098000d02da102c055100c05a030340e00d0b190700010105500041045c0700440002041041c2c03541000d5406002c1c086100d8001c010082542e61196096a0f044d0b440c1c5c541820061860041e503480880a41c20450402d0280c1c10204e8807070f03083c80c4182d0040d4104080d410302074841400807505005014030090380c11071040d1003165603011040c055000d070351100b04980c40c2c1d4015503903010308850506807113160820030b9181125602d68020f8401d00a0340c11541001c00c0e41e51a580c01009462180020b01080981c004095100384290900280100c2c80c1d000020400e58aa00d001d00c1000c01141c2400c01351141d1034000300304400d480da0010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 271394271 1250 271393021 271393033
    0x705090f0c0d09050d020f060703020a1b020607080c0c0f011119320606030106030201051206010e12150a150501080408040e1f0801060f121103060a0f06051002 70
    0x2000340840c0d40002040b119a2511404a07102003001400b2202003031526501030515001d46030b41071407502e080034210a0806204100240003c0d900618001e010002407820000360b04150002035154018242d01034000d00d000286c072400d11400045110610318141d500c6850030941d0401990b02c1590b030289504d003a042700c410345003a012030300404080244a2442c7e000501c421071000380e41c425803241c071070400300311210b4080c550710381c00c106060b40306038101c009110150a40e070000341107000d003600c8201e041c103110f000f140b80b5a010301c007440010172001e002c0341840102c056405a6683d0700103212105180783c4000701c0c05004260040307500c201560f02c0003140941c500390045a803050006c0045e50409800d00c000b103400b450f00c00100c1e005d94003800381c460045000003010003080d60743d43e02045032685000002c20244082c0251070046507107400304442d62000c1d600703106541001e10b00e4015894058102080981034032a0b1081d06626800700c41000340a0f100c10511410b815280342d00c401584c001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 271395521 1250 271394271 271394281
    0x5220c030209060d022a070302040b06070305071b0306020a050a0f14040521070303030e0601090e0d03050a090507180608070302091302011b0f060e010203072c060403060b030705090f 80
    0x217400401540c1c1d10030340c258030300d0b07036071000d41c041c910650b8080c0c092260801c190030025072810740240540300741c00701d400c4c0340f030701c42c417581c020307045210380d0760300510010000413041007209201000800540e0020300a42da18651000002d2040d80a0b142090118810405000d115445800e84c03014945400601c1c510f842c0c103100803c102c0214802c0f02150b980c0c850061040b50031001d0080b240110b100b07440220711412429121420410160010301205207440601c41d2210301c00580b035490511203060008843d241d4003109005010602ea01034120b10440030001041d9000704090a0001420102001140d0b03c83d010390b52100c4241c0301c044d50242c10038003c900e810082e4903020039103e02c141070104500e281001803614402c0901810b50300000362031480c0301840070341e00400e140c0e82c1d0314000071451450720300400f50020448a251141203941d00ea41c6102000040240801c4680000c0c00e00342c4030b07907a0380741200113010310848040c043d00803150700140e141081d104071400340802d148180625607030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 271396771 1250 271395521 271395547
    0x1e06030203062b02030c0909030d0b0d0b16020601060201060f18060e09030c010b0d0302211c0501030512030f07030e070b0a02060a140c0a140405220c03020906 70
    0x202800b074991014100016140c0c101c582c0d8015600c0c800d0300800149a00094010107040100c40c10425002c1c60200081041390031010084420712000110009000c551b040041b55501701980310003008116100c05100c03d18001e54201050104154210f0300d1607030320b8550490a0321541c1c4581c10507134203c4001400601d0b81a81d002e1001580c5540005880d0303034403080d00c0100d4100b41e6240e0302c80d4100103107440b24144207008008100c80705035902d124004440c2d80082d40c560001201e00c0d1070311441c0321409403000c0c03607504981c84c0131003850320141e61321082c02d4898000c0000b072008803814440c1340c090034488026003054911a00b0140d2011003207540d00882a80a0094074901c2c003141d008922001c01c81d604034401a01d10400503500400c101d1402d0b203403040c21519a42070015940800380708010400184070225809002146403030703035a288030100c0c00700c031034061500456804540103102c0e80c40f40401088190500300c040c1f00a018003447e58078190100c0c880c02d01100d400c101d080202000b2003070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 271398021 1250 271396771 271396777
    0x2030d0f090c1203121b0c05010b03062805010326090a03060902180c16080706320112030f120f0204170631050304030602131e060302 59
    0x460008288100d055640c01c09284540d085070082c0030545400c50180f5038880e4052407003100c145c1d0300b00701042c2d0b42003401307602c604200209420800801c1200301003000030f40018014880180841c0c000e410689504072840c100311070710741503142401d140f443c8849894010a41281c3e0040401c07451507003100b904000028101e449010454010480d038910f0307855076060b64000758091003000442080b603104111300c4502c0c1c0624010500e10400c00d20900c0e0b10254100c1e84140300000340040b0204c0c0c80d240821a50080c0d410140ca190b18243c0e02c100c000e103012400390250748040380b05032208802c0350305500c0001c074203014644006000c8496500044d00070390700b08107000c1150820b070345560941c0a80348255400340381e0310008642c01140811100c02842410559424198080c01a5141092064040240c045e031501e1040c0e0007030306c802d02c0ca401040c2c03154540d40e4000c0c00b6265510745a0520201035030190710b45040f40d031000440001c00303840c0381c14800601c81040300d800c03410a00c0c00c042100070750 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 271399271 1250 271398021 271398041
    0xc090902010c0b010e0105090a1e2007061a01050a0f0503060402191d040603080f03040f1a04050c0a030302030307030c0201020903011a040e0d140a03230f090c0102030d 74
    0xa2401070b102c0c0402d841c0c00019008182440d007510040d030510041c46a0484054400004a410039aaa0000c40102c50003101c0e00c50b002c2000140740d105e00814040c010350101c004e501d40910004685050107290740001048403411021800c0108426004640310312800f045100000c14074103082109520500c01180c024100600250034402c05004e007080815030b4091a001007610a83d042000700e10404100c50002c038111020032095186d03465805052044001a01004a001000800704504c00c4942c0790b41e240c00031440001d070810303029071070340005040d10140c9040c424100210f20901c4c000305043e0599505030301542c10b5032680310702079010300000c40c196820b654082c4040c01e200d8409105180709013644100414280c2d5001c010b03c001c0320b41c070f2074618a080c1c0105110100c000d40001000c001d02a0034006140c0d280410320f4201c00a084030402000b0b2181c03441c09490010b02e0311601640622820301744000c140c0c0310360080c01e0b0381d000383c0c0000c2c60142e003091001d50039800390f943c0120710341 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 271400521 1250 271399271 271399277
    0x5060a0207110a12020907080705040b0306031504050615040b0d03083c090102090d14010b04141f080c12010902060c03130e10090209041e0506040f02070c09090201 72
    0xda00b480000d08150216005000c0f0070001c0c4421038154500142030301e0b044907203801c090100742002d4600420500c158015102581780c000003103411038604100881001f042500d01382d605081c14500a40c1f0380c5800d4801158a890307280c2d50002e2880c04d0300c20f071120000d0080c001c0e03a1401041d5429210300b030006043c110618000d0b180400da034804104d5000203681d00030709030210440810f5a200b03091001603c0000a68410b000440003911810504202250407180c0b034400b01030004d8412780074199000e00e280c1c21504245203032940051445883c0d0040040c00803244401100207110380f465400392181110301e50109451017050704040d0741c01c04100400c0c000218030010582c001ca840b940c440741118034a0361001070039001c81c001100f08100900009401d07982a820a990340c0401c5955502464505681c00951245207030740b5548040e480b40160312610243d50b1441c42e0b1080281700c21a03071103000d0b508021148444048500c22038550a9001d070043c8000c2d41042e4070701c001000904412414 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 271401771 1250 271400521 271400543
    0x108070f11010504060209011215142b15020c0607080c070204060b0d1d030703030c051c060312030209060d11090303030c0a201c02030d0c02060412090305060a0207 72
    0x1600083c0a0301c0d1103a4014140980c1da103985000041c0003095424110751401c0c50300c81421040002d020805080f10011003200c1592400d050004158003899640224020100182d03030548540c1d0f010107c8602c0e01035070346800041d860100704010382c0301c3d801c822001900300500250000d80140d88076500801080702550500c1c1d1651301050466541d40c00403a24240c1c00314072241c1e64801c40c055a04036105183d00c0f10100c03070702004481e5503800341007001803e242d1200004448584102c0a0320451044054607030002800c07920b00e003000f05014001078502c42c01e0000707800419800b90084490144020b400e261400c080403d141008045001807002c20f00010098051965010005076004215054001e5641d074075401002c0c0903411100041007146110015160141c04013203400303040f201c00381c10b8038003102202c00c03000c9086104505090340c20324500300d81142c11a5001071140d12a601ca881c21000b0300350107450541d040e500310300c001429540104009421407003681c000d8281588a5003241017 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 271402877 1106 271401771 271401797
    0x501081f0207020d06050c0a02010f02040506041413020301170c0a0b07062f040f1707050d1707080705011805030d0c090302060f0c070b090108070f 65
    0x12a650120b00d0700c0564551001c0030300c81c254848810017542c58400f02460f4036410403001c8100542c84c0c10307140360403c0400d208540a48000400d0751b0b042a00d050340900343c00c0c14075100150805054800070b2030024150010754080c000008100710f40c0310007032100c246441c2c2004051382c800c11400d001040701280907001c66030160b401500201b1510040c801c20b25043c1d6105400000c0c00c070000701c1c80c802004004001d08155140848401070850365400e00040111043c02002400e40041004002910b410070500d101d80d4800c103000c003058a02003800c903440341c1044d80150340d4400300144c0c0108000003031183c80c046d05c0c030047c1c181d00780c0509601d41c69500d010b003403c0c1120013584c40b407904120074018842c80000319402031003a5038a204980300c07d055034000b00013104042c49140000300300002480c1c03d0f903a04a0041c4d4801d403450b541c0300000c440d02416840510207010314688901 = true := by decide +kernel

theorem cover : BRFrame.Cov 271223021 271402877 := by
  have h0 := BRFrame.cov_init 271223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 271223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 271223021 ≤ n) (h2 : n < 271402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
